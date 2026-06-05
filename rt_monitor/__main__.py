# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

import argparse
import time
import signal
import sys
import threading
import wx
import logging
# Create a logger for the monitor component.
logger = None  # Will be initialized in main().

from rt_monitor.config import config
from rt_monitor.errors.framework_errors import FrameworkError
from rt_monitor.errors.monitor_errors import MonitorError
from rt_monitor.logging_configuration import (
    LoggingLevel,
    LoggingDestination,
    set_up_logging,
    configure_logging_destination,
    configure_logging_level,
)
from rt_monitor.monitor import Monitor
from rt_monitor import rabbitmq_server_connections
from rt_monitor.utility import (
    is_valid_file_with_extension_nex,
    is_valid_file_with_extension,
)
from fancy_namer.namer import FancyNamer
from fancy_namer.enums import NameType

class MonitorRunnerFrame(wx.Frame):
    # Hidden frame that manages the monitor thread and handles signals.
    def __init__(self, parent, spec_file):
        super().__init__(parent, title="MonitorRunnerFrame", size=(1, 1))
        self._signal_flags = {
            "stop": threading.Event(),
            "pause": threading.Event()
        }
        # Register signal handlers.
        self._register_signal_handlers()
        # Make the frame hidden.
        self.Show(False)
        
        try:
            self._monitor = Monitor(spec_file, self._signal_flags)
        except FrameworkError:
            logger.critical(f"Framework error.")
            wx.CallAfter(self._exit_wx)
            raise MonitorError()
        
        def _run_monitor():
            self._monitor.start()
            self._monitor.join()
            wx.CallAfter(self._exit_wx)
        
        self._monitor_thread = threading.Thread(target=_run_monitor, daemon=False)
        self._monitor_thread.start()

    def _register_signal_handlers(self):
        # Register signal handlers that set the flags.
        def sigint_handler(signum, frame):
            self._signal_flags["stop"].set()
        
        def sigtstp_handler(signum, frame):
            # Toggle pause state.
            self._signal_flags["pause"].clear() if self._signal_flags["pause"].is_set() else self._signal_flags["pause"].set()
        
        # Register the handlers.
        signal.signal(signal.SIGINT, sigint_handler)
        signal.signal(signal.SIGTSTP, sigtstp_handler)    

    def _exit_wx(self):
        # Exit wx application (called from main thread).
        if wx.GetApp():
            wx.GetApp().ExitMainLoop()


def parse_arguments():
    # Argument processing
    parser = argparse.ArgumentParser(
        prog="The Runtime Monitor",
        description="Performs runtime assertion checking of events got from a RabbitMQ server with respect to a structured sequential process specification.",
        epilog="Example: python -m rt_monitor path/to/spec.toml --rabbitmq-config-file=/path/to/rabbitmq/config/file.toml --log-file=/path/to/log/file.log --log-level=event --timeout=120 --stop=dont",
    )
    parser.add_argument(
        "spec_file",
        type=str,
        help="Path to the TOML file containing the analysis framework specification.",
    )
    parser.add_argument(
        "-r",
        "--rabbitmq-config-file",
        type=str,
        default="./rabbitmq_config.toml",
        help="Path to the TOML file containing the RabbitMQ server configuration.",
    )
    parser.add_argument(
        "-ll",
        "--log-level",
        type=str,
        choices=["debug", "info", "warnings", "errors", "critical"],
        default="info",
        help="Log verbose level.",
    )
    parser.add_argument(
        "-lf",
        "--log-file",
        type=str,
        help="Path to log file.",
    )
    parser.add_argument(
        "--timeout",
        type=int,
        default=0,
        help="Timeout in seconds to wait for events after last received, from the RabbitMQ server (0 = no timeout).",
    )
    parser.add_argument(
        "--stop",
        type=str,
        choices=["on_might_fail", "on_fail", "dont"],
        default="on_might_fail",
        help="Stop policy.",
    )
    return parser.parse_args()


# Exit codes:
# -1: Input file error
# -2: RabbitMQ configuration error
# -3: Monitor error
# -4: Unexpected error
def main():
    global logger
    # Generate unique name for this execution of the RT Monitor.
    process_name = FancyNamer.generate_name(name_type=NameType.TOOL, tool_name="rt_monitor", random_seed=42)
    # Parse arguments.
    args = parse_arguments()
    # Configure logging level.
    level_map = {
        "debug": LoggingLevel.DEBUG,
        "info": LoggingLevel.INFO,
        "warnings": LoggingLevel.WARNING,
        "errors": LoggingLevel.ERROR,
        "critical": LoggingLevel.CRITICAL,
    }
    logging_level = level_map.get(args.log_level, LoggingLevel.INFO)
    # Configure logging destination.
    if args.log_file is None:
        logging_destination = LoggingDestination.CONSOLE
    else:
        valid_log_file = is_valid_file_with_extension_nex(args.log_file, "log")
        if not valid_log_file:
            logging_destination = LoggingDestination.CONSOLE
        else:
            logging_destination = LoggingDestination.FILE
    set_up_logging()
    configure_logging_destination(logging_destination, args.log_file)
    configure_logging_level(logging_level)
    # Create a logger for this component.
    logger = logging.getLogger("rt_monitor.rt_monitor_sh")
    logger.info(f"Log verbosity level: {logging_level}.")
    if args.log_file is None:
        logger.info("Log destination: CONSOLE.")
    else:
        if not valid_log_file:
            logger.info("Log file error. Log destination: CONSOLE.")
        else:
            logger.info(f"Log destination: FILE ({args.log_file}).")
    # Determine timeout.
    config.timeout = args.timeout if args.timeout >= 0 else 0
    logger.info(f"Timeout for message reception: {config.timeout} seconds.")
    # Determine stop policy.
    config.stop = args.stop
    # Analysis framework specification file.
    valid = is_valid_file_with_extension(args.spec_file, "toml")
    if not valid:
        logger.critical(f"Analysis framework specification file error.")
        return -1
    logger.info(f"Analysis framework specification file: {args.spec_file}")
    # RabbitMQ infrastructure configuration.
    valid = is_valid_file_with_extension(args.rabbitmq_config_file, "toml")
    if not valid:
        logger.critical(f"RabbitMQ infrastructure configuration file error.")
        return -2
    logger.info(f"RabbitMQ infrastructure configuration file: {args.rabbitmq_config_file}")
    # Create RabbitMQ communication infrastructure.
    rabbitmq_server_connections.build_rabbitmq_server_connections(args.rabbitmq_config_file)
    # Run the rt_monitor.
    try:
        # Initiating wx application.
        app = wx.App()
        monitor_runner_frame = MonitorRunnerFrame(None, args.spec_file)
        # Initiating the wx main event loop.
        app.MainLoop()
        # Give threads time to clean up
        time.sleep(1)
    except MonitorError:
        logger.critical("Monitor error.")
        return -3
    except Exception as e:
        logger.critical(f"Unexpected error: {e}.")
        return -4
    # Close connection to the RabbitMQ events server if it exists.
    rabbitmq_server_connections.rabbitmq_events_server_connection.close_channel()
    rabbitmq_server_connections.rabbitmq_events_server_connection.close_connection()
    # Close connections to the RabbitMQ results log server if it exists
    rabbitmq_server_connections.rabbitmq_analysis_results_server_incoming_connection.close_channel()
    rabbitmq_server_connections.rabbitmq_analysis_results_server_incoming_connection.close_connection()
    rabbitmq_server_connections.rabbitmq_analysis_results_server_outgoing_connection.close_channel()
    rabbitmq_server_connections.rabbitmq_analysis_results_server_outgoing_connection.close_connection()
    # Exit with success code.
    return 0


if __name__ == "__main__":
    sys.exit(main())