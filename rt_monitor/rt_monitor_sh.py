# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

import argparse
import logging
import signal
import sys
from pathlib import Path
import wx

from rt_monitor.errors.monitor_errors import (
    FrameworkError,
    EventReportError
)
from rt_monitor.logging_configuration import (
    LoggingLevel,
    LoggingDestination,
    set_up_logging,
    configure_logging_destination,
    configure_logging_level
)
from rt_monitor.monitor_builder import MonitorBuilder
from rt_monitor.utility import validate_input_path
from rt_monitor.rabbitmq_server_config import rabbitmq_server_config

# Errors:
# -1: Logging infrastructure error
# -2: Input files error

def main():
    # Signal handling flags
    signal_flags = {'stop': False, 'pause': False}

    # Signal handling functions
    def sigint_handler(signum, frame):
        signal_flags['stop'] = True

    def sigtstp_handler(signum, frame):
        signal_flags['pause'] = not signal_flags['pause']  # Toggle pause state

    # Registering signal handlers
    signal.signal(signal.SIGINT, sigint_handler)
    signal.signal(signal.SIGTSTP, sigtstp_handler)

    # Argument processing
    parser = argparse.ArgumentParser(
        prog="The Runtime Monitor",
        description="Performs runtime assertion checking over an event report with respecto to a structured sequential process.",
        epilog="Example: python -m rt_monitor.rt_monitor_sh ssp_spec.toml main_log.csv --log-file=output_log.txt --log-level=event"
    )
    parser.add_argument("framework", type=str, help="Path to the framework specification file in toml format.")
    parser.add_argument('--host', default='localhost', required=True, help='RabbitMQ server host')
    parser.add_argument('--port', default=5673, type=int, required=True, help='RabbitMQ server port')
    parser.add_argument('--user', default='guest', help='RabbitMQ server user')
    parser.add_argument('--password', default='guest', help='RabbitMQ server password')
    parser.add_argument('--exchange', type=str, required=True, help='Name of the exchange at the RabbitMQ server')
    parser.add_argument("--log_level", type=str, choices=["debug", "analysis", "event", "info", "warnings", "errors", "critical"], default="analysis", required=False, help="Log verbose level (optional argument)")
    parser.add_argument('--log_file', required=False, help='Path to log file (optional argument).')
    parser.add_argument("--timeout", type=int, default=60, help="Timeout in seconds to wait for messages after last received message (no timeout = 0) (60 = default).")
    parser.add_argument("--retries", type=int, default=5, help="Maximum number of retries for establishing the connection to the RabbitMQ server.")
    # Start the execution of The Runtime Monitor
    # Parse arguments
    args = parser.parse_args()
    # Set up the logging infrastructure
    # Configure logging level.
    if args.log_level is None:
        logging_level = LoggingLevel.INFO
    else:
        match args.log_level:
            case "debug":
                logging_level = LoggingLevel.DEBUG
            case "event":
                logging_level = LoggingLevel.EVENT
            case "analysis":
                logging_level = LoggingLevel.ANALYSIS
            case "info":
                logging_level = LoggingLevel.INFO
            case "warnings":
                logging_level = LoggingLevel.WARNING
            case "errors":
                logging_level = LoggingLevel.ERROR
            case "critical":
                logging_level = LoggingLevel.CRITICAL
            case _:
                print(f"Logging level error: {args.log_level} is not a logging level.", file=sys.stderr)
                exit(-1)
    # Configure logging destination.
    if args.log_file is None:
        logging_destination = LoggingDestination.CONSOLE
    else:
        valid, message = validate_input_path(args.log_file)
        if not valid:
            print(f"Log file error. {message}", file=sys.stderr)
            exit(-1)
        else:
            logging_destination = LoggingDestination.FILE
    set_up_logging()
    configure_logging_destination(logging_destination, args.log_file)
    configure_logging_level(logging_level)
    # Validate and normalize the framework path
    framework_path = Path(args.framework)
    valid, message = validate_input_path(framework_path)
    if not valid:
        print(f"Framework file error. {message}", file=sys.stderr)
        exit(-2)
    # Determine timeout
    timeout = args.timeout if args.timeout >= 0 else 0
    logging.info(f"Timeout for message reception: {timeout} seconds.")
    # Determine retries
    retries = args.retries if args.retries >= 0 else 0
    logging.info(f"Maximum number of retries for reestablishing the connection to the RabitMQ server: {retries}.")
    # RabbitMQ server configuration
    rabbitmq_server_config.host = args.host
    rabbitmq_server_config.port = args.port
    rabbitmq_server_config.user = args.user
    rabbitmq_server_config.password = args.password
    rabbitmq_server_config.exchange = args.exchange
    rabbitmq_server_config.timeout = timeout
    rabbitmq_server_config.retries = retries
    # Create the Monitor
    monitor_builder = MonitorBuilder(args.framework, signal_flags)
    try:
        monitor = monitor_builder.build_monitor()
    except FrameworkError:
        logging.critical(f"Runtime monitoring process ABORTED.")
    else:
        # Starts the monitor thread
        monitor.start()
        # Waiting for the verification process to finish, either naturally or manually.
        monitor.join()
        # Signal the main loop to exit
        wx.CallAfter(wx.GetApp().ExitMainLoop)


if __name__ == "__main__":
    app = wx.App()
    main()
    app.MainLoop()
