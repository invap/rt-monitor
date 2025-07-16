# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

import argparse
import logging
import signal
import threading
import wx

from rt_monitor.config import config
from rt_monitor.errors.monitor_errors import FrameworkError
from rt_monitor.logging_configuration import (
    LoggingLevel,
    LoggingDestination,
    set_up_logging,
    configure_logging_destination,
    configure_logging_level
)
from rt_monitor.monitor_builder import MonitorBuilder
from rt_monitor.rabbitmq_server_config import rabbitmq_server_config
from rt_monitor.utility import is_valid_file_with_extension_nex, is_valid_file_with_extension


def _run_verification(process_thread):
    # Starts the monitor thread
    process_thread.start()
    # Waiting for the verification process to finish, either naturally or manually.
    process_thread.join()
    # Signal the main loop to exit
    wx.CallAfter(wx.GetApp().ExitMainLoop)

# Errors:
# -1: Framework error

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
        description="Performs runtime assertion checking of events got from a RabbitMQ server with respect to a structured sequential process specification.",
        epilog="Example: python -m rt_monitor.rt_monitor_sh ssp_spec.toml --host=https://myrabbitmq.org.ar --port=5672 --user=my_user --password=my_password --log_file=output_log.txt --log_level=event --timeout=120"
    )
    parser.add_argument("framework", type=str, help="Path to the framework specification file in toml format.")
    parser.add_argument('--host', type=str, default='localhost', help='RabbitMQ server host.')
    parser.add_argument('--port', type=int, default=5672, help='RabbitMQ server port.')
    parser.add_argument('--user', default='guest', help='RabbitMQ server user.')
    parser.add_argument('--password', default='guest', help='RabbitMQ server password.')
    parser.add_argument('--exchange', type=str, default='my_exchange', help='Name of the exchange at the RabbitMQ server.')
    parser.add_argument("--log_level", type=str, choices=["debug", "event", "analysis", "info", "warnings", "errors", "critical"], default="analysis", help="Log verbose level (optional argument).")
    parser.add_argument('--log_file', help='Path to log file (optional argument).')
    parser.add_argument("--timeout", type=int, default=60, help="Timeout in seconds to wait for messages after last received message (0 = no timeout) (default = 60 seconds).")
    # Start the execution of The Runtime Monitor
    # Parse arguments
    args = parser.parse_args()
    # Set up the logging infrastructure
    # Configure logging level.
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
            logging_level = LoggingLevel.ANALYSIS
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
    logging.info(f"Log verbosity level: {logging_level}.")
    if args.log_file is None:
        logging.info("Log destination: CONSOLE.")
    else:
        if not valid_log_file:
            logging.info("Log file error. Log destination: CONSOLE.")
        else:
            logging.info(f"Log destination: FILE ({args.log_file}).")
    # Validate and normalize the framework path
    valid = is_valid_file_with_extension(args.framework, "toml")
    if not valid:
        logging.critical(f"Framework file error.")
        exit(-1)
    logging.info(f"Framework file: {args.framework}")
    # Determine timeout
    timeout = args.timeout if args.timeout >= 0 else 0
    logging.info(f"Timeout for message reception: {timeout} seconds.")
    # RabbitMQ server configuration
    rabbitmq_server_config.host = args.host
    rabbitmq_server_config.port = args.port
    rabbitmq_server_config.user = args.user
    rabbitmq_server_config.password = args.password
    rabbitmq_server_config.exchange = args.exchange
    # Other configuration
    config.timeout = timeout
    # Create the Monitor
    monitor_builder = MonitorBuilder(args.framework, signal_flags)
    try:
        monitor = monitor_builder.build_monitor()
    except FrameworkError:
        logging.critical(f"Runtime monitoring process ABORTED.")
    else:
        # Creates a thread for controlling the analysis process
        application_thread = threading.Thread(
            target=_run_verification, args=[monitor]
        )
        application_thread.start()


if __name__ == "__main__":
    app = wx.App()
    main()
    app.MainLoop()
