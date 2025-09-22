# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

import argparse
import logging

from rt_monitor.config import config
from rt_monitor.errors.monitor_errors import MonitorError
from rt_monitor.logging_configuration import (
    LoggingLevel,
    LoggingDestination,
    set_up_logging,
    configure_logging_destination,
    configure_logging_level
)
from rt_monitor.monitor import rt_monitor_runner
from rt_monitor import rabbitmq_server_connections
from rt_monitor.utility import (
    is_valid_file_with_extension_nex,
    is_valid_file_with_extension
)


# Exit codes:
# -1: Input file error
# -2: RabbitMQ configuration error
# -3: Monitor error
# -4: Unexpected error
def main():
    # Argument processing
    parser = argparse.ArgumentParser(
        prog="The Runtime Monitor",
        description="Performs runtime assertion checking of events got from a RabbitMQ server with respect to a structured sequential process specification.",
        epilog="Example: python -m rt_monitor.rt_monitor_sh path/to/spec.toml --rabbitmq_config_file=/path/to/rabbitmq_config.toml --log_file=output.log --log_level=event --timeout=120 --stop=dont"
    )
    parser.add_argument("spec_file", type=str, help='Path to the TOML file containing the analysis framework specification.')
    parser.add_argument("--rabbitmq_config_file", type=str, default='./rabbitmq_config.toml', help='Path to the TOML file containing the RabbitMQ server configuration.')
    parser.add_argument("--log_level", type=str, choices=["debug", "info", "warnings", "errors", "critical"], default="info", help="Log verbose level.")
    parser.add_argument("--log_file", help='Path to log file.')
    parser.add_argument("--timeout", type=int, default=0, help="Timeout in seconds to wait for events after last received, from the RabbitMQ server (0 = no timeout).")
    parser.add_argument("--stop", type=str, choices=["on_might_fail", "on_fail", "dont"], default="on_might_fail", help="Stop policy.")
    # Start the execution of The Runtime Monitor
    # Parse arguments
    args = parser.parse_args()
    # Set up the logging infrastructure
    # Configure logging level.
    match args.log_level:
        case "debug":
            logging_level = LoggingLevel.DEBUG
        case "info":
            logging_level = LoggingLevel.INFO
        case "warnings":
            logging_level = LoggingLevel.WARNING
        case "errors":
            logging_level = LoggingLevel.ERROR
        case "critical":
            logging_level = LoggingLevel.CRITICAL
        case _:
            logging_level = LoggingLevel.INFO
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
    # Create a logger for this component
    logger = logging.getLogger("rt_monitor.rt_monitor_sh")
    logger.info(f"Log verbosity level: {logging_level}.")
    if args.log_file is None:
        logger.info("Log destination: CONSOLE.")
    else:
        if not valid_log_file:
            logger.info("Log file error. Log destination: CONSOLE.")
        else:
            logger.info(f"Log destination: FILE ({args.log_file}).")
    # Determine timeout
    config.timeout = args.timeout if args.timeout >= 0 else 0
    logger.info(f"Timeout for message reception: {config.timeout} seconds.")
    # Determine stop policy
    config.stop = args.stop
    # Analysis framework specification file
    valid = is_valid_file_with_extension(args.spec_file, "toml")
    if not valid:
        logger.critical(f"Analysis framework specification file error.")
        exit(-1)
    logger.info(f"Analysis framework specification file: {args.spec_file}")
    # RabbitMQ infrastructure configuration
    valid = is_valid_file_with_extension(args.rabbitmq_config_file, "toml")
    if not valid:
        logger.critical(f"RabbitMQ infrastructure configuration file error.")
        exit(-2)
    logger.info(f"RabbitMQ infrastructure configuration file: {args.rabbitmq_config_file}")
    # Create RabbitMQ communication infrastructure
    rabbitmq_server_connections.build_rabbitmq_server_connections(args.rabbitmq_config_file)
    # Run the rt_monitor
    try:
        rt_monitor_runner(args.spec_file)
    except MonitorError:
        logger.critical("Monitor error.")
        exit(-3)
    except Exception as e:
        logger.critical(f"Unexpected error: {e}.")
        exit(-4)
    # Close connection to the RabbitMQ events server if it exists
    rabbitmq_server_connections.rabbitmq_event_server_connection.close()
    # Close connection to the RabbitMQ results log server if it exists
    rabbitmq_server_connections.rabbitmq_result_log_server_connection.close()
    exit(0)


if __name__ == "__main__":
    main()
 