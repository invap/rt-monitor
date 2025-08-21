# Copyright (c) 2025 Carlos Gustavo Lopez Pombo, clpombo@gmail.com
# Copyright (c) 2025 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Lopez-Pombo-Commercial

import tomllib
import logging
# Create a logger for the monitor builder component
logger = logging.getLogger(__name__)

from rt_rabbitmq_wrapper.rabbitmq_utility import (
    RabbitMQ_server_incoming_connection,
    RabbitMQ_server_outgoing_connection,
    RabbitMQError,
    RabbitMQ_server_info
)


# Singleton instance shared globally
rabbitmq_dispatch_server_connection = None
rabbitmq_event_server_connection = None
rabbitmq_result_log_server_connection = None


# Errors:
# -2: RabbitMQ server setup error
def build_rabbitmq_server_connections(file_path):
    global rabbitmq_event_server_connection, rabbitmq_result_log_server_connection, rabbitmq_dispatch_server_connection
    try:
        f = open(file_path, "rb")
    except FileNotFoundError:
        logger.error(f"RabbitMQ infrastructure configuration file [ {file_path} ] not found.")
        exit(-2)
    except PermissionError:
        logger.error(f"Permissions error opening file [ {file_path} ].")
        exit(-2)
    except IsADirectoryError:
        logger.error(f"[ {file_path} ] is a directory and not a file.")
        exit(-2)
    try:
        rabbitmq_exchange_dict = tomllib.load(f)
    except tomllib.TOMLDecodeError:
        logger.error(f"TOML decoding of file [ {file_path} ] failed.")
        exit(-2)
    # Configure dispatch exchange
    try:
        dispatch_conf_dict = rabbitmq_exchange_dict["exchanges"]["dispatch"]
    except KeyError:
        host, port, user, password, connection_attempts, retry_delay, exchange, exchange_type = "localhost", 5672, "guest", "guest", 5, 3, "dispatch_exchange", "direct"
    else:
        host = dispatch_conf_dict["host"] if "host" in dispatch_conf_dict else "localhost"
        port = dispatch_conf_dict["port"] if "port" in dispatch_conf_dict else 5672
        user = dispatch_conf_dict["user"] if "user" in dispatch_conf_dict else "guest"
        password = dispatch_conf_dict["password"] if "password" in dispatch_conf_dict else "guest"
        connection_attempts = dispatch_conf_dict["connection_attempts"] if "connection_attempts" in dispatch_conf_dict else 5
        retry_delay = dispatch_conf_dict["retry_delay"] if "retry_delay" in dispatch_conf_dict else 3
        exchange = dispatch_conf_dict["name"] if "name" in dispatch_conf_dict else "dispatch_exchange"
        exchange_type = dispatch_conf_dict["exchange_type"] if "exchange_type" in dispatch_conf_dict else "direct"
    finally:
        server_info = RabbitMQ_server_info(host, port, user, password)
        rabbitmq_dispatch_server_connection = RabbitMQ_server_incoming_connection(
            server_info,
            connection_attempts,
            retry_delay,
            exchange,
            exchange_type
        )
    # Connect to the RabbitMQ events server
    try:
        rabbitmq_dispatch_server_connection.connect()
    except RabbitMQError:
        logger.error(f"RabbitMQ framework server connection error.")
        exit(-2)
    # Configure events exchange
    try:
        events_conf_dict = rabbitmq_exchange_dict["exchanges"]["events"]
    except KeyError:
        host, port, user, password, connection_attempts, retry_delay, exchange, exchange_type = "localhost", 5672, "guest", "guest", 5, 3, "events_exchange", "fanout"
    else:
        host = events_conf_dict["host"] if "host" in events_conf_dict else "localhost"
        port = events_conf_dict["port"] if "port" in events_conf_dict else 5672
        user = events_conf_dict["user"] if "user" in events_conf_dict else "guest"
        password = events_conf_dict["password"] if "password" in events_conf_dict else "guest"
        connection_attempts = events_conf_dict["connection_attempts"] if "connection_attempts" in events_conf_dict else 5
        retry_delay = events_conf_dict["retry_delay"] if "retry_delay" in events_conf_dict else 3
        exchange = events_conf_dict["name"] if "name" in events_conf_dict else "events_exchange"
        exchange_type = events_conf_dict["exchange_type"] if "exchange_type" in events_conf_dict else "fanout"
    finally:
        server_info = RabbitMQ_server_info(host, port, user, password)
        rabbitmq_event_server_connection = RabbitMQ_server_incoming_connection(
            server_info,
            connection_attempts,
            retry_delay,
            exchange,
            exchange_type
        )
    # Connect to the RabbitMQ events server
    try:
        rabbitmq_event_server_connection.connect()
    except RabbitMQError:
        logger.error(f"RabbitMQ events server connection error.")
        exit(-2)
    # Configure results log exchange
    try:
        results_log_conf_dict = rabbitmq_exchange_dict["exchanges"]["results_log"]
    except KeyError:
        host, port, user, password, connection_attempts, retry_delay, exchange, exchange_type = "localhost", 5672, "guest", "guest", 5, 3, "results_log_exchange", "fanout"
    else:
        host = results_log_conf_dict["host"] if "host" in results_log_conf_dict else "localhost"
        port = results_log_conf_dict["port"] if "port" in results_log_conf_dict else 5672
        user = results_log_conf_dict["user"] if "user" in results_log_conf_dict else "guest"
        password = results_log_conf_dict["password"] if "password" in results_log_conf_dict else "guest"
        connection_attempts = results_log_conf_dict["connection_attempts"] if "connection_attempts" in results_log_conf_dict else 5
        retry_delay = results_log_conf_dict["retry_delay"] if "retry_delay" in results_log_conf_dict else 3
        exchange = results_log_conf_dict["name"] if "name" in results_log_conf_dict else "results_log_exchange"
        exchange_type = results_log_conf_dict["exchange_type"] if "exchange_type" in results_log_conf_dict else "fanout"
    finally:
        server_info = RabbitMQ_server_info(host, port, user, password)
        rabbitmq_result_log_server_connection = RabbitMQ_server_outgoing_connection(
            server_info,
            connection_attempts,
            retry_delay,
            exchange,
            exchange_type
        )
    # Connect to the RabbitMQ results log server
    try:
        rabbitmq_result_log_server_connection.connect()
    except RabbitMQError:
        logger.error(f"RabbitMQ results log server connection error.")
        exit(-2)
