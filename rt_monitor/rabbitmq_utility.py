# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

import logging

import pika
from pika.exceptions import (
    AMQPConnectionError,
    ProbableAuthenticationError,
    ProbableAccessDeniedError,
    IncompatibleProtocolError,
    ChannelClosed,
    ConnectionClosed
)


class RabbitMQ_server_config:
    def __init__(self):
        self.host = None
        self.port = None
        self.user = None
        self.password = None
        self.exchange = None


class RabbitMQ_server_connection:
    def __init__(self):
        self.connection = None
        self.channel = None
        self.exchange = None
        self.queue_name = None


class RabbitMQError(Exception):
    def __init__(self):
        super().__init__("RabbitMQ server error.")


def rabbitmq_connect_to_server(rabbitmq_server_config):
    # Connection parameters with CLI arguments
    credentials = pika.PlainCredentials(rabbitmq_server_config.user, rabbitmq_server_config.password)
    parameters = pika.ConnectionParameters(
        host=rabbitmq_server_config.host,
        port=rabbitmq_server_config.port,
        credentials=credentials,
        connection_attempts=5,
        retry_delay=3,
        heartbeat=0
    )
    # Setting up the RabbitMQ connection
    try:
        connection = pika.BlockingConnection(parameters)
    except IncompatibleProtocolError as e:
        logging.error(f"Protocol version at RabbitMQ server at {rabbitmq_server_config.host}:{rabbitmq_server_config.port} error: {e}.")
        raise RabbitMQError()
    except ProbableAuthenticationError as e:
        logging.error(f"Authentication to RabbitMQ server at {rabbitmq_server_config.host}:{rabbitmq_server_config.port} failed with user {rabbitmq_server_config.user} and password {rabbitmq_server_config.password}: {e}.")
        raise RabbitMQError()
    except ProbableAccessDeniedError as e:
        logging.error(f"User {rabbitmq_server_config.user} lacks access permissions to RabbitMQ server at {rabbitmq_server_config.host}:{rabbitmq_server_config.port}: {e}.")
        raise RabbitMQError()
    except AMQPConnectionError as e:
        logging.error(f"Connection to RabbitMQ server at {rabbitmq_server_config.host}:{rabbitmq_server_config.port} failed: {e}.")
        raise RabbitMQError()
    except TypeError as e:
        logging.error(f"Invalid argument types: {e}.")
        raise RabbitMQError()
    logging.info(f"Connection to RabbitMQ server at {rabbitmq_server_config.host}:{rabbitmq_server_config.port} established.")
    # Setting up the RabbitMQ channel and exchange
    try:
        # Declare RabbitMQ connection channel
        rabbitmq_channel = connection.channel()
        # Declare exchange for the RabbitMQ connection channel
        rabbitmq_channel.exchange_declare(
            exchange=rabbitmq_server_config.exchange,
            exchange_type='fanout',
            auto_delete=True,
            durable=False
        )
    except ChannelClosed as e:
        logging.error(f"Channel closed: {e}.")
        raise RabbitMQError()
    except ConnectionClosed as e:
        logging.error(f"Unexpected connection loss during operation: {e}.")
        raise RabbitMQError()
    except TypeError as e:
        logging.error(f"Invalid argument types: {e}.")
        raise RabbitMQError()
    logging.info(f"Channel and exchange {rabbitmq_server_config.exchange} created at RabbitMQ server at {rabbitmq_server_config.host}:{rabbitmq_server_config.port}.")
    return connection, rabbitmq_channel


def rabbitmq_declare_queue(rabbitmq_server_config, channel, routing_key):
    # Declare queue
    try:
        result = channel.queue_declare(
            queue='',  # Let RabbitMQ generate unique name
            exclusive=True,
            durable=False
        )
        queue_name = result.method.queue
    except ChannelClosed as e:
        logging.error(f"Channel closed: {e}.")
        raise RabbitMQError()
    except ConnectionClosed as e:
        logging.error(f"Unexpected connection loss during operation: {e}.")
        raise RabbitMQError()
    except TypeError as e:
        logging.error(f"Invalid argument types: {e}.")
        raise RabbitMQError()
    # Bind queue
    try:
        channel.queue_bind(
            exchange=rabbitmq_server_config.exchange,
            queue=queue_name,
            routing_key=routing_key
        )
    except ChannelClosed as e:
        logging.error(f"Binding violates server rules: {e}.")
        raise RabbitMQError()
    except ConnectionClosed as e:
        logging.error(f"Connection lost during binding operation: {e}.")
        raise RabbitMQError()
    except ValueError as e:
        logging.error(f"Missing required arguments: {e}.")
        raise RabbitMQError()
    except TypeError as e:
        logging.error(f"Invalid argument types: {e}.")
        raise RabbitMQError()
    else:
        logging.info(f"Queue {queue_name} created and bound to {rabbitmq_server_config.exchange} at RabbitMQ server at {rabbitmq_server_config.host}:{rabbitmq_server_config.port} established.")
        return queue_name

def setup_rabbitmq(rabbitmq_server_config, routing_key):
    # Full RabbitMQ setup: connection, queue, binding
    try:
        connection, channel = rabbitmq_connect_to_server(rabbitmq_server_config)
    except RabbitMQError:
        logging.critical(f"RabbitMQ connection or channel setup failed.")
        raise RabbitMQError()
    # Declare and bind queue
    try:
        queue_name = rabbitmq_declare_queue(rabbitmq_server_config, channel, routing_key)
    except RabbitMQError:
        logging.critical(f"Queue declaration at RabbitMQ failed.")
        raise RabbitMQError()
    return connection, channel, queue_name

