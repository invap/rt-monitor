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
    ConnectionClosed,
    ChannelWrongStateError,
    AMQPChannelError
)


class RabbitMQ_server_config:
    def __init__(self):
        self.host = None
        self.port = None
        self.user = None
        self.password = None


class RabbitMQ_exchange_config:
    def __init__(self):
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


def connect_to_server(rabbitmq_server_config):
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
    except IncompatibleProtocolError:
        logging.error(f"Protocol version at RabbitMQ server at {rabbitmq_server_config.host}:{rabbitmq_server_config.port} error.")
        raise RabbitMQError()
    except ProbableAuthenticationError:
        logging.error(f"Authentication to RabbitMQ server at {rabbitmq_server_config.host}:{rabbitmq_server_config.port} failed with user {rabbitmq_server_config.user} and password {rabbitmq_server_config.password}.")
        raise RabbitMQError()
    except ProbableAccessDeniedError:
        logging.error(f"User {rabbitmq_server_config.user} lacks access permissions to RabbitMQ server at {rabbitmq_server_config.host}:{rabbitmq_server_config.port}.")
        raise RabbitMQError()
    except AMQPConnectionError:
        logging.error(f"Connection to RabbitMQ server at {rabbitmq_server_config.host}:{rabbitmq_server_config.port} failed.")
        raise RabbitMQError()
    except TypeError:
        logging.error(f"Invalid argument types.")
        raise RabbitMQError()
    else:
        logging.info(f"Connection to RabbitMQ server at {rabbitmq_server_config.host}:{rabbitmq_server_config.port} established.")
        return connection

def connect_to_channel_exchange(rabbitmq_server_config, rabbitmq_exchange_config, connection):
    # Setting up the RabbitMQ channel and exchange
    try:
        # Declare RabbitMQ connection channel
        rabbitmq_channel = connection.channel()
        # Declare exchange for the RabbitMQ connection channel
        rabbitmq_channel.exchange_declare(
            exchange=rabbitmq_exchange_config.exchange,
            exchange_type='fanout',
            auto_delete=True,
            durable=False
        )
    except ChannelClosed:
        logging.error(f"Channel closed.")
        raise RabbitMQError()
    except ConnectionClosed:
        logging.error(f"Unexpected connection loss during operation.")
        raise RabbitMQError()
    except TypeError:
        logging.error(f"Invalid argument types.")
        raise RabbitMQError()
    else:
        logging.info(f"Channel and exchange {rabbitmq_exchange_config.exchange} created at RabbitMQ server at {rabbitmq_server_config.host}:{rabbitmq_server_config.port}.")
        return rabbitmq_channel


def declare_queue(rabbitmq_server_config, rabbitmq_exchange_config, channel, routing_key):
    # Declare queue
    try:
        result = channel.queue_declare(
            queue='',  # Let RabbitMQ generate unique name
            exclusive=True,
            durable=False
        )
        queue_name = result.method.queue
    except ChannelClosed:
        logging.error(f"Channel closed.")
        raise RabbitMQError()
    except ConnectionClosed:
        logging.error(f"Unexpected connection loss during operation.")
        raise RabbitMQError()
    except TypeError:
        logging.error(f"Invalid argument types.")
        raise RabbitMQError()
    # Bind queue
    try:
        channel.queue_bind(
            exchange=rabbitmq_exchange_config.exchange,
            queue=queue_name,
            routing_key=routing_key
        )
    except ChannelClosed:
        logging.error(f"Binding violates server rules.")
        raise RabbitMQError()
    except ConnectionClosed:
        logging.error(f"Connection lost during binding operation.")
        raise RabbitMQError()
    except ValueError:
        logging.error(f"Missing required arguments.")
        raise RabbitMQError()
    except TypeError:
        logging.error(f"Invalid argument types.")
        raise RabbitMQError()
    logging.info(f"Queue {queue_name} created and bound to exchange {rabbitmq_exchange_config.exchange} at RabbitMQ server at {rabbitmq_server_config.host}:{rabbitmq_server_config.port}.")
    return queue_name


def get_message(rabbitmq_server_connection):
    try:
        method, properties, body = rabbitmq_server_connection.channel.basic_get(
            queue=rabbitmq_server_connection.queue_name,
            auto_ack=False
        )
    except AMQPConnectionError:  # Raised if the connection is closed or lost during the operation.
        logging.error(f"Connection closed or lost during message reception.")
        raise RabbitMQError()
    except ChannelClosed:  # Subclass of AMQPChannelError: Triggered if RabbitMQ closes the channel mid - operation(e.g., due to an error).
        logging.error(f"Channel closed during message reception.")
        raise RabbitMQError()
    except ChannelWrongStateError:  # Occurs if the channel is in an unusable state(e.g., recovering).
        logging.error(f"Channel is in an unusable state.")
        raise RabbitMQError()
    except AMQPChannelError:  # Raised if the channel is closed or invalid when calling basic_get.
        logging.error(f"Channel is closed or invalid when calling basic_get.")
        raise RabbitMQError()
    except TypeError:  # Raised for invalid arguments(e.g., non - string queue name, empty queue name).
        logging.error(f"Invalid argument type.")
        raise RabbitMQError()
    except ValueError:
        logging.error(f"Invalid argument value.")
        raise RabbitMQError()
    else:
        return method, properties, body


def ack_message(rabbitmq_server_connection, delivery_tag):
    try:
        rabbitmq_server_connection.channel.basic_ack(delivery_tag)
    except AMQPConnectionError:  # Raised if the connection is closed or lost during acknowledgement.
        logging.error(f"Connection closed or lost during acknowledgement.")
        raise RabbitMQError()
    except ChannelClosed:  # Raised if: The channel is closed or invalid, RabbitMQ closes the channel due to an error(e.g., invalid delivery_tag)
        logging.error(f"Channel closed during acknowledgement.")
        raise RabbitMQError()
    except AMQPChannelError:
        logging.error(f"Channel is closed or invalid when calling basic_ack.")
        raise RabbitMQError()
    except TypeError:  # Raised if arguments have invalid types(e.g., delivery_tag is a string).
        logging.error(f"Invalid argument type.")
        raise RabbitMQError()
    except ValueError:  # Raised if the delivery_tag is: Negative, Zero, A non-integer value
        logging.error(f"Invalid argument value.")
        raise RabbitMQError()


def publish_message(rabbitmq_server_connection, routing_key, body, properties=None):
    try:
        rabbitmq_server_connection.channel.basic_publish(
            exchange=rabbitmq_server_connection.exchange,
            routing_key=routing_key,
            body=body,
            properties=properties
        )
    except AMQPConnectionError:  # Raised if the connection is closed or lost during the operation.
        logging.error(f"Connection closed or lost during message publishing.")
        raise RabbitMQError()
    except ChannelClosed:  # Subclass of AMQPChannelError: Triggered if RabbitMQ closes the channel mid - operation(e.g., due to an error).
        logging.error(f"Channel closed during message publishing.")
        raise RabbitMQError()
    except AMQPChannelError:  # Raised if the channel is closed or invalid when calling basic_publish.
        logging.error(f"Channel is closed or invalid when calling basic_publish.")
        raise RabbitMQError()
    except TypeError:  # Raised for invalid arguments(e.g., non - string queue name, empty queue name).
        logging.error(f"Invalid argument type.")
        raise RabbitMQError()
    except ValueError:
        logging.error(f"Invalid argument value.")
        raise RabbitMQError()
