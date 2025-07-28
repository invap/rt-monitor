# Copyright (c) 2025 Carlos Gustavo Lopez Pombo, clpombo@gmail.com
# Copyright (c) 2025 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Lopez-Pombo-Commercial

from rt_rabbitmq_wrapper.rabbitmq_utility import RabbitMQ_server_config, RabbitMQ_exchange_config

# Singleton instance shared globally
rabbitmq_server_config = RabbitMQ_server_config()
rabbitmq_event_exchange_config = RabbitMQ_exchange_config()
rabbitmq_log_exchange_config = RabbitMQ_exchange_config()