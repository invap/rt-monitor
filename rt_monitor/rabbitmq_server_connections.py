# Copyright (c) 2025 Carlos Gustavo Lopez Pombo, clpombo@gmail.com
# Copyright (c) 2025 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Lopez-Pombo-Commercial

from rt_rabbitmq_wrapper.rabbitmq_utility import RabbitMQ_server_connection

# Singleton instance shared globally
rabbitmq_event_server_connection = RabbitMQ_server_connection()
rabbitmq_result_log_server_connection = RabbitMQ_server_connection()