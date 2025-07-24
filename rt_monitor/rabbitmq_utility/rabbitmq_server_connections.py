# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

from rt_monitor.rabbitmq_utility.rabbitmq_utility import RabbitMQ_server_connection

# Instance shared globally
rabbitmq_event_server_connection = RabbitMQ_server_connection()
rabbitmq_log_server_connection = RabbitMQ_server_connection()
