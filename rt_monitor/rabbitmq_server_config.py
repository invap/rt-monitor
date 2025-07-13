# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

class RabbitMQ_server_config:
    def __init__(self):
        self.host = None
        self.port = None
        self.user = None
        self.password = None
        self.exchange = None
        self.timeout = None
        self.retries = None

# Singleton instance to share globally
rabbitmq_server_config = RabbitMQ_server_config()