# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

import logging
from enum import IntEnum, StrEnum


class LoggingLevel(IntEnum):
    INFO = logging.INFO
    ANALYSIS = logging.INFO + 5
    WARNING = logging.WARNING
    ERROR = logging.ERROR


class LoggingDestination(StrEnum):
    CONSOLE = "Standard output"
    FILE = "File (log.txt)"

    @classmethod
    def all(cls):
        return [cls.CONSOLE, cls.FILE]
