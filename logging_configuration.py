import logging
from enum import IntEnum, StrEnum


class LoggingLevel(IntEnum):
    INFO = logging.INFO
    PROPERTY_ANALYSIS = logging.INFO + 5
    WARNING = logging.WARNING
    ERROR = logging.ERROR


class LoggingDestination(StrEnum):
    CONSOLE = "Consola"
    FILE = "Archivo"

    @classmethod
    def all(cls):
        return [cls.CONSOLE, cls.FILE]
