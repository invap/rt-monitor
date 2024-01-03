import logging
from enum import IntEnum, StrEnum


class LoggingLevel(IntEnum):
    INFO = logging.INFO
    PROPERTY_ANALYSIS = logging.INFO + 5
    WARNING = logging.WARNING
    ERROR = logging.ERROR


class LoggingDestination(StrEnum):
    WINDOW = "Ventana"
    CONSOLE = "Consola"
    FILE = "Archivo"

    @classmethod
    def all(cls):
        return [cls.WINDOW, cls.CONSOLE, cls.FILE]
