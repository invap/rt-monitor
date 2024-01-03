import logging
from enum import IntEnum


class LoggingLevel(IntEnum):
    INFO = logging.INFO
    PROPERTY_ANALYSIS = logging.INFO + 5
    WARNING = logging.WARNING
    ERROR = logging.ERROR
