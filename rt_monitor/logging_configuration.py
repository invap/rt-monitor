# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

import logging
import sys
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


def _set_up_logging():
    logging.addLevelName(LoggingLevel.ANALYSIS, "ANALYSIS")
    logging.basicConfig(
        stream=sys.stdout,
        level=_default_logging_level(),
        datefmt=_date_logging_format(),
        format=_logging_format(),
        encoding="utf-8",
    )


def _configure_logging_destination(logging_destination, log_file=''):
    logging.getLogger().handlers.clear()
    formatter = logging.Formatter(
        _logging_format(), datefmt=_date_logging_format()
    )
    match logging_destination:
        case LoggingDestination.FILE:
            if log_file == '':
                handler = logging.FileHandler("log.txt", encoding="utf-8")
            else:
                handler = logging.FileHandler(log_file, encoding="utf-8")
        case _:
            handler = logging.StreamHandler(sys.stdout)
    handler.setFormatter(formatter)
    logging.getLogger().addHandler(handler)


def _configure_logging_level(logging_level):
    logging.getLogger().setLevel(logging_level)


def _default_logging_level():
    return LoggingLevel.INFO


def _date_logging_format():
    return "%d/%m/%Y %H:%M:%S"


def _logging_format():
    return "%(asctime)s : [%(name)s:%(levelname)s] - %(message)s"
