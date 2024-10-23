# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

import logging
import sys

from errors.monitor_errors import FrameworkError, MonitorConstructionError, ReportListError, AbortRun
from logging_configuration import LoggingLevel, LoggingDestination
from monitor import Monitor


def _set_up_logging():
    logging.addLevelName(LoggingLevel.ANALYSIS, "ANALYSIS")
    logging.basicConfig(
        stream=sys.stdout,
        level=_default_logging_level(),
        datefmt=_date_logging_format(),
        format=_logging_format(),
        encoding="utf-8",
    )


def _configure_logging_destination(logging_destination):
    logging.getLogger().handlers.clear()
    formatter = logging.Formatter(
        _logging_format(), datefmt=_date_logging_format()
    )
    match logging_destination:
        case LoggingDestination.FILE:
            handler = logging.FileHandler(
                "sandbox/rt-monitor-example-app/log.txt", encoding="utf-8"
            )
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


def main():
    # Building argument map
    argument_map = {}
    for argument in range(1, len(sys.argv)):
        if sys.argv[argument].startswith("--framework="):
            if "framework" in argument_map:
                print("Multiple --framework argument.", file=sys.stderr)
                exit(-11)
            else:
                split_argument = sys.argv[argument].split("=")
                argument_map["framework"] = split_argument[1]
        elif sys.argv[argument].startswith("--reports="):
            if "reports" in argument_map:
                print("Multiple --reports argument.", file=sys.stderr)
                exit(-12)
            else:
                split_argument = sys.argv[argument].split("=")
                argument_map["reports"] = split_argument[1]
        elif sys.argv[argument] == "--log-file":
            if "log-file" in argument_map:
                print("Multiple --log-file argument.", file=sys.stderr)
                exit(-13)
            else:
                argument_map["log-file"] = ""
        elif sys.argv[argument].startswith("--log-level="):
            if "log-level" in argument_map:
                print("Multiple --log-level argument.", file=sys.stderr)
                exit(-14)
            else:
                split_argument = sys.argv[argument].split("=")
                argument_map["log-level"] = split_argument[1]
        else:
            print("Erroneous argument.", file=sys.stderr)
            exit(-1)
    if "framework" not in argument_map:
        print("Missing --framework argument.", file=sys.stderr)
        exit(-2)
    if "reports" not in argument_map:
        print("Missing --reports argument.", file=sys.stderr)
        exit(-3)
    # Configuring logger
    _set_up_logging()
    # Choosing logging destination
    if "log-file" in argument_map:
        logging_destination = LoggingDestination.FILE
    else:
        logging_destination = LoggingDestination.CONSOLE
    _configure_logging_destination(logging_destination)
    # Choosing logging level
    if "log-level" in argument_map:
        match argument_map["log-level"]:
            case "all":
                logging_level = LoggingLevel.INFO
            case "analysis":
                logging_level = LoggingLevel.ANALYSIS
            case "warnings":
                logging_level = LoggingLevel.WARNING
            case "errors":
                logging_level = LoggingLevel.ERROR
            case _:
                print("Erroneous logging level.", file=sys.stderr)
                exit(-141)
    else:
        logging_level = LoggingLevel.ANALYSIS
    _configure_logging_level(logging_level)
    # Create and run monitor
    try:
        monitor = Monitor.new_from_files(logging_destination, logging_level, argument_map["framework"],
                                         argument_map["reports"], False)
    except FrameworkError:
        logging.critical(f"Runtime monitoring process ABORTED.")
    except ReportListError:
        logging.critical(f"Runtime monitoring process ABORTED..")
    except MonitorConstructionError:
        logging.critical(f"Runtime monitoring process ABORTED..")
    else:
        try:
            monitor.run()
        except AbortRun():
            logging.critical(f"Runtime monitoring process ABORTED.")


if __name__ == "__main__":
    main()
