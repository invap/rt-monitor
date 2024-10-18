# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

import logging
import sys
import threading

from toml.decoder import TomlDecodeError

from logging_configuration import LoggingLevel, LoggingDestination
from workflow_runtime_verification.errors import AbortRun, UndeclaredComponentVariable, \
    UnknownVariableClass, FormulaError
from monitor import Monitor
from workflow_runtime_verification.specification.TOMLParser import TOMLParser


class Verification:
    def __init__(self, workflow_specification, components_specification):
        super().__init__()
        Verification._set_up_logging()
        try:
            self._monitor = Monitor(workflow_specification, components_specification)
        except UndeclaredComponentVariable as e:
            logging.critical(f"The variables [ {e.get_varnames()} ] is not declared in any component.")
            raise AbortRun()
        except UnknownVariableClass as e:
            logging.critical(f"The variable class [ {e.get_varclass()} ] of variable [ {e.get_varnames()} ] is unknown.")
            raise AbortRun()

    def run_for_report(
        self,
        event_report_path,
        logging_destination,
        logging_level,
        pause_event,
        stop_event,
        monitoring_panel,
    ):
        self._configure_logging_destination(logging_destination)
        self._configure_logging_level(logging_level)
        logs_map = {}
        try:
            with open(event_report_path, "r") as file:
                for line in file:
                    split_line = line.strip().split(",")
                    device_name = split_line[0]
                    logs_map[device_name] = open(split_line[1], "r")
        except FileNotFoundError:
            logging.critical(f"A necessary file is missing.")

        event_processed_callback = monitoring_panel.update_amount_of_processed_events
        monitor_thread = threading.Thread(
            target=self._monitor.run,
            args=[logs_map, pause_event, stop_event, event_processed_callback],
        )
        application_thread = threading.Thread(
            target=monitoring_panel.run_verification, args=[monitor_thread]
        )
        try:
            application_thread.start()
        except AbortRun():
            logging.critical(f"Runtime monitoring process ABORTED.")

    def stop_component_monitoring(self):
        self._monitor.stop_component_monitoring()

    @staticmethod
    def _set_up_logging():
        logging.addLevelName(LoggingLevel.PROPERTY_ANALYSIS, "PROPERTY_ANALYSIS")
        logging.basicConfig(
            stream=sys.stdout,
            level=Verification._default_logging_level(),
            datefmt=Verification._date_logging_format(),
            format=Verification._logging_format(),
            encoding="utf-8",
        )

    @staticmethod
    def _configure_logging_destination(logging_destination):
        logging.getLogger().handlers.clear()
        formatter = logging.Formatter(
            Verification._logging_format(), datefmt=Verification._date_logging_format()
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

    @staticmethod
    def _configure_logging_level(logging_level):
        logging.getLogger().setLevel(logging_level)

    @staticmethod
    def _default_logging_level():
        return LoggingLevel.INFO

    @staticmethod
    def _date_logging_format():
        return "%d/%m/%Y %H:%M:%S"

    @staticmethod
    def _logging_format():
        return "%(asctime)s : [%(name)s:%(levelname)s] - %(message)s"

    @staticmethod
    def new_from_toml_file(toml_specification_file):
        try:
            parser = TOMLParser(toml_specification_file)
            return Verification(parser.workflow(), parser.components())
        except TomlDecodeError as e:
            logging.error(f"TOML error in file: {toml_specification_file}, line: {e.lineno}, column: {e.colno} - [ {e.msg} ].")
        except FormulaError as e:
            logging.error(f"Variables for formula [ {e.get_formula()} ] have not been declared.")
