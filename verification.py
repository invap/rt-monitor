# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

import logging
import sys
import threading

from toml.decoder import TomlDecodeError

from errors.errors import FormulaError, AbortRun, FrameworkFileError, ReportsFileError
from errors.variable_errors import UndeclaredComponentVariable, UnknownVariableClass
from logging_configuration import LoggingLevel, LoggingDestination
from monitor import Monitor
from framework.process.framework import Framework


class Verification:
    def __init__(self, monitoring_panel):
        super().__init__()
        self._monitor = None
        self._reports_map = None
        self._monitoring_panel = monitoring_panel

    def load_framework(self, framework_file):
        try:
            framework = Framework(framework_file, True)
        except TomlDecodeError as e:
            logging.error(f"TOML error in file: {framework_file}, line: {e.lineno}, column: {e.colno} - [ {e.msg} ].")
            raise FrameworkFileError(framework_file)
        except FormulaError as e:
            logging.error(f"Variables for formula [ {e.get_formula()} ] have not been declared.")
            raise FrameworkFileError(framework_file)
        except UndeclaredComponentVariable as e:
            logging.error(f"The variables [ {e.variable_names()} ] is not declared in any component.")
            raise FrameworkFileError(framework_file)
        try:
            monitor = Monitor(framework.process(), framework.components())
        except UnknownVariableClass as e:
            logging.error(f"The variable class [ {e.variable_class()} ] of variable [ {e.variable_names()} ] is unknown.")
            raise FrameworkFileError(framework_file)
        self._monitor = monitor

    def load_event_reports(self, reports_list_file):
        reports_map = {}
        try:
            file = open(reports_list_file, "r")
        except FileNotFoundError as e:
            logging.error(f"Event reports list file [ {e.filename} ] not found.")
            raise ReportsFileError(reports_list_file)
        try:
            for line in file:
                split_line = line.strip().split(",")
                device_name = split_line[0]
                reports_map[device_name] = open(split_line[1], "r")
        except FileNotFoundError as e:
            logging.error(f"Event report file [ {e.filename} ] not found.")
            raise ReportsFileError(reports_list_file)
        if "main" not in reports_map:
            logging.error(f"Main event report file not found.")
            raise ReportsFileError(reports_list_file)
        else:
            self._reports_map = reports_map
            amount_of_events = len(self._reports_map["main"].readlines())
            self._reports_map["main"].seek(0)
            self._monitoring_panel._amount_of_events_to_verify = amount_of_events
            self._monitoring_panel.amount_of_events_to_verify_text_label.SetLabel(
                self._monitoring_panel.amount_of_events_to_verify_label()
            )
            self._monitoring_panel.progress_bar.SetRange(self._monitoring_panel._amount_of_events_to_verify)

    def run(
        self,
        logging_destination,
        logging_level,
        pause_event,
        stop_event,
        monitoring_panel,
    ):
        Verification._set_up_logging()
        Verification._configure_logging_destination(logging_destination)
        Verification._configure_logging_level(logging_level)

        event_processed_callback = monitoring_panel.update_amount_of_processed_events
        monitor_thread = threading.Thread(
            target=self._monitor.run,
            args=[self._reports_map, pause_event, stop_event, event_processed_callback],
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


