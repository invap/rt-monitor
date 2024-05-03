import importlib
import logging
import os
import sys
import threading

from logging_configuration import LoggingLevel, LoggingDestination
from workflow_runtime_verification.errors import AbortRun, EventLogFileMissing
from workflow_runtime_verification.monitor import Monitor
from workflow_runtime_verification.specification.workflow_specification import (
    WorkflowSpecification,
)


class Verification:
    def __init__(self, workflow_specification, components_specification):
        super().__init__()
        self._monitor = Monitor(workflow_specification, components_specification)
        Verification._set_up_logging()

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
    def new_from_files(specification_path):
        try:
            workflow_specification = Verification._read_workflow_specification_from(specification_path)
            components_specification = Verification._read_components_specification_from(specification_path)
            return Verification(workflow_specification, components_specification)
        except EventLogFileMissing as e:
            logging.error(f"Missing log file [ {e.get_filename()} ].")
            raise AbortRun()

    @staticmethod
    def _read_workflow_specification_from(specification_directory):
        file_name = "workflow.desc"
        path = os.path.join(specification_directory, file_name)
        file = open(path, "r")
        return WorkflowSpecification.new_from_open_file(file)

    @staticmethod
    def _read_components_specification_from(specification_path):
        file_name = "components.desc"
        components_file = open(os.path.join(specification_path, file_name), "r")
        component_map = {}
        for line in components_file:
            split_line = line.strip().split(",")
            device_name = split_line[0]
            component_class_path = split_line[1]
            split_component_class_path = component_class_path.rsplit(".", 1)
            component_module = importlib.import_module(split_component_class_path[0])
            component_class = getattr(component_module, split_component_class_path[1])
            component_map[device_name] = component_class()
        return component_map
