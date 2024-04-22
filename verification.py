import importlib
import logging
import os
import shutil
import sys
import threading

from logging_configuration import LoggingLevel, LoggingDestination
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

        event_report_file = open(event_report_path, "r")

        event_processed_callback = monitoring_panel.update_amount_of_processed_events

        monitor_thread = threading.Thread(
            target=self._monitor.run,
            args=[event_report_file, pause_event, stop_event, event_processed_callback],
        )

        application_thread = threading.Thread(
            target=monitoring_panel.run_verification, args=[monitor_thread]
        )
        application_thread.start()

    def stop_component_monitoring(self):
        self._monitor.stop_component_monitoring()

    @staticmethod
    def new_for_workflow_in_file(specification_path):
        specification_directory = Verification._unpack_specification_file(specification_path)

        workflow_specification = Verification._read_workflow_specification_from(
            specification_directory
        )
        components_specification = Verification._read_components_specification_from(
            specification_directory
        )

        return Verification(workflow_specification, components_specification)

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
    def _unpack_specification_file(file_path):
        split_file_path = os.path.split(file_path)
        file_directory = split_file_path[0]
        file_name = split_file_path[1]

        file_name_without_extension = os.path.splitext(file_name)[0]
        specification_directory = os.path.join(
            file_directory, file_name_without_extension
        )

        try:
            os.mkdir(specification_directory)
        except FileExistsError:
            shutil.rmtree(specification_directory)
            os.mkdir(specification_directory)

        shutil.unpack_archive(file_path, specification_directory)
        return specification_directory

    @staticmethod
    def _read_workflow_specification_from(specification_directory):
        file_name = "workflow.desc"
        path = os.path.join(specification_directory, file_name)

        file = open(path, "r")
        return WorkflowSpecification.new_from_open_file(file)

    @staticmethod
    def _read_components_specification_from(specification_directory):
        file_name = "components.desc"
        path = os.path.join(specification_directory, file_name)

        file = open(path, "r")
        return Verification._new_component_map_from_open_file(file)

    @staticmethod
    def _new_component_map_from_open_file(component_file):
        component_map = {}

        for line in component_file:
            split_line = line.split(",")

            device_name = split_line[0]

            component_class_path = split_line[1].strip()
            split_component_class_path = component_class_path.rsplit(".", 1)
            component_module = importlib.import_module(split_component_class_path[0])
            component_class = getattr(component_module, split_component_class_path[1])

            component_map[device_name] = component_class()

        return component_map
