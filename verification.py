import importlib
import logging
import os
import shutil
import sys
import threading

from workflow_runtime_verification.monitor import Monitor
from workflow_runtime_verification.specification.workflow_specification import (
    WorkflowSpecification,
)


class Verification:
    @classmethod
    def new_for_workflow_in_file(cls, specification_path):
        specification_directory = cls._unpack_specification_file(specification_path)

        workflow_specification = cls._read_workflow_specification_from(
            specification_directory
        )
        hardware_specification = cls._read_hardware_specification_from(
            specification_directory
        )

        return cls(workflow_specification, hardware_specification)

    def __init__(self, workflow_specification, hardware_specification):
        super().__init__()
        self._monitor = Monitor(workflow_specification, hardware_specification)

    def run_for_report(
        self, event_report_path, pause_event, stop_event, simulation_panel
    ):
        self._set_up()

        event_report_file = open(event_report_path, "r")

        monitor_thread = threading.Thread(
            target=self._monitor.run,
            args=[event_report_file, pause_event, stop_event],
        )

        application_thread = threading.Thread(
            target=simulation_panel.run_verification, args=[monitor_thread]
        )
        application_thread.start()

    def stop_hardware_simulation(self):
        self._monitor.stop_hardware_simulation()

    def _set_up(self):
        self._set_up_logging()

    def _set_up_logging(self):
        self._configure_logging()

    def _configure_logging(self):
        logging.basicConfig(
            stream=sys.stdout,
            level=logging.INFO,
            datefmt="%d/%m/%Y %H:%M:%S",
            format="%(asctime)s : [%(name)s:%(levelname)s] - %(message)s",
            encoding="utf-8",
        )
        # log_dest = "FILE" : file destination
        # log_dest = "VISUAL" : Window box destination
        # log_dest = "STDOUT" : Standard output destination
        # match logging_cfg.log_dest:
        #     case "FILE":
        #         logging.basicConfig(
        #             filename=logging_cfg.filename + ".log",
        #             filemode="w",
        #             level=logging_cfg.level,
        #             datefmt="%d/%m/%Y %H:%M:%S",
        #             format="%(asctime)s : [%(name)s:%(levelname)s] - %(message)s",
        #             encoding="utf-8",
        #         )
        #     case "VISUAL":
        #         logging.basicConfig(
        #             stream=sys.stdout,
        #             level=logging_cfg.level,
        #             datefmt="%d/%m/%Y %H:%M:%S",
        #             format="%(asctime)s : [%(name)s:%(levelname)s] - %(message)s",
        #             encoding="utf-8",
        #         )
        #     case "STDOUT":
        #         logging.basicConfig(
        #             stream=sys.stdout,
        #             level=logging_cfg.level,
        #             datefmt="%d/%m/%Y %H:%M:%S",
        #             format="%(asctime)s : [%(name)s:%(levelname)s] - %(message)s",
        #             encoding="utf-8",
        #         )
        #     case _:
        #         logging.basicConfig(
        #             stream=sys.stdout,
        #             level=logging_cfg.level,
        #             datefmt="%d/%m/%Y %H:%M:%S",
        #             format="%(asctime)s : [%(name)s:%(levelname)s] - %(message)s",
        #             encoding="utf-8",
        #         )

    @classmethod
    def _unpack_specification_file(cls, file_path):
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

    @classmethod
    def _read_workflow_specification_from(cls, specification_directory):
        file_name = "workflow.desc"
        path = os.path.join(specification_directory, file_name)

        file = open(path, "r")
        return WorkflowSpecification.new_from_open_file(file)

    @classmethod
    def _read_hardware_specification_from(cls, specification_directory):
        file_name = "hardware.desc"
        path = os.path.join(specification_directory, file_name)

        file = open(path, "r")
        return cls._new_hardware_map_from_open_file(file)

    @classmethod
    def _new_hardware_map_from_open_file(cls, hardware_file):
        hardware_map = {}

        for line in hardware_file:
            split_line = line.split(",")

            device_name = split_line[0]

            component_class_path = split_line[1].strip()
            split_component_class_path = component_class_path.rsplit(".", 1)
            component_module = importlib.import_module(split_component_class_path[0])
            component_class = getattr(component_module, split_component_class_path[1])

            hardware_map[device_name] = component_class()

        return hardware_map