# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

import logging
import tomllib

from rt_monitor.framework.framework_builder import FrameworkBuilder
from rt_monitor.monitor import Monitor
from rt_monitor.errors.monitor_errors import (
    FrameworkError,
    EventReportError
)
from rt_monitor.errors.framework_errors import FrameworkSpecificationError


class MonitorBuilder:
    framework_file = ""
    event_report_file = ""

    def __init__(self, framework_file, event_report_file):
        MonitorBuilder.framework_file = framework_file
        MonitorBuilder.event_report_file = event_report_file

    # Raises: FrameworkError(), EventLogListError(), MonitorConstructionError()
    @staticmethod
    def build_monitor():
        logging.info(f"Creating monitor with files: [ {MonitorBuilder.framework_file} ] and [ {MonitorBuilder.event_report_file} ].")
        try:
            framework_builder = FrameworkBuilder(MonitorBuilder.framework_file)
            framework = framework_builder.build_framework()
        except FrameworkSpecificationError:
            logging.error(f"Error creating framework.")
            raise FrameworkError()
        try:
            event_report = open(MonitorBuilder.event_report_file, "r")
        except FileNotFoundError:
            logging.error(f"Event report file [ {MonitorBuilder.event_report_file} ] not found.")
            raise EventReportError()
        except PermissionError:
            logging.error(f"Permissions error opening file [ {MonitorBuilder.event_report_file} ].")
            raise EventReportError()
        except IsADirectoryError:
            logging.error(f"[ {MonitorBuilder.event_report_file} ] is a directory and not a file.")
            raise EventReportError()
        # Build monitor
        logging.info(f"Creating monitor...")
        monitor = Monitor(framework, event_report)
        logging.info(f"Monitor created.")
        return monitor
