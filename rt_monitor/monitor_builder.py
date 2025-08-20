# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

import logging
# Create a logger for the monitor builder component
logger = logging.getLogger(__name__)

from rt_monitor.framework.framework_builder import FrameworkBuilder
from rt_monitor.monitor import Monitor
from rt_monitor.errors.monitor_errors import FrameworkError
from rt_monitor.errors.framework_errors import FrameworkSpecificationError


class MonitorBuilder:
    framework_file = ""
    event_report_file = ""
    signal_flags = []

    def __init__(self, framework_file, signal_flags):
        MonitorBuilder.framework_file = framework_file
        MonitorBuilder.signal_flags = signal_flags

    # Raises: FrameworkError(), EventLogListError(), MonitorConstructionError()
    @staticmethod
    def build_monitor():
        logger.info(f"Creating monitor with framework: [ {MonitorBuilder.framework_file} ].")
        try:
            framework_builder = FrameworkBuilder(MonitorBuilder.framework_file)
            framework = framework_builder.build_framework()
        except FrameworkSpecificationError:
            logger.error(f"Error creating framework.")
            raise FrameworkError()
        # Build monitor
        logger.info(f"Creating monitor...")
        monitor = Monitor(framework, MonitorBuilder.signal_flags)
        logger.info(f"Monitor created.")
        return monitor
