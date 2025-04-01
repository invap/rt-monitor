# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial
import logging

from rt_monitor.errors.process_errors import ProcessSpecificationError
from rt_monitor.framework.process.regex_process import RegExProcess
from rt_monitor.framework.process.graph_process import GraphProcess


class ProcessBuilder:
    def __init__(self):
        pass

    @staticmethod
    def build_process(process_dict, files_path):
        if "format" not in process_dict:
            logging.error(f"Process format not found.")
            raise ProcessSpecificationError()
        factory = {
            "graph": GraphProcess,
            "regex": RegExProcess
        }
        process_type = process_dict["format"]
        if process_type not in factory:
            raise ProcessSpecificationError
        return factory[process_type].process_from_toml_dict(process_dict, files_path)
