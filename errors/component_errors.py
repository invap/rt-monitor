# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial


class FunctionNotImplementedError(Exception):
    def __init__(self, function_name):
        super().__init__()
        self._function_name = function_name

    def function_name(self):
        return self._function_name
