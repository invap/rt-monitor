# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

class Operator:
    @classmethod
    def new_of_type(cls, operator_type):
        return cls(operator_type)

    def __init__(self, operator_type):
        super().__init__()
        self._type = operator_type

    def type(self):
        return "Operator"