# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

from framework.process.property import Property


class SMT2Property(Property):
    def __init__(self, property_name, variables, formula, filename):
        super().__init__(property_name, variables, formula, filename)

    @staticmethod
    def property_from_file(property_name, file_name):
        variables, formula = Property.preproperty_from_file(file_name)
        return SMT2Property(property_name, variables, formula, file_name)

    @staticmethod
    def property_from_str(property_name, property_variables, property_formula):
        variables, formula = Property.preproperty_from_str(property_variables, property_formula)
        return SMT2Property(property_name, variables, formula, "")

    def format(self):
        return "protosmt2"