# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial
import unittest

from rt_monitor.framework.process.property import Property


class Test_Property (unittest.TestCase):

    @classmethod
    def setUpClass(cls):
        pass

    def setUp(self):
        pass

    def test_preproperty_from_str (self):
        property_name_str = "property"

        property_variables_str = "(bound:State Int),(data:State Array Int)"
        property_formula_str = "(forall (i Int) (implies (and (<= 0 i) (<= i bound)) (and (<= 1 (select data i))) (<= (select data i) 10)))"
        variable_decls, property_formula = Property.preproperty_from_str (property_variables_str, property_formula_str)
        property = Property(property_name_str, variable_decls, property_formula, "")

        variable_decls_oracle = {"bound": ("State", "Int"), "data": ("State", "Array Int")}
        property_oracle = Property(property_name_str, variable_decls_oracle, property_formula_str, "")

        assert(property.name() == property_oracle.name() and
               property.variables() == property.variables() and
               property.formula() == property.formula() and
               property.filename() == property_oracle.filename())

    def test_preproperty_from_file (self):
        property_name_str = "property"
        property_file_path = "property.protosmt2"

        variable_decls, property_formula = Property.preproperty_from_file (property_file_path)
        property = Property(
            property_name_str,
            variable_decls,
            property_formula,
            property_file_path
        )

        variable_decls_oracle = {"bound": ("State", "Int"), "data": ("State", "Array Int")}
        property_formula_oracle = "(forall (i Int) (implies (and (<= 0 i) (<= i bound)) (and (<= 1 (select data i))) (<= (select data i) 10)))"
        property_oracle = Property(
            property_name_str,
            variable_decls_oracle,
            property_formula_oracle,
            property_file_path
        )

        assert(property.name() == property_oracle.name() and
               property.variables() == property.variables() and
               property.formula() == property.formula() and
               property.filename() == property_oracle.filename())

    @classmethod
    def tearDownClass(cls):
        pass

    def tearDown(self):
        pass
