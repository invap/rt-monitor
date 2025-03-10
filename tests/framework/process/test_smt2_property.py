# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial
import unittest

from rt_monitor.framework.process.smt2_property import SMT2Property


class Test_SMT2Property (unittest.TestCase):

    @classmethod
    def setUpClass(cls):
        pass

    def setUp(self):
        pass

    def test_property_from_str (self):
        property_name_str = "property"

        property_variables_str = "(bound:State Int),(data:State Array Int)"
        property_formula_oracle = "(forall (i Int) (implies (and (<= 0 i) (<= i bound)) (and (<= 1 (select data i))) (<= (select data i) 10)))"
        smt2_property = SMT2Property.property_from_str (property_name_str, property_variables_str, property_formula_oracle)

        variable_decls_oracle = {"bound": ("State", "Int"), "data": ("State", "Array Int")}
        smt2_property_oracle = SMT2Property(
            property_name_str,
            variable_decls_oracle,
            property_formula_oracle,
            ""
        )

        assert(smt2_property.name() == smt2_property_oracle.name() and
               smt2_property.variables() == smt2_property.variables() and
               smt2_property.formula() == smt2_property.formula() and
               smt2_property.filename() == smt2_property_oracle.filename())

    def test_property_from_file (self):
        property_name_str = "property"
        property_file_path = "property.protosmt2"

        smt2_property = SMT2Property.property_from_file (property_name_str, property_file_path)

        property_formula_oracle = "(forall (i Int) (implies (and (<= 0 i) (<= i bound)) (and (<= 1 (select data i))) (<= (select data i) 10)))"
        variable_decls_oracle = {"bound": ("State", "Int"), "data": ("State", "Array Int")}
        smt2_property_oracle = SMT2Property(
            property_name_str,
            variable_decls_oracle,
            property_formula_oracle,
            property_file_path
        )

        assert(smt2_property.name() == smt2_property_oracle.name() and
               smt2_property.variables() == smt2_property.variables() and
               smt2_property.formula() == smt2_property.formula() and
               smt2_property.filename() == smt2_property_oracle.filename())

    @classmethod
    def tearDownClass(cls):
        pass

    def tearDown(self):
        pass
