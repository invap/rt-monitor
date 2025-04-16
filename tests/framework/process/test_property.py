# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial
import sys
import unittest

import toml

from rt_monitor.framework.process.process_node.property import Property


class Test_Property (unittest.TestCase):

    @classmethod
    def setUpClass(cls):
        pass

    def setUp(self):
        pass

    def test_property_from_file(self):
        try:
            property_dict = toml.load("summation_data_chk.toml")
        except FileNotFoundError:
            print(f"File summation_data_chk.toml not found.", file=sys.stderr)
            assert False
        except toml.TomlDecodeError as e:
            print(f"Incorrect toml format in file summation_data_chk.toml in line {e.lineno}, column {e.colno}.", file=sys.stderr)
            assert False
        except PermissionError:
            print(f"Permissions error opening file summation_data_chk.toml.", file=sys.stderr)
            assert False
        property_name = "summation_data_chk"
        # Property
        property = Property.property_from_toml_dict(property_name, property_dict)

        # Property oracle
        variables_oracle = {"summation": ("State", "Int"), "data": ("State", "(Array Int (Array Int Int))")}
        declarations_oracle = """(declare-fun sum ((Array Int Int) Int Int) Int)
                  (assert (forall ((a (Array Int Int)) (i Int)) (= (sum a i i) 0)))
                  (assert (forall ((a (Array Int Int)) (i Int) (j Int))
                              (=> (< i j)
                                  (= (sum a i j) (+ (select a i) (sum a (+ i 1) j)))
                              )
                          )
                  )"""
        formula_oracle = """(exists ((a (Array Int Int)))
                    (and
                         (forall ((i Int)) (=> (<= 0 10) (= (select a i) (sum (select data i) 0 10))))
                         (= (sum a 0 10) summation)
                    )
             )"""
        property_oracle = Property(property_name, "smt2", variables_oracle, declarations_oracle, formula_oracle)

        assert ((property.name() == property_oracle.name()) and
                (property.format() == property_oracle.format()) and
                (property.variables() == property_oracle.variables()) and
                (property.declarations() == property_oracle.declarations()) and
                (property.formula() == property_oracle.formula()))

    @classmethod
    def tearDownClass(cls):
        pass

    def tearDown(self):
        pass
