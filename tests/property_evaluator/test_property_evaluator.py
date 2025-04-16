# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial
import unittest

import numpy as np

from rt_monitor.property_evaluator.py_property_evaluator import PyPropertyEvaluator


class Test_Property (unittest.TestCase):

    @classmethod
    def setUpClass(cls):
        pass

    def setUp(self):
        pass

    def test_py_property_evaluator_ndarray(self):
        assumption = PyPropertyEvaluator._build_assumption("var", np.zeros((2, 3, 4)))
        assumption_oracle = "var[0][0][0] = 0.0\nvar[0][0][1] = 0.0\nvar[0][0][2] = 0.0\nvar[0][0][3] = 0.0\n"+\
                            "var[0][1][0] = 0.0\nvar[0][1][1] = 0.0\nvar[0][1][2] = 0.0\nvar[0][1][3] = 0.0\n"+\
                            "var[0][2][0] = 0.0\nvar[0][2][1] = 0.0\nvar[0][2][2] = 0.0\nvar[0][2][3] = 0.0\n"+\
                            "var[1][0][0] = 0.0\nvar[1][0][1] = 0.0\nvar[1][0][2] = 0.0\nvar[1][0][3] = 0.0\n"+\
                            "var[1][1][0] = 0.0\nvar[1][1][1] = 0.0\nvar[1][1][2] = 0.0\nvar[1][1][3] = 0.0\n"+\
                            "var[1][2][0] = 0.0\nvar[1][2][1] = 0.0\nvar[1][2][2] = 0.0\nvar[1][2][3] = 0.0\n"
        assert assumption == assumption_oracle

    def test_py_property_evaluator_dict(self):
        var = {"[0][0][0]": "0.0", "[0][0][1]": "0.0", "[0][0][2]": "0.0", "[0][0][3]": "0.0",
               "[0][1][0]": "0.0", "[0][1][1]": "0.0", "[0][1][2]": "0.0", "[0][1][3]": "0.0",
               "[0][2][0]": "0.0", "[0][2][1]": "0.0", "[0][2][2]": "0.0", "[0][2][3]": "0.0",
               "[1][0][0]": "0.0", "[1][0][1]": "0.0", "[1][0][2]": "0.0", "[1][0][3]": "0.0",
               "[1][1][0]": "0.0", "[1][1][1]": "0.0", "[1][1][2]": "0.0", "[1][1][3]": "0.0",
               "[1][2][0]": "0.0", "[1][2][1]": "0.0", "[1][2][2]": "0.0", "[1][2][3]": "0.0"}
        assumption = PyPropertyEvaluator._build_assumption("var", var)
        assumption_oracle = "var[0][0][0] = 0.0\nvar[0][0][1] = 0.0\nvar[0][0][2] = 0.0\nvar[0][0][3] = 0.0\n"+\
                            "var[0][1][0] = 0.0\nvar[0][1][1] = 0.0\nvar[0][1][2] = 0.0\nvar[0][1][3] = 0.0\n"+\
                            "var[0][2][0] = 0.0\nvar[0][2][1] = 0.0\nvar[0][2][2] = 0.0\nvar[0][2][3] = 0.0\n"+\
                            "var[1][0][0] = 0.0\nvar[1][0][1] = 0.0\nvar[1][0][2] = 0.0\nvar[1][0][3] = 0.0\n"+\
                            "var[1][1][0] = 0.0\nvar[1][1][1] = 0.0\nvar[1][1][2] = 0.0\nvar[1][1][3] = 0.0\n"+\
                            "var[1][2][0] = 0.0\nvar[1][2][1] = 0.0\nvar[1][2][2] = 0.0\nvar[1][2][3] = 0.0\n"
        assert assumption == assumption_oracle

    @classmethod
    def tearDownClass(cls):
        pass

    def tearDown(self):
        pass
