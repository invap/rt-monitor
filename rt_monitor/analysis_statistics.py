# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

from colorama import Fore, Style


class AnalysisStatistics:
    events = 0
    passed_props = 0
    failed_props = 0
    might_fail_props = 0

    @staticmethod
    def init():
        AnalysisStatistics.events = 0
        AnalysisStatistics.passed_props = 0
        AnalysisStatistics.failed_props = 0
        AnalysisStatistics.might_fail_props = 0

    @staticmethod
    def event():
        AnalysisStatistics.events += 1

    @staticmethod
    def passed():
        AnalysisStatistics.passed_props += 1

    @staticmethod
    def failed():
        AnalysisStatistics.failed_props += 1

    @staticmethod
    def might_fail():
        AnalysisStatistics.might_fail_props += 1

    @staticmethod
    def print():
        n1 = AnalysisStatistics.passed_props
        n2 = AnalysisStatistics.might_fail_props
        n3 = AnalysisStatistics.failed_props
        print("+-----------------+------------+")
        print(f"| Processed evs.  : {(str(AnalysisStatistics.events) if AnalysisStatistics.events <= 1000000000 else "Too many").rjust(10)} |")
        print(f"| Analyzed props. : {(str(n1 + n2 + n3) if n1 + n2 + n3 <= 1000000000 else "Too many").rjust(10)} |")
        print("+-----------------+------------+------------+")
        print("|     Verdict     |  Quantity  | Percentage |")
        print("+-----------------+------------+------------+")
        n1p = n1 * 100 / (n1 + n2 + n3)
        print(f"| {Fore.GREEN}PASSED         {Style.RESET_ALL} | " +
              f"{(str(n1) if n1 <= 1000000000 else "Too many").rjust(10)} |" +
              f"{n1p:.3f}".rjust(11) +
              " |")
        n2p = n2 * 100 / (n1 + n2 + n3)
        print(f"| {Fore.YELLOW}MIGHT FAIL     {Style.RESET_ALL} | " +
              f"{(str(n2) if n2 <= 1000000000 else "Too many").rjust(10)} |" +
              f"{n2p:.3f}".rjust(11) +
              " |")
        n3p = n3 * 100 / (n1 + n2 + n3)
        print(f"| {Fore.RED}FAILED         {Style.RESET_ALL} | " +
              f"{(str(n3) if n3 <= 1000000000 else "Too many").rjust(10)} |" +
              f"{n3p:.3f}".rjust(11) +
              " |")
        print("+-----------------+------------+------------+")
