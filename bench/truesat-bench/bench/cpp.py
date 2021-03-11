import benchexec.tools.template
import benchexec.result as result
import benchexec.util as util
import re
import os


class Tool(benchexec.tools.template.BaseTool):
    def executable(self):
        if "TRUESAT_BENCHEXEC" in os.environ:
            return os.environ.get("TRUESAT_BENCHEXEC") + "/cpp_solver/dpllcpp" 
        else:
            raise NameError('Please set TRUESAT_BENCHEXEC to the root folder of the TrueSAT repo')

    def name(self):
        return "DPLL in CPP"

    def cmdline(self, executable, options, tasks, propertyfile, rlimits):
        return (
            [executable]
            + options
            + tasks
        )

    def get_value_from_output(self, lines, identifier):
        for line in reversed(lines):
            pattern = identifier
            if pattern[-1] != ":":
                pattern += ":"
            match = re.match("^" + pattern + "(.*)", line)
            if match and match.group(1):
                return match.group(1).strip()
        return None
