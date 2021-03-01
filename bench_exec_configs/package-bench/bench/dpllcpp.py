import benchexec.tools.template
import benchexec.result as result
import benchexec.util as util
import re


class Tool(benchexec.tools.template.BaseTool):
    def executable(self):
        return "/home/cezar/work/fii/jlamp-2020-si-submission/impl/dpllcpp" 

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
