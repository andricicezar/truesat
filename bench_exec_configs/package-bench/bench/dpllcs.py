import benchexec.tools.template
import benchexec.result as result
import benchexec.util as util
import re


class Tool(benchexec.tools.template.BaseTool):
    def executable(self):
        return util.find_executable("mono")

    def name(self):
        return "DPLL in C#"

    def cmdline(self, executable, options, tasks, propertyfile, rlimits):
        return (
            [executable, "/home/cezar/work/fii/jlamp-2020-si-submission/impl/dpll.exe"]
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
