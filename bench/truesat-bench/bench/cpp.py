import benchexec.tools.template
import benchexec.result as result
import benchexec.util as util
import re
import os


class Tool(benchexec.tools.template.BaseTool2):
    def executable(self, tool_locator):
        return tool_locator.find_executable("dpllcpp", subdir="cpp_solver")

    def name(self):
        return "DPLL in CPP"

    def cmdline(self, executable, options, task, rlimits):
        return [executable] + options + [task.single_input_file]

    def determine_result(self, run):
        status = None

        for line in run.output:
            if "s SATISFIABLE" in line:
                status = result.RESULT_TRUE_PROP
            elif "s UNSATISFIABLE" in line:
                status = result.RESULT_FALSE_PROP

        if not status:
            status = result.RESULT_ERROR
        return status
