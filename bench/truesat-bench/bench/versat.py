import benchexec.tools.template
import benchexec.result as result
import benchexec.util as util
import re

class Tool(benchexec.tools.template.BaseTool2):
    def executable(self, tool_locator):
        return tool_locator.find_executable("versat")

    def name(self):
        return "versat"

    def cmdline(self, executable, options, task, rlimits):
        return [executable] + options + [task.single_input_file]


    def determine_result(self, run):
        status = None

        for line in run.output:
            if "UNSAT" in line:
                status = result.RESULT_FALSE_PROP
            elif "SAT" in line:
                status = result.RESULT_TRUE_PROP

        if not status:
            status = result.RESULT_ERROR
        return status
