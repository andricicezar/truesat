import benchexec.tools.template
import benchexec.result as result
import benchexec.util as util
import re


class Tool(benchexec.tools.template.BaseTool2):
    def executable(self, tool_locator):
        self.tool_locator2 = tool_locator
        return util.find_executable("mono")

    def name(self):
        return "TrueSAT (noopt)"

    def cmdline(self, executable, options, task, rlimits):
        return [executable, self.tool_locator2.find_executable("truesatnoopt.exe")] + options + [task.single_input_file]

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
