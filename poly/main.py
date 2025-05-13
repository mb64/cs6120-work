# main.py -- the main function

from util import *
import bril
import relooper
import static

import traceback
import json, sys

def main() -> None:
    program: bril.Program = bril.load(sys.stdin)
    new_functions: list[bril.Function] = []
    for function in program['functions']:
        try:
            cfg = bril.function_to_cfg(function)
            # cfg.debug()

            cmd = relooper.to_structured_control_flow(cfg)
            # cmd.debug()

            s = static.command_to_static(cmd)
            # s.debug()

            cmd2 = s.to_structured()
            # cmd2.debug()

            func2 = cmd2.codegen()
        except Unhandled as e:
            print(traceback.format_exc(), file=sys.stderr)
            func2 = function
        new_functions.append(func2)
    new_program: bril.Program = { 'functions': new_functions }
    json.dump(new_program, sys.stdout)


if __name__ == '__main__':
    main()
