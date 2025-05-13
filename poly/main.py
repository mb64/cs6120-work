# main.py -- the main function

from util import *
import bril
import relooper
import static

import traceback
import json, sys, copy

debug = False

def main() -> None:
    program: bril.Program = bril.load(sys.stdin)
    new_functions: list[bril.Function] = []
    for function in program['functions']:
        try:
            cfg = bril.function_to_cfg(function)
            if debug: cfg.debug()

            cmd = relooper.to_structured_control_flow(cfg)
            if debug: cmd.debug()

            try:
                s = static.command_to_static(cmd)
                if debug: s.debug()

                cmd2 = s.to_structured()
                if debug: cmd2.debug()
            except Unhandled as e:
                if debug:
                    print(traceback.format_exc(), file=sys.stderr)

            func2 = cmd.codegen()
            # cfg2 = bril.function_to_cfg(func2)
            # if debug: cfg2.debug()
        except Unhandled as e:
            if debug:
                print(traceback.format_exc(), file=sys.stderr)
            func2 = function
        new_functions.append(func2)

        if debug:
            print()
            print('---------')
            print()

    new_program: bril.Program = { 'functions': new_functions }
    json.dump(new_program, sys.stdout)


if __name__ == '__main__':
    main()
