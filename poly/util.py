# Infra / util
# ~~~~~~~~~~~~

import dataclasses, itertools, copy
from collections import defaultdict
from typing import *

# Some things are simply unhandled; this is ok since we're not trying to
# optimize _every_ program
#
# When there's a bizarre edge case, it's ok to raise Unhandled('too wonky')
class Unhandled(Exception):
    pass
