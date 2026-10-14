"""Run the scoped CK research evidence; standard-library Python only."""
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent
SCRIPTS = [
    'check_carrier.py',
    'typed_coaction_inverse.py',
    'test_typed_checker.py',
    'check_natural_demand.py',
    'test_typed_natural.py',
    'sell_material_cuts.py',
    'test_coaction_normalization.py',
]

for name in SCRIPTS:
    start = time.monotonic()
    subprocess.run([sys.executable, str(ROOT / 'research_round3' / name)],
                   cwd=ROOT, check=True)
    print(f'PASS {name} ({time.monotonic()-start:.2f}s)', flush=True)
print('All scoped checks passed. See README and reports for theorem boundaries.')
