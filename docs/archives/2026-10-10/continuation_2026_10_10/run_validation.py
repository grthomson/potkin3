"""Run the continuation checks using Python's standard library only."""
from pathlib import Path
import json, subprocess, sys, time

ROOT = Path(__file__).resolve().parent
SCRIPTS = [
    'cofree_profile.py', 'island_seal.py', 'material_modes.py',
    'material_modes_validation.py', 'hole_refill_challenge.py',
    'adversarial_no_go_probe.py', 'adversarial_parametric_probe.py',
    'adversarial_hole_refill_probe.py', 'hole_refill_modes.py',
    'nonprimitive_lift_obstruction.py', 'faa_di_bruno_expansion.py',
    'carrier_client/check_translation.py', 'carrier_client/tensor_shell.py',
]

def main():
    logs = ROOT / 'validation_logs'
    logs.mkdir(exist_ok=True)
    results = []
    for script in SCRIPTS:
        started = time.monotonic()
        completed = subprocess.run([sys.executable, str(ROOT / script)],
                                   cwd=ROOT.parent, text=True, capture_output=True)
        (logs / (script.replace('/', '__') + '.log')).write_text(
            completed.stdout + completed.stderr, encoding='utf-8')
        row = dict(script=script, returncode=completed.returncode,
                   seconds=round(time.monotonic() - started, 3))
        results.append(row)
        print(json.dumps(row), flush=True)
    report = dict(python=sys.version, passed=all(r['returncode'] == 0 for r in results),
                  checks=results)
    (ROOT / 'validation_summary.json').write_text(json.dumps(report, indent=2)+'\n')
    return 0 if report['passed'] else 1

if __name__ == '__main__':
    raise SystemExit(main())
