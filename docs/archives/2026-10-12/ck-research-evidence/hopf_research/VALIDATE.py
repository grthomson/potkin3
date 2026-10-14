"""Reproduce the finite evidence; this does not check the universal paper proofs."""
from pathlib import Path
from datetime import datetime, timezone
import subprocess, time, json, hashlib, sys

root=Path(__file__).resolve().parent
logs=root/'validation_logs'
logs.mkdir(exist_ok=True)
scripts=sorted(root.glob('check_*.py'))+[root/'partition_kernels.py']
results=[]
for script in scripts:
    start=datetime.now(timezone.utc).isoformat()
    before=time.monotonic()
    process=subprocess.run([sys.executable,str(script)],cwd=root.parent,
                           stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
    elapsed=time.monotonic()-before
    destination=logs/(script.stem+'.txt')
    destination.write_text(process.stdout)
    result={'script':script.name,'started_utc':start,'duration_seconds':round(elapsed,4),
            'exit_code':process.returncode,'stdout_file':str(destination.relative_to(root)),
            'source_sha256':hashlib.sha256(script.read_bytes()).hexdigest()}
    results.append(result)
    print(json.dumps(result),flush=True)
report={'status':'finite exact executable evidence; no Lean or native theorem claim',
        'all_passed':all(r['exit_code']==0 for r in results),
        'results':results,'finished_utc':datetime.now(timezone.utc).isoformat()}
(root/'VALIDATION.json').write_text(json.dumps(report,indent=2)+'\n')
if not report['all_passed']:raise SystemExit(1)
