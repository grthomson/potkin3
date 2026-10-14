from pathlib import Path
import subprocess, sys, json

ROOT = Path(__file__).resolve().parent
SCRIPTS = ['mixed_checker/check_mixed.py', 'verification_client/test_client.py']

def main():
    results=[]
    for script in SCRIPTS:
        run=subprocess.run([sys.executable,str(ROOT/script)],cwd=ROOT.parent,
                           text=True,capture_output=True)
        (ROOT/(script.replace('/','__')+'.log')).write_text(run.stdout+run.stderr)
        results.append({'script':script,'returncode':run.returncode})
    data={'passed':all(x['returncode']==0 for x in results),'checks':results,
          'scope':'finite checks; paper mixed theorem; implicational certificate implementation'}
    (ROOT/'validation_summary.json').write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps(data,indent=2))
    return 0 if data['passed'] else 1

if __name__=='__main__':
    raise SystemExit(main())
