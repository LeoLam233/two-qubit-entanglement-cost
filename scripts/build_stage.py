#!/usr/bin/env python3
"""Complete a bounded Lake build stage within an unchanged recorded clean build.
Usage: python3 scripts/build_stage.py STAGE MODULE [MODULE ...]
Then run: python3 scripts/verify.py --resume-clean
"""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, os, re, subprocess, sys

root=Path(__file__).resolve().parents[1]
if len(sys.argv)<3 or not re.fullmatch(r'[a-zA-Z0-9_]+',sys.argv[1]):
    raise SystemExit(__doc__)
context_path=root/'evidence'/'clean_build_context.json'
context=json.loads(context_path.read_text())
for name,digest in context['source_sha256'].items():
    if hashlib.sha256((root/name).read_bytes()).hexdigest()!=digest:
        raise RuntimeError('Source changed after clean build began: '+name)
os.environ.setdefault('LEAN_NUM_THREADS','1')
command=['lake','build',*sys.argv[2:]]
log=root/'evidence'/('clean_build_stage_'+sys.argv[1]+'.log')
start=datetime.now(timezone.utc).isoformat()
print('Running:', ' '.join(command),flush=True)
with log.open('w') as output:
    output.write('Command: '+' '.join(command)+'\nStarted UTC: '+start+'\n')
    output.flush()
    result=subprocess.run(command,cwd=root,stdout=output,stderr=subprocess.STDOUT)
    output.write('\nExit code: '+str(result.returncode)+'\n')
context['stages'].append({'command':command,'started_utc':start,
                          'log':str(log.relative_to(root)),'returncode':result.returncode})
context_path.write_text(json.dumps(context,indent=2)+'\n')
print('Stage',sys.argv[1],'exit',result.returncode,flush=True)
if result.returncode:
    print(log.read_text()[-16000:],flush=True)
sys.exit(result.returncode)
