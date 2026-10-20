#!/usr/bin/env python3
"""Build the complete EC2 project and save exact dependency/axiom evidence.

Usage: python3 scripts/verify.py --clean
The optional clean removes only this project's .lake/build. Pinned upstream
source and independently cached dependency builds are retained.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
EVIDENCE = ROOT / 'evidence'
EXPECTED = {
    'mathlib': '56a005855ea17e0b0958f73ec801ae140b0a1679',
    'Physlib': '1eefcc45aa0d864b8c742e72de5d975b3ee3b15e',
}
TARGETS = [
    'EC2.balanced_complex_rectangular_block_entropy',
    'EC2.fixed_axis_concurrence',
    'EC2.strong_superadditivity',
    'EC2.arbitrary_partner_additivity',
    'EC2.formation_tensor_power',
    'EC2.entanglement_cost_formula',
]

def run_logged(command: list[str], name: str) -> dict:
    path = EVIDENCE / name
    began = datetime.now(timezone.utc).isoformat()
    print('Running:', ' '.join(command), flush=True)
    with path.open('w') as output:
        output.write('Command: ' + ' '.join(command) + '\nStarted UTC: ' + began + '\n')
        output.flush()
        result = subprocess.run(command, cwd=ROOT, stdout=output, stderr=subprocess.STDOUT)
        output.write('\nExit code: ' + str(result.returncode) + '\n')
    print(name + ': exit ' + str(result.returncode), flush=True)
    record = {'command': command, 'log': str(path.relative_to(ROOT)),
              'started_utc': began, 'returncode': result.returncode}
    if result.returncode:
        print(path.read_text()[-18000:], flush=True)
        raise subprocess.CalledProcessError(result.returncode, command)
    return record

def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--clean', action='store_true')
    parser.add_argument('--resume-clean', action='store_true',
                        help='Finish an unchanged clean build recorded in evidence/clean_build_context.json')
    args = parser.parse_args()
    EVIDENCE.mkdir(exist_ok=True)
    os.environ.setdefault('LEAN_NUM_THREADS', '1')
    manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
    actual_pins = {p['name']: p['rev'] for p in manifest['packages'] if p['type'] == 'git'}
    for name, revision in EXPECTED.items():
        if actual_pins.get(name) != revision:
            raise RuntimeError(f'Wrong manifest pin for {name}: {actual_pins.get(name)}')
    if (ROOT / 'lean-toolchain').read_text().strip() != 'leanprover/lean4:v4.35.0':
        raise RuntimeError('Wrong Lean toolchain')
    lean_sources = sorted((ROOT / 'EC2').glob('*.lean')) + [ROOT / 'EC2.lean']
    bad = []
    for p in lean_sources:
        # This is a source hygiene gate, in addition to the kernel dependency audit.
        for lineno, line in enumerate(p.read_text().splitlines(), 1):
            if re.search(r'\b(sorry|admit)\b|^\s*(axiom|opaque)\s', line):
                bad.append(f'{p.relative_to(ROOT)}:{lineno}: {line}')
    if bad:
        raise RuntimeError('Unreviewed source admissions or opaque declarations:\n' + '\n'.join(bad))
    if args.clean and args.resume_clean:
        raise RuntimeError('Choose --clean or --resume-clean')
    context_path = EVIDENCE / 'clean_build_context.json'
    context = None
    if args.clean:
        shutil.rmtree(ROOT / '.lake' / 'build', ignore_errors=True)
        context = {'clean_started_utc': datetime.now(timezone.utc).isoformat(),
                   'origin': 'scripts/verify.py --clean removed this project .lake/build',
                   'source_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                                     for p in lean_sources}, 'stages': []}
        context_path.write_text(json.dumps(context, indent=2) + '\n')
    if args.resume_clean:
        context = json.loads(context_path.read_text())
        for name, digest in context['source_sha256'].items():
            if hashlib.sha256((ROOT / name).read_bytes()).hexdigest() != digest:
                raise RuntimeError('Source changed after clean build began: ' + name)
    summary = {'clean_project_build': args.clean or args.resume_clean,
               'resumed_clean_build': args.resume_clean, 'clean_build_context': context,
               'manifest_pins': actual_pins,
               'LEAN_NUM_THREADS': os.environ['LEAN_NUM_THREADS'], 'commands': []}
    summary['commands'].append(run_logged(['lake', 'env', 'lean', '--version'], 'final_toolchain.log'))
    summary['commands'].append(run_logged(['lake', 'build'], 'final_build.log'))
    heads = {}
    worktree_status = {}
    for name, revision in EXPECTED.items():
        source = ROOT / '.lake' / 'packages' / name
        head = subprocess.check_output(['git', '-C', str(source), 'rev-parse', 'HEAD'], text=True).strip()
        if head != revision:
            raise RuntimeError(f'Wrong checked-out source for {name}: {head}')
        heads[name] = head
        status = subprocess.check_output(
            ['git', '-C', str(source), 'status', '--porcelain', '--untracked-files=no'],
            text=True)
        if status.strip():
            raise RuntimeError(f'Modified tracked dependency files in {name}:\n{status}')
        worktree_status[name] = status
    summary['checked_out_heads'] = heads
    summary['checked_out_tracked_worktree_status'] = worktree_status
    summary['mathematical_status'] = 'All EC2-specific arguments proved; final declarations retain explicit published-result proof parameters.'
    summary['published_interfaces'] = ['EC2.Entropy.RectangularHanner', 'EC2.Literature.WoottersFormation', 'EC2.ConcurrenceReduction.WoottersSpectralFormula', 'EC2.Operational.HHTRegularization']
    summary['unproved_ec2_obligations'] = []
    summary['commands'].append(run_logged(['lake', 'env', 'lean', 'verification/Statements.lean'],
                                          'final_statements_and_axioms.log'))
    audit = (EVIDENCE / 'final_statements_and_axioms.log').read_text()
    if 'sorryAx' in audit:
        raise RuntimeError('A final declaration depends on sorryAx')
    dependencies = {}
    dependencies_as_printed = {}
    for name, body in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", audit):
        dependencies_as_printed[name] = body.strip()
        # pp.universes prints e.g. Classical.choice.{u}. Universe arguments do
        # not change the axiom constant's name. Preserve the raw report too.
        names_only = re.sub(r'\.\{[^{}]*\}', '', body)
        axioms = [v.strip() for v in names_only.replace('\n', ' ').split(',') if v.strip()]
        unexpected = set(axioms) - {'propext', 'Classical.choice', 'Quot.sound'}
        if unexpected:
            raise RuntimeError(f'Unexpected axioms for {name}: {unexpected}')
        dependencies[name] = axioms
    for name in TARGETS:
        if name not in dependencies:
            raise RuntimeError(f'No successful axiom report for {name}')
    summary['axiom_dependencies'] = dependencies
    summary['axiom_dependencies_as_printed'] = dependencies_as_printed
    summary['source_sha256'] = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                                 for p in lean_sources}
    summary['completed_utc'] = datetime.now(timezone.utc).isoformat()
    (EVIDENCE / 'final_verification.json').write_text(json.dumps(summary, indent=2) + '\n')
    print('Complete build and exact statement/axiom audit passed.', flush=True)
    return 0

if __name__ == '__main__':
    sys.exit(main())
