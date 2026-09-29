"""Check complete source coverage, compile the project, and audit theorem dependencies."""

import argparse
from datetime import datetime, timezone
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
LIBRARY = 'ExactValue'
FORBIDDEN = re.compile(r'\b(sorry|admit|axiom|native_decide|unsafe)\b')


def check_sources():
    sources = sorted((ROOT / LIBRARY).rglob('*.lean'))
    if not sources:
        raise ValueError(f'No proof modules found in {LIBRARY}/.')
    entrypoint = ROOT / f'{LIBRARY}.lean'
    imports = set(re.findall(r'^import\s+(\S+)\s*$',
                            entrypoint.read_text(encoding='utf-8-sig'), re.M))
    for source in sources:
        module = '.'.join(source.relative_to(ROOT).with_suffix('').parts)
        if module not in imports:
            raise ValueError(f'Module omitted from the full audit: {module}')
    for source in [entrypoint, *sources]:
        content = source.read_text(encoding='utf-8-sig')
        match = FORBIDDEN.search(content)
        if match:
            raise ValueError(f'Forbidden proof placeholder/trust escape ({match[0]}) '
                             f'in {source.relative_to(ROOT)}')
    theorem_count = sum(len(re.findall(r'^\s*(?:theorem|lemma)\s+',
        source.read_text(encoding='utf-8-sig'), re.M)) for source in sources)
    return len(sources), theorem_count


def run(lake, args, log_name):
    path = ROOT / 'proof' / log_name
    with path.open('w', encoding='utf-8') as log:
        process = subprocess.Popen([lake, *args], cwd=ROOT, stdout=subprocess.PIPE,
                                   stderr=subprocess.STDOUT, text=True,
                                   encoding='utf-8', errors='replace')
        for line in process.stdout:
            log.write(line)
            log.flush()
            print(line, end='', flush=True)
        returncode = process.wait()
    if returncode:
        raise SystemExit(returncode)
    return path.read_text(encoding='utf-8')


def main():
    for stream in (sys.stdout, sys.stderr):
        if hasattr(stream, 'reconfigure'):
            stream.reconfigure(encoding='utf-8', errors='replace')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--static', action='store_true', help='Check sources without invoking Lean.')
    args = parser.parse_args()
    try:
        modules, theorems = check_sources()
    except (OSError, ValueError) as error:
        parser.exit(1, f'{error}\n')
    print(f'Source checks passed: {modules} modules; {theorems} handwritten theorems.', flush=True)
    if args.static:
        return 0
    lake = shutil.which('lake')
    if not lake:
        parser.exit(1, 'lake was not found on PATH. Install elan and reopen your terminal.\n')
    (ROOT / 'proof').mkdir(exist_ok=True)
    run(lake, ['build'], 'build.log')
    audit = run(lake, ['env', 'lean', 'proof/Audit.lean'], 'audit.log')
    result = re.search(r'AUDIT PASSED: (\d+) project theorems; standard axioms only\.', audit)
    if not result:
        parser.exit(1, 'The audit did not report successful completion.\n')
    summary = {
        'verified_at_utc': datetime.now(timezone.utc).isoformat(),
        'lean_toolchain': (ROOT / 'lean-toolchain').read_text().strip(),
        'modules': modules,
        'handwritten_theorems': theorems,
        'audited_theorem_constants': int(result[1]),
        'allowed_axioms': ['propext', 'Classical.choice', 'Quot.sound'],
        'status': 'passed',
    }
    (ROOT / 'proof/verification.json').write_text(json.dumps(summary, indent=2) + '\n', encoding='utf-8')
    print('Build and axiom audit both passed.', flush=True)
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
