"""Discover independent Lean projects and validate their repository layout."""

import argparse
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]


def discover():
    projects = []
    for directory in sorted((ROOT / 'problems').iterdir()):
        if not directory.is_dir() or directory.name.startswith('.'):
            continue
        if not re.fullmatch(r'[a-z0-9]+(?:-[a-z0-9]+)*', directory.name):
            raise ValueError(f'Invalid problem directory name: {directory.name}')
        required = ('README.md', 'lean-toolchain', 'lake-manifest.json',
                    'proof/COVERAGE.md', 'proof/Audit.lean', 'scripts/verify.py')
        missing = [name for name in required if not (directory / name).is_file()]
        if not any((directory / name).is_file() for name in ('lakefile.toml', 'lakefile.lean')):
            missing.append('lakefile.toml or lakefile.lean')
        if missing:
            raise ValueError(f'{directory.name}: missing {", ".join(missing)}')
        projects.append({'name': directory.name, 'path': directory.relative_to(ROOT).as_posix()})
    if not projects:
        raise ValueError('No Lean projects found under problems/.')
    return projects


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--json', action='store_true', help='Output a GitHub Actions matrix.')
    args = parser.parse_args()
    try:
        projects = discover()
    except ValueError as error:
        parser.exit(1, f'{error}\n')
    if args.json:
        print(json.dumps({'include': projects}, separators=(',', ':')))
    else:
        for project in projects:
            print(f'{project["name"]}: {project["path"]}')


if __name__ == '__main__':
    main()
