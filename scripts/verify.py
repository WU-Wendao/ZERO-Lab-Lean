"""Run each independent problem's verification entry point."""

import argparse
import subprocess
import sys

from projects import ROOT, discover


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--project', help='Verify only this problem directory name.')
    parser.add_argument('--static', action='store_true', help='Run source checks without Lean.')
    args = parser.parse_args()
    try:
        projects = discover()
    except ValueError as error:
        parser.exit(1, f'{error}\n')
    if args.project:
        projects = [project for project in projects if project['name'] == args.project]
        if not projects:
            parser.error(f'Unknown problem: {args.project}')
    failed = []
    for project in projects:
        directory = ROOT / project['path']
        command = [sys.executable, str(directory / 'scripts' / 'verify.py')]
        if args.static:
            command.append('--static')
        print(f'Verifying {project["name"]} ...', flush=True)
        if subprocess.run(command, cwd=directory).returncode:
            failed.append(project['name'])
    if failed:
        print('Verification failed: ' + ', '.join(failed), file=sys.stderr)
        return 1
    print(f'All {len(projects)} problem(s) passed.', flush=True)
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
