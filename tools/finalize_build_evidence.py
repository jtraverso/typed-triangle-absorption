"""Seal the verified local Palomar build; does not publish or run a build.

Copyright 2026 Juan Pablo Traverso Gianini. SPDX-License-Identifier: Apache-2.0
"""
from datetime import datetime, timezone
from pathlib import Path
import hashlib
import json
import subprocess
import sys
import zipfile

ROOT = Path(__file__).resolve().parents[1]
LOGS = ROOT / '.lake/palomar-build'
CHECKER_BASE = '93979dd796e185f13676a9b09593cc09b2b95bbf'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def save(path, data):
    path.write_text(json.dumps(data, indent=2) + '\n', encoding='utf-8', newline='\n')


result = json.loads((ROOT/'tools/check_result.json').read_text(encoding='utf-8'))
report = ROOT/'tools/check_report.txt'
assert result['status'] == 'ALL CHECKS PASSED'
assert sha(report) == result['report_sha256']
assert report.read_text(encoding='utf-8').rstrip().endswith('ALL CHECKS PASSED')
checker = ROOT/'tools/check_palomar.py'
original_checker = subprocess.check_output(['git', 'show', f'{CHECKER_BASE}:tools/check_palomar.py'], cwd=ROOT)
checker_logic = checker.read_text(encoding='utf-8').replace('import sys\n', '', 1)
checker_logic = checker_logic.replace(', newline="\\n"', '')
checker_logic = checker_logic.replace('    sys.stdout.reconfigure(encoding="utf8")\n', '', 1)
assert checker_logic == original_checker.decode('utf-8').replace('\r\n', '\n')
assert 'Build completed successfully' in (LOGS/'build.log').read_text(encoding='utf-8')
assert 'Build completed successfully' in (LOGS/'challenge-interface-rebuild.log').read_text(encoding='utf-8-sig')
with (LOGS/'final-preservation-audit.log').open('w', encoding='utf-8') as output:
    subprocess.run([sys.executable, '-X', 'utf8', '-I', 'tools/audit_build_repairs.py'],
                   cwd=ROOT, stdout=output, stderr=subprocess.STDOUT, check=True)

sources = sorted((ROOT/'PartitionedTriangleAbsorption').rglob('*.lean'))
sources += [ROOT/name for name in ('PartitionedTriangleAbsorption.lean', 'Challenge.lean', 'Solution.lean')]
assert len(sources) == 1514
rows = []
for path in sources:
    name = path.relative_to(ROOT).as_posix()
    olean = ROOT/'.lake/build/lib/lean'/Path(name).with_suffix('.olean')
    assert olean.is_file(), name
    rows.append({'path': name, 'sha256': sha(path),
                 'compiled_module': olean.relative_to(ROOT).as_posix()})
manifest = ROOT/'tools/built_sources_manifest.json'
save(manifest, {'files': rows, 'scope': 'Current source hashes and existence of every compiled local module; frozen upstream input manifest is preserved separately.'})

files = ['.lake/palomar-build/build.log', '.lake/palomar-build/challenge-interface-rebuild.log',
         '.lake/palomar-build/checks-final-utf8.log', 'tools/check_report.txt',
         'tools/check_result.json', 'tools/build_repair_preservation.json',
         'tools/interface_parameter_alignment.json', 'tools/import_header_repair.json',
         'tools/heartbeat_budget_repair.json', 'tools/charge_walk_budget_repair.json',
         'tools/redundant_rfl_repair.json', 'tools/checker_io_repair.json',
         'tools/check_io_regression.json']
archive = ROOT/'tools/final_build_logs.zip'
with zipfile.ZipFile(archive, 'w', compression=zipfile.ZIP_DEFLATED) as z:
    for name in files:
        z.write(ROOT/name, name.removeprefix('.lake/palomar-build/'))
locked = json.loads((ROOT/'lake-manifest.json').read_text(encoding='utf-8'))
mathlib = next(p for p in locked['packages'] if p['name'] == 'mathlib')
evidence = {'status': 'ALL CHECKS PASSED', 'sealed_utc': datetime.now(timezone.utc).isoformat(),
            'git_head': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
            'local_compiled_modules': len(sources), 'mathlib_revision': mathlib['rev'],
            'toolchain': (ROOT/'lean-toolchain').read_text().strip(),
            'check_report_sha256': sha(report), 'checker_sha256': sha(checker),
            'checker_test_logic_unchanged_from_baseline': True,
            'checker_baseline_revision': CHECKER_BASE,
            'checker_original_sha256': hashlib.sha256(original_checker).hexdigest(),
            'checker_io_only_repairs': ['UTF-8 console output', 'LF report output matching its declared SHA-256'],
            'built_sources_manifest_sha256': sha(manifest),
            'successful_logs_archive_sha256': sha(archive),
            'scope': 'Local preflight and complete independent proof-library build. The recorded git_head is the parent revision at evidence generation; built_sources_manifest.json identifies the exact checked source bytes. Palomar Comparator/NanoDa verification and submission remain separate. Canonical manuscript freezes are unchanged.',
            'files': [{'path': name, 'sha256': sha(ROOT/name)} for name in files]}
save(ROOT/'tools/final_build_evidence.json', evidence)
print(json.dumps({k: evidence[k] for k in ('status', 'local_compiled_modules', 'check_report_sha256', 'successful_logs_archive_sha256')}, indent=2))
