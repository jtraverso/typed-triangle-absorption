"""Verify packaged build evidence and source/document hashes without Lean.

Copyright 2026 Juan Pablo Traverso Gianini. SPDX-License-Identifier: Apache-2.0
"""
from pathlib import Path
import hashlib
import json
import zipfile

ROOT = Path(__file__).resolve().parents[1]


def read(name):
    return json.loads((ROOT / name).read_text(encoding='utf-8'))


def sha(data):
    return hashlib.sha256(data).hexdigest()


evidence = read('tools/final_build_evidence.json')
assert evidence['status'] == 'ALL CHECKS PASSED'
for name, key in (
    ('tools/check_report.txt', 'check_report_sha256'),
    ('tools/check_palomar.py', 'checker_sha256'),
    ('tools/built_sources_manifest.json', 'built_sources_manifest_sha256'),
    ('tools/final_build_logs.zip', 'successful_logs_archive_sha256'),
):
    assert sha((ROOT / name).read_bytes()) == evidence[key], name
assert read('tools/check_result.json')['report_sha256'] == evidence['check_report_sha256']
assert read('tools/check_result.json')['status'] == 'ALL CHECKS PASSED'
with zipfile.ZipFile(ROOT / 'tools/final_build_logs.zip') as archive:
    for row in evidence['files']:
        name = row['path']
        packed = name.removeprefix('.lake/palomar-build/')
        assert sha(archive.read(packed)) == row['sha256'], packed
        if not name.startswith('.lake/'):
            assert sha((ROOT / name).read_bytes()) == row['sha256'], name
sources = read('tools/built_sources_manifest.json')['files']
actual = {p.relative_to(ROOT).as_posix() for p in (ROOT / 'PartitionedTriangleAbsorption').rglob('*.lean')}
actual.update(('PartitionedTriangleAbsorption.lean', 'Challenge.lean', 'Solution.lean'))
assert len(sources) == len(actual) == evidence['local_compiled_modules'] == 1514
assert {row['path'] for row in sources} == actual
for row in sources:
    assert sha((ROOT / row['path']).read_bytes()) == row['sha256'], row['path']
documents = read('docs/preprint-1.0/MANIFEST.json')['files']
assert len(documents) == 6
for row in documents:
    data = (ROOT / row['path']).read_bytes()
    assert sha(data) == row['sha256'] and len(data) == row['bytes'], row['path']
assert (ROOT / 'lean-toolchain').read_text().strip() == evidence['toolchain']
mathlib = next(p for p in read('lake-manifest.json')['packages'] if p['name'] == 'mathlib')
assert mathlib['rev'] == evidence['mathlib_revision']
print(json.dumps(dict(status='PASS_PACKAGED_BUILD_CONSISTENCY',
                      source_modules=len(sources), document_files=len(documents),
                      scope='Hash/inventory verification of the packaged evidence; no Lean rebuild or external Palomar verification.')))
