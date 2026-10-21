"""Regress the verifier's Windows output paths without rerunning Lean.

Copyright 2026 Juan Pablo Traverso Gianini. SPDX-License-Identifier: Apache-2.0
"""
from pathlib import Path
import ast
import hashlib
import json
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
tree = ast.parse((ROOT/'tools/check_palomar.py').read_text(encoding='utf-8'))
footer = ast.unparse(tree.body[-1])
assert footer.startswith("if __name__ == '__main__':")
rows = []
for name, fail in (('unicode_success', False), ('unicode_failure', True), ('ascii_failure', True)):
    message = 'τ σ₀: ' + name if name.startswith('unicode') else name
    with tempfile.TemporaryDirectory() as directory:
        base = Path(directory)
        (base/'tools').mkdir()
        stub = ("raise RuntimeError(" + repr(message) + ")" if fail else
                "REPORT.extend([" + repr(message) + ", 'ALL CHECKS PASSED'])")
        code = ('from pathlib import Path\nimport hashlib,json,sys\n'
                'sys.stdout.reconfigure(encoding="cp1252")\n'
                f'ROOT=Path({str(base)!r})\nREPORT=[]\n'
                f'def main():\n    {stub}\n' + footer)
        result = subprocess.run([sys.executable, '-I', '-c', code], capture_output=True)
        assert result.returncode == int(fail), result.stderr
        assert message in result.stdout.decode('utf-8')
        report = (base/'tools/check_report.txt').read_bytes()
        metadata = json.loads((base/'tools/check_result.json').read_text())
        assert b'\r\n' not in report
        assert hashlib.sha256(report).hexdigest() == metadata['report_sha256']
        assert metadata['status'] == ('CHECKS FAILED' if fail else 'ALL CHECKS PASSED')
        rows.append({'case': name, 'status': 'PASS'})
out = {'status': 'PASS_VERIFIER_WINDOWS_IO_REGRESSION', 'cases': rows,
       'scope': 'Only exercises the actual output footer with stubbed results; the real Lean assertions and comparison passed separately and are unchanged.'}
(ROOT/'tools/check_io_regression.json').write_text(json.dumps(out, indent=2)+'\n', encoding='utf-8', newline='\n')
print(json.dumps(out))
