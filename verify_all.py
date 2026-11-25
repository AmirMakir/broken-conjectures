#!/usr/bin/env python3
"""Run every verifier in this repository. Python 3.8+, standard library only."""
import os
import subprocess
import sys

root = os.path.join(os.path.dirname(os.path.abspath(__file__)), "conjectures")
folders = sorted(d for d in os.listdir(root) if os.path.isfile(os.path.join(root, d, "verify.py")))
results = []
for d in folders:
    print(f"\n=== {d}")
    r = subprocess.run([sys.executable, os.path.join(root, d, "verify.py")])
    results.append((d, r.returncode == 0))
print("\nSummary:")
for d, ok in results:
    print(f"  {'PASS' if ok else 'FAIL'}  {d}")
sys.exit(0 if all(ok for _, ok in results) else 1)
