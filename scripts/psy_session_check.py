#!/usr/bin/env python3
"""Psy multi-step session continuity harness (ProofForgePsy).

Runs the ported psy_dpn_session.py over each emitted package and asserts the
expected multi-step state evolution (write-then-reload across calls).

Engineering only — not UPS/proof/network. Matches the official session
harness semantics (Set overlays committed between calls; Get reloads).
"""
from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / "build" / "out"

# (package, [calls], expected final slots {leaf:[value]}, expected outputs seq)
CASES: list[tuple[str, list[str], dict[int, list[int]], list[list[int]]]] = [
    ("Counter",
     ["initialize:7", "increment:5", "get", "decrement:3", "get"],
     {0: [9]},
     [[], [12], [12], [9], [9]]),
    ("Flag",
     ["initialize:9", "setFlag:200", "getFlag"],
     {0: [200], 1: [9]},
     [[], [200], [200]]),
    ("OptionProbe",
     ["initSome:5", "peek", "setSome:9", "peek", "clear", "peek"],
     {0: [0], 1: [0]},
     [[], [5], [9], [9], [0], [0]]),
    ("MultiRetProbe",
     ["initialize:3", "both:2", "getSum"],
     {0: [5], 1: [5]},
     [[], [5, 5], [10]]),
    ("BoolProbe",
     ["initialize:3", "andProbe:2", "orProbe:1", "getN"],
     {0: [0], 1: [5]},
     [[], [5], [5], [5]]),
    ("InitCompute",
     ["initialize:4,3", "raiseLevel:2", "get"],
     {0: [14], 1: [7]},
     [[], [14], [14]]),

    ("ErrorProbe",
     ["initialize:100", "raise:5"],
     {0: [105]},
     [[], [105]]),
    ("MultiLeafProbe",
     ["initialize:6", "swapAdd:2", "cross"],
     {0: [8], 1: [8]},
     [[], [8], [8]]),
]


def run_case(name: str, calls: list[str],
             expect_slots: dict[int, list[int]],
             expect_outputs: list[list[int]]) -> bool:
    dpn = OUT / f"{name}.dpn.json"
    if not dpn.exists():
        print(f"  SKIP {name}: no {dpn.name}", file=sys.stderr)
        return True
    cmd = [sys.executable, str(ROOT / "scripts" / "psy_dpn_session.py"),
           "--dpn", str(dpn), "--json"]
    for c in calls:
        cmd += ["--call", c]
    r = subprocess.run(cmd, capture_output=True, text=True)
    if r.returncode != 0:
        print(f"  FAIL {name}: session rc={r.returncode}\n{r.stderr}", file=sys.stderr)
        return False
    data = json.loads(r.stdout)
    if not data.get("success"):
        print(f"  FAIL {name}: {data}", file=sys.stderr)
        return False
    slots = data.get("slots", data.get("final_slots", {}))
    # normalize: slot -> leaf -> [values]
    final = {}
    for leaf, vals in slots.items():
        final[int(leaf)] = vals if isinstance(vals, list) else [vals]
    ok = True
    for leaf, vals in expect_slots.items():
        got = final.get(leaf)
        if got != vals:
            print(f"  FAIL {name}: slot {leaf} want {vals} got {got}", file=sys.stderr)
            ok = False
    # outputs
    for i, call in enumerate(data.get("calls", [])):
        want = expect_outputs[i] if i < len(expect_outputs) else []
        got = call.get("outputs", [])
        if got != want:
            print(f"  FAIL {name}: call {i} outputs want {want} got {got}", file=sys.stderr)
            ok = False
    if ok:
        print(f"  OK   {name} ({len(calls)} calls)")
    return ok


def main() -> int:
    all_ok = True
    for name, calls, slots, outputs in CASES:
        all_ok = run_case(name, calls, slots, outputs) and all_ok
    if all_ok:
        print("psy session continuity: all cases pass")
        return 0
    print("psy session continuity: FAILURES", file=sys.stderr)
    return 1


if __name__ == "__main__":
    sys.exit(main())
