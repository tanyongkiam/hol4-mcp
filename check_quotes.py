#!/usr/bin/env python3
"""Detect and fix mismatched Unicode smart quotes in a file.
U+2018 (LEFT SINGLE QUOTATION MARK) = opening
U+2019 (RIGHT SINGLE QUOTATION MARK) = closing
Matched pairs are valid HOL4 term quotations — left alone.
Unmatched quotes are replaced with ASCII single quote '.
Usage: python3 check_quotes.py <file> [--fix]
"""
import sys

fname = sys.argv[1]
fix = '--fix' in sys.argv

with open(fname, 'r', encoding='utf-8') as f:
    lines = f.readlines()

# First pass: find all quote positions
quotes = []  # (lineno_0indexed, col, 'open'|'close')
for li, line in enumerate(lines):
    for col, ch in enumerate(line):
        if ch == '\u2018':
            quotes.append((li, col, 'open'))
        elif ch == '\u2019':
            quotes.append((li, col, 'close'))

# Match pairs greedily
matched = set()
stack = []
for i, (li, col, kind) in enumerate(quotes):
    if kind == 'open':
        stack.append(i)
    elif kind == 'close':
        if stack:
            matched.add(stack.pop())
            matched.add(i)

# Report and optionally fix unmatched
unmatched = [q for i, q in enumerate(quotes) if i not in matched]
for li, col, kind in unmatched:
    label = 'open \u2018' if kind == 'open' else 'close \u2019'
    print(f"Line {li+1}, col {col}: unmatched {label}: {lines[li].rstrip()}")

if fix and unmatched:
    for li, col, kind in reversed(unmatched):  # reverse to preserve positions
        line = lines[li]
        lines[li] = line[:col] + "'" + line[col+1:]
    with open(fname, 'w', encoding='utf-8') as f:
        f.writelines(lines)
    print(f"Fixed {len(unmatched)} unmatched quote(s)")
elif not unmatched:
    print("No unmatched quotes found")
