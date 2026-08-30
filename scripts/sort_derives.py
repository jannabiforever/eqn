#!/usr/bin/env python3
import sys
import re

DERIVE_REGEX = re.compile(r"#\[derive\((.*)\)\]")


def sort_derives(content: str) -> str:
    for matched in DERIVE_REGEX.finditer(content):
        sorted_derives = sorted(d.strip() for d in matched.group(1).split(","))
        content = content.replace(matched.group(0), f"#[derive({', '.join(sorted_derives)})]")
    return content


def main():
    if len(sys.argv) > 1:
        path = sys.argv[1]
        with open(path) as f:
            content = f.read()
        with open(path, "w") as f:
            _ = f.write(sort_derives(content))
    else:
        _ = sys.stdout.write(sort_derives(sys.stdin.read()))

    return 0


if __name__ == "__main__":
    sys.exit(main())
