#!/usr/bin/env python3
"""Check source imports, layer boundaries, and coverage by the root Lean module."""

from pathlib import Path
import re
import sys


ROOT = Path(__file__).resolve().parent.parent
PREFIX = "RelationalOutcomeLogic"


def check_structure() -> list[str]:
    sources = [ROOT / f"{PREFIX}.lean", *(ROOT / PREFIX).rglob("*.lean")]
    modules = {".".join(p.relative_to(ROOT).with_suffix("").parts): p for p in sources}
    graph: dict[str, list[str]] = {}
    errors: list[str] = []

    for module, path in sorted(modules.items()):
        # Imports in this repository are single-line commands in the source header.
        imports = re.findall(r"^import\s+([^\n]+)", path.read_text(), re.MULTILINE)
        dependencies = [name for line in imports for name in line.split("--", 1)[0].split()
                        if name == PREFIX or name.startswith(PREFIX + ".")]
        graph[module] = dependencies
        layer = module.split(".")[1] if module != PREFIX else None
        for dependency in dependencies:
            if dependency not in modules:
                errors.append(f"{module}: imported source does not exist: {dependency}")
                continue
            target = dependency.split(".")[1] if dependency != PREFIX else None
            if layer and layer != "Examples" and target == "Examples":
                errors.append(f"{module}: library code imports example {dependency}")
            if layer == "Algebra" and target != "Algebra":
                errors.append(f"{module}: algebra depends on higher layer {dependency}")
            if layer == "Generic" and target not in {"Algebra", "Generic"}:
                errors.append(f"{module}: generic logic depends on concrete layer {dependency}")

    visited: set[str] = set()
    active: list[str] = []

    def visit(module: str) -> None:
        if module in active:
            cycle = active[active.index(module):] + [module]
            errors.append("import cycle: " + " -> ".join(cycle))
            return
        if module in visited or module not in graph:
            return
        visited.add(module)
        active.append(module)
        for dependency in graph[module]:
            visit(dependency)
        active.pop()

    visit(PREFIX)
    missing = sorted(modules.keys() - visited)
    for module in missing:
        errors.append(f"{module}: not imported by the root; build and axiom gate would miss it")
    for module in missing:
        visit(module)

    if not errors:
        print(f"structure gate: {len(modules)} modules, all sources present and reachable; layers checked")
    return errors


if __name__ == "__main__":
    problems = check_structure()
    for problem in problems:
        print("FAIL: " + problem, file=sys.stderr)
    sys.exit(bool(problems))
