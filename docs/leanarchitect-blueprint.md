# LeanArchitect Blueprint Workflow

This document describes a concrete way to use LeanArchitect in this repository and render a project blueprint.

## Goal

Generate blueprint artifacts directly from Lean declarations in `InfinitaryLogic/*`, then render PDF/web blueprint pages with `leanblueprint`.

## Toolchain Notes

- Current project toolchain: Lean `v4.27.0` (`lean-toolchain`).
- Use a LeanArchitect revision compatible with Lean `v4.27.0`.
- Reservoir metadata indicates commit `4373fe8` supports `v4.27.0`.

## 1. Install Prerequisites

```bash
pip install leanblueprint invoke
```

Optional system deps (if needed by your environment):

```bash
sudo apt install graphviz libgraphviz-dev
```

## 2. Add LeanArchitect Dependency

Edit `lakefile.toml`:

```toml
[[require]]
name = "LeanArchitect"
git = "https://github.com/hanwenzhu/LeanArchitect.git"
rev = "4373fe8"
```

Then update/build deps:

```bash
lake update LeanArchitect
lake build
```

## 3. Add Blueprint Annotations in Lean

In files you want rendered, import Architect and annotate key declarations.

Example (`InfinitaryLogic/Scott/RefinementCount.lean`):

```lean
import Architect

@[blueprint "thm:countable-refinement-hypothesis"
  (statement := /-- For countable `M`, refinement ordinals for a fixed tuple are countable. -/)
  (title := /-- Countable Refinement Hypothesis -/)]
theorem countableRefinementHypothesis : CountableRefinementHypothesis.{u, v, w} L := by
  ...
```

Suggested first wave of nodes:

- `thm:countable-refinement-hypothesis`
- `thm:per-tuple-stabilization-below-omega1`
- `thm:exists-complete-stabilization`
- `thm:scott-sentence-characterizes`
- `thm:scott-height-lt-omega1`
- `thm:countable-lomega-equiv-implies-iso`

## 4. Create/Use Blueprint LaTeX Skeleton

If you do not already have a blueprint skeleton:

```bash
leanblueprint new
```

This creates `blueprint/src/*` and blueprint workflows/layout.

In `blueprint/src/content.tex`, include extracted LeanArchitect output and selected nodes:

```tex
% Expose \inputleanmodule and \inputleannode.
\input{../../.lake/build/blueprint/library/InfinitaryLogic}

% Pull individual nodes:
\inputleannode{thm:countable-refinement-hypothesis}
\inputleannode{thm:scott-sentence-characterizes}

% Or pull all tagged nodes from a module:
% \inputleanmodule{InfinitaryLogic.Scott.RefinementCount}
```

## 5. Extract and Render

From repo root:

```bash
# Extract LeanArchitect blueprint artifacts
lake build :blueprint

# Optional machine-readable output
lake build :blueprintJson

# Render
leanblueprint pdf
leanblueprint web
leanblueprint serve
```

Generated extraction output is under:

- `.lake/build/blueprint/library/*`
- `.lake/build/blueprint/*.json` (if `:blueprintJson` was built)

## 6. CI Integration

If using a blueprint GitHub Action, ensure extraction runs before rendering:

```yaml
- name: Extract blueprint
  run: lake build :blueprint
```

## 7. Suggested Adoption Plan for This Repo

1. Annotate only theorems on the main Scott pipeline first.
2. Render and fix any LaTeX statement text issues.
3. Add model existence and Karp milestones as second wave.
4. Keep labels stable (`thm:*`, `def:*`) to avoid link churn.

## 8. Troubleshooting

- If `leanblueprint checkdecls` fails, run `lake build` first.
- If web render fails on bibliography, run `leanblueprint pdf` before `leanblueprint web`.
- If extracted dependency edges are noisy, override with `uses := [...]` or `proofUses := [...]` in `@[blueprint]`.
