# LeanArchitect Blueprint Workflow

This document describes how the project blueprint is generated from Lean annotations
and rendered via `leanblueprint`.

## 1. Prerequisites

```bash
pip install leanblueprint invoke
```

Optional system deps:

```bash
sudo apt install graphviz libgraphviz-dev
```

## 2. LeanArchitect Dependency

The dependency is configured in `lakefile.toml`, pointing to a patched fork that avoids
batteries version conflicts with Mathlib:

```toml
[[require]]
name = "LeanArchitect"
git = "https://github.com/cameronfreer/LeanArchitect.git"
rev = "<commit-sha>"
```

## 3. Blueprint Annotations

Import Architect and annotate key declarations with `@[blueprint]`:

```lean
import Architect

@[blueprint "thm:CRH"
  (title := /-- Countable refinement hypothesis --/)]
theorem countableRefinementHypothesis : CountableRefinementHypothesis.{u, v, w} L := by
  ...
```

The narrative in `blueprint/src/content.tex` uses `\inputleannode{<label>}` to pull in
the statement text and dependency metadata from each annotated declaration.

### Current annotated nodes (16 total)

**Definitions (8):**
- `def:BFEquiv` — Back-and-forth equivalence
- `def:scottFormula` — Scott formula
- `def:stabilization-ordinal` — Stabilization ordinal
- `def:scott-sentence` — Scott sentence
- `def:scottRank` — Scott rank
- `def:scottHeight` — Scott height
- `def:potential-iso` — Potential isomorphism
- `def:linf-equiv` — $L_{\infty\omega}$-equivalence

**Theorems (8):**
- `thm:scottFormula-iff` — Scott formula characterization
- `thm:self-stabilization` — Self-stabilization
- `thm:scott-characterizes-of` — Scott characterization (conditional)
- `thm:CRH` — Countable refinement hypothesis
- `thm:scott-characterizes` — Scott characterization
- `thm:scottRank-lt-omega1` — Scott rank below $\omega_1$
- `thm:scottHeight-lt-omega1` — Scott height below $\omega_1$
- `thm:karp-theorem` — Karp's theorem

## 4. Extract and Render

```bash
# Extract LeanArchitect blueprint artifacts + build project
lake build :blueprint

# Render
leanblueprint pdf   # → blueprint/print/print.pdf
leanblueprint web   # → blueprint/web/
leanblueprint serve # local preview
```

## 5. CI

The workflow at `.github/workflows/build.yml` runs `lake build :blueprint` then
deploys the rendered blueprint to GitHub Pages on every push to `master`.

To enable deployment, set the repository's Pages source to **GitHub Actions** in
Settings > Pages.

## 6. Troubleshooting

- If web render fails on bibliography, run `leanblueprint pdf` before `leanblueprint web`.
- If extracted dependency edges are noisy, override with `uses := [...]` or `proofUses := [...]` in `@[blueprint]`.
