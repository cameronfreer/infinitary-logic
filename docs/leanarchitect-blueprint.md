# LeanArchitect Blueprint Workflow

This document describes a concrete way to use LeanArchitect in this repository and render a project blueprint.

## Goal

Generate blueprint artifacts directly from Lean declarations in `InfinitaryLogic/*`, then render PDF/web blueprint pages with `leanblueprint`.

## Toolchain Notes

- Current project toolchain: Lean `v4.27.0` (`lean-toolchain`).
- Use a LeanArchitect revision compatible with Lean `v4.27.0`.
- We use a fork (`cameronfreer/LeanArchitect`) that comments out the explicit `batteries`
  dependency, which conflicts with Mathlib's batteries version and causes hours of recompilation.
  See [batteries version conflict](#batteries-version-conflict) below.

## 1. Install Prerequisites

```bash
pip install leanblueprint invoke
```

Optional system deps (if needed by your environment):

```bash
sudo apt install graphviz libgraphviz-dev
```

## 2. Add LeanArchitect Dependency

The dependency is already configured in `lakefile.toml`, pointing to the patched fork:

```toml
[[require]]
name = "LeanArchitect"
git = "https://github.com/cameronfreer/LeanArchitect.git"
rev = "<commit-sha>"
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

@[blueprint "thm:CRH"
  (title := /-- Countable refinement hypothesis --/)]
theorem countableRefinementHypothesis : CountableRefinementHypothesis.{u, v, w} L := by
  ...
```

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

## 4. Create/Use Blueprint LaTeX Skeleton

If you do not already have a blueprint skeleton:

```bash
leanblueprint new
```

This creates `blueprint/src/*` and blueprint workflows/layout.

In `blueprint/src/content.tex`, the narrative references LeanArchitect labels:

```tex
\begin{definition}[Scott sentence]\label{def:scott-sentence}
  \lean{scottSentence}\leanok
  \uses{def:scottFormula, def:stabilization-ordinal}
  The Scott sentence of a countable structure $M$ is ...
\end{definition}
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

### Batteries version conflict

LeanArchitect upstream (`hanwenzhu/LeanArchitect`) pins `batteries` at a version that conflicts
with Mathlib's batteries, causing Lake to rebuild Mathlib from source (~hours). The workaround
is to use a fork that comments out the explicit `require batteries` line, since Mathlib already
provides batteries transitively.

If the upstream merges the fix, the fork can be replaced with the upstream URL.

### Other issues

- If web render fails on bibliography, run `leanblueprint pdf` before `leanblueprint web`.
- If extracted dependency edges are noisy, override with `uses := [...]` or `proofUses := [...]` in `@[blueprint]`.
