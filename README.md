# Markov block hierarchy · Proof Atlas

Explore Bhaskar Krishnamachari's *A Block Hierarchy for Rate-Distortion and Dispersion of Binary Markov Sources*. The Atlas binds its excerpts and PDF to the local v4 manuscript. [Paper on arXiv](https://arxiv.org/abs/2603.07435v4) · [Manuscript source repository](https://github.com/ANRGUSC/markov-block-hierarchy)

- [Read the Proof Atlas](https://anrgusc.github.io/markov-block-hierarchy-proof-atlas/proofs/)
- [Explore the dependency graph for Theorem 8](https://anrgusc.github.io/markov-block-hierarchy-proof-atlas/proofs/#/graph/thm%3Acommon)
- [View the progress dashboard](https://anrgusc.github.io/markov-block-hierarchy-proof-atlas/progress.html)

The inventory contains ten numbered results and one conjecture. The graph displays the recorded prerequisites. Selecting a claim highlights its upstream and downstream results and opens the explanations for its direct links. The structured proofs come from the paper's proof companion.

## Lean coverage

Lean checks all ten numbered results against their paper statements. The conjecture remains open. The [combined release transcript](evidence/paper-release.txt) records the same ten declarations checked together. Each receipt records the declaration, its expected type, the pinned toolchain, the input hashes and the transitive axioms.

| Numbered result | Formal statement | Verification |
|---|---|---|
| Proposition 1 | [Lean statement](lean/FirstChangeStatement.lean) | [Audit receipt](evidence/first-change-audit-v2.json) |
| Theorem 2 | [Lean statement](lean/ReducedPair/PaperStatement.lean) | [Audit receipt](evidence/persistent-pair-audit.json) |
| Theorem 3 | [Lean statement](lean/BlockHierarchy/PairVariance/ThreeStatement.lean) | [Audit receipt](evidence/three-symbol-full-audit.json) |
| Theorem 4 | [Lean statement](lean/BlockHierarchy/PairVariance/FourStatement.lean) | [Audit receipt](evidence/four-symbol-full-audit.json) |
| Proposition 5 | [Lean statement](lean/BlockHierarchy/RecurrenceStatement.lean) | [Audit receipt](evidence/recurrence-audit.json) |
| Theorem 6 | [Lean statement](lean/BlockHierarchy/Varentropy/Statement.lean) | [Audit receipt](evidence/varentropy-audit.json) |
| Lemma 7 | [Lean statement](lean/BlockHierarchy/Cut/Statement.lean) | [Audit receipt](evidence/cut-audit.json) |
| Theorem 8 | [Lean statement](lean/BlockHierarchy/VarianceLimit/Statement.lean) | [Audit receipt](evidence/variance-limit-audit.json) |
| Corollary 9 | [Lean statement](lean/BlockHierarchy/VarianceLimit/PositiveStatement.lean) | [Audit receipt](evidence/positive-audit.json) |
| Proposition 10 | [Lean statement](lean/BlockHierarchy/Converse/Statement.lean) | [Audit receipt](evidence/converse-audit.json) |

## Build or preview

With Python 3.9 or later, run from the repository root:

```sh
python tools/proof-atlas/scripts/preview.py . --open
```

The preview opens the explorer and the dashboard and updates them as records change. For a static build, run `python tools/proof-atlas/scripts/atlas.py build .`. The Pages workflow runs this build on pushes to main and deploys the resulting `dist/` directory.

To recheck all ten numbered results in one build, run `python tools/proof-atlas/scripts/check_lean.py lean --logs evidence --target BlockHierarchy.PaperRelease`. The helper locates or provisions the pinned toolchain. Once its dependencies are available locally, use `--offline`. The website build reuses the selected recorded evidence. New mathematical results require a new Lean check.

The paper-specific records are in `project.json`, `reader.json`, `companion/`, and `lean/`. A portable renderer snapshot is included in `tools/proof-atlas/`; bundled third-party notices accompany its assets.
