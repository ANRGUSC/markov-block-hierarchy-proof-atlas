# Markov block hierarchy · Proof Atlas

Explore Bhaskar Krishnamachari's *A Block Hierarchy for Rate-Distortion and Dispersion of Binary Markov Sources*. The Atlas binds its excerpts and PDF to the local v4 manuscript. [Paper on arXiv](https://arxiv.org/abs/2603.07435v4) · [Manuscript source repository](https://github.com/ANRGUSC/markov-block-hierarchy)

- [Read the Proof Atlas](https://anrgusc.github.io/markov-block-hierarchy-proof-atlas/proofs/)
- [Explore the dependency graph for Theorem 8](https://anrgusc.github.io/markov-block-hierarchy-proof-atlas/proofs/#/graph/thm%3Acommon)
- [View the progress dashboard](https://anrgusc.github.io/markov-block-hierarchy-proof-atlas/progress.html)

The inventory contains ten numbered results and one conjecture. The graph displays the recorded prerequisites. Selecting a claim highlights its upstream and downstream results and opens the explanations for its direct links. The structured proofs come from the paper's proof companion.

## Lean coverage

Proposition 1 is closed for all three persistence cases, including the equal-bias tie and the lossless endpoint. Lean proves that the displayed marginal uniquely minimizes mutual information under the paper's distortion budget. [Independent contract](lean/FirstChangeStatement.lean) ? [Assembled theorem](lean/FirstChange.lean) ? [Declaration and axiom audit](evidence/first-change-audit-v2.json).

Theorem 2 is closed for the persistent two-symbol source. The proof covers all three rate and variance branches and the biased zero-rate endpoint. [Independent contract](lean/ReducedPair/PaperStatement.lean) ? [Assembled theorem](lean/ReducedPair/Paper.lean) ? [Declaration and axiom audit](evidence/persistent-pair-audit.json).

Theorem 3 is closed for all three support regimes of the symmetric three-symbol source. The independent audit covers the lossless endpoint, both transitions, uniqueness of the optimizing reproduction law, and the rate and tilted variance throughout the stated range. [Independent contract](lean/BlockHierarchy/Three/PaperStatement.lean) ? [Declaration and axiom audit](evidence/three-symbol-audit.json).

The current target is Theorem 4 for the symmetric four-symbol source.

## Build or preview

With Python 3.9 or later, run from the repository root:

```sh
python tools/proof-atlas/scripts/preview.py . --open
```

The preview opens the explorer and the dashboard and updates them as records change. For a static build, run `python tools/proof-atlas/scripts/atlas.py build .`. The Pages workflow runs this build on pushes to main and deploys the resulting `dist/` directory.

To rerun the Lean checks, use `python tools/proof-atlas/scripts/check_lean.py lean --logs evidence`. The helper locates or provisions the pinned toolchain. Once its dependencies are available locally, use `--offline`. The website build reuses the selected recorded evidence. New mathematical results require a new Lean check.

The paper-specific records are in `project.json`, `reader.json`, `companion/`, and `lean/`. A portable renderer snapshot is included in `tools/proof-atlas/`; bundled third-party notices accompany its assets.
