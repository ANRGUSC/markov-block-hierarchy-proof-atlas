# Markov block hierarchy · Proof Atlas

Explore Bhaskar Krishnamachari's *A Block Hierarchy for Rate-Distortion and Dispersion of Binary Markov Sources*. The Atlas binds its excerpts and PDF to the local v4 manuscript. [Paper on arXiv](https://arxiv.org/abs/2603.07435v4) · [Manuscript source repository](https://github.com/ANRGUSC/markov-block-hierarchy)

- [Read the Proof Atlas](https://anrgusc.github.io/markov-block-hierarchy-proof-atlas/proofs/)
- [Explore the dependency graph for Theorem 8](https://anrgusc.github.io/markov-block-hierarchy-proof-atlas/proofs/#/graph/thm%3Acommon)
- [View the progress dashboard](https://anrgusc.github.io/markov-block-hierarchy-proof-atlas/progress.html)

The inventory contains ten numbered results and one conjecture. The graph displays the recorded prerequisites. Selecting a claim highlights its upstream and downstream results and opens the explanations for its direct links. The structured proofs come from the paper's proof companion.

## Lean coverage

For Proposition 1, Lean checks the positive-persistence threshold for the four explicit inverse-prior masses on the admissible distortion interval. For zero persistence, Lean checks that the four masses form a product distribution and stay strictly positive below the smaller stationary probability. For negative persistence, five named algebraic lemmas cover the smaller quadratic root, positivity before it, the ordering of constant words, the tie at a zero and positivity of the transition masses. Deriving their hypotheses from the source model, assembling the first-loss result and establishing channel optimality remain open. The independent contract and axiom queries are in [lean/Audit.lean](lean/Audit.lean). [Recorded Lean run](evidence/negative-support-subproofs.txt)

## Build or preview

With Python 3.9 or later, run from the repository root:

```sh
python tools/proof-atlas/scripts/preview.py . --open
```

The preview opens the explorer and the dashboard and updates them as records change. For a static build, run `python tools/proof-atlas/scripts/atlas.py build .`. The Pages workflow runs this build on pushes to main and deploys the resulting `dist/` directory.

To rerun the Lean checks, use `python tools/proof-atlas/scripts/check_lean.py lean --logs evidence`. The helper locates or provisions the pinned toolchain. Once its dependencies are available locally, use `--offline`. The website build reuses the selected recorded evidence. New mathematical results require a new Lean check.

The paper-specific records are in `project.json`, `reader.json`, `companion/`, and `lean/`. A portable renderer snapshot is included in `tools/proof-atlas/`; bundled third-party notices accompany its assets.
