# Markov block hierarchy · Proof Atlas

Explore Bhaskar Krishnamachari's *A Block Hierarchy for Rate-Distortion and Dispersion of Binary Markov Sources*. The Atlas binds its excerpts and PDF to the local v4 manuscript. [Paper on arXiv](https://arxiv.org/abs/2603.07435v4) · [Manuscript source repository](https://github.com/ANRGUSC/markov-block-hierarchy)

- [Read the Proof Atlas](https://anrgusc.github.io/markov-block-hierarchy-proof-atlas/proofs/)
- [Explore the dependency graph for Theorem 8](https://anrgusc.github.io/markov-block-hierarchy-proof-atlas/proofs/#/graph/thm%3Acommon)
- [View the progress dashboard](https://anrgusc.github.io/markov-block-hierarchy-proof-atlas/progress.html)

The inventory contains ten numbered results and one conjecture. The graph displays the recorded prerequisites. Selecting a claim highlights its upstream and downstream results and opens the explanations for its direct links. The structured proofs come from the paper's proof companion.

## Author review

[Open the public review queue](https://anrgusc.github.io/markov-block-hierarchy-proof-atlas/review.html) to compare the v4 manuscript with the mathematical reading of each audited Lean statement. GitHub verification and optional human review have separate badges. The open conjecture has no proof to approve. [How to use this atlas](https://anrgusc.github.io/markov-block-hierarchy-proof-atlas/guide.html).

To submit a decision, tell your coding agent **“Open the local review dashboard for the Markov paper.”** From this repository you can also run:

```sh
python tools/proof-atlas/scripts/atlas.py review .
```

Choose **Yes, these match**, **I see a difference**, or **Skip for now**. Decisions are saved to this checkout; publishing the committed review records makes them visible to readers.

## Lean coverage

Lean checks the formal declarations mapped to the ten numbered results. The review queue tracks their correspondence with the manuscript. The conjecture remains open. The [combined release transcript](evidence/paper-release.txt) records the same ten declarations checked together. Each receipt records the declaration, its expected type, the pinned toolchain, the input hashes and the transitive axioms.

| Numbered result | Formal statement | Verification |
|---|---|---|
| Proposition 1 | [Lean statement](lean/FirstChangeStatement.lean) | [Audit receipt](evidence/phase-review-audit.json) |
| Theorem 2 | [Lean statement](lean/ReducedPair/PaperStatement.lean) | [Audit receipt](evidence/two-review-audit.json) |
| Theorem 3 | [Lean statement](lean/BlockHierarchy/PairVariance/ThreeStatement.lean) | [Audit receipt](evidence/three-review-audit.json) |
| Theorem 4 | [Lean statement](lean/BlockHierarchy/PairVariance/FourStatement.lean) | [Audit receipt](evidence/four-review-audit.json) |
| Proposition 5 | [Lean statement](lean/BlockHierarchy/RecurrenceStatement.lean) | [Audit receipt](evidence/rec-review-audit.json) |
| Theorem 6 | [Lean statement](lean/BlockHierarchy/Varentropy/Statement.lean) | [Audit receipt](evidence/varentropy-review-audit.json) |
| Lemma 7 | [Lean statement](lean/BlockHierarchy/Cut/Statement.lean) | [Audit receipt](evidence/cut-review-audit.json) |
| Theorem 8 | [Lean statement](lean/BlockHierarchy/VarianceLimit/Statement.lean) | [Audit receipt](evidence/common-review-audit.json) |
| Corollary 9 | [Lean statement](lean/BlockHierarchy/VarianceLimit/PositiveStatement.lean) | [Audit receipt](evidence/positive-review-audit.json) |
| Proposition 10 | [Lean statement](lean/BlockHierarchy/Converse/Statement.lean) | [Audit receipt](evidence/converse-review-audit.json) |

The review receipts fingerprint the theorem statements and their definitions in the original module layout. The separate check that statement modules import only other statement modules was not run for this edition.

## Build or preview

With Python 3.9 or later, run from the repository root:

```sh
python tools/proof-atlas/scripts/preview.py . --open
```

The preview opens the explorer and the dashboard and updates them as records change. For a static build, run `python tools/proof-atlas/scripts/atlas.py build .`. The Pages workflow runs this build on pushes to main and deploys the resulting `dist/` directory.

To recheck all ten numbered results in one build, run `python tools/proof-atlas/scripts/check_lean.py lean --logs evidence --target BlockHierarchy.PaperRelease`. The helper locates or provisions the pinned toolchain. Once its dependencies are available locally, use `--offline`. The website build reuses the selected recorded evidence. New mathematical results require a new Lean check.

The paper-specific records are in `project.json`, `reader.json`, `companion/`, and `lean/`. A portable renderer snapshot is included in `tools/proof-atlas/`; bundled third-party notices accompany its assets.
