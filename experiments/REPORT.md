# Experiments in Lean proof writing

The metric is elapsed time from the release of an unseen obligation until Lean accepts the entire contract. The split arm includes the check that joins both lemmas. Each arm checks the same proposition with the same pinned Lean installation. The paper-wide study is ongoing.

## Findings by experiment

| Experiment | Completed pairs | First complete certificate | Working decision |
|---|---:|---|---|
| Parallel split vs combined | 3 | 3 combined | Keep short algebraic pairs together when adding an agent would add a join or queue delay. Test harder goals separately. |
| Sequential split vs combined | 2 | 2 combined | Pilot evidence. Review the individual drafting intervals, retries and integration cost before changing the skill. |

## Matched trials

| Pair and paper obligation | Approach | Complete (s) | First draft per author (s) | Outside Lean per author (s) | Lean per author (s) | Extra join (s) | Checks |
|---|---|---:|---:|---:|---:|---:|---:|
| D1 · Four-symbol source order and Hamming coefficients | combined | 79.0 | 44.1 | 44.1 | 34.8 | 0.0 | 1 |
| D1 · Four-symbol source order and Hamming coefficients | parallel split | 159.0 | 25.3 / 25.5 | 49.8 / 25.5 | 86.0 / 53.5 | 23.1 | 4 |
| D2 · Four-symbol Hamming normalizers and conditional costs | combined | 58.0 | 16.1 | 16.1 | 34.9 | 0.0 | 1 |
| D2 · Four-symbol Hamming normalizers and conditional costs | parallel split | 143.0 | 11.1 / 16.1 | 11.1 / 16.1 | 24.6 / 34.0 | 18.8 | 3 |
| D3 · Water-filling transition for the two odd classes | combined | 50.6 | 17.6 | 17.6 | 25.6 | 0.0 | 1 |
| D3 · Water-filling transition for the two odd classes | parallel split | 140.7 | 9.7 / 10.4 | 9.7 / 10.4 | 21.2 / 25.3 | 19.0 | 3 |
| P1 · Four-symbol Markov class totals | sequential | 197.9 | 14.9 | 72.8 | 124.9 | 0.0 | 3 |
| P1 · Four-symbol Markov class totals | combined | 58.3 | 15.3 | 15.3 | 43.1 | 0.0 | 1 |
| P2 · Characterize the first inactive even class at the constant-word candidate | combined | 91.3 | 49.7 | 49.7 | 41.6 | 0.0 | 1 |
| P2 · Characterize the first inactive even class at the constant-word candidate | sequential | 242.9 | 49.7 | 108.9 | 133.8 | 0.0 | 3 |

## Interpretation

In D1 all three agents claimed the task together. In D2 and D3, the next pair opened when the first proof finished. One split worker was still finishing the preceding pair and claimed the new task about 88 and 91 seconds after release. These two comparisons measure pipeline throughput with a busy worker. They cannot establish the effect of splitting for two authors who start together. The equal-author series uses a synchronized gate and alternates which author receives the intervention.

First draft ends when the author submits their first attempt. Outside-Lean time includes reasoning, editing, reading diagnostics and tool or scheduling delays. These are wall-clock measurements. Checker time covers Lean process startup, elaboration and kernel verification. The raw event data includes individual attempt times, author occupancy, accepted source text and axiom reports. Small samples from this paper support conditional working rules.

The study protocol records the remaining comparisons and how the evidence will inform the reusable skill. [Study protocol](PROTOCOL.md) · [Machine-readable trial records](trials.json)
