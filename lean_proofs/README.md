# Lean proofs

Lean proofs of the 24 results listed below from *Reversible Arithmetic with One-Wire Transpositions*, including its appendices.

## Build the proofs

Install Git and Lean through Elan. From this folder, run:

```sh
lake exe cache get
lake build
```

Lean and Mathlib versions are pinned.

## Source files

[Toffoli.lean](Toffoli.lean) imports all the proofs. The files are grouped by topic:

| Folder | Contents |
|---|---|
| [Foundations](Toffoli/Foundations/) | Circuits, composition, and wire locality. |
| [Universality](Toffoli/Universality/) | Permutation groups and universality. |
| [Additions](Toffoli/Additions/) | Transfers, cycles, and powers. |
| [Polarization](Toffoli/Polarization/) | Polarization identities and circuits. |
| [Schedules](Toffoli/Schedules/) | Gray codes and optimal preparation order. |
| [Divide](Toffoli/Divide/) | Divide-and-conquer and its bounds. |
| [Borrow](Toffoli/Borrow/) | Borrowed ladders and the Borrow construction. |
| [Mixed](Toffoli/Mixed/) | Borrow-and-conquer and workspace counts. |
| [Polynomial](Toffoli/Polynomial/) | Polynomial synthesis and zero-sum criteria. |
| [Quadratic](Toffoli/Quadratic/) | Quadratic forms and square decompositions. |

## Results in the paper

| Paper result | Subject | Lean files |
|---|---|---|
| Lemma 2.3 | Affine conjugacy of local transpositions | [LocalSwapConjugacy](Toffoli/Additions/LocalSwapConjugacy.lean) |
| Theorem 2.4 | Prime-field universality | [PrimeUniversality](Toffoli/Universality/PrimeUniversality.lean) |
| Lemma 3.3 | Two-point transfer circuit | [TwoPointTransfer](Toffoli/Additions/TwoPointTransfer.lean) |
| Theorem 3.4 | Accumulator-form characterization | [MultiControlZeroSumIff](Toffoli/Polynomial/MultiControlZeroSumIff.lean) |
| Theorem 3.5 | Cycle synthesis characterization | [CycleAddition](Toffoli/Additions/CycleAddition.lean) |
| Lemma 3.6 | Power sums vanish on multiplier cycles | [PowerCycles](Toffoli/Additions/PowerCycles.lean) |
| Proposition 3.7 | Optimal affine cycle choice for powers | [OptimalPowerCycles](Toffoli/Additions/OptimalPowerCycles.lean) |
| Lemma 4.1 | Grouped polarization correctness and call counts | [GroupedPolarization](Toffoli/Polarization/GroupedPolarization.lean) |
| Theorem 4.2 | Exact divide-and-conquer recurrence | [DivideProduct](Toffoli/Divide/DivideProduct.lean), [DivideRecurrence](Toffoli/Divide/DivideRecurrence.lean) |
| Lemma 5.2 | Grouped borrowed ladder correctness and cost | [BorrowedLadder](Toffoli/Borrow/BorrowedLadder.lean) |
| Corollary 5.3 | Binary borrowed ladder | [BinaryBorrowedLadder](Toffoli/Borrow/BinaryBorrowedLadder.lean) |
| Proposition 5.4 | Borrow construction on the original wires | [BorrowOnly](Toffoli/Borrow/BorrowOnly.lean) |
| Proposition 6.3 | Borrow-and-conquer correctness and comparison | [BorrowAndConquer](Toffoli/Mixed/BorrowAndConquer.lean) |
| Theorem 7.1 | Summary of asymptotic upper bounds | [DirectProductBound](Toffoli/Divide/DirectProductBound.lean), [DividePolynomialCircuit](Toffoli/Divide/DividePolynomialCircuit.lean), [BorrowLinear](Toffoli/Borrow/BorrowLinear.lean), [MixedLinearCircuit](Toffoli/Mixed/MixedLinearCircuit.lean) |
| Theorem A.1 | Universality over odd composite alphabets | [ModularUniversality](Toffoli/Universality/ModularUniversality.lean) |
| Corollary A.2 | Universality over finite fields | [FiniteFieldUniversality](Toffoli/Universality/FiniteFieldUniversality.lean) |
| Theorem B.1 | Polynomial synthesis through linear powers | [PolynomialSynthesis](Toffoli/Polynomial/PolynomialSynthesis.lean) |
| Proposition B.2 | Reduced-polynomial criterion | [PolynomialZeroSumIff](Toffoli/Polynomial/PolynomialZeroSumIff.lean), [PolynomialLowDegreeSynthesis](Toffoli/Polynomial/PolynomialLowDegreeSynthesis.lean) |
| Corollary B.3 | Odd function synthesis | [OddFunctionAddition](Toffoli/Additions/OddFunctionAddition.lean) |
| Proposition B.4 | Quadratic rank and synthesis count | [QuadraticAdditions](Toffoli/Quadratic/QuadraticAdditions.lean) |
| Proposition C.1 | Optimal preparation schedule | [GroupedSchedule](Toffoli/Schedules/GroupedSchedule.lean) |
| Lemma D.1 | Balanced grouping polynomial growth | [DividePolynomial](Toffoli/Divide/DividePolynomial.lean) |
| Lemma D.2 | Comparison with direct polarization | [DivideComparison](Toffoli/Divide/DivideComparison.lean) |
| Proposition E.1 | Exact workspace-aware mixed recurrence | [BorrowedRecursion](Toffoli/Mixed/BorrowedRecursion.lean), [MixedRecurrence](Toffoli/Mixed/MixedRecurrence.lean) |
