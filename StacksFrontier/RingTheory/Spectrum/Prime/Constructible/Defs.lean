module

public import Mathlib.RingTheory.Spectrum.Prime.ConstructibleSet
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.Constructible

import StacksCore.Tactic.StacksAttribute

/-!
# Quasi-compact opens and constructible subsets of `Spec R`

For an open `U ⊆ Spec R`, being retrocompact, being quasi-compact, being a finite union of
standard opens `D(f)`, and being the complement of the zero locus of a finitely generated ideal
are all equivalent: these are `QuasiSeparatedSpace.isRetrocompact_iff_isCompact`,
`PrimeSpectrum.isCompact_isOpen_iff` — whose `(zeroLocus ↑t)ᶜ` for a `Finset` `t` is exactly
`⋃ f ∈ t, D(f)` — and `PrimeSpectrum.isCompact_isOpen_iff_ideal`.

A subset of `Spec R` is constructible iff it is a finite union of sets `D(f) ∩ V(g₁, …, gₘ)`:
`PrimeSpectrum.BasicConstructibleSetData` packages such a tuple,
`PrimeSpectrum.BasicConstructibleSetData.toSet` is the set it describes (as `V(g) \ V(f)`, i.e.
`D(f) ∩ V(g)`), `PrimeSpectrum.ConstructibleSetData.toSet` takes the finite union, and
`PrimeSpectrum.exists_constructibleSetData_iff` is the equivalence.
-/

@[expose] public section

add_to_stacks 00F6 "(1) ↔ (2)" QuasiSeparatedSpace.isRetrocompact_iff_isCompact
add_to_stacks 00F6 "(2) ↔ (3)" PrimeSpectrum.isCompact_isOpen_iff
add_to_stacks 00F6 "(2) ↔ (4)" PrimeSpectrum.isCompact_isOpen_iff_ideal

add_to_stacks 0G1P PrimeSpectrum.exists_constructibleSetData_iff
add_to_stacks 0G1P "the data of a `D(f) ∩ V(g₁, …, gₘ)`"
  PrimeSpectrum.BasicConstructibleSetData
add_to_stacks 0G1P "the set it describes" PrimeSpectrum.BasicConstructibleSetData.toSet
add_to_stacks 0G1P "the finite union" PrimeSpectrum.ConstructibleSetData.toSet

end
