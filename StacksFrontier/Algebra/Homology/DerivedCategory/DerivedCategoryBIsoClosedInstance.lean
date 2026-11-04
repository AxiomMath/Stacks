module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.DerivedQuasicoherentCohomology

/-!
# `D_B(A)` is strictly full as soon as `B` is, as an instance

The library proves that `DerivedCategoryB.derivedCategoryB B` is closed under isomorphisms
whenever `B` is, as `DerivedCategoryB.isClosedUnderIsomorphisms_derivedCategoryB`. It is declared
a theorem there; this module makes it available to instance search, which is how the
admissibility statements of [Stacks, Tag 0H0P] consume it.
-/

public section

attribute [instance] DerivedCategoryB.isClosedUnderIsomorphisms_derivedCategoryB
