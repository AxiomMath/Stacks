module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The reduced induced closed subscheme structure on a closed subset

A closed subset `Z` of a scheme `X` carries a canonical *reduced* closed subscheme structure:
the subscheme cut out by the vanishing ideal sheaf of `Z`, which is the largest quasi-coherent
ideal sheaf with support `Z`. Mathlib constructs the ideal sheaf
(`AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal`) and the associated closed subscheme
(`AlgebraicGeometry.Scheme.IdealSheafData.subscheme`), but does not record that the result is
reduced. This file supplies that.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.isReduced_subscheme`: the closed subscheme cut out
  by an ideal sheaf all of whose component ideals are radical is reduced.
* `AlgebraicGeometry.Scheme.IdealSheafData.isReduced_subscheme_radical`: the closed subscheme
  cut out by the radical of an ideal sheaf is reduced.
* `AlgebraicGeometry.Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal`: the reduced
  induced closed subscheme structure on a closed subset really is reduced.
* `AlgebraicGeometry.Scheme.IdealSheafData.range_subschemeι_vanishingIdeal`: that subscheme is
  supported exactly on the given closed subset.
* `AlgebraicGeometry.Scheme.IdealSheafData.irreducibleSpace_subscheme`: a closed subscheme
  supported on an irreducible closed subset is irreducible.

## Implementation notes

Reducedness is local on an open cover (`AlgebraicGeometry.IsReduced.of_openCover`) and
`AlgebraicGeometry.Scheme.IdealSheafData.subschemeCover` exhibits `I.subscheme` as covered by
the spectra of the rings `Γ(X, U) ⧸ I.ideal U` for `U` ranging over the affine opens of `X`. So
it suffices that each of those quotients is a reduced ring, which is
`Ideal.isRadical_iff_quotient_reduced`. For the vanishing ideal sheaf the component ideals are
the ideals `PrimeSpectrum.vanishingIdeal (U.2.fromSpec ⁻¹' Z)`, radical by
`PrimeSpectrum.isRadical_vanishingIdeal`.

The general `isReduced_subscheme` is stated with a hypothesis on the component ideals rather
than as an instance because an ideal sheaf carries no `IsRadical` typeclass; the two
specialisations that do dispatch by instance search are given separately.

This is the "reduced induced closed subscheme structure" of Stacks tag 01J3. That tag covers
more than is proved here (the universal property, and functoriality in `Z`), so no `@[stacks]`
attribute is attached.

## References

* [Stacks Project, Tag 01J3](https://stacks.math.columbia.edu/tag/01J3)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

namespace IdealSheafData

variable {X : Scheme.{u}}

/-- If every component ideal of an ideal sheaf `I` is radical, then the closed subscheme of `X`
cut out by `I` is reduced.

Reducedness is local on an affine cover, and `I.subschemeCover` covers `I.subscheme` by the
spectra of the quotients `Γ(X, U) ⧸ I.ideal U`. -/
theorem isReduced_subscheme (I : X.IdealSheafData)
    (hI : ∀ U : X.affineOpens, (I.ideal U).IsRadical) : IsReduced I.subscheme := by
  have (i : I.subschemeCover.openCover.I₀) : IsReduced (I.subschemeCover.openCover.X i) := by
    have : _root_.IsReduced (I.subschemeCover.X i) :=
      (Ideal.isRadical_iff_quotient_reduced (I.ideal i)).mp (hI i)
    exact inferInstanceAs (IsReduced (Spec (I.subschemeCover.X i)))
  exact .of_openCover _ I.subschemeCover.openCover

/-- The closed subscheme cut out by the radical of an ideal sheaf is reduced. -/
@[ega "I 5.1.2" "more general"]
instance isReduced_subscheme_radical (I : X.IdealSheafData) : IsReduced I.radical.subscheme :=
  I.radical.isReduced_subscheme fun U ↦ by
    rw [radical_ideal]; exact Ideal.radical_isRadical _

/-- **The reduced induced closed subscheme structure on a closed subset is reduced.**

The closed subscheme cut out by the vanishing ideal sheaf of a closed subset `Z` of `X` is
reduced: on an affine open `U` its ring of sections is `Γ(X, U)` modulo the vanishing ideal of
a subset of `Spec Γ(X, U)`, which is a radical ideal. -/
@[ega "I 5.1.2" "reducedness",
  ega "I 5.2.1" "(b) reduced, closed case",
  ega "I 5.1.3" "more general",
  ega "I 5.5.4" "partial",
  ega "II 6.5.1" "partial",
  ega "IV 3.4.1" "partial",
  ega "IV 4.9.4" "partial", sga "3 XV 3.2" "partial", sga "6 X 1.1.2" "reducedness of Z(x)"]
instance isReduced_subscheme_vanishingIdeal (Z : Closeds X) :
    IsReduced (vanishingIdeal Z).subscheme :=
  isReduced_subscheme _ fun U ↦ by
    rw [vanishingIdeal_ideal]; exact PrimeSpectrum.isRadical_vanishingIdeal _

/-- The reduced induced closed subscheme on a closed subset `Z` has underlying set `Z`.

Together with the instance above this says that `(vanishingIdeal Z).subscheme` is a reduced
closed subscheme of `X` supported exactly on `Z`. -/
@[simp]
theorem range_subschemeι_vanishingIdeal (Z : Closeds X) :
    Set.range (vanishingIdeal Z).subschemeι = Z :=
  (range_subschemeι _).trans (coe_support_vanishingIdeal Z)

/-- A closed subscheme supported on an irreducible closed subset has irreducible underlying
space: its closed immersion is an embedding, hence a homeomorphism onto that subset. -/
theorem irreducibleSpace_subscheme (X : Scheme.{u}) (I : X.IdealSheafData)
    (hirr : IsIrreducible (Set.range I.subschemeι)) : IrreducibleSpace I.subscheme := by
  have hemb : Topology.IsEmbedding I.subschemeι.base := IsPreimmersion.isEmbedding I.subschemeι
  let h : I.subscheme ≃ₜ Set.range I.subschemeι.base := hemb.toHomeomorph
  have : IrreducibleSpace (Set.range I.subschemeι.base) := by
    rw [← isIrreducible_iff_irreducibleSpace]; exact hirr
  exact h.symm.surjective.irreducibleSpace h.symm.continuous

end IdealSheafData

end AlgebraicGeometry.Scheme

end
