module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ChowCohomologyOverFieldIso
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.ZeroCycleDegree
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductDedekind.ChowCohomology

/-!
# Stacks 0FC5 needs the components of the base to be curves

Section 42.63 of the Stacks Project takes `S` locally Noetherian with an open covering by spectra
of Dedekind domains, `δ = 0` at the closed points and `δ = 1` elsewhere, and refers to Example
02QN, where `S` is the spectrum of a Noetherian domain of dimension one. A field is a Dedekind
domain (Algebra, Lemma 034X), so without the dimension restriction the spectrum of a field is
allowed, and there Stacks 0FC5 fails: for `S = Spec k` the point is closed, `δ = 0`,
`CH_1(S) = 0`, whereas `A^0(S ⟶ S) = CH_0(S) = ℤ` by Stacks 0FBW and Stacks 0AZ1. This file
records that counterexample.

## Main results

* `Stacks.Chow.isDedekindChowBase_fieldChowSituation`: the spectrum of a field is a base as in
  section 42.63, read without the dimension restriction.
* `Stacks.Chow.not_bijective_bivariantChowClassCapBaseFundamentalClass_field`: for it, the map
  `A^0(S ⟶ S) ⟶ CH_1(S)`, `c ↦ c ∩ [S]₁`, is not bijective.

## References

* [Stacks Project, Tag 0FC5](https://stacks.math.columbia.edu/tag/0FC5)
* [Stacks Project, Example 02QN](https://stacks.math.columbia.edu/tag/02QN)
* [Stacks Project, Tag 034X](https://stacks.math.columbia.edu/tag/034X)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Stacks.Chow

variable (k : Type u) [Field k]

/-- The spectrum of a field, with its zero dimension function, satisfies the hypothesis
`Stacks.Chow.IsDedekindChowBase` of section 42.63. -/
theorem isDedekindChowBase_fieldChowSituation : IsDedekindChowBase (fieldChowSituation k) := by
  refine ⟨fun s ↦ ⟨⊤, trivial, isAffineOpen_top _, ?_⟩, fun s _ ↦ rfl,
    fun s hs ↦ absurd (isClosed_discrete _) hs⟩
  have hF : IsField Γ(Spec (CommRingCat.of k), ⊤) :=
    MulEquiv.isField (Field.toIsField k)
      (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.toMulEquiv
  let := hF.toField
  infer_instance

/-- Over the spectrum of a field the Chow group of `1`-cycles of the base vanishes. -/
theorem subsingleton_chowGroup_one_fieldChowSituation :
    Subsingleton (chowGroup (fieldChowSituation k) (𝟙 (fieldChowSituation k).S) (1 - 0)) := by
  have hcyc : ∀ α : CycleGroup (fieldChowSituation k) (𝟙 (fieldChowSituation k).S) (1 - 0),
      α = 0 := by
    intro α
    refine Subtype.ext (Function.locallyFinsuppWithin.ext fun x ↦ ?_)
    by_contra hx
    have h := (mem_cyclesOfDimension_iff_forall_point _ _ _ α.1).1 α.2 x hx
    rw [relativeDimension_id, fieldChowSituation_dimensionFunction] at h
    exact absurd h (by decide)
  refine ⟨fun a b ↦ ?_⟩
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective _ a
  obtain ⟨b, rfl⟩ := QuotientAddGroup.mk'_surjective _ b
  rw [hcyc a, hcyc b]

/-- **Stacks 0FC5 fails for the spectrum of a field.** For `S = Spec k`, which satisfies the
hypothesis of section 42.63 read without the dimension restriction
(`Stacks.Chow.isDedekindChowBase_fieldChowSituation`), the map `A^0(S ⟶ S) ⟶ CH_1(S)`,
`c ↦ c ∩ [S]₁`, is not bijective. -/
theorem not_bijective_bivariantChowClassCapBaseFundamentalClass_field :
    ¬ Function.Bijective
      (bivariantChowClassCapBaseFundamentalClass (𝟙 (fieldChowSituation k).S) 0) := by
  intro hbij
  have := subsingleton_chowGroup_one_fieldChowSituation k
  have hA : Subsingleton (BivariantChowClass (fieldChowSituation k) (𝟙 (fieldChowSituation k).S)
      (𝟙 (fieldChowSituation k).S) (𝟙 (fieldChowSituation k).S) (Category.comp_id _) 0) :=
    ⟨fun c d ↦ hbij.1 (Subsingleton.elim _ _)⟩
  exact zero_ne_one (α := ℤ) <|
    ((bivariantChowClassToBaseEquivField k (𝟙 (fieldChowSituation k).S) 0).trans
      (chowGroupBaseEquivInt (fieldChowSituation k) (fieldChowSituation_dimensionFunction k)
        (Classical.arbitrary _))).symm.injective (Subsingleton.elim _ _)

end Stacks.Chow

end
