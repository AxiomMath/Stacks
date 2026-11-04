module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.OpenLift.SupportedPerfectLift
import StacksCore.Tactic.StacksAttribute

/-!
# Lifting a map from a perfect complex over an affine base

Let `A` be a commutative ring, `X = Spec A`, let `T ⊆ X` be a closed subset with quasi-compact
complement, let `U ⊆ X` be a quasi-compact open and let `E` be an object of `D_QCoh(𝒪_X)`. Every
map `α : P ⟶ E|_U` out of a perfect object `P` of `D(𝒪_U)` whose cohomology is supported on
`T ∩ U` is, up to a direct summand, the restriction of a map `β : R ⟶ E` out of a perfect object
`R` of `D(𝒪_X)` whose cohomology is supported on `T`.

This is the case `X` affine of [Stacks, Tag 09IM], the case the source's induction over an
affine cover starts from, and it needs no glueing: [Stacks, Tag 08EK] produces a perfect `Q` on
`X` supported on `T` with `P ⊕ P[1] ≅ Q|_U`, and [Stacks, Tag 08EH] then lifts the composite
`Q|_U ≅ (P ⊕ P[1])|_U ⟶ P|_U ⟶ E|_U` to a pair `β : I ⊗^L Q ⟶ Q`, `γ : I ⊗^L Q ⟶ E` with `β|_U`
invertible. The object `R = I ⊗^L Q` and the map `γ` are what the statement asks for: `R|_U` is
`Q|_U` through `β|_U`, hence `P ⊕ P[1]`, which contains `P` as a direct summand compatibly with
`α`, and `R` is supported on `T` because `Q` is.

The restriction `R|_U` is here *identified* with `P ⊕ P[1]`, not merely shown to contain `P` as
a summand. That is the form the source's induction step needs of its affine input: the glueing
of [Stacks, Tag 08DG] takes an isomorphism of the two restrictions to the intersection as part
of its data, and `P ⊕ P[1]` is the object on the other open precisely so that there is one.

## Main results

* `Stacks.Perfect.LiftingComplexes.exists_isPerfect_lift_spec`: **[Stacks, Tag 09IM] over
  `Spec A`**, with `R|_U` identified with `P ⊕ P[1]`.
* `Stacks.Perfect.LiftingComplexes.exists_isPerfect_lift_summand_spec`: the same with the
  identification weakened to the split inclusion of `P` that [Stacks, Tag 09IM] states.

## Implementation notes

The hypotheses are the source's own, not the weaker ones of
`Stacks.Perfect.LiftingComplexes.exists_isPerfect_lift_of_isClosed_subset`: the complement of
`T` is quasi-compact -- which over an affine scheme is what retrocompactness of that complement
says -- and `E` has quasi-coherent cohomology, which is what [Stacks, Tag 08EH] needs of it.
The closed subset is *not* assumed to be contained in `U`.

Restriction to `U` is written as `Stacks.Duality.OpenImmersion.derivedRestrict U.ι`, the spelling
[Stacks, Tag 08EK] and the cohomological support condition are stated in; [Stacks, Tag 08EH] is
stated in the open-subspace spelling `Stacks.Cohomology.OpenSubspace.derivedRestriction`, and
the two are crossed by
`Stacks.DerivedQCoh.OpenLift.schemeDerivedRestrictIsoOpenSubspace`, along which the map being
lifted is transported and the two conclusions are carried back by
`CategoryTheory.NatIso.isIso_map_iff` and
`Stacks.DerivedQCoh.OpenLift.map_comp_conj_eq_map`.

## References

* [Stacks Project, Lemma 36.13.11 (Tag 09IM)](https://stacks.math.columbia.edu/tag/09IM)
* [Stacks Project, Lemma 36.13.10 (Tag 08EK)](https://stacks.math.columbia.edu/tag/08EK)
* [Stacks Project, Lemma 36.13.7 (Tag 08EH)](https://stacks.math.columbia.edu/tag/08EH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.PerfectComplexes
open Stacks.Duality.OpenImmersion (derivedRestrict)
open Stacks.DerivedQCoh.OpenLift

namespace Stacks.Perfect.LiftingComplexes

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable {A : CommRingCat.{u}}

/-- **[Stacks, Tag 09IM] over `Spec A`.** Let `T` be a closed subset of `X = Spec A` with
quasi-compact complement, let `U ⊆ X` be a quasi-compact open and let `E` be an object of
`D(𝒪_X)` with quasi-coherent cohomology. Every map `α : P ⟶ E|_U` out of a perfect object `P` of
`D(𝒪_U)` whose cohomology is supported on `T ∩ U` arises from a map `β : R ⟶ E` out of a perfect
object `R` of `D(𝒪_X)` supported on `T`, in the strong sense that `R|_U` is isomorphic to
`P ⊕ P[1]` by an isomorphism carrying `β|_U` to the first projection followed by `α`.

[Stacks, Tag 08EK] gives a perfect `Q` supported on `T` with `ε : P ⊞ P[1] ≅ Q|_U`, and
[Stacks, Tag 08EH] lifts `ε⁻¹ ≫ pr₁ ≫ α` to `β, γ : I ⊗^L Q ⟶ Q, E` with `β|_U` invertible. The
identification is `ε` followed by the inverse of `β|_U`. -/
theorem exists_isPerfect_lift_spec (T : Set (Spec A)) (hT : IsClosed T)
    (hTc : IsCompact (Tᶜ : Set (Spec A))) (U : (Spec A).Opens)
    (hU : IsCompact (U : Set (Spec A))) (E : DerivedCategory (Spec A).Modules)
    (hE : Stacks.DerivedQCoh.IsDQCoh (R := (Spec A).ringCatSheaf) E)
    (P : DerivedCategory U.toScheme.Modules)
    (hP : IsPerfect (X := U.toScheme.toRingedSpace) P)
    (hPT : CohomologySupportedOn U.toScheme.ringCatSheaf (Subtype.val ⁻¹' T) P)
    (α : P ⟶ (derivedRestrict U.ι).obj E) :
    ∃ (R : DerivedCategory (Spec A).Modules) (β : R ⟶ E),
      IsPerfect (X := (Spec A).toRingedSpace) R ∧
      CohomologySupportedOn (Spec A).ringCatSheaf T R ∧
      ∃ e : P ⊞ P⟦(1 : ℤ)⟧ ≅ (derivedRestrict U.ι).obj R,
        e.hom ≫ (derivedRestrict U.ι).map β = biprod.fst ≫ α := by
  classical
  obtain ⟨Q, hQperf, hQsupp, ⟨ε⟩⟩ :=
    exists_isPerfect_cohomologySupportedOn_biprod_shift_iso_restrict T hT hTc U hU P hP hPT
  obtain ⟨I, -, hIQ, β, γ, hβ, hβγ⟩ :=
    exists_isPerfect_lift_of_isPerfect_of_isDQCoh U hU Q E hQperf hE
      ((schemeDerivedRestrictIsoOpenSubspace (Spec A) U).inv.app Q ≫
        ((ε.inv ≫ biprod.fst ≫ α :
          (derivedRestrict U.ι).obj Q ⟶ (derivedRestrict U.ι).obj E)) ≫
        (schemeDerivedRestrictIsoOpenSubspace (Spec A) U).hom.app E)
  have hβiso : IsIso ((derivedRestrict U.ι).map β) :=
    (NatIso.isIso_map_iff (schemeDerivedRestrictIsoOpenSubspace (Spec A) U) β).mpr hβ
  have heq : (derivedRestrict U.ι).map β ≫ (ε.inv ≫ biprod.fst ≫ α) =
      (derivedRestrict U.ι).map γ :=
    map_comp_conj_eq_map (schemeDerivedRestrictIsoOpenSubspace (Spec A) U) β γ _ hβγ
  refine ⟨_, γ, hIQ,
    cohomologySupportedOn_derivedTensorProduct (Spec A) T hT I Q hQsupp,
    ε ≪≫ (asIso ((derivedRestrict U.ι).map β)).symm, ?_⟩
  rw [← heq]
  simp

/-- **[Stacks, Tag 09IM] over `Spec A`, in the shape the source states it**: `P` is a direct
summand of `R|_U` by an inclusion `i` with `i ≫ β|_U = α`.

This is `Stacks.Perfect.LiftingComplexes.exists_isPerfect_lift_spec` with the identification of
`R|_U` with `P ⊕ P[1]` composed with the inclusion of and the projection to the first summand. -/
theorem exists_isPerfect_lift_summand_spec (T : Set (Spec A)) (hT : IsClosed T)
    (hTc : IsCompact (Tᶜ : Set (Spec A))) (U : (Spec A).Opens)
    (hU : IsCompact (U : Set (Spec A))) (E : DerivedCategory (Spec A).Modules)
    (hE : Stacks.DerivedQCoh.IsDQCoh (R := (Spec A).ringCatSheaf) E)
    (P : DerivedCategory U.toScheme.Modules)
    (hP : IsPerfect (X := U.toScheme.toRingedSpace) P)
    (hPT : CohomologySupportedOn U.toScheme.ringCatSheaf (Subtype.val ⁻¹' T) P)
    (α : P ⟶ (derivedRestrict U.ι).obj E) :
    ∃ (R : DerivedCategory (Spec A).Modules) (β : R ⟶ E),
      IsPerfect (X := (Spec A).toRingedSpace) R ∧
      CohomologySupportedOn (Spec A).ringCatSheaf T R ∧
      ∃ (i : P ⟶ (derivedRestrict U.ι).obj R)
        (p : (derivedRestrict U.ι).obj R ⟶ P),
        i ≫ p = 𝟙 P ∧ i ≫ (derivedRestrict U.ι).map β = α := by
  obtain ⟨R, β, hR, hRT, e, he⟩ :=
    exists_isPerfect_lift_spec T hT hTc U hU E hE P hP hPT α
  refine ⟨R, β, hR, hRT, biprod.inl ≫ e.hom, e.inv ≫ biprod.fst, by simp, ?_⟩
  rw [Category.assoc, he]
  simp

end Stacks.Perfect.LiftingComplexes

end
