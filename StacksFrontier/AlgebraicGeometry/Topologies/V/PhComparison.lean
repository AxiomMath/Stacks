module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import Mathlib.RingTheory.Valuation.LocalSubring
public import StacksFrontier.AlgebraicGeometry.Topologies.Ph.Coverings
public import StacksFrontier.AlgebraicGeometry.Topologies.V.Coverings
public import StacksCore.Tactic.StacksAttribute

/-!
# Ph coverings are V coverings

A standard ph covering of an affine scheme is a standard V covering, because a proper
surjection satisfies the valuative lifting condition after an extension of valuation rings.
Consequently every ph covering is a V covering.

## Main results

* `AlgebraicGeometry.StandardPHCovering.isStandardVCovering`: a standard ph covering is a
  standard V covering.
* `AlgebraicGeometry.isVCovering_of_isPHCovering`: every ph covering is a V covering.

## Implementation notes

The lifting is produced from Mathlib's valuative criterion for proper morphisms: a map from
the spectrum of a valuation ring into the base lifts to the source of the presenting proper
surjection after replacing the valuation ring by an extension dominating the local ring of
the lifted point, and the affine open cover of that source then selects a member of the
family.  Passing from the standard statement to the general one is immediate, since both
`AlgebraicGeometry.IsPHCovering` and `AlgebraicGeometry.IsVCovering` are affine-local on the
target with the same shape of refinement data.

## References

* [Stacks Project, Tag 0ETD](https://stacks.math.columbia.edu/tag/0ETD)
* [Stacks Project, Tag 0ETK](https://stacks.math.columbia.edu/tag/0ETK)
* [Stacks Project, Tag 0ETR](https://stacks.math.columbia.edu/tag/0ETR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v

namespace AlgebraicGeometry

/-- A standard ph covering is a standard V covering. -/
@[stacks 0ETD]
public theorem StandardPHCovering.isStandardVCovering
    {T : Scheme.{u}} [IsAffine T] {I : Type v} {X : I → Scheme.{u}}
    {f : ∀ i, X i ⟶ T} (hf : StandardPHCovering f) :
    @IsStandardVCovering T _ I hf.finite X hf.isAffine f := by
  have : Finite I := hf.finite
  have : ∀ i, IsAffine (X i) := hf.isAffine
  rw [isStandardVCovering_iff]
  obtain ⟨U, p, j, hp, hp_surj, hj, hcover, hcomp⟩ := hf.exists_presentation
  intro V _ _ _ g
  let K := FractionRing V
  let : Field K := inferInstance
  let gK : Spec (.of K) ⟶ T := Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ g
  obtain ⟨x, hx⟩ := (surjective_iff p).mp hp_surj (gK (genericPoint (Spec (.of K))))
  obtain ⟨z, _, _⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := p) (g := gK) x (genericPoint (Spec (.of K))) hx
  let P := Limits.pullback p gK
  let L := P.residueField z
  let ρ : Spec (.of L) ⟶ P := P.fromSpecResidueField z
  let zK := Limits.pullback.snd p gK z
  let kρ : (Spec (.of K)).residueField zK ⟶ CommRingCat.of L :=
    (Limits.pullback.snd p gK).residueFieldMap z
  let kK : CommRingCat.of K ⟶ (Spec (.of K)).residueField zK :=
    Spec.preimage ((Spec (.of K)).fromSpecResidueField zK)
  let eK : K →+* L := (kK ≫ kρ).hom
  let eV : V →+* L := eK.comp (algebraMap V K)
  have heV : Function.Injective eV :=
    (RingHom.injective eK).comp (FaithfulSMul.algebraMap_injective V K)
  obtain ⟨W, hle, hlocal⟩ := (LocalSubring.range eV).exists_le_valuationSubring
  let r : V →+* (LocalSubring.range eV).toSubring := eV.rangeRestrict
  have : IsLocalHom r := IsLocalHom.of_surjective r eV.rangeRestrict_surjective
  let e : V →+* W := (Subring.inclusion hle).comp r
  have : IsLocalHom (Subring.inclusion hle) := hlocal
  have : IsLocalHom e := RingHom.isLocalHom_comp (Subring.inclusion hle) r
  have he : Function.Injective e := fun a b hab => heV (congrArg (fun x : W => (x : L)) hab)
  let iL : Spec (.of L) ⟶ U := ρ ≫ Limits.pullback.fst p gK
  let iW : Spec (.of W) ⟶ T := Spec.map (CommRingCat.ofHom e) ≫ g
  have heVL : (algebraMap W L).comp e = eV := by ext a; rfl
  have hres := Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField
    (Limits.pullback.snd p gK) z
  have hSpecV : ρ ≫ Limits.pullback.snd p gK ≫
      Spec.map (CommRingCat.ofHom (algebraMap V K)) = Spec.map (CommRingCat.ofHom eV) := by
    dsimp [P, ρ]
    calc
      _ = ((Limits.pullback p gK).fromSpecResidueField z ≫ Limits.pullback.snd p gK) ≫
          Spec.map (CommRingCat.ofHom (algebraMap V K)) := by simp only [Category.assoc]
      _ = (Spec.map kρ ≫ (Spec (.of K)).fromSpecResidueField zK) ≫
          Spec.map (CommRingCat.ofHom (algebraMap V K)) :=
        congrArg (fun q : Spec (.of L) ⟶ Spec (.of K) =>
          q ≫ Spec.map (CommRingCat.ofHom (algebraMap V K))) hres.symm
      _ = Spec.map (CommRingCat.ofHom eV) := by
        rw [← Spec.map_preimage ((Spec (.of K)).fromSpecResidueField zK), ← Spec.map_comp,
          ← Spec.map_comp]
        congr 1
  have hSpecExtend :
      Spec.map (CommRingCat.ofHom (algebraMap W L)) ≫ Spec.map (CommRingCat.ofHom e) =
        Spec.map (CommRingCat.ofHom eV) := by rw [← Spec.map_comp]; congr 1
  let S : ValuativeCommSq p :=
    { R := W
      K := L
      i₁ := iL
      i₂ := iW
      commSq := ⟨by
        dsimp [iL, iW]
        calc
          _ = ρ ≫ (Limits.pullback.fst p gK ≫ p) := by simp [Category.assoc]
          _ = ρ ≫ (Limits.pullback.snd p gK ≫ gK) := by rw [Limits.pullback.condition]
          _ = ρ ≫ Limits.pullback.snd p gK ≫
                Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ g := by
            simp [gK]
          _ = Spec.map (CommRingCat.ofHom eV) ≫ g := by
            simpa only [Category.assoc] using congrArg
              (fun k : Spec (.of L) ⟶ Spec (.of V) => k ≫ g) hSpecV
          _ = Spec.map (CommRingCat.ofHom (algebraMap W L)) ≫
                Spec.map (CommRingCat.ofHom e) ≫ g := by
            rw [← hSpecExtend]
            simp only [Category.assoc]⟩ }
  have hcrit : ValuativeCriterion p := by
    have hproper : IsProper p := hp
    rw [IsProper.eq_valuativeCriterion] at hproper
    exact hproper.1.1.1
  let liftData := (hcrit S).some.default
  let lift : Spec (.of W) ⟶ U := liftData.l
  have hlift₂ : lift ≫ p = iW := liftData.fac_right
  obtain ⟨i, x_i, hxi⟩ := Set.mem_iUnion.mp
    (show lift (IsLocalRing.closedPoint W) ∈ ⋃ i, Set.range (j i) by rw [hcover]; trivial)
  have : IsOpenImmersion (j i) := hj i
  have hsub : Set.range lift ⊆ Set.range (j i) := by
    rintro y ⟨w, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint w).map lift.continuous).mem_open
      (IsOpenImmersion.isOpen_range (j i)) ⟨x_i, hxi⟩
  let h : Spec (.of W) ⟶ X i := IsOpenImmersion.lift (j i) lift hsub
  refine ⟨W, inferInstance, inferInstance, inferInstance, e, ⟨he, inferInstance⟩, i, h, ?_⟩
  calc
    Spec.map (CommRingCat.ofHom e) ≫ g = lift ≫ p := hlift₂.symm
    _ = h ≫ f i := by rw [← IsOpenImmersion.lift_fac (j i) lift hsub, Category.assoc, hcomp]

/-- **Stacks 0ETK.** Every ph covering is a V covering. It needs no finiteness hypothesis on the
members of the family.

This is also one half of Stacks 0ETR, which for a family locally of finite presentation asserts
that being a ph covering and being a V covering are *equivalent*; it carries no 0ETR
registration. The two conditions 0ETR compares are the numbered items of one assertion, that
equivalence, so a single implication is a fragment of that assertion and not a part of it; 0ETR
belongs where the equivalence is stated in full, which is
`AlgebraicGeometry.isPHCovering_iff_isVCovering` in
`StacksFrontier/AlgebraicGeometry/Topologies/V/PhVFlatteningModification.lean`. The converse
implication is `AlgebraicGeometry.isPHCovering_of_isVCovering`, which carries
`AlgebraicGeometry.StandardVCoveringHasPHRefinement`; the inputs the Stacks argument needs for
that predicate are the generic flatness stratification of the base (Stacks 0H3Z),
`AlgebraicGeometry.finitePresentationHasFlatStratification`, and the Raynaud-Gruson flattening
theorem for an admissible blowup (Stacks 0815), and both are available. -/
@[stacks 0ETK "ph_v"]
public theorem isVCovering_of_isPHCovering {T : Scheme.{u}} {I : Type v}
    (X : I → Scheme.{u}) (f : ∀ i, X i ⟶ T)
    (hph : IsPHCovering X f) :
    IsVCovering X f := by
  rcases hph with ⟨_, hph⟩
  intro U hU
  have : IsAffine U.toScheme := hU
  obtain ⟨𝒰, hs, hr⟩ := hph U hU
  exact ⟨𝒰, hs.finite, hs.isAffine, hs.isStandardVCovering, hr⟩

end AlgebraicGeometry
