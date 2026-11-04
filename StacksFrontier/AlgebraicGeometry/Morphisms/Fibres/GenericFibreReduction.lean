module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Reduction of a generic fibre

For a morphism of schemes, reduction commutes with passage to the fibre over a generic point of
an irreducible component of the base.

## Main results

* `AlgebraicGeometry.comap_nilradical_fiberι` identifies the ideal sheaf defining the base
  change of the reduction with the nilradical ideal sheaf of the fibre.

## Implementation notes

The reduction of a scheme is the closed subscheme defined by its nilradical ideal sheaf.
Pullback of an ideal sheaf describes base change of its closed subscheme, so equality of the
two ideal sheaves gives the claimed canonical equality of reduced closed subschemes. Generic
points of irreducible components are expressed by `genericPoints`.

## References

* [Stacks Project, Tag 054Z](https://stacks.math.columbia.edu/tag/054Z)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A point specializing to a generic point of an irreducible component equals it. -/
private theorem eq_of_specializes_genericPoints {Y : Scheme} {η y : Y}
    (hη : η ∈ genericPoints Y) (hy : y ⤳ η) : y = η := by
  have hsub : closure ({η} : Set Y) ⊆ closure {y} := hy.closure_subset
  have heq : closure ({η} : Set Y) = closure {y} :=
    subset_antisymm hsub (hη.2 (isIrreducible_singleton.closure) hsub)
  exact Inseparable.eq (hy.antisymm (specializes_iff_closure_subset.mpr heq.symm.le))

/-- The local ring at a generic point of an irreducible component has a unique prime ideal. -/
private theorem prime_stalk_eq_closedPoint {Y : Scheme} {η : Y}
    (hη : η ∈ genericPoints Y) (p : PrimeSpectrum (Y.presheaf.stalk η)) :
    p = IsLocalRing.closedPoint (Y.presheaf.stalk η) := by
  let p' : Spec (Y.presheaf.stalk η) := ⟨p.asIdeal, p.2⟩
  apply (Y.fromSpecStalk η).isEmbedding.injective
  show (Y.fromSpecStalk η) p' = (Y.fromSpecStalk η) _
  have hp : (Y.fromSpecStalk η) p' ⤳ η := by
    have hrange : (Y.fromSpecStalk η) p' ∈ Set.range (Y.fromSpecStalk η) := ⟨p', rfl⟩
    rwa [Scheme.range_fromSpecStalk] at hrange
  rw [Scheme.fromSpecStalk_closedPoint]
  exact eq_of_specializes_genericPoints hη hp

/-- A flat local homomorphism of local rings is injective. -/
private theorem injective_of_flat_local {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (φ : R →+* S) (hf : φ.Flat)
    [IsLocalHom φ] : Function.Injective φ := by
  let : Algebra R S := φ.toAlgebra
  have : Module.Flat R S := hf
  exact RingHom.FaithfullyFlat.injective (Module.FaithfullyFlat.of_flat_of_isLocalHom)

/-- The source of a flat preimmersion into a reduced scheme is reduced: flatness and
surjectivity of the stalk maps make them isomorphisms. -/
private theorem isReduced_of_flat_preimmersion {X Y : Scheme} (f : X ⟶ Y)
    [Flat f] [IsPreimmersion f] [IsReduced Y] : IsReduced X := by
  have (x : X) : _root_.IsReduced (X.presheaf.stalk x) := by
    have := isReduced_stalk_of_isReduced Y (f x)
    let e := RingEquiv.ofBijective (f.stalkMap x).hom
      ⟨injective_of_flat_local _ (Flat.stalkMap f x), f.stalkMap_surjective x⟩
    exact isReduced_of_injective e.symm.toRingHom e.symm.injective
  exact isReduced_of_isReduced_stalk X

/-- The canonical morphism from the spectrum of the local ring at a generic point of an
irreducible component is flat. -/
private theorem flat_fromSpecStalk (Y : Scheme) (η : Y) (hη : η ∈ genericPoints Y) :
    Flat (Y.fromSpecStalk η) := by
  apply Flat.of_stalkMap
  intro z
  obtain rfl := prime_stalk_eq_closedPoint hη z
  let g := Y.fromSpecStalk η
  let c := IsLocalRing.closedPoint (Y.presheaf.stalk η)
  have hcomp : IsIso (Scheme.stalkClosedPointTo g) := by
    rw [Scheme.stalkClosedPointTo_fromSpecStalk]
    infer_instance
  change IsIso (g.stalkMap c ≫ (stalkClosedPointIso (.of (Y.presheaf.stalk η))).hom) at hcomp
  have := IsIso.of_isIso_comp_right (g.stalkMap c)
    (stalkClosedPointIso (.of (Y.presheaf.stalk η))).hom
  exact RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso (g.stalkMap c))

/-- The reduction of the fibre over a generic point of an irreducible component is the
base change of the reduction of the source. -/
@[stacks 054Z]
theorem comap_nilradical_fiberι {X Y : Scheme.{u}} (f : X ⟶ Y)
    (η : Y) (hη : η ∈ genericPoints Y) :
    X.nilradical.comap (f.fiberι η) = (f.fiber η).nilradical := by
  have : IsReduced X.nilradical.subscheme := isReduced_nilradical_subscheme X
  have : Flat (Y.fromSpecStalk η) := flat_fromSpecStalk Y η hη
  let redι := X.nilradical.subschemeι
  let q : Spec (Y.residueField η) ⟶ Spec (Y.presheaf.stalk η) := Spec.map (Y.residue η)
  let g : Spec (Y.presheaf.stalk η) ⟶ Y := Y.fromSpecStalk η
  have hT := isReduced_of_flat_preimmersion (pullback.fst (redι ≫ f) g)
  have hsurj : Function.Surjective (Spec.map (Y.residue η)) := fun p ↦
    ⟨default, by rw [Scheme.SpecMap_residue_apply]; exact (prime_stalk_eq_closedPoint hη p).symm⟩
  have hsupp : q.ker.support = ⊤ := by
    apply SetLike.coe_injective
    rw [Scheme.Hom.support_ker, Set.range_eq_univ.mpr hsurj]
    simp
  have hfactor : q.ker ≤ (pullback.snd (redι ≫ f) g).ker := by
    rw [ker_eq_nilradical_of_support_eq_top _ hsupp, Scheme.Hom.ker,
      Scheme.IdealSheafData.le_ofIdeals_iff]
    intro U x hx
    change x ∈ nilradical Γ(Spec (Y.presheaf.stalk η), U) at hx
    exact (IsNilpotent.map (mem_nilradical.mp hx)
      ((pullback.snd (redι ≫ f) g).app U).hom).eq_zero
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : pullback (redι ≫ f) g ⟶ Spec (Y.residueField η),
      ℓ ≫ q = pullback.snd (redι ≫ f) g :=
    ⟨_, IsClosedImmersion.lift_fac _ _ hfactor⟩
  have hqg : q ≫ g = Y.fromSpecResidueField η := rfl
  let tToF : pullback (redι ≫ f) g ⟶ f.fiber η :=
    pullback.lift (pullback.fst (redι ≫ f) g ≫ redι) ℓ (by
      show (pullback.fst (redι ≫ f) g ≫ redι) ≫ f = ℓ ≫ Y.fromSpecResidueField η
      rw [Category.assoc, pullback.condition, ← hℓ, Category.assoc, hqg])
  have htF₁ : tToF ≫ f.fiberι η = pullback.fst (redι ≫ f) g ≫ redι := by
    dsimp [tToF, Scheme.Hom.fiberι, Scheme.Hom.fiber]
    rw [pullback.lift_fst]
  have htF₂ : tToF ≫ f.fiberToSpecResidueField η = ℓ := by
    dsimp [tToF, Scheme.Hom.fiberToSpecResidueField, Scheme.Hom.fiber]
    rw [pullback.lift_snd]
  let tToZ : pullback (redι ≫ f) g ⟶ pullback (f.fiberι η) redι :=
    pullback.lift tToF (pullback.fst (redι ≫ f) g) htF₁
  let zToT : pullback (f.fiberι η) redι ⟶ pullback (redι ≫ f) g :=
    pullback.lift (pullback.snd (f.fiberι η) redι)
      (pullback.fst (f.fiberι η) redι ≫ f.fiberToSpecResidueField η ≫ q) (by
        rw [← pullback.condition_assoc, Scheme.Hom.fiber_fac, ← hqg]
        simp only [Category.assoc])
  have hzT₁ : zToT ≫ pullback.fst (redι ≫ f) g = pullback.snd (f.fiberι η) redι :=
    pullback.lift_fst _ _ _
  have hzT₂ : zToT ≫ pullback.snd (redι ≫ f) g =
      pullback.fst (f.fiberι η) redι ≫ f.fiberToSpecResidueField η ≫ q :=
    pullback.lift_snd _ _ _
  have htZ₁ : tToZ ≫ pullback.fst (f.fiberι η) redι = tToF := pullback.lift_fst _ _ _
  have htZ₂ : tToZ ≫ pullback.snd (f.fiberι η) redι = pullback.fst (redι ≫ f) g :=
    pullback.lift_snd _ _ _
  have hzF : zToT ≫ tToF = pullback.fst (f.fiberι η) redι := by
    apply pullback.hom_ext
    · show (zToT ≫ tToF) ≫ f.fiberι η = pullback.fst _ _ ≫ f.fiberι η
      simp [htF₁, reassoc_of% hzT₁, pullback.condition]
    · apply (cancel_mono q).1
      show (zToT ≫ tToF) ≫ f.fiberToSpecResidueField η ≫ q =
        (pullback.fst _ _ ≫ f.fiberToSpecResidueField η) ≫ q
      simp [reassoc_of% htF₂, hℓ, hzT₂]
  have hZ : IsReduced (pullback (f.fiberι η) X.nilradical.subschemeι) := by
    refine ObjectProperty.prop_of_iso (fun S : Scheme => IsReduced S)
      { hom := tToZ, inv := zToT, hom_inv_id := ?_, inv_hom_id := ?_ } hT
    · apply pullback.hom_ext
      · simp [hzT₁, htZ₂]
      · simp [hzT₂, reassoc_of% htZ₁, reassoc_of% htF₂, hℓ]
    · apply pullback.hom_ext
      · show zToT ≫ tToZ ≫ pullback.fst (f.fiberι η) redι = 𝟙 _ ≫ pullback.fst (f.fiberι η) redι
        rw [htZ₁, hzF, Category.id_comp]
      · show zToT ≫ tToZ ≫ pullback.snd (f.fiberι η) redι = 𝟙 _ ≫ pullback.snd (f.fiberι η) redι
        rw [htZ₂, hzT₁, Category.id_comp]
  let i := pullback.fst (f.fiberι η) X.nilradical.subschemeι
  have hker : i.ker = X.nilradical.comap (f.fiberι η) := by
    rw [Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
      Scheme.IdealSheafData.ker_subschemeι]
  rw [← hker]
  refine ker_eq_nilradical_of_support_eq_top i (SetLike.coe_injective ?_)
  rw [hker, Scheme.IdealSheafData.support_comap, Scheme.support_nilradical]
  simp

end AlgebraicGeometry
