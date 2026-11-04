module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.StageSituation
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.StageBlowUp
public import StacksFrontier.AlgebraicGeometry.Blowup.IsomorphismOffCenter.Basic
public import StacksFrontier.AlgebraicGeometry.Blowup.FiniteOverLocalDimensionOne

/-!
# Blowing up a closed point, seen from the local ring there

Let `y` be a closed point of a scheme `Y` and let `A` be a local ring isomorphic to `𝒪_{Y, y}`.
The blowup `Y'` of `Y` in `y` is described by two pieces.

* Away from the centre, `Y' ⟶ Y` is an isomorphism: a point of `Y'` not lying over `y` has the
  local ring of its image.
* Over the centre, `Y'` is the blowup `X` of `Spec(A)` in its maximal ideal: the base change of
  `Y' ⟶ Y` along the flat preimmersion `Spec(A) ≅ Spec 𝒪_{Y, y} ⟶ Y` is `X ⟶ Spec(A)`, and the
  resulting morphism `X ⟶ Y'` is injective, an isomorphism on all local rings, maps the fibre
  over the closed point of `Spec(A)` onto the fibre over `y`, and matches closed points of those
  fibres.

## Main results

* `AlgebraicGeometry.blowUpToBase_injective_of_ne`: the blowup is injective away from the
  centre (the isomorphism on local rings there is the library's
  `AlgebraicGeometry.isIso_stalkMap_blowUpToBase_of_ne`).
* `AlgebraicGeometry.exists_hom_blowUp_maximalIdealSheaf_localization`: the comparison morphism
  from the blowup of `Spec(A)` in its maximal ideal, with its five properties.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **The blowup at a closed point is injective away from that point.** -/
theorem blowUpToBase_injective_of_ne {Y : Scheme.{u}} (y : Y) (hy : IsClosed ({y} : Set Y))
    {w₁ w₂ : blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y))}
    (hw : blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)) w₁ ≠ y)
    (h : blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)) w₁ =
      blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)) w₂) :
    w₁ = w₂ :=
  blowUpToBase_injective_of_notMem_support _ (by simpa using hw) h

/-- **The blowup of a closed point near the centre is the blowup of the local ring.** Let `A` be
a local ring isomorphic to the local ring of `Y` at a closed point `y`. There is a morphism `ψ`
from the blowup of `Spec(A)` in its maximal ideal to the blowup of `Y` in `y` which is injective,
an isomorphism on every local ring, lies over `Spec(A) ⟶ Y` (so a point lies over the closed point
of `Spec(A)` exactly when its image lies over `y`), reaches every point over `y`, and matches the
closed points over the two centres. -/
theorem exists_hom_blowUp_maximalIdealSheaf_localization (A : Type u) [CommRing A]
    [IsLocalRing A] {Y : Scheme.{u}} (y : Y) (hy : IsClosed ({y} : Set Y))
    (e : A ≃+* ↑(Y.presheaf.stalk y)) :
    ∃ ψ : blowUp (maximalIdealSheaf A) ⟶
        blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)),
      Function.Injective ψ.base ∧ (∀ x, IsIso (ψ.stalkMap x)) ∧
      (∀ x, blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)) (ψ x) = y ↔
        blowUpToBase (maximalIdealSheaf A) x = closedPoint A) ∧
      (∀ w, blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)) w = y →
        ∃ x, ψ x = w) ∧
      (∀ x, blowUpToBase (maximalIdealSheaf A) x = closedPoint A →
        (IsClosed ({ψ x} : Set (blowUp (Scheme.IdealSheafData.vanishingIdeal
          (⟨{y}, hy⟩ : Closeds Y)))) ↔ IsClosed ({x} : Set (blowUp (maximalIdealSheaf A))))) ∧
      ψ ≫ blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)) =
        blowUpToBase (maximalIdealSheaf A) ≫
          Spec.map (CommRingCat.ofHom (e.symm : ↑(Y.presheaf.stalk y) →+* A)) ≫
            Y.fromSpecStalk y := by
  have : Flat (Y.fromSpecStalk y) := flat_fromSpecStalk Y y
  have : IsLocalHom ((CommRingCat.ofHom (e.symm : ↑(Y.presheaf.stalk y) →+* A)).hom) :=
    IsLocalHom.of_surjective _ e.symm.surjective
  have : IsIso (CommRingCat.ofHom (e.symm : ↑(Y.presheaf.stalk y) →+* A)) :=
    e.symm.toCommRingCatIso.isIso_hom
  set I := Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)
  set g : Spec (.of A) ⟶ Y :=
    Spec.map (CommRingCat.ofHom (e.symm : ↑(Y.presheaf.stalk y) →+* A)) ≫ Y.fromSpecStalk y
    with hg
  have hcomap : I.comap g = maximalIdealSheaf A := by
    rw [hg, Scheme.IdealSheafData.comap_comp, comap_fromSpecStalk_vanishingIdeal_singleton Y y hy,
      comap_maximalIdealSheaf_specMap_ringEquiv]
  have hgy : g.base (closedPoint A) = y :=
    (Scheme.Hom.comp_apply _ _ _).trans
      ((congrArg (fun t => (Y.fromSpecStalk y).base t)
        AlgebraicGeometry.Spec_closedPoint).trans Scheme.fromSpecStalk_closedPoint)
  have hginj : Function.Injective g.base := g.isEmbedding.injective
  have : Flat g := by rw [hg]; infer_instance
  rw [← hcomap]
  obtain ⟨k, hsq⟩ := exists_isPullback_blowUpToBase_comap g I
  have : IsPreimmersion k :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq inferInstance
  have : Flat k := MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq ‹Flat g›
  have hcomm : ∀ x, blowUpToBase I (k x) = g (blowUpToBase (I.comap g) x) := fun x => by
    simpa [Scheme.Hom.comp_apply] using (congrArg (fun t => t.base x) hsq.w).symm
  have hover : ∀ x, blowUpToBase I (k x) = y ↔ blowUpToBase (I.comap g) x = closedPoint A :=
    fun x => by rw [hcomm, ← hgy]; exact hginj.eq_iff
  have hsurj : ∀ w, blowUpToBase I w = y → ∃ x, k x = w := fun w hw =>
    (Scheme.exists_preimage_of_isPullback hsq (closedPoint A) w (hgy.trans hw.symm)).imp
      fun _ => And.right
  refine ⟨k, k.isEmbedding.injective, fun x => isIso_stalkMap_of_flat_isPreimmersion k x,
    hover, hsurj, ?_, hsq.w.symm⟩
  refine fun x hx => ⟨fun hc => ?_, fun hc => closure_subset_iff_isClosed.mp fun z hz => ?_⟩
  · rw [← k.isEmbedding.injective.preimage_image {x}, Set.image_singleton]
    exact hc.preimage k.continuous
  · have hbz : blowUpToBase I z = y := by
      have h1 : blowUpToBase I z ∈ closure ({blowUpToBase I (k x)} : Set Y) :=
        map_mem_closure (blowUpToBase I).continuous hz (Set.mapsTo_singleton.mpr rfl)
      rwa [(hover x).mpr hx, hy.closure_eq] at h1
    obtain ⟨x', rfl⟩ := hsurj z hbz
    have hx' : x' ∈ closure ({x} : Set (blowUp (I.comap g))) := by
      rwa [k.isEmbedding.closure_eq_preimage_closure_image, Set.image_singleton]
    rw [hc.closure_eq, Set.mem_singleton_iff] at hx'
    exact hx' ▸ Set.mem_singleton _

end AlgebraicGeometry

end
