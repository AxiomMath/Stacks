module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VeryWeakBivariantCriterion
public import StacksFrontier.AlgebraicGeometry.NodalContraction.Basic

/-!
# The fibre of a contraction over its centre, and its generic stalk
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The kernel of the canonical morphism from the spectrum of the residue field at a closed
point is the vanishing ideal of that point. -/
public theorem ker_fromSpecResidueField (X : Scheme.{u}) (x : X)
    (hx : IsClosed ({x} : Set X)) :
    (X.fromSpecResidueField x).ker =
      Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) := by
  have h := Scheme.IdealSheafData.map_vanishingIdeal (X.fromSpecResidueField x) ⊤
  have hc : Closeds.closure ({x} : Set X) = (⟨{x}, hx⟩ : Closeds X) := by
    ext; simp
  simpa [Scheme.IdealSheafData.vanishingIdeal_top, Scheme.nilradical_eq_bot,
    Scheme.range_fromSpecResidueField, hc] using h

/-- The scheme-theoretic fibre of a morphism over a closed point is the closed subscheme cut out
by the inverse image of the vanishing ideal of that point. -/
public theorem exists_fiberIso_subscheme_comap_vanishingIdeal {X Y : Scheme.{u}} (b : X ⟶ Y)
    (z : Y) (hz : IsClosed ({z} : Set Y)) :
    ∃ e : b.fiber z ≅
        ((Scheme.IdealSheafData.vanishingIdeal (⟨{z}, hz⟩ : Closeds Y)).comap b).subscheme,
      e.hom ≫ ((Scheme.IdealSheafData.vanishingIdeal
        (⟨{z}, hz⟩ : Closeds Y)).comap b).subschemeι = b.fiberι z := by
  have : IsClosedImmersion (Y.fromSpecResidueField z) :=
    isClosed_singleton_iff_isClosedImmersion.mp hz
  have : IsClosedImmersion (b.fiberι z) :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion)
      (IsPullback.of_hasPullback b (Y.fromSpecResidueField z)).flip inferInstance
  have hker : (b.fiberι z).ker =
      (Scheme.IdealSheafData.vanishingIdeal (⟨{z}, hz⟩ : Closeds Y)).comap b := by
    rw [← ker_fromSpecResidueField Y z hz]
    exact Scheme.IdealSheafData.ker_fst_of_isClosedImmersion (Y.fromSpecResidueField z) b
  exact ⟨Stacks.Chow.isoSubschemeOfKer (b.fiberι z) _ hker,
    Stacks.Chow.isoSubschemeOfKer_hom_subschemeι (b.fiberι z) _ hker⟩

/-- **At the generic point of the exceptional curve the fibre of the contraction has a field as
its local ring.** The fibre over the centre is the exceptional curve, an integral scheme, so its
local ring at the generic point is its function field. -/
public theorem exists_isField_stalk_fiber_of_isContractionOfExceptionalCurve
    {X X' : Scheme.{u}} (D : X.IdealSheafData) (k : Type u) [Field k]
    (e : projectiveLineProj k ≅ D.subscheme)
    (b : X ⟶ X') (z : X') (hz : IsClosed ({z} : Set X'))
    (hDz : D = (Scheme.IdealSheafData.vanishingIdeal (⟨{z}, hz⟩ : Closeds X')).comap b) :
    ∃ x : D.subscheme,
      IsField ((b.fiber (b (D.subschemeι x))).presheaf.stalk
        (b.asFiber (D.subschemeι x))) := by
  have := isIntegral_subscheme_of_iso_projectiveLineProj D k e
  have hcentre : ∀ y : D.subscheme, b (D.subschemeι y) = z := fun y =>
    IsContractionOfExceptionalCurve.eq_centre_of_mem_support hDz
      (by rw [← D.range_subschemeι]; exact ⟨y, rfl⟩)
  subst hDz
  obtain ⟨ε, hε⟩ := exists_fiberIso_subscheme_comap_vanishingIdeal b z hz
  refine ⟨genericPoint _, ?_⟩
  set x := genericPoint
    ((Scheme.IdealSheafData.vanishingIdeal (⟨{z}, hz⟩ : Closeds X')).comap b).subscheme with hx
  have hc : b (((Scheme.IdealSheafData.vanishingIdeal
    (⟨{z}, hz⟩ : Closeds X')).comap b).subschemeι x) = z := hcentre x
  have : Nonempty (b.fiber z) := ⟨ε.inv x⟩
  have : IsIntegral (b.fiber z) := isIntegral_of_isOpenImmersion ε.hom
  have hgen : ε.inv x = genericPoint (b.fiber z) := genericPoint_eq_of_isOpenImmersion ε.inv
  have hd : b.fiberι z (ε.inv x) = ((Scheme.IdealSheafData.vanishingIdeal
      (⟨{z}, hz⟩ : Closeds X')).comap b).subschemeι x := by
    have h := congrArg (fun q => q (ε.inv x)) hε
    simpa using h.symm
  generalize hydef : b.asFiber (((Scheme.IdealSheafData.vanishingIdeal
    (⟨{z}, hz⟩ : Closeds X')).comap b).subschemeι x) = y
  have hiy : b.fiberι (b (((Scheme.IdealSheafData.vanishingIdeal
      (⟨{z}, hz⟩ : Closeds X')).comap b).subschemeι x)) y =
      ((Scheme.IdealSheafData.vanishingIdeal
        (⟨{z}, hz⟩ : Closeds X')).comap b).subschemeι x := by
    rw [← hydef]; exact b.fiberι_asFiber _
  clear hydef
  revert y
  rw [hc]
  intro y hiy
  have hy : y = ε.inv x := (b.fiberι z).isEmbedding.injective (hiy.trans hd.symm)
  rw [hy, hgen]
  exact Field.toIsField (b.fiber z).functionField

end AlgebraicGeometry

end
