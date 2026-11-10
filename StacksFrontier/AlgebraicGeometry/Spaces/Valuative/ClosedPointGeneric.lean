module

public import StacksFrontier.AlgebraicGeometry.Spaces.Valuative.ExtensionLifts
public import StacksFrontier.AlgebraicGeometry.Spaces.ConstructiblePoints

/-!
# The generic and the closed point of a valuative square

Let `q` be a valuative square, with valuation ring `R` and fraction field `K`. The spectrum of
`R` is irreducible with generic point the image of `Spec K`, and every point of it specializes
to the closed point. On the points of the presheaf represented by `Spec R`:

* the image of the points of `Spec K` is dense, so a morphism `Spec R ⟶ X` has all its points in
  the closure of the image of the generic point;
* every point specializes to the closed point, so a morphism `Spec R ⟶ X` sending the closed
  point into an open set sends every point there.

## Main results

* `AlgebraicGeometry.Space.ValuativeSquare.denseRange_pointsMap_fracHom`: density of the
  generic point.
* `AlgebraicGeometry.Space.ValuativeSquare.range_subset_closure_range_fracHom_comp`: the image
  of a morphism out of `Spec R` lies in the closure of the image of its generic point.
* `AlgebraicGeometry.Space.ValuativeSquare.range_subset_of_closedPoint_mem`: a morphism out of
  `Spec R` sending the closed point into an open set sends every point there.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Topology

universe u

namespace AlgebraicGeometry.Space

namespace ValuativeSquare

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}

attribute [local instance] pointTopology

/-- **The generic point of a valuative square is dense.** The points of `Spec K` have dense image
in the points of `Spec R`. -/
theorem denseRange_pointsMap_fracHom (q : ValuativeSquare f) :
    DenseRange (pointsMap B S hS _ (yoneda.map q.fracHom)) := by
  set hK := schemePointsHomeomorph B S hS (siteObject B S hS q.field_mem
    (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base))
  set hR := schemePointsHomeomorph B S hS (siteObject B S hS q.ring_mem q.base)
  have hcomp : pointsMap B S hS _ (yoneda.map q.fracHom) =
      hR.symm ∘ (BigFppfOver.toScheme B S hS).map q.fracHom ∘ hK := by
    funext x
    simp only [Function.comp_apply]
    rw [← schemePointsHomeomorph_symm_naturality, Homeomorph.symm_apply_apply]
  have hd : DenseRange ((BigFppfOver.toScheme B S hS).map q.fracHom) := by
    change DenseRange (PrimeSpectrum.comap (algebraMap q.R q.K))
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
      (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective q.R q.K)]
    exact bot_le
  rw [hcomp]
  exact hR.symm.surjective.denseRange.comp (hd.comp hK.surjective.denseRange
    ((BigFppfOver.toScheme B S hS).map q.fracHom).continuous) hR.symm.continuous

/-- **A morphism out of `Spec R` lands in the closure of its generic point.** -/
theorem range_subset_closure_range_fracHom_comp (q : ValuativeSquare f)
    (φ : yoneda.obj (siteObject B S hS q.ring_mem q.base) ⟶ Z) :
    Set.range (pointsMap B S hS _ φ) ⊆
      closure (Set.range (pointsMap B S hS _ (yoneda.map q.fracHom ≫ φ))) := by
  rw [pointsMap_comp, Set.range_comp, ← Set.image_univ]
  refine (Set.image_mono (q.denseRange_pointsMap_fracHom.closure_range ▸ subset_rfl)).trans
    (image_closure_subset_closure_image (continuous_pointsMap B S hS _))

/-- **Every point of `Spec R` specializes to the closed point.** -/
theorem specializes_closedPoint (q : ValuativeSquare f)
    (x : points B S hS (yoneda.obj (siteObject B S hS q.ring_mem q.base))) :
    x ⤳ q.closedPoint := by
  set hR := schemePointsHomeomorph B S hS (siteObject B S hS q.ring_mem q.base)
  have hc : hR q.closedPoint = IsLocalRing.closedPoint q.R :=
    IsLocalRing.comap_closedPoint (IsLocalRing.residue q.R)
  have h : hR x ⤳ hR q.closedPoint := by
    rw [hc]
    exact IsLocalRing.specializes_closedPoint (hR x)
  simpa using h.map hR.symm.continuous

/-- **A morphism out of `Spec R` sending the closed point into an open set sends every point
there.** -/
theorem range_subset_of_closedPoint_mem (q : ValuativeSquare f)
    (φ : yoneda.obj (siteObject B S hS q.ring_mem q.base) ⟶ Z) {O : Set (points B S hS Z)}
    (hO : IsOpen O) (h : pointsMap B S hS _ φ q.closedPoint ∈ O) :
    Set.range (pointsMap B S hS _ φ) ⊆ O := by
  rintro _ ⟨x, rfl⟩
  exact ((q.specializes_closedPoint x).map (continuous_pointsMap B S hS _)).mem_open hO h

end ValuativeSquare

end AlgebraicGeometry.Space

end
