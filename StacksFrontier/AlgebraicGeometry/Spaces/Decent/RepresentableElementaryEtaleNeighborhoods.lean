module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.Topology.DiscreteSubset
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.EtaleChartNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.HenselianLocalRingStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeNormalization
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Elementary étale neighbourhoods of a point of a representable algebraic space

Let `W` be an object of the big fppf site of `S` and `w` a point of its scheme. The presheaf
represented by `W` is an algebraic space, and the scheme `W` itself, pointed at `w`, is an
elementary étale neighbourhood of the point of that space which `w` defines.

When `W` is affine, every affine elementary étale neighbourhood `(E, e)` of that point is refined
by one whose distinguished point is the only point above `w`.

## Main definitions

* `AlgebraicGeometry.Space.ElementaryEtaleNeighborhood.self`: the scheme `W` as an elementary
  étale neighbourhood of the point of the represented space defined by `w`.

## Main results

* `AlgebraicGeometry.Space.ElementaryEtaleNeighborhood.exists_hom_of_unique_point`: an affine
  elementary étale neighbourhood is refined by an affine one whose distinguished point is the
  only point above the given one.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

namespace ElementaryEtaleNeighborhood

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The scheme of an object of the site, pointed at one of its points, as an elementary étale
neighbourhood of the point of the represented algebraic space defined by that point. -/
abbrev self (W : BigFppfOver B S hS) (w : W.left.1)
    (hw : B.Contains (Spec (.of (W.left.1.residueField w)))) :
    ElementaryEtaleNeighborhood B S hS (yoneda.obj W) (isAlgebraicSpace_yoneda B S hS W)
      (presheafPoint B S hS W w hw) where
  scheme := W
  point := w
  residueField_contained := hw
  toSpace := 𝟙 _
  etale_toSpace := isEtale_id B S hS _
  map_point := by rw [pointsMap_id]; rfl
  mono_residueField := by
    rw [Category.comp_id]
    have := (BigFppfOver.toScheme B S hS).mono_of_mono_map (f := residueFieldMap B S hS W w hw)
      (inferInstanceAs (Mono (W.left.1.fromSpecResidueField w)))
    infer_instance

/-- The scheme point underlying the image of a point of a represented presheaf under a morphism
of represented presheaves is the image of its scheme point. -/
theorem pointsToScheme_pointsMap_of_eq {U V : BigFppfOver B S hS} (f : U ⟶ V)
    (g : yoneda.obj U ⟶ yoneda.obj V) (hg : yoneda.map f = g)
    (y : points B S hS (yoneda.obj U)) :
    pointsToScheme B S hS V (pointsMap B S hS (yoneda.obj U) g y) =
      (BigFppfOver.toScheme B S hS).map f (pointsToScheme B S hS U y) := by
  subst hg
  exact pointsToScheme_pointsMap B S hS f y

/-- **An affine elementary étale neighbourhood of a point of an affine representable space is
refined by one whose distinguished point is the only point above the given one.** -/
theorem exists_hom_of_unique_point (W : BigFppfOver B S hS) (w : W.left.1)
    (hw : B.Contains (Spec (.of (W.left.1.residueField w))))
    (E : ElementaryEtaleNeighborhood B S hS (yoneda.obj W) (isAlgebraicSpace_yoneda B S hS W)
      (presheafPoint B S hS W w hw)) (hE : IsAffine E.scheme.left.1) :
    ∃ E' : ElementaryEtaleNeighborhood B S hS (yoneda.obj W) (isAlgebraicSpace_yoneda B S hS W)
        (presheafPoint B S hS W w hw),
      IsAffine E'.scheme.left.1 ∧
      (∀ y : points B S hS (yoneda.obj E'.scheme),
        pointsMap B S hS (yoneda.obj E'.scheme) E'.toSpace y = presheafPoint B S hS W w hw →
          y = presheafPoint B S hS E'.scheme E'.point E'.residueField_contained) ∧
      Nonempty (E' ⟶ E) := by
  let q : E.scheme ⟶ W := yoneda.preimage E.toSpace
  have hq : yoneda.map q = E.toSpace := Functor.map_preimage _ _
  let f : E.scheme.left.1 ⟶ W.left.1 := (BigFppfOver.toScheme B S hS).map q
  have hfe : Etale f := (presheaf_yoneda_map_etale_iff B S hS q).mp
    ((isEtale_iff_presheaf_of_yoneda B S hS _).mp (hq.symm ▸ E.etale_toSpace))
  have hlqf : LocallyQuasiFinite f := by
    rw [HasRingHomProperty.iff_appLE (P := @LocallyQuasiFinite)]
    intro U V e
    algebraize [(f.appLE U V e).hom]
    have := RingHom.Etale.toAlgebra (f.etale_appLE U.2 V.2 e)
    exact inferInstanceAs (Algebra.QuasiFinite Γ(W.left.1, U) Γ(E.scheme.left.1, V))
  have hpt : ∀ {V : BigFppfOver B S hS} (r : V ⟶ E.scheme) (y : points B S hS (yoneda.obj V)),
      pointsMap B S hS (yoneda.obj V) (yoneda.map r ≫ E.toSpace) y =
          presheafPoint B S hS W w hw →
        f ((BigFppfOver.toScheme B S hS).map r (pointsToScheme B S hS V y)) = w := by
    intro V r y hy
    have h1 := congrArg (pointsToScheme B S hS W) hy
    rw [pointsToScheme_presheafPoint, ← hq, ← Functor.map_comp,
      pointsToScheme_pointsMap] at h1
    simpa [f] using h1
  have hew : f E.point = w := by
    simpa [pointsToScheme_presheafPoint] using
      hpt (𝟙 _) (presheafPoint B S hS E.scheme E.point E.residueField_contained)
        (by rw [yoneda.map_id, Category.id_comp]; exact E.map_point)
  obtain ⟨o, ho, hos⟩ := isDiscrete_iff_forall_mem_exists_isOpen.mp
    (f.isDiscrete_preimage_singleton w) E.point hew
  obtain ⟨g, hgo, hge⟩ := (isAffineOpen_top E.scheme.left.1).exists_basicOpen_le
    (V := ⟨o, ho⟩) ⟨E.point, (Set.ext_iff.mp hos E.point).mpr rfl |>.1⟩ trivial
  let O := E.scheme.left.1.basicOpen g
  have hO : IsAffineOpen O := (isAffineOpen_top E.scheme.left.1).basicOpen g
  let E' := openRestrictionNeighborhood B S hS (yoneda.obj W) (isAlgebraicSpace_yoneda B S hS W)
    (presheafPoint B S hS W w hw) E O hge
  refine ⟨E', hO, ?_, ⟨openRestrictionNeighborhoodHom B S hS (yoneda.obj W)
    (isAlgebraicSpace_yoneda B S hS W) (presheafPoint B S hS W w hw) E le_top hge trivial ≫
      openRestrictionNeighborhoodToOriginal B S hS (yoneda.obj W)
        (isAlgebraicSpace_yoneda B S hS W) (presheafPoint B S hS W w hw) E⟩⟩
  intro y hy
  have h := hpt (openRestrictionMap B S hS (yoneda.obj W) (isAlgebraicSpace_yoneda B S hS W)
    (presheafPoint B S hS W w hw) E O) y hy
  set y₀ := pointsToScheme B S hS E'.scheme y
  have hmem : y₀.1 ∈ o ∩ f ⁻¹' {w} := ⟨hgo y₀.2, h⟩
  rw [hos] at hmem
  exact injective_pointsToScheme B S hS E'.scheme
    (by rw [pointsToScheme_presheafPoint]; exact Subtype.ext hmem)

end ElementaryEtaleNeighborhood

end AlgebraicGeometry.Space

end
