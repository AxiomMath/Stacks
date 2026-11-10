module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Jacobson
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Jacobson
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.Dimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PointsOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback

/-!
# Closed points of a scheme above a finite type point

Let `X` be a Jacobson algebraic space over a scheme `S` and let `g : W ⟶ X` be a morphism
locally of finite type whose source is represented by a scheme. A finite type point of `X`
lying in the image of `g` is then the image of a *closed* point of that scheme.

On a Jacobson scheme the finite type points are exactly the closed points, so the statement
is an instance of the fact that a morphism locally of finite type between Jacobson schemes
carries closed points to closed points. The reduction to that fact uses an affine étale chart
`U ⟶ X` carrying a closed point above the given one, which exists by Stacks 06EH, and the
fibre product `W ×_X U`, which is again a scheme because the diagonal of `X` is
representable.

## Main results

* `AlgebraicGeometry.Space.exists_isClosed_pointsToScheme_of_isFiniteTypePoint`:
  **Stacks 0BA4**.

## Implementation notes

The Jacobson condition on `X` is written out as the existence of a surjective étale atlas by
a Jacobson scheme, which is the form
`AlgebraicGeometry.Space.exists_jacobson_atlas_of_isLocallyOfFiniteType` — Stacks 0BA3 —
consumes and produces. Inside the proof that existence is converted into the Jacobson
property of *every* étale scheme chart by Stacks 03E8, which applies because being Jacobson
is local for the fppf topology (Stacks 0368,
`AlgebraicGeometry.jacobsonSpace_isLocal_fppf`) and therefore for the étale topology.

A point of the scheme representing `W` is recorded here as a point of the presheaf it
represents together with its image `AlgebraicGeometry.Space.pointsToScheme` in the
scheme, the two being the same datum by clause (1) of Stacks 03BX; this is the datum the map
on points of Stacks 03BU acts on, so the conclusion is stated with it.

## References

* [Stacks Project, Tag 0368](https://stacks.math.columbia.edu/tag/0368)
* [Stacks Project, Tag 01TB](https://stacks.math.columbia.edu/tag/01TB)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 03E8](https://stacks.math.columbia.edu/tag/03E8)
* [Stacks Project, Tag 06EH](https://stacks.math.columbia.edu/tag/06EH)
* [Stacks Project, Tag 0BA3](https://stacks.math.columbia.edu/tag/0BA3)
* [Stacks Project, Tag 0BA4](https://stacks.math.columbia.edu/tag/0BA4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0BA4.** Let `X` be a Jacobson algebraic space over `S`, written as having a
surjective étale atlas by a Jacobson scheme, and let `g : h_W ⟶ X` be locally of finite type
with `W` an object of the big fppf site of `S`. A finite type point of `X` in the image of `g`
is the image of a point of `h_W` whose underlying point of the scheme `W` is closed. -/
@[stacks 0BA4]
theorem exists_isClosed_pointsToScheme_of_isFiniteTypePoint
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hJac : ∃ (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) a ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) a ∧
      JacobsonSpace ((BigFppfOver.toScheme B S hS).obj U))
    (W : BigFppfOver B S hS) (g : yoneda.obj W ⟶ X)
    (hg : IsLocallyOfFiniteType B S hS g)
    (x : points B S hS X) (hx : IsFiniteTypePoint B S hS X x)
    (himage : x ∈ Set.range (pointsMap B S hS (yoneda.obj W) g)) :
    ∃ y : points B S hS (yoneda.obj W),
      IsClosed ({pointsToScheme B S hS W y} :
        Set ((BigFppfOver.toScheme B S hS).obj W)) ∧
      pointsMap B S hS (yoneda.obj W) g y = x := by
  classical
  have _ : ObjectProperty.IsLocal (fun Z : Scheme.{u} ↦ JacobsonSpace Z)
      Scheme.etalePrecoverage :=
    ObjectProperty.IsLocal.of_le Scheme.etalePrecoverage_le_fppfPrecoverage
  have _ : HasBinaryProducts (BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  -- A Jacobson atlas makes every étale scheme chart, in particular the identity, Jacobson.
  have jacobson_of_atlas (V : BigFppfOver B S hS) :
      HasEtaleLocalProperty B S hS (yoneda.obj V) (fun Z : Scheme.{u} ↦ JacobsonSpace Z) →
      JacobsonSpace ((BigFppfOver.toScheme B S hS).obj V) := fun h ↦
    (exists_atlas_iff_forall_etale B S hS (yoneda.obj V) _
      (isAlgebraicSpace_yoneda B S hS V)).mp h V (𝟙 _) (presheaf_etale_id B S hS V)
  obtain ⟨w, hw⟩ := himage
  -- An affine étale chart of `X` with a closed point above `x`, by Stacks 06EH.
  obtain ⟨U, φ, p, -, hφEtale, hclosed, hpoint⟩ :=
    (isFiniteTypePoint_iff_exists_isAffine_isClosed_etaleChart B S hS X hX x).mp hx
  have hWAlg : IsAlgebraicSpace B S hS (yoneda.obj W) := isAlgebraicSpace_yoneda B S hS W
  have hUAlg : IsAlgebraicSpace B S hS (yoneda.obj U) := isAlgebraicSpace_yoneda B S hS U
  -- `W` is Jacobson, being locally of finite type over `X`.
  have hWJacAtlas := exists_jacobson_atlas_of_isLocallyOfFiniteType B S hS hX hWAlg g hg hJac
  have _ := jacobson_of_atlas W hWJacAtlas
  -- The fibre product `h_W ×_X h_U`, as a represented presheaf.
  have hrep : yoneda.relativelyRepresentable g :=
    (Functor.relativelyRepresentable.diag_iff (F := yoneda) (X := X)).mp
      hX.diagonal_representable g
  obtain ⟨R, r, s, hsq⟩ : ∃ (R : BigFppfOver B S hS) (r : R ⟶ W) (s : R ⟶ U),
      IsPullback (yoneda.map r) (yoneda.map s) g φ := by
    refine ⟨hrep.pullback φ, yoneda.preimage (hrep.fst φ), hrep.snd φ, ?_⟩
    rw [yoneda.map_preimage]
    exact hrep.isPullback φ
  have hRAlg : IsAlgebraicSpace B S hS (yoneda.obj R) := isAlgebraicSpace_yoneda B S hS R
  -- The square, read in the category of algebraic spaces over `S`.
  have hsqR : IsPullback
      (ObjectProperty.homMk (yoneda.map r) :
        (⟨yoneda.obj R, hRAlg⟩ : AlgebraicSpaces B S hS) ⟶ ⟨yoneda.obj W, hWAlg⟩)
      (ObjectProperty.homMk (yoneda.map s) :
        (⟨yoneda.obj R, hRAlg⟩ : AlgebraicSpaces B S hS) ⟶ ⟨yoneda.obj U, hUAlg⟩)
      (ObjectProperty.homMk g :
        (⟨yoneda.obj W, hWAlg⟩ : AlgebraicSpaces B S hS) ⟶ ⟨X, hX⟩)
      (ObjectProperty.homMk φ :
        (⟨yoneda.obj U, hUAlg⟩ : AlgebraicSpaces B S hS) ⟶ ⟨X, hX⟩) :=
    IsPullback.of_map_of_faithful
      (F := ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u ↦
        IsAlgebraicSpace B S hS F)) hsq
  have hrLft : IsLocallyOfFiniteType B S hS (yoneda.map r) :=
    isLocallyOfFiniteType_of_isEtale B S hS hWAlg
      (isEtale_of_isPullback B S hS _ _ _ _ hsqR.flip hφEtale)
  -- Hence `R` is Jacobson too, being étale over `W`.
  have _ := jacobson_of_atlas R
    (exists_jacobson_atlas_of_isLocallyOfFiniteType B S hS hWAlg hRAlg
      (yoneda.map r) hrLft hWJacAtlas)
  -- The fibre of `R ⟶ U` above the chosen point of `U` is nonempty and closed.
  obtain ⟨z, hzW, hzU⟩ :=
    exists_point_of_isPullback B S hS hsqR w (p.class B S hS (yoneda.obj U))
      (hw.trans hpoint.symm)
  have hzFibre : (BigFppfOver.toScheme B S hS).map s (pointsToScheme B S hS R z) =
      schemePoint B S hS U p := by
    rw [← pointsToScheme_pointsMap B S hS s z]
    exact congrArg (pointsToScheme B S hS U) hzU
  -- A closed point of `R` in that fibre, `R` being Jacobson.
  obtain ⟨y, hyFibre, hyClosed⟩ :=
    nonempty_inter_closedPoints
      (Z := (BigFppfOver.toScheme B S hS).map s ⁻¹' {schemePoint B S hS U p})
      ⟨pointsToScheme B S hS R z, hzFibre⟩
      (hclosed.preimage ((BigFppfOver.toScheme B S hS).map s).continuous).isLocallyClosed
  -- Its image in `W` is closed, `r` being locally of finite type and `W` Jacobson.
  set c : points B S hS (yoneda.obj R) :=
    (schemePointRepresentative B S hS R y).class B S hS (yoneda.obj R)
  have hc : pointsToScheme B S hS R c = y :=
    schemePointRepresentative_point B S hS R y
  refine ⟨pointsMap B S hS (yoneda.obj R) (yoneda.map r) c, ?_, ?_⟩
  · rw [pointsToScheme_pointsMap B S hS r c, hc]
    have _ : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map r) :=
      hrLft R W (𝟙 (yoneda.obj R)) (𝟙 (yoneda.obj W)) r (presheaf_etale_id B S hS R)
        (presheaf_etale_id B S hS W) (by simp)
    exact ((BigFppfOver.toScheme B S hS).map r).closedPoints_subset_preimage_closedPoints
      hyClosed
  · have hsClass : pointsMap B S hS (yoneda.obj R) (yoneda.map s) c =
        p.class B S hS (yoneda.obj U) := by
      refine injective_pointsToScheme B S hS U ?_
      rw [pointsToScheme_pointsMap B S hS s c, hc]
      exact hyFibre
    rw [← pointsMap_comp_apply, hsq.w, pointsMap_comp_apply, hsClass, hpoint]

end AlgebraicGeometry.Space

end
