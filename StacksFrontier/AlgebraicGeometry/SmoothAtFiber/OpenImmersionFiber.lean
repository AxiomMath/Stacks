module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The fibre of a morphism precomposed with an open immersion

Let `j : P ⟶ X` be an open immersion, let `f : X ⟶ Y` and let `y : Y`.  The scheme-theoretic
fibre of `j ≫ f` over `y` is an open subscheme of the fibre of `f` over `y`, compatibly with
the two maps to `Spec κ(y)` and with the two embeddings into `P` and into `X`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.fiberMapOfComp`: the morphism `(j ≫ f).fiber y ⟶ f.fiber y`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.fiberMapOfComp_fiberToSpecResidueField`: the map to
  `Spec κ(y)` from the smaller fibre factors through the larger one.
* `AlgebraicGeometry.Scheme.Hom.fiberMapOfComp_fiberι`: compatibility with the embeddings of
  the fibres into the sources.
* `AlgebraicGeometry.Scheme.Hom.range_fiberMapOfComp`: the image of that open immersion is the
  part of the fibre of `f` lying over the image of `j`.

## Implementation notes

Both fibres are pullbacks, and the comparison is the pasting isomorphism
`CategoryTheory.Limits.pullbackRightPullbackFstIso` for the two squares over
`P ⟶ X ⟶ Y ⟵ Spec κ(y)`: it presents `(j ≫ f).fiber y` as `P ×_X (f.fiber y)`, which is the
pullback of the open immersion `j` along `f.fiberι y` and hence an open subscheme of
`f.fiber y`.  Both compatibilities are then instances of the `pullbackRightPullbackFstIso`
projection lemmas, and the image is `AlgebraicGeometry.Scheme.Pullback.range_snd` transported
along that isomorphism.

## References

* [Stacks Project, Tag 01V9](https://stacks.math.columbia.edu/tag/01V9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Precomposing with an isomorphism does not change the set of points in the image. -/
public theorem Scheme.range_comp_of_isIso {A B C : Scheme.{u}} (i : A ⟶ B) [IsIso i]
    (h : B ⟶ C) : Set.range (i ≫ h) = Set.range h := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨z, rfl⟩
    exact ⟨i z, Scheme.Hom.comp_apply i h z⟩
  · rintro _ ⟨z, rfl⟩
    refine ⟨inv i z, ?_⟩
    have h1 : i (inv i z) = z := by
      rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
      simp
    exact (Scheme.Hom.comp_apply i h (inv i z)).trans (congrArg (fun w => h w) h1)

namespace Scheme.Hom

variable {P X Y : Scheme.{u}} (j : P ⟶ X) (f : X ⟶ Y) (y : Y)

/-- The fibre of `j ≫ f` over `y` as a scheme over the fibre of `f` over `y`; it is an open
immersion when `j` is one. -/
@[ega "IV 17.7.11", sga "7 XVIII 5.1"]
public noncomputable def fiberMapOfComp : (j ≫ f).fiber y ⟶ f.fiber y :=
  (pullbackRightPullbackFstIso f (Y.fromSpecResidueField y) j).inv ≫
    pullback.snd j (f.fiberι y)

/-- If `j` is an open immersion, then the map of fibres `fiberMapOfComp j f y` is an open
immersion. -/
instance isOpenImmersion_fiberMapOfComp [IsOpenImmersion j] :
    IsOpenImmersion (fiberMapOfComp j f y) :=
  MorphismProperty.comp_mem (W := @IsOpenImmersion)
    (pullbackRightPullbackFstIso f (Y.fromSpecResidueField y) j).inv
    (pullback.snd j (f.fiberι y)) inferInstance
    (MorphismProperty.pullback_snd (P := @IsOpenImmersion) _ _ inferInstance)

/-- The map from the fibre of `j ≫ f` to `Spec κ(y)` is the restriction of the corresponding
map for `f`. -/
@[reassoc (attr := simp)]
public theorem fiberMapOfComp_fiberToSpecResidueField :
    fiberMapOfComp j f y ≫ f.fiberToSpecResidueField y =
      (j ≫ f).fiberToSpecResidueField y :=
  pullbackRightPullbackFstIso_inv_snd_snd f (Y.fromSpecResidueField y) j

/-- The map of fibres is compatible with the embeddings of the fibres into the sources. -/
@[reassoc (attr := simp), sga "7 XVIII 5.1" "k∘h = i∘ℓ"]
public theorem fiberMapOfComp_fiberι :
    fiberMapOfComp j f y ≫ f.fiberι y = (j ≫ f).fiberι y ≫ j :=
  pullbackRightPullbackFstIso_inv_snd_fst f (Y.fromSpecResidueField y) j

/-- On points, the map of fibres carries the image in `P` of a point of the smaller fibre to
its image in `X`. -/
public theorem fiberι_fiberMapOfComp_apply (z : (j ≫ f).fiber y) :
    f.fiberι y (fiberMapOfComp j f y z) = j ((j ≫ f).fiberι y z) := by
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, fiberMapOfComp_fiberι]

/-- The image of the map of fibres is the part of the fibre of `f` lying over the image
of `j`. -/
public theorem range_fiberMapOfComp :
    Set.range (fiberMapOfComp j f y) = f.fiberι y ⁻¹' Set.range j :=
  (Scheme.range_comp_of_isIso
      (pullbackRightPullbackFstIso f (Y.fromSpecResidueField y) j).inv
      (pullback.snd j (f.fiberι y))).trans
    (Scheme.Pullback.range_snd j (f.fiberι y))

end Scheme.Hom

end AlgebraicGeometry

end
