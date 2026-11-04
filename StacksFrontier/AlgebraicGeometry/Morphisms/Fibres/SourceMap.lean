module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Functoriality of the scheme-theoretic fibre in the source

Mathlib's `AlgebraicGeometry.Scheme.Hom.fiber` is functorial in the target variable only: there
is no comparison morphism between `(i ≫ f).fiber y` and `f.fiber y` for a morphism `i : Z ⟶ X`
of sources. This file supplies it, together with the structural fact that makes it useful: the
comparison morphism is the base change of `i` along `f.fiberι y`, so every property stable under
base change transfers to it, and its set-theoretic image is the preimage of the image of `i`.

The intended consumer is a closed subscheme `Z ⊆ X` cut out by an ideal sheaf `I`. There the
comparison identifies the fibre of `Z` over `y` with the part of the fibre of `X` over `y` that
lies in the support of `I`, which is the form in which Stacks 053R speaks about `Z_s`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.fiberMap`: the morphism `(i ≫ f).fiber y ⟶ f.fiber y` induced by
  `i : Z ⟶ X`.
* `AlgebraicGeometry.Scheme.Hom.fiberMapHomeo`: for `i` a preimmersion, the induced
  homeomorphism from `(i ≫ f).fiber y` onto the preimage of the range of `i` in `f.fiber y`.
* `AlgebraicGeometry.Scheme.IdealSheafData.fiberHomeo`: the same homeomorphism for the closed
  subscheme cut out by an ideal sheaf, with the range of `i` replaced by the support.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isPullback_fiberMap`: `fiberMap` is the base change of `i` along
  the fibre inclusion `f.fiberι y`.
* `AlgebraicGeometry.Scheme.Hom.range_fiberMap`: its range is `f.fiberι y ⁻¹' Set.range i`.
* `AlgebraicGeometry.Scheme.Hom.isEmpty_fiber_comp_iff` and
  `AlgebraicGeometry.Scheme.IdealSheafData.isEmpty_fiber_comp_iff`: emptiness of the fibre of a
  composite, in the pointwise form used when a closed subscheme is assumed to miss a fibre.

## Implementation notes

`fiberMap` takes the ambient morphism first, so that it reads `f.fiberMap i y`; the top-level
name `AlgebraicGeometry.fiberMap` is already taken by the comparison morphism of fibres over two
different bases.

The two morphisms out of `(i ≫ f).fiber y` to `Spec (Y.residueField y)` agree with each other
through `fiberMap` by `fiberMap_fiberToSpecResidueField`, so the comparison is a morphism of
`Spec (Y.residueField y)`-schemes; this is recorded at the level of morphisms rather than of
points, which is strictly stronger than the compatibility a consumer of the homeomorphism needs.

`range_fiberMap` is proved by transporting `AlgebraicGeometry.Scheme.Pullback.range_snd` along
`CategoryTheory.IsPullback.isoPullback`, since the range of a pullback projection is a genuine
fact about the carrier of a fibre product of schemes and not a formal consequence of the
universal property.

## References

* [Stacks Project, Tag 053R](https://stacks.math.columbia.edu/tag/053R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {X Y Z : Scheme.{u}}

/-- The morphism of scheme-theoretic fibres induced by precomposition: for `i : Z ⟶ X` and
`f : X ⟶ Y`, a morphism `(i ≫ f).fiber y ⟶ f.fiber y` over `Spec (Y.residueField y)` whose
composite with the fibre inclusion of `f` is the fibre inclusion of `i ≫ f` followed by `i`. -/
public noncomputable def Scheme.Hom.fiberMap (f : X ⟶ Y) (i : Z ⟶ X) (y : Y) :
    (i ≫ f).fiber y ⟶ f.fiber y :=
  pullback.lift ((i ≫ f).fiberι y ≫ i) ((i ≫ f).fiberToSpecResidueField y)
    (by rw [Category.assoc]; exact (i ≫ f).fiber_fac y)

/-- Following the comparison morphism by the fibre inclusion of `f` is the fibre inclusion of
`i ≫ f` followed by `i`. -/
@[reassoc (attr := simp)]
public lemma Scheme.Hom.fiberMap_fiberι (f : X ⟶ Y) (i : Z ⟶ X) (y : Y) :
    f.fiberMap i y ≫ f.fiberι y = (i ≫ f).fiberι y ≫ i :=
  pullback.lift_fst _ _ _

/-- The comparison morphism of fibres is a morphism over `Spec (Y.residueField y)`. -/
@[reassoc (attr := simp)]
public lemma Scheme.Hom.fiberMap_fiberToSpecResidueField (f : X ⟶ Y) (i : Z ⟶ X) (y : Y) :
    f.fiberMap i y ≫ f.fiberToSpecResidueField y = (i ≫ f).fiberToSpecResidueField y :=
  pullback.lift_snd _ _ _

/-- The comparison morphism of fibres is the base change of `i` along the fibre inclusion. -/
public theorem Scheme.Hom.isPullback_fiberMap (f : X ⟶ Y) (i : Z ⟶ X) (y : Y) :
    IsPullback (f.fiberMap i y) ((i ≫ f).fiberι y) (f.fiberι y) i := by
  have houter : IsPullback ((i ≫ f).fiberToSpecResidueField y) ((i ≫ f).fiberι y)
      (Y.fromSpecResidueField y) (i ≫ f) :=
    (IsPullback.of_hasPullback (i ≫ f) (Y.fromSpecResidueField y)).flip
  rw [← f.fiberMap_fiberToSpecResidueField i y] at houter
  exact IsPullback.of_right houter (f.fiberMap_fiberι i y)
    ((IsPullback.of_hasPullback f (Y.fromSpecResidueField y)).flip)

/-- The comparison morphism of fibres induced by a preimmersion is a preimmersion. -/
public instance Scheme.Hom.isPreimmersion_fiberMap (f : X ⟶ Y) (i : Z ⟶ X) [IsPreimmersion i]
    (y : Y) : IsPreimmersion (f.fiberMap i y) :=
  MorphismProperty.of_isPullback (f.isPullback_fiberMap i y).flip inferInstance

/-- The comparison morphism of fibres induced by a closed immersion is a closed immersion. -/
public instance Scheme.Hom.isClosedImmersion_fiberMap (f : X ⟶ Y) (i : Z ⟶ X)
    [IsClosedImmersion i] (y : Y) : IsClosedImmersion (f.fiberMap i y) :=
  MorphismProperty.of_isPullback (f.isPullback_fiberMap i y).flip inferInstance

/-- The comparison morphism of fibres induced by an open immersion is an open immersion. -/
public instance Scheme.Hom.isOpenImmersion_fiberMap (f : X ⟶ Y) (i : Z ⟶ X) [IsOpenImmersion i]
    (y : Y) : IsOpenImmersion (f.fiberMap i y) :=
  MorphismProperty.of_isPullback (f.isPullback_fiberMap i y).flip inferInstance

/-- Pointwise form of `AlgebraicGeometry.Scheme.Hom.fiberMap_fiberι`. -/
@[simp]
public lemma Scheme.Hom.fiberι_fiberMap (f : X ⟶ Y) (i : Z ⟶ X) (y : Y)
    (z : (i ≫ f).fiber y) : f.fiberι y (f.fiberMap i y z) = i ((i ≫ f).fiberι y z) := by
  rw [← Scheme.Hom.comp_apply, f.fiberMap_fiberι i y, Scheme.Hom.comp_apply]

/-- The image of the fibre of `i ≫ f` inside the fibre of `f` is the part of the latter that
lies over the image of `i`. -/
public theorem Scheme.Hom.range_fiberMap (f : X ⟶ Y) (i : Z ⟶ X) (y : Y) :
    Set.range (f.fiberMap i y) = f.fiberι y ⁻¹' Set.range i := by
  obtain ⟨e, he⟩ : ∃ e : (i ≫ f).fiber y ≅ pullback i (f.fiberι y),
      e.hom ≫ pullback.snd i (f.fiberι y) = f.fiberMap i y :=
    ⟨(f.isPullback_fiberMap i y).flip.isoPullback,
      (f.isPullback_fiberMap i y).flip.isoPullback_hom_snd⟩
  have hsurj : Function.Surjective ⇑e.hom := (Scheme.homeoOfIso e).surjective
  have hcoe : ∀ z, f.fiberMap i y z = pullback.snd i (f.fiberι y) (e.hom z) := by
    intro z
    rw [← he, Scheme.Hom.comp_apply]
  rw [← Scheme.Pullback.range_snd]
  ext
  simp only [Set.mem_range, hcoe, hsurj.exists]

/-- For `i` a preimmersion, the fibre of `i ≫ f` over `y` is homeomorphic to the part of the
fibre of `f` over `y` lying over the image of `i`. -/
public noncomputable def Scheme.Hom.fiberMapHomeo (f : X ⟶ Y) (i : Z ⟶ X) [IsPreimmersion i]
    (y : Y) : (i ≫ f).fiber y ≃ₜ f.fiberι y ⁻¹' Set.range i :=
  .trans (f.fiberMap i y).isEmbedding.toHomeomorph (.setCongr (f.range_fiberMap i y))

/-- The point underlying `fiberMapHomeo` at `z` is the image of `z` under `fiberMap`. -/
@[simp]
public lemma Scheme.Hom.fiberMapHomeo_apply (f : X ⟶ Y) (i : Z ⟶ X) [IsPreimmersion i] (y : Y)
    (z : (i ≫ f).fiber y) : (f.fiberMapHomeo i y z).1 = f.fiberMap i y z := rfl

/-- Emptiness of the fibre of a composite, in pointwise form. -/
public theorem Scheme.Hom.isEmpty_fiber_comp_iff (f : X ⟶ Y) (i : Z ⟶ X) (y : Y) :
    IsEmpty ((i ≫ f).fiber y) ↔ ∀ z : Z, f (i z) ≠ y := by
  constructor
  · intro h z hz
    have hmem : z ∈ Set.range ((i ≫ f).fiberι y) := by
      rw [(i ≫ f).range_fiberι y]
      simpa [Scheme.Hom.comp_apply] using hz
    exact h.elim hmem.choose
  · intro h
    refine ⟨fun w => h ((i ≫ f).fiberι y w) ?_⟩
    simpa [Scheme.Hom.comp_apply] using ((i ≫ f).range_fiberι y).le ⟨w, rfl⟩

namespace Scheme.IdealSheafData

variable (I : X.IdealSheafData)

/-- The fibre over `y` of the closed subscheme cut out by `I` is homeomorphic to the part of the
fibre of `f` over `y` that lies in the support of `I`. -/
public noncomputable def fiberHomeo (f : X ⟶ Y) (y : Y) :
    (I.subschemeι ≫ f).fiber y ≃ₜ f.fiberι y ⁻¹' (I.support : Set X) :=
  (f.fiberMapHomeo I.subschemeι y).trans (.setCongr (by rw [I.range_subschemeι]))

/-- The point underlying `fiberHomeo` at `z` is the image of `z` under the comparison morphism
of fibres. -/
@[simp]
public lemma fiberHomeo_apply (f : X ⟶ Y) (y : Y) (z : (I.subschemeι ≫ f).fiber y) :
    (I.fiberHomeo f y z).1 = f.fiberMap I.subschemeι y z := rfl

/-- The image of the fibre of the closed subscheme is the part of the fibre of `f` lying in the
support of `I`. -/
public theorem range_fiberMap_subschemeι (f : X ⟶ Y) (y : Y) :
    Set.range (f.fiberMap I.subschemeι y) = f.fiberι y ⁻¹' (I.support : Set X) := by
  rw [f.range_fiberMap I.subschemeι y, I.range_subschemeι]

/-- A closed subscheme misses the fibre over `y` exactly when no point of its support lies
over `y`. -/
public theorem isEmpty_fiber_comp_iff (f : X ⟶ Y) (y : Y) :
    IsEmpty ((I.subschemeι ≫ f).fiber y) ↔ ∀ x ∈ (I.support : Set X), f x ≠ y := by
  rw [Scheme.Hom.isEmpty_fiber_comp_iff]
  constructor
  · intro h x hx
    obtain ⟨z, rfl⟩ := (I.range_subschemeι ▸ hx : x ∈ Set.range I.subschemeι)
    exact h z
  · exact fun h z => h _ (I.range_subschemeι ▸ Set.mem_range_self z)

end Scheme.IdealSheafData

end AlgebraicGeometry

end
