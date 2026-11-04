module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!
# The fibre of a morphism restricted over an open of the base

Let `f : X ⟶ S` be a morphism of schemes, let `U ⊆ S` be open and let `y ∈ U`. The restriction
`f ∣_ U : f⁻¹U ⟶ U` (`AlgebraicGeometry.morphismRestrict`) has a scheme-theoretic fibre at the
point `y' = ⟨y, hy⟩` of `U`, and that fibre **is** the fibre of `f` at `y`: nothing of `X` over
`y` is lost by passing to `f⁻¹U`, because `y` already lies in `U`.

This file records that identification together with the two compatibilities that make it usable,
namely with the embeddings of the two fibres into `X` and with the two structure morphisms to the
spectrum of the residue field. It is the transport the proof of [Stacks, Tag 0D2N] needs in order
to move the hypothesis "`ℒ` is ample on `X_y`", and a morphism `X_y ⟶ ℙⁿ_{κ(y)}`, between `f` and
its restriction over a neighbourhood of `y`; the route described in
`AmpleFibreNeighbourhood/FibreImmersion.lean` uses it as one of its two transports.

## Main definitions

* `Stacks.AmpleFibreNeighbourhood.fiberMorphismRestrictHom`: the comparison morphism
  `(f ∣_ U).fiber y' ⟶ f.fiber y`, as the map of pullbacks induced by `(f ⁻¹ᵁ U).ι`, `U.ι` and
  the residue-field identification.
* `Stacks.AmpleFibreNeighbourhood.fiberMorphismRestrictIso`: **the isomorphism of schemes
  `(f ∣_ U).fiber y' ≅ f.fiber y`**, that comparison morphism promoted to an isomorphism.

## Main results

* `Stacks.AmpleFibreNeighbourhood.isPullback_fiberMorphismRestrictHom`: the comparison morphism
  sits in a **cartesian** square over the two morphisms to the spectra of the residue fields and
  `Spec.map` of the canonical residue-field map of `U.ι` at `y'`. This is the statement every
  other result here is read off.
* `Stacks.AmpleFibreNeighbourhood.isIso_specMap_residueFieldMap_ι`: **`Spec` of the canonical
  residue-field map of `U.ι` at `y'` is an isomorphism of schemes.** This is the identification
  `κ(y) ≅ κ(y')` the square below is read through.
* `Stacks.AmpleFibreNeighbourhood.isIso_fiberMorphismRestrictHom`: the comparison morphism is an
  isomorphism.
* `Stacks.AmpleFibreNeighbourhood.fiberMorphismRestrictIso_hom_comp_fiberι` and
  `Stacks.AmpleFibreNeighbourhood.fiberMorphismRestrictIso_inv_comp_fiberι`: **compatibility with
  the embeddings into `X`.** The isomorphism, followed by `f.fiberι y`, is the embedding of the
  fibre of `f ∣_ U` into `f ⁻¹ᵁ U` followed by the inclusion of `f ⁻¹ᵁ U` in `X`.
* `Stacks.AmpleFibreNeighbourhood.fiberMorphismRestrictIso_hom_comp_fiberToSpecResidueField` and
  `Stacks.AmpleFibreNeighbourhood.fiberMorphismRestrictIso_inv_comp_fiberToSpecResidueField`:
  **compatibility with the structure morphisms to the residue field.** The square
  `(f ∣_ U).fiberToSpecResidueField y' ≫ Spec.map (U.ι.residueFieldMap y')
    = e.hom ≫ f.fiberToSpecResidueField y`
  commutes, where `U.ι.residueFieldMap y' : κ(y) ⟶ κ(y')` is an isomorphism because `U.ι` is an
  open immersion (`AlgebraicGeometry.Scheme.instIsIsoCommRingCatResidueFieldMapOfIsOpenImmersion`),
  so this transports a morphism of the fibre over `Spec κ(y)` to one over `Spec κ(y')` and back.

## The route

Both fibres are pullbacks by definition (`AlgebraicGeometry.Scheme.Hom.fiber` is
`pullback f (S.fromSpecResidueField y)`), and the whole content is one instance of a Mathlib
lemma. `AlgebraicGeometry.isPullback_morphismRestrict` says that

```
f⁻¹U --f ∣_ U--> U
  |              |
 ι              U.ι
  v              v
  X ----f------> S
```

is cartesian, and `AlgebraicGeometry.isPullback_fiberToSpecResidueField_of_isPullback`, applied to
the flip of that square and to the point `y'` of `U`, says that the induced map of fibres

```
(f ∣_ U).fiber y' --------> f.fiber y
      |                        |
 fiberToSpecResidueField   fiberToSpecResidueField
      v                        v
  Spec κ(y') --Spec.map--> Spec κ(y)
```

is cartesian too. The map along the top is `CategoryTheory.Limits.pullback.map` for the three
morphisms `(f ⁻¹ᵁ U).ι`, `Spec.map (U.ι.residueFieldMap y')` and `U.ι`; its two commutativity
hypotheses are the square above and
`AlgebraicGeometry.Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField`, so it is written out
here rather than left implicit, and the compatibility with the embeddings into `X` is then
`CategoryTheory.Limits.pullback.lift_fst` and nothing more. The bottom map is an isomorphism, `U.ι`
being an open immersion, so the top one is as well by
`CategoryTheory.IsPullback.isIso_fst_of_isIso` — a pullback of an isomorphism is an isomorphism.
The identification `U.ι y' = y` of points is definitional, which is why no transport along an
equality of points appears anywhere below.

## No `@[stacks]` attribute is attached, and why

Nothing here is a numbered result of the Stacks project. It is the compatibility of Mathlib's
`AlgebraicGeometry.Scheme.Hom.fiber` with `AlgebraicGeometry.morphismRestrict`, a bookkeeping step
that the source of [Stacks, Tag 0D2N] performs silently when it replaces `f` by its restriction
over a neighbourhood of `y`. Tag 0D2N itself is proved and registered as
`Stacks.AmpleFibreNeighbourhood.exists_mem_isRelativelyAmple_of_isAmple_fibre`
(`AmpleFibreNeighbourhood/RelativelyAmpleNeighbourhood.lean`), so no tag is claimed for any
declaration in this file.

## References

* [Stacks Project, Tag 0D2N](https://stacks.math.columbia.edu/tag/0D2N)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.AmpleFibreNeighbourhood

variable {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Opens) (y : S) (hy : y ∈ U)

/-! ### The comparison morphism and its cartesian square -/

/-- **The residue field of `U.toScheme` at `y' = ⟨y, hy⟩` is canonically the residue field of `S`
at `y`, and the two spectra are canonically isomorphic.** The open immersion `U.ι` is an
isomorphism on stalks, hence on residue fields, by
`AlgebraicGeometry.Scheme.instIsIsoCommRingCatResidueFieldMapOfIsOpenImmersion`; that instance has
to be applied by hand, as at
`StacksFrontier/AlgebraicGeometry/Descent/Germ/TranscendenceDegree.lean:111`, because instance
resolution does not find it on its own. That `Spec.map` of an isomorphism of rings is an
isomorphism of schemes is not an instance either, so `Spec.map` of the inverse is exhibited as the
inverse, exactly as at
`StacksFrontier/RingTheory/Seminormalization/SeminormalizationInitial.lean:2399`.

This is what makes the cartesian square
`Stacks.AmpleFibreNeighbourhood.isPullback_fiberMorphismRestrictHom` an identification of fibres
rather than merely a base change, and it is what lets a consumer invert the `Spec.map` appearing
in `Stacks.AmpleFibreNeighbourhood.fiberMorphismRestrictIso_hom_comp_fiberToSpecResidueField`. -/
instance isIso_specMap_residueFieldMap_ι :
    IsIso (Spec.map (U.ι.residueFieldMap (⟨y, hy⟩ : U.toScheme))) :=
  haveI : IsIso (U.ι.residueFieldMap (⟨y, hy⟩ : U.toScheme)) :=
    Scheme.instIsIsoCommRingCatResidueFieldMapOfIsOpenImmersion U.ι (⟨y, hy⟩ : U.toScheme)
  ⟨Spec.map (inv (U.ι.residueFieldMap (⟨y, hy⟩ : U.toScheme))),
    by rw [← Spec.map_comp, IsIso.inv_hom_id, Spec.map_id],
    by rw [← Spec.map_comp, IsIso.hom_inv_id, Spec.map_id]⟩

/-- **The comparison morphism from the fibre of `f ∣_ U` at `y' = ⟨y, hy⟩` to the fibre of `f` at
`y`.** Both are pullbacks — `AlgebraicGeometry.Scheme.Hom.fiber` is by definition
`CategoryTheory.Limits.pullback f (S.fromSpecResidueField y)` — and this is the induced map of
pullbacks for the inclusion `(f ⁻¹ᵁ U).ι` of the source, the morphism
`Spec.map (U.ι.residueFieldMap ⟨y, hy⟩)` of the two spectra of residue fields, and the inclusion
`U.ι` of the base.

Its two commutativity hypotheses are the cartesian square
`AlgebraicGeometry.isPullback_morphismRestrict` of the restriction, and
`AlgebraicGeometry.Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField` at the open immersion
`U.ι`.

It is an isomorphism (`Stacks.AmpleFibreNeighbourhood.isIso_fiberMorphismRestrictHom`); the
packaged isomorphism is `Stacks.AmpleFibreNeighbourhood.fiberMorphismRestrictIso`. -/
def fiberMorphismRestrictHom : (f ∣_ U).fiber (⟨y, hy⟩ : U.toScheme) ⟶ f.fiber y :=
  pullback.map (f ∣_ U) (U.toScheme.fromSpecResidueField (⟨y, hy⟩ : U.toScheme)) f
    (S.fromSpecResidueField y) (f ⁻¹ᵁ U).ι
    (Spec.map (U.ι.residueFieldMap (⟨y, hy⟩ : U.toScheme))) U.ι
    (isPullback_morphismRestrict f U).w
    (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField U.ι (⟨y, hy⟩ : U.toScheme)).symm

/-- **The comparison morphism of fibres sits in a cartesian square over the two spectra of residue
fields.** This is `AlgebraicGeometry.isPullback_fiberToSpecResidueField_of_isPullback` applied to
the flip of `AlgebraicGeometry.isPullback_morphismRestrict` and to the point `⟨y, hy⟩` of `U`: the
fibre of `f ∣_ U` at `⟨y, hy⟩` is the fibre of `f` at `y`, base changed along
`Spec.map (U.ι.residueFieldMap ⟨y, hy⟩)`.

Everything else in this file is read off this one statement: its `CategoryTheory.IsPullback.w` is
the compatibility with the structure morphisms to the residue field, and
`CategoryTheory.IsPullback.isIso_fst_of_isIso` turns it into an isomorphism because the bottom
morphism is one. -/
theorem isPullback_fiberMorphismRestrictHom :
    IsPullback (fiberMorphismRestrictHom f U y hy)
      ((f ∣_ U).fiberToSpecResidueField (⟨y, hy⟩ : U.toScheme)) (f.fiberToSpecResidueField y)
      (Spec.map (U.ι.residueFieldMap (⟨y, hy⟩ : U.toScheme))) :=
  isPullback_fiberToSpecResidueField_of_isPullback (isPullback_morphismRestrict f U).flip
    (⟨y, hy⟩ : U.toScheme)

/-- **The comparison morphism of fibres is an isomorphism.** In the cartesian square
`Stacks.AmpleFibreNeighbourhood.isPullback_fiberMorphismRestrictHom` the comparison morphism is
the base change of `Spec.map (U.ι.residueFieldMap ⟨y, hy⟩)`, which is an isomorphism because
`U.ι` is an open immersion, hence an isomorphism on stalks and so on residue fields
(`AlgebraicGeometry.Scheme.instIsIsoCommRingCatResidueFieldMapOfIsOpenImmersion`). A pullback of
an isomorphism is an isomorphism, by `CategoryTheory.IsPullback.isIso_fst_of_isIso`. That the
bottom morphism is an isomorphism is
`Stacks.AmpleFibreNeighbourhood.isIso_specMap_residueFieldMap_ι`, and it is handed to the
`autoParam` of that lemma explicitly: instance resolution does not find it there. -/
instance isIso_fiberMorphismRestrictHom : IsIso (fiberMorphismRestrictHom f U y hy) :=
  (isPullback_fiberMorphismRestrictHom f U y hy).isIso_fst_of_isIso
    (isIso_specMap_residueFieldMap_ι U y hy)

/-! ### The isomorphism of fibres and its two compatibilities -/

/-- **The scheme-theoretic fibre of `f ∣_ U` at `y' = ⟨y, hy⟩` is the fibre of `f` at `y`.** The
isomorphism is the comparison morphism
`Stacks.AmpleFibreNeighbourhood.fiberMorphismRestrictHom`, which
`Stacks.AmpleFibreNeighbourhood.isIso_fiberMorphismRestrictHom` shows to be an isomorphism.

Its compatibility with the embeddings of the two fibres into `X` is
`Stacks.AmpleFibreNeighbourhood.fiberMorphismRestrictIso_hom_comp_fiberι`, and its compatibility
with the two structure morphisms to the spectrum of the residue field is
`Stacks.AmpleFibreNeighbourhood.fiberMorphismRestrictIso_hom_comp_fiberToSpecResidueField`. -/
def fiberMorphismRestrictIso : (f ∣_ U).fiber (⟨y, hy⟩ : U.toScheme) ≅ f.fiber y :=
  asIso (fiberMorphismRestrictHom f U y hy)

/-- The forward direction of `Stacks.AmpleFibreNeighbourhood.fiberMorphismRestrictIso` is the
comparison morphism `Stacks.AmpleFibreNeighbourhood.fiberMorphismRestrictHom` it was built from,
so the cartesian square `Stacks.AmpleFibreNeighbourhood.isPullback_fiberMorphismRestrictHom` is a
square about the isomorphism. -/
@[simp]
theorem fiberMorphismRestrictIso_hom :
    (fiberMorphismRestrictIso f U y hy).hom = fiberMorphismRestrictHom f U y hy :=
  rfl

/-- **Compatibility of the identification of fibres with the embeddings into `X`.** The
isomorphism `Stacks.AmpleFibreNeighbourhood.fiberMorphismRestrictIso`, followed by the embedding
`f.fiberι y` of the fibre of `f` into `X`, is the embedding of the fibre of `f ∣_ U` into
`f ⁻¹ᵁ U` followed by the inclusion of `f ⁻¹ᵁ U` into `X`.

Both embeddings are the first projection of a pullback, and the comparison morphism is a map of
pullbacks, so this is `CategoryTheory.Limits.pullback.lift_fst`. -/
theorem fiberMorphismRestrictIso_hom_comp_fiberι :
    (fiberMorphismRestrictIso f U y hy).hom ≫ f.fiberι y =
      (f ∣_ U).fiberι (⟨y, hy⟩ : U.toScheme) ≫ (f ⁻¹ᵁ U).ι :=
  pullback.lift_fst _ _ _

/-- The inverse form of
`Stacks.AmpleFibreNeighbourhood.fiberMorphismRestrictIso_hom_comp_fiberι`: the embedding of the
fibre of `f` into `X` factors through the fibre of `f ∣_ U`. -/
theorem fiberMorphismRestrictIso_inv_comp_fiberι :
    (fiberMorphismRestrictIso f U y hy).inv ≫
        (f ∣_ U).fiberι (⟨y, hy⟩ : U.toScheme) ≫ (f ⁻¹ᵁ U).ι =
      f.fiberι y :=
  (Iso.inv_comp_eq _).2 (fiberMorphismRestrictIso_hom_comp_fiberι f U y hy).symm

/-- **Compatibility of the identification of fibres with the structure morphisms to the residue
field.** The residue field of `U.toScheme` at `y' = ⟨y, hy⟩` is canonically the residue field of
`S` at `y`: the open immersion `U.ι` is an isomorphism on stalks, so
`U.ι.residueFieldMap y' : κ(y) ⟶ κ(y')` is an isomorphism, by
`AlgebraicGeometry.Scheme.instIsIsoCommRingCatResidueFieldMapOfIsOpenImmersion`. Under that
identification the two structure morphisms correspond: the square

```
(f ∣_ U).fiber y' ----e.hom----> f.fiber y
      |                             |
 fiberToSpecResidueField       fiberToSpecResidueField
      v                             v
  Spec κ(y') ---Spec.map κ---> Spec κ(y)
```

commutes. This is the commutativity half of
`Stacks.AmpleFibreNeighbourhood.isPullback_fiberMorphismRestrictHom`, and it is what carries a
morphism of `X_y` over `Spec κ(y)` — a morphism to `ℙⁿ_{κ(y)}`, say — to one of the fibre of
`f ∣_ U` over `Spec κ(y')`. -/
theorem fiberMorphismRestrictIso_hom_comp_fiberToSpecResidueField :
    (f ∣_ U).fiberToSpecResidueField (⟨y, hy⟩ : U.toScheme) ≫
        Spec.map (U.ι.residueFieldMap (⟨y, hy⟩ : U.toScheme)) =
      (fiberMorphismRestrictIso f U y hy).hom ≫ f.fiberToSpecResidueField y :=
  (isPullback_fiberMorphismRestrictHom f U y hy).w.symm

/-- The inverse form of
`Stacks.AmpleFibreNeighbourhood.fiberMorphismRestrictIso_hom_comp_fiberToSpecResidueField`: the
structure morphism of the fibre of `f` to `Spec κ(y)` is the structure morphism of the fibre of
`f ∣_ U` to `Spec κ(y')`, read through the identification of the two fibres and of the two
residue fields. -/
theorem fiberMorphismRestrictIso_inv_comp_fiberToSpecResidueField :
    (fiberMorphismRestrictIso f U y hy).inv ≫
        (f ∣_ U).fiberToSpecResidueField (⟨y, hy⟩ : U.toScheme) ≫
          Spec.map (U.ι.residueFieldMap (⟨y, hy⟩ : U.toScheme)) =
      f.fiberToSpecResidueField y :=
  (Iso.inv_comp_eq _).2 (fiberMorphismRestrictIso_hom_comp_fiberToSpecResidueField f U y hy)

end Stacks.AmpleFibreNeighbourhood

end
