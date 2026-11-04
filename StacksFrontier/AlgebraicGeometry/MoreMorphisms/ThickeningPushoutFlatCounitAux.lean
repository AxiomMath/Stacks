module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.Stability
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutEtale
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutGluing
public import StacksFrontier.AlgebraicGeometry.Pushout.FlatSectionsDescent
public import StacksFrontier.RingTheory.MilnorPatching.Algebras

/-!
# Machinery for the counit of the gluing adjunction at a flat scheme

Let `i : X ⟶ X'` be a thickening of schemes, let `f : X ⟶ Y` be an affine morphism and let
`Y' = Y ⨿_X X'` be the pushout of [Stacks Project, Tag 07RT].  Gluing is left adjoint to base
change by [Stacks Project, Tag 07RV], and the unit of that adjunction is an isomorphism
(`Stacks.Pushout.gluingAdjunction_unit_app_isIso`).  [Stacks Project, Tag 07RX] adds that the
*counit* is an isomorphism at a scheme `W'` over `Y'` which is flat over `Y'`.

This file collects everything that goes into that statement except the flat characterisation of
the glued scheme and the final assembly: the affineness and thickening facts about the two
inclusions into the pushout, and the identification of the counit after base change.  The
ring-theoretic heart and its affine-local form for schemes are
`MilnorPatching.isIso_of_isIso_baseChange_of_isPullback` and
`AlgebraicGeometry.isIso_sectionsPushoutMap_of_isIso_pullback`, in
`StacksFrontier.AlgebraicGeometry.Pushout.FlatSectionsDescent`.

## Main results

* `Stacks.Pushout.baseChange_counit_isIso` and its four component forms: the counit of the gluing
  adjunction becomes an isomorphism after base change to the two pieces of the pushout.
* `Stacks.Pushout.gluingCounit_isAffine`: the counit is an affine morphism.
* `Stacks.Pushout.pushout_inl_isAffineHom`, `Stacks.Pushout.gluingYComponent_isThickening`: the
  two structural facts about the pushout square that the argument needs.

## Implementation notes

Four features of the proof are worth recording.

*No transparency overrides are used.*  The defeq-sensitive steps are done in term mode or through `change`,
which check at `default` transparency, and every morphism that has to be matched against a
local `IsIso` hypothesis or a universal property is named at the type at which it is used, so
that the match succeeds at `instances` transparency.

*Nothing is assumed beyond the hypotheses of the source.*  [Stacks Project, Tag 06AD] — a
thickening of an affine scheme is affine — is proved in this development,
`Stacks.Thickenings.isAffine_of_isThickening`, and the statements of Tag 07RT reached from here
take it as an explicit hypothesis which every call below discharges with
`Stacks.Thickenings.forall_isAffine_of_isThickening`.  Nor is the existence of `Y' = Y ⨿_X X'`
assumed: it is the first assertion of Tag 07RT, obtained from `hi` and the affineness of `f` by
`Stacks.Pushout.hasPushout_of_isThickening`, and the statements below bind that instance inside
their own types,

```
(hi : IsThickening i) [IsAffineHom f] :
  letI := hasPushout_of_isThickening i f hi
  <statement mentioning `pushout i f`>
```

so that `pushout i f` is writable while only `hi` and the affineness of `f` are hypotheses.

*Three steps use existing results.*  `Stacks.Pushout.pushout_inl_isAffineHom` goes
through `Stacks.Pushout.isAffineHom_of_isThickening_comp` rather than a hand-rolled cover
argument; `Stacks.Pushout.gluingSourceMap_isAffineHom` is base change of an affine morphism along
`Stacks.Pushout.gluingSourceMap_isPullback`; and `Stacks.Pushout.gluingYComponent_isThickening`
reads off `Stacks.Pushout.gluing_inr_isThickening`.

*The correspondence of affine opens across a thickening is not needed.*  It would be used only to
produce, from an affine open of the thickened scheme, an affine open of the ambient scheme with
the same preimage.  That is `Stacks.Pushout.affineOpen_of_thickening_preimage`, which follows
directly from Tag 06AD applied to the restriction `i ∣_ U`.

## References

* [Stacks Project, Tag 06AD](https://stacks.math.columbia.edu/tag/06AD)
* [Stacks Project, Tag 07RT](https://stacks.math.columbia.edu/tag/07RT)
* [Stacks Project, Tag 07RV](https://stacks.math.columbia.edu/tag/07RV)
* [Stacks Project, Tag 07RX](https://stacks.math.columbia.edu/tag/07RX)
* [Stacks Project, Tag 08KQ](https://stacks.math.columbia.edu/tag/08KQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Pushout

open Stacks.Thickenings

-- The two universal properties this file computes with, and the structure projection of an
-- object of a `MorphismProperty.Under` category.  `CategoryTheory.Limits.pushout.inl_desc` and
-- `CategoryTheory.Limits.pushout.inr_desc` are not global `simp` lemmas, and without them `simp`
-- stops one step short of every pushout computation below; the alternative is to reach them via
-- `colimit.ι_desc` under `backward.isDefEq.respectTransparency false`, which is avoided here.
attribute [local simp] pushout.inl_desc pushout.inr_desc
  MorphismProperty.Under.mk_hom

/-! ### Opens, affineness and thickenings in the pushout square -/

/-- The map on sections of a morphism of schemes only depends on the morphism. -/
theorem schemeAppLE_eq_of_hom_eq {X Y : Scheme.{u}} (f g : X ⟶ Y)
    (h : f = g) (U : Y.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U) :
    f.appLE U V e = g.appLE U V (by simpa [h] using e) := by
  cases h
  rfl

/-- A surjective morphism of schemes reflects equality of opens of its target. -/
theorem opens_eq_of_preimage_eq {X X' : Scheme.{u}} (i : X ⟶ X')
    (hi : Function.Surjective i) {U V : X'.Opens} (h : i ⁻¹ᵁ U = i ⁻¹ᵁ V) :
    U = V := by
  ext y
  obtain ⟨x, rfl⟩ := hi y
  simpa using SetLike.ext_iff.mp h x

/-- **[Stacks Project, Tag 06AD] for an open.**  An open of the target of a thickening is affine
as soon as its preimage is. -/
theorem affineOpen_of_thickening_preimage {A B : Scheme.{u}} (j : A ⟶ B)
    (hj : IsThickening j) (U : B.Opens)
    (hU : IsAffineOpen (j ⁻¹ᵁ U)) : IsAffineOpen U := by
  let : IsAffine (j ⁻¹ᵁ U).toScheme := hU
  exact isAffine_of_isThickening (i := j ∣_ U)
    (isThickening_of_isPullback (isPullback_morphismRestrict j U) hj)

/-- If a morphism becomes, after a thickening of its source, an isomorphism onto a closed
immersion, then it pulls affine opens back to affine opens. -/
theorem affine_preimage_of_iso_after_thickening
    {S S₀ T T₀ : Scheme.{u}} (j : S₀ ⟶ S) (k : T₀ ⟶ T) (c : S ⟶ T)
    (hj : IsThickening j) (e : S₀ ≅ T₀)
    (hcomm : j ≫ c = e.hom ≫ k) {U : T.Opens} (hU : IsAffineOpen U)
    [IsClosedImmersion k] : IsAffineOpen (c ⁻¹ᵁ U) := by
  have hpre : IsAffineOpen (j ⁻¹ᵁ (c ⁻¹ᵁ U)) := by
    rw [← Scheme.Hom.comp_preimage, hcomm, Scheme.Hom.comp_preimage]
    have hk : IsAffineHom k := (isClosedImmersion_iff_isAffineHom.mp ‹IsClosedImmersion k›).1
    exact (hU.preimage k).preimage e.hom
  exact affineOpen_of_thickening_preimage j hj (c ⁻¹ᵁ U) hpre

/-- The inclusion of the thickened piece into the pushout of a thickening and an affine morphism
is an affine morphism. -/
theorem pushout_inl_isAffineHom {X X' Y : Scheme.{u}}
    (i : X ⟶ X') (f : X ⟶ Y) (hi : IsThickening i) [IsAffineHom f] :
    letI := hasPushout_of_isThickening i f hi
    IsAffineHom (pushout.inl i f) := by
  let := hasPushout_of_isThickening i f hi
  let : IsClosedImmersion (pushout.inr i f) :=
    (pushout_inr_isThickening forall_isAffine_of_isThickening i f hi).1
  have : IsAffineHom (i ≫ pushout.inl i f) := by
    rw [pushout.condition]
    infer_instance
  exact isAffineHom_of_isThickening_comp forall_isAffine_of_isThickening i _ hi

/-- The map from the common restriction of a compatible pair to its `Y`-component is affine. -/
theorem gluingSourceMap_isAffineHom {X X' Y : Scheme.{u}}
    (i : X ⟶ X') (f : X ⟶ Y) [IsAffineHom f]
    (T : gluingData i f) :
    IsAffineHom (gluingSourceMap i f T) :=
  MorphismProperty.of_isPullback (gluingSourceMap_isPullback i f T).flip inferInstance

/-- The `Y`-component of a compatible pair maps into the glued scheme by a thickening, compatibly
with the structure morphisms. -/
theorem gluingYComponent_isThickening {X X' Y : Scheme.{u}}
    (i : X ⟶ X') (f : X ⟶ Y)
    (hi : IsThickening i) [IsAffineHom f]
    (T : gluingData i f) :
    letI := hasPushout_of_isThickening i f hi
    ∃ v : T.obj.left.left ⟶ ((gluingFunctor i f hi).obj T).left,
      IsThickening v ∧
        v ≫ ((gluingFunctor i f hi).obj T).hom =
          T.obj.left.hom ≫ pushout.inr i f := by
  let := hasPushout_of_isThickening i f hi
  let : HasPushout (pullback.fst T.obj.right.hom i) (gluingSourceMap i f T) :=
    gluingHasPushout i f hi T
  refine ⟨pushout.inr (pullback.fst T.obj.right.hom i) (gluingSourceMap i f T),
    gluing_inr_isThickening i f hi T, ?_⟩
  show _ ≫ (gluingPushoutData i f T).hom = _
  exact gluingPushoutData_inr i f T

/-! ### The counit of an adjunction at an object isomorphic to an image -/

/-- If the unit of an adjunction is invertible at `A`, then the counit is invertible at every
object isomorphic to the image of `A`. -/
theorem counit_isIso_of_iso_to_image {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) (A : C) (B : D)
    (e : F.obj A ≅ B) (hη : IsIso (adj.unit.app A)) : IsIso (adj.counit.app B) := by
  have : IsIso (adj.counit.app (F.obj A)) :=
    isIso_of_hom_comp_eq_id (F.map (adj.unit.app A)) (adj.left_triangle_components A)
  have : IsIso ((G ⋙ F).map e.hom ≫ adj.counit.app B) := by
    rw [adj.counit.naturality e.hom]
    infer_instance
  exact IsIso.of_isIso_comp_left ((G ⋙ F).map e.hom) _

/-! ### The counit after base change -/

/-- The counit of the gluing adjunction becomes an isomorphism after base change to the two
pieces of the pushout. -/
theorem baseChange_counit_isIso {X X' Y : Scheme.{u}}
    (i : X ⟶ X') (f : X ⟶ Y) (hi : IsThickening i) [IsAffineHom f] :
    letI := hasPushout_of_isThickening i f hi
    ∀ W' : Over (pushout i f), IsIso ((baseChangeFunctor i f hi).map
      ((gluingAdjunction i f hi).counit.app W')) := by
  let := hasPushout_of_isThickening i f hi
  intro W'
  have := gluingAdjunction_unit_app_isIso i f hi ((baseChangeFunctor i f hi).obj W')
  exact isIso_of_hom_comp_eq_id ((gluingAdjunction i f hi).unit.app _)
    ((gluingAdjunction i f hi).right_triangle_components W')

/-- The `Y`-component of the base change of the counit of the gluing adjunction is an
isomorphism. -/
theorem baseChange_counit_left_isIso {X X' Y : Scheme.{u}}
    (i : X ⟶ X') (f : X ⟶ Y) (hi : IsThickening i) [IsAffineHom f] :
    letI := hasPushout_of_isThickening i f hi
    ∀ W' : Over (pushout i f),
      IsIso ((Comma.fst (Over.pullback f) (Over.pullback i)).map
        ((show ObjectProperty (Comma (Over.pullback f) (Over.pullback i)) from
          fun T ↦ IsIso T.hom).ι.map
          ((baseChangeFunctor i f hi).map
            ((gluingAdjunction i f hi).counit.app W')))) := by
  let := hasPushout_of_isThickening i f hi
  intro W'
  have := baseChange_counit_isIso i f hi W'
  infer_instance

/-- The `X'`-component of the base change of the counit of the gluing adjunction is an
isomorphism. -/
theorem baseChange_counit_right_isIso {X X' Y : Scheme.{u}}
    (i : X ⟶ X') (f : X ⟶ Y) (hi : IsThickening i) [IsAffineHom f] :
    letI := hasPushout_of_isThickening i f hi
    ∀ W' : Over (pushout i f),
      IsIso ((Comma.snd (Over.pullback f) (Over.pullback i)).map
        ((show ObjectProperty (Comma (Over.pullback f) (Over.pullback i)) from
          fun T ↦ IsIso T.hom).ι.map
          ((baseChangeFunctor i f hi).map
            ((gluingAdjunction i f hi).counit.app W')))) := by
  let := hasPushout_of_isThickening i f hi
  intro W'
  have := baseChange_counit_isIso i f hi W'
  infer_instance

/-- Base change of the counit of the gluing adjunction along `X' ⟶ Y'` is an isomorphism of
schemes. -/
theorem baseChange_counit_inl_scheme_isIso {X X' Y : Scheme.{u}}
    (i : X ⟶ X') (f : X ⟶ Y) (hi : IsThickening i) [IsAffineHom f] :
    letI := hasPushout_of_isThickening i f hi
    ∀ W' : Over (pushout i f),
      IsIso (((Over.pullback (pushout.inl i f)).map
        ((gluingAdjunction i f hi).counit.app W')).left) := by
  let := hasPushout_of_isThickening i f hi
  intro W'
  have h' : IsIso ((Over.forget X').map
      ((Comma.snd (Over.pullback f) (Over.pullback i)).map
        ((show ObjectProperty (Comma (Over.pullback f) (Over.pullback i)) from
          fun T ↦ IsIso T.hom).ι.map
          ((baseChangeFunctor i f hi).map
            ((gluingAdjunction i f hi).counit.app W'))))) := by
    let := baseChange_counit_right_isIso i f hi W'
    exact Functor.map_isIso (Over.forget X') _
  exact h'

/-- Base change of the counit of the gluing adjunction along `Y ⟶ Y'` is an isomorphism of
schemes. -/
theorem baseChange_counit_inr_scheme_isIso {X X' Y : Scheme.{u}}
    (i : X ⟶ X') (f : X ⟶ Y) (hi : IsThickening i) [IsAffineHom f] :
    letI := hasPushout_of_isThickening i f hi
    ∀ W' : Over (pushout i f),
      IsIso (((Over.pullback (pushout.inr i f)).map
        ((gluingAdjunction i f hi).counit.app W')).left) := by
  let := hasPushout_of_isThickening i f hi
  intro W'
  have h' : IsIso ((Over.forget Y).map
      ((Comma.fst (Over.pullback f) (Over.pullback i)).map
        ((show ObjectProperty (Comma (Over.pullback f) (Over.pullback i)) from
          fun T ↦ IsIso T.hom).ι.map
          ((baseChangeFunctor i f hi).map
            ((gluingAdjunction i f hi).counit.app W'))))) := by
    let := baseChange_counit_left_isIso i f hi W'
    exact Functor.map_isIso (Over.forget Y) _
  exact h'

/-- The counit of the gluing adjunction is an affine morphism. -/
theorem gluingCounit_isAffine {X X' Y : Scheme.{u}}
    (i : X ⟶ X') (f : X ⟶ Y) (hi : IsThickening i) [IsAffineHom f] :
    letI := hasPushout_of_isThickening i f hi
    ∀ W' : Over (pushout i f),
      IsAffineHom ((gluingAdjunction i f hi).counit.app W').left := by
  let := hasPushout_of_isThickening i f hi
  intro W'
  let G := (gluingFunctor i f hi).obj ((baseChangeFunctor i f hi).obj W')
  let c := (gluingAdjunction i f hi).counit.app W'
  let a := pushout.inr i f
  have ha : IsThickening a := pushout_inr_isThickening forall_isAffine_of_isThickening i f hi
  let j := pullback.fst G.hom a
  let k := pullback.fst W'.hom a
  have hj : IsThickening j :=
    isThickening_of_isPullback (IsPullback.of_hasPullback G.hom a) ha
  let : IsClosedImmersion k := by
    let : IsClosedImmersion a := ha.1
    infer_instance
  have hIso : IsIso ((Over.pullback a).map c).left :=
    baseChange_counit_inr_scheme_isIso i f hi W'
  let e : pullback G.hom a ≅ pullback W'.hom a := asIso ((Over.pullback a).map c).left
  have hcomm : j ≫ c.left = e.hom ≫ k :=
    (pullback.lift_fst _ _ _ :
      ((Over.pullback a).map c).left ≫ pullback.fst W'.hom a = _).symm
  rw [isAffineHom_iff]
  intro U hU
  exact affine_preimage_of_iso_after_thickening j k c.left hj e hcomm hU

end Stacks.Pushout

end
