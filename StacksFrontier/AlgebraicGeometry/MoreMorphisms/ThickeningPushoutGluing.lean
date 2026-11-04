module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import StacksFrontier.AlgebraicGeometry.GlueingNearClosedPoints.Basic
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushout07RT
public import StacksFrontier.AlgebraicGeometry.Pushout.QuasiFiniteFunctoriality
public import StacksFrontier.AlgebraicGeometry.Thickenings.Affine
public import StacksFrontier.AlgebraicGeometry.Thickenings.BaseChange
public import StacksFrontier.RingTheory.MilnorPatching.Adjunction
public import StacksFrontier.RingTheory.MilnorPatching.Algebras

/-!
# Gluing schemes across a pushout along a thickening

Let `i : X ⟶ X'` be a thickening of schemes, let `f : X ⟶ Y` be an affine morphism and let
`Y' = Y ⨿_X X'` be the pushout of [Stacks Project, Tag 07RT].  Base change along `Y ⟶ Y'` and
`X' ⟶ Y'` sends a scheme `V'` over `Y'` to the triple `(V' ×_{Y'} Y, V' ×_{Y'} X', 1)`, an object
of the fibre product of the categories of schemes over `Y` and over `X'` above the category of
schemes over `X`.  [Stacks Project, Tag 07RV] says that this functor has a left adjoint, which
sends a triple `(V, U', φ)` to the pushout `V ⨿_{V ×_Y X} U'`, and that the composition of the
left adjoint with base change is isomorphic to the identity.

## Main definitions

* `Stacks.Pushout.gluingData` is the fibre product of the category of schemes over `Y` and the
  category of schemes over `X'` above the category of schemes over `X`, modelled as the
  iso-comma category of the two base-change functors.
* `Stacks.Pushout.baseChangeFunctor` is the functor `F` of Tag 07RV, base change to `Y` and to
  `X'` together with the canonical comparison of the two restrictions to `X`.
* `Stacks.Pushout.gluingFunctor` is the functor `G` of Tag 07RV, the objectwise pushout
  `V ⨿_{V ×_Y X} U'` with its structure morphism to `Y'`.

## Main results

* `Stacks.Pushout.gluingFunctor_obj_isPushout`: the glued scheme really is the pushout of the two
  components of a triple along their identified restrictions to `X`.
* `Stacks.Pushout.gluingHomEquiv`: the hom-set bijection, morphisms out of the glued scheme
  against morphisms of triples into a base change.
* `Stacks.Pushout.gluingAdjunction`: gluing is left adjoint to base change.
* `Stacks.Pushout.gluing_inr_isThickening`: the map from the `Y`-component of a triple into the
  glued scheme is a thickening, being the cobase change of the thickening `U ⟶ U'`.
* `Stacks.Pushout.gluing_components_isPullback`: the two squares of Tag 07RV are cartesian, so the
  two components of a triple are recovered from the glued scheme by base change.
* `Stacks.Pushout.gluingAdjunction_unit_app_isIso` and
  `Stacks.Pushout.gluingAdjunction_unit_isIso`: the unit of that adjunction is invertible.
* `Stacks.Pushout.gluingCompBaseChangeIsoId` is the last assertion of Tag 07RV: the composition
  `F ∘ G` of gluing with base change is isomorphic to the identity functor.

## Implementation notes

The fibre product of categories is `AlgebraicGeometry.IsoComma`, the full subcategory of the
comma category of the two base-change functors on the objects whose comparison morphism is
invertible, so a triple carries its isomorphism `φ` as data and a morphism of triples satisfies
the compatibility square automatically.  The comparison used to build `F` is not chosen: it is
the base-change associativity isomorphism of `CategoryTheory.Over.pullbackComp`, transported
along the equality `i ≫ (X' ⟶ Y') = f ≫ (Y ⟶ Y')`.

The adjunction is built from the hom-set bijection, as in the source: a morphism out of the
pushout is a pair of morphisms agreeing on `V ×_Y X`, and a morphism into a fibre product is a
morphism together with a factorization of its structure map.  The unit is computed componentwise
and each component is identified with a comparison map into a fibre product.

Many of the lemmas below write the structure morphism of a base change `(Over.pullback g).obj Z`
out as the projection `pullback.snd Z.hom g` of a fibre product, and name the morphisms that
occur with their types written out.  That is not cosmetic: the objects `(Over.pullback g).obj Z`
and `pullback Z.hom g` are equal by definition but not as terms, so a rewrite whose left-hand
side mentions the former does not fire on a goal that mentions the latter.

**The last assertion.**  That the unit `(V, U', φ) ⟶ F(G(V, U', φ))` is an isomorphism is the
assertion that both squares

```
V  ⟶ V ⨿_U U'      U' ⟶ V ⨿_U U'
↓        ↓          ↓        ↓
Y  ⟶    Y'          X' ⟶    Y'
```

are cartesian, which is `Stacks.Pushout.gluing_components_isPullback`.  Being cartesian is local
on `Y'`, and over an affine open `S` of `Y'` and an affine open `T` of `V'` above it every corner
of both squares becomes affine, because `Y ⟶ Y'` and `V ⟶ V'` are thickenings and `X' ⟶ Y'` and
`U' ⟶ V'` are affine (that last point is
`Stacks.Pushout.isAffineHom_of_thickening_comp`, and it is where Tag 06AD enters a second time).
The two cocartesian squares have cartesian squares of *sections* by the fourth assertion of
Tag 07RT, `Stacks.Pushout.pushout_structureSheaf_isPullback`, so on those charts the assertion is
a statement about two ring fibre products — it is Milnor patching,
`MilnorPatching.pullback_baseChange`.  The passage between a cartesian square of affine schemes
and a cocartesian square of their global sections is
`AlgebraicGeometry.isPushout_appTop_of_isPullback` in one direction and
`Stacks.Pushout.isPullback_of_isPushout_appTop` in the other.

**Nothing is assumed.**  [Stacks Project, Tag 06AD] — *a thickening of an affine scheme is
affine* — enters through Tag 07RT, which needs it to produce the pushouts `V ⨿_U U'`, and it is
taken from the library, where it is proved unconditionally as
`Stacks.Thickenings.forall_isAffine_of_isThickening`.  The lemmas of Tag 07RT reached from here
still take it as an explicit universally quantified hypothesis, and every call below discharges
that hypothesis with that theorem; no statement in this file carries it.

The existence of `Y' = Y ⨿_X X'` is not assumed either.  It is the first assertion of Tag 07RT,
`Stacks.Pushout.hasPushout_of_isThickening_of_isAffineHom`, and it is obtained here from `i`
being a thickening and `f` being affine by `Stacks.Pushout.hasPushout_of_isThickening`.  Because
`Y'` is written as Mathlib's canonical pushout `CategoryTheory.Limits.pushout i f`, whose very
notation needs a `HasPushout i f` instance, the statements of Tag 07RV bind that instance inside
their own types,

```
(hi : IsThickening i) [IsAffineHom f] :
  letI := hasPushout_of_isThickening i f hi
  <statement mentioning `pushout i f`>
```

so that `pushout i f` is writable while nothing beyond `hi` and the affineness of `f` — the
hypotheses of the source — is assumed.  The auxiliary lemmas that are not themselves part of the
statement of Tag 07RV still take `[HasPushout i f]` as an instance argument, which costs
nothing: every application of them below supplies that instance from `hi`.

## References

* [Stacks Project, Tag 06AD](https://stacks.math.columbia.edu/tag/06AD)
* [Stacks Project, Tag 07RT](https://stacks.math.columbia.edu/tag/07RT)
* [Stacks Project, Tag 07RU](https://stacks.math.columbia.edu/tag/07RU)
* [Stacks Project, Tag 07RV](https://stacks.math.columbia.edu/tag/07RV)
* [Stacks Project, Tag 08KQ](https://stacks.math.columbia.edu/tag/08KQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Pushout

open Stacks.Thickenings

/-- Compatible schemes over the two pieces of a pushout. -/
abbrev gluingData {X X' Y : Scheme.{u}} (i : X ⟶ X') (f : X ⟶ Y) :=
  IsoComma (Over.pullback f) (Over.pullback i)

/-- **The pushout `Y' = Y ⨿_X X'` exists**, for a thickening `i : X ⟶ X'` and an affine morphism
`f : X ⟶ Y`.  This is the first assertion of [Stacks Project, Tag 07RT],
`Stacks.Pushout.hasPushout_of_isThickening_of_isAffineHom`, with its [Stacks Project, Tag 06AD]
hypothesis discharged by `Stacks.Thickenings.forall_isAffine_of_isThickening`.  It is what lets
the statements of [Stacks Project, Tag 07RV] write `pushout i f` without assuming that it
exists. -/
theorem hasPushout_of_isThickening {X X' Y : Scheme.{u}} (i : X ⟶ X') (f : X ⟶ Y)
    (hi : IsThickening i) [IsAffineHom f] : HasPushout i f :=
  hasPushout_of_isThickening_of_isAffineHom forall_isAffine_of_isThickening i f hi

/-- The canonical comparison between the two ways of restricting a scheme
 over the pushout to `X`. -/
noncomputable def baseChangeComparison {X X' Y : Scheme.{u}}
    (i : X ⟶ X') (f : X ⟶ Y) [HasPushout i f] :
    Over.pullback (pushout.inr i f) ⋙ Over.pullback f ≅
      Over.pullback (pushout.inl i f) ⋙ Over.pullback i :=
  (Over.pullbackComp f (pushout.inr i f)).symm ≪≫
    eqToIso (congrArg (fun h : X ⟶ pushout i f ↦ Over.pullback h)
      (pushout.condition (f := i) (g := f)).symm) ≪≫
      Over.pullbackComp i (pushout.inl i f)

/-- Base change from schemes over the pushout to compatible schemes over
its two constituent pieces. -/
@[stacks 07RV "the base-change functor F"]
noncomputable def baseChangeFunctor {X X' Y : Scheme.{u}}
    (i : X ⟶ X') (f : X ⟶ Y) (hi : IsThickening i) [IsAffineHom f] :
    letI := hasPushout_of_isThickening i f hi
    Over (pushout i f) ⥤ gluingData i f :=
  letI := hasPushout_of_isThickening i f hi
  (show ObjectProperty (Comma (Over.pullback f) (Over.pullback i)) from
      fun T ↦ IsIso T.hom).lift
    { obj := fun Z ↦
        ⟨(Over.pullback (pushout.inr i f)).obj Z,
          (Over.pullback (pushout.inl i f)).obj Z,
          (baseChangeComparison i f).hom.app Z⟩
      map := fun g ↦
        ⟨(Over.pullback (pushout.inr i f)).map g,
          (Over.pullback (pushout.inl i f)).map g,
          (baseChangeComparison i f).hom.naturality g⟩
      map_id := by intro Z; ext <;> simp
      map_comp := by intro Z W Q g h; ext <;> simp }
    (fun Z ↦ inferInstance)

/-- The map from the common restriction of a compatible pair to its
`Y`-component, using the comparison isomorphism. -/
noncomputable def gluingSourceMap {X X' Y : Scheme.{u}}
    (i : X ⟶ X') (f : X ⟶ Y) (T : gluingData i f) :
    pullback T.obj.right.hom i ⟶ T.obj.left.left := by
  letI : IsIso T.obj.hom := T.property
  exact (inv T.obj.hom).left ≫ pullback.fst T.obj.left.hom f

/-- The common restriction `U` of a compatible pair is the fibre product `X ×_Y V`: the square
with sides `U ⟶ V`, `U ⟶ X`, `V ⟶ Y` and `X ⟶ Y` is cartesian. -/
theorem gluingSourceMap_isPullback {X X' Y : Scheme.{u}}
    (i : X ⟶ X') (f : X ⟶ Y) (T : gluingData i f) :
    IsPullback (gluingSourceMap i f T) (pullback.snd T.obj.right.hom i)
      T.obj.left.hom f := by
  have : IsIso T.obj.hom := T.property
  let e := (Over.forget X).mapIso (asIso T.obj.hom).symm
  have hs : e.hom ≫ pullback.snd T.obj.left.hom f =
      pullback.snd T.obj.right.hom i := (inv T.obj.hom).w
  apply IsPullback.of_iso_pullback _ e rfl hs
  constructor
  change (e.hom ≫ pullback.fst T.obj.left.hom f) ≫ T.obj.left.hom = _
  rw [Category.assoc, pullback.condition, ← Category.assoc, hs]

/-- The projection from the common restriction `U` of a compatible pair to `U'` is a
thickening. -/
private theorem isThickening_pullback_fst {X X' Y : Scheme.{u}}
    (i : X ⟶ X') (f : X ⟶ Y) (hi : IsThickening i) (T : gluingData i f) :
    IsThickening (pullback.fst T.obj.right.hom i) :=
  isThickening_of_isPullback (IsPullback.of_hasPullback T.obj.right.hom i) hi

/-- The map from the common restriction `U` of a compatible pair to `V` is affine. -/
private theorem isAffineHom_gluingSourceMap {X X' Y : Scheme.{u}}
    (i : X ⟶ X') (f : X ⟶ Y) [IsAffineHom f] (T : gluingData i f) :
    IsAffineHom (gluingSourceMap i f T) :=
  MorphismProperty.of_isPullback (gluingSourceMap_isPullback i f T).flip inferInstance

/-- The pushout `V ⨿_U U'` of a compatible pair exists: `U ⟶ U'` is a thickening and `U ⟶ V` is
affine, so Tag 07RT applies to them. -/
theorem gluingHasPushout {X X' Y : Scheme.{u}}
    (i : X ⟶ X') (f : X ⟶ Y)
    (hi : IsThickening i) [IsAffineHom f] [HasPushout i f]
    (T : gluingData i f) :
    HasPushout (pullback.fst T.obj.right.hom i) (gluingSourceMap i f T) := by
  have := isAffineHom_gluingSourceMap i f T
  exact hasPushout_of_isThickening_of_isAffineHom forall_isAffine_of_isThickening
    (pullback.fst T.obj.right.hom i) (gluingSourceMap i f T) (isThickening_pullback_fst i f hi T)

/-- The scheme glued from a compatible pair `(V, U', φ)`: the pushout of `V ⨿_U U'`, where
`U = V ×_Y X` is identified with `U' ×_{X'} X` by `φ`, with the structure morphism to `Y'`
induced by `V ⟶ Y` and `U' ⟶ X'`. -/
noncomputable abbrev gluingPushoutData {X X' Y : Scheme.{u}}
    (i : X ⟶ X') (f : X ⟶ Y)
    [IsAffineHom f] [HasPushout i f]
    (T : gluingData i f)
    [HasPushout (pullback.fst T.obj.right.hom i) (gluingSourceMap i f T)] :
    Over (pushout i f) := by
  letI : IsIso T.obj.hom := T.property
  have hcommon :
      pullback.fst T.obj.right.hom i ≫ T.obj.right.hom ≫ pushout.inl i f =
        gluingSourceMap i f T ≫ T.obj.left.hom ≫ pushout.inr i f := by
    have hcmp := (inv T.obj.hom).w
    have hcmp' :
        (inv T.obj.hom).left ≫ pullback.snd T.obj.left.hom f =
          pullback.snd T.obj.right.hom i := by
      simpa only [Over.pullback_obj_hom] using hcmp
    dsimp [gluingSourceMap]
    calc
      pullback.fst T.obj.right.hom i ≫ T.obj.right.hom ≫ pushout.inl i f =
          (pullback.snd T.obj.right.hom i ≫ i) ≫ pushout.inl i f := by
            rw [← pullback.condition]
            simp [Category.assoc]
      _ = pullback.snd T.obj.right.hom i ≫ (i ≫ pushout.inl i f) := by
          simp [Category.assoc]
      _ = pullback.snd T.obj.right.hom i ≫ (f ≫ pushout.inr i f) := by
          rw [pushout.condition (f := i) (g := f)]
      _ = (pullback.snd T.obj.right.hom i ≫ f) ≫ pushout.inr i f := by
          simp [Category.assoc]
      _ = ((inv T.obj.hom).left ≫ pullback.snd T.obj.left.hom f) ≫
            f ≫ pushout.inr i f := by
          rw [← hcmp']
          simp [Category.assoc]
      _ = (inv T.obj.hom).left ≫
            (pullback.snd T.obj.left.hom f ≫ f) ≫ pushout.inr i f := by
          simp [Category.assoc]
      _ = (inv T.obj.hom).left ≫
            (pullback.fst T.obj.left.hom f ≫ T.obj.left.hom) ≫ pushout.inr i f := by
          rw [← pullback.condition]
      _ = (inv T.obj.hom).left ≫ pullback.fst T.obj.left.hom f ≫
            T.obj.left.hom ≫ pushout.inr i f := by
          simp [Category.assoc]
  let q := pushout.desc (T.obj.right.hom ≫ pushout.inl i f)
    (T.obj.left.hom ≫ pushout.inr i f) hcommon
  exact Over.mk q

/-- On `U'` the structure morphism of the glued scheme is the given morphism `U' ⟶ X'` followed
by `X' ⟶ Y'`. -/
theorem gluingPushoutData_inl {X X' Y : Scheme.{u}}
    (i : X ⟶ X') (f : X ⟶ Y)
    [IsAffineHom f] [HasPushout i f]
    (T : gluingData i f)
    [HasPushout (pullback.fst T.obj.right.hom i) (gluingSourceMap i f T)] :
    pushout.inl (pullback.fst T.obj.right.hom i) (gluingSourceMap i f T) ≫
        (gluingPushoutData i f T).hom = T.obj.right.hom ≫ pushout.inl i f := by
  dsimp [gluingPushoutData]
  simp [pushout.inl_desc]

/-- On `V` the structure morphism of the glued scheme is the given morphism `V ⟶ Y` followed by
`Y ⟶ Y'`. -/
theorem gluingPushoutData_inr {X X' Y : Scheme.{u}}
    (i : X ⟶ X') (f : X ⟶ Y)
    [IsAffineHom f] [HasPushout i f]
    (T : gluingData i f)
    [HasPushout (pullback.fst T.obj.right.hom i) (gluingSourceMap i f T)] :
    pushout.inr (pullback.fst T.obj.right.hom i) (gluingSourceMap i f T) ≫
        (gluingPushoutData i f T).hom = T.obj.left.hom ≫ pushout.inr i f := by
  dsimp [gluingPushoutData]
  simp [pushout.inr_desc]

/-- The morphism of glued schemes induced by a morphism of compatible pairs, by the universal
property of the pushout. -/
noncomputable def gluingPushoutMap {X X' Y : Scheme.{u}}
    (i : X ⟶ X') (f : X ⟶ Y)
    [IsAffineHom f] [HasPushout i f]
    {T S : gluingData i f}
    [HasPushout (pullback.fst T.obj.right.hom i) (gluingSourceMap i f T)]
    [HasPushout (pullback.fst S.obj.right.hom i) (gluingSourceMap i f S)]
    (g : T ⟶ S) :
    gluingPushoutData i f T ⟶ gluingPushoutData i f S := by
  letI : IsIso T.obj.hom := T.property
  letI : IsIso S.obj.hom := S.property
  let k := ((Over.pullback i).map g.hom.right).left
  let l := ((Over.pullback f).map g.hom.left).left
  have hk₁ : k ≫ pullback.fst S.obj.right.hom i =
      pullback.fst T.obj.right.hom i ≫ g.hom.right.left := by
    change pullback.lift (pullback.fst T.obj.right.hom i ≫ g.hom.right.left)
      (pullback.snd T.obj.right.hom i) _ ≫ pullback.fst S.obj.right.hom i = _
    rw [pullback.lift_fst]
  have hl₁ : pullback.fst T.obj.left.hom f ≫ g.hom.left.left =
      l ≫ pullback.fst S.obj.left.hom f := by
    change _ = pullback.lift (pullback.fst T.obj.left.hom f ≫ g.hom.left.left)
      (pullback.snd T.obj.left.hom f) _ ≫ pullback.fst S.obj.left.hom f
    rw [pullback.lift_fst]
  have hwraw :
      (Over.pullback f).map g.hom.left ≫ S.obj.hom =
        T.obj.hom ≫ (Over.pullback i).map g.hom.right := g.hom.w
  have hw : l ≫ S.obj.hom.left = T.obj.hom.left ≫ k := by
    change ((Over.pullback f).map g.hom.left).left ≫ S.obj.hom.left =
      T.obj.hom.left ≫ ((Over.pullback i).map g.hom.right).left
    exact congrArg (fun m => m.left) hwraw
  have hSinv : S.obj.hom.left ≫ (inv S.obj.hom).left = 𝟙 _ :=
    congrArg Over.Hom.left (IsIso.hom_inv_id S.obj.hom)
  have htransport :
      (inv T.obj.hom).left ≫ l = k ≫ (inv S.obj.hom).left := by
    calc
      (inv T.obj.hom).left ≫ l =
          ((inv T.obj.hom).left ≫ l ≫ S.obj.hom.left) ≫
            (inv S.obj.hom).left := by
              simp [Category.assoc, hSinv]
      _ = ((inv T.obj.hom).left ≫ T.obj.hom.left ≫ k) ≫
            (inv S.obj.hom).left := by rw [hw]
      _ = k ≫ (inv S.obj.hom).left := by
        have hTinv : (inv T.obj.hom).left ≫ T.obj.hom.left = 𝟙 _ :=
          congrArg Over.Hom.left (IsIso.inv_hom_id T.obj.hom)
        calc
          ((inv T.obj.hom).left ≫ T.obj.hom.left) ≫ k ≫
              (inv S.obj.hom).left = (𝟙 _ ≫ k) ≫
                (inv S.obj.hom).left := by simp [hTinv]
          _ = k ≫ (inv S.obj.hom).left := by simp
  have hsource : k ≫ gluingSourceMap i f S =
      gluingSourceMap i f T ≫ g.hom.left.left := by
    dsimp [gluingSourceMap]
    calc
      k ≫ (inv S.obj.hom).left ≫ pullback.fst S.obj.left.hom f =
          (inv T.obj.hom).left ≫ l ≫ pullback.fst S.obj.left.hom f := by
            simpa [Category.assoc] using
              (congrArg (fun m => m ≫ pullback.fst S.obj.left.hom f) htransport).symm
      _ = (inv T.obj.hom).left ≫ pullback.fst T.obj.left.hom f ≫
            g.hom.left.left := by rw [hl₁]
  have hcommon :
      pullback.fst T.obj.right.hom i ≫ g.hom.right.left ≫
          pushout.inl (pullback.fst S.obj.right.hom i) (gluingSourceMap i f S) =
        gluingSourceMap i f T ≫ g.hom.left.left ≫
          pushout.inr (pullback.fst S.obj.right.hom i) (gluingSourceMap i f S) := by
    calc
      (pullback.fst T.obj.right.hom i ≫ g.hom.right.left) ≫
          pushout.inl (pullback.fst S.obj.right.hom i) (gluingSourceMap i f S) =
        (k ≫ pullback.fst S.obj.right.hom i) ≫
          pushout.inl (pullback.fst S.obj.right.hom i) (gluingSourceMap i f S) := by
            rw [← hk₁]
      _ = k ≫ (pullback.fst S.obj.right.hom i ≫
          pushout.inl (pullback.fst S.obj.right.hom i) (gluingSourceMap i f S)) := by
            simp [Category.assoc]
      _ = k ≫ (gluingSourceMap i f S ≫
          pushout.inr (pullback.fst S.obj.right.hom i) (gluingSourceMap i f S)) := by
            rw [pushout.condition]
      _ = (gluingSourceMap i f T ≫ g.hom.left.left) ≫
          pushout.inr (pullback.fst S.obj.right.hom i) (gluingSourceMap i f S) := by
            simpa [Category.assoc] using
              congrArg (fun m => m ≫ pushout.inr (pullback.fst S.obj.right.hom i)
                (gluingSourceMap i f S)) hsource
  have hcommon' : pullback.fst T.obj.right.hom i ≫
      (g.hom.right.left ≫ pushout.inl (pullback.fst S.obj.right.hom i)
        (gluingSourceMap i f S)) = gluingSourceMap i f T ≫
      (g.hom.left.left ≫ pushout.inr (pullback.fst S.obj.right.hom i)
        (gluingSourceMap i f S)) := by
    simpa [Category.assoc] using hcommon
  let q := pushout.desc
    (g.hom.right.left ≫ pushout.inl (pullback.fst S.obj.right.hom i) (gluingSourceMap i f S))
    (g.hom.left.left ≫ pushout.inr (pullback.fst S.obj.right.hom i) (gluingSourceMap i f S))
    hcommon'
  refine Over.homMk q ?_
  apply pushout.hom_ext
  · change
      (pushout.inl (pullback.fst T.obj.right.hom i) (gluingSourceMap i f T) ≫ q) ≫
          (gluingPushoutData i f S).hom =
        pushout.inl (pullback.fst T.obj.right.hom i) (gluingSourceMap i f T) ≫
          (gluingPushoutData i f T).hom
    calc
      (pushout.inl (pullback.fst T.obj.right.hom i) (gluingSourceMap i f T) ≫ q) ≫
          (gluingPushoutData i f S).hom =
        (g.hom.right.left ≫
          pushout.inl (pullback.fst S.obj.right.hom i) (gluingSourceMap i f S)) ≫
          (gluingPushoutData i f S).hom := by
            dsimp [q]
            rw [pushout.inl_desc]
      _ = g.hom.right.left ≫
          (pushout.inl (pullback.fst S.obj.right.hom i) (gluingSourceMap i f S) ≫
            (gluingPushoutData i f S).hom) := by
              exact Category.assoc _ _ _
      _ = g.hom.right.left ≫ (S.obj.right.hom ≫ pushout.inl i f) := by
            rw [gluingPushoutData_inl]
      _ = T.obj.right.hom ≫ pushout.inl i f := by
            exact congrArg (fun m => m ≫ pushout.inl i f) g.hom.right.w
      _ = pushout.inl (pullback.fst T.obj.right.hom i) (gluingSourceMap i f T) ≫
          (gluingPushoutData i f T).hom := by
              exact (gluingPushoutData_inl i f T).symm
  · change
      (pushout.inr (pullback.fst T.obj.right.hom i) (gluingSourceMap i f T) ≫ q) ≫
          (gluingPushoutData i f S).hom =
        pushout.inr (pullback.fst T.obj.right.hom i) (gluingSourceMap i f T) ≫
          (gluingPushoutData i f T).hom
    calc
      (pushout.inr (pullback.fst T.obj.right.hom i) (gluingSourceMap i f T) ≫ q) ≫
          (gluingPushoutData i f S).hom =
        (g.hom.left.left ≫
          pushout.inr (pullback.fst S.obj.right.hom i) (gluingSourceMap i f S)) ≫
          (gluingPushoutData i f S).hom := by
            dsimp [q]
            rw [pushout.inr_desc]
      _ = g.hom.left.left ≫
          (pushout.inr (pullback.fst S.obj.right.hom i) (gluingSourceMap i f S) ≫
            (gluingPushoutData i f S).hom) := by
              exact Category.assoc _ _ _
      _ = g.hom.left.left ≫ (S.obj.left.hom ≫ pushout.inr i f) := by
            rw [gluingPushoutData_inr]
      _ = T.obj.left.hom ≫ pushout.inr i f := by
            exact congrArg (fun m => m ≫ pushout.inr i f) g.hom.left.w
      _ = pushout.inr (pullback.fst T.obj.right.hom i) (gluingSourceMap i f T) ≫
          (gluingPushoutData i f T).hom := by
              exact (gluingPushoutData_inr i f T).symm

/-- On `U'` the glued morphism is the `U'`-component of the morphism of compatible pairs. -/
@[reassoc] theorem gluingPushoutMap_inl {X X' Y : Scheme.{u}}
    (i : X ⟶ X') (f : X ⟶ Y)
    [IsAffineHom f] [HasPushout i f]
    {T S : gluingData i f}
    [HasPushout (pullback.fst T.obj.right.hom i) (gluingSourceMap i f T)]
    [HasPushout (pullback.fst S.obj.right.hom i) (gluingSourceMap i f S)]
    (g : T ⟶ S) :
    pushout.inl (pullback.fst T.obj.right.hom i) (gluingSourceMap i f T) ≫
        (gluingPushoutMap i f g).left =
      g.hom.right.left ≫
        pushout.inl (pullback.fst S.obj.right.hom i) (gluingSourceMap i f S) := by
  dsimp [gluingPushoutMap]
  change pushout.inl (pullback.fst T.obj.right.hom i) (gluingSourceMap i f T) ≫
    pushout.desc
      (g.hom.right.left ≫ pushout.inl (pullback.fst S.obj.right.hom i) (gluingSourceMap i f S))
      (g.hom.left.left ≫ pushout.inr (pullback.fst S.obj.right.hom i) (gluingSourceMap i f S)) _ = _
  rw [pushout.inl_desc]

/-- On `V` the glued morphism is the `V`-component of the morphism of compatible pairs. -/
@[reassoc] theorem gluingPushoutMap_inr {X X' Y : Scheme.{u}}
    (i : X ⟶ X') (f : X ⟶ Y)
    [IsAffineHom f] [HasPushout i f]
    {T S : gluingData i f}
    [HasPushout (pullback.fst T.obj.right.hom i) (gluingSourceMap i f T)]
    [HasPushout (pullback.fst S.obj.right.hom i) (gluingSourceMap i f S)]
    (g : T ⟶ S) :
    pushout.inr (pullback.fst T.obj.right.hom i) (gluingSourceMap i f T) ≫
        (gluingPushoutMap i f g).left =
      g.hom.left.left ≫
        pushout.inr (pullback.fst S.obj.right.hom i) (gluingSourceMap i f S) := by
  dsimp [gluingPushoutMap]
  change pushout.inr (pullback.fst T.obj.right.hom i) (gluingSourceMap i f T) ≫
    pushout.desc
      (g.hom.right.left ≫ pushout.inl (pullback.fst S.obj.right.hom i) (gluingSourceMap i f S))
      (g.hom.left.left ≫ pushout.inr (pullback.fst S.obj.right.hom i) (gluingSourceMap i f S)) _ = _
  rw [pushout.inr_desc]

/-- Gluing compatible schemes over `Y` and `X'` to a scheme over their
pushout. Its objectwise pushout property is stated below. -/
@[stacks 07RV "the left adjoint G"]
noncomputable def gluingFunctor {X X' Y : Scheme.{u}}
    (i : X ⟶ X') (f : X ⟶ Y)
    (hi : IsThickening i) [IsAffineHom f] :
    letI := hasPushout_of_isThickening i f hi
    gluingData i f ⥤ Over (pushout i f) where
  obj T := by
    letI := hasPushout_of_isThickening i f hi
    letI : HasPushout (pullback.fst T.obj.right.hom i) (gluingSourceMap i f T) := by
      exact gluingHasPushout i f hi T
    exact gluingPushoutData i f T
  map {T S} g := by
    letI := hasPushout_of_isThickening i f hi
    letI : HasPushout (pullback.fst T.obj.right.hom i) (gluingSourceMap i f T) := by
      exact gluingHasPushout i f hi T
    letI : HasPushout (pullback.fst S.obj.right.hom i) (gluingSourceMap i f S) := by
      exact gluingHasPushout i f hi S
    exact gluingPushoutMap i f g
  map_id := by
    intro T
    letI := hasPushout_of_isThickening i f hi
    have : HasPushout (pullback.fst T.obj.right.hom i) (gluingSourceMap i f T) := by
      exact gluingHasPushout i f hi T
    apply Over.OverMorphism.ext
    apply pushout.hom_ext
    · simp [gluingPushoutMap_inl]
    · simp [gluingPushoutMap_inr]
  map_comp := by
    intro T S R g h
    letI := hasPushout_of_isThickening i f hi
    have : HasPushout (pullback.fst T.obj.right.hom i) (gluingSourceMap i f T) := by
      exact gluingHasPushout i f hi T
    have : HasPushout (pullback.fst S.obj.right.hom i) (gluingSourceMap i f S) := by
      exact gluingHasPushout i f hi S
    have := gluingHasPushout i f hi R
    apply Over.OverMorphism.ext
    apply pushout.hom_ext
    · rw [gluingPushoutMap_inl i f (g ≫ h)]
      simp only [Over.comp_left]
      calc
        _ = g.hom.right.left ≫
            (h.hom.right.left ≫ pushout.inl (pullback.fst R.obj.right.hom i)
              (gluingSourceMap i f R)) := by simp [Category.assoc]
        _ = g.hom.right.left ≫
            (pushout.inl (pullback.fst S.obj.right.hom i)
              (gluingSourceMap i f S) ≫ (gluingPushoutMap i f h).left) := by
              rw [← gluingPushoutMap_inl i f h]
        _ = (g.hom.right.left ≫
            pushout.inl (pullback.fst S.obj.right.hom i)
              (gluingSourceMap i f S)) ≫ (gluingPushoutMap i f h).left := by
              simp [Category.assoc]
        _ = (pushout.inl (pullback.fst T.obj.right.hom i)
            (gluingSourceMap i f T) ≫ (gluingPushoutMap i f g).left) ≫
            (gluingPushoutMap i f h).left := by
              rw [← gluingPushoutMap_inl i f g]
    · rw [gluingPushoutMap_inr i f (g ≫ h)]
      simp only [Over.comp_left]
      calc
        _ = g.hom.left.left ≫
            (h.hom.left.left ≫ pushout.inr (pullback.fst R.obj.right.hom i)
              (gluingSourceMap i f R)) := by simp [Category.assoc]
        _ = g.hom.left.left ≫
            (pushout.inr (pullback.fst S.obj.right.hom i)
              (gluingSourceMap i f S) ≫ (gluingPushoutMap i f h).left) := by
              rw [← gluingPushoutMap_inr i f h]
        _ = (g.hom.left.left ≫
            pushout.inr (pullback.fst S.obj.right.hom i)
              (gluingSourceMap i f S)) ≫ (gluingPushoutMap i f h).left := by
              simp [Category.assoc]
        _ = (pushout.inr (pullback.fst T.obj.right.hom i)
            (gluingSourceMap i f T) ≫ (gluingPushoutMap i f g).left) ≫
            (gluingPushoutMap i f h).left := by
              rw [← gluingPushoutMap_inr i f g]

/-- The glued scheme is the pushout of its two components along their
identified restrictions to `X`, with the induced map to the ambient pushout. -/
@[stacks 07RV "the left adjoint sends a triple to the pushout V ⨿_{V ×_Y X} U'"]
theorem gluingFunctor_obj_isPushout {X X' Y : Scheme.{u}}
    (i : X ⟶ X') (f : X ⟶ Y)
    (hi : IsThickening i) [IsAffineHom f]
    (T : gluingData i f) :
    letI := hasPushout_of_isThickening i f hi
    ∃ (v : T.obj.left.left ⟶ ((gluingFunctor i f hi).obj T).left)
      (u' : T.obj.right.left ⟶ ((gluingFunctor i f hi).obj T).left),
      IsPushout (gluingSourceMap i f T) (pullback.fst T.obj.right.hom i) v u' ∧
      v ≫ ((gluingFunctor i f hi).obj T).hom =
        T.obj.left.hom ≫ pushout.inr i f ∧
      u' ≫ ((gluingFunctor i f hi).obj T).hom =
        T.obj.right.hom ≫ pushout.inl i f := by
  letI := hasPushout_of_isThickening i f hi
  have : HasPushout (pullback.fst T.obj.right.hom i) (gluingSourceMap i f T) := by
      exact gluingHasPushout i f hi T
  refine ⟨pushout.inr (pullback.fst T.obj.right.hom i) (gluingSourceMap i f T),
    pushout.inl (pullback.fst T.obj.right.hom i) (gluingSourceMap i f T), ?_⟩
  refine ⟨IsPushout.of_hasPushout _ _ |>.flip, ?_, ?_⟩
  · change _ ≫ (gluingPushoutData i f T).hom = _
    exact gluingPushoutData_inr i f T
  · change _ ≫ (gluingPushoutData i f T).hom = _
    exact gluingPushoutData_inl i f T

attribute [local simp] pullback.lift_fst pullback.lift_snd
  pushout.inl_desc pushout.inr_desc Over.homMk_left

section
universe v w
variable {C : Type w} [Category.{v} C] [HasPullbacks C]
/-- The comparison isomorphism `CategoryTheory.Over.pullbackComp` is compatible with the first
projections: its component at `T`, followed by the two projections down to `T`, is the first
projection of the fibre product along the composite. -/
theorem comp_hom_fst {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (T : Over Z) :
    ((Over.pullbackComp f g).hom.app T).left ≫
      pullback.fst (pullback.snd T.hom g) f ≫ pullback.fst T.hom g =
      pullback.fst T.hom (f ≫ g) := by
  have h := congrArg Over.Hom.left (conjugateEquiv_counit
    (Over.mapPullbackAdj (f ≫ g))
    ((Over.mapPullbackAdj f).comp (Over.mapPullbackAdj g))
    (Over.mapComp f g).inv T)
  simp only [Over.comp_left, Adjunction.comp_counit_app,
    Over.mapPullbackAdj_counit_app, Functor.comp_map, Over.map_map_left,
    Over.pullback_obj_hom, Over.pullback_obj_left, Over.mapComp_inv_app_left,
    Over.homMk_left] at h
  exact h.trans (Category.id_comp _)

/-- The inverse of `CategoryTheory.Over.pullbackComp` is compatible with the first
projections. -/
theorem comp_inv_fst {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (T : Over Z) :
    ((Over.pullbackComp f g).inv.app T).left ≫ pullback.fst T.hom (f ≫ g) =
      pullback.fst (pullback.snd T.hom g) f ≫ pullback.fst T.hom g := by
  rw [← comp_hom_fst f g T, ← Category.assoc]
  have h : ((Over.pullbackComp f g).inv.app T).left ≫
      ((Over.pullbackComp f g).hom.app T).left = 𝟙 _ :=
    congrArg Over.Hom.left ((Over.pullbackComp f g).app T).inv_hom_id
  rw [h, Category.id_comp]

/-- Transporting base change along an equality of morphisms is compatible with the first
projections. -/
theorem pullback_congr_fst {X Z : C} {f g : X ⟶ Z} (h : f = g) (T : Over Z) :
    ((eqToHom (congrArg (fun k : X ⟶ Z => Over.pullback k) h)).app T).left ≫
      pullback.fst T.hom g = pullback.fst T.hom f := by
  subst g
  simp

end

/-- The comparison isomorphism of the base-change functor is compatible with the projections to
`Z`: the two ways of restricting `Z` to `X` have the same projection to `Z`. -/
theorem baseChangeComparison_fst {X X' Y : Scheme.{u}}
    (i : X ⟶ X') (f : X ⟶ Y) [HasPushout i f] (Z : Over (pushout i f)) :
    ((baseChangeComparison i f).hom.app Z).left ≫
      pullback.fst (pullback.snd Z.hom (pushout.inl i f)) i ≫
        pullback.fst Z.hom (pushout.inl i f) =
      pullback.fst (pullback.snd Z.hom (pushout.inr i f)) f ≫
        pullback.fst Z.hom (pushout.inr i f) := by
  dsimp only [baseChangeComparison, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Over.comp_left, eqToIso.hom]
  simp only [Category.assoc, comp_hom_fst]
  rw [pullback_congr_fst (pushout.condition (f := i) (g := f)).symm Z,
    comp_inv_fst]

/-- Two morphisms into an iterated fibre product `(Z ×_D B) ×_B A` agree as soon as they agree
after projecting to `Z` and to `A`. -/
theorem iterated_pullback_hom_ext {C : Type*} [Category C] [HasPullbacks C]
    {A B D E : C} (f : A ⟶ B) (g : B ⟶ D) (Z : Over D)
    {a b : E ⟶ pullback (pullback.snd Z.hom g) f}
    (h₁ : a ≫ pullback.fst _ _ ≫ pullback.fst _ _ =
      b ≫ pullback.fst _ _ ≫ pullback.fst _ _)
    (h₂ : a ≫ pullback.snd _ _ = b ≫ pullback.snd _ _) : a = b := by
  apply ((IsPullback.of_hasPullback (pullback.snd Z.hom g) f).paste_horiz
    (IsPullback.of_hasPullback Z.hom g)).hom_ext
  · simpa only [Category.assoc] using h₁
  · exact h₂

/-- Base change along `f` of a morphism `l` into `(Over.pullback g).obj Z`, followed by the two
projections to `Z`, is `l` followed by the projection to `Z`, precomposed with `pullback.fst`. -/
private theorem map_pullback_fst_fst {C : Type*} [Category C] [HasPullbacks C]
    {X Y D : C} (f : X ⟶ Y) (g : Y ⟶ D) (Z : Over D) {A : Over Y}
    (l : A ⟶ (Over.pullback g).obj Z) :
    ((Over.pullback f).map l).left ≫ pullback.fst (pullback.snd Z.hom g) f ≫
        pullback.fst Z.hom g =
      pullback.fst A.hom f ≫ l.left ≫ pullback.fst Z.hom g :=
  (pullback.lift_fst_assoc _ _ _ _).trans (Category.assoc _ _ _)

/-- A morphism of compatible pairs from `(V, U', φ)` into the base change of a scheme `Z` over
`Y'`, built from a morphism `V ⟶ Z` and a morphism `U' ⟶ Z` over `Y ⟶ Y'` and `X' ⟶ Y'` which
agree on `U`. -/
noncomputable def compatiblePairHom {X X' Y : Scheme.{u}}
    (i : X ⟶ X') (f : X ⟶ Y)
    (hi : IsThickening i) [IsAffineHom f] [HasPushout i f]
    (T : gluingData i f) (Z : Over (pushout i f))
    (a : T.obj.left.left ⟶ Z.left) (b : T.obj.right.left ⟶ Z.left)
    (ha : a ≫ Z.hom = T.obj.left.hom ≫ pushout.inr i f)
    (hb : b ≫ Z.hom = T.obj.right.hom ≫ pushout.inl i f)
    (hab : gluingSourceMap i f T ≫ a = pullback.fst T.obj.right.hom i ≫ b) :
    T ⟶ (baseChangeFunctor i f hi).obj Z := by
  dsimp [baseChangeFunctor]
  letI : IsIso T.obj.hom := T.property
  let l : T.obj.left ⟶ (Over.pullback (pushout.inr i f)).obj Z :=
    Over.homMk (pullback.lift a T.obj.left.hom ha) (pullback.lift_snd _ _ _)
  let r : T.obj.right ⟶ (Over.pullback (pushout.inl i f)).obj Z :=
    Over.homMk (pullback.lift b T.obj.right.hom hb) (pullback.lift_snd _ _ _)
  refine ObjectProperty.homMk { left := l, right := r, w := ?_ }
  apply Over.OverMorphism.ext
  apply iterated_pullback_hom_ext i (pushout.inl i f) Z
  · dsimp only [Over.comp_left]
    change (((Over.pullback f).map l).left ≫
        ((baseChangeComparison i f).hom.app Z).left) ≫ _ = _
    simp only [Category.assoc]
    rw [baseChangeComparison_fst]
    rw [show ((Over.pullback f).map l).left ≫
          pullback.fst (pullback.snd Z.hom (pushout.inr i f)) f ≫
            pullback.fst Z.hom (pushout.inr i f) = _ from
          (pullback.lift_fst_assoc _ _ _ _).trans (Category.assoc _ _ _),
      show ((Over.pullback i).map r).left ≫
          pullback.fst (pullback.snd Z.hom (pushout.inl i f)) i ≫
            pullback.fst Z.hom (pushout.inl i f) = _ from
          (pullback.lift_fst_assoc _ _ _ _).trans (Category.assoc _ _ _)]
    have hl : l.left ≫ pullback.fst Z.hom (pushout.inr i f) = a := pullback.lift_fst _ _ _
    have hr : r.left ≫ pullback.fst Z.hom (pushout.inl i f) = b := pullback.lift_fst _ _ _
    rw [hl, hr]
    have hid : T.obj.hom.left ≫ (inv T.obj.hom).left = 𝟙 _ :=
      congrArg Over.Hom.left (IsIso.hom_inv_id T.obj.hom)
    have hgs : gluingSourceMap i f T =
        (inv T.obj.hom).left ≫ pullback.fst T.obj.left.hom f := rfl
    rw [← hab, hgs]
    simp only [Category.assoc]
    rw [← Category.assoc, hid, Category.id_comp]
  · change ((Over.pullback f).map _ ≫ ((baseChangeComparison i f).hom.app Z)).left ≫
        ((Over.pullback i).obj ((Over.pullback (pushout.inl i f)).obj Z)).hom =
        (T.obj.hom ≫ (Over.pullback i).map _).left ≫
        ((Over.pullback i).obj ((Over.pullback (pushout.inl i f)).obj Z)).hom
    exact (Over.w _).trans (Over.w _).symm

/-- The `V`-component of `Stacks.Pushout.compatiblePairHom` is the morphism into the fibre
product `Z ×_{Y'} Y` determined by the given morphism `V ⟶ Z`. -/
@[simp] theorem compatiblePairHom_hom_left_left {X X' Y : Scheme.{u}}
    (i : X ⟶ X') (f : X ⟶ Y)
    (hi : IsThickening i) [IsAffineHom f] [HasPushout i f]
    (T : gluingData i f) (Z : Over (pushout i f))
    (a : T.obj.left.left ⟶ Z.left) (b : T.obj.right.left ⟶ Z.left)
    (ha : a ≫ Z.hom = T.obj.left.hom ≫ pushout.inr i f)
    (hb : b ≫ Z.hom = T.obj.right.hom ≫ pushout.inl i f)
    (hab : gluingSourceMap i f T ≫ a = pullback.fst T.obj.right.hom i ≫ b) :
    (compatiblePairHom i f hi T Z a b ha hb hab).hom.left.left =
      pullback.lift a T.obj.left.hom ha :=
  rfl

/-- The `U'`-component of `Stacks.Pushout.compatiblePairHom` is the morphism into the fibre
product `Z ×_{Y'} X'` determined by the given morphism `U' ⟶ Z`. -/
@[simp] theorem compatiblePairHom_hom_right_left {X X' Y : Scheme.{u}}
    (i : X ⟶ X') (f : X ⟶ Y)
    (hi : IsThickening i) [IsAffineHom f] [HasPushout i f]
    (T : gluingData i f) (Z : Over (pushout i f))
    (a : T.obj.left.left ⟶ Z.left) (b : T.obj.right.left ⟶ Z.left)
    (ha : a ≫ Z.hom = T.obj.left.hom ≫ pushout.inr i f)
    (hb : b ≫ Z.hom = T.obj.right.hom ≫ pushout.inl i f)
    (hab : gluingSourceMap i f T ≫ a = pullback.fst T.obj.right.hom i ≫ b) :
    (compatiblePairHom i f hi T Z a b ha hb hab).hom.right.left =
      pullback.lift b T.obj.right.hom hb :=
  rfl

/-- The two morphisms to `Z` cut out on `V` and on `U'` by a morphism of compatible pairs into
the base change of `Z` agree on the common restriction `U`. -/
theorem compatiblePairHom_agree {X X' Y : Scheme.{u}}
    (i : X ⟶ X') (f : X ⟶ Y)
    (hi : IsThickening i) [IsAffineHom f] [HasPushout i f]
    {T : gluingData i f} {Z : Over (pushout i f)}
    (h : T ⟶ (baseChangeFunctor i f hi).obj Z) :
    gluingSourceMap i f T ≫ h.hom.left.left ≫ pullback.fst Z.hom (pushout.inr i f) =
      pullback.fst T.obj.right.hom i ≫ h.hom.right.left ≫
        pullback.fst Z.hom (pushout.inl i f) := by
  dsimp [baseChangeFunctor] at h
  have : IsIso T.obj.hom := T.property
  let w : pullback T.obj.right.hom i ⟶ pullback T.obj.left.hom f := (inv T.obj.hom).left
  have hgs : gluingSourceMap i f T = w ≫ pullback.fst T.obj.left.hom f := rfl
  have hid : w ≫ T.obj.hom.left = 𝟙 _ :=
    congrArg Over.Hom.left (IsIso.inv_hom_id T.obj.hom)
  have hid_assoc (W : Scheme.{u}) (k : pullback T.obj.right.hom i ⟶ W) :
      w ≫ T.obj.hom.left ≫ k = k := by
    rw [← Category.assoc, hid, Category.id_comp]
  have hw := congrArg (fun k => k.left ≫
    pullback.fst (pullback.snd Z.hom (pushout.inl i f)) i ≫
      pullback.fst Z.hom (pushout.inl i f)) h.hom.w
  change (((Over.pullback f).map h.hom.left).left ≫
      ((baseChangeComparison i f).hom.app Z).left) ≫ _ = _ at hw
  simp only [Over.comp_left, Category.assoc, baseChangeComparison_fst] at hw
  rw [map_pullback_fst_fst f (pushout.inr i f) Z h.hom.left,
    map_pullback_fst_fst i (pushout.inl i f) Z h.hom.right] at hw
  have hh := congrArg (fun k => w ≫ k) hw
  rw [hgs]
  simp only [hid_assoc] at hh
  exact hh

/-- A morphism into a base change `(Over.pullback f).obj Z`, followed by the projection to `Z`,
is a morphism over `f`. -/
theorem over_pullback_fst {C : Type*} [Category C] [HasPullbacks C]
    {X Y : C} (f : X ⟶ Y) {T : Over X} {Z : Over Y}
    (h : T ⟶ (Over.pullback f).obj Z) :
    (h.left ≫ pullback.fst Z.hom f) ≫ Z.hom = T.hom ≫ f := by
  rw [Category.assoc, pullback.condition, ← Category.assoc]
  exact congrArg (fun k => k ≫ f) h.w

/-- The half of the hom-set bijection of [Stacks Project, Tag 07RV] that turns a morphism out of
the glued scheme into a morphism of compatible pairs, by restricting along the two inclusions
into the pushout. -/
noncomputable def gluingToPair {X X' Y : Scheme.{u}}
    (i : X ⟶ X') (f : X ⟶ Y)
    (hi : IsThickening i) [IsAffineHom f] [HasPushout i f]
    {T : gluingData i f} {Z : Over (pushout i f)}
    (k : (gluingFunctor i f hi).obj T ⟶ Z) :
    T ⟶ (baseChangeFunctor i f hi).obj Z := by
  letI := gluingHasPushout i f hi T
  let kl : pushout (pullback.fst T.obj.right.hom i) (gluingSourceMap i f T) ⟶ Z.left := k.left
  have hkl : kl ≫ Z.hom = (gluingPushoutData i f T).hom := k.w
  refine compatiblePairHom i f hi T Z
    (pushout.inr _ _ ≫ kl) (pushout.inl _ _ ≫ kl) ?_ ?_ ?_
  · rw [Category.assoc, hkl]
    exact gluingPushoutData_inr i f T
  · rw [Category.assoc, hkl]
    exact gluingPushoutData_inl i f T
  · simp only [← Category.assoc, pushout.condition]

/-- The half of the hom-set bijection of [Stacks Project, Tag 07RV] that turns a morphism of
compatible pairs into a morphism out of the glued scheme, by the universal property of the
pushout. -/
noncomputable def gluingFromPair {X X' Y : Scheme.{u}}
    (i : X ⟶ X') (f : X ⟶ Y)
    (hi : IsThickening i) [IsAffineHom f] [HasPushout i f]
    {T : gluingData i f} {Z : Over (pushout i f)}
    (h : T ⟶ (baseChangeFunctor i f hi).obj Z) :
    (gluingFunctor i f hi).obj T ⟶ Z := by
  letI := gluingHasPushout i f hi T
  let hr : T.obj.right.left ⟶ pullback Z.hom (pushout.inl i f) := h.hom.right.left
  let hl : T.obj.left.left ⟶ pullback Z.hom (pushout.inr i f) := h.hom.left.left
  have hcompat : pullback.fst T.obj.right.hom i ≫ hr ≫ pullback.fst Z.hom (pushout.inl i f) =
      gluingSourceMap i f T ≫ hl ≫ pullback.fst Z.hom (pushout.inr i f) :=
    (compatiblePairHom_agree i f hi h).symm
  have hw : pushout.desc (hr ≫ pullback.fst Z.hom (pushout.inl i f))
        (hl ≫ pullback.fst Z.hom (pushout.inr i f)) hcompat ≫ Z.hom =
      (gluingPushoutData i f T).hom := by
    apply pushout.hom_ext
    · rw [pushout.inl_desc_assoc, gluingPushoutData_inl i f T]
      exact over_pullback_fst (pushout.inl i f) h.hom.right
    · rw [pushout.inr_desc_assoc, gluingPushoutData_inr i f T]
      exact over_pullback_fst (pushout.inr i f) h.hom.left
  exact Over.homMk _ hw

/-- The `V`-component of `Stacks.Pushout.gluingToPair`, followed by the projection to `Z`, is
the restriction of the given morphism to `V`. -/
@[simp] theorem gluingToPair_left_comp_fst {X X' Y : Scheme.{u}}
    (i : X ⟶ X') (f : X ⟶ Y)
    (hi : IsThickening i) [IsAffineHom f] [HasPushout i f]
    {T : gluingData i f} {Z : Over (pushout i f)}
    [HasPushout (pullback.fst T.obj.right.hom i) (gluingSourceMap i f T)]
    (k : (gluingFunctor i f hi).obj T ⟶ Z) :
    (gluingToPair i f hi k).hom.left.left ≫ pullback.fst Z.hom (pushout.inr i f) =
      pushout.inr (pullback.fst T.obj.right.hom i) (gluingSourceMap i f T) ≫ k.left :=
  pullback.lift_fst _ _ _

/-- The `U'`-component of `Stacks.Pushout.gluingToPair`, followed by the projection to `Z`, is
the restriction of the given morphism to `U'`. -/
@[simp] theorem gluingToPair_right_comp_fst {X X' Y : Scheme.{u}}
    (i : X ⟶ X') (f : X ⟶ Y)
    (hi : IsThickening i) [IsAffineHom f] [HasPushout i f]
    {T : gluingData i f} {Z : Over (pushout i f)}
    [HasPushout (pullback.fst T.obj.right.hom i) (gluingSourceMap i f T)]
    (k : (gluingFunctor i f hi).obj T ⟶ Z) :
    (gluingToPair i f hi k).hom.right.left ≫ pullback.fst Z.hom (pushout.inl i f) =
      pushout.inl (pullback.fst T.obj.right.hom i) (gluingSourceMap i f T) ≫ k.left :=
  pullback.lift_fst _ _ _

/-- The reassociated form of `Stacks.Pushout.gluingToPair_left_comp_fst`. -/
@[simp] theorem gluingToPair_left_comp_fst_assoc {X X' Y W : Scheme.{u}}
    (i : X ⟶ X') (f : X ⟶ Y)
    (hi : IsThickening i) [IsAffineHom f] [HasPushout i f]
    {T : gluingData i f} {Z : Over (pushout i f)}
    [HasPushout (pullback.fst T.obj.right.hom i) (gluingSourceMap i f T)]
    (k : (gluingFunctor i f hi).obj T ⟶ Z) (x : Z.left ⟶ W) :
    (gluingToPair i f hi k).hom.left.left ≫ pullback.fst Z.hom (pushout.inr i f) ≫ x =
      pushout.inr (pullback.fst T.obj.right.hom i) (gluingSourceMap i f T) ≫ k.left ≫ x :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun m => m ≫ x) (gluingToPair_left_comp_fst i f hi k)).trans
      (Category.assoc _ _ _))

/-- The reassociated form of `Stacks.Pushout.gluingToPair_right_comp_fst`. -/
@[simp] theorem gluingToPair_right_comp_fst_assoc {X X' Y W : Scheme.{u}}
    (i : X ⟶ X') (f : X ⟶ Y)
    (hi : IsThickening i) [IsAffineHom f] [HasPushout i f]
    {T : gluingData i f} {Z : Over (pushout i f)}
    [HasPushout (pullback.fst T.obj.right.hom i) (gluingSourceMap i f T)]
    (k : (gluingFunctor i f hi).obj T ⟶ Z) (x : Z.left ⟶ W) :
    (gluingToPair i f hi k).hom.right.left ≫ pullback.fst Z.hom (pushout.inl i f) ≫ x =
      pushout.inl (pullback.fst T.obj.right.hom i) (gluingSourceMap i f T) ≫ k.left ≫ x :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun m => m ≫ x) (gluingToPair_right_comp_fst i f hi k)).trans
      (Category.assoc _ _ _))

/-- On `U'` the glued morphism of `Stacks.Pushout.gluingFromPair` is the `U'`-component of the
given morphism of compatible pairs, followed by the projection to `Z`. -/
@[simp] theorem inl_comp_gluingFromPair {X X' Y : Scheme.{u}}
    (i : X ⟶ X') (f : X ⟶ Y)
    (hi : IsThickening i) [IsAffineHom f] [HasPushout i f]
    {T : gluingData i f} {Z : Over (pushout i f)}
    [HasPushout (pullback.fst T.obj.right.hom i) (gluingSourceMap i f T)]
    (h : T ⟶ (baseChangeFunctor i f hi).obj Z) :
    pushout.inl (pullback.fst T.obj.right.hom i) (gluingSourceMap i f T) ≫
        (gluingFromPair i f hi h).left =
      h.hom.right.left ≫ pullback.fst Z.hom (pushout.inl i f) :=
  pushout.inl_desc _ _ _

/-- On `V` the glued morphism of `Stacks.Pushout.gluingFromPair` is the `V`-component of the
given morphism of compatible pairs, followed by the projection to `Z`. -/
@[simp] theorem inr_comp_gluingFromPair {X X' Y : Scheme.{u}}
    (i : X ⟶ X') (f : X ⟶ Y)
    (hi : IsThickening i) [IsAffineHom f] [HasPushout i f]
    {T : gluingData i f} {Z : Over (pushout i f)}
    [HasPushout (pullback.fst T.obj.right.hom i) (gluingSourceMap i f T)]
    (h : T ⟶ (baseChangeFunctor i f hi).obj Z) :
    pushout.inr (pullback.fst T.obj.right.hom i) (gluingSourceMap i f T) ≫
        (gluingFromPair i f hi h).left =
      h.hom.left.left ≫ pullback.fst Z.hom (pushout.inr i f) :=
  pushout.inr_desc _ _ _

/-- The `V`-component of `Stacks.Pushout.gluingToPair`, followed by the projection to `Y`, is
the structure morphism of `V`. -/
@[simp] theorem gluingToPair_left_comp_snd {X X' Y : Scheme.{u}}
    (i : X ⟶ X') (f : X ⟶ Y)
    (hi : IsThickening i) [IsAffineHom f] [HasPushout i f]
    {T : gluingData i f} {Z : Over (pushout i f)}
    [HasPushout (pullback.fst T.obj.right.hom i) (gluingSourceMap i f T)]
    (k : (gluingFunctor i f hi).obj T ⟶ Z) :
    (gluingToPair i f hi k).hom.left.left ≫ pullback.snd Z.hom (pushout.inr i f) =
      T.obj.left.hom :=
  pullback.lift_snd _ _ _

/-- The `U'`-component of `Stacks.Pushout.gluingToPair`, followed by the projection to `X'`, is
the structure morphism of `U'`. -/
@[simp] theorem gluingToPair_right_comp_snd {X X' Y : Scheme.{u}}
    (i : X ⟶ X') (f : X ⟶ Y)
    (hi : IsThickening i) [IsAffineHom f] [HasPushout i f]
    {T : gluingData i f} {Z : Over (pushout i f)}
    [HasPushout (pullback.fst T.obj.right.hom i) (gluingSourceMap i f T)]
    (k : (gluingFunctor i f hi).obj T ⟶ Z) :
    (gluingToPair i f hi k).hom.right.left ≫ pullback.snd Z.hom (pushout.inl i f) =
      T.obj.right.hom :=
  pullback.lift_snd _ _ _

/-- The gluing functor acts on morphisms by `Stacks.Pushout.gluingPushoutMap`. -/
@[simp] theorem gluingFunctor_map {X X' Y : Scheme.{u}}
    (i : X ⟶ X') (f : X ⟶ Y)
    (hi : IsThickening i) [IsAffineHom f] [HasPushout i f]
    {T S : gluingData i f}
    [HasPushout (pullback.fst T.obj.right.hom i) (gluingSourceMap i f T)]
    [HasPushout (pullback.fst S.obj.right.hom i) (gluingSourceMap i f S)]
    (a : T ⟶ S) : (gluingFunctor i f hi).map a = gluingPushoutMap i f a :=
  rfl

/-- The `V`-component of the base-change functor on morphisms is base change along `Y ⟶ Y'`. -/
@[simp] theorem baseChangeFunctor_map_hom_left {X X' Y : Scheme.{u}}
    (i : X ⟶ X') (f : X ⟶ Y)
    (hi : IsThickening i) [IsAffineHom f] [HasPushout i f]
    {Z W : Over (pushout i f)} (k : Z ⟶ W) :
    ((baseChangeFunctor i f hi).map k).hom.left = (Over.pullback (pushout.inr i f)).map k :=
  rfl

/-- The `U'`-component of the base-change functor on morphisms is base change along
`X' ⟶ Y'`. -/
@[simp] theorem baseChangeFunctor_map_hom_right {X X' Y : Scheme.{u}}
    (i : X ⟶ X') (f : X ⟶ Y)
    (hi : IsThickening i) [IsAffineHom f] [HasPushout i f]
    {Z W : Over (pushout i f)} (k : Z ⟶ W) :
    ((baseChangeFunctor i f hi).map k).hom.right = (Over.pullback (pushout.inl i f)).map k :=
  rfl

/-- The hom-set bijection of [Stacks Project, Tag 07RV]: morphisms from the glued scheme
`V ⨿_U U'` to a scheme `Z` over `Y'` are the same thing as morphisms of compatible pairs from
`(V, U', φ)` to the base change of `Z`. -/
noncomputable def gluingHomEquiv {X X' Y : Scheme.{u}}
    (i : X ⟶ X') (f : X ⟶ Y)
    (hi : IsThickening i) [IsAffineHom f] [HasPushout i f]
    (T : gluingData i f) (Z : Over (pushout i f)) :
    ((gluingFunctor i f hi).obj T ⟶ Z) ≃ (T ⟶ (baseChangeFunctor i f hi).obj Z) where
  toFun := gluingToPair i f hi
  invFun := gluingFromPair i f hi
  left_inv k := by
    have := gluingHasPushout i f hi T
    apply Over.OverMorphism.ext
    refine pushout.hom_ext ?_ ?_
    · exact (inl_comp_gluingFromPair i f hi (gluingToPair i f hi k)).trans
        (gluingToPair_right_comp_fst i f hi k)
    · exact (inr_comp_gluingFromPair i f hi (gluingToPair i f hi k)).trans
        (gluingToPair_left_comp_fst i f hi k)
  right_inv h := by
    have := gluingHasPushout i f hi T
    apply ObjectProperty.hom_ext
    apply Comma.hom_ext
    · apply Over.OverMorphism.ext
      refine pullback.hom_ext ?_ ?_
      · exact (gluingToPair_left_comp_fst i f hi (gluingFromPair i f hi h)).trans
          (inr_comp_gluingFromPair i f hi h)
      · change _ = h.hom.left.left ≫ ((Over.pullback (pushout.inr i f)).obj Z).hom
        exact (Over.w _).trans (Over.w _).symm
    · apply Over.OverMorphism.ext
      refine pullback.hom_ext ?_ ?_
      · exact (gluingToPair_right_comp_fst i f hi (gluingFromPair i f hi h)).trans
          (inl_comp_gluingFromPair i f hi h)
      · change _ = h.hom.right.left ≫ ((Over.pullback (pushout.inl i f)).obj Z).hom
        exact (Over.w _).trans (Over.w _).symm

/-- The forward direction of the hom-set bijection is `Stacks.Pushout.gluingToPair`. -/
@[simp] theorem gluingHomEquiv_apply {X X' Y : Scheme.{u}}
    (i : X ⟶ X') (f : X ⟶ Y)
    (hi : IsThickening i) [IsAffineHom f] [HasPushout i f]
    (T : gluingData i f) (Z : Over (pushout i f))
    (k : (gluingFunctor i f hi).obj T ⟶ Z) :
    gluingHomEquiv i f hi T Z k = gluingToPair i f hi k :=
  rfl

/-- The backward direction of the hom-set bijection is `Stacks.Pushout.gluingFromPair`. -/
@[simp] theorem gluingHomEquiv_symm_apply {X X' Y : Scheme.{u}}
    (i : X ⟶ X') (f : X ⟶ Y)
    (hi : IsThickening i) [IsAffineHom f] [HasPushout i f]
    (T : gluingData i f) (Z : Over (pushout i f))
    (h : T ⟶ (baseChangeFunctor i f hi).obj Z) :
    (gluingHomEquiv i f hi T Z).symm h = gluingFromPair i f hi h :=
  rfl

/-- **Stacks Project, Tag 07RV, the adjunction.**  Gluing is left adjoint to
base change: a morphism from the glued scheme `V ⨿_U U'` to a scheme `Z` over `Y'` is the same
thing as a morphism of compatible pairs from `(V, U', φ)` to the base change of `Z`.

The bijection is the universal property of the pushout on one side and of the two fibre products
on the other. -/
@[stacks 07RV "the adjunction G ⊣ F"]
noncomputable def gluingAdjunction {X X' Y : Scheme.{u}}
    (i : X ⟶ X') (f : X ⟶ Y)
    (hi : IsThickening i) [IsAffineHom f] :
    letI := hasPushout_of_isThickening i f hi
    gluingFunctor i f hi ⊣ baseChangeFunctor i f hi :=
  letI := hasPushout_of_isThickening i f hi
  Adjunction.mkOfHomEquiv {
    homEquiv := gluingHomEquiv i f hi
    homEquiv_naturality_left_symm := by
      intro T S Z a h
      have := gluingHasPushout i f hi T
      have := gluingHasPushout i f hi S
      apply Over.OverMorphism.ext
      refine pushout.hom_ext ?_ ?_
      · exact (inl_comp_gluingFromPair i f hi (a ≫ h)).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (fun m => Over.Hom.left a.hom.right ≫ m)
              (inl_comp_gluingFromPair i f hi h)).symm.trans
                (gluingPushoutMap_inl_assoc i f a _).symm))
      · exact (inr_comp_gluingFromPair i f hi (a ≫ h)).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (fun m => Over.Hom.left a.hom.left ≫ m)
              (inr_comp_gluingFromPair i f hi h)).symm.trans
                (gluingPushoutMap_inr_assoc i f a _).symm))
    homEquiv_naturality_right := by
      intro T Z W h k
      have := gluingHasPushout i f hi T
      apply ObjectProperty.hom_ext
      apply Comma.hom_ext
      · apply Over.OverMorphism.ext
        refine pullback.hom_ext ?_ ?_
        · exact (gluingToPair_left_comp_fst i f hi (h ≫ k)).trans
            (((Category.assoc _ _ _).trans
              ((congrArg (fun m => (gluingToPair i f hi h).hom.left.left ≫ m)
                (pullback.lift_fst _ _ _ :
                  ((Over.pullback (pushout.inr i f)).map k).left ≫
                    pullback.fst W.hom (pushout.inr i f) = _)).trans
                  (gluingToPair_left_comp_fst_assoc i f hi h k.left))).symm)
        · exact (gluingToPair_left_comp_snd i f hi (h ≫ k)).trans
            (((Category.assoc _ _ _).trans
              ((congrArg (fun m => (gluingToPair i f hi h).hom.left.left ≫ m)
                (pullback.lift_snd _ _ _ :
                  ((Over.pullback (pushout.inr i f)).map k).left ≫
                    pullback.snd W.hom (pushout.inr i f) = _)).trans
                  (gluingToPair_left_comp_snd i f hi h))).symm)
      · apply Over.OverMorphism.ext
        refine pullback.hom_ext ?_ ?_
        · exact (gluingToPair_right_comp_fst i f hi (h ≫ k)).trans
            (((Category.assoc _ _ _).trans
              ((congrArg (fun m => (gluingToPair i f hi h).hom.right.left ≫ m)
                (pullback.lift_fst _ _ _ :
                  ((Over.pullback (pushout.inl i f)).map k).left ≫
                    pullback.fst W.hom (pushout.inl i f) = _)).trans
                  (gluingToPair_right_comp_fst_assoc i f hi h k.left))).symm)
        · exact (gluingToPair_right_comp_snd i f hi (h ≫ k)).trans
            (((Category.assoc _ _ _).trans
              ((congrArg (fun m => (gluingToPair i f hi h).hom.right.left ≫ m)
                (pullback.lift_snd _ _ _ :
                  ((Over.pullback (pushout.inl i f)).map k).left ≫
                    pullback.snd W.hom (pushout.inl i f) = _)).trans
                  (gluingToPair_right_comp_snd i f hi h))).symm) }

/-! ### The composition of gluing with base change is the identity -/

/-- **Milnor patching, base change, for abstract fibre products.**  Let `R = B ×_A A'` be a ring
fibre product along a surjection `A' → A`, let `D` and `C'` be algebras over `B` and `A'` whose
base changes to `A` agree, and let `P = D ×_C C'` be the resulting fibre product: then `D` and
`C'` are the base changes of `P` along `R → B` and `R → A'`.

This is `MilnorPatching.pullback_baseChange`, which is stated for the literal fibre product
`RingHom.pullback`, carried over to a pair of abstract fibre products by the uniqueness of
pullbacks.  It is the pushout half of
`MilnorPatching.finiteType_and_isPushout_of_fibreProduct`, without that lemma's finite-type
hypotheses and finite-type conclusion. -/
private theorem isPushout_of_fibreProduct
    {A A' B D C' C R P : CommRingCat.{u}}
    {toBase : B ⟶ A} {surjection : A' ⟶ A} {BtoD : B ⟶ D} {A'toC' : A' ⟶ C'}
    {AtoC : A ⟶ C} {DtoC : D ⟶ C} {C'toC : C' ⟶ C}
    {toB : R ⟶ B} {toA' : R ⟶ A'} {comparison : R ⟶ P} {PtoD : P ⟶ D} {PtoC' : P ⟶ C'}
    (hSource : IsPullback toB toA' toBase surjection)
    (hTarget : IsPullback PtoD PtoC' DtoC C'toC)
    (hD : IsPushout BtoD toBase DtoC AtoC)
    (hC' : IsPushout A'toC' surjection C'toC AtoC)
    (hsurj : Function.Surjective surjection.hom)
    (hw₁ : toB ≫ BtoD = comparison ≫ PtoD)
    (hw₂ : toA' ≫ A'toC' = comparison ≫ PtoC') :
    IsPushout comparison toB PtoD BtoD ∧ IsPushout comparison toA' PtoC' A'toC' := by
  let base : RingFibreProduct.Situation toBase.hom surjection.hom
      (RingHom.ker surjection.hom) := ⟨hsurj, rfl⟩
  let sourceCone := base.pullbackCone
  let sourcePullback := IsPullback.of_isLimit base.pullbackConeIsLimit
  let targetCone := CommRingCat.pullbackCone DtoC C'toC
  let targetLimit := CommRingCat.pullbackConeIsLimit DtoC C'toC
  let targetPullback := IsPullback.of_isLimit targetLimit
  let toD' : base.fibreProduct →+* RingHom.pullback DtoC.hom C'toC.hom :=
    RingHom.codRestrict ((BtoD.hom.comp base.pullbackCone.fst.hom).prod
        (A'toC'.hom.comp base.pullbackCone.snd.hom))
      (RingHom.pullback DtoC.hom C'toC.hom) (fun x ↦ by
        change DtoC.hom (BtoD.hom (base.pullbackCone.fst.hom x)) =
          C'toC.hom (A'toC'.hom (base.pullbackCone.snd.hom x))
        have hd : DtoC.hom.comp BtoD.hom = AtoC.hom.comp toBase.hom :=
          congrArg CommRingCat.Hom.hom hD.w
        have hc : C'toC.hom.comp A'toC'.hom = AtoC.hom.comp surjection.hom :=
          congrArg CommRingCat.Hom.hom hC'.w
        calc
          _ = AtoC.hom (toBase.hom (base.pullbackCone.fst.hom x)) := DFunLike.congr_fun hd _
          _ = AtoC.hom (surjection.hom (base.pullbackCone.snd.hom x)) := congrArg AtoC.hom
            (DFunLike.congr_fun
              (congrArg CommRingCat.Hom.hom base.pullbackCone.condition) x)
          _ = _ := (DFunLike.congr_fun hc _).symm)
  let eSource := hSource.isoIsPullback _ _ sourcePullback
  let eTarget := hTarget.isoIsPullback _ _ targetPullback
  have hSourceInvFst : eSource.inv ≫ toB = sourceCone.fst :=
    hSource.isoIsPullback_inv_fst _ _ sourcePullback
  have hSourceInvSnd : eSource.inv ≫ toA' = sourceCone.snd :=
    hSource.isoIsPullback_inv_snd _ _ sourcePullback
  have hTargetHomFst : eTarget.hom ≫ targetCone.fst = PtoD :=
    hTarget.isoIsPullback_hom_fst _ _ targetPullback
  have hTargetHomSnd : eTarget.hom ≫ targetCone.snd = PtoC' :=
    hTarget.isoIsPullback_hom_snd _ _ targetPullback
  have hpullfst : sourceCone.fst ≫ BtoD = CommRingCat.ofHom toD' ≫ targetCone.fst := by
    apply CommRingCat.hom_ext
    ext x
    rfl
  have hpullsnd : sourceCone.snd ≫ A'toC' = CommRingCat.ofHom toD' ≫ targetCone.snd := by
    apply CommRingCat.hom_ext
    ext x
    rfl
  have hfst : (eSource.inv ≫ comparison ≫ eTarget.hom) ≫ targetCone.fst =
      CommRingCat.ofHom toD' ≫ targetCone.fst := by
    simp only [Category.assoc]
    rw [hTargetHomFst, ← hw₁, ← Category.assoc, hSourceInvFst]
    exact hpullfst
  have hsnd : (eSource.inv ≫ comparison ≫ eTarget.hom) ≫ targetCone.snd =
      CommRingCat.ofHom toD' ≫ targetCone.snd := by
    simp only [Category.assoc]
    rw [hTargetHomSnd, ← hw₂, ← Category.assoc, hSourceInvSnd]
    exact hpullsnd
  have hfactor : eSource.inv ≫ comparison ≫ eTarget.hom = CommRingCat.ofHom toD' :=
    PullbackCone.IsLimit.hom_ext targetLimit hfst hsnd
  have hp := MilnorPatching.pullback_baseChange base BtoD.hom A'toC'.hom AtoC.hom DtoC.hom
    C'toC.hom hD hC' toD' (fun _ => rfl) (fun _ => rfl)
  have hmap : CommRingCat.ofHom toD' ≫ eTarget.inv = eSource.inv ≫ comparison :=
    (congrArg (fun k => k ≫ eTarget.inv) hfactor).symm.trans (by
      rw [Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id])
  have hTargetFst : targetCone.fst = eTarget.inv ≫ PtoD := by
    rw [← hTargetHomFst, Iso.inv_hom_id_assoc]
  have hTargetSnd : targetCone.snd = eTarget.inv ≫ PtoC' := by
    rw [← hTargetHomSnd, Iso.inv_hom_id_assoc]
  refine ⟨?_, ?_⟩
  · exact hp.1.of_iso eSource.symm eTarget.symm (Iso.refl _) (Iso.refl _)
      hmap (by
        change sourceCone.fst ≫ 𝟙 _ = eSource.inv ≫ toB
        simpa only [Category.comp_id] using hSourceInvFst.symm)
      (by
        change targetCone.fst ≫ 𝟙 _ = eTarget.inv ≫ PtoD
        simpa only [Category.comp_id] using hTargetFst)
      (by simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]; rfl)
  · exact hp.2.of_iso eSource.symm eTarget.symm (Iso.refl _) (Iso.refl _)
      hmap (by
        change sourceCone.snd ≫ 𝟙 _ = eSource.inv ≫ toA'
        simpa only [Category.comp_id] using hSourceInvSnd.symm)
      (by
        change targetCone.snd ≫ 𝟙 _ = eTarget.inv ≫ PtoC'
        simpa only [Category.comp_id] using hTargetSnd)
      (by simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]; rfl)

/-- The map on sections over an open whose inverse image is a given open is the map on sections
over the whole inverse image, transported along that equality of opens. -/
private theorem appLE_eq_app_comp_eqToHom {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.Opens) (V : X.Opens) (h : f ⁻¹ᵁ U = V) :
    f.appLE U V h.ge = f.app U ≫ eqToHom (congrArg (fun W ↦ Γ(X, W)) h) := by
  subst V
  simp [Scheme.Hom.appLE_eq_app]

/-- **The affine case of the two cartesian squares of [Stacks Project, Tag 07RV].**  Two squares
of affine schemes, the lower one `(i, f, a, b)` and the upper one `(j, g, c, d)`, joined by
`z`, `w`, `v`, `q`, in which the two squares of global sections are cartesian, the two side
squares are cartesian, and the map `i` is surjective on global sections: then the two remaining
side squares are cartesian as well.

The ring content is `Stacks.Pushout.isPushout_of_fibreProduct`; everything else is the
dictionary between a cartesian square of affine schemes and a cocartesian square of their global
sections, in both directions. -/
private theorem isPullback_of_affine_ring_cube
    {X X' Y P U U' V W : Scheme.{u}}
    [IsAffine X] [IsAffine X'] [IsAffine Y] [IsAffine P]
    [IsAffine U] [IsAffine U'] [IsAffine V] [IsAffine W]
    (i : X ⟶ X') (f : X ⟶ Y) (a : X' ⟶ P) (b : Y ⟶ P)
    (j : U ⟶ U') (g : U ⟶ V) (c : U' ⟶ W) (d : V ⟶ W)
    (z : U ⟶ X) (w : U' ⟶ X') (v : V ⟶ Y) (q : W ⟶ P)
    (hR : IsPullback b.appTop a.appTop f.appTop i.appTop)
    (hP : IsPullback d.appTop c.appTop g.appTop j.appTop)
    (hv : IsPullback g z v f) (hw : IsPullback j z w i)
    (hqd : d ≫ q = v ≫ b) (hqc : c ≫ q = w ≫ a)
    (hi : Function.Surjective i.appTop.hom) :
    IsPullback d v q b ∧ IsPullback c w q a := by
  have hv' := isPushout_appTop_of_isPullback hv
  have hw' := isPushout_appTop_of_isPullback hw
  have hqd' : q.appTop ≫ d.appTop = b.appTop ≫ v.appTop := by
    simpa only [← Scheme.Hom.comp_appTop] using congrArg Scheme.Hom.appTop hqd
  have hqc' : q.appTop ≫ c.appTop = a.appTop ≫ w.appTop := by
    simpa only [← Scheme.Hom.comp_appTop] using congrArg Scheme.Hom.appTop hqc
  obtain ⟨hb, ha⟩ :=
    isPushout_of_fibreProduct hR hP hv' hw' hi hqd'.symm hqc'.symm
  exact ⟨AlgebraicGeometry.isPullback_of_isPushout_appTop hb, AlgebraicGeometry.isPullback_of_isPushout_appTop ha⟩

/-- A square of schemes is cartesian as soon as it becomes cartesian over every affine open of
the lower right corner above an affine open of the base. -/
private theorem isPullback_of_affine_neighbourhoods
    {A B C D : Scheme.{u}} (a : A ⟶ B) (b : A ⟶ C) (c : B ⟶ D) (d : C ⟶ D)
    (H : ∀ (UD : D.Opens) (UB : B.Opens), IsAffineOpen UD → IsAffineOpen UB →
      UB ≤ c ⁻¹ᵁ UD →
      IsPullback (a ∣_ UB) ((a ⁻¹ᵁ UB).ι ≫ b) (UB.ι ≫ c) d) :
    IsPullback a b c d := by
  apply AlgebraicGeometry.isPullback_of_forall_exists_restrict
  intro x
  obtain ⟨UD, hUD, hxD, -⟩ := exists_isAffineOpen_mem_and_subset
    (show c x ∈ (⊤ : D.Opens) from trivial)
  obtain ⟨UB, hUB, hxB, hBD⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ c ⁻¹ᵁ UD from hxD)
  exact ⟨UB, hxB, H UD UB hUD hUB hBD⟩

/-- The cartesian square of sections over an open `S` of the apex, read as a cartesian square of
the global sections of the four restricted schemes. -/
private theorem isPullback_appTop_restrict_of_sections
    {X X' Y P : Scheme.{u}}
    (i : X ⟶ X') (f : X ⟶ Y) (a : X' ⟶ P) (b : Y ⟶ P)
    (comm : i ≫ a = f ≫ b) (S : P.Opens)
    (H : IsPullback (b.app S) (a.app S) (f.app (b ⁻¹ᵁ S))
      (i.app (a ⁻¹ᵁ S) ≫ eqToHom (congrArg (fun V ↦ Γ(X, V))
        (congrArg (fun k : X ⟶ P ↦ k ⁻¹ᵁ S) comm)))) :
    IsPullback (b ∣_ S).appTop (a ∣_ S).appTop
      (f ∣_ (b ⁻¹ᵁ S)).appTop
      (i.resLE (a ⁻¹ᵁ S) (f ⁻¹ᵁ (b ⁻¹ᵁ S))
        (by simp only [← Scheme.Hom.comp_preimage, comm]; exact le_rfl)).appTop := by
  have he : i ⁻¹ᵁ (a ⁻¹ᵁ S) = f ⁻¹ᵁ (b ⁻¹ᵁ S) :=
    congrArg (fun k : X ⟶ P ↦ k ⁻¹ᵁ S) comm
  rw [← appLE_eq_app_comp_eqToHom i (a ⁻¹ᵁ S) _ he] at H
  apply H.of_iso S.topIso.symm (b ⁻¹ᵁ S).topIso.symm
    (a ⁻¹ᵁ S).topIso.symm (f ⁻¹ᵁ (b ⁻¹ᵁ S)).topIso.symm
  · have hh : b.appLE S (b ⁻¹ᵁ S) le_rfl ≫ (b ⁻¹ᵁ S).topIso.inv =
        S.topIso.inv ≫ (b.resLE S (b ⁻¹ᵁ S) le_rfl).appTop :=
      (arrowResLEAppIso b S (b ⁻¹ᵁ S) le_rfl).inv.w.symm
    simpa only [Scheme.Hom.appLE_eq_app, Scheme.Hom.resLE_eq_morphismRestrict,
      Iso.symm_hom] using hh
  · have hh : a.appLE S (a ⁻¹ᵁ S) le_rfl ≫ (a ⁻¹ᵁ S).topIso.inv =
        S.topIso.inv ≫ (a.resLE S (a ⁻¹ᵁ S) le_rfl).appTop :=
      (arrowResLEAppIso a S (a ⁻¹ᵁ S) le_rfl).inv.w.symm
    simpa only [Scheme.Hom.appLE_eq_app, Scheme.Hom.resLE_eq_morphismRestrict,
      Iso.symm_hom] using hh
  · have hh : f.appLE (b ⁻¹ᵁ S) (f ⁻¹ᵁ (b ⁻¹ᵁ S)) le_rfl ≫
        (f ⁻¹ᵁ (b ⁻¹ᵁ S)).topIso.inv = (b ⁻¹ᵁ S).topIso.inv ≫
        (f.resLE (b ⁻¹ᵁ S) (f ⁻¹ᵁ (b ⁻¹ᵁ S)) le_rfl).appTop :=
      (arrowResLEAppIso f (b ⁻¹ᵁ S) (f ⁻¹ᵁ (b ⁻¹ᵁ S)) le_rfl).inv.w.symm
    simpa only [Scheme.Hom.appLE_eq_app, Scheme.Hom.resLE_eq_morphismRestrict,
      Iso.symm_hom] using hh
  · exact (arrowResLEAppIso i (a ⁻¹ᵁ S) (f ⁻¹ᵁ (b ⁻¹ᵁ S)) he.ge).inv.w.symm

/-- The fourth assertion of [Stacks Project, Tag 07RT] for a square `(i, f, a, b)`: over every
open of the apex the square of rings of sections is cartesian. -/
private abbrev IsSectionPullback {X X' Y P : Scheme.{u}}
    (i : X ⟶ X') (f : X ⟶ Y) (a : X' ⟶ P) (b : Y ⟶ P)
    (comm : i ≫ a = f ≫ b) : Prop :=
  ∀ S : P.Opens, IsPullback (b.app S) (a.app S) (f.app (b ⁻¹ᵁ S))
    (i.app (a ⁻¹ᵁ S) ≫ eqToHom (congrArg (fun V ↦ Γ(X, V))
      (congrArg (fun k : X ⟶ P ↦ k ⁻¹ᵁ S) comm)))

/-- **The two cartesian squares of [Stacks Project, Tag 07RV], in general.**  Two squares joined
by `z`, `w`, `v`, `q` as in `Stacks.Pushout.isPullback_of_affine_ring_cube`, in which the lower
`i` is a closed immersion, all the vertical maps are affine, the two squares of *sections* are
cartesian over every open, and the two side squares `(g, z, v, f)` and `(j, z, w, i)` are
cartesian: then the two remaining side squares are cartesian.

Both conclusions are local on the apex `P`: over an affine open `S` of `P` and an affine open `T`
of `W` above it all eight schemes in sight become affine, the two cartesian squares of sections
become cartesian squares of global sections by
`Stacks.Pushout.isPullback_appTop_restrict_of_sections`, and the affine case
`Stacks.Pushout.isPullback_of_affine_ring_cube` applies. -/
private theorem isPullback_of_section_cube
    {X X' Y P U U' V W : Scheme.{u}}
    (i : X ⟶ X') (f : X ⟶ Y) (a : X' ⟶ P) (b : Y ⟶ P)
    (j : U ⟶ U') (g : U ⟶ V) (c : U' ⟶ W) (d : V ⟶ W)
    (z : U ⟶ X) (w : U' ⟶ X') (v : V ⟶ Y) (q : W ⟶ P)
    [IsClosedImmersion i] [IsAffineHom f] [IsAffineHom g]
    [IsAffineHom a] [IsAffineHom b] [IsAffineHom c] [IsAffineHom d]
    (hRcomm : i ≫ a = f ≫ b) (hPcomm : j ≫ c = g ≫ d)
    (hR : IsSectionPullback i f a b hRcomm)
    (hP : IsSectionPullback j g c d hPcomm)
    (hv : IsPullback g z v f) (hw : IsPullback j z w i)
    (hqd : d ≫ q = v ≫ b) (hqc : c ≫ q = w ≫ a) :
    IsPullback d v q b ∧ IsPullback c w q a := by
  have Hloc (S : P.Opens) (T : W.Opens) (hS : IsAffineOpen S)
      (hT : IsAffineOpen T) (hTS : T ≤ q ⁻¹ᵁ S) :
      IsPullback (d ∣_ T) ((d ⁻¹ᵁ T).ι ≫ v) (T.ι ≫ q) b ∧
      IsPullback (c ∣_ T) ((c ⁻¹ᵁ T).ι ≫ w) (T.ι ≫ q) a := by
    have hiS : f ⁻¹ᵁ (b ⁻¹ᵁ S) = i ⁻¹ᵁ (a ⁻¹ᵁ S) := by
      simp only [← Scheme.Hom.comp_preimage, hRcomm]
    have hjT : g ⁻¹ᵁ (d ⁻¹ᵁ T) = j ⁻¹ᵁ (c ⁻¹ᵁ T) := by
      simp only [← Scheme.Hom.comp_preimage, hPcomm]
    have hvS : d ⁻¹ᵁ T ≤ v ⁻¹ᵁ (b ⁻¹ᵁ S) := by
      calc
        _ ≤ d ⁻¹ᵁ (q ⁻¹ᵁ S) := d.preimage_mono hTS
        _ = _ := by simp only [← Scheme.Hom.comp_preimage, hqd]
    have hwS : c ⁻¹ᵁ T ≤ w ⁻¹ᵁ (a ⁻¹ᵁ S) := by
      calc
        _ ≤ c ⁻¹ᵁ (q ⁻¹ᵁ S) := c.preimage_mono hTS
        _ = _ := by simp only [← Scheme.Hom.comp_preimage, hqc]
    have hzS : g ⁻¹ᵁ (d ⁻¹ᵁ T) ≤ z ⁻¹ᵁ (f ⁻¹ᵁ (b ⁻¹ᵁ S)) := by
      calc
        _ ≤ g ⁻¹ᵁ (v ⁻¹ᵁ (b ⁻¹ᵁ S)) := g.preimage_mono hvS
        _ = _ := congrArg (fun k : U ⟶ Y => k ⁻¹ᵁ (b ⁻¹ᵁ S)) hv.w
    let ir := i.resLE (a ⁻¹ᵁ S) (f ⁻¹ᵁ (b ⁻¹ᵁ S)) hiS.le
    let jr := j.resLE (c ⁻¹ᵁ T) (g ⁻¹ᵁ (d ⁻¹ᵁ T)) hjT.le
    let vr := v.resLE (b ⁻¹ᵁ S) (d ⁻¹ᵁ T) hvS
    let wr := w.resLE (a ⁻¹ᵁ S) (c ⁻¹ᵁ T) hwS
    let zr := z.resLE (f ⁻¹ᵁ (b ⁻¹ᵁ S)) (g ⁻¹ᵁ (d ⁻¹ᵁ T)) hzS
    let qr := q.resLE S T hTS
    letI : IsAffine S.toScheme := hS
    letI : IsAffine T.toScheme := hT
    letI : IsAffine (a ⁻¹ᵁ S).toScheme := hS.preimage a
    letI : IsAffine (b ⁻¹ᵁ S).toScheme := hS.preimage b
    letI : IsAffine (f ⁻¹ᵁ (b ⁻¹ᵁ S)).toScheme := (hS.preimage b).preimage f
    letI : IsAffine (c ⁻¹ᵁ T).toScheme := hT.preimage c
    letI : IsAffine (d ⁻¹ᵁ T).toScheme := hT.preimage d
    letI : IsAffine (g ⁻¹ᵁ (d ⁻¹ᵁ T)).toScheme := (hT.preimage d).preimage g
    have hir : IsPullback ir (f ⁻¹ᵁ (b ⁻¹ᵁ S)).ι (a ⁻¹ᵁ S).ι i := by
      apply IsOpenImmersion.isPullback
      · exact (Scheme.Hom.resLE_comp_ι _ _).symm
      · simpa using hiS.symm
    haveI : IsClosedImmersion ir :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback hir.flip inferInstance
    have hvr : IsPullback (g ∣_ (d ⁻¹ᵁ T)) zr vr (f ∣_ (b ⁻¹ᵁ S)) := by
      simpa only [Scheme.Hom.resLE_eq_morphismRestrict] using
        Scheme.Hom.isPullback_resLE hv le_rfl hvS (inf_eq_left.mpr hzS).symm
    have hwr : IsPullback jr zr wr ir := by
      apply Scheme.Hom.isPullback_resLE hw hiS.le hwS
      rw [← hjT, inf_eq_left.mpr hzS]
    have hqdr : (d ∣_ T) ≫ qr = vr ≫ (b ∣_ S) := by
      dsimp only [qr, vr]
      rw [← Scheme.Hom.resLE_eq_morphismRestrict d (U := T),
        ← Scheme.Hom.resLE_eq_morphismRestrict b (U := S)]
      simp only [Scheme.Hom.resLE_comp_resLE, hqd]
    have hqcr : (c ∣_ T) ≫ qr = wr ≫ (a ∣_ S) := by
      dsimp only [qr, wr]
      rw [← Scheme.Hom.resLE_eq_morphismRestrict c (U := T),
        ← Scheme.Hom.resLE_eq_morphismRestrict a (U := S)]
      simp only [Scheme.Hom.resLE_comp_resLE, hqc]
    obtain ⟨hd, hc⟩ := isPullback_of_affine_ring_cube
      ir (f ∣_ (b ⁻¹ᵁ S)) (a ∣_ S) (b ∣_ S)
      jr (g ∣_ (d ⁻¹ᵁ T)) (c ∣_ T) (d ∣_ T) zr wr vr qr
      (isPullback_appTop_restrict_of_sections i f a b hRcomm S (hR S))
      (isPullback_appTop_restrict_of_sections j g c d hPcomm T (hP T))
      hvr hwr hqdr hqcr (IsClosedImmersion.isAffine_surjective_of_isAffine ir).2
    constructor
    · simpa only [vr, qr, Scheme.Hom.resLE_comp_ι] using
        hd.paste_vert (isPullback_morphismRestrict b S)
    · simpa only [wr, qr, Scheme.Hom.resLE_comp_ι] using
        hc.paste_vert (isPullback_morphismRestrict a S)
  exact ⟨isPullback_of_affine_neighbourhoods d v q b
    (fun S T hS hT hTS => (Hloc S T hS hT hTS).1),
    isPullback_of_affine_neighbourhoods c w q a
      (fun S T hS hT hTS => (Hloc S T hS hT hTS).2)⟩

/-- A morphism out of a thickening is affine as soon as its restriction to the thickened
subscheme is: the preimage of an affine open is a thickening of the preimage in the subscheme,
which is affine. -/
private theorem isAffineHom_of_thickening_comp
    {X X' Y : Scheme.{u}} (i : X ⟶ X') (g : X' ⟶ Y)
    (hi : IsThickening i) [IsAffineHom (i ≫ g)] : IsAffineHom g := by
  constructor
  intro U hU
  have hs : IsAffineOpen (i ⁻¹ᵁ (g ⁻¹ᵁ U)) := hU.preimage (i ≫ g)
  exact forall_isAffine_of_isThickening _ _ (i ∣_ (g ⁻¹ᵁ U))
    (isThickening_of_isPullback (isPullback_morphismRestrict i (g ⁻¹ᵁ U)) hi) hs

/-- The map from the `Y`-component of a compatible pair into the glued scheme is a thickening:
it is the map from `V` into `V ⨿_U U'`, and `U ⟶ U'` is a thickening, so this is the second
assertion of [Stacks Project, Tag 07RT]. -/
theorem gluing_inr_isThickening {X X' Y : Scheme.{u}}
    (i : X ⟶ X') (f : X ⟶ Y) (hi : IsThickening i) [IsAffineHom f]
    (T : gluingData i f)
    [HasPushout (pullback.fst T.obj.right.hom i) (gluingSourceMap i f T)] :
    IsThickening (pushout.inr (pullback.fst T.obj.right.hom i) (gluingSourceMap i f T)) := by
  have := isAffineHom_gluingSourceMap i f T
  exact pushout_inr_isThickening forall_isAffine_of_isThickening _ _
    (isThickening_pullback_fst i f hi T)

/-- **The two cartesian squares of [Stacks Project, Tag 07RV].**  For a
compatible pair `T = (V, U', φ)`, both squares

```
V  ⟶ V ⨿_U U'      U' ⟶ V ⨿_U U'
↓        ↓          ↓        ↓
Y  ⟶    Y'          X' ⟶    Y'
```

are cartesian: the two components of `T` are recovered from the glued scheme by base change
along `Y ⟶ Y'` and `X' ⟶ Y'`.

Both cocartesian squares have cartesian squares of sections by the fourth assertion of
[Stacks Project, Tag 07RT], so this is
`Stacks.Pushout.isPullback_of_section_cube` applied to the cube built from them. -/
theorem gluing_components_isPullback {X X' Y : Scheme.{u}}
    (i : X ⟶ X') (f : X ⟶ Y)
    (hi : IsThickening i) [IsAffineHom f] [HasPushout i f]
    (T : gluingData i f)
    [HasPushout (pullback.fst T.obj.right.hom i) (gluingSourceMap i f T)] :
    IsPullback
        (pushout.inr (pullback.fst T.obj.right.hom i) (gluingSourceMap i f T))
        T.obj.left.hom ((gluingFunctor i f hi).obj T).hom (pushout.inr i f) ∧
      IsPullback
        (pushout.inl (pullback.fst T.obj.right.hom i) (gluingSourceMap i f T))
        T.obj.right.hom ((gluingFunctor i f hi).obj T).hom (pushout.inl i f) := by
  letI : IsClosedImmersion i := hi.1
  have hj := isThickening_pullback_fst i f hi T
  have hb := pushout_inr_isThickening forall_isAffine_of_isThickening i f hi
  have hd := gluing_inr_isThickening i f hi T
  letI : IsClosedImmersion (pushout.inr i f) := hb.1
  letI : IsClosedImmersion
      (pushout.inr (pullback.fst T.obj.right.hom i) (gluingSourceMap i f T)) := hd.1
  have := isAffineHom_gluingSourceMap i f T
  haveI : IsAffineHom (i ≫ pushout.inl i f) := by
    rw [pushout.condition]
    infer_instance
  haveI : IsAffineHom (pushout.inl i f) :=
    isAffineHom_of_thickening_comp i _ hi
  haveI : IsAffineHom (pullback.fst T.obj.right.hom i ≫
      pushout.inl (pullback.fst T.obj.right.hom i) (gluingSourceMap i f T)) := by
    rw [pushout.condition]
    infer_instance
  haveI : IsAffineHom
      (pushout.inl (pullback.fst T.obj.right.hom i) (gluingSourceMap i f T)) :=
    isAffineHom_of_thickening_comp _ _ hj
  exact isPullback_of_section_cube i f (pushout.inl i f) (pushout.inr i f)
    (pullback.fst T.obj.right.hom i) (gluingSourceMap i f T)
    (pushout.inl _ _) (pushout.inr _ _)
    (pullback.snd T.obj.right.hom i) T.obj.right.hom T.obj.left.hom
    (gluingPushoutData i f T).hom
    pushout.condition pushout.condition
    (pushout_structureSheaf_isPullback forall_isAffine_of_isThickening i f hi)
    (pushout_structureSheaf_isPullback forall_isAffine_of_isThickening _ _ hj)
    (gluingSourceMap_isPullback i f T) (IsPullback.of_hasPullback T.obj.right.hom i)
    (gluingPushoutData_inr i f T) (gluingPushoutData_inl i f T)

/-- **The unit of the gluing adjunction is an isomorphism at every compatible pair.**  Its two
components are the comparison maps of the two cartesian squares of
`Stacks.Pushout.gluing_components_isPullback`, so each is an isomorphism; a morphism of
compatible pairs whose two components are isomorphisms is an isomorphism. -/
theorem gluingAdjunction_unit_app_isIso {X X' Y : Scheme.{u}}
    (i : X ⟶ X') (f : X ⟶ Y)
    (hi : IsThickening i) [IsAffineHom f] [HasPushout i f]
    (T : gluingData i f) : IsIso ((gluingAdjunction i f hi).unit.app T) := by
  letI := gluingHasPushout i f hi T
  obtain ⟨hd, hc⟩ := gluing_components_isPullback i f hi T
  let η := (gluingAdjunction i f hi).unit.app T
  let ηl : T.obj.left.left ⟶
      pullback ((gluingFunctor i f hi).obj T).hom (pushout.inr i f) := η.hom.left.left
  let ηr : T.obj.right.left ⟶
      pullback ((gluingFunctor i f hi).obj T).hom (pushout.inl i f) := η.hom.right.left
  have hlfst : ηl ≫ pullback.fst ((gluingFunctor i f hi).obj T).hom (pushout.inr i f) =
      pushout.inr (pullback.fst T.obj.right.hom i) (gluingSourceMap i f T) :=
    (gluingToPair_left_comp_fst i f hi (𝟙 ((gluingFunctor i f hi).obj T))).trans
      (Category.comp_id _)
  have hlsnd : ηl ≫ pullback.snd ((gluingFunctor i f hi).obj T).hom (pushout.inr i f) =
      T.obj.left.hom :=
    gluingToPair_left_comp_snd i f hi (𝟙 ((gluingFunctor i f hi).obj T))
  have hrfst : ηr ≫ pullback.fst ((gluingFunctor i f hi).obj T).hom (pushout.inl i f) =
      pushout.inl (pullback.fst T.obj.right.hom i) (gluingSourceMap i f T) :=
    (gluingToPair_right_comp_fst i f hi (𝟙 ((gluingFunctor i f hi).obj T))).trans
      (Category.comp_id _)
  have hrsnd : ηr ≫ pullback.snd ((gluingFunctor i f hi).obj T).hom (pushout.inl i f) =
      T.obj.right.hom :=
    gluingToPair_right_comp_snd i f hi (𝟙 ((gluingFunctor i f hi).obj T))
  have hleft : ηl = hd.isoPullback.hom :=
    pullback.hom_ext (hlfst.trans hd.isoPullback_hom_fst.symm)
      (hlsnd.trans hd.isoPullback_hom_snd.symm)
  have hright : ηr = hc.isoPullback.hom :=
    pullback.hom_ext (hrfst.trans hc.isoPullback_hom_fst.symm)
      (hrsnd.trans hc.isoPullback_hom_snd.symm)
  haveI : IsIso ηl := hleft ▸ hd.isoPullback.isIso_hom
  haveI : IsIso ηr := hright ▸ hc.isoPullback.isIso_hom
  haveI : IsIso ((Over.forget Y).map η.hom.left) := by
    change IsIso ηl
    infer_instance
  haveI : IsIso ((Over.forget X').map η.hom.right) := by
    change IsIso ηr
    infer_instance
  haveI : IsIso η.hom.left := isIso_of_reflects_iso η.hom.left (Over.forget Y)
  haveI : IsIso η.hom.right := isIso_of_reflects_iso η.hom.right (Over.forget X')
  let e := Comma.isoMk (asIso η.hom.left) (asIso η.hom.right) η.hom.w
  have he : e.hom = η.hom := by apply Comma.hom_ext <;> rfl
  haveI : IsIso η.hom := he ▸ e.isIso_hom
  exact (ObjectProperty.isIso_hom_iff η).mp inferInstance

/-- **The unit of the gluing adjunction is an isomorphism.** -/
theorem gluingAdjunction_unit_isIso {X X' Y : Scheme.{u}}
    (i : X ⟶ X') (f : X ⟶ Y)
    (hi : IsThickening i) [IsAffineHom f] [HasPushout i f] :
    IsIso (gluingAdjunction i f hi).unit :=
  (NatTrans.isIso_iff_isIso_app _).mpr (gluingAdjunction_unit_app_isIso i f hi)

/-- **Stacks Project, Tag 07RV, the last assertion.**  The composition of
gluing with base change is isomorphic to the identity functor: a compatible pair `(V, U', φ)` is
recovered from the glued scheme `V ⨿_{V ×_Y X} U'` by base change along `Y ⟶ Y'` and
`X' ⟶ Y'`.

The isomorphism is the unit of `Stacks.Pushout.gluingAdjunction`, which is exactly the
comparison map of the source. -/
@[stacks 07RV "the composition F ∘ G is isomorphic to the identity functor"]
noncomputable def gluingCompBaseChangeIsoId {X X' Y : Scheme.{u}}
    (i : X ⟶ X') (f : X ⟶ Y)
    (hi : IsThickening i) [IsAffineHom f] :
    letI := hasPushout_of_isThickening i f hi
    gluingFunctor i f hi ⋙ baseChangeFunctor i f hi ≅ 𝟭 (gluingData i f) :=
  letI := hasPushout_of_isThickening i f hi
  letI := gluingAdjunction_unit_isIso i f hi
  (asIso (gluingAdjunction i f hi).unit).symm

end Stacks.Pushout

end
