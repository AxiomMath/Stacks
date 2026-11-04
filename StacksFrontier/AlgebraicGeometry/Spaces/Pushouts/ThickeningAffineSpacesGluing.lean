module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomFpqcLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineSpacesSupplement
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.CategoryTheory.Comma.IsoComma

/-!
# Gluing algebraic spaces across a pushout along a thickening

Let `i : X ⟶ X'` be a thickening of algebraic spaces over `S`, let `f : X ⟶ Y` be an affine
morphism and let `Y' = Y ⨿_X X'` be the pushout.  Base change along `Y ⟶ Y'` and `X' ⟶ Y'`
sends an algebraic space `V'` over `Y'` to the triple `(V' ×_{Y'} Y, V' ×_{Y'} X', 1)`, an
object of the `2`-fibre product of the categories of algebraic spaces over `Y` and over `X'`
above the category of algebraic spaces over `X`.  [Stacks Project, Tag 07VY] says that this
functor has a left adjoint, which sends a triple `(V, U', φ)` to the pushout
`V ⨿_{V ×_Y X} U'`.

## The categorical core

Nothing in the construction of the two functors or of the adjunction between them uses that
`Y'` is the pushout of the span: only that the square `i ≫ (X' ⟶ Y') = f ≫ (Y ⟶ Y')` commutes,
that the ambient category has fibre products, and that the pushout `V ⨿_U U'` of each triple
exists.  The first half of this file therefore carries out the whole construction in an
arbitrary category with pullbacks, in `CategoryTheory.PushoutGluing`, and the second half
instantiates it at algebraic spaces over `S`.

`Stacks.Pushout.baseChangeFunctor`, `Stacks.Pushout.gluingFunctor` and
`Stacks.Pushout.gluingAdjunction` are the scheme-level instance of the same construction, for
[Stacks Project, Tag 07RV].  They are *not* rewritten in terms of
`CategoryTheory.PushoutGluing` here: doing so would change the signatures of the existing Tag 07RV
registrations.  The genuinely
general plumbing lemmas that file already proves (`Stacks.Pushout.comp_hom_fst`,
`Stacks.Pushout.comp_inv_fst`, `Stacks.Pushout.pullback_congr_fst`,
`Stacks.Pushout.iterated_pullback_hom_ext` and `Stacks.Pushout.over_pullback_fst`) are reused
rather than restated; base change is compared with the projections through Mathlib's
`CategoryTheory.Limits.pullback.lift_fst` and `CategoryTheory.Limits.pullback.lift_snd`.

## Main definitions

* `CategoryTheory.PushoutGluing.GluingData`: compatible objects over the two legs of a span,
  as the iso-comma model of the `2`-fibre product of the two base-change functors.
* `CategoryTheory.PushoutGluing.baseChangeFunctor`: the functor `F`, base change to `Y` and to
  `X'` together with the canonical comparison of the two restrictions to `X`.
* `CategoryTheory.PushoutGluing.gluingFunctor`: the functor `G`, the objectwise pushout
  `V ⨿_{V ×_Y X} U'` with its structure morphism to `Y'`.
* `CategoryTheory.PushoutGluing.adjunction`: gluing is left adjoint to base change.
* `AlgebraicGeometry.Space.pushoutGluingData`,
  `AlgebraicGeometry.Space.pushoutBaseChangeFunctor`,
  `AlgebraicGeometry.Space.pushoutGluingFunctor` and
  `AlgebraicGeometry.Space.pushoutGluingAdjunction`: the same four things for algebraic spaces
  over `S`, which is [Stacks Project, Tag 07VY].

## Main results

* `AlgebraicGeometry.Space.isThickeningHom_of_isPullback`: a base change of a thickening of
  algebraic spaces over `S` is a thickening.  Together with
  `AlgebraicGeometry.Space.isAffineHom_hom_of_isPullback` this is what makes the span of each
  triple a thickening-and-affine span again, so that the pushout `V ⨿_U U'` is available.
* `AlgebraicGeometry.Space.pushoutGluingFunctor_obj_isPushout`: the glued algebraic space is
  the pushout of the two components of a triple along their identified restrictions to `X`.
* `AlgebraicGeometry.Space.exists_etaleChartCube_gluingData_of_isThickening_of_isAffineHom`:
  [Stacks Project, Tag 07W2], equation 81.6.5.2 of the proof of Tag 07W0 — the cube of étale
  charts of the span `U' ⟵ U ⟶ V` of a triple and of its pushout `G(V, U', φ)`, with its back
  and front squares pushouts, its four lateral squares cartesian and its four northeast arrows
  surjective étale.

## What is carried, and what is not

The space-level pushout `Y' = Y ⨿_X X'` is [Stacks Project, Tag 07VX], which is not available
unconditionally in this library:
`AlgebraicGeometry.Space.hasPushout_of_isThickening_of_isAffineHom` carries
`AlgebraicGeometry.Space.HasThickeningAffineAtlases` as an undischarged hypothesis.
That hypothesis is therefore carried, under the name `hatlas`, by every Tag 07VY declaration
below and by the Tag 07W2 declaration at the end of the file — it is another tag's result used
as an input, in the same way that
`AlgebraicGeometry.Space.smallEtalePullback_isEquivalence_of_isThickeningHom` carries the two
inputs of Stacks 05ZR.  Tag 07VY's own assertions — that `F` exists, that it has a left
adjoint, and that the left adjoint is the objectwise pushout — are proved, not assumed.

Two clauses of Tag 07VY are **not** covered here: that `F` carries `(Sch/Y')` into
`(Sch/Y) ×_{(Sch/X)} (Sch/X')` and that `G` carries that fibre product back into `(Sch/Y')`.
Both are statements about the representable objects, and neither is used by the three clauses
that are covered.

## References

* [Stacks Project, Tag 07VX](https://stacks.math.columbia.edu/tag/07VX)
* [Stacks Project, Tag 07VY](https://stacks.math.columbia.edu/tag/07VY)
* [Stacks Project, Tag 07RV](https://stacks.math.columbia.edu/tag/07RV)
* [Stacks Project, Tag 07W2](https://stacks.math.columbia.edu/tag/07W2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory.PushoutGluing

variable {C : Type u} [Category.{v} C] [HasPullbacks C]

/-- Compatible objects over the two legs of a span `X' ⟵ X ⟶ Y`: an object `V` over `Y`, an
object `U'` over `X'`, and an isomorphism `V ×_Y X ≅ U' ×_{X'} X`. -/
abbrev GluingData {X X' Y : C} (i : X ⟶ X') (f : X ⟶ Y) :=
  CategoryTheory.IsoComma (Over.pullback f) (Over.pullback i)

/-- The canonical comparison between the two ways of restricting an object over `Y'` to `X`,
for a commuting square `i ≫ a = f ≫ b`. -/
noncomputable def baseChangeComparison {X X' Y Y' : C} (i : X ⟶ X') (f : X ⟶ Y)
    {a : X' ⟶ Y'} {b : Y ⟶ Y'} (w : i ≫ a = f ≫ b) :
    Over.pullback b ⋙ Over.pullback f ≅ Over.pullback a ⋙ Over.pullback i :=
  (Over.pullbackComp f b).symm ≪≫
    eqToIso (congrArg (fun h : X ⟶ Y' ↦ Over.pullback h) w.symm) ≪≫ Over.pullbackComp i a

/-- Base change from objects over `Y'` to compatible objects over the two legs of the span.

This is `CategoryTheory.IsoComma.lift` of the two base-change functors along
`CategoryTheory.PushoutGluing.baseChangeComparison`, written out as the
`CategoryTheory.ObjectProperty.lift` it is: that one is `implicit_reducible` and carries
`@[simps]`, so the components of the resulting triple are visible to `dsimp` and to the keyed
matching of `rw`, which the proofs below need. -/
noncomputable def baseChangeFunctor {X X' Y Y' : C} (i : X ⟶ X') (f : X ⟶ Y)
    {a : X' ⟶ Y'} {b : Y ⟶ Y'} (w : i ≫ a = f ≫ b) :
    Over Y' ⥤ GluingData i f :=
  (show ObjectProperty (Comma (Over.pullback f) (Over.pullback i)) from fun T ↦ IsIso T.hom).lift
    { obj := fun Z ↦
        ⟨(Over.pullback b).obj Z, (Over.pullback a).obj Z,
          (baseChangeComparison i f w).hom.app Z⟩
      map := fun g ↦
        ⟨(Over.pullback b).map g, (Over.pullback a).map g,
          (baseChangeComparison i f w).hom.naturality g⟩
      map_id := by intro Z; ext <;> simp
      map_comp := by intro Z W Q g h; ext <;> simp }
    (fun Z ↦ inferInstance)

/-- The map from the common restriction `U` of a compatible pair, computed on the `X'`-side as
`U' ×_{X'} X`, to its `Y`-component `V`, using the comparison isomorphism. -/
noncomputable def sourceMap {X X' Y : C} (i : X ⟶ X') (f : X ⟶ Y) (T : GluingData i f) :
    pullback T.obj.right.hom i ⟶ T.obj.left.left := by
  letI : IsIso T.obj.hom := T.property
  exact (inv T.obj.hom).left ≫ pullback.fst T.obj.left.hom f

/-- The common restriction `U` of a compatible pair is the fibre product `X ×_Y V`: the square
with sides `U ⟶ V`, `U ⟶ X`, `V ⟶ Y` and `X ⟶ Y` is cartesian. -/
theorem sourceMap_isPullback {X X' Y : C} (i : X ⟶ X') (f : X ⟶ Y) (T : GluingData i f) :
    IsPullback (sourceMap i f T) (pullback.snd T.obj.right.hom i) T.obj.left.hom f := by
  have : IsIso T.obj.hom := T.property
  let e := (Over.forget X).mapIso (asIso T.obj.hom).symm
  have hs : e.hom ≫ pullback.snd T.obj.left.hom f =
      pullback.snd T.obj.right.hom i := (inv T.obj.hom).w
  apply IsPullback.of_iso_pullback _ e rfl hs
  constructor
  show (e.hom ≫ pullback.fst T.obj.left.hom f) ≫ T.obj.left.hom = _
  rw [Category.assoc, pullback.condition, ← Category.assoc, hs]

/-- The object glued from a compatible pair `(V, U', φ)`: the pushout `V ⨿_U U'`, where
`U = V ×_Y X` is identified with `U' ×_{X'} X` by `φ`, with the structure morphism to `Y'`
induced by `V ⟶ Y` and `U' ⟶ X'`. -/
noncomputable abbrev gluedObj {X X' Y Y' : C} (i : X ⟶ X') (f : X ⟶ Y)
    {a : X' ⟶ Y'} {b : Y ⟶ Y'} (w : i ≫ a = f ≫ b) (T : GluingData i f)
    [HasPushout (pullback.fst T.obj.right.hom i) (sourceMap i f T)] :
    Over Y' := by
  letI : IsIso T.obj.hom := T.property
  have hcmp' :
      (inv T.obj.hom).left ≫ pullback.snd T.obj.left.hom f =
        pullback.snd T.obj.right.hom i := by
    simpa only [Over.pullback_obj_hom] using (inv T.obj.hom).w
  have key : sourceMap i f T ≫ T.obj.left.hom = pullback.snd T.obj.right.hom i ≫ f := by
    change ((inv T.obj.hom).left ≫ pullback.fst T.obj.left.hom f) ≫ T.obj.left.hom = _
    rw [Category.assoc, pullback.condition, ← Category.assoc, hcmp']
  have hcommon :
      pullback.fst T.obj.right.hom i ≫ T.obj.right.hom ≫ a =
        sourceMap i f T ≫ T.obj.left.hom ≫ b := by
    rw [reassoc_of% key, ← w, pullback.condition_assoc]
  exact Over.mk (pushout.desc (T.obj.right.hom ≫ a) (T.obj.left.hom ≫ b) hcommon)

/-- On `U'` the structure morphism of the glued object is the given morphism `U' ⟶ X'` followed
by `X' ⟶ Y'`. -/
theorem gluedObj_inl {X X' Y Y' : C} (i : X ⟶ X') (f : X ⟶ Y)
    {a : X' ⟶ Y'} {b : Y ⟶ Y'} (w : i ≫ a = f ≫ b) (T : GluingData i f)
    [HasPushout (pullback.fst T.obj.right.hom i) (sourceMap i f T)] :
    pushout.inl (pullback.fst T.obj.right.hom i) (sourceMap i f T) ≫
        (gluedObj i f w T).hom = T.obj.right.hom ≫ a := by
  dsimp [gluedObj]
  simp [pushout.inl_desc]

/-- On `V` the structure morphism of the glued object is the given morphism `V ⟶ Y` followed by
`Y ⟶ Y'`. -/
theorem gluedObj_inr {X X' Y Y' : C} (i : X ⟶ X') (f : X ⟶ Y)
    {a : X' ⟶ Y'} {b : Y ⟶ Y'} (w : i ≫ a = f ≫ b) (T : GluingData i f)
    [HasPushout (pullback.fst T.obj.right.hom i) (sourceMap i f T)] :
    pushout.inr (pullback.fst T.obj.right.hom i) (sourceMap i f T) ≫
        (gluedObj i f w T).hom = T.obj.left.hom ≫ b := by
  dsimp [gluedObj]
  simp [pushout.inr_desc]

/-- The morphism of glued objects induced by a morphism of compatible pairs, by the universal
property of the pushout. -/
noncomputable def gluedMap {X X' Y Y' : C} (i : X ⟶ X') (f : X ⟶ Y)
    {a : X' ⟶ Y'} {b : Y ⟶ Y'} (w : i ≫ a = f ≫ b) {T S : GluingData i f}
    [HasPushout (pullback.fst T.obj.right.hom i) (sourceMap i f T)]
    [HasPushout (pullback.fst S.obj.right.hom i) (sourceMap i f S)]
    (g : T ⟶ S) :
    gluedObj i f w T ⟶ gluedObj i f w S := by
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
  have hw : l ≫ S.obj.hom.left = T.obj.hom.left ≫ k := congrArg (·.left) g.hom.w
  have hSinv : S.obj.hom.left ≫ (inv S.obj.hom).left = 𝟙 _ :=
    congrArg Over.Hom.left (IsIso.hom_inv_id S.obj.hom)
  have hTinv : (inv T.obj.hom).left ≫ T.obj.hom.left = 𝟙 _ :=
    congrArg Over.Hom.left (IsIso.inv_hom_id T.obj.hom)
  have htransport : (inv T.obj.hom).left ≫ l = k ≫ (inv S.obj.hom).left := by
    rw [← Category.comp_id l, ← hSinv, reassoc_of% hw, reassoc_of% hTinv]
  have hsource : k ≫ sourceMap i f S = sourceMap i f T ≫ g.hom.left.left := by
    change k ≫ (inv S.obj.hom).left ≫ pullback.fst S.obj.left.hom f =
      ((inv T.obj.hom).left ≫ pullback.fst T.obj.left.hom f) ≫ g.hom.left.left
    rw [← reassoc_of% htransport, Category.assoc, hl₁]
  have hcommon' : pullback.fst T.obj.right.hom i ≫
      (g.hom.right.left ≫ pushout.inl (pullback.fst S.obj.right.hom i)
        (sourceMap i f S)) = sourceMap i f T ≫
      (g.hom.left.left ≫ pushout.inr (pullback.fst S.obj.right.hom i)
        (sourceMap i f S)) := by
    rw [← reassoc_of% hk₁, pushout.condition, reassoc_of% hsource]
  refine Over.homMk (pushout.desc
    (g.hom.right.left ≫ pushout.inl (pullback.fst S.obj.right.hom i) (sourceMap i f S))
    (g.hom.left.left ≫ pushout.inr (pullback.fst S.obj.right.hom i) (sourceMap i f S))
    hcommon') ?_
  apply pushout.hom_ext
  · rw [← Category.assoc, pushout.inl_desc, Category.assoc, gluedObj_inl i f w S,
      ← Category.assoc, g.hom.right.w, ← gluedObj_inl i f w T]
  · rw [← Category.assoc, pushout.inr_desc, Category.assoc, gluedObj_inr i f w S,
      ← Category.assoc, g.hom.left.w, ← gluedObj_inr i f w T]

/-- On `U'` the glued morphism is the `U'`-component of the morphism of compatible pairs. -/
@[reassoc] theorem gluedMap_inl {X X' Y Y' : C} (i : X ⟶ X') (f : X ⟶ Y)
    {a : X' ⟶ Y'} {b : Y ⟶ Y'} (w : i ≫ a = f ≫ b) {T S : GluingData i f}
    [HasPushout (pullback.fst T.obj.right.hom i) (sourceMap i f T)]
    [HasPushout (pullback.fst S.obj.right.hom i) (sourceMap i f S)]
    (g : T ⟶ S) :
    pushout.inl (pullback.fst T.obj.right.hom i) (sourceMap i f T) ≫
        (gluedMap i f w g).left =
      g.hom.right.left ≫
        pushout.inl (pullback.fst S.obj.right.hom i) (sourceMap i f S) :=
  pushout.inl_desc _ _ _

/-- On `V` the glued morphism is the `V`-component of the morphism of compatible pairs. -/
@[reassoc] theorem gluedMap_inr {X X' Y Y' : C} (i : X ⟶ X') (f : X ⟶ Y)
    {a : X' ⟶ Y'} {b : Y ⟶ Y'} (w : i ≫ a = f ≫ b) {T S : GluingData i f}
    [HasPushout (pullback.fst T.obj.right.hom i) (sourceMap i f T)]
    [HasPushout (pullback.fst S.obj.right.hom i) (sourceMap i f S)]
    (g : T ⟶ S) :
    pushout.inr (pullback.fst T.obj.right.hom i) (sourceMap i f T) ≫
        (gluedMap i f w g).left =
      g.hom.left.left ≫
        pushout.inr (pullback.fst S.obj.right.hom i) (sourceMap i f S) :=
  pushout.inr_desc _ _ _

/-- Gluing compatible objects over `Y` and over `X'` to an object over `Y'`.  Its objectwise
pushout property is `CategoryTheory.PushoutGluing.gluingFunctor_obj_isPushout`. -/
noncomputable def gluingFunctor {X X' Y Y' : C} (i : X ⟶ X') (f : X ⟶ Y)
    {a : X' ⟶ Y'} {b : Y ⟶ Y'} (w : i ≫ a = f ≫ b)
    (hpo : ∀ T : GluingData i f,
      HasPushout (pullback.fst T.obj.right.hom i) (sourceMap i f T)) :
    GluingData i f ⥤ Over Y' where
  obj T := by
    letI := hpo T
    exact gluedObj i f w T
  map {T S} g := by
    letI := hpo T
    letI := hpo S
    exact gluedMap i f w g
  map_id := by
    intro T
    let := hpo T
    apply Over.OverMorphism.ext
    apply pushout.hom_ext
    · simp [gluedMap_inl]
    · simp [gluedMap_inr]
  map_comp := by
    intro T S R g h
    let := hpo T
    let := hpo S
    let := hpo R
    apply Over.OverMorphism.ext
    apply pushout.hom_ext
    · rw [gluedMap_inl, show (gluedMap i f w g ≫ gluedMap i f w h).left =
        (gluedMap i f w g).left ≫ (gluedMap i f w h).left from rfl,
        ← Category.assoc, gluedMap_inl, Category.assoc, gluedMap_inl,
        show (g ≫ h).hom.right.left = g.hom.right.left ≫ h.hom.right.left from rfl,
        Category.assoc]
    · rw [gluedMap_inr, show (gluedMap i f w g ≫ gluedMap i f w h).left =
        (gluedMap i f w g).left ≫ (gluedMap i f w h).left from rfl,
        ← Category.assoc, gluedMap_inr, Category.assoc, gluedMap_inr,
        show (g ≫ h).hom.left.left = g.hom.left.left ≫ h.hom.left.left from rfl,
        Category.assoc]

/-- The glued object is the pushout of the two components of a compatible pair along their
identified restrictions to `X`, with the induced map to `Y'`. -/
theorem gluingFunctor_obj_isPushout {X X' Y Y' : C} (i : X ⟶ X') (f : X ⟶ Y)
    {a : X' ⟶ Y'} {b : Y ⟶ Y'} (w : i ≫ a = f ≫ b)
    (hpo : ∀ T : GluingData i f,
      HasPushout (pullback.fst T.obj.right.hom i) (sourceMap i f T))
    (T : GluingData i f) :
    ∃ (v : T.obj.left.left ⟶ ((gluingFunctor i f w hpo).obj T).left)
      (u' : T.obj.right.left ⟶ ((gluingFunctor i f w hpo).obj T).left),
      IsPushout (sourceMap i f T) (pullback.fst T.obj.right.hom i) v u' ∧
      v ≫ ((gluingFunctor i f w hpo).obj T).hom = T.obj.left.hom ≫ b ∧
      u' ≫ ((gluingFunctor i f w hpo).obj T).hom = T.obj.right.hom ≫ a := by
  let := hpo T
  exact ⟨pushout.inr (pullback.fst T.obj.right.hom i) (sourceMap i f T),
    pushout.inl (pullback.fst T.obj.right.hom i) (sourceMap i f T),
    (IsPushout.of_hasPushout _ _).flip, gluedObj_inr i f w T, gluedObj_inl i f w T⟩

attribute [local simp] pullback.lift_fst pullback.lift_snd pushout.inl_desc pushout.inr_desc
  Over.homMk_left

/-- The comparison isomorphism of the base-change functor is compatible with the projections to
`Z`: the two ways of restricting `Z` to `X` have the same projection to `Z`. -/
theorem baseChangeComparison_fst {X X' Y Y' : C} (i : X ⟶ X') (f : X ⟶ Y)
    {a : X' ⟶ Y'} {b : Y ⟶ Y'} (w : i ≫ a = f ≫ b) (Z : Over Y') :
    ((baseChangeComparison i f w).hom.app Z).left ≫
        pullback.fst (pullback.snd Z.hom a) i ≫ pullback.fst Z.hom a =
      pullback.fst (pullback.snd Z.hom b) f ≫ pullback.fst Z.hom b := by
  dsimp only [baseChangeComparison, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Over.comp_left, eqToIso.hom]
  simp only [Category.assoc, Stacks.Pushout.comp_hom_fst]
  rw [Stacks.Pushout.pullback_congr_fst w.symm Z, Stacks.Pushout.comp_inv_fst]

/-- Precomposing the comparison isomorphism of a compatible pair with `sourceMap` gives the
projection from the `V`-side. -/
private theorem hom_left_comp_sourceMap {X X' Y : C} (i : X ⟶ X') (f : X ⟶ Y)
    (T : GluingData i f) :
    T.obj.hom.left ≫ sourceMap i f T = pullback.fst T.obj.left.hom f := by
  have : IsIso T.obj.hom := T.property
  change T.obj.hom.left ≫ (inv T.obj.hom).left ≫ _ = _
  rw [← Category.assoc, ← Over.comp_left, IsIso.hom_inv_id]
  simp

/-- The compatibility square of a morphism of compatible pairs into a base change, tested on the
projections to `Z`, says that the two morphisms to `Z` agree on the common restriction `U`. -/
private theorem comparison_fst_iff {X X' Y Y' : C} (i : X ⟶ X') (f : X ⟶ Y)
    {a : X' ⟶ Y'} {b : Y ⟶ Y'} (w : i ≫ a = f ≫ b) (T : GluingData i f) {Z : Over Y'}
    (l : T.obj.left ⟶ (Over.pullback b).obj Z) (r : T.obj.right ⟶ (Over.pullback a).obj Z) :
    sourceMap i f T ≫ l.left ≫ pullback.fst Z.hom b =
        pullback.fst T.obj.right.hom i ≫ r.left ≫ pullback.fst Z.hom a ↔
      ((Over.pullback f).map l ≫ (baseChangeComparison i f w).hom.app Z).left ≫
          pullback.fst (pullback.snd Z.hom a) i ≫ pullback.fst Z.hom a =
        (T.obj.hom ≫ (Over.pullback i).map r).left ≫
          pullback.fst (pullback.snd Z.hom a) i ≫ pullback.fst Z.hom a := by
  have : IsIso T.obj.hom := T.property
  have : IsIso T.obj.hom.left := inferInstanceAs (IsIso ((Over.forget _).map T.obj.hom))
  rw [← cancel_epi T.obj.hom.left, ← Category.assoc, ← Category.assoc,
    hom_left_comp_sourceMap]
  simp [baseChangeComparison_fst, pullback.lift_fst_assoc]

/-- A morphism of compatible pairs from `(V, U', φ)` into the base change of an object `Z` over
`Y'`, built from a morphism `V ⟶ Z` and a morphism `U' ⟶ Z` over `Y ⟶ Y'` and `X' ⟶ Y'` which
agree on `U`. -/
noncomputable def compatiblePairHom {X X' Y Y' : C} (i : X ⟶ X') (f : X ⟶ Y)
    {a : X' ⟶ Y'} {b : Y ⟶ Y'} (w : i ≫ a = f ≫ b)
    (T : GluingData i f) (Z : Over Y')
    (u : T.obj.left.left ⟶ Z.left) (v : T.obj.right.left ⟶ Z.left)
    (hu : u ≫ Z.hom = T.obj.left.hom ≫ b)
    (hv : v ≫ Z.hom = T.obj.right.hom ≫ a)
    (huv : sourceMap i f T ≫ u = pullback.fst T.obj.right.hom i ≫ v) :
    T ⟶ (baseChangeFunctor i f w).obj Z := by
  dsimp [baseChangeFunctor]
  letI : IsIso T.obj.hom := T.property
  let l : T.obj.left ⟶ (Over.pullback b).obj Z :=
    Over.homMk (pullback.lift u T.obj.left.hom hu) (pullback.lift_snd _ _ _)
  let r : T.obj.right ⟶ (Over.pullback a).obj Z :=
    Over.homMk (pullback.lift v T.obj.right.hom hv) (pullback.lift_snd _ _ _)
  refine ObjectProperty.homMk { left := l, right := r, w := ?_ }
  apply Over.OverMorphism.ext
  apply Stacks.Pushout.iterated_pullback_hom_ext i a Z
  · dsimp only [Over.comp_left]
    change (((Over.pullback f).map l).left ≫
        ((baseChangeComparison i f w).hom.app Z).left) ≫ _ = _
    simp only [Category.assoc]
    rw [baseChangeComparison_fst]
    rw [show ((Over.pullback f).map l).left ≫
          pullback.fst (pullback.snd Z.hom b) f ≫
            pullback.fst Z.hom b = _ from
          (pullback.lift_fst_assoc _ _ _ _).trans (Category.assoc _ _ _),
      show ((Over.pullback i).map r).left ≫
          pullback.fst (pullback.snd Z.hom a) i ≫
            pullback.fst Z.hom a = _ from
          (pullback.lift_fst_assoc _ _ _ _).trans (Category.assoc _ _ _)]
    have hl : l.left ≫ pullback.fst Z.hom b = u := pullback.lift_fst _ _ _
    have hr : r.left ≫ pullback.fst Z.hom a = v := pullback.lift_fst _ _ _
    rw [hl, hr]
    have hid : T.obj.hom.left ≫ (inv T.obj.hom).left = 𝟙 _ :=
      congrArg Over.Hom.left (IsIso.hom_inv_id T.obj.hom)
    have hgs : sourceMap i f T = (inv T.obj.hom).left ≫ pullback.fst T.obj.left.hom f := rfl
    rw [← huv, hgs]
    simp only [Category.assoc]
    rw [← Category.assoc, hid, Category.id_comp]
  · change ((Over.pullback f).map _ ≫ ((baseChangeComparison i f w).hom.app Z)).left ≫
        ((Over.pullback i).obj ((Over.pullback a).obj Z)).hom =
      (T.obj.hom ≫ (Over.pullback i).map _).left ≫
        ((Over.pullback i).obj ((Over.pullback a).obj Z)).hom
    exact (Over.w _).trans (Over.w _).symm

/-- The `V`-component of `CategoryTheory.PushoutGluing.compatiblePairHom` is the morphism into
the fibre product `Z ×_{Y'} Y` determined by the given morphism `V ⟶ Z`. -/
@[simp] theorem compatiblePairHom_hom_left_left {X X' Y Y' : C} (i : X ⟶ X') (f : X ⟶ Y)
    {a : X' ⟶ Y'} {b : Y ⟶ Y'} (w : i ≫ a = f ≫ b)
    (T : GluingData i f) (Z : Over Y')
    (u : T.obj.left.left ⟶ Z.left) (v : T.obj.right.left ⟶ Z.left)
    (hu : u ≫ Z.hom = T.obj.left.hom ≫ b)
    (hv : v ≫ Z.hom = T.obj.right.hom ≫ a)
    (huv : sourceMap i f T ≫ u = pullback.fst T.obj.right.hom i ≫ v) :
    (compatiblePairHom i f w T Z u v hu hv huv).hom.left.left =
      pullback.lift u T.obj.left.hom hu :=
  rfl

/-- The `U'`-component of `CategoryTheory.PushoutGluing.compatiblePairHom` is the morphism into
the fibre product `Z ×_{Y'} X'` determined by the given morphism `U' ⟶ Z`. -/
@[simp] theorem compatiblePairHom_hom_right_left {X X' Y Y' : C} (i : X ⟶ X') (f : X ⟶ Y)
    {a : X' ⟶ Y'} {b : Y ⟶ Y'} (w : i ≫ a = f ≫ b)
    (T : GluingData i f) (Z : Over Y')
    (u : T.obj.left.left ⟶ Z.left) (v : T.obj.right.left ⟶ Z.left)
    (hu : u ≫ Z.hom = T.obj.left.hom ≫ b)
    (hv : v ≫ Z.hom = T.obj.right.hom ≫ a)
    (huv : sourceMap i f T ≫ u = pullback.fst T.obj.right.hom i ≫ v) :
    (compatiblePairHom i f w T Z u v hu hv huv).hom.right.left =
      pullback.lift v T.obj.right.hom hv :=
  rfl

/-- The two morphisms to `Z` cut out on `V` and on `U'` by a morphism of compatible pairs into
the base change of `Z` agree on the common restriction `U`. -/
theorem compatiblePairHom_agree {X X' Y Y' : C} (i : X ⟶ X') (f : X ⟶ Y)
    {a : X' ⟶ Y'} {b : Y ⟶ Y'} (w : i ≫ a = f ≫ b)
    {T : GluingData i f} {Z : Over Y'} (h : T ⟶ (baseChangeFunctor i f w).obj Z) :
    sourceMap i f T ≫ h.hom.left.left ≫ pullback.fst Z.hom b =
      pullback.fst T.obj.right.hom i ≫ h.hom.right.left ≫ pullback.fst Z.hom a := by
  dsimp [baseChangeFunctor] at h
  exact (comparison_fst_iff i f w T h.hom.left h.hom.right).2
    (congrArg (fun k => k.left ≫ pullback.fst (pullback.snd Z.hom a) i ≫ pullback.fst Z.hom a)
      h.hom.w)

/-- The half of the hom-set bijection that turns a morphism out of the glued object into a
morphism of compatible pairs, by restricting along the two inclusions into the pushout. -/
noncomputable def gluingToPair {X X' Y Y' : C} (i : X ⟶ X') (f : X ⟶ Y)
    {a : X' ⟶ Y'} {b : Y ⟶ Y'} (w : i ≫ a = f ≫ b)
    (hpo : ∀ T : GluingData i f,
      HasPushout (pullback.fst T.obj.right.hom i) (sourceMap i f T))
    {T : GluingData i f} {Z : Over Y'} (k : (gluingFunctor i f w hpo).obj T ⟶ Z) :
    T ⟶ (baseChangeFunctor i f w).obj Z := by
  letI := hpo T
  let kl : pushout (pullback.fst T.obj.right.hom i) (sourceMap i f T) ⟶ Z.left := k.left
  have hkl : kl ≫ Z.hom = (gluedObj i f w T).hom := k.w
  refine compatiblePairHom i f w T Z
    (pushout.inr _ _ ≫ kl) (pushout.inl _ _ ≫ kl) ?_ ?_ ?_
  · rw [Category.assoc, hkl]
    exact gluedObj_inr i f w T
  · rw [Category.assoc, hkl]
    exact gluedObj_inl i f w T
  · simp only [← Category.assoc, pushout.condition]

/-- The half of the hom-set bijection that turns a morphism of compatible pairs into a morphism
out of the glued object, by the universal property of the pushout. -/
noncomputable def gluingFromPair {X X' Y Y' : C} (i : X ⟶ X') (f : X ⟶ Y)
    {a : X' ⟶ Y'} {b : Y ⟶ Y'} (w : i ≫ a = f ≫ b)
    (hpo : ∀ T : GluingData i f,
      HasPushout (pullback.fst T.obj.right.hom i) (sourceMap i f T))
    {T : GluingData i f} {Z : Over Y'} (h : T ⟶ (baseChangeFunctor i f w).obj Z) :
    (gluingFunctor i f w hpo).obj T ⟶ Z := by
  letI := hpo T
  let hr : T.obj.right.left ⟶ pullback Z.hom a := h.hom.right.left
  let hl : T.obj.left.left ⟶ pullback Z.hom b := h.hom.left.left
  have hcompat : pullback.fst T.obj.right.hom i ≫ hr ≫ pullback.fst Z.hom a =
      sourceMap i f T ≫ hl ≫ pullback.fst Z.hom b :=
    (compatiblePairHom_agree i f w h).symm
  have hwd : pushout.desc (hr ≫ pullback.fst Z.hom a) (hl ≫ pullback.fst Z.hom b) hcompat ≫
      Z.hom = (gluedObj i f w T).hom := by
    apply pushout.hom_ext
    · rw [pushout.inl_desc_assoc, gluedObj_inl i f w T]
      exact Stacks.Pushout.over_pullback_fst a h.hom.right
    · rw [pushout.inr_desc_assoc, gluedObj_inr i f w T]
      exact Stacks.Pushout.over_pullback_fst b h.hom.left
  exact Over.homMk _ hwd

/-- The `V`-component of `CategoryTheory.PushoutGluing.gluingToPair`, followed by the projection
to `Z`, is the restriction of the given morphism to `V`. -/
@[simp] theorem gluingToPair_left_comp_fst {X X' Y Y' : C} (i : X ⟶ X') (f : X ⟶ Y)
    {a : X' ⟶ Y'} {b : Y ⟶ Y'} (w : i ≫ a = f ≫ b)
    (hpo : ∀ T : GluingData i f,
      HasPushout (pullback.fst T.obj.right.hom i) (sourceMap i f T))
    {T : GluingData i f} {Z : Over Y'} (k : (gluingFunctor i f w hpo).obj T ⟶ Z) :
    (gluingToPair i f w hpo k).hom.left.left ≫ pullback.fst Z.hom b =
      pushout.inr (pullback.fst T.obj.right.hom i) (sourceMap i f T) ≫ k.left :=
  pullback.lift_fst _ _ _

/-- The `U'`-component of `CategoryTheory.PushoutGluing.gluingToPair`, followed by the
projection to `Z`, is the restriction of the given morphism to `U'`. -/
@[simp] theorem gluingToPair_right_comp_fst {X X' Y Y' : C} (i : X ⟶ X') (f : X ⟶ Y)
    {a : X' ⟶ Y'} {b : Y ⟶ Y'} (w : i ≫ a = f ≫ b)
    (hpo : ∀ T : GluingData i f,
      HasPushout (pullback.fst T.obj.right.hom i) (sourceMap i f T))
    {T : GluingData i f} {Z : Over Y'} (k : (gluingFunctor i f w hpo).obj T ⟶ Z) :
    (gluingToPair i f w hpo k).hom.right.left ≫ pullback.fst Z.hom a =
      pushout.inl (pullback.fst T.obj.right.hom i) (sourceMap i f T) ≫ k.left :=
  pullback.lift_fst _ _ _

/-- The reassociated form of `CategoryTheory.PushoutGluing.gluingToPair_left_comp_fst`. -/
@[simp] theorem gluingToPair_left_comp_fst_assoc {X X' Y Y' W : C} (i : X ⟶ X') (f : X ⟶ Y)
    {a : X' ⟶ Y'} {b : Y ⟶ Y'} (w : i ≫ a = f ≫ b)
    (hpo : ∀ T : GluingData i f,
      HasPushout (pullback.fst T.obj.right.hom i) (sourceMap i f T))
    {T : GluingData i f} {Z : Over Y'} (k : (gluingFunctor i f w hpo).obj T ⟶ Z)
    (x : Z.left ⟶ W) :
    (gluingToPair i f w hpo k).hom.left.left ≫ pullback.fst Z.hom b ≫ x =
      pushout.inr (pullback.fst T.obj.right.hom i) (sourceMap i f T) ≫ k.left ≫ x :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun m => m ≫ x) (gluingToPair_left_comp_fst i f w hpo k)).trans
      (Category.assoc _ _ _))

/-- The reassociated form of `CategoryTheory.PushoutGluing.gluingToPair_right_comp_fst`. -/
@[simp] theorem gluingToPair_right_comp_fst_assoc {X X' Y Y' W : C} (i : X ⟶ X') (f : X ⟶ Y)
    {a : X' ⟶ Y'} {b : Y ⟶ Y'} (w : i ≫ a = f ≫ b)
    (hpo : ∀ T : GluingData i f,
      HasPushout (pullback.fst T.obj.right.hom i) (sourceMap i f T))
    {T : GluingData i f} {Z : Over Y'} (k : (gluingFunctor i f w hpo).obj T ⟶ Z)
    (x : Z.left ⟶ W) :
    (gluingToPair i f w hpo k).hom.right.left ≫ pullback.fst Z.hom a ≫ x =
      pushout.inl (pullback.fst T.obj.right.hom i) (sourceMap i f T) ≫ k.left ≫ x :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun m => m ≫ x) (gluingToPair_right_comp_fst i f w hpo k)).trans
      (Category.assoc _ _ _))

/-- The `V`-component of `CategoryTheory.PushoutGluing.gluingToPair`, followed by the projection
to `Y`, is the structure morphism of `V`. -/
@[simp] theorem gluingToPair_left_comp_snd {X X' Y Y' : C} (i : X ⟶ X') (f : X ⟶ Y)
    {a : X' ⟶ Y'} {b : Y ⟶ Y'} (w : i ≫ a = f ≫ b)
    (hpo : ∀ T : GluingData i f,
      HasPushout (pullback.fst T.obj.right.hom i) (sourceMap i f T))
    {T : GluingData i f} {Z : Over Y'} (k : (gluingFunctor i f w hpo).obj T ⟶ Z) :
    (gluingToPair i f w hpo k).hom.left.left ≫ pullback.snd Z.hom b = T.obj.left.hom :=
  pullback.lift_snd _ _ _

/-- The `U'`-component of `CategoryTheory.PushoutGluing.gluingToPair`, followed by the
projection to `X'`, is the structure morphism of `U'`. -/
@[simp] theorem gluingToPair_right_comp_snd {X X' Y Y' : C} (i : X ⟶ X') (f : X ⟶ Y)
    {a : X' ⟶ Y'} {b : Y ⟶ Y'} (w : i ≫ a = f ≫ b)
    (hpo : ∀ T : GluingData i f,
      HasPushout (pullback.fst T.obj.right.hom i) (sourceMap i f T))
    {T : GluingData i f} {Z : Over Y'} (k : (gluingFunctor i f w hpo).obj T ⟶ Z) :
    (gluingToPair i f w hpo k).hom.right.left ≫ pullback.snd Z.hom a = T.obj.right.hom :=
  pullback.lift_snd _ _ _

/-- On `U'` the glued morphism of `CategoryTheory.PushoutGluing.gluingFromPair` is the
`U'`-component of the given morphism of compatible pairs, followed by the projection to `Z`. -/
@[simp] theorem inl_comp_gluingFromPair {X X' Y Y' : C} (i : X ⟶ X') (f : X ⟶ Y)
    {a : X' ⟶ Y'} {b : Y ⟶ Y'} (w : i ≫ a = f ≫ b)
    (hpo : ∀ T : GluingData i f,
      HasPushout (pullback.fst T.obj.right.hom i) (sourceMap i f T))
    {T : GluingData i f} {Z : Over Y'} (h : T ⟶ (baseChangeFunctor i f w).obj Z) :
    pushout.inl (pullback.fst T.obj.right.hom i) (sourceMap i f T) ≫
        (gluingFromPair i f w hpo h).left =
      h.hom.right.left ≫ pullback.fst Z.hom a :=
  pushout.inl_desc _ _ _

/-- On `V` the glued morphism of `CategoryTheory.PushoutGluing.gluingFromPair` is the
`V`-component of the given morphism of compatible pairs, followed by the projection to `Z`. -/
@[simp] theorem inr_comp_gluingFromPair {X X' Y Y' : C} (i : X ⟶ X') (f : X ⟶ Y)
    {a : X' ⟶ Y'} {b : Y ⟶ Y'} (w : i ≫ a = f ≫ b)
    (hpo : ∀ T : GluingData i f,
      HasPushout (pullback.fst T.obj.right.hom i) (sourceMap i f T))
    {T : GluingData i f} {Z : Over Y'} (h : T ⟶ (baseChangeFunctor i f w).obj Z) :
    pushout.inr (pullback.fst T.obj.right.hom i) (sourceMap i f T) ≫
        (gluingFromPair i f w hpo h).left =
      h.hom.left.left ≫ pullback.fst Z.hom b :=
  pushout.inr_desc _ _ _

/-- The hom-set bijection: morphisms from the glued object `V ⨿_U U'` to an object `Z` over `Y'`
are the same thing as morphisms of compatible pairs from `(V, U', φ)` to the base change
of `Z`. -/
noncomputable def homEquiv {X X' Y Y' : C} (i : X ⟶ X') (f : X ⟶ Y)
    {a : X' ⟶ Y'} {b : Y ⟶ Y'} (w : i ≫ a = f ≫ b)
    (hpo : ∀ T : GluingData i f,
      HasPushout (pullback.fst T.obj.right.hom i) (sourceMap i f T))
    (T : GluingData i f) (Z : Over Y') :
    ((gluingFunctor i f w hpo).obj T ⟶ Z) ≃ (T ⟶ (baseChangeFunctor i f w).obj Z) where
  toFun := gluingToPair i f w hpo
  invFun := gluingFromPair i f w hpo
  left_inv k := by
    let := hpo T
    apply Over.OverMorphism.ext
    refine pushout.hom_ext ?_ ?_
    · exact (inl_comp_gluingFromPair i f w hpo (gluingToPair i f w hpo k)).trans
        (gluingToPair_right_comp_fst i f w hpo k)
    · exact (inr_comp_gluingFromPair i f w hpo (gluingToPair i f w hpo k)).trans
        (gluingToPair_left_comp_fst i f w hpo k)
  right_inv h := by
    let := hpo T
    apply ObjectProperty.hom_ext
    apply Comma.hom_ext
    · apply Over.OverMorphism.ext
      refine pullback.hom_ext ?_ ?_
      · exact (gluingToPair_left_comp_fst i f w hpo (gluingFromPair i f w hpo h)).trans
          (inr_comp_gluingFromPair i f w hpo h)
      · change _ = h.hom.left.left ≫ ((Over.pullback b).obj Z).hom
        exact (Over.w _).trans (Over.w _).symm
    · apply Over.OverMorphism.ext
      refine pullback.hom_ext ?_ ?_
      · exact (gluingToPair_right_comp_fst i f w hpo (gluingFromPair i f w hpo h)).trans
          (inl_comp_gluingFromPair i f w hpo h)
      · change _ = h.hom.right.left ≫ ((Over.pullback a).obj Z).hom
        exact (Over.w _).trans (Over.w _).symm

/-- **Gluing is left adjoint to base change.**  A morphism from the glued object `V ⨿_U U'` to
an object `Z` over `Y'` is the same thing as a morphism of compatible pairs from `(V, U', φ)`
to the base change of `Z`.

The bijection is the universal property of the pushout on one side and of the two fibre
products on the other. -/
noncomputable def adjunction {X X' Y Y' : C} (i : X ⟶ X') (f : X ⟶ Y)
    {a : X' ⟶ Y'} {b : Y ⟶ Y'} (w : i ≫ a = f ≫ b)
    (hpo : ∀ T : GluingData i f,
      HasPushout (pullback.fst T.obj.right.hom i) (sourceMap i f T)) :
    gluingFunctor i f w hpo ⊣ baseChangeFunctor i f w :=
  Adjunction.mkOfHomEquiv {
    homEquiv := homEquiv i f w hpo
    homEquiv_naturality_left_symm := by
      intro T S Z g h
      let := hpo T
      let := hpo S
      apply Over.OverMorphism.ext
      refine pushout.hom_ext ?_ ?_
      · exact (inl_comp_gluingFromPair i f w hpo (g ≫ h)).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (fun m => Over.Hom.left g.hom.right ≫ m)
              (inl_comp_gluingFromPair i f w hpo h)).symm.trans
                (gluedMap_inl_assoc i f w g _).symm))
      · exact (inr_comp_gluingFromPair i f w hpo (g ≫ h)).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (fun m => Over.Hom.left g.hom.left ≫ m)
              (inr_comp_gluingFromPair i f w hpo h)).symm.trans
                (gluedMap_inr_assoc i f w g _).symm))
    homEquiv_naturality_right := by
      intro T Z W h k
      let := hpo T
      apply ObjectProperty.hom_ext
      apply Comma.hom_ext
      · apply Over.OverMorphism.ext
        refine pullback.hom_ext ?_ ?_
        · exact (gluingToPair_left_comp_fst i f w hpo (h ≫ k)).trans
            (((Category.assoc _ _ _).trans
              ((congrArg (fun m => (gluingToPair i f w hpo h).hom.left.left ≫ m)
                (pullback.lift_fst _ _ _ :
                  ((Over.pullback b).map k).left ≫ pullback.fst W.hom b = _)).trans
                  (gluingToPair_left_comp_fst_assoc i f w hpo h k.left))).symm)
        · exact (gluingToPair_left_comp_snd i f w hpo (h ≫ k)).trans
            (((Category.assoc _ _ _).trans
              ((congrArg (fun m => (gluingToPair i f w hpo h).hom.left.left ≫ m)
                (pullback.lift_snd _ _ _ :
                  ((Over.pullback b).map k).left ≫ pullback.snd W.hom b = _)).trans
                  (gluingToPair_left_comp_snd i f w hpo h))).symm)
      · apply Over.OverMorphism.ext
        refine pullback.hom_ext ?_ ?_
        · exact (gluingToPair_right_comp_fst i f w hpo (h ≫ k)).trans
            (((Category.assoc _ _ _).trans
              ((congrArg (fun m => (gluingToPair i f w hpo h).hom.right.left ≫ m)
                (pullback.lift_fst _ _ _ :
                  ((Over.pullback a).map k).left ≫ pullback.fst W.hom a = _)).trans
                  (gluingToPair_right_comp_fst_assoc i f w hpo h k.left))).symm)
        · exact (gluingToPair_right_comp_snd i f w hpo (h ≫ k)).trans
            (((Category.assoc _ _ _).trans
              ((congrArg (fun m => (gluingToPair i f w hpo h).hom.right.left ≫ m)
                (pullback.lift_snd _ _ _ :
                  ((Over.pullback a).map k).left ≫ pullback.snd W.hom a = _)).trans
                  (gluingToPair_right_comp_snd i f w hpo h))).symm) }

end CategoryTheory.PushoutGluing

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A base change of a thickening of algebraic spaces over `S` is a thickening: a thickening is
a closed immersion that is surjective on points, and both classes are stable under base
change. -/
theorem isThickeningHom_of_isPullback {F G H P : AlgebraicSpaces B S hS}
    {f : F ⟶ H} {g : G ⟶ H} {fst : P ⟶ F} {snd : P ⟶ G} (sq : IsPullback fst snd f g)
    (hf : IsThickeningHom B S hS f) : IsThickeningHom B S hS snd := by
  rw [isThickeningHom_iff_isClosedImmersion_and_isSurjective]
  exact ⟨isClosedImmersion_of_isPullback B S hS sq hf.isClosedImmersion,
    isSurjective_of_isPullback B S hS sq hf.surjective_pointsMap⟩

/-- Compatible algebraic spaces over the two legs of a thickening-and-affine span: an algebraic
space `V` over `Y`, an algebraic space `U'` over `X'`, and an isomorphism
`V ×_Y X ≅ U' ×_{X'} X`. -/
abbrev pushoutGluingData {X X' Y : AlgebraicSpaces B S hS} (i : X ⟶ X') (f : X ⟶ Y) :=
  CategoryTheory.PushoutGluing.GluingData i f

/-- The pushout `V ⨿_U U'` of a compatible pair of algebraic spaces exists: `U ⟶ U'` is a base
change of the thickening `i` and `U ⟶ V` is a base change of the affine morphism `f`, so
Stacks 07VX applies to them. -/
theorem pushoutGluingHasPushout (hatlas : HasThickeningAffineAtlases B S hS)
    {X X' Y : AlgebraicSpaces B S hS} (i : X ⟶ X') (f : X ⟶ Y)
    (hi : IsThickeningHom B S hS i) (hf : IsAffineHom B S hS f.hom)
    (T : pushoutGluingData B S hS i f) :
    HasPushout (pullback.fst T.obj.right.hom i)
      (CategoryTheory.PushoutGluing.sourceMap i f T) := by
  have hthick : IsThickeningHom B S hS (pullback.fst T.obj.right.hom i) :=
    isThickeningHom_of_isPullback B S hS
      (IsPullback.of_hasPullback T.obj.right.hom i).flip hi
  have haff : IsAffineHom B S hS
      (CategoryTheory.PushoutGluing.sourceMap i f T).hom :=
    isAffineHom_hom_of_isPullback
      (CategoryTheory.PushoutGluing.sourceMap_isPullback i f T).flip hf
  exact hasPushout_of_isThickening_of_isAffineHom B S hS hatlas _ _ hthick haff

/-- **Stacks 07VY, the base-change functor `F`.**  Let `i : X ⟶ X'` be a thickening of
algebraic spaces over `S`, let `f : X ⟶ Y` be an affine morphism and let `Y' = Y ⨿_X X'` be the
pushout.  Base change along `Y ⟶ Y'` and `X' ⟶ Y'` sends an algebraic space `V'` over `Y'` to
the triple `(V' ×_{Y'} Y, V' ×_{Y'} X', 1)`.

The `2`-fibre product of the source is modelled by
`AlgebraicGeometry.Space.pushoutGluingData`, the iso-comma category of the two base-change
functors to algebraic spaces over `X`: an object carries the comparison isomorphism as data, so
a morphism of triples satisfies the compatibility square automatically. -/
noncomputable def pushoutBaseChangeFunctor (hatlas : HasThickeningAffineAtlases B S hS)
    {X X' Y : AlgebraicSpaces B S hS} (i : X ⟶ X') (f : X ⟶ Y)
    (hi : IsThickeningHom B S hS i) (hf : IsAffineHom B S hS f.hom) :
    letI := hasPushout_of_isThickening_of_isAffineHom B S hS hatlas i f hi hf
    Over (pushout i f) ⥤ pushoutGluingData B S hS i f :=
  letI := hasPushout_of_isThickening_of_isAffineHom B S hS hatlas i f hi hf
  CategoryTheory.PushoutGluing.baseChangeFunctor i f (pushout.condition (f := i) (g := f))

/-- **Stacks 07VY, the left adjoint `G`.**  Gluing compatible algebraic spaces over `Y` and
over `X'` to an algebraic space over `Y' = Y ⨿_X X'`, by the objectwise pushout
`V ⨿_{V ×_Y X} U'`.

That pushout exists because the span of a triple is again a thickening-and-affine span:
`V ×_Y X ⟶ U'` is a base change of `i` and `V ×_Y X ⟶ V` is a base change of `f`.  Its
objectwise pushout property is
`AlgebraicGeometry.Space.pushoutGluingFunctor_obj_isPushout`. -/
noncomputable def pushoutGluingFunctor (hatlas : HasThickeningAffineAtlases B S hS)
    {X X' Y : AlgebraicSpaces B S hS} (i : X ⟶ X') (f : X ⟶ Y)
    (hi : IsThickeningHom B S hS i) (hf : IsAffineHom B S hS f.hom) :
    letI := hasPushout_of_isThickening_of_isAffineHom B S hS hatlas i f hi hf
    pushoutGluingData B S hS i f ⥤ Over (pushout i f) :=
  letI := hasPushout_of_isThickening_of_isAffineHom B S hS hatlas i f hi hf
  CategoryTheory.PushoutGluing.gluingFunctor i f (pushout.condition (f := i) (g := f))
    (pushoutGluingHasPushout B S hS hatlas i f hi hf)

/-- **Stacks 07VY, the formula for the left adjoint.**  The algebraic space glued from a triple
`(V, U', φ)` is the pushout of `V` and `U'` along their identified restrictions to `X`, and its
structure morphism to `Y'` restricts to `V ⟶ Y ⟶ Y'` and to `U' ⟶ X' ⟶ Y'`. -/
theorem pushoutGluingFunctor_obj_isPushout (hatlas : HasThickeningAffineAtlases B S hS)
    {X X' Y : AlgebraicSpaces B S hS} (i : X ⟶ X') (f : X ⟶ Y)
    (hi : IsThickeningHom B S hS i) (hf : IsAffineHom B S hS f.hom)
    (T : pushoutGluingData B S hS i f) :
    letI := hasPushout_of_isThickening_of_isAffineHom B S hS hatlas i f hi hf
    ∃ (v : T.obj.left.left ⟶
        ((pushoutGluingFunctor B S hS hatlas i f hi hf).obj T).left)
      (u' : T.obj.right.left ⟶
        ((pushoutGluingFunctor B S hS hatlas i f hi hf).obj T).left),
      IsPushout (CategoryTheory.PushoutGluing.sourceMap i f T)
          (pullback.fst T.obj.right.hom i) v u' ∧
        v ≫ ((pushoutGluingFunctor B S hS hatlas i f hi hf).obj T).hom =
          T.obj.left.hom ≫ pushout.inr i f ∧
        u' ≫ ((pushoutGluingFunctor B S hS hatlas i f hi hf).obj T).hom =
          T.obj.right.hom ≫ pushout.inl i f := by
  let := hasPushout_of_isThickening_of_isAffineHom B S hS hatlas i f hi hf
  exact CategoryTheory.PushoutGluing.gluingFunctor_obj_isPushout i f
    (pushout.condition (f := i) (g := f))
    (pushoutGluingHasPushout B S hS hatlas i f hi hf) T

/-- **Stacks 07VY, the adjunction.**  Gluing is left adjoint to base change: a morphism from the
glued algebraic space `V ⨿_U U'` to an algebraic space `Z` over `Y'` is the same thing as a
morphism of triples from `(V, U', φ)` to the base change of `Z`. -/
noncomputable def pushoutGluingAdjunction (hatlas : HasThickeningAffineAtlases B S hS)
    {X X' Y : AlgebraicSpaces B S hS} (i : X ⟶ X') (f : X ⟶ Y)
    (hi : IsThickeningHom B S hS i) (hf : IsAffineHom B S hS f.hom) :
    letI := hasPushout_of_isThickening_of_isAffineHom B S hS hatlas i f hi hf
    pushoutGluingFunctor B S hS hatlas i f hi hf ⊣
      pushoutBaseChangeFunctor B S hS hatlas i f hi hf :=
  letI := hasPushout_of_isThickening_of_isAffineHom B S hS hatlas i f hi hf
  CategoryTheory.PushoutGluing.adjunction i f (pushout.condition (f := i) (g := f))
    (pushoutGluingHasPushout B S hS hatlas i f hi hf)

/-! ### The cube of étale charts over a triple -/

/-- **Stacks 07W2**, equation 81.6.5.2 of the proof of Stacks 07W0: the cube of étale charts of
the span of a triple `(V, U', φ)` and of the glued algebraic space `G(V, U', φ) = V ⨿_U U'`.

Let `i : X ⟶ X'` be a thickening of algebraic spaces over `S`, let `f : X ⟶ Y` be an affine
morphism, and let `(V, U', φ)` be a triple: an algebraic space `V` over `Y`, an algebraic space
`U'` over `X'` and an identification of `V ×_Y X` with `U = U' ×_{X'} X`.  The span
`U' ⟵ U ⟶ V` is again a thickening and an affine morphism, so it has a pushout
`G(V, U', φ) = V ⨿_U U'`, and it carries a cube of étale scheme charts:

```
back face:    U  ⟶ U'       front face:   U₁ ⟶ U₁'
              ↓     ↓                     ↓     ↓
              V  ⟶ G                      V₁ ⟶ G₁

northeast arrows:   U₁ ⟶ U,  U₁' ⟶ U',  V₁ ⟶ V,  G₁ ⟶ G
```

The back square `U, U', V, G` and the front square `U₁, U₁', V₁, G₁` are pushouts — the second
one of schemes, so that `G₁ = G₁(V₁, U₁', φ₁) = V₁ ⨿_{U₁} U₁'` — the four lateral squares are
cartesian, and the four northeast arrows are surjective and étale.  The last of those four,
`IsSurjective … r` and `IsEtale … r`, is the source's "in particular
`G₁(V₁, U₁', φ₁) ⟶ G(V, U', φ)` is surjective étale".

The two cartesian lateral squares over the legs of the front span say that `(V₁, U₁', φ₁)` is a
triple for the span `U' ⟵ U ⟶ V`: `U₁ = V₁ ×_V U` and `U₁ = U₁' ×_{U'} U`.

The corner `G` is quantified over rather than named, exactly as `Y'` is in equation 81.6.5.1;
being a pushout of the span of the triple it is canonically the value of the functor `G` of
Tag 07VY on that triple, by `AlgebraicGeometry.Space.pushoutGluingFunctor_obj_isPushout` and
uniqueness of pushouts.

This is `AlgebraicGeometry.Space.exists_etaleChartCube_of_isThickening_of_isAffineHom`,
equation 81.6.5.1 for the same cube over a thickening-and-affine span, instantiated at the span
of the triple — which is exactly how the source states it, by repeating the sentence it used
for the first cube.  That the span of a triple is again a thickening-and-affine span is
`AlgebraicGeometry.Space.isThickeningHom_of_isPullback` and
`AlgebraicGeometry.Space.isAffineHom_hom_of_isPullback`, as in
`AlgebraicGeometry.Space.pushoutGluingHasPushout`.

The *prescribed* cube — in which `V₁` is a chart of `Y₁ ×_Y V` and `U₁ = V₁ ×_Y X`, so that
`G₁` acquires a morphism to `Y₁'` — is a strictly stronger statement that the displayed
diagram does not make: the diagram names none of `X₁, X₁', Y₁, Y₁'`.  It is not claimed
here. -/
theorem exists_etaleChartCube_gluingData_of_isThickening_of_isAffineHom
    (hatlas : HasThickeningAffineAtlases B S hS)
    {X X' Y : AlgebraicSpaces B S hS} (i : X ⟶ X') (f : X ⟶ Y)
    (hi : IsThickeningHom B S hS i) (hf : IsAffineHom B S hS f.hom)
    (T : pushoutGluingData B S hS i f) :
    ∃ (U₁ U₁' V₁ G₁ : BigFppfOver B S hS) (G : AlgebraicSpaces B S hS)
      (aG : T.obj.right.left ⟶ G) (bG : T.obj.left.left ⟶ G) (k : U₁ ⟶ U₁') (g : U₁ ⟶ V₁)
      (aG₁ : U₁' ⟶ G₁) (bG₁ : V₁ ⟶ G₁)
      (p : yoneda.obj U₁ ⟶ (pullback T.obj.right.hom i).1)
      (p' : yoneda.obj U₁' ⟶ T.obj.right.left.1)
      (q : yoneda.obj V₁ ⟶ T.obj.left.left.1) (r : yoneda.obj G₁ ⟶ G.1),
      IsPushout (pullback.fst T.obj.right.hom i)
        (CategoryTheory.PushoutGluing.sourceMap i f T) aG bG ∧
      IsPushout ((BigFppfOver.toScheme B S hS).map k) ((BigFppfOver.toScheme B S hS).map g)
        ((BigFppfOver.toScheme B S hS).map aG₁) ((BigFppfOver.toScheme B S hS).map bG₁) ∧
      Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map k) ∧
      _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map g) ∧
      IsPullback (yoneda.map k) p p' (pullback.fst T.obj.right.hom i).hom ∧
      IsPullback p (yoneda.map g)
        (CategoryTheory.PushoutGluing.sourceMap i f T).hom q ∧
      IsPullback (yoneda.map aG₁) p' r aG.hom ∧
      IsPullback (yoneda.map bG₁) q r bG.hom ∧
      IsSurjective B S hS p ∧ IsEtale B S hS p ∧
      IsSurjective B S hS p' ∧ IsEtale B S hS p' ∧
      IsSurjective B S hS q ∧ IsEtale B S hS q ∧
      IsSurjective B S hS r ∧ IsEtale B S hS r :=
  exists_etaleChartCube_of_isThickening_of_isAffineHom B S hS hatlas _ _
    (isThickeningHom_of_isPullback B S hS
      (IsPullback.of_hasPullback T.obj.right.hom i).flip hi)
    (isAffineHom_hom_of_isPullback
      (CategoryTheory.PushoutGluing.sourceMap_isPullback i f T).flip hf)

end AlgebraicGeometry.Space

end
