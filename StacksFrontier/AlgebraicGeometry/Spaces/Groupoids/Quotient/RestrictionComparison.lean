module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.Restriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Stabilizer.RestrictionArrows
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.EquivalenceRelationGroupoid
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits

/-!
# Restricting a groupoid and restricting its relation agree

This is **Stacks 044D**: the restriction of groupoids in algebraic spaces (**Stacks 044C**) and the
restriction of (pre-)equivalence relations (**Stacks 043D**) agree via the constructions of
**Stacks 043X** and **Stacks 043Y**. Let `B` be an algebraic space over `S` and let
`g : U' ⟶ U` be a morphism of algebraic spaces.

1. For a groupoid `G = (U, R, s, t, c)` in algebraic spaces over `B`, the pre-relation
   `(t', s') : R' ⟶ U' ×_B U'` of the restriction `G|_{U'}`, whose arrow space is
   `R' = U' ×_{g, U, t} R ×_{s, U, g} U'`, is the restriction along `g` of the pre-relation
   `(t, s) : R ⟶ U ×_B U` of `G`: `R' = (U' ×_B U') ×_{U ×_B U} R`.
2. For an equivalence relation `j : R ⟶ U ×_B U` of algebraic spaces over `B`, the groupoid in
   algebraic spaces of the restricted equivalence relation `j|_{U'}` is the restriction to `U'` of
   the groupoid in algebraic spaces of `j`.

## Main definitions

* `AlgebraicGeometry.Space.overHomOfComp` and
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.restrictionObjectsHom`: a morphism of algebraic
  spaces, read in the slice of presheaves over the base.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.restrictionArrowsOver`,
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.restrictionTargetOver`,
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.restrictionSourceOver` and
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.restrictionArrowsToArrowsOver`: the arrow space of
  the restriction and its three structure morphisms, read in the slice over the base, and
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.restrictionArrowsOverIso`, the comparison of that
  arrow space with the chosen restriction of the pre-relation of `G`.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.Isomorphism`: an isomorphism of groupoids in
  algebraic spaces, and `AlgebraicGeometry.GroupoidInAlgebraicSpaces.Isomorphism.ofMono`, which
  builds one from compatible isomorphisms of objects and arrows when both pre-relations are
  monomorphisms.
* `AlgebraicGeometry.Space.restrictionSpace` and `AlgebraicGeometry.Space.restrictSpace`: the
  restriction of a pre-relation of algebraic spaces, read as a pre-relation of algebraic spaces.

## Main results

* `CategoryTheory.Limits.isPullback_prodLift_of_isPullback`: three iterated cartesian squares
  assemble into one cartesian square over a self-product.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isPullback_groupoidPreRelation_restrict`: the
  pre-relation of `G|_{U'}` is the base change of the pre-relation of `G` along
  `U' ×_B U' ⟶ U ×_B U`.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.existsUnique_iso_restriction_groupoidPreRelation`:
  **Stacks 044D**, part 1 above.
* `AlgebraicGeometry.Space.isAlgebraicSpace_restriction`: the restriction of a pre-relation of
  algebraic spaces has an algebraic space of arrows.
* `AlgebraicGeometry.Space.existsUnique_isomorphism_restrict_groupoidOfIsEquivalenceRelation`:
  **Stacks 044D**, part 2 above.

## Implementation notes

The pre-relation of **Stacks 043C** attached to a groupoid in algebraic spaces lives in the slice
`CategoryTheory.Over B.obj` of presheaves on the big fppf site, which is where
`AlgebraicGeometry.Space.groupoidPreRelation`, the restriction
`AlgebraicGeometry.Space.PreRelation.restriction` of **Stacks 043D** and the groupoid
`AlgebraicGeometry.Space.groupoidOfIsEquivalenceRelation` of **Stacks 043Y** are all stated; the
arrow space of the restricted groupoid is built in the category of algebraic spaces. The four
`…Over` declarations below read the arrow space of the restriction and its three structure
morphisms as an object and three morphisms of that slice.

The cartesian square itself is an instance of `isPullback_prodLift_of_isPullback`, which says in
any category with binary products that if `A = U' ×_{g, U, t} R`, `D = R ×_{s, U, g} U'` and
`P = A ×_R D`, then `P` is the fibre product of `prod.map g g` and `prod.lift t s`. The three
hypotheses hold in the slice because `CategoryTheory.Over.forget` creates connected limits and is
faithful, so a square of the slice is cartesian as soon as the underlying square of presheaves
is, and the underlying squares are the defining ones of the three chosen presheaf fibre products.

The source writes the arrow spaces as equal fibre products. Since fibre products are chosen
objects in Lean, both comparisons are isomorphisms: of arrow spaces commuting with the maps to
`U' ×_B U'` and to `R` in the first part, and of groupoids in algebraic spaces, the identity on
objects and commuting with the maps of arrows to `R`, in the second. These compatibilities
determine each isomorphism uniquely.

## References

* [Stacks Project, Tag 043C](https://stacks.math.columbia.edu/tag/043C)
* [Stacks Project, Tag 043D](https://stacks.math.columbia.edu/tag/043D)
* [Stacks Project, Tag 043X](https://stacks.math.columbia.edu/tag/043X)
* [Stacks Project, Tag 043Y](https://stacks.math.columbia.edu/tag/043Y)
* [Stacks Project, Tag 044B](https://stacks.math.columbia.edu/tag/044B)
* [Stacks Project, Tag 044C](https://stacks.math.columbia.edu/tag/044C)
* [Stacks Project, Tag 044D](https://stacks.math.columbia.edu/tag/044D)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory.Limits

/-- Three iterated cartesian squares assemble into one cartesian square over a self-product: if
`A` is the fibre product of `g : U' ⟶ U` and `t : R ⟶ U`, if `D` is the fibre product of
`s : R ⟶ U` and `g`, and if `P` is the fibre product of `A` and `D` over `R`, then `P` is the
fibre product of `prod.map g g : U' ⨯ U' ⟶ U ⨯ U` and `prod.lift t s : R ⟶ U ⨯ U`. -/
@[ega "I 5.3.5" "special case"]
theorem isPullback_prodLift_of_isPullback {C : Type u} [Category.{v} C] [HasBinaryProducts C]
    {R U U' A D P : C} {t s : R ⟶ U} {g : U' ⟶ U}
    {a₁ : A ⟶ U'} {a₂ : A ⟶ R} (ha : IsPullback a₁ a₂ g t)
    {d₁ : D ⟶ R} {d₂ : D ⟶ U'} (hd : IsPullback d₁ d₂ s g)
    {p₁ : P ⟶ A} {p₂ : P ⟶ D} (hp : IsPullback p₁ p₂ a₂ d₁) :
    IsPullback (prod.lift (p₁ ≫ a₁) (p₂ ≫ d₂)) (p₁ ≫ a₂) (prod.map g g) (prod.lift t s) := by
  have hsnd : (p₂ ≫ d₂) ≫ g = (p₁ ≫ a₂) ≫ s := by
    rw [Category.assoc, ← hd.w, hp.w]; simp [Category.assoc]
  have hw : prod.lift (p₁ ≫ a₁) (p₂ ≫ d₂) ≫ prod.map g g = (p₁ ≫ a₂) ≫ prod.lift t s :=
    prod.hom_ext (by simpa [Category.assoc] using congrArg (p₁ ≫ ·) ha.w)
      (by simpa [Category.assoc] using hsnd)
  have key : ∀ c : PullbackCone (prod.map g g) (prod.lift t s),
      ((c.fst ≫ prod.fst) ≫ g = c.snd ≫ t) ∧ (c.snd ≫ s = (c.fst ≫ prod.snd) ≫ g) := by
    intro c
    refine ⟨?_, ?_⟩
    · simpa [Category.assoc] using congrArg (· ≫ prod.fst) c.condition
    · simpa [Category.assoc] using (congrArg (· ≫ prod.snd) c.condition).symm
  have mid : ∀ c : PullbackCone (prod.map g g) (prod.lift t s),
      ha.lift (c.fst ≫ prod.fst) c.snd (key c).1 ≫ a₂ =
        hd.lift c.snd (c.fst ≫ prod.snd) (key c).2 ≫ d₁ :=
    fun c => (ha.lift_snd _ _ _).trans (hd.lift_fst _ _ _).symm
  let lift : ∀ c : PullbackCone (prod.map g g) (prod.lift t s), c.pt ⟶ P := fun c =>
    hp.lift (ha.lift (c.fst ≫ prod.fst) c.snd (key c).1)
      (hd.lift c.snd (c.fst ≫ prod.snd) (key c).2) (mid c)
  have hfst : ∀ c, lift c ≫ p₁ ≫ a₁ = c.fst ≫ prod.fst := fun c => by
    rw [← Category.assoc, hp.lift_fst, ha.lift_fst]
  have hsnd' : ∀ c, lift c ≫ p₂ ≫ d₂ = c.fst ≫ prod.snd := fun c => by
    rw [← Category.assoc, hp.lift_snd, hd.lift_snd]
  have harr : ∀ c, lift c ≫ p₁ ≫ a₂ = c.snd := fun c => by
    rw [← Category.assoc, hp.lift_fst, ha.lift_snd]
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk hw lift (fun c => ?_)
    (fun c => harr c) (fun c m hm₁ hm₂ => ?_))
  · exact prod.hom_ext (by simpa [Category.assoc] using hfst c)
      (by simpa [Category.assoc] using hsnd' c)
  · have hm₁f : m ≫ p₁ ≫ a₁ = c.fst ≫ prod.fst := by
      simpa [Category.assoc] using congrArg (· ≫ prod.fst) hm₁
    have hm₁s : m ≫ p₂ ≫ d₂ = c.fst ≫ prod.snd := by
      simpa [Category.assoc] using congrArg (· ≫ prod.snd) hm₁
    refine hp.hom_ext (ha.hom_ext ?_ ?_) (hd.hom_ext ?_ ?_)
    · simpa only [Category.assoc] using hm₁f.trans (hfst c).symm
    · simpa only [Category.assoc] using hm₂.trans (harr c).symm
    · rw [Category.assoc, Category.assoc, ← hp.w, ← Category.assoc, ← Category.assoc]
      simpa only [Category.assoc] using hm₂.trans (harr c).symm
    · simpa only [Category.assoc] using hm₁s.trans (hsnd' c).symm

end CategoryTheory.Limits

namespace AlgebraicGeometry.Space

/-- A morphism `g : U' ⟶ U` of algebraic spaces, `U` lying over `B` through `q`, read as a
morphism of the slice of presheaves over `B`, `U'` lying over `B` through `g ≫ q`. -/
def overHomOfComp {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {B U U' : AlgebraicSpaces C S hS} (q : U ⟶ B) (g : U' ⟶ U) :
    (Over.mk (g ≫ q).hom : Over B.obj) ⟶ Over.mk q.hom :=
  Over.homMk g.hom rfl

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-- **Stacks 044B.** The target of an arrow of the restriction and its underlying arrow have the
same composite to the base. -/
theorem restrictionTarget_comp_objectsToBase (G : GroupoidInAlgebraicSpaces C S hS B)
    {U' : AlgebraicSpaces C S hS} (g : U' ⟶ G.objects) :
    restrictionTarget G g ≫ g ≫ G.objectsToBase =
      restrictionArrowsToArrows G g ≫ G.arrowsToBase := by
  rw [← Category.assoc, ← restrictionArrowsToArrows_comp_target, Category.assoc, G.target_over]

/-- **Stacks 044B.** The source of an arrow of the restriction and its underlying arrow have the
same composite to the base. -/
theorem restrictionSource_comp_objectsToBase (G : GroupoidInAlgebraicSpaces C S hS B)
    {U' : AlgebraicSpaces C S hS} (g : U' ⟶ G.objects) :
    restrictionSource G g ≫ g ≫ G.objectsToBase =
      restrictionArrowsToArrows G g ≫ G.arrowsToBase := by
  rw [← Category.assoc, ← restrictionArrowsToArrows_comp_source, Category.assoc, G.source_over]

/-- The restricting morphism `g` of **Stacks 044B**, read as a morphism of the slice of
presheaves over the base in which the pre-relation of **Stacks 043X** lives. -/
def restrictionObjectsHom (G : GroupoidInAlgebraicSpaces C S hS B)
    {U' : AlgebraicSpaces C S hS} (g : U' ⟶ G.objects) :
    (Over.mk (g ≫ G.objectsToBase).hom : Over B.obj) ⟶ Over.mk G.objectsToBase.hom :=
  Space.overHomOfComp G.objectsToBase g

/-- The arrow space of the restriction of a groupoid in algebraic spaces (**Stacks 044B**), read
as an object of the slice of presheaves over the base. -/
noncomputable def restrictionArrowsOver (G : GroupoidInAlgebraicSpaces C S hS B)
    {U' : AlgebraicSpaces C S hS} (g : U' ⟶ G.objects) : Over B.obj :=
  Over.mk ((restrictionArrowsToArrows G g).hom ≫ G.arrowsToBase.hom)

/-- The target of an arrow of the restriction (**Stacks 044B**), read in the slice of presheaves
over the base. -/
noncomputable def restrictionTargetOver (G : GroupoidInAlgebraicSpaces C S hS B)
    {U' : AlgebraicSpaces C S hS} (g : U' ⟶ G.objects) :
    restrictionArrowsOver G g ⟶ Over.mk (g ≫ G.objectsToBase).hom :=
  Over.homMk (restrictionTarget G g).hom
    (congrArg (fun k : restrictionArrows G g ⟶ B => k.hom)
      (restrictionTarget_comp_objectsToBase G g))

/-- The source of an arrow of the restriction (**Stacks 044B**), read in the slice of presheaves
over the base. -/
noncomputable def restrictionSourceOver (G : GroupoidInAlgebraicSpaces C S hS B)
    {U' : AlgebraicSpaces C S hS} (g : U' ⟶ G.objects) :
    restrictionArrowsOver G g ⟶ Over.mk (g ≫ G.objectsToBase).hom :=
  Over.homMk (restrictionSource G g).hom
    (congrArg (fun k : restrictionArrows G g ⟶ B => k.hom)
      (restrictionSource_comp_objectsToBase G g))

/-- The underlying arrow of an arrow of the restriction (**Stacks 044B**), read in the slice of
presheaves over the base. -/
noncomputable def restrictionArrowsToArrowsOver (G : GroupoidInAlgebraicSpaces C S hS B)
    {U' : AlgebraicSpaces C S hS} (g : U' ⟶ G.objects) :
    restrictionArrowsOver G g ⟶ Over.mk G.arrowsToBase.hom :=
  Over.homMk (restrictionArrowsToArrows G g).hom rfl

/-- The arrow space of the restriction of a groupoid in algebraic spaces along
`g : U' ⟶ U` is the fibre product of `U' ×_B U' ⟶ U ×_B U` and the pre-relation
`(t, s) : R ⟶ U ×_B U` of the groupoid: an arrow of the restriction is an arrow of `G` together
with a lift of each of its two endpoints along `g`. -/
theorem isPullback_restrictionArrowsOver (G : GroupoidInAlgebraicSpaces C S hS B)
    {U' : AlgebraicSpaces C S hS} (g : U' ⟶ G.objects) :
    IsPullback (prod.lift (restrictionTargetOver G g) (restrictionSourceOver G g))
      (restrictionArrowsToArrowsOver G g)
      (prod.map (restrictionObjectsHom G g) (restrictionObjectsHom G g))
      (Space.groupoidPreRelation G) := by
  have htgt : fiberProductSnd g G.target ≫ G.arrowsToBase =
      fiberProductFst g G.target ≫ g ≫ G.objectsToBase := by
    rw [← G.target_over, ← Category.assoc,
      ← (AlgebraicSpaces.isPullback_fiberProduct C S hS g G.target).w, Category.assoc]
  have hsrc : fiberProductFst G.source g ≫ G.arrowsToBase =
      fiberProductSnd G.source g ≫ g ≫ G.objectsToBase := by
    rw [← G.source_over, ← Category.assoc,
      (AlgebraicSpaces.isPullback_fiberProduct C S hS G.source g).w, Category.assoc]
  let Uo : Over B.obj := Over.mk G.objectsToBase.hom
  let Ro : Over B.obj := Over.mk G.arrowsToBase.hom
  let U'o : Over B.obj := Over.mk (g ≫ G.objectsToBase).hom
  let a₁ : (Over.mk ((fiberProductFst g G.target).hom ≫ (g ≫ G.objectsToBase).hom) :
      Over B.obj) ⟶ U'o :=
    Over.homMk (fiberProductFst g G.target).hom rfl
  let a₂ : (Over.mk ((fiberProductFst g G.target).hom ≫ (g ≫ G.objectsToBase).hom) :
      Over B.obj) ⟶ Ro :=
    Over.homMk (fiberProductSnd g G.target).hom
      (congrArg (fun k : AlgebraicSpaces.fiberProduct C S hS g G.target ⟶ B => k.hom) htgt)
  let d₁ : (Over.mk ((fiberProductSnd G.source g).hom ≫ (g ≫ G.objectsToBase).hom) :
      Over B.obj) ⟶ Ro :=
    Over.homMk (fiberProductFst G.source g).hom
      (congrArg (fun k : AlgebraicSpaces.fiberProduct C S hS G.source g ⟶ B => k.hom) hsrc)
  let d₂ : (Over.mk ((fiberProductSnd G.source g).hom ≫ (g ≫ G.objectsToBase).hom) :
      Over B.obj) ⟶ U'o :=
    Over.homMk (fiberProductSnd G.source g).hom rfl
  let p₁ : restrictionArrowsOver G g ⟶
      Over.mk ((fiberProductFst g G.target).hom ≫ (g ≫ G.objectsToBase).hom) :=
    Over.homMk
      (fiberProductFst (fiberProductSnd g G.target) (fiberProductFst G.source g)).hom
      (by
        show (fiberProductFst (fiberProductSnd g G.target) (fiberProductFst G.source g)).hom ≫
            (fiberProductFst g G.target).hom ≫ (g ≫ G.objectsToBase).hom =
          (restrictionArrowsToArrows G g).hom ≫ G.arrowsToBase.hom
        rw [← Category.assoc]
        exact congrArg (fun k : restrictionArrows G g ⟶ B => k.hom)
          (restrictionTarget_comp_objectsToBase G g))
  let p₂ : restrictionArrowsOver G g ⟶
      Over.mk ((fiberProductSnd G.source g).hom ≫ (g ≫ G.objectsToBase).hom) :=
    Over.homMk
      (fiberProductSnd (fiberProductSnd g G.target) (fiberProductFst G.source g)).hom
      (by
        show (fiberProductSnd (fiberProductSnd g G.target) (fiberProductFst G.source g)).hom ≫
            (fiberProductSnd G.source g).hom ≫ (g ≫ G.objectsToBase).hom =
          (restrictionArrowsToArrows G g).hom ≫ G.arrowsToBase.hom
        rw [← Category.assoc]
        exact congrArg (fun k : restrictionArrows G g ⟶ B => k.hom)
          (restrictionSource_comp_objectsToBase G g))
  have ha : IsPullback a₁ a₂ (restrictionObjectsHom G g)
      (Over.homMk G.target.hom
        (congrArg (fun k : G.arrows ⟶ B => k.hom) G.target_over) : Ro ⟶ Uo) :=
    IsPullback.of_map_of_faithful (Over.forget B.obj)
      (IsPullback.of_hasPullback g.hom G.target.hom)
  have hd : IsPullback d₁ d₂
      (Over.homMk G.source.hom
        (congrArg (fun k : G.arrows ⟶ B => k.hom) G.source_over) : Ro ⟶ Uo)
      (restrictionObjectsHom G g) :=
    IsPullback.of_map_of_faithful (Over.forget B.obj)
      (IsPullback.of_hasPullback G.source.hom g.hom)
  have hp : IsPullback p₁ p₂ a₂ d₁ :=
    IsPullback.of_map_of_faithful (Over.forget B.obj)
      (IsPullback.of_hasPullback (pullback.snd g.hom G.target.hom)
        (pullback.fst G.source.hom g.hom))
  exact isPullback_prodLift_of_isPullback ha hd hp

/-- The arrow space of the restriction of a groupoid in algebraic spaces along
`g` is canonically isomorphic to the restriction along `g` of the pre-relation of the groupoid:
the two notions of restriction, of a groupoid and of a pre-equivalence relation, agree. -/
noncomputable def restrictionArrowsOverIso (G : GroupoidInAlgebraicSpaces C S hS B)
    {U' : AlgebraicSpaces C S hS} (g : U' ⟶ G.objects) :
    restrictionArrowsOver G g ≅
      Space.PreRelation.restriction (Space.groupoidPreRelation G)
        (restrictionObjectsHom G g) :=
  (isPullback_restrictionArrowsOver G g).isoIsPullback _ _ (IsPullback.of_hasPullback _ _)

/-- The comparison matches the target of the restricted groupoid with the target
of the restricted pre-relation. -/
theorem restrictionArrowsOverIso_hom_target (G : GroupoidInAlgebraicSpaces C S hS B)
    {U' : AlgebraicSpaces C S hS} (g : U' ⟶ G.objects) :
    (restrictionArrowsOverIso G g).hom ≫
        (Space.PreRelation.restrict (Space.groupoidPreRelation G)
          (restrictionObjectsHom G g)).target =
      restrictionTargetOver G g := by
  rw [Space.PreRelation.target, ← Category.assoc]
  exact congrArg (· ≫ prod.fst)
    (IsPullback.isoIsPullback_hom_fst _ _ (isPullback_restrictionArrowsOver G g)
      (IsPullback.of_hasPullback _ _)) |>.trans (prod.lift_fst _ _)

/-- The comparison matches the source of the restricted groupoid with the source
of the restricted pre-relation. -/
theorem restrictionArrowsOverIso_hom_source (G : GroupoidInAlgebraicSpaces C S hS B)
    {U' : AlgebraicSpaces C S hS} (g : U' ⟶ G.objects) :
    (restrictionArrowsOverIso G g).hom ≫
        (Space.PreRelation.restrict (Space.groupoidPreRelation G)
          (restrictionObjectsHom G g)).source =
      restrictionSourceOver G g := by
  rw [Space.PreRelation.source, ← Category.assoc]
  exact congrArg (· ≫ prod.snd)
    (IsPullback.isoIsPullback_hom_fst _ _ (isPullback_restrictionArrowsOver G g)
      (IsPullback.of_hasPullback _ _)) |>.trans (prod.lift_snd _ _)

/-- The comparison matches the underlying arrow of an arrow of the restricted
groupoid with the projection to `R` of the restricted pre-relation. -/
theorem restrictionArrowsOverIso_hom_snd (G : GroupoidInAlgebraicSpaces C S hS B)
    {U' : AlgebraicSpaces C S hS} (g : U' ⟶ G.objects) :
    (restrictionArrowsOverIso G g).hom ≫
        pullback.snd (prod.map (restrictionObjectsHom G g) (restrictionObjectsHom G g))
          (Space.groupoidPreRelation G) =
      restrictionArrowsToArrowsOver G g :=
  IsPullback.isoIsPullback_hom_snd _ _ (isPullback_restrictionArrowsOver G g)
    (IsPullback.of_hasPullback _ _)

/-! ### Restricting a groupoid, then taking its pre-relation -/

/-- The pre-relation `(t', s')` of the restriction `G|_{U'}` of **Stacks 044C** is the base change
of the pre-relation `(t, s)` of `G` along `U' ×_B U' ⟶ U ×_B U`, the top arrow of the square being
the map on arrows of the canonical morphism `G|_{U'} ⟶ G` of **Stacks 044B**. -/
theorem isPullback_groupoidPreRelation_restrict (G : GroupoidInAlgebraicSpaces C S hS B)
    {U' : AlgebraicSpaces C S hS} (g : U' ⟶ G.objects) :
    IsPullback (Space.groupoidPreRelation (G.restrict g).groupoid)
      (Over.homMk (G.restrict g).hom.toGroupoidHom.mapArrows (G.restrict g).hom.mapArrows_over :
        (Over.mk (G.restrict g).groupoid.arrowsToBase.hom : Over B.obj) ⟶
          Over.mk G.arrowsToBase.hom)
      (prod.map (restrictionObjectsHom G g) (restrictionObjectsHom G g))
      (Space.groupoidPreRelation G) :=
  isPullback_restrictionArrowsOver G g

/-- **Stacks 044D**, restricting a groupoid and then taking its pre-relation. Let `G` be a
groupoid in algebraic spaces over `B` and `g : U' ⟶ U` a morphism to its space of objects. The
pre-relation `j' = (t', s') : R' ⟶ U' ×_B U'` of the restriction `G|_{U'}` of **Stacks 044C**,
whose arrow space is `R' = U' ×_{g, U, t} R ×_{s, U, g} U'`, is the restriction along `g`, in the
sense of **Stacks 043D**, of the pre-relation `j = (t, s) : R ⟶ U ×_B U` of `G` (**Stacks 043X**):
`R' = (U' ×_B U') ×_{U ×_B U} R`. Precisely, there is exactly one isomorphism from the arrow space
of `G|_{U'}` to the restricted pre-relation's arrow space taking the restricted pre-relation to
`j'` and its projection to `R` to the map on arrows of the morphism `G|_{U'} ⟶ G`. -/
@[stacks 044D "restricting a groupoid, then taking its pre-relation"]
theorem existsUnique_iso_restriction_groupoidPreRelation (G : GroupoidInAlgebraicSpaces C S hS B)
    {U' : AlgebraicSpaces C S hS} (g : U' ⟶ G.objects) :
    ∃! e : (Over.mk (G.restrict g).groupoid.arrowsToBase.hom : Over B.obj) ≅
        Space.PreRelation.restriction (Space.groupoidPreRelation G) (restrictionObjectsHom G g),
      e.hom ≫ Space.PreRelation.restrict (Space.groupoidPreRelation G)
          (restrictionObjectsHom G g) = Space.groupoidPreRelation (G.restrict g).groupoid ∧
        e.hom ≫ pullback.snd (prod.map (restrictionObjectsHom G g) (restrictionObjectsHom G g))
            (Space.groupoidPreRelation G) =
          Over.homMk (G.restrict g).hom.toGroupoidHom.mapArrows (G.restrict g).hom.mapArrows_over :=
  ⟨(isPullback_groupoidPreRelation_restrict G g).isoPullback,
    ⟨(isPullback_groupoidPreRelation_restrict G g).isoPullback_hom_fst,
      (isPullback_groupoidPreRelation_restrict G g).isoPullback_hom_snd⟩,
    fun _ he => Iso.ext (pullback.hom_ext
      (he.1.trans (isPullback_groupoidPreRelation_restrict G g).isoPullback_hom_fst.symm)
      (he.2.trans (isPullback_groupoidPreRelation_restrict G g).isoPullback_hom_snd.symm))⟩

/-! ### Isomorphisms of groupoids in algebraic spaces -/

/-- An isomorphism of groupoids in algebraic spaces over `B`: morphisms of groupoids in both
directions whose maps on objects and on arrows are mutually inverse. -/
structure Isomorphism (G H : GroupoidInAlgebraicSpaces C S hS B) where
  /-- The morphism from `G` to `H`. -/
  hom : Hom G H
  /-- The morphism from `H` to `G`. -/
  inv : Hom H G
  /-- The maps on objects compose to the identity of the objects of `G`. -/
  hom_inv_id_objects :
    hom.toGroupoidHom.mapObjects ≫ inv.toGroupoidHom.mapObjects = 𝟙 _
  /-- The maps on objects compose to the identity of the objects of `H`. -/
  inv_hom_id_objects :
    inv.toGroupoidHom.mapObjects ≫ hom.toGroupoidHom.mapObjects = 𝟙 _
  /-- The maps on arrows compose to the identity of the arrows of `G`. -/
  hom_inv_id_arrows :
    hom.toGroupoidHom.mapArrows ≫ inv.toGroupoidHom.mapArrows = 𝟙 _
  /-- The maps on arrows compose to the identity of the arrows of `H`. -/
  inv_hom_id_arrows :
    inv.toGroupoidHom.mapArrows ≫ hom.toGroupoidHom.mapArrows = 𝟙 _

/-- When the pre-relation `(t, s)` of a groupoid in algebraic spaces is a monomorphism, a section
of its arrow space is determined by its source and its target. -/
theorem section_eq_of_mono (H : GroupoidInAlgebraicSpaces C S hS B)
    [Mono (Space.groupoidPreRelation H)] {T : (BigFppfOver C S hS)ᵒᵖ}
    {a b : H.arrows.obj.obj T} (hs : H.source.hom.app T a = H.source.hom.app T b)
    (ht : H.target.hom.app T a = H.target.hom.app T b) : a = b :=
  Space.PreRelation.section_eq_of_endpoints (T := T.unop) (Space.groupoidPreRelation H)
    inferInstance (by simpa [Space.PreRelation.source] using hs)
    (by simpa [Space.PreRelation.target] using ht)

/-- Maps of algebraic spaces on objects and on arrows, compatible with source, target and the
structure morphisms to the base, form a morphism of groupoids in algebraic spaces as soon as the
pre-relation of the target groupoid is a monomorphism: identities and composites are then
determined by their endpoints. -/
noncomputable def Hom.ofMono {G H : GroupoidInAlgebraicSpaces C S hS B}
    [Mono (Space.groupoidPreRelation H)] (φ : G.objects ⟶ H.objects) (ψ : G.arrows ⟶ H.arrows)
    (hs : ψ ≫ H.source = G.source ≫ φ) (ht : ψ ≫ H.target = G.target ≫ φ)
    (hφ : φ ≫ H.objectsToBase = G.objectsToBase) (hψ : ψ ≫ H.arrowsToBase = G.arrowsToBase) :
    Hom G H where
  toGroupoidHom :=
    { mapObjects := φ.hom
      mapArrows := ψ.hom
      map_source := fun T a => congrArg (fun k => k.hom.app T a) hs
      map_target := fun T a => congrArg (fun k => k.hom.app T a) ht
      map_id := fun T x => by
        have hG := (G.toGroupoidInFunctors.evaluationArrowEquiv T x x (𝟙 x)).2
        have hH := (H.toGroupoidInFunctors.evaluationArrowEquiv T (φ.hom.app T x)
          (φ.hom.app T x) (𝟙 _)).2
        refine section_eq_of_mono H ?_ ?_
        · refine (congrArg (fun k => k.hom.app T (G.toGroupoidInFunctors.identity T x)) hs).trans ?_
          exact (congrArg (φ.hom.app T) hG.1).trans hH.1.symm
        · refine (congrArg (fun k => k.hom.app T (G.toGroupoidInFunctors.identity T x)) ht).trans ?_
          exact (congrArg (φ.hom.app T) hG.2).trans hH.2.symm
      map_comp := fun T a b h => by
        have hsrc : ∀ (a b : G.arrows.obj.obj T) (h), G.source.hom.app T
            (G.toGroupoidInFunctors.compose T a b h) = G.source.hom.app T b :=
          fun a b h => (G.toGroupoidInFunctors.pointwiseData T).source_comp a b h
        have htgt : ∀ (a b : G.arrows.obj.obj T) (h), G.target.hom.app T
            (G.toGroupoidInFunctors.compose T a b h) = G.target.hom.app T a :=
          fun a b h => (G.toGroupoidInFunctors.pointwiseData T).target_comp a b h
        refine section_eq_of_mono H ?_ ?_
        · refine ((H.toGroupoidInFunctors.pointwiseData T).source_comp _ _ _).trans ?_
          refine (congrArg (fun k => k.hom.app T b) hs).trans ?_
          refine (congrArg (φ.hom.app T) (hsrc a b h).symm).trans ?_
          exact (congrArg (fun k => k.hom.app T (G.toGroupoidInFunctors.compose T a b h)) hs).symm
        · refine ((H.toGroupoidInFunctors.pointwiseData T).target_comp _ _ _).trans ?_
          refine (congrArg (fun k => k.hom.app T a) ht).trans ?_
          refine (congrArg (φ.hom.app T) (htgt a b h).symm).trans ?_
          exact (congrArg (fun k => k.hom.app T (G.toGroupoidInFunctors.compose T a b h)) ht).symm }
  mapObjects_over := congrArg (fun k => k.hom) hφ
  mapArrows_over := congrArg (fun k => k.hom) hψ

/-- Two morphisms of groupoids in algebraic spaces with the same maps on objects and on arrows are
equal. -/
theorem Hom.ext_of_map {G H : GroupoidInAlgebraicSpaces C S hS B} {F₁ F₂ : Hom G H}
    (h₁ : F₁.toGroupoidHom.mapObjects = F₂.toGroupoidHom.mapObjects)
    (h₂ : F₁.toGroupoidHom.mapArrows = F₂.toGroupoidHom.mapArrows) : F₁ = F₂ := by
  rcases F₁ with ⟨F₁, _, _⟩
  rcases F₂ with ⟨F₂, _, _⟩
  obtain rfl : F₁ = F₂ := Deformation.GroupoidInFunctors.Hom.ext h₁ h₂
  rfl

/-- An inverse is unique: if `f = f'`, `g ≫ f = 𝟙` and `f' ≫ g' = 𝟙`, then `g = g'`. -/
private theorem eq_of_comp_eq_id {C : Type*} [Category C] {X Y : C} {f f' : X ⟶ Y}
    {g g' : Y ⟶ X} (hf : f = f') (h₁ : g ≫ f = 𝟙 Y) (h₂ : f' ≫ g' = 𝟙 X) : g = g' := by
  subst hf
  rw [← Category.comp_id g, ← h₂, ← Category.assoc, h₁, Category.id_comp]

/-- An isomorphism of groupoids in algebraic spaces is determined by the maps on objects and on
arrows of its forward morphism. -/
theorem Isomorphism.ext_of_hom {G H : GroupoidInAlgebraicSpaces C S hS B}
    {e₁ e₂ : Isomorphism G H}
    (h₁ : e₁.hom.toGroupoidHom.mapObjects = e₂.hom.toGroupoidHom.mapObjects)
    (h₂ : e₁.hom.toGroupoidHom.mapArrows = e₂.hom.toGroupoidHom.mapArrows) : e₁ = e₂ := by
  have i₁ := eq_of_comp_eq_id h₁ e₁.inv_hom_id_objects e₂.hom_inv_id_objects
  have i₂ := eq_of_comp_eq_id h₂ e₁.inv_hom_id_arrows e₂.hom_inv_id_arrows
  rcases e₁ with ⟨f₁, g₁, _, _, _, _⟩
  rcases e₂ with ⟨f₂, g₂, _, _, _, _⟩
  obtain rfl := Hom.ext_of_map h₁ h₂
  obtain rfl := Hom.ext_of_map i₁ i₂
  rfl

/-- Isomorphisms of the spaces of objects and of the spaces of arrows of two groupoids in
algebraic spaces, compatible with source, target and the structure morphisms to the base, form an
isomorphism of groupoids in algebraic spaces when the pre-relations of both groupoids are
monomorphisms. -/
noncomputable def Isomorphism.ofMono {G H : GroupoidInAlgebraicSpaces C S hS B}
    [Mono (Space.groupoidPreRelation G)] [Mono (Space.groupoidPreRelation H)]
    (φ : G.objects ≅ H.objects) (ψ : G.arrows ≅ H.arrows)
    (hs : ψ.hom ≫ H.source = G.source ≫ φ.hom) (ht : ψ.hom ≫ H.target = G.target ≫ φ.hom)
    (hφ : φ.hom ≫ H.objectsToBase = G.objectsToBase)
    (hψ : ψ.hom ≫ H.arrowsToBase = G.arrowsToBase) : Isomorphism G H where
  hom := Hom.ofMono φ.hom ψ.hom hs ht hφ hψ
  inv := Hom.ofMono φ.inv ψ.inv
    (by rw [Iso.inv_comp_eq, reassoc_of% hs, Iso.hom_inv_id, Category.comp_id])
    (by rw [Iso.inv_comp_eq, reassoc_of% ht, Iso.hom_inv_id, Category.comp_id])
    (by rw [Iso.inv_comp_eq, hφ]) (by rw [Iso.inv_comp_eq, hψ])
  hom_inv_id_objects := congrArg (fun k => k.hom) φ.hom_inv_id
  inv_hom_id_objects := congrArg (fun k => k.hom) φ.inv_hom_id
  hom_inv_id_arrows := congrArg (fun k => k.hom) ψ.hom_inv_id
  inv_hom_id_arrows := congrArg (fun k => k.hom) ψ.inv_hom_id

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

/-! ### Restricting an equivalence relation, then taking its groupoid -/

namespace AlgebraicGeometry.Space

open GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B U R U' : AlgebraicSpaces C S hS} {qU : U ⟶ B} {qR : R ⟶ B}

/-- The restriction along a morphism of algebraic spaces `g : U' ⟶ U` of a pre-relation
`j : R ⟶ U ×_B U` of algebraic spaces over `B` (**Stacks 043D**),
`R' = (U' ×_B U') ×_{U ×_B U} R`, is an algebraic space: it is a fibre product of algebraic
spaces. -/
theorem isAlgebraicSpace_restriction (j : PreRelation (Over.mk qR.hom) (Over.mk qU.hom))
    (g : U' ⟶ U) :
    IsAlgebraicSpace C S hS (PreRelation.restriction j (overHomOfComp qU g)).left := by
  have hprod : ∀ {V : AlgebraicSpaces C S hS} (q : V ⟶ B),
      IsAlgebraicSpace C S hS ((Over.mk q.hom : Over B.obj) ⨯ Over.mk q.hom).left := fun {V} q =>
    (algebraicSpaceProperty C S hS).prop_of_iso
      (Over.prodLeftIsoPullback (Over.mk q.hom) (Over.mk q.hom)).symm
      (isAlgebraicSpace_pullback C S hS q.hom q.hom V.property V.property
        B.property)
  have hsq := (IsPullback.of_hasPullback (prod.map (overHomOfComp qU g) (overHomOfComp qU g))
    j).map (Over.forget B.obj)
  exact (algebraicSpaceProperty C S hS).prop_of_iso hsq.isoPullback.symm
    (isAlgebraicSpace_pullback C S hS _ _ (hprod (g ≫ qU)) R.property (hprod qU))

/-- The arrow space `R' = (U' ×_B U') ×_{U ×_B U} R` of the restriction of a pre-relation
`j : R ⟶ U ×_B U` of algebraic spaces along `g : U' ⟶ U` (**Stacks 043D**), as an algebraic
space. -/
noncomputable def restrictionSpace (j : PreRelation (Over.mk qR.hom) (Over.mk qU.hom))
    (g : U' ⟶ U) : AlgebraicSpaces C S hS :=
  ⟨(PreRelation.restriction j (overHomOfComp qU g)).left, isAlgebraicSpace_restriction j g⟩

/-- The structure morphism to the base of the arrow space of a restricted pre-relation. -/
noncomputable def restrictionSpaceToBase (j : PreRelation (Over.mk qR.hom) (Over.mk qU.hom))
    (g : U' ⟶ U) : restrictionSpace j g ⟶ B :=
  ObjectProperty.homMk (PreRelation.restriction j (overHomOfComp qU g)).hom

/-- The restriction `j' : R' ⟶ U' ×_B U'` of a pre-relation `j : R ⟶ U ×_B U` of algebraic spaces
over `B` along `g : U' ⟶ U` (**Stacks 043D**), read as a pre-relation of algebraic spaces: it is
`AlgebraicGeometry.Space.PreRelation.restrict j g`, its arrow space being the algebraic space
`restrictionSpace j g`. -/
noncomputable abbrev restrictSpace (j : PreRelation (Over.mk qR.hom) (Over.mk qU.hom))
    (g : U' ⟶ U) :
    PreRelation (Over.mk (restrictionSpaceToBase j g).hom) (Over.mk (g ≫ qU).hom) :=
  PreRelation.restrict j (overHomOfComp qU g)

/-- **Stacks 043D.** The restriction of an equivalence relation of algebraic spaces is an
equivalence relation. -/
instance isEquivalenceRelation_restrictSpace (j : PreRelation (Over.mk qR.hom) (Over.mk qU.hom))
    [IsEquivalenceRelation j.target j.source] (g : U' ⟶ U) :
    IsEquivalenceRelation (restrictSpace j g).target (restrictSpace j g).source :=
  PreRelation.isEquivalenceRelation_restrict j (overHomOfComp qU g)

/-- The pre-relation of the groupoid of an equivalence relation is the relation itself. -/
theorem groupoidPreRelation_groupoidOfIsEquivalenceRelation
    (j : PreRelation (Over.mk qR.hom) (Over.mk qU.hom)) [IsEquivalenceRelation j.target j.source] :
    groupoidPreRelation (groupoidOfIsEquivalenceRelation j) = j :=
  prod.hom_ext (by rw [prod.lift_fst]; rfl) (by rw [prod.lift_snd]; rfl)

/-- **Stacks 044D**, restricting an equivalence relation and then taking its groupoid. Let
`j : R ⟶ U ×_B U` be an equivalence relation of algebraic spaces over `B`, let
`(U, R, s, t, c)` be the groupoid in algebraic spaces it extends to (**Stacks 043Y**), and let
`g : U' ⟶ U` be a morphism of algebraic spaces. The groupoid in algebraic spaces of the
restricted equivalence relation `j' : R' = (U' ×_B U') ×_{U ×_B U} R ⟶ U' ×_B U'`
(**Stacks 043D**) is the restriction `(U, R, s, t, c)|_{U'}` of **Stacks 044C**: there is exactly
one isomorphism of groupoids in algebraic spaces between them which is the identity of `U'` on
objects, and it takes the projection `R' ⟶ R` to the map on arrows of the morphism
`(U, R, s, t, c)|_{U'} ⟶ (U, R, s, t, c)` of **Stacks 044B**. -/
@[stacks 044D "restricting an equivalence relation, then taking its groupoid"]
theorem existsUnique_isomorphism_restrict_groupoidOfIsEquivalenceRelation
    (j : PreRelation (Over.mk qR.hom) (Over.mk qU.hom)) [IsEquivalenceRelation j.target j.source]
    (g : U' ⟶ U) :
    ∃! e : Isomorphism (groupoidOfIsEquivalenceRelation (restrictSpace j g))
        ((groupoidOfIsEquivalenceRelation j).restrict g).groupoid,
      e.hom.toGroupoidHom.mapObjects = 𝟙 U'.obj ∧
        e.hom.toGroupoidHom.mapArrows ≫
            ((groupoidOfIsEquivalenceRelation j).restrict g).hom.toGroupoidHom.mapArrows =
          (pullback.snd (prod.map (overHomOfComp qU g) (overHomOfComp qU g)) j).left := by
  let Gj := groupoidOfIsEquivalenceRelation j
  let H := (Gj.restrict g).groupoid
  let K := groupoidOfIsEquivalenceRelation (restrictSpace j g)
  have hsq : IsPullback (groupoidPreRelation H)
      (Over.homMk (Gj.restrict g).hom.toGroupoidHom.mapArrows (Gj.restrict g).hom.mapArrows_over :
        (Over.mk H.arrowsToBase.hom : Over B.obj) ⟶ Over.mk Gj.arrowsToBase.hom)
      (prod.map (overHomOfComp qU g) (overHomOfComp qU g)) j := by
    have h := isPullback_groupoidPreRelation_restrict Gj g
    rwa [groupoidPreRelation_groupoidOfIsEquivalenceRelation] at h
  let e := hsq.isoPullback
  have : Mono j := ((isEquivalenceRelation_iff_mono_and_isPreEquivalenceRelation j).1
    inferInstance).1
  have hfst : Mono (pullback.fst (prod.map (overHomOfComp qU g) (overHomOfComp qU g)) j) :=
    inferInstance
  have : Mono (groupoidPreRelation K) :=
    (groupoidPreRelation_groupoidOfIsEquivalenceRelation (restrictSpace j g)).symm ▸ hfst
  have hH : groupoidPreRelation H =
      e.hom ≫ pullback.fst (prod.map (overHomOfComp qU g) (overHomOfComp qU g)) j :=
    hsq.isoPullback_hom_fst.symm
  have : Mono (groupoidPreRelation H) := hH ▸ @mono_comp _ _ _ _ _ e.hom inferInstance _ hfst
  have hinv : e.inv ≫ groupoidPreRelation H =
      pullback.fst (prod.map (overHomOfComp qU g) (overHomOfComp qU g)) j :=
    (Iso.inv_comp_eq e).2 hH
  let ψ : K.arrows ≅ H.arrows :=
    { hom := ObjectProperty.homMk e.inv.left
      inv := ObjectProperty.homMk e.hom.left
      hom_inv_id := ObjectProperty.hom_ext _ (congrArg (fun k => k.left) e.inv_hom_id)
      inv_hom_id := ObjectProperty.hom_ext _ (congrArg (fun k => k.left) e.hom_inv_id) }
  have hs : ψ.hom ≫ H.source = K.source ≫ (Iso.refl U').hom := by
    refine ObjectProperty.hom_ext _ ?_
    have h := congrArg (· ≫ prod.snd) hinv
    simp only [Category.assoc, prod.lift_snd] at h
    exact (congrArg Over.Hom.left h).trans (Category.comp_id _).symm
  have ht : ψ.hom ≫ H.target = K.target ≫ (Iso.refl U').hom := by
    refine ObjectProperty.hom_ext _ ?_
    have h := congrArg (· ≫ prod.fst) hinv
    simp only [Category.assoc, prod.lift_fst] at h
    exact (congrArg Over.Hom.left h).trans (Category.comp_id _).symm
  let e₀ : Isomorphism K H := Isomorphism.ofMono (Iso.refl U') ψ hs ht
    (Category.id_comp _) (ObjectProperty.hom_ext _ (Over.w e.inv))
  refine ⟨e₀, ⟨rfl, ?_⟩, fun e' he' => Isomorphism.ext_of_hom (he'.1.trans rfl) ?_⟩
  · exact congrArg Over.Hom.left ((Iso.inv_comp_eq e).2 hsq.isoPullback_hom_snd.symm)
  · ext T a
    refine section_eq_of_mono H ?_ ?_
    · refine (e'.hom.toGroupoidHom.map_source T a).trans ?_
      rw [he'.1]
      exact (e₀.hom.toGroupoidHom.map_source T a).symm
    · refine (e'.hom.toGroupoidHom.map_target T a).trans ?_
      rw [he'.1]
      exact (e₀.hom.toGroupoidHom.map_target T a).symm

end AlgebraicGeometry.Space

end
