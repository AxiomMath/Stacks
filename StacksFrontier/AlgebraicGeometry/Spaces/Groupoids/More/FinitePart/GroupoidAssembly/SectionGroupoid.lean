module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.GroupoidComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.GroupoidAssembly.TargetIdentities

/-!
# The finite part of a groupoid in algebraic spaces is a groupoid

Let `(U, R, s, t, c, e, i)` be a groupoid in algebraic spaces over `B` whose source and target
are separated and locally of finite type, and let `(U', Z_univ, s', t', c', e', i')` be the
structure spaces and structure morphisms of its finite part, built in
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/More/FinitePart/GroupoidStructure.lean` and
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/More/FinitePart/GroupoidComposition.lean`
(Stacks 04RU, clauses (1), (2) and part of (3)). This is the last of the three parts which
complete clause (3) of Stacks 04RU (the first two are `ArrowComposition.lean` and
`TargetIdentities.lean`, in
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/More/FinitePart/GroupoidAssembly/`): the
evaluation of `(U', Z_univ, s', t', c')` at every test scheme is a groupoid, so those data
assemble into an `AlgebraicGeometry.GroupoidInAlgebraicSpaces` over `B`, and the étale
projection `g : U' ⟶ U` together with the map `Z_univ ⟶ R` on arrows assemble into an
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.Hom` to the given groupoid, which is the canonical
morphism of groupoids of Stacks 04RU.

With `t' ∘ c' = t' ∘ pr₁` and `t' ∘ e' = 𝟙` proved in `TargetIdentities.lean`, the remaining
identity `t' ∘ i' = s'` is formal: for a section `z` of `Z_univ` the composite `c'(z, i'(z))`
has the same source and the same arrow as `e'(s'(z))`, hence equals it because a section of
`Z_univ` is determined by its source and its arrow, and applying `t'` to that equality gives
`t'(i'(z)) = t'(c'(z, i'(z))) = t'(e'(s'(z))) = s'(z)`.

## Main definitions

* `AlgebraicGeometry.Space.FinitePartUniversalOpen.compAt`: the composition `c'` of the finite
  part read on a composable pair of sections of `Z_univ` over a test scheme.
* `AlgebraicGeometry.Space.FinitePartUniversalOpen.groupoid`: **Stacks 04RU, clause (3)**, the
  finite part `(U', Z_univ, s', t', c')` as an
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces` over `B`.
* `AlgebraicGeometry.Space.FinitePartUniversalOpen.hom`: **Stacks 04RU, clause (3)**, the
  canonical morphism of groupoids from the finite part to the given groupoid, as an
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.Hom` (Stacks 043W, part (2)).

## Main results

* `AlgebraicGeometry.Space.FinitePartUniversalOpen.inverseMap_comp_target`: `t' ∘ i' = s'`.
* `AlgebraicGeometry.Space.FinitePartUniversalOpen.compAt_assoc`,
  `AlgebraicGeometry.Space.FinitePartUniversalOpen.compAt_unit_right`,
  `AlgebraicGeometry.Space.FinitePartUniversalOpen.compAt_unit_left`,
  `AlgebraicGeometry.Space.FinitePartUniversalOpen.compAt_inverse_left` and
  `AlgebraicGeometry.Space.FinitePartUniversalOpen.compAt_inverse_right`: the groupoid
  identities of `c'` read on sections.
* `AlgebraicGeometry.Space.FinitePartUniversalOpen.pointwiseGroupoid`: the pointwise groupoid
  condition, which is the tenth and last field of
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces` for the finite part.
* `AlgebraicGeometry.Space.FinitePartUniversalOpen.arrows_ext`: a section of `Z_univ` is
  determined by its source and its arrow.

## Implementation notes

Everything is carried by the data of a `AlgebraicGeometry.Space.FinitePartUniversalOpen G`, as
in the modules it continues: **no separatedness, finite type or étaleness hypothesis appears**.
No further hypothesis is carried by any declaration here.

`AlgebraicGeometry.Space.FinitePartUniversalOpen.arrows_ext` is what makes the element-level
groupoid identities cheap: `Z_univ` is an open subspace of `R ×_{s, U, g} U'`, so a section of
it is determined by the pair `(s'(y), z(y))` of its two projections, and each identity of `c'`
reduces to the corresponding identity of `c` together with the computation of the source.

The pointwise groupoid is built with `Equiv.refl` as its `arrowEquiv`: the arrows of the
category put on the sections of `U'` over a test scheme are *by definition* the sections of
`Z_univ` with prescribed source and target, and composition is *by definition*
`AlgebraicGeometry.Space.FinitePartUniversalOpen.compAt`, which is the composition the
structure's `pointwiseGroupoid` field asks about; so the `comp_eq` field holds by `rfl` and
nothing is transported.

`map_id` of the morphism of groupoids is not proved by hand: the identity arrow of an evaluated
groupoid is defined through a chosen witness of the pointwise groupoid condition, which need
not be the witness constructed here, so it is obtained from `map_source`, `map_target` and
`map_comp` by `AlgebraicGeometry.Space.mapIdentityOfMapComp`.

### What is not reached

The groupoid and its morphism are assembled, so all ten fields of
`AlgebraicGeometry.GroupoidInAlgebraicSpaces` and all five fields of
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.Hom` are available for the finite part. Not
addressed here are the remaining assertions attached to Stacks 04RU and 04RT beyond clause (3)
of 04RU: that the projection `g : U' ⟶ U` is étale and that `s'` is finite are proved in the
earlier modules and are not re-expressed as properties of
`AlgebraicGeometry.Space.FinitePartUniversalOpen.groupoid`; the uniqueness of the finite part,
the general form of Stacks 04RT for an arbitrary pair and an arbitrary arrow, and the
consequences drawn in Stacks 03FM and 0DTC are not touched.

## References

* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 04RT](https://stacks.math.columbia.edu/tag/04RT)
* [Stacks Project, Tag 04RU](https://stacks.math.columbia.edu/tag/04RU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace AlgebraicGeometry.Space

/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance (priority := high) hasPullbacks_presheaf_sectionGroupoid
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    HasPullbacks ((AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_sectionGroupoid
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (hasPullbacks_presheaf_sectionGroupoid B S hS).has_limit _

namespace FinitePartUniversalOpen

variable {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicGeometry.AlgebraicSpaces C S hS}
  {G : AlgebraicGeometry.GroupoidInAlgebraicSpaces C S hS B}

/-! ### The composition read on sections -/

/-- The composite of two composable sections of the arrow space of the finite part: the
composition `c'` applied to the pair they form. -/
public def compAt (F : FinitePartUniversalOpen G)
    (T : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ) (a b : F.arrows.obj.obj T)
    (h : F.source.hom.app T a = F.target.hom.app T b) : F.arrows.obj.obj T :=
  (AlgebraicGeometry.composableToPullback F.source.hom F.target.hom ≫ F.comp.hom).app T
    (⟨(a, b), h⟩ : (Deformation.composableArrows F.objects.obj F.arrows.obj
      F.source.hom F.target.hom).obj T)

/-- The first entry of the composable pair underlying a composite. -/
private theorem composable_fst (F : FinitePartUniversalOpen G)
    (T : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ) (a b : F.arrows.obj.obj T)
    (h : F.source.hom.app T a = F.target.hom.app T b) :
    (pullback.fst F.source.hom F.target.hom).app T
      ((AlgebraicGeometry.composableToPullback F.source.hom F.target.hom).app T
        (⟨(a, b), h⟩ : (Deformation.composableArrows F.objects.obj F.arrows.obj
          F.source.hom F.target.hom).obj T)) = a := by
  change (AlgebraicGeometry.composableToPullback F.source.hom F.target.hom ≫
    pullback.fst F.source.hom F.target.hom).app T _ = a
  rw [AlgebraicGeometry.composableToPullback, pullback.lift_fst]
  rfl

/-- The second entry of the composable pair underlying a composite. -/
private theorem composable_snd (F : FinitePartUniversalOpen G)
    (T : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ) (a b : F.arrows.obj.obj T)
    (h : F.source.hom.app T a = F.target.hom.app T b) :
    (pullback.snd F.source.hom F.target.hom).app T
      ((AlgebraicGeometry.composableToPullback F.source.hom F.target.hom).app T
        (⟨(a, b), h⟩ : (Deformation.composableArrows F.objects.obj F.arrows.obj
          F.source.hom F.target.hom).obj T)) = b := by
  change (AlgebraicGeometry.composableToPullback F.source.hom F.target.hom ≫
    pullback.snd F.source.hom F.target.hom).app T _ = b
  rw [AlgebraicGeometry.composableToPullback, pullback.lift_snd]
  rfl

/-- The source of a composite of sections is the source of its second entry. -/
public theorem compAt_source (F : FinitePartUniversalOpen G)
    (T : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ) (a b : F.arrows.obj.obj T)
    (h : F.source.hom.app T a = F.target.hom.app T b) :
    F.source.hom.app T (F.compAt T a b h) = F.source.hom.app T b := by
  have e := congrArg (fun z => z.app T
    ((AlgebraicGeometry.composableToPullback F.source.hom F.target.hom).app T
      (⟨(a, b), h⟩ : (Deformation.composableArrows F.objects.obj F.arrows.obj
        F.source.hom F.target.hom).obj T))) F.comp_hom_comp_source
  exact e.trans (congrArg (fun z => F.source.hom.app T z) (F.composable_snd T a b h))

/-- The target of a composite of sections is the target of its first entry. -/
public theorem compAt_target (F : FinitePartUniversalOpen G)
    (T : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ) (a b : F.arrows.obj.obj T)
    (h : F.source.hom.app T a = F.target.hom.app T b) :
    F.target.hom.app T (F.compAt T a b h) = F.target.hom.app T a := by
  have e := congrArg (fun z => z.app T
    ((AlgebraicGeometry.composableToPullback F.source.hom F.target.hom).app T
      (⟨(a, b), h⟩ : (Deformation.composableArrows F.objects.obj F.arrows.obj
        F.source.hom F.target.hom).obj T))) F.comp_hom_comp_target
  exact e.trans (congrArg (fun z => F.target.hom.app T z) (F.composable_fst T a b h))

/-- The arrow of a composite of sections is the composite of the arrows. -/
public theorem compAt_arrowMap (F : FinitePartUniversalOpen G)
    (T : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ) (a b : F.arrows.obj.obj T)
    (h : F.source.hom.app T a = F.target.hom.app T b)
    (hc : G.source.hom.app T (F.arrowMap.hom.app T a) =
      G.target.hom.app T (F.arrowMap.hom.app T b)) :
    F.arrowMap.hom.app T (F.compAt T a b h) =
      G.toGroupoidInFunctors.compose T (F.arrowMap.hom.app T a)
        (F.arrowMap.hom.app T b) hc := by
  refine (F.comp_arrowMap_app T _).trans ?_
  exact compose_congr G T _ _ _ _ (F.comp_composable_app T _) hc
    (congrArg (fun z => F.arrowMap.hom.app T z) (F.composable_fst T a b h))
    (congrArg (fun z => F.arrowMap.hom.app T z) (F.composable_snd T a b h))

/-! ### The unit, the inverse and the projections read on sections -/

/-- The source of the unit of the finite part at a point of the object space is that point. -/
public theorem unitMap_source_app (F : FinitePartUniversalOpen G)
    (T : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ) (x : F.objects.obj.obj T) :
    F.source.hom.app T (F.unitMap.hom.app T x) = x :=
  congrArg (fun z : F.objects ⟶ F.objects => z.hom.app T x) F.unitMap_comp_source

/-- The target of the unit of the finite part at a point of the object space is that point. -/
public theorem unitMap_target_app (F : FinitePartUniversalOpen G)
    (T : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ) (x : F.objects.obj.obj T) :
    F.target.hom.app T (F.unitMap.hom.app T x) = x :=
  congrArg (fun z : F.objects ⟶ F.objects => z.hom.app T x) F.unitMap_comp_target

/-- The arrow of the unit of the finite part is the identity arrow at the image of the point
under the projection on objects. -/
public theorem unitMap_arrowMap_app (F : FinitePartUniversalOpen G)
    (T : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ) (x : F.objects.obj.obj T) :
    F.arrowMap.hom.app T (F.unitMap.hom.app T x) =
      G.toGroupoidInFunctors.identity T (F.objectProjection.hom.app T x) := by
  have e := congrArg (fun z : F.objects ⟶ G.arrows => z.hom.app T x)
    F.unitMap_comp_arrowMap
  refine e.trans ?_
  change F.unit.hom.app T (F.universalOpen.toBase.hom.app T x) = _
  rw [F.unit_identity]
  exact congrArg (fun z => G.toGroupoidInFunctors.identity T z)
    (congrArg (fun z => z.app T x) F.universalOpen_toBase_hom)

/-- The source of the inverse of a section of the arrow space of the finite part is its
target. -/
public theorem inverseMap_source_app (F : FinitePartUniversalOpen G)
    (T : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ) (a : F.arrows.obj.obj T) :
    F.source.hom.app T (F.inverseMap.hom.app T a) = F.target.hom.app T a :=
  congrArg (fun z : F.arrows ⟶ F.objects => z.hom.app T a) F.inverseMap_comp_source

/-- The arrow of the inverse of a section of the arrow space of the finite part is the inverse
of its arrow. -/
public theorem inverseMap_arrowMap_app (F : FinitePartUniversalOpen G)
    (T : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ) (a : F.arrows.obj.obj T) :
    F.arrowMap.hom.app T (F.inverseMap.hom.app T a) =
      Deformation.inverseArrow G.toGroupoidInFunctors T (F.arrowMap.hom.app T a) :=
  (congrArg (fun z => z.app T a) F.inverseMap_comp_arrowMap).trans
    (inverseHom_app G T (F.arrowMap.hom.app T a))

/-- The projection on objects of the source of a section of the arrow space is the source of
its arrow. -/
public theorem objectProjection_source_app (F : FinitePartUniversalOpen G)
    (T : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ) (a : F.arrows.obj.obj T) :
    F.objectProjection.hom.app T (F.source.hom.app T a) =
      G.source.hom.app T (F.arrowMap.hom.app T a) :=
  (congrArg (fun z : F.arrows ⟶ G.objects => z.hom.app T a) F.arrowMap_comp_source).symm

/-- The projection on objects of the target of a section of the arrow space is the target of
its arrow. -/
public theorem objectProjection_target_app (F : FinitePartUniversalOpen G)
    (T : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ) (a : F.arrows.obj.obj T) :
    F.objectProjection.hom.app T (F.target.hom.app T a) =
      G.target.hom.app T (F.arrowMap.hom.app T a) :=
  (congrArg (fun z : F.arrows ⟶ G.objects => z.hom.app T a) F.arrowMap_comp_target).symm

/-- Two sections of the arrow space of the finite part with the same source and the same arrow
are equal: the arrow space is an open subspace of `R ×_{s, U, g} U'` and those are the two
projections. -/
public theorem arrows_ext (F : FinitePartUniversalOpen G)
    (T : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ) (x y : F.arrows.obj.obj T)
    (hs : F.source.hom.app T x = F.source.hom.app T y)
    (ha : F.arrowMap.hom.app T x = F.arrowMap.hom.app T y) : x = y := by
  have h : F.arrowsInclusion.app T x = F.arrowsInclusion.app T y := by
    refine pullback_obj_ext F.universalOpen.toBase.hom G.source.hom T _ _ ?_ ?_
    · exact ((congrArg (fun z => z.app T x) F.source_hom_eq).symm.trans hs).trans
        (congrArg (fun z => z.app T y) F.source_hom_eq)
    · exact ((congrArg (fun z => z.app T x) F.arrowMap_hom_eq).symm.trans ha).trans
        (congrArg (fun z => z.app T y) F.arrowMap_hom_eq)
  exact Subtype.ext h

/-! ### The groupoid identities of the composition read on sections -/

/-- Sections with equal source and target have arrows with equal source and target. -/
private theorem arrowMap_source_eq_target (F : FinitePartUniversalOpen G)
    (T : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ) {a b : F.arrows.obj.obj T}
    (h : F.source.hom.app T a = F.target.hom.app T b) :
    G.source.hom.app T (F.arrowMap.hom.app T a) =
      G.target.hom.app T (F.arrowMap.hom.app T b) := by
  rw [← F.objectProjection_source_app, ← F.objectProjection_target_app]
  exact congrArg (fun z => F.objectProjection.hom.app T z) h

/-- Composing a section of the arrow space of the finite part with the unit at its source
returns that section. -/
public theorem compAt_unit_right (F : FinitePartUniversalOpen G)
    (T : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ) (a : F.arrows.obj.obj T)
    (x : F.objects.obj.obj T) (hx : F.source.hom.app T a = x)
    (h : F.source.hom.app T a = F.target.hom.app T (F.unitMap.hom.app T x)) :
    F.compAt T a (F.unitMap.hom.app T x) h = a := by
  have ham : F.arrowMap.hom.app T (F.unitMap.hom.app T x) =
      G.toGroupoidInFunctors.identity T
        (G.source.hom.app T (F.arrowMap.hom.app T a)) := by
    rw [F.unitMap_arrowMap_app, ← hx, F.objectProjection_source_app]
  have hc' : G.source.hom.app T (F.arrowMap.hom.app T a) =
      G.target.hom.app T (G.toGroupoidInFunctors.identity T
        (G.source.hom.app T (F.arrowMap.hom.app T a))) := by
    rw [target_identity_app]
  have hc : G.source.hom.app T (F.arrowMap.hom.app T a) =
      G.target.hom.app T (F.arrowMap.hom.app T (F.unitMap.hom.app T x)) := by
    rw [ham]; exact hc'
  refine F.arrows_ext T _ _ ?_ ?_
  · rw [F.compAt_source, F.unitMap_source_app, hx]
  · rw [F.compAt_arrowMap T a _ h hc]
    exact (compose_congr G T _ _ _ _ hc hc' rfl ham).trans
      (compose_identity_right_app G T (F.arrowMap.hom.app T a) hc')

/-- Composing the unit at the target of a section of the arrow space of the finite part with
that section returns it. -/
public theorem compAt_unit_left (F : FinitePartUniversalOpen G)
    (T : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ) (a : F.arrows.obj.obj T)
    (y : F.objects.obj.obj T) (hy : F.target.hom.app T a = y)
    (h : F.source.hom.app T (F.unitMap.hom.app T y) = F.target.hom.app T a) :
    F.compAt T (F.unitMap.hom.app T y) a h = a := by
  have ham : F.arrowMap.hom.app T (F.unitMap.hom.app T y) =
      G.toGroupoidInFunctors.identity T
        (G.target.hom.app T (F.arrowMap.hom.app T a)) := by
    rw [F.unitMap_arrowMap_app, ← hy, F.objectProjection_target_app]
  have hc' : G.source.hom.app T (G.toGroupoidInFunctors.identity T
        (G.target.hom.app T (F.arrowMap.hom.app T a))) =
      G.target.hom.app T (F.arrowMap.hom.app T a) := by
    rw [source_identity_app]
  have hc : G.source.hom.app T (F.arrowMap.hom.app T (F.unitMap.hom.app T y)) =
      G.target.hom.app T (F.arrowMap.hom.app T a) := by
    rw [ham]; exact hc'
  refine F.arrows_ext T _ _ ?_ ?_
  · rw [F.compAt_source]
  · rw [F.compAt_arrowMap T _ a h hc]
    exact (compose_congr G T _ _ _ _ hc hc' ham rfl).trans
      (compose_identity_app G T (F.arrowMap.hom.app T a) hc')

/-- **Associativity of the composition of the finite part**, read on sections. -/
public theorem compAt_assoc (F : FinitePartUniversalOpen G)
    (T : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ) (a b d : F.arrows.obj.obj T)
    (hab : F.source.hom.app T a = F.target.hom.app T b)
    (hbd : F.source.hom.app T b = F.target.hom.app T d)
    (h₁ : F.source.hom.app T (F.compAt T a b hab) = F.target.hom.app T d)
    (h₂ : F.source.hom.app T a = F.target.hom.app T (F.compAt T b d hbd)) :
    F.compAt T (F.compAt T a b hab) d h₁ = F.compAt T a (F.compAt T b d hbd) h₂ := by
  have hcab := F.arrowMap_source_eq_target T hab
  have hcbd := F.arrowMap_source_eq_target T hbd
  have hc₁ := F.arrowMap_source_eq_target T h₁
  have hc₂ := F.arrowMap_source_eq_target T h₂
  have e₁ : G.source.hom.app T (G.toGroupoidInFunctors.compose T
        (F.arrowMap.hom.app T a) (F.arrowMap.hom.app T b) hcab) =
      G.target.hom.app T (F.arrowMap.hom.app T d) := by
    rw [← F.compAt_arrowMap T a b hab hcab]; exact hc₁
  have e₂ : G.source.hom.app T (F.arrowMap.hom.app T a) =
      G.target.hom.app T (G.toGroupoidInFunctors.compose T
        (F.arrowMap.hom.app T b) (F.arrowMap.hom.app T d) hcbd) := by
    rw [← F.compAt_arrowMap T b d hbd hcbd]; exact hc₂
  refine F.arrows_ext T _ _ ?_ ?_
  · simp only [F.compAt_source]
  · rw [F.compAt_arrowMap T _ d h₁ hc₁, F.compAt_arrowMap T a _ h₂ hc₂]
    refine (compose_congr G T _ _ _ _ hc₁ e₁
      (F.compAt_arrowMap T a b hab hcab) rfl).trans ?_
    refine (compose_assoc_app G T (F.arrowMap.hom.app T a) (F.arrowMap.hom.app T b)
      (F.arrowMap.hom.app T d) hcab hcbd e₁ e₂).trans ?_
    exact compose_congr G T _ _ _ _ e₂ hc₂ rfl
      (F.compAt_arrowMap T b d hbd hcbd).symm

/-- Composing a section of the arrow space of the finite part with its inverse returns the
unit at its target. -/
public theorem compAt_inverse_left (F : FinitePartUniversalOpen G)
    (T : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ) (a : F.arrows.obj.obj T)
    (h : F.source.hom.app T a =
      F.target.hom.app T (F.inverseMap.hom.app T a)) :
    F.compAt T a (F.inverseMap.hom.app T a) h =
      F.unitMap.hom.app T (F.target.hom.app T a) := by
  have hinv : G.source.hom.app T (F.arrowMap.hom.app T a) =
      G.target.hom.app T (F.arrowMap.hom.app T (F.inverseMap.hom.app T a)) := by
    rw [F.inverseMap_arrowMap_app]
    exact (inverseArrow_app_target G T (F.arrowMap.hom.app T a)).symm
  refine F.arrows_ext T _ _ ?_ ?_
  · rw [F.compAt_source, F.unitMap_source_app, F.inverseMap_source_app]
  · rw [F.compAt_arrowMap T a _ h hinv, F.unitMap_arrowMap_app,
      F.objectProjection_target_app]
    refine (compose_congr G T _ _ _ _ hinv
      (inverseArrow_app_target G T (F.arrowMap.hom.app T a)).symm rfl
      (F.inverseMap_arrowMap_app T a)).trans ?_
    exact compose_self_inverseArrow_app G T (F.arrowMap.hom.app T a)
      (inverseArrow_app_target G T (F.arrowMap.hom.app T a)).symm

/-- Composing the inverse of a section of the arrow space of the finite part with that section
returns the unit at its source. -/
public theorem compAt_inverse_right (F : FinitePartUniversalOpen G)
    (T : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ) (a : F.arrows.obj.obj T)
    (h : F.source.hom.app T (F.inverseMap.hom.app T a) =
      F.target.hom.app T a) :
    F.compAt T (F.inverseMap.hom.app T a) a h =
      F.unitMap.hom.app T (F.source.hom.app T a) := by
  have hinv : G.source.hom.app T (F.arrowMap.hom.app T (F.inverseMap.hom.app T a)) =
      G.target.hom.app T (F.arrowMap.hom.app T a) := by
    rw [F.inverseMap_arrowMap_app]
    exact inverseArrow_app_source G T (F.arrowMap.hom.app T a)
  refine F.arrows_ext T _ _ ?_ ?_
  · rw [F.compAt_source, F.unitMap_source_app]
  · rw [F.compAt_arrowMap T _ a h hinv, F.unitMap_arrowMap_app,
      F.objectProjection_source_app]
    refine (compose_congr G T _ _ _ _ hinv
      (inverseArrow_app_source G T (F.arrowMap.hom.app T a))
      (F.inverseMap_arrowMap_app T a) rfl).trans ?_
    exact compose_inverseArrow_app G T (F.arrowMap.hom.app T a)
      (inverseArrow_app_source G T (F.arrowMap.hom.app T a))

/-! ### The target of the inverse -/

/-- **Stacks 04RU, clause (3).** `t' ∘ i' = s'`: the inverse of the finite part exchanges the
source and the target. -/
public theorem inverseMap_comp_target (F : FinitePartUniversalOpen G) :
    F.inverseMap ≫ F.target = F.source := by
  apply ObjectProperty.hom_ext
  ext T a
  change F.target.hom.app T (F.inverseMap.hom.app T a) = F.source.hom.app T a
  calc F.target.hom.app T (F.inverseMap.hom.app T a)
      = F.target.hom.app T
          (F.compAt T (F.inverseMap.hom.app T a) a (F.inverseMap_source_app T a)) :=
        (F.compAt_target T _ _ (F.inverseMap_source_app T a)).symm
    _ = F.target.hom.app T (F.unitMap.hom.app T (F.source.hom.app T a)) := by
          rw [F.compAt_inverse_right T a (F.inverseMap_source_app T a)]
    _ = F.source.hom.app T a := F.unitMap_target_app T _

/-- The target of the inverse of a section of the arrow space of the finite part is its
source. -/
public theorem inverseMap_target_app (F : FinitePartUniversalOpen G)
    (T : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ) (a : F.arrows.obj.obj T) :
    F.target.hom.app T (F.inverseMap.hom.app T a) = F.source.hom.app T a :=
  congrArg (fun z : F.arrows ⟶ F.objects => z.hom.app T a) F.inverseMap_comp_target

/-! ### The pointwise groupoid, the groupoid and the morphism of groupoids -/

/-- **Stacks 04RU, clause (3).** At every test scheme the sections of the object space of the
finite part, together with the sections of its arrow space with prescribed source and target,
form a groupoid whose composition is the composition `c'` of the finite part. -/
public theorem pointwiseGroupoid (F : FinitePartUniversalOpen G)
    (T : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ) :
    Nonempty (Deformation.PointwiseGroupoid (F.source.hom.app T) (F.target.hom.app T)
      (fun p => (AlgebraicGeometry.composableToPullback F.source.hom F.target.hom ≫
        F.comp.hom).app T p)) := by
  let _cat : Category.{u} (F.objects.obj.obj T) :=
    { Hom := fun x y => {a : F.arrows.obj.obj T //
        F.source.hom.app T a = x ∧ F.target.hom.app T a = y}
      id := fun x => ⟨F.unitMap.hom.app T x, F.unitMap_source_app T x,
        F.unitMap_target_app T x⟩
      comp := fun {_ _ _} f g => ⟨F.compAt T g.1 f.1 (g.2.1.trans f.2.2.symm),
        (F.compAt_source T g.1 f.1 _).trans f.2.1,
        (F.compAt_target T g.1 f.1 _).trans g.2.2⟩
      id_comp := fun {x _} f => Subtype.ext
        (F.compAt_unit_right T f.1 x f.2.1 _)
      comp_id := fun {_ y} f => Subtype.ext
        (F.compAt_unit_left T f.1 y f.2.2 _)
      assoc := fun {_ _ _ _} f g k => Subtype.ext
        (F.compAt_assoc T k.1 g.1 f.1 _ _ _ _).symm }
  let _grp : Groupoid.{u} (F.objects.obj.obj T) :=
    { inv := fun {_ _} f => ⟨F.inverseMap.hom.app T f.1,
        (F.inverseMap_source_app T f.1).trans f.2.2,
        (F.inverseMap_target_app T f.1).trans f.2.1⟩
      inv_comp := fun {_ y} f => Subtype.ext
        ((F.compAt_inverse_left T f.1 _).trans
          (congrArg (fun z => F.unitMap.hom.app T z) f.2.2))
      comp_inv := fun {x _} f => Subtype.ext
        ((F.compAt_inverse_right T f.1 _).trans
          (congrArg (fun z => F.unitMap.hom.app T z) f.2.1)) }
  exact ⟨{ groupoid := _grp
           arrowEquiv := fun _ _ => Equiv.refl _
           comp_eq := fun _ _ => rfl }⟩

/-- **Stacks 04RU, clause (3).** The finite part of a groupoid in algebraic spaces whose source
and target are separated and locally of finite type is itself a groupoid in algebraic spaces
over the same base: the object space `U'`, the arrow space `Z_univ`, the source `s'`, the
target `t'` and the composition `c'`. -/
public def groupoid (F : FinitePartUniversalOpen G) :
    AlgebraicGeometry.GroupoidInAlgebraicSpaces C S hS B where
  objects := F.objects
  arrows := F.arrows
  objectsToBase := F.objectsToBase
  arrowsToBase := F.arrowsToBase
  source := F.source
  target := F.target
  source_over := F.source_over
  target_over := F.target_over
  comp := F.comp
  comp_over := F.comp_over
  pointwiseGroupoid := F.pointwiseGroupoid

/-- The map on objects of the canonical morphism of groupoids respects the source. -/
public theorem groupoid_map_source (F : FinitePartUniversalOpen G)
    (T : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ)
    (a : F.groupoid.toGroupoidInFunctors.arrows.obj T) :
    G.toGroupoidInFunctors.source.app T (F.arrowMap.hom.app T a) =
      F.objectProjection.hom.app T
        (F.groupoid.toGroupoidInFunctors.source.app T a) :=
  congrArg (fun z : F.arrows ⟶ G.objects => z.hom.app T a) F.arrowMap_comp_source

/-- The map on objects of the canonical morphism of groupoids respects the target. -/
public theorem groupoid_map_target (F : FinitePartUniversalOpen G)
    (T : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ)
    (a : F.groupoid.toGroupoidInFunctors.arrows.obj T) :
    G.toGroupoidInFunctors.target.app T (F.arrowMap.hom.app T a) =
      F.objectProjection.hom.app T
        (F.groupoid.toGroupoidInFunctors.target.app T a) :=
  congrArg (fun z : F.arrows ⟶ G.objects => z.hom.app T a) F.arrowMap_comp_target

/-- The canonical morphism of groupoids respects the composition. -/
public theorem groupoid_map_comp (F : FinitePartUniversalOpen G)
    (T : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ)
    (a b : F.groupoid.toGroupoidInFunctors.arrows.obj T)
    (h : F.groupoid.toGroupoidInFunctors.source.app T a =
      F.groupoid.toGroupoidInFunctors.target.app T b) :
    G.toGroupoidInFunctors.compose T (F.arrowMap.hom.app T a) (F.arrowMap.hom.app T b)
        ((F.groupoid_map_source T a).trans
          ((congrArg (F.objectProjection.hom.app T) h).trans
            (F.groupoid_map_target T b).symm)) =
      F.arrowMap.hom.app T (F.groupoid.toGroupoidInFunctors.compose T a b h) :=
  (F.compAt_arrowMap T a b h _).symm

/-- **Stacks 04RU, clause (3), and Stacks 043W, part (2).** The canonical morphism of groupoids
in algebraic spaces from the finite part `(U', Z_univ, s', t', c')` to the given groupoid
`(U, R, s, t, c)`: the étale projection `g : U' ⟶ U` on objects and the map `Z_univ ⟶ R` on
arrows. -/
public def hom (F : FinitePartUniversalOpen G) :
    AlgebraicGeometry.GroupoidInAlgebraicSpaces.Hom F.groupoid G where
  toGroupoidHom :=
    { mapObjects := F.objectProjection.hom
      mapArrows := F.arrowMap.hom
      map_source := F.groupoid_map_source
      map_target := F.groupoid_map_target
      map_id := AlgebraicGeometry.Space.mapIdentityOfMapComp
        (G := F.groupoid.toGroupoidInFunctors) (H := G.toGroupoidInFunctors)
        F.objectProjection.hom F.arrowMap.hom F.groupoid_map_source
        F.groupoid_map_target F.groupoid_map_comp
      map_comp := F.groupoid_map_comp }
  mapObjects_over := rfl
  mapArrows_over := rfl

end FinitePartUniversalOpen

end AlgebraicGeometry.Space

end
