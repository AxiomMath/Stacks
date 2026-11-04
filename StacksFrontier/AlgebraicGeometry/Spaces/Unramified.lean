module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Properties
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.Defs
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.Points

/-!
# Unramified and universally injective morphisms of algebraic spaces

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`, that is a morphism of
presheaves on the big fppf site of `S`. Following [Stacks Project, Tag 03ZH], `f` is
*unramified*, respectively *G-unramified*, when the scheme morphism underlying every commuting
square of étale scheme charts of it is unramified, respectively G-unramified; and it has either
property *at* a point of its source when it has that property on some open subspace of the
source containing the point. This file also records universal injectivity of `f`.

Unramifiedness, universal injectivity and formal unramifiedness are exactly the ingredients of
the characterization of a morphism which is both unramified and a monomorphism,
[Stacks Project, Tag 05W6]: there, `f` is unramified and a monomorphism if and only if it is
unramified and universally injective, if and only if it is locally of finite type and a
monomorphism, if and only if it is universally injective, locally of finite type and formally
unramified.

## Main definitions

* `AlgebraicGeometry.Space.IsUnramified`: **Stacks 03ZH**, part (1).
* `AlgebraicGeometry.Space.IsUnramifiedAt`: **Stacks 03ZH**, part (2).
* `AlgebraicGeometry.Space.IsGUnramified`: **Stacks 03ZH**, part (3).
* `AlgebraicGeometry.Space.IsGUnramifiedAt`: **Stacks 03ZH**, part (4).
* `AlgebraicGeometry.Space.UniversallyInjective` — defined in
  `StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/UniversallyInjective.lean`, not here —
  is universal injectivity of `f`: every base change of `f` along a morphism from an algebraic
  space induces an injective map on points.

## Main results

* `AlgebraicGeometry.Space.isLocallyOfFiniteType_of_isUnramified`: **Stacks 05VZ**, an
  unramified morphism of algebraic spaces is locally of finite type. This is also the
  local-finite-type half of the implication (1) ⇒ (3) of [Stacks Project, Tag 05W6].
* `AlgebraicGeometry.Space.isUnramifiedAt_of_isOpenSubspace` and
  `AlgebraicGeometry.Space.isGUnramifiedAt_of_isOpenSubspace` are the introduction rules for the
  pointwise conditions: an unramified, respectively G-unramified, open subspace witnesses the
  condition at each of its points.
* `AlgebraicGeometry.Space.IsUnramifiedAt.exists_mem_range_pointsMap` and
  `AlgebraicGeometry.Space.IsGUnramifiedAt.exists_mem_range_pointsMap` restate the pointwise
  definitions with the point condition as a membership in the image of the open subspace on
  points.
* `AlgebraicGeometry.Space.injective_pointsMap_of_universallyInjective`: a universally injective
  morphism onto an algebraic space is injective on points, by taking the base change along the
  identity.
* `AlgebraicGeometry.Space.formallyUnramified_of_mono`: a monomorphism of presheaves is formally
  unramified. This is the formal-unramifiedness half of the implication (3) ⇒ (4) of
  [Stacks Project, Tag 05W6].

## Implementation notes

Parts (1) and (3) of Tag 03ZH are the every-chart condition of Tag 03MJ,
`AlgebraicGeometry.Space.HoldsOnEveryEtaleChart`, applied to the scheme-morphism classes
`AlgebraicGeometry.Unramified` and `AlgebraicGeometry.GUnramified` of Tag 02G4, parts (3) and
(4) — exactly as the sister notion `AlgebraicGeometry.Space.IsSmooth` (Tag 03ZC) is the same
condition at `AlgebraicGeometry.Smooth`; this is condition (1) of Tag 03MJ, which is what
Tag 03ZH takes as the definition. Parts (2) and (4) follow the shape of
`AlgebraicGeometry.Space.IsSmoothAt`: an open subfunctor of the source, in the sense of
Tag 02YU, together with a point of it lying over the given point, and the restriction of the
morphism along the inclusion.

Note that `AlgebraicGeometry.Unramified` here is the scheme-morphism class of Tag 02G4 and
*not* a property of morphisms of algebraic spaces; inside the namespace
`AlgebraicGeometry.Space` it is written `_root_.AlgebraicGeometry.Unramified` to make that
unambiguous, and likewise for `AlgebraicGeometry.GUnramified`.

Namesake warning: `Algebra.IsUnramifiedAt` is the commutative-algebra notion about a prime of a
ring and is unrelated to `AlgebraicGeometry.Space.IsUnramifiedAt`.

Universal injectivity quantifies over algebraic spaces `Y'` over the same base and *all*
morphisms `Y' ⟶ Y`, and the fibre product `Y' ×_Y X` is the categorical pullback of presheaves,
which exists because the target category is `Type u`. The map on points is
`AlgebraicGeometry.Space.pointsMap` of Tag 03BU. Algebraicity of `X` and `Y` is not assumed:
as with the other predicates of this layer, it is imposed by clients.

`AlgebraicGeometry.Space.FormallyUnramified` is not defined here: it stands next to its siblings
`AlgebraicGeometry.Space.FormallySmooth` and `AlgebraicGeometry.Space.FormallyEtale` in
`StacksFrontier/AlgebraicGeometry/Spaces/FormallySmooth/Defs.lean`, so that the three notions of
Tag 049S are stated against literally the same test diagram —
`AlgebraicGeometry.Space.IsSquareZeroClosedImmersion` and `AlgebraicGeometry.Space.IsLift` — and
the composition and base-change statements can be made uniformly in them.

Every definition is an abbreviation, as in the rest of the algebraic-space layer, so that the
chart, pullback and lifting APIs stay exposed without conversion lemmas.

## References

* [Stacks Project, Tag 02G4](https://stacks.math.columbia.edu/tag/02G4)
* [Stacks Project, Tag 03MV](https://stacks.math.columbia.edu/tag/03MV)
* [Stacks Project, Tag 03ZH](https://stacks.math.columbia.edu/tag/03ZH)
* [Stacks Project, Tag 049S](https://stacks.math.columbia.edu/tag/049S)
* [Stacks Project, Tag 05VZ](https://stacks.math.columbia.edu/tag/05VZ)
* [Stacks Project, Tag 05W6](https://stacks.math.columbia.edu/tag/05W6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Chart

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### Unramified morphisms -/

/-- **Stacks 03ZH, part (1).** A morphism of algebraic spaces over `S` is *unramified* when the
scheme morphism in every commuting square of étale scheme charts is unramified. -/
@[stacks 03ZH "part (1): unramified morphisms"]
abbrev IsUnramified (f : X ⟶ Y) : Prop :=
  HoldsOnEveryEtaleChart B S hS
    (@_root_.AlgebraicGeometry.Unramified : MorphismProperty Scheme.{u}) f

/-- **Stacks 03ZH, part (3).** A morphism of algebraic spaces over `S` is *G-unramified* when the
scheme morphism in every commuting square of étale scheme charts is G-unramified. -/
@[stacks 03ZH "part (3): G-unramified morphisms"]
abbrev IsGUnramified (f : X ⟶ Y) : Prop :=
  HoldsOnEveryEtaleChart B S hS
    (@_root_.AlgebraicGeometry.GUnramified : MorphismProperty Scheme.{u}) f

/-- **Stacks 03ZH, part (2).** A morphism of algebraic spaces over `S` is *unramified at* a point
`x` of its source when it is unramified on some open subspace of the source having a point
over `x`. -/
@[stacks 03ZH "part (2): unramified at a point"]
abbrev IsUnramifiedAt (f : X ⟶ Y) (x : points B S hS X) : Prop :=
  ∃ U : Subfunctor X, IsOpenSubspace B S hS U ∧
    ∃ x' : points B S hS U.toFunctor,
      pointsMap B S hS U.toFunctor U.ι x' = x ∧ IsUnramified B S hS (U.ι ≫ f)

/-- **Stacks 03ZH, part (4).** A morphism of algebraic spaces over `S` is *G-unramified at* a
point `x` of its source when it is G-unramified on some open subspace of the source having a
point over `x`. -/
@[stacks 03ZH "part (4): G-unramified at a point"]
abbrev IsGUnramifiedAt (f : X ⟶ Y) (x : points B S hS X) : Prop :=
  ∃ U : Subfunctor X, IsOpenSubspace B S hS U ∧
    ∃ x' : points B S hS U.toFunctor,
      pointsMap B S hS U.toFunctor U.ι x' = x ∧ IsGUnramified B S hS (U.ι ≫ f)

/-- An unramified open subspace of the source witnesses unramifiedness at each of its
points. -/
theorem isUnramifiedAt_of_isOpenSubspace {f : X ⟶ Y} (U : Subfunctor X)
    (hU : IsOpenSubspace B S hS U) (hf : IsUnramified B S hS (U.ι ≫ f))
    (x' : points B S hS U.toFunctor) :
    IsUnramifiedAt B S hS f (pointsMap B S hS U.toFunctor U.ι x') :=
  ⟨U, hU, x', rfl, hf⟩

/-- A G-unramified open subspace of the source witnesses G-unramifiedness at each of its
points. -/
theorem isGUnramifiedAt_of_isOpenSubspace {f : X ⟶ Y} (U : Subfunctor X)
    (hU : IsOpenSubspace B S hS U) (hf : IsGUnramified B S hS (U.ι ≫ f))
    (x' : points B S hS U.toFunctor) :
    IsGUnramifiedAt B S hS f (pointsMap B S hS U.toFunctor U.ι x') :=
  ⟨U, hU, x', rfl, hf⟩

/-- Unramifiedness at a point, with the point condition read as a membership in the image of
the open subspace on points. -/
theorem IsUnramifiedAt.exists_mem_range_pointsMap {f : X ⟶ Y} {x : points B S hS X}
    (h : IsUnramifiedAt B S hS f x) :
    ∃ U : Subfunctor X, IsOpenSubspace B S hS U ∧ IsUnramified B S hS (U.ι ≫ f) ∧
      x ∈ Set.range (pointsMap B S hS U.toFunctor U.ι) := by
  obtain ⟨U, hU, x', hx', hf⟩ := h
  exact ⟨U, hU, hf, x', hx'⟩

/-- G-unramifiedness at a point, with the point condition read as a membership in the image of
the open subspace on points. -/
theorem IsGUnramifiedAt.exists_mem_range_pointsMap {f : X ⟶ Y} {x : points B S hS X}
    (h : IsGUnramifiedAt B S hS f x) :
    ∃ U : Subfunctor X, IsOpenSubspace B S hS U ∧ IsGUnramified B S hS (U.ι ≫ f) ∧
      x ∈ Set.range (pointsMap B S hS U.toFunctor U.ι) := by
  obtain ⟨U, hU, x', hx', hf⟩ := h
  exact ⟨U, hU, hf, x', hx'⟩

/-- **Stacks 05VZ.** An unramified morphism of algebraic spaces is locally of finite type. In
every étale chart the underlying scheme morphism is unramified, hence locally of finite type by
`AlgebraicGeometry.locallyOfFiniteType_of_unramified`.

This is also the local-finite-type half of the implication (1) ⇒ (3) of
[Stacks Project, Tag 05W6]. -/
@[stacks 05VZ]
theorem isLocallyOfFiniteType_of_isUnramified {f : X ⟶ Y} (hf : IsUnramified B S hS f) :
    IsLocallyOfFiniteType B S hS f := by
  intro U V a b h ha hb hsq
  have := hf U V a b h ha hb hsq
  infer_instance

/-! ### Universally injective morphisms -/

/-- **A universally injective morphism is injective on points.** Take the base change along the
identity of the target: the canonical morphism `X ⟶ Y ×_Y X` is a section of the second
projection, hence injective on points, and composing it with the first projection is `f`. -/
theorem injective_pointsMap_of_universallyInjective {f : X ⟶ Y}
    (hY : IsAlgebraicSpace B S hS Y) (hf : UniversallyInjective B S hS f) :
    Function.Injective (pointsMap B S hS X f) := by
  have hw : f ≫ 𝟙 Y = 𝟙 X ≫ f := (Category.comp_id f).trans (Category.id_comp f).symm
  have key {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : pullback (𝟙 Y) f ⟶ Z) (h : X ⟶ Z)
      (e : pullback.lift f (𝟙 X) hw ≫ g = h) :
      pointsMap B S hS _ g ∘ pointsMap B S hS X (pullback.lift f (𝟙 X) hw) =
        pointsMap B S hS X h := by
    rw [← pointsMap_comp, e]
  rw [← key _ _ (pullback.lift_fst f (𝟙 X) hw)]
  refine (hf Y hY (𝟙 Y)).comp fun z z' hz => ?_
  have h := key _ _ (pullback.lift_snd f (𝟙 X) hw)
  rw [pointsMap_id] at h
  exact (congrFun h z).symm.trans ((congrArg _ hz).trans (congrFun h z'))

end Chart

/-! ### Formally unramified morphisms -/

variable {B S hS}

/-- **A monomorphism of presheaves is formally unramified.** A monomorphism of presheaves of
types is injective in every component, and two lifts of one lifting problem have the same image
under the component of `a` at the thickening, namely the given section of the target.

This is the formal-unramifiedness half of the implication (3) ⇒ (4) of
[Stacks Project, Tag 05W6]. -/
theorem formallyUnramified_of_mono {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type v} (a : F ⟶ G)
    [Mono a] : FormallyUnramified a := by
  intro T T' _ _ i _ x y _ z₁ z₂ h₁ h₂
  have hinj : Function.Injective (a.app (op T')) :=
    (mono_iff_injective (a.app (op T'))).mp inferInstance
  exact hinj (h₁.2.trans h₂.2.symm)

end AlgebraicGeometry.Space

end
