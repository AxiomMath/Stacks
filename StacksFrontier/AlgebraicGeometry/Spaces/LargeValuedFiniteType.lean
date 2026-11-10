module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Cancellation
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FiniteTypeLocalAtSource
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Representable
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedEtaleSiteMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationMorphismProperties
import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedEtaleSiteMorphism
import StacksFrontier.AlgebraicGeometry.Spaces.Category

/-!
# Finite type morphisms of algebraic spaces with values in a larger universe

Let `S` be a scheme contained in a big fppf site `B`. The finite type conditions on a
morphism of algebraic spaces over `S` — being locally of finite type (**Stacks 03XF**,
part (1)), quasi-compactness of a space (**Stacks 03E3**) and of a morphism
(**Stacks 03HE**), and being of finite type (**Stacks 03XF**, part (3)) — are conditions on
a morphism of presheaves on the big fppf site of `S` with values in `Type u`, the universe
of the schemes. This file carries them to presheaves with values in `Type (max w u)` for a
universe `w` independent of `u`, which is the generality in which a formal algebraic space,
a sheaf of `Type (u + 1)`, lives.

Nothing is weakened by the move: the scheme-valued points of a presheaf of `Type (max w u)`
are the morphisms out of `CategoryTheory.uliftYoneda.{w}.obj U`, and each condition is the
same condition tested against those points. Accordingly each notion agrees with the one in
the value universe of the site on a universe-lifted presheaf, which is what the bridge
lemmas below record.

## Main definitions

* `AlgebraicGeometry.Space.HoldsOnEveryEtaleChartULift` is
  `AlgebraicGeometry.Space.HoldsOnEveryEtaleChart` for presheaves of `Type (max w u)`.
* `AlgebraicGeometry.Space.IsLocallyOfFiniteTypeULift`,
  `AlgebraicGeometry.Space.IsQuasiCompactSpaceULift`,
  `AlgebraicGeometry.Space.IsQuasiCompactULift` and
  `AlgebraicGeometry.Space.IsFiniteTypeULift` are the four finite type conditions for such
  presheaves.
* `AlgebraicGeometry.Space.locallyOfFiniteTypePropertyULift`,
  `AlgebraicGeometry.Space.quasiCompactPropertyULift` and
  `AlgebraicGeometry.Space.finiteTypePropertyULift` package three of them as properties of
  morphisms in the category `AlgebraicGeometry.Space.AlgebraicSpacesULift`.

## Main results

* `AlgebraicGeometry.Space.holdsOnEveryEtaleChartULift_whiskerRight_iff`,
  `AlgebraicGeometry.Space.isEtaleULift_whiskerRight_iff`,
  `AlgebraicGeometry.Space.isLocallyOfFiniteTypeULift_whiskerRight_iff`,
  `AlgebraicGeometry.Space.isQuasiCompactSpaceULift_comp_uliftFunctor_iff`,
  `AlgebraicGeometry.Space.isQuasiCompactULift_whiskerRight_iff` and
  `AlgebraicGeometry.Space.isFiniteTypeULift_whiskerRight_iff`: each condition holds for a
  universe-lifted presheaf, respectively for the universe lift of a morphism of presheaves
  of `Type u`, exactly when the condition in the value universe of the site holds.
* `AlgebraicGeometry.Space.isQuasiCompactSpaceULift_of_iso`: quasi-compactness of a space
  transports along an isomorphism of presheaves.
* `AlgebraicGeometry.Space.isPullback_whiskerRight`: the universe lift of a cartesian square
  of presheaves of `Type u` is cartesian.
* `AlgebraicGeometry.Space.relative_uliftYoneda_whiskerRight_iff` and
  `AlgebraicGeometry.Space.exists_whiskerRight_eq`: the two steps of the transfer itself — a
  relative property along the universe-lifted Yoneda embedding holds for a universe lift
  exactly when the property along the Yoneda embedding holds, and every morphism between
  universe lifts is a universe lift. They are the reusable form of the transfer and are
  public for the sake of the other files that carry a condition up to the larger value
  universe.
* `AlgebraicGeometry.Space.exists_uliftFunctor_iso_of_isAlgebraicSpaceULift`: an algebraic
  space over `S` with values in `Type (max w u)` is isomorphic to the universe lift of a
  presheaf of `Type u`.
* `AlgebraicGeometry.Space.isAlgebraicSpaceULift_pullback`: **Stacks 02YS**, a fibre product
  of algebraic spaces over an algebraic space is an algebraic space.
* `AlgebraicGeometry.Space.isLocallyOfFiniteTypeULift_comp`,
  `AlgebraicGeometry.Space.isQuasiCompactULift_comp` and
  `AlgebraicGeometry.Space.isFiniteTypeULift_comp`: **Stacks 03XG** and **Stacks 03HG**,
  closure under composition among algebraic spaces over `S`.
* `AlgebraicGeometry.Space.hasPropertyULift_of_isPullback`: **Stacks 046F**, a base change in
  the bootstrap sense of Stacks 03XZ.
* `AlgebraicGeometry.Space.holdsOnEveryEtaleChartULift_of_surjectiveChart`: **Stacks 03MJ**,
  condition (2) implies condition (1).
* `AlgebraicGeometry.Space.holdsOnEveryEtaleChartULift_of_forall_pullback_fst` and its
  specialisations
  `AlgebraicGeometry.Space.isLocallyOfFiniteTypeULift_of_forall_pullback_fst`,
  `AlgebraicGeometry.Space.isQuasiCompactULift_of_forall_pullback_fst` and
  `AlgebraicGeometry.Space.isFiniteTypeULift_of_forall_pullback_fst`: a condition tested in
  the bootstrap sense of Stacks 03XZ on the scheme-valued points of the target holds for the
  morphism itself.
* `AlgebraicGeometry.Space.holdsOnEveryEtaleChartULift_uliftYoneda_map` and its
  specialisations
  `AlgebraicGeometry.Space.isLocallyOfFiniteTypeULift_uliftYoneda_map`,
  `AlgebraicGeometry.Space.isQuasiCompactULift_uliftYoneda_map` and
  `AlgebraicGeometry.Space.isFiniteTypeULift_uliftYoneda_map`: a morphism of the site whose
  underlying morphism of schemes has the corresponding property has it as a morphism of
  algebraic spaces over `S`.
* `AlgebraicGeometry.Space.locallyOfFiniteTypePropertyULift_respectsIso`,
  `.quasiCompactPropertyULift_respectsIso` and `.finiteTypePropertyULift_respectsIso`: the
  three packaged properties are invariant under isomorphism, which is what Stacks 046F asks
  of them.

## Implementation notes

The chart conditions are stated with the relative morphism property
`CategoryTheory.MorphismProperty.relative` along `CategoryTheory.uliftYoneda.{w}` rather
than with `CategoryTheory.MorphismProperty.presheaf`, which is that relative property along
`CategoryTheory.yoneda` and therefore only available in the value universe of the site.

The bridge lemmas rest on two facts about
`H = CategoryTheory.FunctorToTypes.uliftFunctor`, read as a functor between presheaf
categories: it is fully faithful, so every morphism between universe lifts is the lift of a
morphism and the lift is injective on morphisms; and it preserves fibre products. Together
these say that a relative morphism property along `uliftYoneda.{w} = yoneda ⋙ H` holds for
a lifted morphism exactly when the property along `yoneda` holds for the morphism, which is
the content of each chart condition. For quasi-compactness of a *morphism* the quantifier
ranges over all algebraic spaces over `S` with values in `Type (max w u)`, and these are
universe lifts up to isomorphism: such a presheaf is pointwise `u`-small, because each of
its sections is cut out of the sections of an étale atlas over a `u`-small object of the
site, and a sheaf has injective restriction along a surjective étale morphism of the site.

The one-chart criterion is what replaces locality on the base in the bootstrap test: a
morphism of algebraic spaces over `S` whose base change along every scheme-valued point of
the target satisfies a chart condition satisfies it itself, because a scheme atlas `b` of the
target together with a scheme atlas of the base change of the morphism along `b` is a
commuting square of étale charts whose chart of the source is surjective, and for a morphism
between universe lifts the equivalence of the two chart conditions is the one in the value
universe of the site. Quasi-compactness is not a chart condition and is handled directly: a
quasi-compact algebraic space mapping to the target receives a surjective étale morphism from
a quasi-compact scheme, and the base change along the resulting scheme-valued point is a
quasi-compact chart of the base change along the given one.

That same smallness is what carries the composition statements and Stacks 02YS across: in
each of them every presheaf involved is an algebraic space over `S`, hence a universe lift
up to isomorphism, so the configuration descends to the value universe of the site, where
the statement is already available, and comes back along the isomorphisms. The chart
condition is invariant under composing with an isomorphism on either side, which is what the
transport uses and is also the invariance Stacks 046F asks of the tested property.

## References

* [Stacks Project, Tag 02YS](https://stacks.math.columbia.edu/tag/02YS)
* [Stacks Project, Tag 03E3](https://stacks.math.columbia.edu/tag/03E3)
* [Stacks Project, Tag 03HE](https://stacks.math.columbia.edu/tag/03HE)
* [Stacks Project, Tag 03HG](https://stacks.math.columbia.edu/tag/03HG)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 03XF](https://stacks.math.columbia.edu/tag/03XF)
* [Stacks Project, Tag 03XG](https://stacks.math.columbia.edu/tag/03XG)
* [Stacks Project, Tag 046F](https://stacks.math.columbia.edu/tag/046F)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/- Instance search for pullbacks of presheaves on `BigFppfOver B S hS` times out under Lean
v4.35.0; supply the functor-category instance. -/
local instance (priority := high) : HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  functorCategoryHasLimitsOfShape

local instance (priority := high) {Y Z W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : Y ⟶ W)
    (g : Z ⟶ W) : HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit (cospan f g)

local instance (priority := high) {J : Type} :
    HasLimitsOfShape (Discrete J) ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  functorCategoryHasLimitsOfShape

/-! ### The conditions in a larger value universe -/

/-- **Stacks 03MJ, condition (1)** for presheaves with values in a universe `max w u`
independent of the universe `u` of the schemes: a property `P` of scheme morphisms *holds on
every étale chart* of `f : F ⟶ G` when, for every commuting square of étale charts `a` of
`F` and `b` of `G` over a morphism `h` of the site, the scheme morphism underlying `h` has
`P`. -/
abbrev HoldsOnEveryEtaleChartULift (P : MorphismProperty Scheme.{u})
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)} (f : F ⟶ G) : Prop :=
  ∀ (U V : BigFppfOver B S hS) (a : (uliftYoneda.{w}).obj U ⟶ F)
      (b : (uliftYoneda.{w}).obj V ⟶ G) (h : U ⟶ V),
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{w}) a →
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{w}) b →
    (uliftYoneda.{w}).map h ≫ b = a ≫ f →
    P ((BigFppfOver.toScheme B S hS).map h)

/-- **Stacks 03XF, part (1)** for presheaves with values in a universe `max w u` independent
of the universe `u` of the schemes: a morphism is *locally of finite type* when every
commuting square of étale scheme charts induces a scheme morphism which is locally of finite
type. -/
abbrev IsLocallyOfFiniteTypeULift {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)}
    (f : F ⟶ G) : Prop :=
  HoldsOnEveryEtaleChartULift.{w} B S hS
    (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) f

/-- **Stacks 03E3** for a presheaf with values in a universe `max w u` independent of the
universe `u` of the schemes: an algebraic space over `S` is *quasi-compact* when it admits a
surjective étale morphism from a universe-lifted Yoneda presheaf whose underlying scheme is
quasi-compact. -/
abbrev IsQuasiCompactSpaceULift (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)) : Prop :=
  ∃ (U : BigFppfOver B S hS) (f : (uliftYoneda.{w}).obj U ⟶ F),
    CompactSpace ((BigFppfOver.toScheme B S hS).obj U) ∧
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{w}) f ∧
    IsEtaleULift.{w} B S hS f

/-- **Stacks 03HE** for presheaves with values in a universe `max w u` independent of the
universe `u` of the schemes: a morphism is *quasi-compact* when every base change of it
along a morphism from a quasi-compact algebraic space has quasi-compact source. -/
abbrev IsQuasiCompactULift {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)} (f : F ⟶ G) :
    Prop :=
  ∀ (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)),
    IsAlgebraicSpaceULift.{w} B S hS Z →
    IsQuasiCompactSpaceULift.{w} B S hS Z →
    ∀ (g : Z ⟶ G), IsQuasiCompactSpaceULift.{w} B S hS (pullback g f)

/-- **Stacks 03XF, part (3)** for presheaves with values in a universe `max w u` independent
of the universe `u` of the schemes: a morphism is *of finite type* when it is locally of
finite type and quasi-compact. -/
abbrev IsFiniteTypeULift {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)} (f : F ⟶ G) :
    Prop :=
  IsLocallyOfFiniteTypeULift.{w} B S hS f ∧ IsQuasiCompactULift.{w} B S hS f

/-- Quasi-compactness of a presheaf with values in a larger universe transports along an
isomorphism of presheaves. -/
theorem isQuasiCompactSpaceULift_of_iso
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)} (e : F ≅ G)
    (hF : IsQuasiCompactSpaceULift.{w} B S hS F) : IsQuasiCompactSpaceULift.{w} B S hS G := by
  obtain ⟨U, f, hc, hs, he⟩ := hF
  refine ⟨U, f ≫ e.hom, hc, MorphismProperty.RespectsIso.postcomp _ e.hom f hs, ?_⟩
  intro V φ hφ
  simpa only [Category.assoc] using
    MorphismProperty.RespectsIso.postcomp _ e.hom (φ ≫ f) (he V φ hφ)

/-! ### Transfer along a fully faithful functor preserving fibre products -/

/-- A relative morphism property along the universe-lifted Yoneda embedding holds for the
universe lift of a morphism of presheaves of `Type u` exactly when the relative property
along the Yoneda embedding holds for the morphism. -/
private theorem relative_uliftYoneda_whiskerRight_iff
    (Q : MorphismProperty (BigFppfOver B S hS))
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : F ⟶ G) :
    Q.relative (uliftYoneda.{w}) (Functor.whiskerRight a uliftFunctor.{w}) ↔ Q.presheaf a :=
  relative_comp_map_iff yoneda
    ((Functor.whiskeringRight (BigFppfOver B S hS)ᵒᵖ (Type u)
      (Type (max w u))).obj uliftFunctor.{w}) Q a

/-- A relative morphism property along the universe-lifted Yoneda embedding holds for the
universe lift of a morphism of presheaves of `Type u` exactly when the relative property
along the Yoneda embedding holds for the morphism. -/
alias relative_uliftYoneda_whiskerRight_iff' := relative_uliftYoneda_whiskerRight_iff

/-- The universe lift of a composition of morphisms of presheaves of `Type u` is the
composition of the universe lifts. -/
private theorem whiskerRight_comp {F G K : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (a : F ⟶ G) (b : G ⟶ K) :
    Functor.whiskerRight (a ≫ b) uliftFunctor.{w} =
      Functor.whiskerRight a uliftFunctor.{w} ≫ Functor.whiskerRight b uliftFunctor.{w} :=
  ((Functor.whiskeringRight (BigFppfOver B S hS)ᵒᵖ (Type u)
    (Type (max w u))).obj uliftFunctor.{w}).map_comp a b

/-- The universe-lifted Yoneda embedding sends a morphism of the site to the universe lift
of its Yoneda image. -/
private theorem uliftYoneda_map_whiskerRight {U V : BigFppfOver B S hS} (h : U ⟶ V) :
    (uliftYoneda.{w} (C := BigFppfOver B S hS)).map h =
      Functor.whiskerRight (yoneda.map h) uliftFunctor.{w} := rfl

/-- Every morphism between universe lifts of presheaves of `Type u` is the universe lift of
a morphism of those presheaves. -/
public theorem exists_whiskerRight_eq {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (a : F ⋙ uliftFunctor.{w} ⟶ G ⋙ uliftFunctor.{w}) :
    ∃ a' : F ⟶ G, Functor.whiskerRight a' uliftFunctor.{w} = a :=
  ((Functor.whiskeringRight (BigFppfOver B S hS)ᵒᵖ (Type u)
    (Type (max w u))).obj uliftFunctor.{w}).map_surjective a

/-- Two morphisms of presheaves of `Type u` with the same universe lift are equal. -/
private theorem whiskerRight_injective {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {a b : F ⟶ G}
    (h : Functor.whiskerRight a uliftFunctor.{w} = Functor.whiskerRight b uliftFunctor.{w}) :
    a = b :=
  ((Functor.whiskeringRight (BigFppfOver B S hS)ᵒᵖ (Type u)
    (Type (max w u))).obj uliftFunctor.{w}).map_injective h

/-- The universe lift of a cartesian square of presheaves of `Type u` is cartesian, the
universe lift preserving fibre products. -/
theorem isPullback_whiskerRight {F G K L : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {p : L ⟶ F} {q : L ⟶ G} {a : F ⟶ K} {b : G ⟶ K} (h : IsPullback p q a b) :
    IsPullback (Functor.whiskerRight p uliftFunctor.{w})
      (Functor.whiskerRight q uliftFunctor.{w}) (Functor.whiskerRight a uliftFunctor.{w})
      (Functor.whiskerRight b uliftFunctor.{w}) :=
  h.map ((Functor.whiskeringRight (BigFppfOver B S hS)ᵒᵖ (Type u)
    (Type (max w u))).obj uliftFunctor.{w})

/-- A relative morphism property along the universe-lifted Yoneda embedding holds for a
composition of universe lifts of morphisms of presheaves of `Type u` exactly when the
relative property along the Yoneda embedding holds for the composition. -/
private theorem relative_uliftYoneda_whiskerRight_comp_iff
    (Q : MorphismProperty (BigFppfOver B S hS))
    {F G K : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : F ⟶ G) (b : G ⟶ K) :
    Q.relative (uliftYoneda.{w})
        (Functor.whiskerRight a uliftFunctor.{w} ≫
          Functor.whiskerRight b uliftFunctor.{w}) ↔
      Q.presheaf (a ≫ b) :=
  Iff.trans
    (Iff.of_eq (congrArg
      (fun k : F ⋙ uliftFunctor.{w} ⟶ K ⋙ uliftFunctor.{w} => Q.relative (uliftYoneda.{w}) k)
      (whiskerRight_comp B S hS a b).symm))
    (relative_uliftYoneda_whiskerRight_iff B S hS Q (a ≫ b))

/-! ### Agreement with the conditions in the value universe of the site -/

/-- A property of scheme morphisms holds on every étale chart of the universe lift of a
morphism of presheaves of `Type u` exactly when it holds on every étale chart of the
morphism. -/
theorem holdsOnEveryEtaleChartULift_whiskerRight_iff (P : MorphismProperty Scheme.{u})
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G) :
    HoldsOnEveryEtaleChartULift.{w} B S hS P (Functor.whiskerRight f uliftFunctor.{w}) ↔
      HoldsOnEveryEtaleChart B S hS P f := by
  constructor
  · intro hf U V a b h ha hb hw
    refine hf U V (Functor.whiskerRight a uliftFunctor.{w})
      (Functor.whiskerRight b uliftFunctor.{w}) h
      ((relative_uliftYoneda_whiskerRight_iff B S hS _ a).mpr ha)
      ((relative_uliftYoneda_whiskerRight_iff B S hS _ b).mpr hb) ?_
    refine Eq.trans ?_ (whiskerRight_comp B S hS a f)
    exact Eq.trans (whiskerRight_comp B S hS (yoneda.map h) b).symm
      (congrArg (fun k : yoneda.obj U ⟶ G => Functor.whiskerRight k uliftFunctor.{w}) hw)
  · intro hf U V a b h ha hb hw
    obtain ⟨a', rfl⟩ := exists_whiskerRight_eq B S hS (F := yoneda.obj U) a
    obtain ⟨b', rfl⟩ := exists_whiskerRight_eq B S hS (F := yoneda.obj V) b
    refine hf U V a' b' h ((relative_uliftYoneda_whiskerRight_iff B S hS _ a').mp ha)
      ((relative_uliftYoneda_whiskerRight_iff B S hS _ b').mp hb) ?_
    refine whiskerRight_injective B S hS ?_
    rwa [whiskerRight_comp B S hS, whiskerRight_comp B S hS,
      ← uliftYoneda_map_whiskerRight]

/-- The universe lift of a morphism of presheaves of `Type u` is étale in the larger value
universe exactly when the morphism is étale. -/
theorem isEtaleULift_whiskerRight_iff {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G) :
    IsEtaleULift.{w} B S hS (Functor.whiskerRight f uliftFunctor.{w}) ↔ IsEtale B S hS f := by
  constructor
  · intro hf U φ hφ
    exact (relative_uliftYoneda_whiskerRight_comp_iff B S hS _ φ f).mp
      (hf U (Functor.whiskerRight φ uliftFunctor.{w})
        ((relative_uliftYoneda_whiskerRight_iff B S hS _ φ).mpr hφ))
  · intro hf U φ hφ
    obtain ⟨φ', rfl⟩ := exists_whiskerRight_eq B S hS (F := yoneda.obj U) φ
    exact (relative_uliftYoneda_whiskerRight_comp_iff B S hS _ φ' f).mpr
      (hf U φ' ((relative_uliftYoneda_whiskerRight_iff B S hS _ φ').mp hφ))

/-- The universe lift of a morphism of presheaves of `Type u` is locally of finite type in
the larger value universe exactly when the morphism is locally of finite type. -/
theorem isLocallyOfFiniteTypeULift_whiskerRight_iff
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G) :
    IsLocallyOfFiniteTypeULift.{w} B S hS (Functor.whiskerRight f uliftFunctor.{w}) ↔
      IsLocallyOfFiniteType B S hS f :=
  holdsOnEveryEtaleChartULift_whiskerRight_iff B S hS _ f

/-- The universe lift of a presheaf of `Type u` is a quasi-compact algebraic space over `S`
in the larger value universe exactly when the presheaf is a quasi-compact algebraic space
over `S`. -/
theorem isQuasiCompactSpaceULift_comp_uliftFunctor_iff
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    IsQuasiCompactSpaceULift.{w} B S hS (F ⋙ uliftFunctor.{w}) ↔
      IsQuasiCompactSpace B S hS F := by
  constructor
  · rintro ⟨U, f, hc, hs, he⟩
    obtain ⟨f', rfl⟩ := exists_whiskerRight_eq B S hS (F := yoneda.obj U) f
    exact ⟨U, f', hc, (relative_uliftYoneda_whiskerRight_iff B S hS _ f').mp hs,
      (isEtaleULift_whiskerRight_iff B S hS f').mp he⟩
  · rintro ⟨U, f, hc, hs, he⟩
    exact ⟨U, Functor.whiskerRight f uliftFunctor.{w}, hc,
      (relative_uliftYoneda_whiskerRight_iff B S hS _ f).mpr hs,
      (isEtaleULift_whiskerRight_iff B S hS f).mpr he⟩

/-! ### Smallness of an algebraic space with values in a larger universe -/
/-- An algebraic space over `S` with values in `Type (max w u)` is, up to isomorphism, the
universe lift of a presheaf of `Type u`. -/
theorem exists_uliftFunctor_iso_of_isAlgebraicSpaceULift
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)} (hZ : IsAlgebraicSpaceULift.{w} B S hS Z) :
    ∃ Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u, Nonempty (Z' ⋙ uliftFunctor.{w} ≅ Z) := by
  obtain ⟨Z', -, hZ'⟩ := exists_comp_uliftFunctor_iso_of_isAlgebraicSpaceULift B S hS hZ
  exact ⟨Z', hZ'⟩

/-- A presheaf of `Type u` whose universe lift is isomorphic to an algebraic space with values
in `Type (max w u)` is an algebraic space. -/
private theorem isAlgebraicSpace_of_iso_uliftFunctor {F' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)} (e : F' ⋙ uliftFunctor.{w} ≅ F)
    (hF : IsAlgebraicSpaceULift.{w} B S hS F) : IsAlgebraicSpace B S hS F' :=
  (isAlgebraicSpaceULift_comp_uliftFunctor_iff B S hS F').mp
    (isAlgebraicSpaceULift_of_iso B S hS e.symm hF)

/-- The universe lift of a morphism of presheaves of `Type u` is quasi-compact in the larger
value universe exactly when the morphism is quasi-compact. -/
theorem isQuasiCompactULift_whiskerRight_iff
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G) :
    IsQuasiCompactULift.{w} B S hS (Functor.whiskerRight f uliftFunctor.{w}) ↔
      IsQuasiCompact B S hS f := by
  constructor
  · intro hf Z' hZalg hZqc g'
    have hA : IsAlgebraicSpaceULift.{w} B S hS (Z' ⋙ uliftFunctor.{w}) :=
      (isAlgebraicSpaceULift_comp_uliftFunctor_iff B S hS Z').mpr hZalg
    have hQ : IsQuasiCompactSpaceULift.{w} B S hS (Z' ⋙ uliftFunctor.{w}) :=
      (isQuasiCompactSpaceULift_comp_uliftFunctor_iff B S hS Z').mpr hZqc
    have h := hf (Z' ⋙ uliftFunctor.{w}) hA hQ (Functor.whiskerRight g' uliftFunctor.{w})
    refine (isQuasiCompactSpaceULift_comp_uliftFunctor_iff B S hS (pullback g' f)).mp ?_
    exact isQuasiCompactSpaceULift_of_iso B S hS
      (isPullback_whiskerRight.{w} B S hS (IsPullback.of_hasPullback g' f)).isoPullback.symm h
  · intro hf Z hZalg hZqc g
    obtain ⟨Z', ⟨e⟩⟩ := exists_uliftFunctor_iso_of_isAlgebraicSpaceULift B S hS hZalg
    obtain ⟨g', hmap⟩ := exists_whiskerRight_eq B S hS (F := Z') (e.hom ≫ g)
    have hZ'alg : IsAlgebraicSpace B S hS Z' :=
      isAlgebraicSpace_of_iso_uliftFunctor B S hS e hZalg
    have hZ'qc : IsQuasiCompactSpace B S hS Z' :=
      (isQuasiCompactSpaceULift_comp_uliftFunctor_iff B S hS Z').mp
        (isQuasiCompactSpaceULift_of_iso B S hS e.symm hZqc)
    have hQ := (isQuasiCompactSpaceULift_comp_uliftFunctor_iff B S hS
      (pullback g' f)).mpr (hf Z' hZ'alg hZ'qc g')
    have hR : IsPullback e.hom (Functor.whiskerRight g' uliftFunctor.{w}) g
        (𝟙 (G ⋙ uliftFunctor.{w})) :=
      IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, hmap]⟩
    have hpb : IsPullback
        (Functor.whiskerRight (pullback.fst g' f) uliftFunctor.{w} ≫ e.hom)
        (Functor.whiskerRight (pullback.snd g' f) uliftFunctor.{w}) g
        (Functor.whiskerRight f uliftFunctor.{w}) := by
      simpa using
        (isPullback_whiskerRight.{w} B S hS (IsPullback.of_hasPullback g' f)).paste_horiz hR
    exact isQuasiCompactSpaceULift_of_iso B S hS hpb.isoPullback hQ

/-- The universe lift of a morphism of presheaves of `Type u` is of finite type in the
larger value universe exactly when the morphism is of finite type. -/
theorem isFiniteTypeULift_whiskerRight_iff
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G) :
    IsFiniteTypeULift.{w} B S hS (Functor.whiskerRight f uliftFunctor.{w}) ↔
      IsFiniteType B S hS f :=
  and_congr (isLocallyOfFiniteTypeULift_whiskerRight_iff B S hS f)
    (isQuasiCompactULift_whiskerRight_iff B S hS f)

/-! ### Invariance under isomorphisms -/

/-- The every-étale-chart condition is unchanged by precomposing with an isomorphism of
presheaves: the charts of the source correspond under the isomorphism. -/
theorem holdsOnEveryEtaleChartULift_precomp (P : MorphismProperty Scheme.{u})
    {F G K : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)} (e : F ⟶ G) [IsIso e] (f : G ⟶ K)
    (hf : HoldsOnEveryEtaleChartULift.{w} B S hS P f) :
    HoldsOnEveryEtaleChartULift.{w} B S hS P (e ≫ f) := by
  intro U V a b h ha hb hsq
  refine hf U V (a ≫ e) b h (MorphismProperty.RespectsIso.postcomp _ e a ha) hb ?_
  rw [hsq, Category.assoc]

/-- The every-étale-chart condition is unchanged by postcomposing with an isomorphism of
presheaves: the charts of the target correspond under the isomorphism. -/
theorem holdsOnEveryEtaleChartULift_postcomp (P : MorphismProperty Scheme.{u})
    {F G K : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)} (e : G ⟶ K) [IsIso e] (f : F ⟶ G)
    (hf : HoldsOnEveryEtaleChartULift.{w} B S hS P f) :
    HoldsOnEveryEtaleChartULift.{w} B S hS P (f ≫ e) := by
  intro U V a b h ha hb hsq
  refine hf U V a (b ≫ inv e) h ha
    (MorphismProperty.RespectsIso.postcomp _ (inv e) b hb) ?_
  rw [← Category.assoc, hsq]
  simp

/-- Quasi-compactness of a morphism is unchanged by precomposing with an isomorphism of
presheaves: a base change of the composite is a base change of the morphism. -/
theorem isQuasiCompactULift_precomp {F G K : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)}
    (e : F ≅ G) (f : G ⟶ K) (hf : IsQuasiCompactULift.{w} B S hS f) :
    IsQuasiCompactULift.{w} B S hS (e.hom ≫ f) := by
  intro Z hZalg hZqc g
  have hpb : IsPullback (pullback.fst g (e.hom ≫ f))
      (pullback.snd g (e.hom ≫ f) ≫ e.hom) g f :=
    (IsPullback.of_hasPullback g (e.hom ≫ f)).of_iso (Iso.refl _) (Iso.refl _) e
      (Iso.refl _) (by simp) (by simp) (by simp) (by simp)
  exact isQuasiCompactSpaceULift_of_iso B S hS hpb.isoPullback.symm (hf Z hZalg hZqc g)

/-- Quasi-compactness of a morphism is unchanged by postcomposing with an isomorphism of
presheaves: a base change of the composite is a base change of the morphism along the
transported point. -/
theorem isQuasiCompactULift_postcomp {F G K : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)}
    (e : G ≅ K) (f : F ⟶ G) (hf : IsQuasiCompactULift.{w} B S hS f) :
    IsQuasiCompactULift.{w} B S hS (f ≫ e.hom) := by
  intro Z hZalg hZqc g
  have hpb : IsPullback (pullback.fst g (f ≫ e.hom)) (pullback.snd g (f ≫ e.hom))
      (g ≫ e.inv) f :=
    (IsPullback.of_hasPullback g (f ≫ e.hom)).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
      e.symm (by simp) (by simp) (by simp) (by simp)
  exact isQuasiCompactSpaceULift_of_iso B S hS hpb.isoPullback.symm
    (hf Z hZalg hZqc (g ≫ e.inv))

/-! ### A base change in the bootstrap sense -/

/-- **Stacks 046F** for presheaves with values in a universe `max w u` independent of the
universe `u` of the schemes: in a cartesian square whose right-hand column `a` is
representable by algebraic spaces and has a property `P` of morphisms of algebraic spaces
over `S`, the left-hand column `a'` has `P` as well. Only invariance of `P` under
isomorphism is used. -/
theorem hasPropertyULift_of_isPullback
    {P : MorphismProperty (AlgebraicSpacesULift.{w} B S hS)} [P.RespectsIso]
    {F G F' G' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)} {a : F ⟶ G} {g : G' ⟶ G}
    {k : F' ⟶ F} {a' : F' ⟶ G'} (sq : IsPullback k a' a g)
    (ha : IsRepresentableByAlgebraicSpacesULift.{w} B S hS a)
    (h : HasPropertyULift.{w} B S hS P a ha) :
    HasPropertyULift.{w} B S hS P a'
      (isRepresentableByAlgebraicSpacesULift_of_isPullback B S hS k a' a g sq ha) := by
  intro U ξ
  have hpb : IsPullback (pullback.fst ξ a') (pullback.snd ξ a' ≫ k) (ξ ≫ g) a :=
    ((IsPullback.of_hasPullback ξ a').flip.paste_horiz sq).flip
  have heq : (ObjectProperty.homMk (pullback.fst ξ a') :
      (⟨pullback ξ a', isRepresentableByAlgebraicSpacesULift_of_isPullback B S hS k a' a g
          sq ha U ξ⟩ : AlgebraicSpacesULift.{w} B S hS) ⟶
        ⟨(uliftYoneda.{w}).obj U, isAlgebraicSpaceULift_uliftYoneda.{w} B S hS U⟩) =
      (ObjectProperty.isoMk
        (P := fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u) =>
          IsAlgebraicSpaceULift.{w} B S hS F)
        (X := ⟨pullback ξ a', isRepresentableByAlgebraicSpacesULift_of_isPullback B S hS k a'
          a g sq ha U ξ⟩)
        (Y := ⟨pullback (ξ ≫ g) a, ha U (ξ ≫ g)⟩) hpb.isoPullback).hom ≫
        ObjectProperty.homMk (pullback.fst (ξ ≫ g) a) := by
    apply ObjectProperty.hom_ext
    simp [ObjectProperty.homMk, ObjectProperty.isoMk]
  rw [heq]
  exact MorphismProperty.RespectsIso.precomp _ _ _ (h U (ξ ≫ g))

/-! ### Composition -/

/-- The every-étale-chart condition for `f` is equivalent to that of a morphism `f'` which is
`f` conjugated by isomorphisms of the source and of the target. -/
private theorem holdsOnEveryEtaleChartULift_iff_of_conj (P : MorphismProperty Scheme.{u})
    {F' G' F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)} (eF : F' ≅ F) (eG : G' ≅ G)
    {f : F ⟶ G} {f' : F' ⟶ G'} (h : eF.hom ≫ f ≫ eG.inv = f') :
    HoldsOnEveryEtaleChartULift.{w} B S hS P f ↔ HoldsOnEveryEtaleChartULift.{w} B S hS P f' := by
  subst h
  refine ⟨fun hf => ?_, fun hf => ?_⟩
  · rw [← Category.assoc]
    exact holdsOnEveryEtaleChartULift_postcomp B S hS P eG.inv _
      (holdsOnEveryEtaleChartULift_precomp B S hS P eF.hom f hf)
  · have := holdsOnEveryEtaleChartULift_precomp B S hS P eF.inv _
      (holdsOnEveryEtaleChartULift_postcomp B S hS P eG.hom _ hf)
    simpa using this

/-- **Stacks 02YS** in the value universe `max w u`: a fibre product of algebraic spaces over
`S` with values in `Type (max w u)` over an algebraic space is an algebraic space. All three
presheaves are universe lifts, so this is the statement in the value universe of the site. -/
theorem isAlgebraicSpaceULift_pullback {F G K : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)}
    (a : F ⟶ K) (b : G ⟶ K) (hF : IsAlgebraicSpaceULift.{w} B S hS F)
    (hG : IsAlgebraicSpaceULift.{w} B S hS G) (hK : IsAlgebraicSpaceULift.{w} B S hS K) :
    IsAlgebraicSpaceULift.{w} B S hS (pullback a b) := by
  obtain ⟨F', ⟨eF⟩⟩ := exists_uliftFunctor_iso_of_isAlgebraicSpaceULift B S hS hF
  obtain ⟨G', ⟨eG⟩⟩ := exists_uliftFunctor_iso_of_isAlgebraicSpaceULift B S hS hG
  obtain ⟨K', ⟨eK⟩⟩ := exists_uliftFunctor_iso_of_isAlgebraicSpaceULift B S hS hK
  obtain ⟨a', ha'⟩ := exists_whiskerRight_eq B S hS (F := F') (eF.hom ≫ a ≫ eK.inv)
  obtain ⟨b', hb'⟩ := exists_whiskerRight_eq B S hS (F := G') (eG.hom ≫ b ≫ eK.inv)
  have hsq : IsPullback (pullback.fst a b ≫ eF.inv) (pullback.snd a b ≫ eG.inv)
      (Functor.whiskerRight a' uliftFunctor.{w}) (Functor.whiskerRight b' uliftFunctor.{w}) :=
    (IsPullback.of_hasPullback a b).of_iso (Iso.refl _) eF.symm eG.symm eK.symm (by simp)
      (by simp) (by rw [ha']; simp) (by rw [hb']; simp)
  refine isAlgebraicSpaceULift_of_iso B S hS hsq.isoPullback.symm ?_
  refine isAlgebraicSpaceULift_of_iso B S hS
    (isPullback_whiskerRight.{w} B S hS (IsPullback.of_hasPullback a' b')).isoPullback ?_
  refine (isAlgebraicSpaceULift_comp_uliftFunctor_iff B S hS (pullback a' b')).mpr ?_
  exact isAlgebraicSpace_pullback B S hS a' b' (isAlgebraicSpace_of_iso_uliftFunctor B S hS eF hF)
    (isAlgebraicSpace_of_iso_uliftFunctor B S hS eG hG)
    (isAlgebraicSpace_of_iso_uliftFunctor B S hS eK hK)

/-- **Stacks 03XG**, the local half, in the value universe `max w u`: a composition of
morphisms of algebraic spaces over `S` which are locally of finite type is locally of finite
type. All three presheaves are universe lifts, so this is the statement in the value universe
of the site. -/
theorem isLocallyOfFiniteTypeULift_comp {F G K : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)}
    (hF : IsAlgebraicSpaceULift.{w} B S hS F) (hG : IsAlgebraicSpaceULift.{w} B S hS G)
    (hK : IsAlgebraicSpaceULift.{w} B S hS K) (a : F ⟶ G) (b : G ⟶ K)
    (ha : IsLocallyOfFiniteTypeULift.{w} B S hS a)
    (hb : IsLocallyOfFiniteTypeULift.{w} B S hS b) :
    IsLocallyOfFiniteTypeULift.{w} B S hS (a ≫ b) := by
  obtain ⟨F', ⟨eF⟩⟩ := exists_uliftFunctor_iso_of_isAlgebraicSpaceULift B S hS hF
  obtain ⟨G', ⟨eG⟩⟩ := exists_uliftFunctor_iso_of_isAlgebraicSpaceULift B S hS hG
  obtain ⟨K', ⟨eK⟩⟩ := exists_uliftFunctor_iso_of_isAlgebraicSpaceULift B S hS hK
  obtain ⟨a', ha'⟩ := exists_whiskerRight_eq B S hS (F := F') (eF.hom ≫ a ≫ eG.inv)
  obtain ⟨b', hb'⟩ := exists_whiskerRight_eq B S hS (F := G') (eG.hom ≫ b ≫ eK.inv)
  have hA : IsLocallyOfFiniteType B S hS a' :=
    (isLocallyOfFiniteTypeULift_whiskerRight_iff B S hS a').mp
      ((holdsOnEveryEtaleChartULift_iff_of_conj B S hS _ eF eG ha'.symm).mp ha)
  have hB : IsLocallyOfFiniteType B S hS b' :=
    (isLocallyOfFiniteTypeULift_whiskerRight_iff B S hS b').mp
      ((holdsOnEveryEtaleChartULift_iff_of_conj B S hS _ eG eK hb'.symm).mp hb)
  have hcomp : IsLocallyOfFiniteType B S hS (a' ≫ b') :=
    isLocallyOfFiniteType_comp B S hS (isAlgebraicSpace_of_iso_uliftFunctor B S hS eF hF)
      (isAlgebraicSpace_of_iso_uliftFunctor B S hS eG hG)
      (isAlgebraicSpace_of_iso_uliftFunctor B S hS eK hK) a' b' hA hB
  have heq : eF.hom ≫ (a ≫ b) ≫ eK.inv =
      Functor.whiskerRight (a' ≫ b') uliftFunctor.{w} := by
    rw [whiskerRight_comp, ha', hb']
    simp
  exact (holdsOnEveryEtaleChartULift_iff_of_conj B S hS _ eF eK heq).mpr
    ((isLocallyOfFiniteTypeULift_whiskerRight_iff B S hS (a' ≫ b')).mpr hcomp)

/-- **Stacks 03HG** in the value universe `max w u`: a composition of quasi-compact morphisms
of algebraic spaces over `S` with values in `Type (max w u)` is quasi-compact. -/
theorem isQuasiCompactULift_comp {F G K : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)}
    (hG : IsAlgebraicSpaceULift.{w} B S hS G) (hK : IsAlgebraicSpaceULift.{w} B S hS K)
    (a : F ⟶ G) (b : G ⟶ K) (ha : IsQuasiCompactULift.{w} B S hS a)
    (hb : IsQuasiCompactULift.{w} B S hS b) :
    IsQuasiCompactULift.{w} B S hS (a ≫ b) := fun Z hZ hZqc k =>
  isQuasiCompactSpaceULift_of_iso B S hS (pullbackLeftPullbackSndIso k b a)
    (ha (pullback k b) (isAlgebraicSpaceULift_pullback B S hS k b hZ hG hK)
      (hb Z hZ hZqc k) (pullback.snd k b))

/-- **Stacks 03XG**, the global half, in the value universe `max w u`: a composition of
morphisms of algebraic spaces over `S` which are of finite type is of finite type. -/
theorem isFiniteTypeULift_comp {F G K : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)}
    (hF : IsAlgebraicSpaceULift.{w} B S hS F) (hG : IsAlgebraicSpaceULift.{w} B S hS G)
    (hK : IsAlgebraicSpaceULift.{w} B S hS K) (a : F ⟶ G) (b : G ⟶ K)
    (ha : IsFiniteTypeULift.{w} B S hS a) (hb : IsFiniteTypeULift.{w} B S hS b) :
    IsFiniteTypeULift.{w} B S hS (a ≫ b) :=
  ⟨isLocallyOfFiniteTypeULift_comp B S hS hF hG hK a b ha.1 hb.1,
    isQuasiCompactULift_comp B S hS hG hK a b ha.2 hb.2⟩

/-! ### The one-chart criterion -/

/-- The identity of a universe-lifted Yoneda presheaf is surjective after every represented
base change. -/
public theorem relative_id_surjective (T : BigFppfOver B S hS) :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{w})
        (𝟙 ((uliftYoneda.{w}).obj T)) := by
  refine relative_id_of_isomorphisms B S hS _ (fun _ _ φ hφ => ?_) T
  have := hφ
  change AlgebraicGeometry.Surjective ((BigFppfOver.toScheme B S hS).map φ)
  infer_instance


/-- A relative morphism property along the universe-lifted Yoneda embedding is stable under
composition as soon as the property itself is. -/
public theorem relative_comp {Q : MorphismProperty (BigFppfOver B S hS)}
    [Q.IsStableUnderComposition] {F G K : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)}
    {m : F ⟶ G} {n : G ⟶ K} (hm : Q.relative (uliftYoneda.{w}) m)
    (hn : Q.relative (uliftYoneda.{w}) n) : Q.relative (uliftYoneda.{w}) (m ≫ n) :=
  MorphismProperty.comp_mem _ _ _ hm hn

/-- A relative morphism property along the universe-lifted Yoneda embedding is stable under
base change. -/
public theorem relative_of_isPullback {Q : MorphismProperty (BigFppfOver B S hS)}
    {F G K L : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)} {p : L ⟶ F} {q : L ⟶ G}
    {m : F ⟶ K} {n : G ⟶ K} (sq : IsPullback p q m n)
    (hn : Q.relative (uliftYoneda.{w}) n) : Q.relative (uliftYoneda.{w}) p :=
  (MorphismProperty.relative_isStableUnderBaseChange (F := uliftYoneda.{w})
    Q).of_isPullback sq.flip hn

/-- **Stacks 03MJ, condition (2) implies condition (1)**, in the value universe `max w u`: a
property of morphisms of schemes which is étale local on the source and target and holds on
one commuting square of étale charts of a morphism of algebraic spaces over `S` whose chart
of the source is surjective holds on every such square. Both presheaves are universe lifts,
so this is the statement in the value universe of the site. -/
theorem holdsOnEveryEtaleChartULift_of_surjectiveChart (P : MorphismProperty Scheme.{u})
    (hP : IsEtaleLocalOnSourceAndTarget P)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)}
    (hF : IsAlgebraicSpaceULift.{w} B S hS F) (hG : IsAlgebraicSpaceULift.{w} B S hS G)
    {f : F ⟶ G} (U V : BigFppfOver B S hS) (a : (uliftYoneda.{w}).obj U ⟶ F)
    (b : (uliftYoneda.{w}).obj V ⟶ G) (h : U ⟶ V)
    (ha : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{w}) a)
    (hb : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{w}) b)
    (haSurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{w}) a)
    (hsq : (uliftYoneda.{w}).map h ≫ b = a ≫ f)
    (hPh : P ((BigFppfOver.toScheme B S hS).map h)) :
    HoldsOnEveryEtaleChartULift.{w} B S hS P f := by
  obtain ⟨F', ⟨eF⟩⟩ := exists_uliftFunctor_iso_of_isAlgebraicSpaceULift B S hS hF
  obtain ⟨G', ⟨eG⟩⟩ := exists_uliftFunctor_iso_of_isAlgebraicSpaceULift B S hS hG
  obtain ⟨f', hf'⟩ := exists_whiskerRight_eq B S hS (F := F') (eF.hom ≫ f ≫ eG.inv)
  obtain ⟨a', ha'⟩ := exists_whiskerRight_eq B S hS (F := yoneda.obj U) (a ≫ eF.inv)
  obtain ⟨b', hb'⟩ := exists_whiskerRight_eq B S hS (F := yoneda.obj V) (b ≫ eG.inv)
  have hchart : HoldsOnSurjectiveEtaleChart B S hS P f' := by
    refine ⟨U, V, a', b', h, ?_, ?_, ?_, ?_, hPh⟩
    · refine (relative_uliftYoneda_whiskerRight_iff B S hS _ a').mp ?_
      rw [ha']
      exact MorphismProperty.RespectsIso.postcomp _ eF.inv a ha
    · refine (relative_uliftYoneda_whiskerRight_iff B S hS _ b').mp ?_
      rw [hb']
      exact MorphismProperty.RespectsIso.postcomp _ eG.inv b hb
    · refine (relative_uliftYoneda_whiskerRight_iff B S hS _ a').mp ?_
      rw [ha']
      exact MorphismProperty.RespectsIso.postcomp _ eF.inv a haSurj
    · have key : (uliftYoneda.{w}).map h ≫ b ≫ eG.inv
          = (a ≫ eF.inv) ≫ eF.hom ≫ f ≫ eG.inv :=
        calc (uliftYoneda.{w}).map h ≫ b ≫ eG.inv
            = ((uliftYoneda.{w}).map h ≫ b) ≫ eG.inv := (Category.assoc _ _ _).symm
          _ = (a ≫ f) ≫ eG.inv := by rw [hsq]
          _ = (a ≫ eF.inv) ≫ eF.hom ≫ f ≫ eG.inv := by simp
      refine whiskerRight_injective B S hS ?_
      rw [whiskerRight_comp B S hS, whiskerRight_comp B S hS,
        ← uliftYoneda_map_whiskerRight, ha', hb', hf']
      exact key
  have hall : HoldsOnEveryEtaleChart B S hS P f' :=
    (holdsOnEveryEtaleChart_iff_surjectiveChart B S hS P hP
      (isAlgebraicSpace_of_iso_uliftFunctor B S hS eF hF)
      (isAlgebraicSpace_of_iso_uliftFunctor B S hS eG hG) f').mpr hchart
  exact (holdsOnEveryEtaleChartULift_iff_of_conj B S hS P eF eG hf'.symm).mpr
    ((holdsOnEveryEtaleChartULift_whiskerRight_iff B S hS P f').mpr hall)

/-- The every-étale-chart condition of **Stacks 03MJ** for a morphism `f` of algebraic spaces
over `S` with values in `Type (max w u)` follows from the same condition for the base changes
of `f` along the scheme-valued points of its target. A surjective étale chart of `f` is
assembled from a scheme atlas `b` of the target and a scheme atlas of the base change of `f`
along `b`. -/
theorem holdsOnEveryEtaleChartULift_of_forall_pullback_fst (P : MorphismProperty Scheme.{u})
    (hP : IsEtaleLocalOnSourceAndTarget P)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)}
    (hF : IsAlgebraicSpaceULift.{w} B S hS F) (hG : IsAlgebraicSpaceULift.{w} B S hS G)
    (f : F ⟶ G)
    (hf : ∀ (U : BigFppfOver B S hS) (ξ : (uliftYoneda.{w}).obj U ⟶ G),
      HoldsOnEveryEtaleChartULift.{w} B S hS P (pullback.fst ξ f)) :
    HoldsOnEveryEtaleChartULift.{w} B S hS P f := by
  obtain ⟨V, b, hbSurj, hbEtale⟩ := hG.exists_atlas
  have hT : IsAlgebraicSpaceULift.{w} B S hS (pullback b f) :=
    isAlgebraicSpaceULift_pullback B S hS b f
      (isAlgebraicSpaceULift_uliftYoneda.{w} B S hS V) hF hG
  obtain ⟨W, β, hβSurj, hβEtale⟩ := hT.exists_atlas
  obtain ⟨h, hh⟩ : ∃ h : W ⟶ V, (uliftYoneda.{w}).map h = β ≫ pullback.fst b f :=
    ⟨(uliftYoneda.{w}).preimage (β ≫ pullback.fst b f), by simp⟩
  have hPh : P ((BigFppfOver.toScheme B S hS).map h) :=
    hf V b W V β (𝟙 _) h hβEtale (relative_id_etale B S hS V)
      (by rw [Category.comp_id, hh])
  have hbc : IsPullback (pullback.snd b f) (pullback.fst b f) f b :=
    (IsPullback.of_hasPullback b f).flip
  refine holdsOnEveryEtaleChartULift_of_surjectiveChart B S hS P hP hF hG W V
    (β ≫ pullback.snd b f) b h
    (relative_comp B S hS hβEtale (relative_of_isPullback B S hS hbc hbEtale))
    hbEtale
    (relative_comp B S hS hβSurj (relative_of_isPullback B S hS hbc hbSurj)) ?_ hPh
  rw [hh, Category.assoc, Category.assoc, pullback.condition]

/-- **Stacks 03XF, part (1)** from the bootstrap test of **Stacks 03XZ**: a morphism of
algebraic spaces over `S` with values in `Type (max w u)` is locally of finite type as soon
as its base change along every scheme-valued point of its target is. -/
theorem isLocallyOfFiniteTypeULift_of_forall_pullback_fst
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)}
    (hF : IsAlgebraicSpaceULift.{w} B S hS F) (hG : IsAlgebraicSpaceULift.{w} B S hS G)
    (f : F ⟶ G)
    (hf : ∀ (U : BigFppfOver B S hS) (ξ : (uliftYoneda.{w}).obj U ⟶ G),
      IsLocallyOfFiniteTypeULift.{w} B S hS (pullback.fst ξ f)) :
    IsLocallyOfFiniteTypeULift.{w} B S hS f :=
  holdsOnEveryEtaleChartULift_of_forall_pullback_fst B S hS _
    LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget hF hG f hf

/-- **Stacks 03HE** from the bootstrap test of **Stacks 03XZ**: a morphism of presheaves with
values in `Type (max w u)` is quasi-compact as soon as its base change along every
scheme-valued point of its target is. A quasi-compact algebraic space over `S` mapping to the
target receives a surjective étale morphism from a quasi-compact scheme, and the base change
along the resulting scheme-valued point is a quasi-compact étale surjective chart of the base
change along the given one. -/
theorem isQuasiCompactULift_of_forall_pullback_fst
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)} (f : F ⟶ G)
    (hf : ∀ (U : BigFppfOver B S hS) (ξ : (uliftYoneda.{w}).obj U ⟶ G),
      IsQuasiCompactULift.{w} B S hS (pullback.fst ξ f)) :
    IsQuasiCompactULift.{w} B S hS f := by
  intro Z hZ hZqc g
  obtain ⟨U, c, hUc, hcSurj, hcEtale⟩ := hZqc
  have hcE := (AlgebraicGeometry.Space.isEtaleULift_iff_relative_etale B S hS c).mp hcEtale
  have hUqc : IsQuasiCompactSpaceULift.{w} B S hS ((uliftYoneda.{w}).obj U) :=
    ⟨U, 𝟙 _, hUc, relative_id_surjective B S hS U, fun _ φ hφ => by simpa using hφ⟩
  have hqcT : IsQuasiCompactSpaceULift.{w} B S hS (pullback (c ≫ g) f) :=
    isQuasiCompactSpaceULift_of_iso B S hS
      (IsPullback.of_id_snd (f := pullback.fst (c ≫ g) f)).isoPullback.symm
      (hf U (c ≫ g) ((uliftYoneda.{w}).obj U)
        (isAlgebraicSpaceULift_uliftYoneda.{w} B S hS U) hUqc (𝟙 _))
  let k : pullback (c ≫ g) f ⟶ pullback g f :=
    pullback.lift (pullback.fst (c ≫ g) f ≫ c) (pullback.snd (c ≫ g) f)
      (by rw [Category.assoc, pullback.condition])
  have hbig : IsPullback (pullback.fst (c ≫ g) f) (k ≫ pullback.snd g f) (c ≫ g) f := by
    simpa only [k, pullback.lift_snd] using IsPullback.of_hasPullback (c ≫ g) f
  have hsquare : IsPullback k (pullback.fst (c ≫ g) f) (pullback.fst g f) c :=
    (hbig.of_bot (by dsimp only [k]; rw [pullback.lift_fst])
      (IsPullback.of_hasPullback g f)).flip
  obtain ⟨V, γ, hVc, hγSurj, hγEtale⟩ := hqcT
  exact ⟨V, γ ≫ k, hVc,
    relative_comp B S hS hγSurj (relative_of_isPullback B S hS hsquare hcSurj),
    (AlgebraicGeometry.Space.isEtaleULift_iff_relative_etale B S hS (γ ≫ k)).mpr
      (relative_comp B S hS
        ((AlgebraicGeometry.Space.isEtaleULift_iff_relative_etale B S hS γ).mp hγEtale)
        (relative_of_isPullback B S hS hsquare hcE))⟩

/-- **Stacks 03XF, part (3)** from the bootstrap test of **Stacks 03XZ**: a morphism of
algebraic spaces over `S` with values in `Type (max w u)` is of finite type as soon as its
base change along every scheme-valued point of its target is. -/
theorem isFiniteTypeULift_of_forall_pullback_fst
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)}
    (hF : IsAlgebraicSpaceULift.{w} B S hS F) (hG : IsAlgebraicSpaceULift.{w} B S hS G)
    (f : F ⟶ G)
    (hf : ∀ (U : BigFppfOver B S hS) (ξ : (uliftYoneda.{w}).obj U ⟶ G),
      IsFiniteTypeULift.{w} B S hS (pullback.fst ξ f)) :
    IsFiniteTypeULift.{w} B S hS f :=
  ⟨isLocallyOfFiniteTypeULift_of_forall_pullback_fst B S hS hF hG f (fun U ξ => (hf U ξ).1),
    isQuasiCompactULift_of_forall_pullback_fst B S hS f (fun U ξ => (hf U ξ).2)⟩

/-! ### The conditions for a morphism of the site -/

/-- A morphism `k` of the big fppf site of `S` whose underlying morphism of schemes has a
property `P` that is étale local on the source and target satisfies the every-chart condition
of **Stacks 03MJ** for `P` in the larger value universe: every commuting square of étale
charts of the universe-lifted Yoneda image of `k` comes, by full faithfulness of the
universe-lifted Yoneda embedding, from a commuting square of the site whose two chart edges
are étale morphisms of schemes, so étale-local cancellation applies. -/
theorem holdsOnEveryEtaleChartULift_uliftYoneda_map {P : MorphismProperty Scheme.{u}}
    (hP : IsEtaleLocalOnSourceAndTarget P) {V U : BigFppfOver B S hS} (k : V ⟶ U)
    (hk : P ((BigFppfOver.toScheme B S hS).map k)) :
    HoldsOnEveryEtaleChartULift.{w} B S hS P ((uliftYoneda.{w}).map k) := by
  intro U' V' a b h ha hb hsq
  obtain ⟨α, rfl⟩ : ∃ α : U' ⟶ V, (uliftYoneda.{w}).map α = a :=
    ⟨(uliftYoneda.{w}).preimage a, by simp⟩
  obtain ⟨β, rfl⟩ : ∃ β : V' ⟶ U, (uliftYoneda.{w}).map β = b :=
    ⟨(uliftYoneda.{w}).preimage b, by simp⟩
  have hsite : h ≫ β = α ≫ k := (uliftYoneda.{w}).map_injective (by simpa using hsq)
  refine hP.of_commSq_etale ((BigFppfOver.toScheme B S hS).map α)
    ((BigFppfOver.toScheme B S hS).map β) ((BigFppfOver.toScheme B S hS).map k) _
    ((AlgebraicGeometry.Space.relative_etale_uliftYoneda_map_iff B S hS α).1 ha)
    ((AlgebraicGeometry.Space.relative_etale_uliftYoneda_map_iff B S hS β).1 hb) hk ?_
  simpa using congrArg (BigFppfOver.toScheme B S hS).map hsite

/-- A morphism of the big fppf site of `S` whose underlying morphism of schemes is locally of
finite type is locally of finite type in the larger value universe. -/
theorem isLocallyOfFiniteTypeULift_uliftYoneda_map {V U : BigFppfOver B S hS} (k : V ⟶ U)
    (hk : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map k)) :
    IsLocallyOfFiniteTypeULift.{w} B S hS ((uliftYoneda.{w}).map k) :=
  holdsOnEveryEtaleChartULift_uliftYoneda_map B S hS
    LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget k hk

/-- A morphism of the big fppf site of `S` whose underlying morphism of schemes is
quasi-compact is quasi-compact in the larger value universe. -/
theorem isQuasiCompactULift_uliftYoneda_map {V U : BigFppfOver B S hS} (k : V ⟶ U)
    (hk : QuasiCompact ((BigFppfOver.toScheme B S hS).map k)) :
    IsQuasiCompactULift.{w} B S hS ((uliftYoneda.{w}).map k) := by
  have : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.QuasiCompact.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange :=
    inverseImage_isStableUnderBaseChange B S hS inferInstance
  exact (isQuasiCompactULift_whiskerRight_iff B S hS (yoneda.map k)).mpr
    (isQuasiCompact_of_presheaf_quasiCompact B S hS (MorphismProperty.relative_map hk))

/-- A morphism of the big fppf site of `S` whose underlying morphism of schemes is locally of
finite type and quasi-compact is of finite type in the larger value universe. -/
theorem isFiniteTypeULift_uliftYoneda_map {V U : BigFppfOver B S hS} (k : V ⟶ U)
    (hk : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map k))
    (hqc : QuasiCompact ((BigFppfOver.toScheme B S hS).map k)) :
    IsFiniteTypeULift.{w} B S hS ((uliftYoneda.{w}).map k) :=
  ⟨isLocallyOfFiniteTypeULift_uliftYoneda_map B S hS k hk,
    isQuasiCompactULift_uliftYoneda_map B S hS k hqc⟩

/-! ### The conditions as properties of morphisms of algebraic spaces -/

/-- Being locally of finite type (**Stacks 03XF**, part (1)), as a property of morphisms in
the category of algebraic spaces over `S` with values in `Type (max w u)`. -/
abbrev locallyOfFiniteTypePropertyULift :
    MorphismProperty (AlgebraicSpacesULift.{w} B S hS) :=
  fun _ _ f => IsLocallyOfFiniteTypeULift.{w} B S hS f.hom

/-- Being quasi-compact (**Stacks 03HE**), as a property of morphisms in the category of
algebraic spaces over `S` with values in `Type (max w u)`. -/
abbrev quasiCompactPropertyULift : MorphismProperty (AlgebraicSpacesULift.{w} B S hS) :=
  fun _ _ f => IsQuasiCompactULift.{w} B S hS f.hom

/-- Being of finite type (**Stacks 03XF**, part (3)), as a property of morphisms in the
category of algebraic spaces over `S` with values in `Type (max w u)`. -/
abbrev finiteTypePropertyULift : MorphismProperty (AlgebraicSpacesULift.{w} B S hS) :=
  fun _ _ f => IsFiniteTypeULift.{w} B S hS f.hom

/-- The morphism of presheaves underlying an isomorphism of algebraic spaces over `S` with
values in `Type (max w u)` is an isomorphism. -/
public theorem isIso_hom_of_iso {X Y : AlgebraicSpacesULift.{w} B S hS} (e : X ≅ Y) :
    IsIso e.hom.hom :=
  ⟨e.inv.hom, congrArg (fun k => k.hom) e.hom_inv_id,
    congrArg (fun k => k.hom) e.inv_hom_id⟩

/-- Being locally of finite type is invariant under isomorphisms of algebraic spaces over
`S` with values in `Type (max w u)`. -/
instance locallyOfFiniteTypePropertyULift_respectsIso :
    (locallyOfFiniteTypePropertyULift.{w} B S hS).RespectsIso := by
  refine MorphismProperty.RespectsIso.mk _ (fun e f hf => ?_) (fun e f hf => ?_)
  · have := isIso_hom_of_iso B S hS e
    exact holdsOnEveryEtaleChartULift_precomp B S hS _ e.hom.hom f.hom hf
  · have := isIso_hom_of_iso B S hS e
    exact holdsOnEveryEtaleChartULift_postcomp B S hS _ e.hom.hom f.hom hf

/-- Quasi-compactness is invariant under isomorphisms of algebraic spaces over `S` with
values in `Type (max w u)`. -/
instance quasiCompactPropertyULift_respectsIso :
    (quasiCompactPropertyULift.{w} B S hS).RespectsIso := by
  refine MorphismProperty.RespectsIso.mk _ (fun e f hf => ?_) (fun e f hf => ?_)
  · have he := isIso_hom_of_iso B S hS e
    exact isQuasiCompactULift_precomp B S hS (asIso e.hom.hom) f.hom hf
  · have he := isIso_hom_of_iso B S hS e
    exact isQuasiCompactULift_postcomp B S hS (asIso e.hom.hom) f.hom hf

/-- Being of finite type is invariant under isomorphisms of algebraic spaces over `S` with
values in `Type (max w u)`. -/
instance finiteTypePropertyULift_respectsIso :
    (finiteTypePropertyULift.{w} B S hS).RespectsIso := by
  refine MorphismProperty.RespectsIso.mk _ (fun e f hf => ⟨?_, ?_⟩) (fun e f hf => ⟨?_, ?_⟩)
  · exact MorphismProperty.RespectsIso.precomp
      (locallyOfFiniteTypePropertyULift.{w} B S hS) e.hom f hf.1
  · exact MorphismProperty.RespectsIso.precomp
      (quasiCompactPropertyULift.{w} B S hS) e.hom f hf.2
  · exact MorphismProperty.RespectsIso.postcomp
      (locallyOfFiniteTypePropertyULift.{w} B S hS) e.hom f hf.1
  · exact MorphismProperty.RespectsIso.postcomp
      (quasiCompactPropertyULift.{w} B S hS) e.hom f hf.2

end AlgebraicGeometry.Space

end
