module

public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorBaseChangeChartRatioUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicChartFunctionField

/-!
# The germ square for the flat pullback of a meromorphic function

Let `X` be an algebraic space over a scheme `S`, let `Z ⊂ X` be a prime divisor with generic
point `ξ`, let `j : Spec(𝒪_{U, u}) ⟶ X` be the chart at `ξ`, let `V` be an étale chart of `X`
with integral affine scheme and let `ι : Q ⟶ V ×_X Spec(𝒪_{U, u})` be a chart of
`Spec(𝒪_{U, u})` over the base change of `V`. A point `q` of `chartScheme Q` has an image in
`chartScheme V`, and a meromorphic function of `V` can be read in `Frac(𝒪_{Q, q})` in two ways:

* through the function field of `V` — `𝒦_X(V) ≃ R(chartScheme V)` by Stacks 0EN6, part (2) — and
  the stalk map of `chartScheme Q ⟶ chartScheme V` at `q`; or
* through the flat pullback of meromorphic functions along `j`, restricted to `Q`, and the germ
  at `q`.

**The two agree.** That is the content of this file, and it is the last step of the flat-descent
route of Stacks 0EPX as the roadmap of
`StacksFrontier/AlgebraicGeometry/Spaces/PicardWeilDivisorClassInjective.lean` records it. Applied
to `AlgebraicGeometry.Space.chartRatio`, whose pullback is a unit regular function on `Q` by
`AlgebraicGeometry.Space.PrimeDivisor.exists_sieve_isUnit_baseChangeChartRatio`, it makes that
ratio a unit of `𝒪_{Q, q}` *read through the function field of `V`*, which is the shape the
faithfully flat descent
`Stacks.FaithfullyFlatFractionUnit.exists_isUnit_eq_algebraMap_of_isUnit_of_faithfullyFlat`
consumes.

Nothing in the development related `AlgebraicGeometry.Space.chartMeromorphicPullbackHom` to a
stalk before this: its lemmas are all about restriction and about regular functions.

## The form of the statement

The two comparison maps are **hypotheses**, given with their defining equations on the regular
functions rather than constructed here. That is the idiom of
`AlgebraicGeometry.exists_isUnit_eq_appTop_of_isUnit_of_flat`, and for the same reason: each is a
localization lift, the unit conditions that build it are flatness facts about a particular
geometric situation, and a consumer that has built them at its own spelling of the two rings of
regular functions can pass them by name. The statement is not weaker for it — the hypotheses are
exactly the defining property of the lifts, and they determine both composites, `𝒦_X(V)` being a
localization of `𝒪_X(V)`.

The point of `chartScheme V` is the *image* of `q` rather than a point with an equation to it, so
that no germ has to be transported across a propositional equality of points; a consumer holding
a point `z` and a proof that `q` lies over it substitutes, exactly as
`AlgebraicGeometry.isIso_germ_top_of_eq_closedPoint` is set up to allow.

## Main results

* `AlgebraicGeometry.Space.PrimeDivisor.genericStalkBaseChangeSchemeMap`: the morphism of schemes
  from a chart over the base change of `V` down to `V`.
* `AlgebraicGeometry.Space.PrimeDivisor.appTop_genericStalkBaseChangeSchemeMap`: its map of
  regular functions is restriction along `ι` after the chart diagram's.
* `AlgebraicGeometry.Space.PrimeDivisor.lift_chartMeromorphicFunctionFieldEquiv_eq`: the germ
  square.

## References

* [Stacks Project, Tag 0EN6](https://stacks.math.columbia.edu/tag/0EN6)
* [Stacks Project, Tag 0EPX](https://stacks.math.columbia.edu/tag/0EPX)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry.Space

-- `chartMeromorphicAlgebra` is deliberately *not* a local instance here: it and
-- `chartMeromorphicFunctionAlgebra` are two definitionally equal `Algebra` structures on
-- definitionally equal spellings of the same pair of rings, and with both in scope instance
-- search picks between them unpredictably, so that an `algebraMap` written here and one inside a
-- cited lemma are different terms and no rewrite matches.
attribute [local instance] pointTopology
attribute [local instance] chartMeromorphicFunctionAlgebra chartFunctionFieldAlgebra
attribute [local instance] nonempty_top_chartScheme

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : AlgebraicSpaces B S hS}
    (hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS X, localRingDimension B S hS z = 0)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X.1)
    (hdec : IsDecentSpace B S hS X.1) (Z : PrimeDivisor B S hS X.1)

/-- **The morphism of schemes from a chart of `Spec(𝒪_{U, u})` over the base change of `V` down
to `V`.** It is the chart morphism `ι` followed by the vertical morphism of the cartesian square
`AlgebraicGeometry.Space.PrimeDivisor.genericStalkBaseChangeDiagram`, read on schemes.

It is given as a composite of two morphisms of schemes rather than as the morphism of schemes
beneath a composite of morphisms of charts, so that `AlgebraicGeometry.Scheme.Hom.comp_appTop`
applies to it definitionally. -/
abbrev PrimeDivisor.genericStalkBaseChangeSchemeMap (V : SmallEtale B S hS X.1)
    {Q : SmallEtale B S hS (Z.genericStalkSpace B S hS X.2 hdec).1}
    (ι : Q ⟶ Z.genericStalkBaseChangeChart B S hS X.2 hdec V) :
    chartScheme Q ⟶ chartScheme V :=
  chartSchemeMap ι ≫
    (BigFppfOver.toScheme B S hS).map (Z.genericStalkBaseChangeDiagram B S hS X.2 hdec V).g

/-- **The regular functions along that morphism**: restriction along the chart diagram of the
base change, followed by restriction along `ι`.

Both identifications are definitional — `AlgebraicGeometry.Space.chartDiagramRestrict_eq_appTop`
for the chart diagram, the structure presheaf of the small étale site being global regular
functions on the underlying schemes, and `AlgebraicGeometry.Scheme.Hom.comp_appTop` for the
composite. -/
theorem PrimeDivisor.appTop_genericStalkBaseChangeSchemeMap (V : SmallEtale B S hS X.1)
    {Q : SmallEtale B S hS (Z.genericStalkSpace B S hS X.2 hdec).1}
    (ι : Q ⟶ Z.genericStalkBaseChangeChart B S hS X.2 hdec V)
    (a : (structurePresheaf B S hS X.1).obj (op V)) :
    (Z.genericStalkBaseChangeSchemeMap B S hS hdec V ι).appTop.hom a =
      ((structurePresheaf B S hS (Z.genericStalkSpace B S hS X.2 hdec).1).map ι.op).hom
        (chartDiagramRestrict B S hS (Z.genericStalkMorphism B S hS X.2 hdec)
          (Z.genericStalkBaseChangeDiagram B S hS X.2 hdec V) a) :=
  rfl

/-- **The morphism of schemes down to `V` is flat.** It is a morphism of étale charts of
`Spec(𝒪_{U, u})`, hence étale by Stacks 03EC, part (2)
(`AlgebraicGeometry.Space.etale_toOver_map_of_smallEtale`) and so flat, followed by the morphism
beneath the base-change chart diagram, which is flat because `j` is
(`AlgebraicGeometry.Space.PrimeDivisor.flat_genericStalkBaseChangeDiagram_g`).

This is what makes `AlgebraicGeometry.Flat.stalkMap` available at a point of `chartScheme Q`, and
with it both the unit conditions of the two localization lifts the germ square below compares
and — a stalk map of schemes being local — the faithful flatness that descends a unit of
`𝒪_{Q, q}` to one of `𝒪_{V, z}`. -/
theorem PrimeDivisor.flat_genericStalkBaseChangeSchemeMap (V : SmallEtale B S hS X.1)
    {Q : SmallEtale B S hS (Z.genericStalkSpace B S hS X.2 hdec).1}
    (ι : Q ⟶ Z.genericStalkBaseChangeChart B S hS X.2 hdec V) :
    AlgebraicGeometry.Flat (Z.genericStalkBaseChangeSchemeMap B S hS hdec V ι) := by
  have he : AlgebraicGeometry.Etale (chartSchemeMap ι) :=
    etale_toOver_map_of_smallEtale B S hS ι
  have h1 : AlgebraicGeometry.Flat (chartSchemeMap ι) :=
    (AlgebraicGeometry.Etale.iff_flat_and_formallyUnramified.mp he).1
  have h2 : AlgebraicGeometry.Flat
      ((BigFppfOver.toScheme B S hS).map
        (Z.genericStalkBaseChangeDiagram B S hS X.2 hdec V).g) :=
    Z.flat_genericStalkBaseChangeDiagram_g B S hS X.2 hdec V
  exact MorphismProperty.comp_mem @AlgebraicGeometry.Flat _ _ h1 h2

/-- **The germ square for the flat pullback of a meromorphic function.** Reading a meromorphic
function of the étale chart `V` of `X` in `Frac(𝒪_{Q, q})` through the function field of
`chartScheme V` and the stalk map at `q` gives the same element as pulling it back along
`j : Spec(𝒪_{U, u}) ⟶ X`, restricting to the chart `Q` and taking the germ at `q`.

Both sides are ring homomorphisms out of `𝒦_X(V)`, which is the total ring of fractions of
`𝒪_X(V)` by Stacks 0EN6, part (2)
(`AlgebraicGeometry.Space.isFractionRing_meromorphicFunctionSheaf_obj`), so they are determined
by their values on regular functions, and there each side is the germ at `q` of the restriction
of the function to `Q`: on the left by
`AlgebraicGeometry.Space.chartMeromorphicFunctionFieldEquiv_algebraMap`, Mathlib's
`AlgebraicGeometry.Scheme.algebraMap_germ_eq_germToFunctionField` and
`AlgebraicGeometry.Scheme.Hom.germ_stalkMap_apply`; on the right by
`AlgebraicGeometry.Space.chartMeromorphicFunctionPullback_algebraMap`, which is the coefficient
square of the pullback, and `AlgebraicGeometry.Space.meromorphicFunctionSheaf_map_algebraMap`,
after which the two readings of the restricted regular function agree by
`AlgebraicGeometry.Space.PrimeDivisor.appTop_genericStalkBaseChangeSchemeMap`.

This is the last unbuilt step of the flat-descent route of Stacks 0EPX. -/
theorem PrimeDivisor.lift_chartMeromorphicFunctionFieldEquiv_eq (V : SmallEtale B S hS X.1)
    [AlgebraicGeometry.IsIntegral (chartScheme V)] (hV : IsAffine (chartScheme V))
    {Q : SmallEtale B S hS (Z.genericStalkSpace B S hS X.2 hdec).1}
    (ι : Q ⟶ Z.genericStalkBaseChangeChart B S hS X.2 hdec V) (q : chartScheme Q)
    (fV : ↥(chartScheme V).functionField →+*
      FractionRing ↥((chartScheme Q).presheaf.stalk q))
    (hfV : ∀ r : ↥((chartScheme V).presheaf.stalk
        ((Z.genericStalkBaseChangeSchemeMap B S hS hdec V ι).base q)),
      fV (algebraMap _ _ r) =
        algebraMap _ _ (((Z.genericStalkBaseChangeSchemeMap B S hS hdec V ι).stalkMap q).hom r))
    (gQ : ((meromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS X.2 hdec).1
          (Z.genericStalkSpace B S hS X.2 hdec).2).obj.obj (op Q)) →+*
      FractionRing ↥((chartScheme Q).presheaf.stalk q))
    (hgQ : ∀ s : (structurePresheaf B S hS
        (Z.genericStalkSpace B S hS X.2 hdec).1).obj (op Q),
      gQ (algebraMap _ _ s) =
        algebraMap _ _ ((chartScheme Q).presheaf.germ ⊤ q trivial s))
    (c : (meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op V)) :
    fV (chartMeromorphicFunctionFieldEquiv B S hS X hwa hfin V hV c) =
      gQ (((meromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS X.2 hdec).1
            (Z.genericStalkSpace B S hS X.2 hdec).2).obj.map ι.op).hom
        (chartMeromorphicPullbackHom B S hS (Z.genericStalkMorphism B S hS X.2 hdec)
          (Z.pullbacksMeromorphicSections_genericStalkMorphism B S hS X.2 hdec)
          (Z.genericStalkBaseChangeDiagram B S hS X.2 hdec V) c)) := by
  have := isFractionRing_meromorphicFunctionSheaf_obj B S hS X hwa hfin V hV
  have key : fV.comp
        (chartMeromorphicFunctionFieldEquiv B S hS X hwa hfin V hV).toRingEquiv.toRingHom =
      gQ.comp ((((meromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS X.2 hdec).1
            (Z.genericStalkSpace B S hS X.2 hdec).2).obj.map ι.op).hom).comp
        (chartMeromorphicPullbackHom B S hS (Z.genericStalkMorphism B S hS X.2 hdec)
          (Z.pullbacksMeromorphicSections_genericStalkMorphism B S hS X.2 hdec)
          (Z.genericStalkBaseChangeDiagram B S hS X.2 hdec V))) := by
    refine IsLocalization.ringHom_ext ((structurePresheaf B S hS X.1).obj (op V))⁰
      (RingHom.ext fun a => ?_)
    have hL : fV (chartMeromorphicFunctionFieldEquiv B S hS X hwa hfin V hV
          (algebraMap ((structurePresheaf B S hS X.1).obj (op V))
            ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op V)) a)) =
        algebraMap ↥((chartScheme Q).presheaf.stalk q)
            (FractionRing ↥((chartScheme Q).presheaf.stalk q))
          (((Z.genericStalkBaseChangeSchemeMap B S hS hdec V ι).stalkMap q).hom
            ((chartScheme V).presheaf.germ ⊤
              ((Z.genericStalkBaseChangeSchemeMap B S hS hdec V ι).base q) trivial a)) := by
      rw [chartMeromorphicFunctionFieldEquiv_algebraMap B S hS X hwa hfin V hV a,
        ← Scheme.algebraMap_germ_eq_germToFunctionField
          (X := chartScheme V) (U := ⊤)
          (x := (Z.genericStalkBaseChangeSchemeMap B S hS hdec V ι).base q) trivial a]
      exact hfV _
    have hR : gQ (((meromorphicFunctionSheaf B S hS
            (Z.genericStalkSpace B S hS X.2 hdec).1
            (Z.genericStalkSpace B S hS X.2 hdec).2).obj.map ι.op).hom
          (chartMeromorphicPullbackHom B S hS (Z.genericStalkMorphism B S hS X.2 hdec)
            (Z.pullbacksMeromorphicSections_genericStalkMorphism B S hS X.2 hdec)
            (Z.genericStalkBaseChangeDiagram B S hS X.2 hdec V)
            (algebraMap ((structurePresheaf B S hS X.1).obj (op V))
              ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op V)) a))) =
        algebraMap ↥((chartScheme Q).presheaf.stalk q)
            (FractionRing ↥((chartScheme Q).presheaf.stalk q))
          ((chartScheme Q).presheaf.germ ⊤ q trivial
            ((Z.genericStalkBaseChangeSchemeMap B S hS hdec V ι).appTop.hom a)) := by
      have hpull : chartMeromorphicPullbackHom B S hS
            (Z.genericStalkMorphism B S hS X.2 hdec)
            (Z.pullbacksMeromorphicSections_genericStalkMorphism B S hS X.2 hdec)
            (Z.genericStalkBaseChangeDiagram B S hS X.2 hdec V)
            (algebraMap ((structurePresheaf B S hS X.1).obj (op V))
              ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op V)) a) =
          algebraMap ((structurePresheaf B S hS
                (Z.genericStalkSpace B S hS X.2 hdec).1).obj
              (op (Z.genericStalkBaseChangeChart B S hS X.2 hdec V)))
            ((meromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS X.2 hdec).1
              (Z.genericStalkSpace B S hS X.2 hdec).2).obj.obj
                (op (Z.genericStalkBaseChangeChart B S hS X.2 hdec V)))
            (chartDiagramRestrict B S hS (Z.genericStalkMorphism B S hS X.2 hdec)
              (Z.genericStalkBaseChangeDiagram B S hS X.2 hdec V) a) :=
        RingHom.congr_fun (chartMeromorphicFunctionPullback_algebraMap B S hS
          (Z.genericStalkMorphism B S hS X.2 hdec)
          (Z.pullbacksMeromorphicSections_genericStalkMorphism B S hS X.2 hdec)
          (Z.genericStalkBaseChangeDiagram B S hS X.2 hdec V)) a
      have hres : ((meromorphicFunctionSheaf B S hS
              (Z.genericStalkSpace B S hS X.2 hdec).1
              (Z.genericStalkSpace B S hS X.2 hdec).2).obj.map ι.op).hom
            (algebraMap ((structurePresheaf B S hS
                  (Z.genericStalkSpace B S hS X.2 hdec).1).obj
                (op (Z.genericStalkBaseChangeChart B S hS X.2 hdec V)))
              ((meromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS X.2 hdec).1
                (Z.genericStalkSpace B S hS X.2 hdec).2).obj.obj
                  (op (Z.genericStalkBaseChangeChart B S hS X.2 hdec V)))
              (chartDiagramRestrict B S hS (Z.genericStalkMorphism B S hS X.2 hdec)
                (Z.genericStalkBaseChangeDiagram B S hS X.2 hdec V) a)) =
          algebraMap ((structurePresheaf B S hS
                (Z.genericStalkSpace B S hS X.2 hdec).1).obj (op Q))
            ((meromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS X.2 hdec).1
              (Z.genericStalkSpace B S hS X.2 hdec).2).obj.obj (op Q))
            ((structurePresheaf B S hS (Z.genericStalkSpace B S hS X.2 hdec).1).map ι.op
              (chartDiagramRestrict B S hS (Z.genericStalkMorphism B S hS X.2 hdec)
                (Z.genericStalkBaseChangeDiagram B S hS X.2 hdec V) a)) :=
        meromorphicFunctionSheaf_map_algebraMap B S hS
          (Z.genericStalkSpace B S hS X.2 hdec) ι _
      exact (congrArg gQ
        ((congrArg (fun x => ((meromorphicFunctionSheaf B S hS
              (Z.genericStalkSpace B S hS X.2 hdec).1
              (Z.genericStalkSpace B S hS X.2 hdec).2).obj.map ι.op).hom x)
            hpull).trans hres)).trans (hgQ _)
    refine hL.trans (Eq.trans ?_ hR.symm)
    refine congrArg (algebraMap ↥((chartScheme Q).presheaf.stalk q)
      (FractionRing ↥((chartScheme Q).presheaf.stalk q))) ?_
    exact Scheme.Hom.germ_stalkMap_apply
      (Z.genericStalkBaseChangeSchemeMap B S hS hdec V ι) ⊤ q trivial a
  exact RingHom.congr_fun key c

end AlgebraicGeometry.Space

end
