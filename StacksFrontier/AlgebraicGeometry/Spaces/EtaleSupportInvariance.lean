module

public import Mathlib.CategoryTheory.Limits.Final.Type
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalRingEtaleInvariance
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricPointEtaleLift
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartEquivalenceClosure

/-!
# The support of a sheaf is étale-local

Let `f : X ⟶ Y` be an étale morphism of algebraic spaces over `S`.  Restriction along
postcomposition of étale charts with `f` — the inverse image of the morphism of small étale
topoi of Stacks 03LP — does not change stalks at geometric points: the stalk of a presheaf `P`
on the small étale site of `Y` at the image of a geometric point `ȳ` of `X` is the stalk of the
restriction of `P` at `ȳ`.  Consequently the support of an abelian sheaf, in the sense of
Stacks 04KA, pulls back: the support of the restriction is the inverse image of the support.

The stalk comparison is the same cofinality argument that
`AlgebraicGeometry.Space.etaleLocalRingIsoOfIsEtale` runs for the structure presheaf, and it
reuses the same initiality input, `AlgebraicGeometry.Space.SmallEtaleNeighborhood.postcomp`
being initial.  What this file adds is that the argument needs nothing about the presheaf, so it
applies to an arbitrary one, and that at the level of set-valued stalks it is available with no
smallness hypothesis, because `CategoryTheory.Functor.bijective_colimitTypePrecomp` compares
the quotient colimits directly.

## Main results

* `AlgebraicGeometry.Space.bijective_colimitTypePrecomp_smallEtaleNeighborhoodPostcomp`: the
  canonical map from the stalk of the restriction of `P` at `ȳ` to the stalk of `P` at the
  image of `ȳ` is bijective.  This is the generalization of
  `AlgebraicGeometry.Space.etaleLocalRingIsoOfIsEtale` to an arbitrary presheaf of sets.
* `AlgebraicGeometry.Space.subsingleton_stalkSet_smallEtalePostcomp_iff`: the stalk of the
  restriction vanishes exactly when the stalk at the image vanishes.  No name is given to the
  bijection itself; this criterion is all the support statements consume.
* `AlgebraicGeometry.Space.supportOfSheaf_sheafPushforwardContinuous_smallEtalePostcomp`: the
  support of the restriction of an abelian sheaf along an étale morphism is the inverse image
  of its support.
* `AlgebraicGeometry.Space.supportOfSheaf_toSheaf_etaleModulePullback`: the same for the
  underlying abelian sheaf of the étale pullback of a sheaf of modules
  (`AlgebraicGeometry.Space.etaleModulePullback`), in an arbitrary module universe.
* `AlgebraicGeometry.Space.supportOfSheaf_chartToSpace`: the case of the structure morphism of
  an étale scheme chart, which is the configuration Stacks 07TY is about.  It also exhibits an
  inhabitant of the étaleness hypothesis of the general statement, taken from a proved result
  rather than assumed.

## Implementation notes

The two inclusions of the support equality use different inputs, and neither is formal.

The inclusion `Supp(f⁻¹G) ⊆ |f|⁻¹ Supp(G)` transports a geometric point of `X` forward by
`AlgebraicGeometry.Space.geometricPointMap` and uses the stalk comparison.  The reverse
inclusion has to produce a geometric point of `X` over a prescribed point of `|X|` whose image
is the *given* geometric point of `Y`, which is Stacks 05VN,
`AlgebraicGeometry.Space.exists_geometricPoint_lift_of_isEtale`: an étale morphism lifts a
geometric point without extending its field.  Without that lift the statement would need the
independence of the support of the choice of geometric point over a point of `|X|`, which this
development has only in the shape of Stacks 04KB, part (4),
`AlgebraicGeometry.Space.supportOfSheaf_eq_iUnion_image_supportOfSection`.

What the file does *not* contain, and what Stacks 07TY and 07TZ ask for beyond it:

* the support of a *quasi-coherent module on the scheme* underlying a chart, which Stacks 07TY
  compares with the support on the space.  That is a comparison between the Zariski support of
  a quasi-coherent module and the support of its associated small-étale module, which needs
  Stacks 05VP;
* pullback along a morphism of algebraic spaces that is *not* étale, which is Stacks 07TZ,
  part (3).  There the stalk of the pullback is `F_x̄ ⊗_{𝒪_{X, x̄}} 𝒪_{Y, ȳ}` by Stacks 05VQ,
  and the vanishing criterion needs Nakayama.

Neither of those two inputs is missing from the development: Stacks 05VP is
`AlgebraicGeometry.Space.chartStalkTensorComparison` with
`AlgebraicGeometry.Space.isIso_chartStalkTensorComparison`, Stacks 05VQ's base change is
`AlgebraicGeometry.Space.geometricModuleStalkPullbackIso`, and on them
`StacksFrontier.AlgebraicGeometry.Spaces.SupportGeometricStalkCriterion` proves Stacks 07TY for a
quasi-coherent module and
`StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupportEquality` proves Stacks 07TZ
part (3).  The two tags are absent only from this file, which is imported by the modules that
prove them.

Both restrictions are hypotheses of the étale case only in the sense that the étale case needs
no tensor product at all: `AlgebraicGeometry.Space.etaleModulePullback` is plain restriction of
sections, so the module universe stays free and no change of scalars occurs.

## References

* [Stacks Project, Tag 04KA](https://stacks.math.columbia.edu/tag/04KA)
* [Stacks Project, Tag 04JY](https://stacks.math.columbia.edu/tag/04JY)
* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
* [Stacks Project, Tag 05VN](https://stacks.math.columbia.edu/tag/05VN)
* [Stacks Project, Tag 04KF](https://stacks.math.columbia.edu/tag/04KF)
-/

@[expose] public section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-! ### Stalks are unchanged by an étale morphism -/

/-- The canonical map from the set-valued stalk of the restriction of `P` along an étale
morphism `f : X ⟶ Y`, at a geometric point `ȳ` of `X`, to the set-valued stalk of `P` at the
image of `ȳ` is bijective.

Both stalks are quotient colimits of the *same* diagram of sections, because postcomposition
leaves the underlying object of the big fppf site of a chart unchanged
(`AlgebraicGeometry.Space.SmallEtaleNeighborhood.postcomp_op_comp_sections` is `rfl`); so the
comparison is `CategoryTheory.Functor.colimitTypePrecomp` along a functor which is final,
because `AlgebraicGeometry.Space.SmallEtaleNeighborhood.postcomp` is initial.

This is `AlgebraicGeometry.Space.etaleLocalRingIsoOfIsEtale` with the structure presheaf
replaced by an arbitrary presheaf of sets, and with no smallness hypothesis. -/
theorem bijective_colimitTypePrecomp_smallEtaleNeighborhoodPostcomp
    (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) (y : GeometricPoint B S hS X.1)
    (P : (SmallEtale B S hS Y.1)ᵒᵖ ⥤ Type w) :
    Function.Bijective (Functor.colimitTypePrecomp
      (SmallEtaleNeighborhood.postcomp B S hS f hf y).op
      (SmallEtaleNeighborhood.sections (x := geometricPointMap f.hom y) P)) :=
  have := SmallEtaleNeighborhood.initial_postcomp B S hS f hf y
  Functor.bijective_colimitTypePrecomp _ _

/-- The stalk of the restriction of `P` along an étale morphism at a geometric point `ȳ` of the
source is a subsingleton exactly when the stalk of `P` at the image of `ȳ` is.

The bijection of the stalks is built inline from
`AlgebraicGeometry.Space.bijective_colimitTypePrecomp_smallEtaleNeighborhoodPostcomp`, rather
than given a name of its own: no consumer needs the map, only the criterion.  The two stalks
are spelled as `AlgebraicGeometry.Space.stalkSet`, which is the form in which the support of
Stacks 04KA is defined. -/
theorem subsingleton_stalkSet_smallEtalePostcomp_iff
    (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) (y : GeometricPoint B S hS X.1)
    (P : (SmallEtale B S hS Y.1)ᵒᵖ ⥤ Type w) :
    Subsingleton (stalkSet y ((smallEtalePostcomp B S hS f hf).op ⋙ P)) ↔
      Subsingleton (stalkSet (geometricPointMap f.hom y) P) :=
  (Equiv.ofBijective _
    (bijective_colimitTypePrecomp_smallEtaleNeighborhoodPostcomp B S hS f hf y P)
      : stalkSet y ((smallEtalePostcomp B S hS f hf).op ⋙ P) ≃
          stalkSet (geometricPointMap f.hom y) P).subsingleton_congr

/-! ### The support pulls back along an étale morphism -/

/-- **The support of an abelian sheaf is étale-local.** For an étale morphism `f : X ⟶ Y` of
algebraic spaces, the support of the restriction of `G` along postcomposition of étale charts
with `f` is the inverse image, under the induced map on points, of the support of `G`.

This is the small-étale-site form of the support statements of Stacks 07TY and of Stacks 07TZ,
part (3); see the implementation notes of this file for what separates it from either. -/
theorem supportOfSheaf_sheafPushforwardContinuous_smallEtalePostcomp
    (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    (G : Sheaf (SmallEtale.topology B S hS Y.1) AddCommGrpCat.{w}) :
    supportOfSheaf B S hS X.1
        (((smallEtalePostcomp B S hS f hf).sheafPushforwardContinuous
          AddCommGrpCat.{w} (SmallEtale.topology B S hS X.1)
          (SmallEtale.topology B S hS Y.1)).obj G) =
      pointsMap B S hS X.1 f.hom ⁻¹' supportOfSheaf B S hS Y.1 G := by
  have key := fun p => subsingleton_stalkSet_smallEtalePostcomp_iff B S hS f hf p
    (G.obj ⋙ forget AddCommGrpCat.{w})
  ext x
  constructor
  · rintro ⟨p, hp, hn⟩
    refine ⟨geometricPointMap f.hom p, ?_, hn ∘ (key p).mpr⟩
    exact (geometricPointMap_image ..).trans (congrArg _ hp)
  · rintro ⟨q, hq, hn⟩
    obtain ⟨p, hp, hval⟩ :=
      exists_geometricPoint_lift_of_isEtale B S hS X.2 Y.2 f.hom hf q x hq.symm
    obtain rfl : geometricPointMap f.hom p = q := Subtype.ext hval
    exact ⟨p, hp, hn ∘ (key p).mp⟩

/-- **The support of a sheaf of modules is étale-local.** The support of the underlying abelian
sheaf of the étale pullback of a sheaf of `𝒪_Y`-modules along an étale morphism `f : X ⟶ Y` is
the inverse image of the support of the underlying abelian sheaf of the module.

The module universe is arbitrary, because `AlgebraicGeometry.Space.etaleModulePullback` is
restriction of sections and performs no change of scalars: the underlying abelian sheaf of the
pullback is the restriction of the underlying abelian sheaf, on the nose. -/
theorem supportOfSheaf_toSheaf_etaleModulePullback
    (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) (M : Modules.{u, w} B S hS Y.1 Y.2) :
    supportOfSheaf B S hS X.1
        ((SheafOfModules.toSheaf _).obj ((etaleModulePullback B S hS f hf).obj M)) =
      pointsMap B S hS X.1 f.hom ⁻¹'
        supportOfSheaf B S hS Y.1 ((SheafOfModules.toSheaf _).obj M) :=
  supportOfSheaf_sheafPushforwardContinuous_smallEtalePostcomp B S hS f hf
    ((SheafOfModules.toSheaf _).obj M)

/-- The support of the restriction of a sheaf of modules to an étale scheme chart of `X` is the
inverse image of its support on `X`, under the map on points of the structure morphism of the
chart.

This is the configuration of Stacks 07TY — a chart `U ⟶ X` with `U` a scheme and a module on
`X` restricted to it — with the support on the chart taken on its small étale site rather than
as a quasi-coherent module on the scheme `U`.  It also discharges the étaleness hypothesis of
`AlgebraicGeometry.Space.supportOfSheaf_toSheaf_etaleModulePullback` from a proved result,
`AlgebraicGeometry.Space.isEtale_chartToSpace`, for every algebraic space and every object of
its small étale site; so that hypothesis is inhabited and the general statement is not
vacuous. -/
theorem supportOfSheaf_chartToSpace (X : AlgebraicSpaces B S hS) (U : SmallEtale B S hS X.1)
    (M : Modules.{u, w} B S hS X.1 X.2) :
    supportOfSheaf B S hS (chartSpace B S hS X U).1
        ((SheafOfModules.toSheaf _).obj ((etaleModulePullback B S hS
          (chartToSpace B S hS X U) (isEtale_chartToSpace B S hS X U)).obj M)) =
      pointsMap B S hS (chartSpace B S hS X U).1 (chartToSpace B S hS X U).hom ⁻¹'
        supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj M) :=
  supportOfSheaf_toSheaf_etaleModulePullback B S hS _ _ M

end AlgebraicGeometry.Space

end
