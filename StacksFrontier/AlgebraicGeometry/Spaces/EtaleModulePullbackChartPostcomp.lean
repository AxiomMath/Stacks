module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleRestrictionPullback

/-!
# Restricting an étale pullback to a chart

Let `j : X' ⟶ X` be an étale morphism of algebraic spaces and `W` an étale scheme chart of `X'`.
An `𝒪_X`-module `M` can be read on the Zariski site of the scheme underlying `W` in two ways:
restrict the étale pullback `j^*M` to the chart `W`, or restrict `M` to the chart `j ∘ W` of `X`.
The two are **the same module**.  This is the general form of
`AlgebraicGeometry.Space.restrictToChart_etaleModulePullback_selfChart`, with the same proof:
both are the Zariski sheafification of one presheaf of modules, the index functors and the changes
of scalars agreeing on the nose.

## Main results

* `AlgebraicGeometry.Space.chartRestrictionPresheaf_etaleModulePullback_postcomp`: the presheaves
  of modules underlying the two restrictions are equal.
* `AlgebraicGeometry.Space.restrictToChart_etaleModulePullback_postcomp`: `(j^*M)|_W = M|_{j ∘ W}`
  as sheaves of modules on the scheme underlying `W`.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe m u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X X' : AlgebraicSpaces B S hS}

/-- **The presheaf of modules underlying the two chart restrictions of an étale pullback is the
same.**  The sections of `j^*M` over the Zariski opens of a chart `W` of `X'` are the sections of
`M` over the same opens read as charts of `X` through `j`, over the same ring of regular functions;
this is the collapse of two pushforwards into one,
`Stacks.SheafOfModules.pushforward_ulift_pushforward_id`. -/
theorem chartRestrictionPresheaf_etaleModulePullback_postcomp (j : X' ⟶ X)
    (hj : IsEtale B S hS j.hom) (M : Modules.{u, m} B S hS X.1 X.2)
    (W : SmallEtale B S hS X'.1) :
    chartRestrictionPresheaf B S hS X'.2 ((etaleModulePullback B S hS j hj).obj M) W =
      chartRestrictionPresheaf B S hS X.2 M ((smallEtalePostcomp B S hS j hj).obj W) :=
  Stacks.SheafOfModules.pushforward_ulift_pushforward_id
    (F := chartOpens B S hS W)
    (G := smallEtalePostcomp B S hS j hj)
    (K := (smallEtaleRingedSite B S hS X'.1 X'.2).J)
    (L := (smallEtaleRingedSite B S hS X.1 X.2).J)
    (R := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
    (hcont := smallEtaleRingedSite_isContinuous_smallEtalePostcomp B S hS j hj)
    (chartRestrictionRingHom B S hS X.2 ((smallEtalePostcomp B S hS j hj).obj W)) M

/-- **The restriction to a chart of an étale pullback is the restriction to the composite
chart.**  For `j : X' ⟶ X` étale, `W` a chart of `X'` and `M` an `𝒪_X`-module,
`(j^*M)|_W = M|_{j ∘ W}` as sheaves of modules on the scheme underlying `W`. -/
theorem restrictToChart_etaleModulePullback_postcomp (j : X' ⟶ X)
    (hj : IsEtale B S hS j.hom) (M : Modules.{u, m} B S hS X.1 X.2)
    (W : SmallEtale B S hS X'.1) :
    restrictToChart B S hS X'.2 ((etaleModulePullback B S hS j hj).obj M) W =
      restrictToChart B S hS X.2 M ((smallEtalePostcomp B S hS j hj).obj W) := by
  let : HasSheafify (Opens.grothendieckTopology (etaleChartScheme B S hS W))
      AddCommGrpCat.{max u m} :=
    hasSheafifyEssentiallySmallSite _ _
  let : (Opens.grothendieckTopology (etaleChartScheme B S hS W)).WEqualsLocallyBijective
      AddCommGrpCat.{max u m} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  exact congrArg
    (PresheafOfModules.sheafification (𝟙 (etaleChartScheme B S hS W).ringCatSheaf.obj)).obj
    (chartRestrictionPresheaf_etaleModulePullback_postcomp B S hS j hj M W)

end AlgebraicGeometry.Space

end
