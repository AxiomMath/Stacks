module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import StacksFrontier.AlgebraicGeometry.FiniteEtaleColimits.BaseChangeCoproducts
public import StacksFrontier.AlgebraicGeometry.FiniteEtaleColimits.LocalCoequalizer
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.EtaleFundamentalGroup

/-!
# Base change of finite étale covers and finite colimits

Let `X` be a scheme. Base change of finite étale covers along any morphism `g : P ⟶ X` preserves
finite coproducts, because a finite coproduct in `FÉt_X` is a disjoint union of schemes, finite
coproducts of schemes are van Kampen, and a cocone of finite étale covers is a colimit as soon as
its underlying cocone of schemes is one.

Base change along the morphism `Spec Ω ⟶ X` of a geometric point preserves *all* finite colimits.
The geometric point factors through an étale neighbourhood of its image over which both covers of a
given pair of morphisms split and both morphisms are induced by maps of the index sets, because the
residue field is separably closed; the coequalizer is preserved by the flat base change to that
neighbourhood, and over the neighbourhood it is a split cover, which base change preserves along
any morphism at all. This is the fourth assertion of Stacks Tag 0BN9 for the morphism from the
spectrum of the residue field of a geometric point.

## Main definitions

* `Stacks.FundamentalGroup.baseChangeFstNatTrans` — the projections from the base changes of a
  finite family of covers to the covers themselves, as a morphism of diagrams.

## Main results

* `Stacks.FundamentalGroup.isColimitMapCoconeSigmaCocone` — the cocone exhibiting a finite
  coproduct of covers, base-changed along any morphism, is still a colimit.
* `Stacks.FundamentalGroup.preservesColimit_parallelPair_finiteEtaleBaseChange_geometricPoint` —
  base change along a geometric point preserves coequalizers.
* `Stacks.FundamentalGroup.preservesFiniteColimits_finiteEtaleBaseChange_geometricPoint` —
  **base change along a geometric point preserves finite colimits.**

## References

* [Stacks Project, Tag 0BN9](https://stacks.math.columbia.edu/tag/0BN9)
* [Stacks Project, Tag 0BNA](https://stacks.math.columbia.edu/tag/0BNA)
* [Stacks Project, Tag 0BNB](https://stacks.math.columbia.edu/tag/0BNB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe v u

namespace Stacks.FundamentalGroup

/-! ### Base change preserves finite coproducts -/

section Coproducts

variable {X P : Scheme.{u}} (g : P ⟶ X) {J : Type} [Fintype J]
  (D : Discrete J ⥤ FiniteEtaleOver X)

/-- The projections from the base changes of a finite family of finite étale covers to the covers
themselves, as a morphism of the two diagrams of underlying schemes. -/
def baseChangeFstNatTrans :
    (D ⋙ finiteEtaleBaseChange g) ⋙ finiteEtaleOverForget P ⟶ D ⋙ finiteEtaleOverForget X :=
  Discrete.natTrans fun j => pullback.fst (D.obj j).hom g

/-- **Base change of finite étale covers preserves finite coproducts.** The base change along `g`
of the cocone `sigmaCocone X D` exhibiting a finite coproduct of finite étale covers is a colimit
cocone. -/
def isColimitMapCoconeSigmaCocone :
    IsColimit ((finiteEtaleBaseChange g).mapCocone (sigmaCocone X D)) := by
  refine isColimitOfIsColimitCoconeLeft _ ?_
  refine ((FinitaryPreExtensive.isUniversal_finiteCoproducts (coproductIsCoproduct' _))
    (coconeLeft ((finiteEtaleBaseChange g).mapCocone (sigmaCocone X D)))
    (baseChangeFstNatTrans g D) (pullback.fst (sigmaCocone X D).pt.hom g) ?_
    (NatTrans.Equifibered.of_discrete _) fun j => ?_).some
  · refine NatTrans.ext (funext fun j => ?_)
    exact (pullback.lift_fst _ _ _).symm
  · exact (isPullback_baseChange_left' g ((finiteEtaleOverForgetOver X).map
      ((sigmaCocone X D).ι.app j))).flip

end Coproducts

/-! ### Base change along a geometric point -/

section Point

variable {X : Scheme.{u}} (x : GeometricPoint X)

/-- **Base change along a geometric point preserves coequalizers of finite étale covers.** For
morphisms `a b : Y ⟶ Z` of finite étale covers of `X`, base change along a geometric point of `X`
preserves the coequalizer of `a` and `b`. -/
instance preservesColimit_parallelPair_finiteEtaleBaseChange_geometricPoint
    {Y Z : FiniteEtaleOver X}
    (a b : Y ⟶ Z) : PreservesColimit (parallelPair a b) (finiteEtaleBaseChange x.hom) := by
  obtain ⟨P, g, hg, p, hp, -, hcol⟩ :=
    exists_etale_isColimit_baseChangeCofork a b (x.hom.base default)
  have := hg
  obtain ⟨l, hl, -⟩ := Scheme.exists_fac_of_etale_of_isSepClosed g x.hom p hp
  refine preservesColimit_of_preserves_colimit_cocone (isColimit_finiteEtaleCofork a b)
    ((isColimitMapCoconeCoforkEquiv _ _).symm ?_)
  exact (hcol x.source l x.hom hl.symm _ (isColimit_finiteEtaleCofork a b)).some

/-- Base change along a geometric point preserves all coequalizers of finite étale covers. -/
instance preservesColimitsOfShape_walkingParallelPair_finiteEtaleBaseChange_geometricPoint :
    PreservesColimitsOfShape WalkingParallelPair (finiteEtaleBaseChange x.hom) where
  preservesColimit {K} := preservesColimit_of_iso_diagram _ (diagramIsoParallelPair K).symm

/-- **Base change along a geometric point preserves finite colimits of finite étale covers.** This
is the fourth assertion of Stacks Tag 0BN9 for the morphism from the spectrum of the residue field
of a geometric point. -/
theorem preservesFiniteColimits_finiteEtaleBaseChange_geometricPoint :
    PreservesFiniteColimits (finiteEtaleBaseChange x.hom) :=
  preservesFiniteColimits_of_preservesCoequalizers_and_finiteCoproducts _

end Point

end Stacks.FundamentalGroup

end
