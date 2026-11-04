module

public import StacksFrontier.AlgebraicGeometry.Crystalline.FiniteLevelTower
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ChangeBaseConnectedLimits
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.Formula07MK
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LowerShriekAbelianExact

/-!
# Restriction along change of crystalline base preserves injectives

Restriction of abelian sheaves from the big crystalline site to the small one, and restriction
along the change of base functor `Cris(X/S) ⥤ Cris(X'/S')` of [Stacks, Tag 07KL], carry injective
abelian sheaves to injective abelian sheaves. In both cases restriction is right adjoint to a lower
shriek that is exact on abelian sheaves, by [Stacks, Tag 00X4]: the source site has fibre products
and equalizers and the functor preserves them. A right adjoint of a monomorphism-preserving functor
preserves injective objects, [Stacks, Tag 015Z].

For the functor `Cris(U/T) ⥤ Cris(X/S)` of the situation `U/T` of [Stacks, Tag 07MJ] this says that
restriction along it, the pullback `F ↦ F_U` along `(U/T)_cris ⟶ (X/S)_cris`, carries injective
abelian sheaves to injective abelian sheaves. No localization at a sheaf, as in [Stacks, Tag 0791],
is involved.

## Main results

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `preservesInjectiveObjects_smallRestriction`: restriction `π_{X, *} = i_X^{-1}` from the big
  crystalline site to the small one carries injective abelian sheaves to injective abelian sheaves.
* `smallChangeBaseAbelianRestriction`: restriction of abelian sheaves along the change of base
  functor `Cris(X/S) ⥤ Cris(X'/S')` of [Stacks, Tag 07KL].
* `preservesFiniteLimits_smallChangeBaseAbelianLowerShriek`: its left adjoint is exact.
* `preservesInjectiveObjects_smallChangeBaseAbelianRestriction`: restriction along change of base
  preserves injective abelian sheaves.
* `pullbackSmallChangeBase`: the functor `Cris(U/T) ⥤ Cris(X/S)` of the situation `U/T` of
  [Stacks, Tag 07MJ].
* `preservesInjectiveObjects_pullbackAbelianRestriction`: restriction along it,
  `pullbackAbelianRestriction`, preserves injective abelian sheaves.

## References

* [Stacks Project, Tag 07MJ](https://stacks.math.columbia.edu/tag/07MJ)
* [Stacks Project, Tag 07MK](https://stacks.math.columbia.edu/tag/07MK)
* [Stacks Project, Tag 0791](https://stacks.math.columbia.edu/tag/0791)
* [Stacks Project, Tag 07KL](https://stacks.math.columbia.edu/tag/07KL)
* [Stacks Project, Tag 00X4](https://stacks.math.columbia.edu/tag/00X4)
* [Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

/-! ### Restriction to the small crystalline site preserves injectives -/

/-- `π_{X, *} = i_X^{-1}`, restriction along the inclusion `Cris(X/S) ⥤ CRIS(X/S)`, carries
injective abelian sheaves to injective abelian sheaves. -/
instance preservesInjectiveObjects_smallRestriction (S : GlobalCrystallineSituation.{u}) :
    (smallRestriction S).PreservesInjectiveObjects :=
  haveI := CrystallineThickening.preservesFiniteLimits_lowerShriekAb S
  haveI : (Functor.sheafPullbackConstruction.sheafPullback (CrystallineThickening.ι S)
      AddCommGrpCat.{u + 1} (smallTopology S) (topology S)).PreservesMonomorphisms :=
    preservesMonomorphisms_of_preservesLimitsOfShape _
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (CrystallineThickening.ι S)
      AddCommGrpCat.{u + 1} (smallTopology S) (topology S))

/-! ### Restriction along change of divided power base -/

section ChangeBase

variable (S S' : GlobalCrystallineSituation.{u}) (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
  (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber)
  [IsOpenImmersion g]

/-- Restriction of abelian sheaves along the change of base functor `Cris(X/S) ⥤ Cris(X'/S')` of
[Stacks, Tag 07KL], at the coefficients `AddCommGrpCat.{u + 1}`. The functor is continuous,
`Crystalline.GlobalCrystallineSituation.smallChangeBase_isContinuous`, so on sections this is
`G ↦ G ∘ smallChangeBase`. -/
def smallChangeBaseAbelianRestriction :
    Sheaf (smallTopology S') AddCommGrpCat.{u + 1} ⥤
      Sheaf (smallTopology S) AddCommGrpCat.{u + 1} :=
  (smallChangeBase S S' f g h).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (smallTopology S) (smallTopology S')

/-- The lower shriek along the change of base functor `Cris(X/S) ⥤ Cris(X'/S')` is exact on abelian
sheaves. -/
theorem preservesFiniteLimits_smallChangeBaseAbelianLowerShriek :
    PreservesFiniteLimits (Functor.sheafPullbackConstruction.sheafPullback
      (smallChangeBase S S' f g h) AddCommGrpCat.{u + 1}
      (smallTopology S) (smallTopology S')) :=
  have := CrystallineThickening.hasPullbacks_crystallineThickening S
  have := CrystallineThickening.hasEqualizers_crystallineThickening S
  Stacks.Sites.LowerShriek.gShriek_preservesFiniteLimits.{u + 1}
    (smallChangeBase S S' f g h) _ _

/-- Restriction along change of divided power base carries injective abelian sheaves to injective
abelian sheaves. -/
theorem preservesInjectiveObjects_smallChangeBaseAbelianRestriction :
    (smallChangeBaseAbelianRestriction S S' f g h).PreservesInjectiveObjects :=
  have := preservesFiniteLimits_smallChangeBaseAbelianLowerShriek S S' f g h
  have : (Functor.sheafPullbackConstruction.sheafPullback (smallChangeBase S S' f g h)
      AddCommGrpCat.{u + 1} (smallTopology S)
      (smallTopology S')).PreservesMonomorphisms :=
    preservesMonomorphisms_of_preservesLimitsOfShape _
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (smallChangeBase S S' f g h)
      AddCommGrpCat.{u + 1} (smallTopology S) (smallTopology S'))

end ChangeBase

/-! ### The situation `U/T` of [Stacks, Tag 07MJ] -/

section Pullback

open DividedPowerScheme

variable (S S' : GlobalCrystallineSituation.{u}) (fS : S.S ⟶ S'.S) (fX : S.X ⟶ S'.X)
  (hf : S.toClosedFiber ≫ closedFiberMap fS = fX ≫ S'.toClosedFiber)
  (A' : CrystallineThickening S')

include hf

/-- The functor `Cris(U/T) ⥤ Cris(X/S)` of the situation `U/T` of [Stacks, Tag 07MJ]: change of
divided power base along `T = S ×_{S'} T' ⟶ S`, for the open immersion `U = X ×_{X'} U' ⟶ X`. -/
def pullbackSmallChangeBase :
    CrystallineThickening (pullbackSituation S S' fS fX hf A') ⥤ CrystallineThickening S :=
  @smallChangeBase (pullbackSituation S S' fS fX hf A') S (pullback.fst fS A'.obj.toBase)
    (pullback.fst fX A'.obj.toX) (pullbackSituation_comm S S' fS fX hf A')
    (isOpenImmersion_pullbackSituationToX S S' fX A')

/-- Restriction of abelian sheaves along `Cris(U/T) ⥤ Cris(X/S)`: the pullback `F ↦ F_U` of
[Stacks, Tag 07MJ], written without the big crystalline site. -/
def pullbackAbelianRestriction :
    Sheaf (smallTopology S) AddCommGrpCat.{u + 1} ⥤
      Sheaf (smallTopology (pullbackSituation S S' fS fX hf A')) AddCommGrpCat.{u + 1} :=
  @smallChangeBaseAbelianRestriction (pullbackSituation S S' fS fX hf A') S
    (pullback.fst fS A'.obj.toBase) (pullback.fst fX A'.obj.toX)
    (pullbackSituation_comm S S' fS fX hf A')
    (isOpenImmersion_pullbackSituationToX S S' fX A')

/-- Restriction of abelian sheaves along `Cris(U/T) ⥤ Cris(X/S)` carries injective abelian sheaves
to injective abelian sheaves. -/
theorem preservesInjectiveObjects_pullbackAbelianRestriction :
    (pullbackAbelianRestriction S S' fS fX hf A').PreservesInjectiveObjects :=
  @preservesInjectiveObjects_smallChangeBaseAbelianRestriction
    (pullbackSituation S S' fS fX hf A') S (pullback.fst fS A'.obj.toBase)
    (pullback.fst fX A'.obj.toX) (pullbackSituation_comm S S' fS fX hf A')
    (isOpenImmersion_pullbackSituationToX S S' fX A')

end Pullback

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
