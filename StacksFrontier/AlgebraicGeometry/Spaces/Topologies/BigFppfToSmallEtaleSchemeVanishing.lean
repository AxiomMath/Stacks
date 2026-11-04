module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FppfEtaleComparison.FinitePushforwardInputs
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfToSmallEtaleHigherVanishing

/-!
# The scheme case of `R^iε_{X,*}(a_X⁻¹F) = 0`

For a big fppf site `B` and an object `Z`, the vanishing `R^pε_{Z,*}(a_Z⁻¹F) = 0` for `p > 0`
(the second half of Stacks 0DDS (1)) is proved in `AlgebraicGeometry` as
`isZero_fppfBigEtaleAbelianPushforward_rightDerived_fppfSmallEtaleAbelianPullback`.
There `ε_{Z,*}` is written with the localized étale topology of Situation 0EZ3, and `a_Z⁻¹` as
`π_Z⁻¹` followed by fppf sheafification. The proposition
`AlgebraicGeometry.SchemeFppfEtaleHigherVanishing` consumed by the algebraic-space comparison
(Stacks 0DGF and its consequences) writes `ε_{Z,*}` with `AlgebraicGeometry.BigEtaleOver.topology`
and `a_Z⁻¹` as the abelian inverse image along `AlgebraicGeometry.fppfToSmallEtaleMorphism`.
This file identifies the two spellings and proves the proposition.

## Main results

* `AlgebraicGeometry.fppfSmallEtaleAbelianPullbackIso`: the two spellings of `a_Z⁻¹` agree.
* `AlgebraicGeometry.schemeFppfEtaleHigherVanishing`: `SchemeFppfEtaleHigherVanishing B`.

## References

* [Stacks Project, Tag 0DDS](https://stacks.math.columbia.edu/tag/0DDS)
* [Stacks Project, Tag 0DGF](https://stacks.math.columbia.edu/tag/0DGF)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (X : B.Schemes)

/-- The two spellings of `a_X⁻¹` on abelian sheaves agree. -/
def fppfSmallEtaleAbelianPullbackIso :
    fppfSmallEtaleAbelianPullback B X ≅
      CategoryTheory.Sites.abelianInverseImage (fppfToSmallEtaleMorphism B X) := by
  let a := fppfToSmallEtaleMorphism B X
  have _ := a.preservesFiniteLimits
  have _ : PreservesLimitsOfSize.{0, 0} a.pushforward := a.adj.rightAdjoint_preservesLimits
  let adjMine :
      CategoryTheory.Sites.abelianInverseImage a ⊣ ProEtale.mapAbelianSheaf a.pushforward :=
    ProEtale.mapAbelianSheafAdjunction a.adj
  let adjTheirs := (fppfEtaleProjectionAdjunction B X).comp (fppfBigEtaleAbelianAdjunction B X)
  have e : ProEtale.mapAbelianSheaf a.pushforward ≅
      fppfBigEtaleAbelianPushforward B X ⋙ fppfEtaleProjectionRestriction B X := by
    let i := SmallEtale.inclusion (associatedBigEtaleSite B) X.1 X.2
    let J₀ := SmallEtale.topology (associatedBigEtaleSite B) X.1 X.2
    let Je := BigEtaleOver.topology (associatedBigEtaleSite B) X.1 X.2
    let K := B.topology.over X
    haveI : (𝟭 (Over X)).IsContinuous Je K := changeOfTopology_isContinuous B X
    haveI : (i ⋙ 𝟭 (Over X)).IsContinuous J₀ K := Functor.isContinuous_comp _ _ _ Je _
    have h₁ : a.pushforward ≅ (i ⋙ 𝟭 (Over X)).sheafPushforwardContinuous (Type (u + 1)) J₀ K :=
      Functor.isoWhiskerRight (fppfToBigEtale_pushforwardIso B X) _ ≪≫
        (Functor.sheafPushforwardContinuousComp i (𝟭 (Over X)) (Type (u + 1)) J₀ Je K).symm
    have _ : PreservesFiniteLimits
        ((i ⋙ 𝟭 (Over X)).sheafPushforwardContinuous (Type (u + 1)) J₀ K) :=
      preservesFiniteLimits_of_natIso h₁
    exact ProEtale.mapAbelianSheafIso h₁ ≪≫
      ProEtale.mapAbelianSheafRestrictionIso (i ⋙ 𝟭 (Over X)) ≪≫ Iso.refl _
  exact adjTheirs.leftAdjointUniq (adjMine.ofNatIsoRight e)

/-- Restriction along the identity for two equal topologies has the same higher direct images. -/
private theorem isZero_rightDerived_id_of_eq {C : Type*} [Category C]
    {K J₁ J₂ : GrothendieckTopology C} (hJ : J₁ = J₂) [(𝟭 C).IsContinuous J₁ K]
    [(𝟭 C).IsContinuous J₂ K] [HasSheafify K AddCommGrpCat.{u + 1}]
    [HasSheafify J₁ AddCommGrpCat.{u + 1}] [HasSheafify J₂ AddCommGrpCat.{u + 1}]
    [HasInjectiveResolutions (Sheaf K AddCommGrpCat.{u + 1})]
    (M : Sheaf K AddCommGrpCat.{u + 1}) (p : ℕ)
    (h : IsZero ((((𝟭 C).sheafPushforwardContinuous AddCommGrpCat.{u + 1} J₁ K).rightDerived
      p).obj M)) :
    IsZero ((((𝟭 C).sheafPushforwardContinuous AddCommGrpCat.{u + 1} J₂ K).rightDerived
      p).obj M) := by
  subst hJ
  exact h

/-- **The scheme case of `R^iε_{X,*}(a_X⁻¹F) = 0`**, Stacks 0DDS (1): for every object `Z` of the
big fppf site `B`, every abelian sheaf `F` on `Z_étale` and every `p > 0`, the higher direct
image `R^pε_{Z,*}(a_Z⁻¹F)` vanishes. -/
theorem schemeFppfEtaleHigherVanishing : SchemeFppfEtaleHigherVanishing B := by
  intro X F p hp
  have h₁ := (isZero_fppfBigEtaleAbelianPushforward_rightDerived_fppfSmallEtaleAbelianPullback
    B X F p hp).of_iso
    (((fppfBigEtaleAbelianPushforward B X).rightDerived p).mapIso
      ((fppfSmallEtaleAbelianPullbackIso B X).app F)).symm
  have : (𝟭 (Over X)).IsContinuous ((associatedBigEtaleSite B).topology.over X)
      (B.topology.over X) := by
    rw [← bigEtaleOver_topology_eq]
    exact changeOfTopology_isContinuous B X
  have h₂ : IsZero ((((𝟭 (Over X)).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      ((associatedBigEtaleSite B).topology.over X) (B.topology.over X)).rightDerived p).obj
        ((CategoryTheory.Sites.abelianInverseImage (fppfToSmallEtaleMorphism B X)).obj F)) :=
    h₁.of_iso ((Functor.rightDerivedIsoOfNatIso (Iso.refl _) p).app _)
  exact isZero_rightDerived_id_of_eq
    (bigEtaleOver_topology_eq (associatedBigEtaleSite B) X.1 X.2).symm _ p h₂

end AlgebraicGeometry
