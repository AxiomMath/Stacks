module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FppfEtaleComparison.Comparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.QcCohomologicalDescent
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Cohomological descent from the fppf to the small étale site

Let `B` be a big fppf site, `X` an object of it, and `a_X : Sh((Sch/X)_fppf) ⟶ Sh(X_étale)` the
composite `π_X ∘ ε_X` of the change of topology `ε_X : (Sch/X)_fppf ⟶ (Sch/X)_étale` and the
projection `π_X : (Sch/X)_étale ⟶ X_étale`. Stacks 0DDT asserts that for `K` in `D⁺(X_étale)`
the canonical map

`K ⟶ Ra_{X,*} a_X^{-1} K`

is an isomorphism. This file builds `a_{X,*}`, the adjunction `a_X^{-1} ⊣ a_{X,*}` and the map,
and proves the statement from the two inputs of Situation 0EZ3 for the fppf and étale topologies
(`AlgebraicGeometry.fppfEtaleCohomologyComparisonOfFinite`).

## Main definitions

* `AlgebraicGeometry.fppfSmallEtaleAbelianPushforward`: `a_{X,*} = π_{X,*} ∘ ε_{X,*}` on abelian
  sheaves.
* `AlgebraicGeometry.fppfSmallEtaleAbelianAdjunction`: `a_X^{-1} ⊣ a_{X,*}`, the composite of
  `π_X^{-1} ⊣ π_{X,*}` and `ε_X^{-1} ⊣ ε_{X,*}`.
* `AlgebraicGeometry.fppfSmallEtaleAdjunctionDerivedUnit`: the map `K ⟶ Ra_{X,*}a_X^{-1}K` on
  `D⁺(X_étale)`, the derived unit of `a_X^{-1} ⊣ a_{X,*}`.

## Main results

* `AlgebraicGeometry.isIso_fppfSmallEtaleAbelianAdjunction_unit_app`: `a_{X,*}a_X^{-1}F = F`
  (Stacks 0DDL), with no hypothesis.
* `AlgebraicGeometry.rightAcyclic_fppfSmallEtaleAbelianPushforward_of_finite`: the vanishing
  `R^q a_{X,*}(a_X^{-1}F) = 0` for `q > 0` of the source's proof.
* `AlgebraicGeometry.isIso_fppfSmallEtaleAdjunctionDerivedUnit_of_finite`: the statement of
  Stacks 0DDT.

## The proof

As in the source. The reduction to a single sheaf is Leray's acyclicity lemma (Stacks 015E),
`CategoryTheory.Functor.isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic`. For a sheaf `F`,
`a_{X,*}a_X^{-1}F = F` because `π_X^{-1}` is fully faithful (Stacks 0DDI) and `π_X^{-1}F` is
already an fppf sheaf (Stacks 0DDL). The vanishing `R^q a_{X,*}(a_X^{-1}F) = 0` for `q > 0`,
which the source gets from the Leray spectral sequence (Stacks 0734), is here the composition
isomorphism of Stacks 015M for `a_{X,*} = π_{X,*} ∘ ε_{X,*}`
(`CategoryTheory.Functor.rightAcyclic_comp_of_preservesHomology`): `ε_{X,*}` preserves injective
objects, `π_{X,*}` is exact (Stacks 0DDI, so `R^jπ_{X,*} = 0` for `j > 0`), and
`R^iε_{X,*}(a_X^{-1}F) = 0` for `i > 0` is Stacks 0DDS (1),
`AlgebraicGeometry.isZero_fppfBigEtaleAbelianPushforward_rightDerived_of_finite`.

## Hypotheses

Stacks 0DDS (1) is proved in this development from Situation 0EZ3 for the fppf and étale
topologies, and that situation is built from the two facts `hex` and `hbc` about the direct
image along a finite morphism of the big étale sites (exactness, and `f_{big,*}π_X^{-1}F ∈ 𝒜'_Y`)
that the proof of Stacks 0DDJ (4) supplies. The results using it take them as arguments, exactly
as `AlgebraicGeometry.isIso_fppfSmallEtaleDerivedUnit_of_finite` does, so the statement of
Stacks 0DDT is not registered here.

The derived categories are arbitrary models: the statements carry `HasDerivedCategory`
instances for the two sheaf categories.

## References

* [Stacks Project, Tag 0DDT](https://stacks.math.columbia.edu/tag/0DDT)
* [Stacks Project, Tag 0DDS](https://stacks.math.columbia.edu/tag/0DDS)
* [Stacks Project, Tag 0DDL](https://stacks.math.columbia.edu/tag/0DDL)
* [Stacks Project, Tag 0DDI](https://stacks.math.columbia.edu/tag/0DDI)
* [Stacks Project, Tag 015E](https://stacks.math.columbia.edu/tag/015E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (X : B.Schemes)

/-- The direct image `a_{X,*} = π_{X,*} ∘ ε_{X,*}` of abelian sheaves along the morphism of topoi
`a_X : Sh((Sch/X)_fppf) ⟶ Sh(X_étale)`: an fppf sheaf regarded as an étale sheaf on the big
étale site of `X`, then restricted to the small étale site. -/
@[sga "4 VII 4.0" "special case"]
abbrev fppfSmallEtaleAbelianPushforward :
    Sheaf (B.topology.over X) AddCommGrpCat.{u + 1} ⥤
      Sheaf (SmallEtale.topology (associatedBigEtaleSite B) X.1 X.2) AddCommGrpCat.{u + 1} :=
  fppfBigEtaleAbelianPushforward B X ⋙ fppfEtaleProjectionRestriction B X

/-- The adjunction `a_X^{-1} ⊣ a_{X,*}` on abelian sheaves, the composite of the projection
adjunction `π_X^{-1} ⊣ π_{X,*}` and the change-of-topology adjunction `ε_X^{-1} ⊣ ε_{X,*}`. -/
def fppfSmallEtaleAbelianAdjunction :
    fppfSmallEtaleAbelianPullback B X ⊣ fppfSmallEtaleAbelianPushforward B X :=
  (fppfEtaleProjectionAdjunction B X).comp (fppfBigEtaleAbelianAdjunction B X)

/-- **`a_{X,*}a_X^{-1}F = F`** for an abelian sheaf `F` on `X_étale`: the unit of
`a_X^{-1} ⊣ a_{X,*}` is invertible at `F`. It is the unit of `π_X^{-1} ⊣ π_{X,*}`, invertible
because `π_X^{-1}` is fully faithful (Stacks 0DDI), followed by `π_{X,*}` of the unit of
`ε_X^{-1} ⊣ ε_{X,*}` at `π_X^{-1}F`, invertible because `π_X^{-1}F` is an fppf sheaf
(Stacks 0DDL). -/
theorem isIso_fppfSmallEtaleAbelianAdjunction_unit_app
    (F : Sheaf (SmallEtale.topology (associatedBigEtaleSite B) X.1 X.2) AddCommGrpCat.{u + 1}) :
    IsIso ((fppfSmallEtaleAbelianAdjunction B X).unit.app F) := by
  have := isIso_fppfBigEtaleAbelianAdjunction_unit_app_projectionPullback B X F
  rw [fppfSmallEtaleAbelianAdjunction, Adjunction.comp_unit_app]
  infer_instance

/-- The unit of `a_X^{-1} ⊣ a_{X,*}` is a natural isomorphism. -/
instance isIso_fppfSmallEtaleAbelianAdjunction_unit :
    IsIso (fppfSmallEtaleAbelianAdjunction B X).unit :=
  have := isIso_fppfSmallEtaleAbelianAdjunction_unit_app B X
  NatIso.isIso_of_isIso_app _

section Descent

variable [HasDerivedCategory
    (Sheaf (SmallEtale.topology (associatedBigEtaleSite B) X.1 X.2) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory (Sheaf (B.topology.over X) AddCommGrpCat.{u + 1})]

/-- **The map `K ⟶ Ra_{X,*}a_X^{-1}K`** of Stacks 0DDT, for `K` in `D⁺(X_étale)`: the derived unit
of `a_X^{-1} ⊣ a_{X,*}`, with `a_X^{-1}` acting degreewise because it is exact. -/
def fppfSmallEtaleAdjunctionDerivedUnit :
    𝟭 (DerivedCategory.Plus
        (Sheaf (SmallEtale.topology (associatedBigEtaleSite B) X.1 X.2) AddCommGrpCat.{u + 1})) ⟶
      (fppfSmallEtaleAbelianPullback B X).mapDerivedCategoryPlus ⋙
        (fppfSmallEtaleAbelianPushforward B X).rightDerivedFunctorPlus :=
  Stacks.LerayPullbackComparison.derivedUnit (fppfSmallEtaleAbelianAdjunction B X)

variable {B X}
  (hex : ∀ ⦃X Y : B.Schemes⦄ (f : X ⟶ Y), fppfEtaleFinite B f →
    PreservesFiniteColimits ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
      ((associatedBigEtaleSite B).topology.over X) ((associatedBigEtaleSite B).topology.over Y)))
  (hbc : ∀ ⦃X Y : B.Schemes⦄ (f : X ⟶ Y), fppfEtaleFinite B f → ∀ A, fppfEtaleWeakSerre B Y
    (((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
      ((associatedBigEtaleSite B).topology.over X)
      ((associatedBigEtaleSite B).topology.over Y)).obj ((fppfEtaleProjectionPullback B X).obj A)))

include hex hbc in
/-- **`R^q a_{X,*}(a_X^{-1}F) = 0` for `q > 0`**: `a_X^{-1}F` is right acyclic for `a_{X,*}`,
given the two inputs of Situation 0EZ3 for the fppf and étale topologies. `ε_{X,*}` preserves
injective objects and `π_{X,*}` is exact, so acyclicity for `a_{X,*} = π_{X,*} ∘ ε_{X,*}` is
acyclicity for `ε_{X,*}`, which is the vanishing `R^iε_{X,*}(a_X^{-1}F) = 0` of Stacks 0DDS (1).
This stands in for the Leray spectral sequence of the source's proof. -/
theorem rightAcyclic_fppfSmallEtaleAbelianPushforward_of_finite
    (F : Sheaf (SmallEtale.topology (associatedBigEtaleSite B) X.1 X.2) AddCommGrpCat.{u + 1}) :
    (fppfSmallEtaleAbelianPushforward B X).rightAcyclic
      ((fppfSmallEtaleAbelianPullback B X).obj F) := by
  -- A model for the derived category of the intermediate big étale sheaves, through which the
  -- composite is factored; it does not appear in the statement.
  let := HasDerivedCategory.standard
    (Sheaf ((associatedBigEtaleSite B).topology.over X) AddCommGrpCat.{u + 1})
  have : (fppfBigEtaleAbelianPushforward B X).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (fppfBigEtaleAbelianAdjunction B X)
  have : (fppfEtaleProjectionRestriction B X).PreservesHomology :=
    Functor.preservesHomologyOfExact _
  exact Functor.rightAcyclic_comp_of_preservesHomology (fppfBigEtaleAbelianPushforward B X)
    (fppfEtaleProjectionRestriction B X) _
    ((rightAcyclic_iff_isZero_rightDerived (fppfBigEtaleAbelianPushforward B X) _).2
      fun i hi ↦ isZero_fppfBigEtaleAbelianPushforward_rightDerived_of_finite X hex hbc F i hi)

include hex hbc in
/-- **Stacks 0DDT.** For `K` in `D⁺(X_étale)` the map `K ⟶ Ra_{X,*}a_X^{-1}K` is an isomorphism,
given the two inputs of Situation 0EZ3 for the fppf and étale topologies. Every term of
`a_X^{-1}K` is right acyclic for `a_{X,*}`
(`rightAcyclic_fppfSmallEtaleAbelianPushforward_of_finite`), so Leray's acyclicity lemma
(Stacks 015E) computes `Ra_{X,*}a_X^{-1}K` degreewise, where the unit is invertible by
`isIso_fppfSmallEtaleAbelianAdjunction_unit_app`. -/
theorem isIso_fppfSmallEtaleAdjunctionDerivedUnit_of_finite :
    IsIso (fppfSmallEtaleAdjunctionDerivedUnit B X) := by
  have hQh : ∀ L : HomotopyCategory.Plus
      (Sheaf (SmallEtale.topology (associatedBigEtaleSite B) X.1 X.2) AddCommGrpCat.{u + 1}),
      IsIso ((fppfSmallEtaleAdjunctionDerivedUnit B X).app (DerivedCategory.Plus.Qh.obj L)) := by
    intro L
    rw [fppfSmallEtaleAdjunctionDerivedUnit, Stacks.LerayPullbackComparison.derivedUnit_app_Qh]
    have h₁ : IsIso (DerivedCategory.Plus.Qh.map
        ((fppfSmallEtaleAbelianAdjunction B X).mapHomotopyCategoryPlus.unit.app L)) := by
      have : IsIso ((fppfSmallEtaleAbelianAdjunction B X).mapHomotopyCategoryPlus.unit.app L) :=
        Adjunction.isIso_mapHomotopyCategoryPlus_unit_app _ L
      infer_instance
    have h₂ : IsIso ((fppfSmallEtaleAbelianPushforward B X).rightDerivedFunctorPlusUnith.app
        ((fppfSmallEtaleAbelianPullback B X).mapHomotopyCategoryPlus.obj L)) :=
      Functor.isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic _ _ fun n ↦
        rightAcyclic_fppfSmallEtaleAbelianPushforward_of_finite hex hbc (L.obj.as.X n)
    have h₃ : IsIso ((fppfSmallEtaleAbelianPushforward B X).rightDerivedFunctorPlus.map
        ((fppfSmallEtaleAbelianPullback B X).mapDerivedCategoryPlusFactorsh.inv.app L)) :=
      inferInstance
    exact IsIso.comp_isIso' h₁ (IsIso.comp_isIso' h₂ h₃)
  have : ∀ K, IsIso ((fppfSmallEtaleAdjunctionDerivedUnit B X).app K) := fun K ↦
    (NatTrans.isIso_app_iff_of_iso _ (DerivedCategory.Plus.Qh.objObjPreimageIso K)).1 (hQh _)
  exact NatIso.isIso_of_isIso_app _

end Descent

end AlgebraicGeometry
