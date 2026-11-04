module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.CohomologyPullbackComparisonCanonical
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.CohomologyDerivedSingleIsoNaturality
public import
  StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ClosedEmbeddingPushforwardColimits

/-!
# Naturality of the pullback map on cohomology, and closed embeddings

The pullback map `pullbackHgroup P φ : Hⁿ(X, ℳ) ⟶ Hⁿ(X', ℳ')` of [Stacks, Tag 01F9] attached to a
`G`-map `φ : ℳ ⟶ G_*ℳ'` is natural in the pair `(ℳ, ℳ')`: for `α : ℳ₁ ⟶ ℳ₂` and
`β : ℳ'₁ ⟶ ℳ'₂` with `φ₁ ≫ G_*β = α ≫ φ₂` the square of cohomology groups commutes. In particular
`pullbackHgroup P φ` is the map `Hⁿ(X, φ) : Hⁿ(X, ℳ) ⟶ Hⁿ(X, G_*ℳ')` followed by the pullback
map of the identity of `G_*ℳ'`.

For the canonical comparisons and `G` a homeomorphism onto a closed subset, the pullback map of
the identity of `G_*ℳ'` is an isomorphism `Hⁿ(X, G_*ℳ') ≅ Hⁿ(X', ℳ')`: the derived direct image
along `G` is computed termwise ([Stacks, Tag 0B55]).

## Main results

* `Stacks.DeRham.GysinCohomologyBaseChange.pullbackHgroup_naturality`.
* `Stacks.DeRham.GysinCohomologyBaseChange.pullbackHgroup_eq_map_comp`.
* `Stacks.DeRham.GysinCohomologyBaseChange.isIso_pullbackHgroup_canonical_id`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DeRham.CohomologicalGysin

namespace Stacks.DeRham.GysinCohomologyBaseChange

universe u

open DerivedCategory

attribute [local instance] Stacks.Topology.RingedSpaceSheafifyOpens.opensHasSheafifyAddCommGrpCat
  Stacks.Topology.RingedSpaceSheafifyOpens.opensWEqualsLocallyBijectiveAddCommGrpCat

-- Sheaves of modules on a ringed space have a derived category; the instance is the one
-- `pullbackHgroup` is built in, re-attached as in `CohomologicalBaseChange`.
attribute [local instance] Stacks.DeRham.CohomologicalGysin.moduleSheavesHasDerivedCategory

variable {X X' : RingedSpace.{u, u}} {G : X' ⟶ X}

/-- **The pullback map on cohomology is natural in the pair of modules.** For `G`-maps
`φ₁ : ℳ₁ ⟶ G_*ℳ'₁`, `φ₂ : ℳ₂ ⟶ G_*ℳ'₂` and morphisms `α : ℳ₁ ⟶ ℳ₂`, `β : ℳ'₁ ⟶ ℳ'₂` with
`φ₁ ≫ G_*β = α ≫ φ₂`, the square
`Hⁿ(X, α) ≫ pullbackHgroup φ₂ = pullbackHgroup φ₁ ≫ Hⁿ(X', β)` commutes. -/
theorem pullbackHgroup_naturality (P : CohomologyPullbackComparison G) (a m : ℤ) (n : ℕ)
    (hn : m - a = n) {M₁ M₂ : RModules X} {M'₁ M'₂ : RModules X'} (α : M₁ ⟶ M₂)
    (β : M'₁ ⟶ M'₂) (φ₁ : M₁ ⟶ (modulePushforward G).obj M'₁)
    (φ₂ : M₂ ⟶ (modulePushforward G).obj M'₂)
    (h : φ₁ ≫ (modulePushforward G).map β = α ≫ φ₂) :
    (Hfunctor (structureSheafRing X) ⊤ n).map α ≫ pullbackHgroup P a m n hn φ₂ =
      pullbackHgroup P a m n hn φ₁ ≫ (Hfunctor (structureSheafRing X') ⊤ n).map β := by
  have hα := cohomologyDerivedSingleIso_hom_naturality X α a m n hn
  have hβ := cohomologyDerivedSingleIso_hom_naturality X' β a m n hn
  have hsm := (P.singleMap a).naturality β
  simp only [Functor.comp_map] at hsm
  have hle := P.leray.hom.naturality ((singleFunctor _ a).map β)
  simp only [Functor.comp_map] at hle
  have hd : (singleFunctor _ a).map α ≫ derivedPushforwardMap P a φ₂ =
      derivedPushforwardMap P a φ₁ ≫ (derivedPushforward G).map ((singleFunctor _ a).map β) := by
    simp only [derivedPushforwardMap]
    rw [← Functor.map_comp_assoc, ← h, Functor.map_comp, Category.assoc, hsm,
      Category.assoc]
  have key : (derivedGlobalSections X).map ((singleFunctor _ a).map α) ≫
        ((derivedGlobalSections X).map (derivedPushforwardMap P a φ₂) ≫
          P.leray.hom.app ((singleFunctor _ a).obj M'₂)) =
      ((derivedGlobalSections X).map (derivedPushforwardMap P a φ₁) ≫
          P.leray.hom.app ((singleFunctor _ a).obj M'₁)) ≫
        (derivedGlobalSections X').map ((singleFunctor _ a).map β) := by
    rw [← Category.assoc, ← Functor.map_comp, hd, Functor.map_comp, Category.assoc, hle,
      Category.assoc]
  rw [← Iso.inv_comp_eq] at hα
  rw [← hα]
  simp only [pullbackHgroup, Category.assoc, Iso.hom_inv_id_assoc]
  let : HasDerivedCategory AddCommGrpCat.{u} := HasDerivedCategory.standard _
  rw [← hβ, ← (DerivedCategory.homologyFunctor AddCommGrpCat.{u} m).map_comp_assoc,
    ← (DerivedCategory.homologyFunctor AddCommGrpCat.{u} m).map_comp_assoc, key]

/-- **The pullback map of a `G`-map `φ : ℳ ⟶ G_*ℳ'` factors through `Hⁿ(X, G_*ℳ')`**: it is
`Hⁿ(X, φ)` followed by the pullback map of the identity of `G_*ℳ'`. -/
theorem pullbackHgroup_eq_map_comp (P : CohomologyPullbackComparison G) (a m : ℤ) (n : ℕ)
    (hn : m - a = n) {M : RModules X} {M' : RModules X'}
    (φ : M ⟶ (modulePushforward G).obj M') :
    pullbackHgroup P a m n hn φ =
      (Hfunctor (structureSheafRing X) ⊤ n).map φ ≫
        pullbackHgroup P a m n hn (𝟙 ((modulePushforward G).obj M')) := by
  have := pullbackHgroup_naturality P a m n hn φ (𝟙 M') φ (𝟙 _)
    (by simp)
  rw [this, CategoryTheory.Functor.map_id, Category.comp_id]

/-- **For a homeomorphism onto a closed subset, the comparison of [Stacks, Tag 01F8] is an
isomorphism on single complexes**: the derived direct image is computed termwise. -/
instance isIso_singleToDerivedPushforward_app (G : X' ⟶ X)
    [hG : Fact (Topology.IsClosedEmbedding G.hom.base)] (a : ℤ) (M' : RModules X') :
    IsIso ((singleToDerivedPushforward G a).app M') := by
  have := Stacks.Cohomology.ClosedEmbeddingPushforward.isIso_derivedPushforwardUnit_app G hG.out
    ((HomotopyCategory.singleFunctor (RModules X') a).obj M')
  dsimp only [singleToDerivedPushforward, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app]
  infer_instance

/-- **For a homeomorphism onto a closed subset, the pullback map of the identity of `G_*ℳ'` is an
isomorphism** `Hⁿ(X, G_*ℳ') ≅ Hⁿ(X', ℳ')`, for the canonical comparisons. -/
instance isIso_pullbackHgroup_canonical_id (G : X' ⟶ X)
    [Fact (Topology.IsClosedEmbedding G.hom.base)] (a m : ℤ) (n : ℕ) (hn : m - a = n)
    (M' : RModules X') :
    IsIso (pullbackHgroup (CohomologyPullbackComparison.canonical G) a m n hn
      (𝟙 ((modulePushforward G).obj M'))) := by
  dsimp only [pullbackHgroup, derivedPushforwardMap]
  rw [CategoryTheory.Functor.map_id, Category.id_comp]
  have : IsIso ((CohomologyPullbackComparison.canonical G).singleMap a |>.app M') :=
    isIso_singleToDerivedPushforward_app G a M'
  infer_instance

end Stacks.DeRham.GysinCohomologyBaseChange

end
