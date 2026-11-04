module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackDerivedExistenceBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackDataCompIso
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBaseDerivedCoherence

/-!
# The comparison over a smaller base, and Stacks 0DLM without it

The structure `AlgebraicGeometry.Space.ComplexesSituation.SmallerBaseDerivedComparison` collects
the data and facts about the derived categories over a smaller base which the change of base of
Stacks 0DIQ uses. This file fills it: the equivalence and the pseudo-coherence from
`StacksFrontier/AlgebraicGeometry/Spaces/SmallerBaseDerived.lean`, the commutation with derived
pullback and its compatibility with composition from
`StacksFrontier/AlgebraicGeometry/Spaces/SmallerBaseDerivedCoherence.lean`, and the identification of
the composition comparison from
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleDerivedPullbackDataCompIso.lean`. The two forms of
Stacks 0DLM with Stacks 0DIQ then no longer take the structure as a hypothesis.

## Main definitions

* `AlgebraicGeometry.Space.smallerBaseToposDerivedEquivalence`: `D(𝒪_Y) ≌ D(𝒪_Z)` in the
  ringed-topos spelling of the derived categories.
* `AlgebraicGeometry.Space.ComplexesSituation.smallerBaseDerivedComparison`: the structure.

## Main results

In `AlgebraicGeometry.Space.ComplexesSituation`:

* `isEffective_formalObject_of_derivedExistence_and_negativeExtLocus` and
  `isStronglyFormallyEffective_complexes_of_derivedExistence_and_negativeExtLocus`:
  Stacks 0DLM from Stacks 0DIQ and Stacks 0DLC, clause (1).

Nothing here is registered: the remaining hypotheses carry Stacks results not yet proved here.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) {W S : Scheme.{u}} {hW : B.Contains W} {hS : B.Contains S}
  (h : B.obj hW ⟶ B.obj hS) {Z : AlgebraicSpaces B W hW} {Y : AlgebraicSpaces B S hS}
  (ε : (OverShriek.relocalizePresheafFunctor h).obj Z.1 ≅ Y.1)

/-- `AlgebraicGeometry.Space.smallerBaseDerivedEquivalence` in the ringed-topos spelling of the
derived categories: the equivalence induced on derived categories by
`AlgebraicGeometry.Space.smallerBaseToposModulesEquivalence`. -/
def smallerBaseToposDerivedEquivalence :
    ComplexesSituation.toposDerived Y ≌ ComplexesSituation.toposDerived Z :=
  letI : HasDerivedCategory.{u + 1} (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) :=
    HasDerivedCategory.standard _
  letI : HasDerivedCategory.{u + 1} (SheafOfModules.{u} (ringedToposStructureRingSheaf B W hW Z)) :=
    HasDerivedCategory.standard _
  letI := Stacks.DerivedCategory.mapDerivedCategory_isEquivalence
    (smallerBaseToposModulesEquivalence B h ε)
  (smallerBaseToposModulesEquivalence B h ε).functor.mapDerivedCategory.asEquivalence

namespace ComplexesSituation

variable (S hS) in
/-- **The comparison over a smaller base**: the data and facts of
`AlgebraicGeometry.Space.ComplexesSituation.SmallerBaseDerivedComparison`, the composition
comparison of the derived pullback datum being identified by
`AlgebraicGeometry.Space.smallEtaleDerivedPullbackData_compIso_eq`. -/
def smallerBaseDerivedComparison : SmallerBaseDerivedComparison B S hS where
  equivalence := fun {_ _} h {_ _} ε => smallerBaseToposDerivedEquivalence B h ε
  pullbackIso := fun {_ _} h {_ _ _ _} ε₁ ε₂ _ _ hfg hf hg =>
    smallerBaseToposDerivedPullbackIso B h ε₁ ε₂ hfg hf hg
  pullbackIso_comp := fun {_ _} h {_ _ _ _ _ _} ε₁ ε₂ ε₃ _ _ _ _ hfg hf hg hfg' hf' hg' hfg'' hf''
      hg'' K =>
    smallerBaseToposDerivedPullbackIso_comp B h ε₁ ε₂ ε₃ hfg hf hg hfg' hf' hg' hfg'' hf'' hg'' K
  isPseudoCoherent_iff := fun {W} {hW} h {Z} {Y} ε K =>
    letI : HasDerivedCategory.{u + 1} (Modules.{u, u} B S hS Y.1 Y.2) :=
      HasDerivedCategory.standard _
    letI : HasDerivedCategory.{u + 1} (Modules.{u, u} B W hW Z.1 Z.2) :=
      HasDerivedCategory.standard _
    isPseudoCoherent_smallerBaseDerivedEquivalence_iff B h ε K
  compIso_eq := fun {_ _ _} f g => smallEtaleDerivedPullbackData_compIso_eq B S hS f g

end ComplexesSituation

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space.ComplexesSituation

open CategoryTheory.Limits
open AlgebraicGeometry.GrothendieckExistence (limitBase)
open Deformation.Artin

attribute [local instance] AlgebraicGeometry.Space.instModulesHasDerivedCategory complexesCategory

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (D : ComplexesSituation B S hS)

/-- **Stacks 0DLM, condition (3) of Stacks 07Y4, with Stacks 0DIQ**:
`AlgebraicGeometry.Space.ComplexesSituation.isEffective_formalObject_of_derivedExistence` with the
comparison over a smaller base supplied by
`AlgebraicGeometry.Space.ComplexesSituation.smallerBaseDerivedComparison`. For `Y = S`, every
formal object of `Complexes_{X/S}` is effective.

* `h0DIQ`: Stacks 0DIQ, not yet proved here.
* `h0DLC`: Stacks 0DLC, clause (1), pending with 0DLC (needs Stacks 0DKY and 0DKX). -/
theorem isEffective_formalObject_of_derivedExistence_and_negativeExtLocus
    (h0DIQ : ∀ DS : DerivedExistenceSystem.{u},
      ∃ (K : DS.limitDerivedCategory) (ψ : ∀ n : ℕ, (DS.stageDerivedPullback n).obj K ≅ DS.K n),
        (letI : HasDerivedCategory.{u + 1} (DS.toposModules DS.X.left) :=
            HasDerivedCategory.standard _;
          RingedSite.IsPseudoCoherent.{u + 1, u, u, u, u + 1}
            (RingedTopos.toRingedSite
              (smallEtaleRingedTopos DS.B (limitBase DS.system) DS.containsLimitBase DS.X.left))
            K) ∧
        ∀ n : ℕ, (ψ n).hom = (DS.stageDerivedPullbackCompIso n).inv.app K ≫
          (transitionDerivedPullback DS.system DS.B DS.containsLimitBase DS.containsBaseAt DS.X
            n).map (ψ (n + 1)).hom ≫ DS.φ n)
    (h0DLC : ExistsNegativeExtLocus B S hS) (hY : IsTerminal D.Y)
    (ξ : FormalObject B S hS (complexesFunctor D)) :
    FormalObject.IsEffective B S hS (complexesFunctor D) (complexesFunctor_isFiberedInGroupoids D)
      ξ :=
  D.isEffective_formalObject_of_derivedExistence h0DIQ (smallerBaseDerivedComparison B S hS) h0DLC
    hY ξ

/-- **Stacks 0DLM: `Complexes_{X/S}` is strongly formally effective (Stacks 0CXT), with Stacks
0DIQ**:
`isStronglyFormallyEffective_complexes_of_derivedExistence`
with the comparison over a smaller base supplied by
`AlgebraicGeometry.Space.ComplexesSituation.smallerBaseDerivedComparison`.

* `h0DIQ`: Stacks 0DIQ, not yet proved here.
* `h0DLC`: Stacks 0DLC, clause (1), pending with 0DLC (needs Stacks 0DKY and 0DKX). -/
theorem isStronglyFormallyEffective_complexes_of_derivedExistence_and_negativeExtLocus
    (h0DIQ : ∀ DS : DerivedExistenceSystem.{u},
      ∃ (K : DS.limitDerivedCategory) (ψ : ∀ n : ℕ, (DS.stageDerivedPullback n).obj K ≅ DS.K n),
        (letI : HasDerivedCategory.{u + 1} (DS.toposModules DS.X.left) :=
            HasDerivedCategory.standard _;
          RingedSite.IsPseudoCoherent.{u + 1, u, u, u, u + 1}
            (RingedTopos.toRingedSite
              (smallEtaleRingedTopos DS.B (limitBase DS.system) DS.containsLimitBase DS.X.left))
            K) ∧
        ∀ n : ℕ, (ψ n).hom = (DS.stageDerivedPullbackCompIso n).inv.app K ≫
          (transitionDerivedPullback DS.system DS.B DS.containsLimitBase DS.containsBaseAt DS.X
            n).map (ψ (n + 1)).hom ≫ DS.φ n)
    (h0DLC : ExistsNegativeExtLocus B S hS) [IsLocallyNoetherian S] (hY : IsTerminal D.Y) :
    IsStronglyFormallyEffective B S hS (complexesFunctor D)
      (complexesFunctor_isFiberedInGroupoids D) :=
  D.isStronglyFormallyEffective_complexes_of_derivedExistence h0DIQ
    (smallerBaseDerivedComparison B S hS) h0DLC hY

end AlgebraicGeometry.Space.ComplexesSituation

end
