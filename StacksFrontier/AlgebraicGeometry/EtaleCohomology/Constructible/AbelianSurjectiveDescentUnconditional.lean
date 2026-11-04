module
public import StacksFrontier.Topology.Sheaves.Modules.TensorExactness
public import StacksCore.Algebra.Homology.SpectralSequence.Tower
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyConstantWeakSerre
public import StacksFrontier.AlgebraicGeometry.Etale.DerivedUpperShriekAdjunctionUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ColimitOfConstructibles
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ModuleShriekPresentation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.ModuleCoefficients
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Restriction.CoefficientEquivalence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SurjectiveMorphismStalkDescent
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.LocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsion.DerivedCategoryOfTorsionSheaves
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.AbelianWeakSerre
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.AbelianSurjectiveDescent
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.AbelianSurjectiveDescent

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.IntegerShriekPresentation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ModuleSurjectiveDescent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.TorsionOfConstructible
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.TorsionOfConstructibleUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.WeakSerreAbelian
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Restriction.CompactConstructibleAbelian
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.TorsionLocalAnnihilation
import StacksCore.Tactic.StacksAttribute

/-!
# AbelianSurjectiveDescentUnconditional

Descent of constructibility of abelian sheaves on the small étale site along a surjective
morphism of quasi-compact and quasi-separated schemes, for arbitrary abelian sheaves.

## Main results

* `AlgebraicGeometry.isConstructibleAbelianSheaf_of_isConstructibleModuleSheaf_int_general`: a
  torsion abelian sheaf whose attached sheaf of `ℤ`-modules is constructible is constructible.
* `AlgebraicGeometry.isConstructibleAbelianSheaf_pullback_iff_of_surjective_general`: for a
  surjective morphism `f : X ⟶ Y` of quasi-compact and quasi-separated schemes, an abelian sheaf
  `ℱ` on `Y_étale` is constructible if and only if `f⁻¹ℱ` is.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Torsion Stacks.ConstantSheaf

universe u r

namespace AlgebraicGeometry

attribute [local instance 2000] Sheaf.instHasColimitsOfShape Sheaf.instHasFiniteCoproducts
attribute [local instance] Cardinal.fact_isRegular_aleph0

variable (B : BigEtaleSite.{u})

section Torsion

variable (X : B.Scheme)

section Coefficients

variable
  [∀ (S T : B.Scheme) (g : T ⟶ S),
    ((smallEtaleBaseChange B g).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) AddCommGrpCat.{u + 1}]

end Coefficients

end Torsion

variable {X Y : B.Scheme} (f : X ⟶ Y)

section ModuleBridge

section Abelian

variable
  [∀ (S T : B.Scheme) (g : T ⟶ S),
    ((smallEtaleBaseChange B g).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]

end Abelian

section IntModules

variable
  [∀ (S T : B.Scheme) (g : T ⟶ S),
    ((smallEtaleBaseChange B g).sheafPushforwardContinuous (ModuleCat.{u + 1} ℤ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{u + 1} ℤ)]

end IntModules

end ModuleBridge

section Descent

/-- Abelian sheafification on the localization of the small étale site at one of its objects, at
the coefficient universe of this file: the slice is essentially small in it. -/
local instance hasWeakSheafify_over_addCommGrp (T : B.Scheme)
    (V : SmallEtale B T.obj T.property) :
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) AddCommGrpCat.{u + 1} := by
  have : EssentiallySmall.{u + 1} (Over V) := inferInstance
  exact HasSheafify.isRightAdjoint.{_, _, _, _}
    (self := hasSheafifyEssentiallySmallSite.{_, _, _, _, u + 1} _ _)

/-- Sheafification of `ℤ`-modules on the localization of the small étale site at one of its
objects, at the coefficient universe of this file. -/
local instance hasWeakSheafify_over_intModule (T : B.Scheme)
    (V : SmallEtale B T.obj T.property) :
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{u + 1} ℤ) :=
  haveI := SmallEtale.hasSheafify_moduleSheaf_over.{u, 0, 0} B T ℤ V
  inferInstance

/-- Let `ℱ` be an abelian sheaf on `Z_étale` satisfying the local torsion condition
`torsionSheafProperty`. If the sheaf of `ℤ`-modules attached to `ℱ` by the equivalence
`AddCommGrpCat ≌ ModuleCat ℤ` is constructible, then `ℱ` is constructible as an abelian sheaf. -/
public theorem isConstructibleAbelianSheaf_of_isConstructibleModuleSheaf_int_general (Z : B.Scheme)
    (𝓕 : Sheaf (SmallEtale.topology B Z.obj Z.property) AddCommGrpCat.{u + 1})
    (hF : IsConstructibleModuleSheaf B Z ℤ
      ((Sheaf.coefficientEquivalence (SmallEtale.topology B Z.obj Z.property)
        AddCommGrpCat.moduleCatIntEquivalence.{u + 1}).functor.obj 𝓕))
    (hTor : torsionSheafProperty (SmallEtale.topology B Z.obj Z.property) 𝓕) :
    IsConstructibleAbelianSheaf B Z 𝓕 := by
  intro U
  obtain ⟨s, hs⟩ := hF U
  refine ⟨s, fun i => ?_⟩
  have hfin : IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, 0}
      (SmallEtale.topology B (s.piece i).obj (s.piece i).property) ℤ
      ((intSheaf.{u, u + 1, 0}
        (SmallEtale.topology B (s.piece i).obj (s.piece i).property)).obj
        ((smallEtaleAbelianPullbackFunctor B (s.inclusion i)).obj 𝓕)) := by
    intro V
    obtain ⟨I, Vs, g, hg, h⟩ := hs i V
    refine ⟨I, Vs, g, hg, fun j => ?_⟩
    obtain ⟨E, hE, ⟨α⟩⟩ := h j
    refine ⟨E, hE, ⟨α ≪≫ ?_⟩⟩
    exact ((SmallEtale.topology B (s.piece i).obj (s.piece i).property).overPullback
      (ModuleCat.{u + 1} ℤ) (Vs j)).mapIso
        ((Sheaf.sheafPullbackCoefficientIso (smallEtaleBaseChange B (s.inclusion i))
          (SmallEtale.topology B Z.obj Z.property)
          (SmallEtale.topology B (s.piece i).obj (s.piece i).property)
          AddCommGrpCat.moduleCatIntEquivalence.{u + 1}).app 𝓕).symm
  exact isFiniteLocallyConstant_of_isFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, 0} _ _ hfin
    (isLocallyAnnihilated_of_torsionSheafProperty.{u, u + 1, 0} _ _
      (torsionSheafProperty_smallEtaleAbelianPullback B (s.inclusion i) 𝓕 hTor) hfin)

variable (hXc : CompactSpace X.obj) (hXq : QuasiSeparatedSpace X.obj)
  (hYc : CompactSpace Y.obj) (hYq : QuasiSeparatedSpace Y.obj)
  (h093C : LocallyTorsionAbelianSheavesAreFilteredColimitsOfZModPresentations B Y)
  (h03S8 : AbelianShriekZModIsConstructible B)
  (h095N : ∀ G : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} ℤ),
    IsConstructibleModuleSheaf B X ℤ G →
      HasFiniteShriekPresentation.{u, 0, u + 1} B X ℤ (IsQCQSEtaleObject B X) G)

include hXc hXq hYc hYq

section ColimitRoute

include h093C h03S8 h095N

end ColimitRoute

/-- Let `f : X ⟶ Y` be a surjective morphism of quasi-compact and quasi-separated schemes and let
`ℱ` be an abelian sheaf on `Y_étale`, with no torsion assumption. Then `ℱ` is constructible if and
only if `f⁻¹ℱ` is constructible. -/
@[stacks 095Q "part (2), abelian sheaves"]
public theorem isConstructibleAbelianSheaf_pullback_iff_of_surjective_general
    (hf : Function.Surjective (B.inclusion.map f).base)
    (𝓕 : Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{u + 1}) :
    IsConstructibleAbelianSheaf B Y 𝓕 ↔
      IsConstructibleAbelianSheaf B X ((smallEtaleAbelianPullbackFunctor B f).obj 𝓕) := by
  refine ⟨isConstructibleFiniteSheaf_pullback B f 𝓕, fun hF => ?_⟩
  have hint : IsConstructibleModuleSheaf B X ℤ
      (((smallEtaleBaseChange B f).sheafPullback (ModuleCat.{u + 1} ℤ)
        (SmallEtale.topology B Y.obj Y.property)
        (SmallEtale.topology B X.obj X.property)).obj
        ((Sheaf.coefficientEquivalence (SmallEtale.topology B Y.obj Y.property)
          AddCommGrpCat.moduleCatIntEquivalence.{u + 1}).functor.obj 𝓕)) :=
    isConstructibleModuleSheaf_of_iso B X ℤ
      ((Sheaf.sheafPullbackCoefficientIso (smallEtaleBaseChange B f)
        (SmallEtale.topology B Y.obj Y.property) (SmallEtale.topology B X.obj X.property)
        AddCommGrpCat.moduleCatIntEquivalence.{u + 1}).app 𝓕)
      (isConstructibleModuleSheaf_moduleCatIntEquivalence B X _ hF)
  have hulift : IsConstructibleModuleSheaf B X (ULift.{u + 1} ℤ)
      ((smallEtaleModulePullbackFunctor B (ULift.{u + 1} ℤ) f).obj
        ((Sheaf.coefficientEquivalence (SmallEtale.topology B Y.obj Y.property)
          ModuleCat.restrictScalarsUliftIntEquivalence.{u + 1, u + 1}).functor.obj
          ((Sheaf.coefficientEquivalence (SmallEtale.topology B Y.obj Y.property)
            AddCommGrpCat.moduleCatIntEquivalence.{u + 1}).functor.obj 𝓕))) :=
    isConstructibleModuleSheaf_of_iso B X (ULift.{u + 1} ℤ)
      ((Sheaf.sheafPullbackCoefficientIso (smallEtaleBaseChange B f)
        (SmallEtale.topology B Y.obj Y.property) (SmallEtale.topology B X.obj X.property)
        ModuleCat.restrictScalarsUliftIntEquivalence.{u + 1, u + 1}).app _)
      (isConstructibleModuleSheaf_uliftIntRestrictScalars B X _ hint)
  exact isConstructibleAbelianSheaf_of_isConstructibleModuleSheaf_int_general B Y 𝓕
    (isConstructibleModuleSheaf_int_of_uliftIntRestrictScalars B Y _
      (isConstructibleModuleSheaf_of_isConstructibleModuleSheaf_pullback B (ULift.{u + 1} ℤ) f
        hYc hYq hXc hXq hf _ hulift))
    (torsionSheafProperty_of_isConstructibleAbelianSheaf_pullback B f hf 𝓕 hF)

end Descent

end AlgebraicGeometry

end
