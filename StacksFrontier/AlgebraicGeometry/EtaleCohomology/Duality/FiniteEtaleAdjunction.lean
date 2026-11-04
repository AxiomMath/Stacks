module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.Trace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedSiteBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ModelBridges.ExtensionByZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleRestrictionInverseImage
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.ContainsFiniteEtale
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Direct image along a finite étale morphism is left adjoint to restriction

Let `π : V ⟶ X` be finite and étale. Then `π_* ⊣ π^{-1}` on sheaves of modules on the small
étale sites `AlgebraicGeometry.Scheme.smallEtaleTopology`: the direct image is also a *left*
adjoint of restriction, being isomorphic to extension by zero `π_!` ([Stacks, Tag 03S7]).

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleDirectImageRestrictionAdjOfSmallEtale`: `π_* ⊣ π^{-1}` on
  Mathlib's sites, for `π` the structure morphism of a finite étale object `U` of the bounded
  site.
* `Stacks.EtaleCohomology.smallEtaleObjOfFiniteEtale`: a finite étale morphism into `X` as an
  object of the bounded small étale site of `X`.
* `Stacks.EtaleCohomology.etaleModuleDirectImageRestrictionAdj`,
  `Stacks.EtaleCohomology.etaleModuleDirectImageInverseImageAdj`: `π_* ⊣ π^{-1}` for an arbitrary
  finite étale morphism `π` of schemes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v

namespace Stacks.EtaleCohomology

open AlgebraicGeometry.SmallEtale

attribute [local instance] moduleCat_hasLimitsOfSize

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X) (U : SmallEtale B X hX)
  [IsFinite (B.inclusion.map U.obj.hom)] (Λ : Type v) [Ring Λ]

/-- **For a finite étale morphism `π = (U ⟶ X)` of a big étale site, direct image of sheaves of
modules on Mathlib's small étale sites is left adjoint to restriction**, `π_* ⊣ π^{-1}`. -/
@[sga "4 IX 5.1" "(i)"]
def etaleModuleDirectImageRestrictionAdjOfSmallEtale :
    letI : Etale (B.inclusion.map U.obj.hom) := U.property
    etaleModuleDirectImage.{u, v} Λ (B.inclusion.map U.obj.hom) ⊣
      etaleModuleRestriction.{u, v} Λ (B.inclusion.map U.obj.hom) := by
  letI : Etale (B.inclusion.map U.obj.hom) := U.property
  letI : (Scheme.Etale.smallEtaleCompose (B.inclusion.map U.obj.hom)).IsContinuous
      U.obj.left.1.smallEtaleTopology X.smallEtaleTopology :=
    Scheme.Etale.smallEtaleCompose_isContinuous _
  let A := ModuleCat.{max (u + 1) v} Λ
  let eX := (sheafEquiv B X hX A).symm
  let eT := (sheafEquiv B U.obj.left.1 U.obj.left.property A).symm
  let adjB := (moduleExtensionByZeroAdjunction B X hX U Λ).ofNatIsoLeft
    (moduleExtensionByZeroIsoPushforward B X hX U Λ)
  let adj := eT.toAdjunction.comp (adjB.comp eX.symm.toAdjunction)
  let iso₁ := toEtaleSitePushforwardBaseChangeIso B (S := ⟨X, hX⟩) U.obj.hom A
  let iso₂ := (toEtaleSiteRestrictionIso B X hX U A).symm
  refine (adj.ofNatIsoLeft ?_).ofNatIsoRight ?_
  · exact (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight iso₁.symm eX.inverse ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ eX.unitIso.symm ≪≫
      Functor.rightUnitor _
  · exact Functor.isoWhiskerRight iso₂ eT.inverse ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ eT.unitIso.symm ≪≫ Functor.rightUnitor _

/-- A finite étale morphism into a scheme of a big étale site, as an object of the bounded small
étale site of its target. -/
def smallEtaleObjOfFiniteEtale {Y : Scheme.{u}} (π : Y ⟶ X) [IsFinite π] [Etale π] :
    SmallEtale B X hX :=
  ⟨Over.mk (Y := B.obj Y (B.contains_of_finiteEtale π ⟨inferInstance, inferInstance⟩ hX))
    (ObjectProperty.homMk π), (inferInstance : Etale π)⟩

end Stacks.EtaleCohomology

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize

variable (Λ : Type v) [Ring Λ] {X Y : Scheme.{u}} (π : Y ⟶ X) [IsFinite π] [Etale π]

/-- **Direct image along a finite étale morphism is left adjoint to restriction**, on sheaves of
modules on Mathlib's small étale sites: `π_* ⊣ π^{-1}` ([Stacks, Tag 03S7]). -/
def etaleModuleDirectImageRestrictionAdj :
    etaleModuleDirectImage.{u, v} Λ π ⊣ etaleModuleRestriction.{u, v} Λ π :=
  let B := BigEtaleSite.containing X
  let hX : B.Contains X := BigEtaleSite.contains_containing X
  haveI : IsFinite (B.inclusion.map (smallEtaleObjOfFiniteEtale B X hX π).obj.hom) :=
    inferInstanceAs (IsFinite π)
  etaleModuleDirectImageRestrictionAdjOfSmallEtale B X hX (smallEtaleObjOfFiniteEtale B X hX π) Λ

/-- **Direct image along a finite étale morphism is left adjoint to inverse image**, on sheaves
of modules on Mathlib's small étale sites: `π_* ⊣ π^{-1}`. -/
def etaleModuleDirectImageInverseImageAdj :
    etaleModuleDirectImage.{u, v} Λ π ⊣ etaleModuleInverseImage.{u, v} Λ π :=
  (etaleModuleDirectImageRestrictionAdj Λ π).ofNatIsoRight
    (etaleModuleInverseImageRestrictionIso.{u, v} Λ π).symm

end Stacks.EtaleCohomology

end
