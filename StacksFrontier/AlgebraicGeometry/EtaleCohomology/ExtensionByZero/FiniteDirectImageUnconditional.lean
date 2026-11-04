module
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EndActionLiftFunctorial
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeContinuous
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedSiteBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.Adjunction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.Localization
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.FiniteDirectImage
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.FiniteDirectImage

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EndActionLiftPushforward
public import StacksFrontier.AlgebraicGeometry.Etale.DerivedLowerShriekQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Etale.EtaleUpperShriekRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ModelBridges.ExtensionByZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ModelBridges.ExtensionByZeroUnconditional
public import StacksFrontier.AlgebraicGeometry.Topologies.BigEtale.SmallEtaleFunctoriality
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Existence

/-!
# Extension by zero along an étale composite of an open immersion and a finite morphism

Let `ι : W ⟶ W̄` be an open immersion and `π : W̄ ⟶ X` a finite morphism whose composite
`ε = ι ≫ π` is étale. Then extension by zero along `ε` factors as extension by zero along `ι`
followed by direct image along `π`, that is `ε_! ≅ π_* ∘ ι_!`. The isomorphism is given for
abelian sheaves and for sheaves of `Λ`-modules on the small étale sites of Tag 021B, and for
sheaves of `Λ`-modules on Mathlib's small étale sites.

## Main definitions

* `AlgebraicGeometry.SmallEtale.abelianExtensionByZeroCompIsoPushforward`: `ε_! ≅ π_* ∘ ι_!` for
  abelian sheaves on the small étale sites of Tag 021B.
* `AlgebraicGeometry.SmallEtale.moduleExtensionByZeroCompIsoPushforward`: `ε_! ≅ π_* ∘ ι_!` for
  sheaves of `Λ`-modules on the small étale sites of Tag 021B.
* `Stacks.EtaleCohomology.etaleModuleExtensionByZeroCompIsoDirectImage`: `ε_! ≅ π_* ∘ ι_!` for
  sheaves of `Λ`-modules on Mathlib's small étale sites.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) {W Wbar Y : B.Scheme} (ι : W ⟶ Wbar) (π : Wbar ⟶ Y)
  [IsOpenImmersion (B.inclusion.map ι)] [IsFinite (B.inclusion.map π)]
  [Etale (B.inclusion.map (ι ≫ π))]

/-- **`ε_! = π_* ∘ ι_!` for abelian sheaves on the small étale sites of Tag 021B.** For an open
immersion `ι` and a finite morphism `π` of a big étale site with `ε = ι ≫ π` étale, extension by
zero along `ε` is extension by zero along `ι` followed by direct image along `π`. -/
public def abelianExtensionByZeroCompIsoPushforward :
    abelianExtensionByZero B Y.obj Y.property (ofEtaleHom B (ι ≫ π)) ≅
      abelianExtensionByZero B Wbar.obj Wbar.property (ofEtaleHom B ι) ⋙
        etalePushforward.{u, u + 1} B π :=
  haveI : IsOpenImmersion (B.inclusion.map (ofEtaleHom B ι).obj.hom) :=
    inferInstanceAs (IsOpenImmersion (B.inclusion.map ι))
  abelianExtensionByZeroIsoFShriek B Y.obj Y.property (ofEtaleHom B (ι ≫ π)) ≪≫
    fShriekFunctorIsoCompactification B π (ofEtaleHom B ι)

variable (Λ : Type (u + 1)) [Ring Λ]

open Stacks.ModuleCatLift in
/-- **`ε_! = π_* ∘ ι_!` for sheaves of `Λ`-modules on the small étale sites of Tag 021B.** For an
open immersion `ι` and a finite morphism `π` of a big étale site with `ε = ι ≫ π` étale, extension
by zero along `ε` of sheaves of `Λ`-modules is extension by zero along `ι` followed by direct
image along `π`. -/
public def moduleExtensionByZeroCompIsoPushforward :
    moduleExtensionByZero B Y.obj Y.property (ofEtaleHom B (ι ≫ π)) Λ ≅
      moduleExtensionByZero B Wbar.obj Wbar.property (ofEtaleHom B ι) Λ ⋙
        (smallEtaleBaseChange B π).sheafPushforwardContinuous (ModuleCat.{u + 1} Λ)
          (topology B Y.obj Y.property) (topology B Wbar.obj Wbar.property) :=
  haveI := smallEtalePostcompose_isContinuous B Y.obj Y.property (ofEtaleHom B (ι ≫ π))
  haveI := smallEtalePostcompose_isContinuous B Wbar.obj Wbar.property (ofEtaleHom B ι)
  haveI := abelianExtensionByZero_additive B Y.obj Y.property (ofEtaleHom B (ι ≫ π))
  haveI := abelianExtensionByZero_additive B Wbar.obj Wbar.property (ofEtaleHom B ι)
  leftAdjointIsoModuleLift.{u + 1} Λ
      (smallEtalePostcompose B Y.obj Y.property (ofEtaleHom B (ι ≫ π))) _ _
      (moduleExtensionByZeroAdjunction B Y.obj Y.property (ofEtaleHom B (ι ≫ π)) Λ)
      (abelianExtensionByZeroAdjunction B Y.obj Y.property (ofEtaleHom B (ι ≫ π))) ≪≫
    moduleLiftNatIso.{u + 1} Λ _ _ _ _ (abelianExtensionByZeroCompIsoPushforward B ι π) ≪≫
    eqToIso (moduleLift_comp.{u + 1} Λ _ _ _ _ _) ≪≫
    Functor.isoWhiskerRight (leftAdjointIsoModuleLift.{u + 1} Λ
        (smallEtalePostcompose B Wbar.obj Wbar.property (ofEtaleHom B ι)) _ _
        (moduleExtensionByZeroAdjunction B Wbar.obj Wbar.property (ofEtaleHom B ι) Λ)
        (abelianExtensionByZeroAdjunction B Wbar.obj Wbar.property (ofEtaleHom B ι))).symm _ ≪≫
    Functor.isoWhiskerLeft _
      (sheafPushforwardContinuousIsoModuleLift.{u + 1} Λ (smallEtaleBaseChange B π) _ _).symm

end AlgebraicGeometry.SmallEtale

namespace Stacks.EtaleCohomology

open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.SmallEtale

attribute [local instance] moduleCat_hasLimitsOfSize

variable (Λ : Type (u + 1)) [Ring Λ]

/-- **Extension by zero along an étale composite of an open immersion and a finite morphism.**
Let `ι : W ⟶ W̄` be an open immersion and `π : W̄ ⟶ X` a finite morphism with `ι ≫ π` étale. Then
`(ι ≫ π)_! ≅ π_* ∘ ι_!` on sheaves of `Λ`-modules on Mathlib's small étale sites. -/
public def etaleModuleExtensionByZeroCompIsoDirectImage {W Wbar X : Scheme.{u}} (ι : W ⟶ Wbar)
    (π : Wbar ⟶ X) [IsOpenImmersion ι] [IsFinite π] [Etale (ι ≫ π)] :
    etaleModuleExtensionByZero.{u, u + 1} Λ (ι ≫ π) ≅
      etaleModuleExtensionByZero.{u, u + 1} Λ ι ⋙ etaleModuleDirectImage.{u, u + 1} Λ π := by
  let A := ModuleCat.{u + 1} Λ
  let B := BigEtaleSite.containing X
  have hX : B.Contains X := BigEtaleSite.contains_containing X
  have hWbar : B.Contains Wbar :=
    (Scheme.size_le_of_locallyOfFiniteType_of_quasiCompact π).trans_lt hX
  have hW : B.Contains W := Scheme.size_lt_of_isOpenImmersion ι hWbar
  let Xb : B.Scheme := B.obj X hX
  let Wbarb : B.Scheme := B.obj Wbar hWbar
  let Wb : B.Scheme := B.obj W hW
  let ιb : Wb ⟶ Wbarb := ObjectProperty.homMk ι
  let πb : Wbarb ⟶ Xb := ObjectProperty.homMk π
  have : IsOpenImmersion (B.inclusion.map ιb) := ‹IsOpenImmersion ι›
  have : IsFinite (B.inclusion.map πb) := ‹IsFinite π›
  have := AlgebraicGeometry.smallEtaleBaseChange_isContinuous B πb
  have : Etale (B.inclusion.map (ιb ≫ πb)) := ‹Etale (ι ≫ π)›
  let eW := sheafEquiv B Wb.obj Wb.property A
  let eWbar := sheafEquiv B Wbarb.obj Wbarb.property A
  let eX := sheafEquiv B Xb.obj Xb.property A
  let Tε :=
    sheafEquivExtensionByZeroIsoUnconditional B Xb.obj Xb.property (ofEtaleHom B (ιb ≫ πb)) A
      (etaleModuleExtensionByZeroAdj.{u, u + 1} Λ (ι ≫ π))
      (moduleExtensionByZeroAdjunction B Xb.obj Xb.property (ofEtaleHom B (ιb ≫ πb)) Λ)
  let Tι := sheafEquivExtensionByZeroIsoUnconditional B Wbarb.obj Wbarb.property (ofEtaleHom B ιb) A
    (etaleModuleExtensionByZeroAdj.{u, u + 1} Λ ι)
    (moduleExtensionByZeroAdjunction B Wbarb.obj Wbarb.property (ofEtaleHom B ιb) Λ)
  let Pπ : (AlgebraicGeometry.smallEtaleBaseChange B πb).sheafPushforwardContinuous A
        (topology B Xb.obj Xb.property) (topology B Wbarb.obj Wbarb.property) ⋙ eX.functor ≅
      eWbar.functor ⋙ etaleModuleDirectImage.{u, u + 1} Λ π :=
    (Iso.inverseCompIso (G := eWbar.symm) (Iso.isoCompInverse (H := eX.symm)
      (toEtaleSitePushforwardBaseChangeIso B πb A) ≪≫ Functor.associator _ _ _)).symm
  let φ : eW.functor ⋙ etaleModuleExtensionByZero.{u, u + 1} Λ (ι ≫ π) ≅
      eW.functor ⋙ (etaleModuleExtensionByZero.{u, u + 1} Λ ι ⋙
        etaleModuleDirectImage.{u, u + 1} Λ π) :=
    Tε ≪≫ Functor.isoWhiskerRight (moduleExtensionByZeroCompIsoPushforward B ιb πb Λ) _ ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ Pπ ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight Tι.symm _ ≪≫
      Functor.associator _ _ _
  exact Iso.isoInverseComp (G := eW) φ ≪≫ eW.invFunIdAssoc _

end Stacks.EtaleCohomology

end
