module

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekComposition
public import StacksFrontier.AlgebraicGeometry.Etale.FiniteSupportExtensionByZero.CoefficientUniverse
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.FiniteDirectImageUnconditional

/-!
# Extension by zero along an étale composite of an open immersion and a finite morphism, at
every coefficient universe

Let `ι : W ⟶ W̄` be an open immersion and `π : W̄ ⟶ X` a finite morphism whose composite
`ε = ι ≫ π` is étale. Then `ε_! ≅ π_* ∘ ι_!`. The file
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.FiniteDirectImageUnconditional`
proves this for coefficient rings in `Type (u + 1)`; here the coefficient ring `Λ : Type r` is in
an arbitrary universe.

## Main definitions

* `AlgebraicGeometry.SmallEtale.abelianExtensionByZeroCompIsoPushforwardUniv`: `ε_! ≅ π_* ∘ ι_!`
  for abelian sheaves with coefficients in `AddCommGrpCat.{max (u + 1) v}` on the small étale
  sites of Tag 021B.
* `AlgebraicGeometry.SmallEtale.moduleExtensionByZeroCompIsoPushforwardUniv`: the same for
  sheaves of `Λ`-modules, `Λ : Type v`.
* `Stacks.EtaleCohomology.etaleModuleExtensionByZeroCompIsoDirectImageUniv`: `ε_! ≅ π_* ∘ ι_!`
  for sheaves of `Λ`-modules on Mathlib's small étale sites, `Λ : Type r`.

## Implementation notes

For abelian sheaves the isomorphism is
`ε_! ≅ ε_!^c ≅ ι_!^c ⋙ π_!^c ≅ ι_! ⋙ π_*`, where `(-)_!^c` is the direct image with proper
support of [Stacks, Tag 0F4X]: extension by zero along an étale morphism is the direct image with
compact support (`AlgebraicGeometry.SmallEtale.abelianExtensionByZeroIsoFShriekUniv`, Tags 0F6Q
and 0F6N), the direct images with proper support compose (Tag 0F50) and for the finite, hence
proper, `π` the direct image with proper support is `π_*` (Tag 0F51). All three are available at
every coefficient universe. The module version is the lift of the abelian one, and the version
on Mathlib's small étale sites is its transport along the equivalence of the two models.

## References

* [Stacks Project, Tag 0F6Q](https://stacks.math.columbia.edu/tag/0F6Q)
* [Stacks Project, Tag 0F50](https://stacks.math.columbia.edu/tag/0F50)
* [Stacks Project, Tag 0F51](https://stacks.math.columbia.edu/tag/0F51)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v r

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) {W Wbar Y : B.Scheme} (ι : W ⟶ Wbar) (π : Wbar ⟶ Y)
  [IsOpenImmersion (B.inclusion.map ι)] [IsFinite (B.inclusion.map π)]
  [Etale (B.inclusion.map (ι ≫ π))]

/-- **`ε_! = π_* ∘ ι_!` for abelian sheaves at every coefficient universe.** For an open
immersion `ι` and a finite morphism `π` of a big étale site with `ε = ι ≫ π` étale, extension by
zero along `ε` is extension by zero along `ι` followed by direct image along `π`, for abelian
sheaves with coefficients in `AddCommGrpCat.{max (u + 1) v}`. -/
public def abelianExtensionByZeroCompIsoPushforwardUniv :
    abelianExtensionByZeroUniv.{u, v} B Y.obj Y.property (ofEtaleHom B (ι ≫ π)) ≅
      abelianExtensionByZeroUniv.{u, v} B Wbar.obj Wbar.property (ofEtaleHom B ι) ⋙
        etalePushforward.{u, max (u + 1) v} B π :=
  haveI : IsSeparated (B.inclusion.map ι) := inferInstance
  haveI : IsSeparated (B.inclusion.map (ι ≫ π)) := by
    rw [Functor.map_comp]; infer_instance
  haveI : LocallyOfFiniteType (B.inclusion.map (ι ≫ π)) := by
    rw [Functor.map_comp]; infer_instance
  haveI : LocallyQuasiFinite (B.inclusion.map (ι ≫ π)) := by
    rw [Functor.map_comp]; infer_instance
  abelianExtensionByZeroIsoFShriekUniv.{u, v} B Y.obj Y.property (ofEtaleHom B (ι ≫ π)) ≪≫
    fShriekFunctorIsoProperSupport.{u, v} B (ι ≫ π) ≪≫
    (properSupportFunctor_compIso B ι π).val.symm ≪≫
    Functor.isoWhiskerRight (fShriekFunctorIsoProperSupport.{u, v} B ι).symm _ ≪≫
    Functor.isoWhiskerLeft _ (properSupportIsoPushforward.{u, max (u + 1) v} B π) ≪≫
    Functor.isoWhiskerRight
      (abelianExtensionByZeroIsoFShriekUniv.{u, v} B Wbar.obj Wbar.property
        (ofEtaleHom B ι)).symm _

/-- Extension by zero of abelian sheaves is additive, being a left adjoint. -/
public theorem abelianExtensionByZeroUniv_additive (X : Scheme.{u}) (hX : B.Contains X)
    (U : SmallEtale B X hX) : (abelianExtensionByZeroUniv.{u, v} B X hX U).Additive :=
  (abelianExtensionByZeroAdjunctionUniv.{u, v} B X hX U).left_adjoint_additive

variable (Λ : Type v) [Ring Λ]

open Stacks.ModuleCatLift in
/-- **`ε_! = π_* ∘ ι_!` for sheaves of `Λ`-modules at every coefficient universe.** For an open
immersion `ι` and a finite morphism `π` of a big étale site with `ε = ι ≫ π` étale, extension by
zero along `ε` of sheaves of `Λ`-modules, `Λ : Type v`, is extension by zero along `ι` followed
by direct image along `π`. -/
public def moduleExtensionByZeroCompIsoPushforwardUniv :
    moduleExtensionByZero B Y.obj Y.property (ofEtaleHom B (ι ≫ π)) Λ ≅
      moduleExtensionByZero B Wbar.obj Wbar.property (ofEtaleHom B ι) Λ ⋙
        (smallEtaleBaseChange B π).sheafPushforwardContinuous (ModuleCat.{max (u + 1) v} Λ)
          (topology B Y.obj Y.property) (topology B Wbar.obj Wbar.property) :=
  haveI := smallEtalePostcompose_isContinuous B Y.obj Y.property (ofEtaleHom B (ι ≫ π))
  haveI := smallEtalePostcompose_isContinuous B Wbar.obj Wbar.property (ofEtaleHom B ι)
  haveI := abelianExtensionByZeroUniv_additive.{u, v} B Y.obj Y.property (ofEtaleHom B (ι ≫ π))
  haveI := abelianExtensionByZeroUniv_additive.{u, v} B Wbar.obj Wbar.property (ofEtaleHom B ι)
  leftAdjointIsoModuleLift.{max (u + 1) v} Λ
      (smallEtalePostcompose B Y.obj Y.property (ofEtaleHom B (ι ≫ π))) _ _
      (moduleExtensionByZeroAdjunction B Y.obj Y.property (ofEtaleHom B (ι ≫ π)) Λ)
      (abelianExtensionByZeroAdjunctionUniv.{u, v} B Y.obj Y.property (ofEtaleHom B (ι ≫ π))) ≪≫
    moduleLiftNatIso.{max (u + 1) v} Λ _ _ _ _
      (abelianExtensionByZeroCompIsoPushforwardUniv.{u, v} B ι π) ≪≫
    eqToIso (moduleLift_comp.{max (u + 1) v} Λ _ _ _ _ _) ≪≫
    Functor.isoWhiskerRight (leftAdjointIsoModuleLift.{max (u + 1) v} Λ
        (smallEtalePostcompose B Wbar.obj Wbar.property (ofEtaleHom B ι)) _ _
        (moduleExtensionByZeroAdjunction B Wbar.obj Wbar.property (ofEtaleHom B ι) Λ)
        (abelianExtensionByZeroAdjunctionUniv.{u, v} B Wbar.obj Wbar.property
          (ofEtaleHom B ι))).symm _ ≪≫
    Functor.isoWhiskerLeft _
      (sheafPushforwardContinuousIsoModuleLift.{max (u + 1) v} Λ (smallEtaleBaseChange B π)
        _ _).symm

end AlgebraicGeometry.SmallEtale

namespace Stacks.EtaleCohomology

open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.SmallEtale

attribute [local instance] moduleCat_hasLimitsOfSize

variable (Λ : Type r) [Ring Λ]

/-- **Extension by zero along an étale composite of an open immersion and a finite morphism, at
every coefficient universe.** Let `ι : W ⟶ W̄` be an open immersion and `π : W̄ ⟶ X` a finite
morphism with `ι ≫ π` étale. Then `(ι ≫ π)_! ≅ π_* ∘ ι_!` on sheaves of `Λ`-modules on Mathlib's
small étale sites, for a ring `Λ` in an arbitrary universe. -/
public def etaleModuleExtensionByZeroCompIsoDirectImageUniv {W Wbar X : Scheme.{u}}
    (ι : W ⟶ Wbar) (π : Wbar ⟶ X) [IsOpenImmersion ι] [IsFinite π] [Etale (ι ≫ π)] :
    etaleModuleExtensionByZero.{u, r} Λ (ι ≫ π) ≅
      etaleModuleExtensionByZero.{u, r} Λ ι ⋙ etaleModuleDirectImage.{u, r} Λ π := by
  let A := ModuleCat.{max (u + 1) r} Λ
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
      (etaleModuleExtensionByZeroAdj.{u, r} Λ (ι ≫ π))
      (moduleExtensionByZeroAdjunction B Xb.obj Xb.property (ofEtaleHom B (ιb ≫ πb)) Λ)
  let Tι := sheafEquivExtensionByZeroIsoUnconditional B Wbarb.obj Wbarb.property (ofEtaleHom B ιb) A
    (etaleModuleExtensionByZeroAdj.{u, r} Λ ι)
    (moduleExtensionByZeroAdjunction B Wbarb.obj Wbarb.property (ofEtaleHom B ιb) Λ)
  let Pπ : (AlgebraicGeometry.smallEtaleBaseChange B πb).sheafPushforwardContinuous A
        (topology B Xb.obj Xb.property) (topology B Wbarb.obj Wbarb.property) ⋙ eX.functor ≅
      eWbar.functor ⋙ etaleModuleDirectImage.{u, r} Λ π :=
    (Iso.inverseCompIso (G := eWbar.symm) (Iso.isoCompInverse (H := eX.symm)
      (toEtaleSitePushforwardBaseChangeIso B πb A) ≪≫ Functor.associator _ _ _)).symm
  let φ : eW.functor ⋙ etaleModuleExtensionByZero.{u, r} Λ (ι ≫ π) ≅
      eW.functor ⋙ (etaleModuleExtensionByZero.{u, r} Λ ι ⋙
        etaleModuleDirectImage.{u, r} Λ π) :=
    Tε ≪≫ Functor.isoWhiskerRight (moduleExtensionByZeroCompIsoPushforwardUniv B ιb πb Λ) _ ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ Pπ ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight Tι.symm _ ≪≫
      Functor.associator _ _ _
  exact Iso.isoInverseComp (G := eW) φ ≪≫ eW.invFunIdAssoc _

end Stacks.EtaleCohomology

end
