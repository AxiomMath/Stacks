module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposLowerShriekUnit
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackModulesComp
public import StacksFrontier.Deformation.ToposThickening.FlatThickeningComplexLifts
public import StacksFrontier.Deformation.ToposThickening.TrivialExtensionUniversal

/-!
# The flat lift `π^*ℱ` of Stacks 08VY

In Situation **Stacks 08VX**, presented on one site as
`Deformation.ToposThickening.FlatThickeningComplexSituation`, let
`π : (Sh(C'₁), O'₁) ⟶ (Sh(C), O)` be the canonical splitting of Remark Stacks 08ML. This file
identifies the `O'₁`-module `π^*ℱ` with the trivial extension `ℱ ⊕ (I₁ ⊗_O ℱ)` of Stacks 08MI and
builds it as a flat lift of `ℱ` across the first column.

The splitting is the change of coefficients `k` along the canonical splitting `s : O ⟶ O'₁` of
structure sheaves followed by the inverse of the equivalence `ι : (Sh(C), O) ⟶ (Sh(C'₁), i_*O)`,
so `π^*ℱ = k^*(ι^{-1})^*ℱ = k^*ι_*ℱ`, and `k^*` is left adjoint to restriction of scalars along
`s`; the trivial extension is the value at `ℱ` of any such left adjoint
(`Deformation.ToposThickening.trivialExtensionIsoOfAdjunction`).

## Main definitions

* `Deformation.ToposThickening.FlatThickeningComplexSituation.trivialModule`: the `O'₁`-module
  `π^*ℱ`.
* `Deformation.ToposThickening.FlatThickeningComplexSituation.trivialModuleIso`: the
  identification of `π^*ℱ` with the trivial extension.
* `Deformation.ToposThickening.FlatThickeningComplexSituation.trivialLift`: `π^*ℱ` as a flat lift
  of `ℱ` across the first column.

## References

* [Stacks Project, Tag 08VY](https://stacks.math.columbia.edu/tag/08VY)
* [Stacks Project, Tag 08ML](https://stacks.math.columbia.edu/tag/08ML)
* [Stacks Project, Tag 08MI](https://stacks.math.columbia.edu/tag/08MI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor pushforwardModuleFunctor)
open Stacks.Sheaves.RingedToposModules.RingedToposHom (pullbackModules)

universe v u v₂ u₂ w vB uB wB vB' uB' wB' e

namespace Deformation.ToposThickening

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v₂, u₂, w}}
  {B : RingedTopos.{vB, uB, wB}} {B' : RingedTopos.{vB', uB', wB'}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [B.J.HasSheafCompose (forget RingCat.{wB})] [B'.J.HasSheafCompose (forget RingCat.{wB'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{wB} RingCat.{wB})]
  [B'.J.HasSheafCompose (forget₂ CommRingCat.{wB'} RingCat.{wB'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [B.J.HasSheafCompose (forget AddCommGrpCat.{wB})]
  [B'.J.HasSheafCompose (forget AddCommGrpCat.{wB'})]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w}] [HasWeakSheafify Y.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify X.J AddCommGrpCat.{w}]
  {i : RingedToposHom X Y} {t : RingedToposHom B B'}

namespace FlatThickeningComplexSituation

variable (D : FlatThickeningComplexSituation i t)

/-- **The `O'₁`-module `π^*ℱ`**: the pullback of `ℱ` along the canonical splitting `π`. -/
noncomputable def trivialModule : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) :=
  D.π.retraction.toModulesHom.pullbackModules.obj D.reduction

/-- The change of coefficients `k : (Sh(C'₁), O'₁) ⟶ (Sh(C'₁), i_*O)` along the canonical
splitting `s : i_*O ⟶ O'₁`. -/
noncomputable abbrev splittingChange : RingedToposHom Y (reshape Y (baseRing i)) :=
  RingedToposHom.coefficientMorphism Y.J (D.upper.canonicalSplittingRingHom D.upper_isComplex)

/-- `k^*` is left adjoint to restriction of scalars along the splitting of `π`. -/
noncomputable def splittingChangeAdjunction :
    D.splittingChange.toModulesHom.pullbackModules ⊣ splitRestriction i D.upper.lower.first D.π :=
  (RingedToposHom.coefficientMorphismPullbackAdjunction
    (D.upper.canonicalSplittingRingHom D.upper_isComplex)).ofNatIsoRight
    (eqToIso (by
      unfold splitRestriction
      rw [π, FirstOrderThickeningComplex.splittingRingHom_canonicalTrivialization]))

/-- **`(ι^{-1})^*ℱ = ι_*ℱ`**: pulling `ℱ` back along the inverse of the equivalence
`ι : (Sh(C), O) ⟶ (Sh(C'₁), i_*O)` is its direct image `i_*ℱ`, read as an `i_*O`-module. The
counit `ι^*ι_*ℱ ⟶ ℱ` is invertible, and pulling back along `ι` and then along its inverse is the
identity. -/
noncomputable def reductionPullbackInverseIso :
    haveI : i.toToposHom.pushforward.IsEquivalence := D.upper.lower.first.equiv
    (RingedToposHom.inverse
        (FirstOrderThickeningComplex.baseEquivalence i)).toModulesHom.pullbackModules.obj
        D.reduction ≅ D.F :=
  have : i.toToposHom.pushforward.IsEquivalence := D.upper.lower.first.equiv
  have := RingedToposHom.isIso_pullbackAdjPushforwardModules_counit
    (FirstOrderThickeningComplex.baseEquivalence i)
  (RingedToposHom.inverse
      (FirstOrderThickeningComplex.baseEquivalence i)).toModulesHom.pullbackModules.mapIso
      (asIso ((RingedToposHom.pullbackAdjPushforwardModules
        (FirstOrderThickeningComplex.baseEquivalence i)).counit.app D.reduction)).symm ≪≫
    ((RingedToposHom.pullbackModulesCompIso
      (RingedToposHom.inverse (FirstOrderThickeningComplex.baseEquivalence i))
      (FirstOrderThickeningComplex.baseEquivalence i)).app _).symm ≪≫
    (RingedToposHom.pullbackModulesCompInverseIso
      (FirstOrderThickeningComplex.baseEquivalence i)).app _ ≪≫ Iso.refl D.F

/-- **`π^*ℱ = k^*ι_*ℱ`**: `π = ι^{-1} ∘ k`, so `π^*ℱ = k^*(ι^{-1})^*ℱ`, and
`(ι^{-1})^*ℱ = ι_*ℱ` by `reductionPullbackInverseIso`. -/
noncomputable def trivialModuleIsoPullback :
    D.trivialModule ≅ D.splittingChange.toModulesHom.pullbackModules.obj D.F :=
  have : i.toToposHom.pushforward.IsEquivalence := D.upper.lower.first.equiv
  (RingedToposHom.pullbackModulesCompIso D.splittingChange
      (RingedToposHom.inverse (FirstOrderThickeningComplex.baseEquivalence i))).app D.reduction ≪≫
    D.splittingChange.toModulesHom.pullbackModules.mapIso D.reductionPullbackInverseIso

/-- **`π^*ℱ` is the trivial extension `ℱ ⊕ (I₁ ⊗_O ℱ)`**: `π^*ℱ = k^*ι_*ℱ`, and `k^*ι_*ℱ` is the
trivial extension because `k^*` is left adjoint to restriction of scalars along the
splitting. -/
noncomputable def trivialModuleIso :
    D.trivialModule ≅ (trivialExtension D.upper.lower.first D.π D.F
      (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj D.F).obj
        D.upper.lower.first.I) (𝟙 _)).Z.left :=
  D.trivialModuleIsoPullback ≪≫
    trivialExtensionIsoOfAdjunction D.upper.lower.first D.π D.F D.splittingChangeAdjunction

/-- **`π^*ℱ` as a flat lift of `ℱ` across the first column**: the `O'₁`-module `π^*ℱ`, flat over
`O_{ℬ'₁}`, with its identification with `ℱ` on `(Sh(C), O)` (`trivialLift_π`). Flatness and the
short exactness of `0 ⟶ I₁·π^*ℱ ⟶ π^*ℱ ⟶ i₁_*ℱ ⟶ 0` come from Stacks 08MQ: through
`trivialModuleIso`, `π^*ℱ` is the trivial extension of `ℱ` by `I₁ ⊗_O ℱ`, whose action map is the
identity. -/
noncomputable def trivialLift : FlatLift i D.f₁ D.upper.lower.first D.F :=
  flatLiftOfIso i t D.f D.f₁ D.upper.lower.first D.lower.lower.first D.restrict₁ D.F
    D.isStrictPullbackIdealMap₁ D.isFlat_reducedBaseModule₁ D.isIso_canonicalFirstFactor₁
    (trivialExtension D.upper.lower.first D.π D.F
      (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj D.F).obj
        D.upper.lower.first.I) (𝟙 _))
    (trivialExtension_extensionActionMap D.upper.lower.first D.π D.F _ _) D.trivialModuleIso

/-- The module of `trivialLift` is `π^*ℱ`. -/
theorem trivialLift_module' : D.trivialLift.module' = D.trivialModule := rfl

/-- **The map `π^*ℱ ⟶ i₁_*ℱ` of `trivialLift` is the canonical one**: through
`π^*ℱ = k^*ι_*ℱ`, it is the transpose under `k^* ⊣ s^*` of the identification of `ι_*ℱ` with its
restriction of scalars to `O'₁` and back along the splitting `s`. -/
theorem trivialLift_π :
    D.trivialLift.π = D.trivialModuleIsoPullback.hom ≫
      (D.splittingChangeAdjunction.homEquiv _ _).symm
        (splitRestrictionRestrictScalarsIso i D.upper.lower.first D.π D.F).inv :=
  (Category.assoc _ _ _).trans (congrArg (D.trivialModuleIsoPullback.hom ≫ ·)
    (trivialExtensionIsoOfAdjunction_hom_comp_fst D.upper.lower.first D.π D.F
      D.splittingChangeAdjunction))

/-- The class attached to `trivialLift` is the class of the trivial extension. -/
theorem fixedActionExtensionClass_trivialLift
    [HasExt.{e} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))] :
    (D.trivialLift.fixedActionExtensionClass i t D.f D.f₁
        D.upper.lower.first D.lower.lower.first D.restrict₁ D.F D.isStrictPullbackIdealMap₁
        D.isFlat_reducedBaseModule₁).1 =
      extensionClass D.F (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj D.F).obj
          D.upper.lower.first.I)
        (trivialExtension D.upper.lower.first D.π D.F
          (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj D.F).obj
            D.upper.lower.first.I) (𝟙 _)) :=
  fixedActionExtensionClass_flatLiftOfIso i t D.f D.f₁ D.upper.lower.first D.lower.lower.first
    D.restrict₁ D.F D.isStrictPullbackIdealMap₁ D.isFlat_reducedBaseModule₁
    D.isIso_canonicalFirstFactor₁ _
    (trivialExtension_extensionActionMap D.upper.lower.first D.π D.F _ _) D.trivialModuleIso

end FlatThickeningComplexSituation

end Deformation.ToposThickening

end
