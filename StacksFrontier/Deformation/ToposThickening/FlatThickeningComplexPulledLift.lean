module

public import StacksFrontier.Deformation.ToposThickening.FlatThickeningComplexSituation

/-!
# The module `h^*ℱ'₂` of Stacks 08VY

In Situation **Stacks 08VX**, presented on one site as
`Deformation.ToposThickening.FlatThickeningComplexSituation`, let
`h : (Sh(C'₁), O'₁) ⟶ (Sh(C'₂), O'₂)` be the first morphism of the upper row. This file builds
the `O'₁`-module `h^*ℱ'₂` and the identification `i₁^*h^*ℱ'₂ ≅ i₂^*ℱ'₂ = ℱ` through which it
restricts to `ℱ` on `(Sh(C), O)`.

## Main definitions

* `Deformation.ToposThickening.FlatThickeningComplexSituation.pulledModule`: the module
  `h^*ℱ'₂`, the pullback of sheaves of modules along `h`.
* `Deformation.ToposThickening.FlatThickeningComplexSituation.pulledRestrictionIso`: the
  identification `i₁^*h^*ℱ'₂ ≅ ℱ`, from `h ∘ i₁ = i₂`.

## References

* [Stacks Project, Tag 08VY](https://stacks.math.columbia.edu/tag/08VY)
* [Stacks Project, Tag 08VX](https://stacks.math.columbia.edu/tag/08VX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor pushforwardModuleFunctor)
open Stacks.Sheaves.RingedToposModules.RingedToposHom (pullbackModules)

universe v u v₂ u₂ w vB uB wB vB' uB' wB'

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

/-- The morphism `h : (Sh(C'₁), O'₁) ⟶ (Sh(C'₂), O'₂)` of the upper row: the change of
coefficients along `h^♯ : O'₂ ⟶ O'₁`. -/
noncomputable abbrev h : RingedToposHom Y (reshape Y D.upper.lower.O₂) :=
  D.upper.lowerHorizontalHom

/-- **The module `h^*ℱ'₂`**: the pullback of `ℱ'₂` along `h`. -/
noncomputable def pulledModule : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) :=
  (pullbackModules D.h.toRingedToposModulesHom).obj D.F'

/-- The direct image along `i₁` followed by the direct image along `h` is the direct image along
`i₂`: on an `O`-module both are its direct image, read over `O'₂` through `O'₂ ⟶ O'₁ ⟶ i_*O`,
respectively through `O'₂ ⟶ i_*O`, and these agree by `h ∘ i₁ = i₂`. -/
noncomputable def pushforwardCompIso :
    i.pushforwardModules ⋙ D.h.pushforwardModules ≅ D.i₂.pushforwardModules :=
  Functor.isoWhiskerLeft i.pushforwardModules
      (RingedToposHom.coefficientMorphismPushforwardIso D.upper.lower.hSharp).symm ≪≫
    NatIso.ofComponents (fun M ↦ D.upper.lower.restrictHIso
      ((pushforwardModuleFunctor i.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj M))
      (fun _ ↦ by ext; rfl)

/-- **`h^*` followed by `i₁^*` is `i₂^*`**: both are left adjoint to the direct image along `i₂`,
by `pushforwardCompIso`. -/
noncomputable def pullbackCompIso :
    pullbackModules D.h.toRingedToposModulesHom ⋙ pullbackModules i.toRingedToposModulesHom ≅
      pullbackModules D.i₂.toRingedToposModulesHom :=
  ((D.h.pullbackAdjPushforwardModulesViaComparison.comp
      i.pullbackAdjPushforwardModulesViaComparison).ofNatIsoRight
        D.pushforwardCompIso).leftAdjointUniq
    D.i₂.pullbackAdjPushforwardModulesViaComparison

/-- **`h^*ℱ'₂` restricts to `ℱ`**: the identification `i₁^*h^*ℱ'₂ ≅ i₂^*ℱ'₂ = ℱ`. -/
noncomputable def pulledRestrictionIso :
    (pullbackModules i.toRingedToposModulesHom).obj D.pulledModule ≅ D.reduction :=
  D.pullbackCompIso.app D.F'

end FlatThickeningComplexSituation

end Deformation.ToposThickening

end
