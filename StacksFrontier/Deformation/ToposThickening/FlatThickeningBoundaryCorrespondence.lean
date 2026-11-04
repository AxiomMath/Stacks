module

public import StacksFrontier.Deformation.ToposThickening.FixedActionFlatnessUnconditional
public import StacksFrontier.Deformation.ToposThickening.FlatLiftCorrespondence
public import StacksFrontier.Deformation.ToposThickening.FlatThickeningBoundary
public import StacksFrontier.Deformation.ToposThickening.IdealTensorShortExactness

/-!
# Stacks 08VY with two of its Stacks 08MQ hypotheses supplied

Situation **Stacks 08VX** is the diagram of
`StacksFrontier/Deformation/ToposThickening/FlatThickeningBoundary.lean`, and
`Deformation.ToposThickening.FirstOrderThickeningComplex`
`.boundary_underlyingExtensionClass_eq_obstruction` proves **Stacks 08VY** there in its general
form, for an arbitrary extension `E₁` of `ℱ` over `O'₁` receiving a map from the extension `E₂`
attached to `ℱ'₂`. Two of the consequences of Stacks 08MQ that its proof consumes are the
flat-lift dictionary `Deformation.ToposThickening.IsFlatLiftCorrespondence` for the third column,
used to turn that column's obstruction class into the existence of a flat lift through
Stacks 08VW, and the flatness criterion
`Deformation.ToposThickening.IsFlatOfFixedActionIdentity` for the first column.

Both are proved, in
`StacksFrontier/Deformation/ToposThickening/FlatLiftCorrespondence.lean` and
`StacksFrontier/Deformation/ToposThickening/FixedActionFlatnessUnconditional.lean`, each of which is
downstream of Stacks 08VY's module, so neither binder can be discharged in place. This file
restates the general form without them.

## Main results

* `Deformation.ToposThickening.FirstOrderThickeningComplex`
  `.boundary_underlyingExtensionClass_eq_obstruction'`: **Stacks 08VY in its general form**, with
  the third column's flat-lift dictionary supplied by
  `Deformation.ToposThickening.isFlatLiftCorrespondence` and the first column's flatness
  criterion by `Deformation.ToposThickening.isFlatOfFixedActionIdentity`, rather than assumed.

The one consequence of Stacks 08MQ that remains a hypothesis there remains a hypothesis here:
`Deformation.ToposThickening.FirstOrderThickeningComplex.IsIdealTensorShortExact` for the
coefficient sequence of the lower row, which is not proved in the library at the time of
writing.

## References

* [Stacks Project, Tag 08VY](https://stacks.math.columbia.edu/tag/08VY)
* [Stacks Project, Tag 08VX](https://stacks.math.columbia.edu/tag/08VX)
* [Stacks Project, Tag 08VW](https://stacks.math.columbia.edu/tag/08VW)
* [Stacks Project, Tag 08MQ](https://stacks.math.columbia.edu/tag/08MQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)

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
  {i : RingedToposHom X Y} {t : RingedToposHom B B'}

namespace FirstOrderThickeningComplex

variable (S : FirstOrderThickeningComplex i) (T : FirstOrderThickeningComplex t)
  (f : RingedToposHom X B) (f₁ : RingedToposHom Y B')
  (f₂ : RingedToposHom (reshape Y S.lower.O₂) (reshape B' T.lower.O₂))
  (f₃ : RingedToposHom (reshape Y S.O₃) (reshape B' T.O₃))
  (commf₁ : f₁.comp i = t.comp f)
  (commf₂ : f₂.comp (reshapeHom i S.lower.O₂ S.lower.fSharp₂) =
    (reshapeHom t T.lower.O₂ T.lower.fSharp₂).comp f)
  (commf₃ : f₃.comp S.thirdHom = T.thirdHom.comp f)
  (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i)))

/-- **Stacks 08VY in its general form, with two of its Stacks 08MQ hypotheses supplied.**
This is `Deformation.ToposThickening.FirstOrderThickeningComplex`
`.boundary_underlyingExtensionClass_eq_obstruction` with two of the consequences of Stacks 08MQ
that its proof consumes supplied: the `IsFlatLiftCorrespondence` hypothesis — through which the
third column's obstruction class becomes the existence of a flat lift, by Stacks 08VW — by
`Deformation.ToposThickening.isFlatLiftCorrespondence`, and the `IsFlatOfFixedActionIdentity`
hypothesis for the first column by
`Deformation.ToposThickening.isFlatOfFixedActionIdentity`. The remaining consequence of
Stacks 08MQ that the proof consumes, `IsIdealTensorShortExact` for the lower row, is still
carried as the hypothesis `hMQ`. -/
theorem boundary_underlyingExtensionClass_eq_obstruction'
    [HasExt.{e} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i)))]
    [HasExt.{e} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
    [HasExt.{e} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf S.O₃))]
    (hS : S.IsComplex) (hT : T.IsComplex)
    (hTSE : (ShortComplex.mk T.idealMap₃₂ T.idealMap₂₁ hT).ShortExact)
    (π : Trivialization i)
    (hπ : S.upper.ringMapH ≫ S.lower.ringMapH =
      S.whole.ringMap₂ ≫ splittingRingHom i S.lower.first π)
    (hstrict₁ : (MorphismOfThickenings.ofFirstOrderThickenings i t f f₁
      S.lower.first T.lower.first commf₁).IsStrict)
    (hstrict₂ : (MorphismOfThickenings.ofFirstOrderThickenings
      (reshapeHom i S.lower.O₂ S.lower.fSharp₂) (reshapeHom t T.lower.O₂ T.lower.fSharp₂) f f₂
      S.lower.second T.lower.second commf₂).IsStrict)
    (hstrict₃ : (MorphismOfThickenings.ofFirstOrderThickenings S.thirdHom T.thirdHom f f₃
      S.third T.third commf₃).IsStrict)
    (hf₁ : f₁.IsFlat) (hf₂ : f₂.IsFlat) (hf₃ : f₃.IsFlat)
    (commh : f₂.comp S.lowerHorizontalHom = T.lowerHorizontalHom.comp f₁)
    (commh₃₂ : f₃.comp S.upperHorizontalHom = T.upperHorizontalHom.comp f₂)
    (hF : IsFlatOverBase i f F)
    (E₂ : Abelian.YonedaExtension
      ((structureRestrict (reshapeHom i S.lower.O₂ S.lower.fSharp₂)).obj F)
      ((structureRestrict (reshapeHom i S.lower.O₂ S.lower.fSharp₂)).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).obj
            S.lower.second.I)) 0)
    (hE₂ : (extensionActionMap S.lower.second E₂).1 =
      𝟙 (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).obj S.lower.second.I))
    (E₁ : Abelian.YonedaExtension ((structureRestrict i).obj F)
      ((structureRestrict i).obj (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj
          F).obj S.lower.first.I)) 0)
    (u : E₂.Z.left ⟶ (S.lower.restrictedExtension E₁).Z.left)
    (hu : E₂.f ≫ u =
      (structureRestrict (reshapeHom i S.lower.O₂ S.lower.fSharp₂)).map
          (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).map S.idealMap₂₁) ≫
        (S.lower.restrictedExtension E₁).f)
    (hug : u ≫ (S.lower.restrictedExtension E₁).g = E₂.g) :
    (extensionActionMap S.lower.first E₁).1 =
        𝟙 (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).obj
            S.lower.first.I) ∧
      (extensionActionMap S.lower.first (trivialExtension S.lower.first π F
          (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).obj S.lower.first.I)
          (𝟙 (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).obj
              S.lower.first.I)))).1 =
        𝟙 (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).obj
            S.lower.first.I) ∧
      AlgebraicGeometry.SheafOfModules.IsFlat
          ((SheafOfModules.restrictScalars
            ((sheafCompose Y.J (forget₂ CommRingCat.{w} RingCat.{w})).map
              f₁.fSharpInverseImage)).obj
            (trivialExtension S.lower.first π F
              (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).obj
                  S.lower.first.I)
              (𝟙 (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).obj
                  S.lower.first.I))).Z.left) ∧
      AlgebraicGeometry.SheafOfModules.IsFlat
          ((SheafOfModules.restrictScalars
            ((sheafCompose Y.J (forget₂ CommRingCat.{w} RingCat.{w})).map
              f₁.fSharpInverseImage)).obj E₁.Z.left) ∧
      underlyingExtensionClass.{e} i S.lower.first π F
            (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).obj
                S.lower.first.I) E₁ =
          splitRestrictionExtHom.{e} S.lower.first π F
              (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).obj
                  S.lower.first.I)
              (extensionClass.{_, _, _, _, _, _, e} F
                (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).obj
                    S.lower.first.I) E₁) -
            splitRestrictionExtHom.{e} S.lower.first π F
              (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).obj
                  S.lower.first.I)
              (extensionClass.{_, _, _, _, _, _, e} F
                (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).obj
                    S.lower.first.I)
                (trivialExtension S.lower.first π F
                  (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).obj
                      S.lower.first.I)
                  (𝟙 (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).obj
                      S.lower.first.I)))) ∧
      (HasFlatLift S.thirdHom f₃ S.third F ↔
          existenceObstructionClass S.third F
              (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).obj S.third.I)
              (𝟙 (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).obj
                  S.third.I)) = 0) ∧
      (underlyingExtensionClass.{e} i S.lower.first π F
            (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).obj
                S.lower.first.I) E₁).comp
          (S.isIdealTensorShortExact T hS f f₁ f₂ f₃ commf₁ commf₂ commf₃ F
            hT hTSE hF hstrict₁ hstrict₂ hstrict₃ hf₁ hf₂ hf₃ commh commh₃₂).extClass
          (by decide) =
        existenceObstructionClass S.third F
          (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).obj S.third.I)
          (𝟙 (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).obj
            S.third.I)) :=
  S.boundary_underlyingExtensionClass_eq_obstruction T f f₁ f₂ f₃ commf₁ commf₂ commf₃ F
    hS hT hTSE π hπ hstrict₁ hstrict₂ hstrict₃ hf₁ hf₂ hf₃ commh commh₃₂ hF
    (S.isIdealTensorShortExact T hS f f₁ f₂ f₃ commf₁ commf₂ commf₃ F) E₂ hE₂ E₁ u hu hug
    (isFlatOfFixedActionIdentity i t f f₁ S.lower.first T.lower.first commf₁ F)
    (isFlatLiftCorrespondence S.thirdHom T.thirdHom f f₃ S.third T.third commf₃ F)

end FirstOrderThickeningComplex

end Deformation.ToposThickening

end
