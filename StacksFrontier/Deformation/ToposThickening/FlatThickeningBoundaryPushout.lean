module

public import StacksFrontier.Deformation.ToposThickening.FlatThickeningBoundaryCorrespondence
public import StacksFrontier.Deformation.ToposThickening.ExtensionPushoutComparison
public import StacksFrontier.Deformation.ToposThickening.ObstructionCompatibility

/-!
# Stacks 08VY at the two lifts the tag is about

Situation **Stacks 08VX** is the diagram of
`StacksFrontier/Deformation/ToposThickening/FlatThickeningBoundary.lean`, and **Stacks 08VY** says
that `π^*ℱ` and `h^*ℱ'₂` are `O'₁`-modules flat over `O_{ℬ'₁}` restricting to `ℱ`, that their
difference is a class `θ ∈ Ext¹_O(ℱ, f^*𝒥₁ ⊗_O ℱ)`, and that the boundary of `θ` is the
obstruction of Stacks 08VW to lifting `ℱ` to an `O'₃`-module flat over `O_{ℬ'₃}`.

`Deformation.ToposThickening.FirstOrderThickeningComplex`
`.boundary_underlyingExtensionClass_eq_obstruction` proves this for an arbitrary extension `E₁`
of `ℱ` over `O'₁` receiving a map `u` from the extension `E₂` attached to `ℱ'₂` which is
`I₂ ⊗ ℱ ⟶ I₁ ⊗ ℱ` on kernel modules and the identity on `ℱ` — the shape in which Remark
**Stacks 08MM** is stated. This file instantiates it at the extension that Stacks 08MJ
*constructs* from `ℱ'₂`, namely the pushout `ℱ'₂ ⊔_{I₂ ⊗ ℱ} (I₁ ⊗ ℱ)`, which is `h^*ℱ'₂`: the
missing input was the canonical map `ℱ'₂ ⟶ h^*ℱ'₂` together with the two pushout identities it
satisfies, now supplied by
`Deformation.ToposThickening.MorphismOfFirstOrderThickenings.PushoutExtensionData.comparisonMap`
(`StacksFrontier/Deformation/ToposThickening/ExtensionPushout.lean`).

## Main definitions

* `Deformation.ToposThickening.FirstOrderThickeningComplex.coefficientPushoutData`: the data of
  Stacks 08MJ at the coefficient modules of Situation 08VX — kernel modules `I₂ ⊗_O ℱ` and
  `I₁ ⊗_O ℱ`, action maps `1`, and `(I₂ ⟶ I₁) ⊗ ℱ` on kernel modules.
* `Deformation.ToposThickening.FirstOrderThickeningComplex.coefficientExtensionOne`: the module
  `h^*ℱ'₂`, as the extension of `ℱ` by `I₁ ⊗_O ℱ` over `O'₁` that Stacks 08MJ produces from
  `ℱ'₂`.

## Main results

* `Deformation.ToposThickening.FirstOrderThickeningComplex.f_comp_coefficientComparisonMap` and
  `.coefficientComparisonMap_comp_g`: the canonical map `ℱ'₂ ⟶ h^*ℱ'₂` is `(I₂ ⟶ I₁) ⊗ ℱ` on
  kernel modules and the identity on `ℱ`, which is the pushout square of Stacks 08MJ.
* `Deformation.ToposThickening.FirstOrderThickeningComplex`
  `.boundary_underlyingExtensionClass_eq_obstruction_pushout`: **Stacks 08VY** at `π^*ℱ` and
  `h^*ℱ'₂`.

## Implementation notes

The readings of the two lifts are the ones under which the library states Stacks 08MI, 08MJ and
08MM, and they are the source's own identifications:

* `π^*ℱ` is the trivial extension `ℱ ⊕ (I₁ ⊗_O ℱ)` of Stacks 08MI attached to the canonical
  splitting `π`, since that splitting makes `O'₁ = O ⊕ I₁` as an `O`-algebra and hence
  `π^*ℱ = O'₁ ⊗_O ℱ`.
* `h^*ℱ'₂ = ℱ'₂ ⊗_{O'₂} O'₁` is the extension of Stacks 08MJ produced from `ℱ'₂`, whose middle
  term is the pushout `ℱ'₂ ⊔_{I₂ ⊗ ℱ} (I₁ ⊗ ℱ)` with the `O'₁`-module structure descended along
  `O'₂ ⋉ I₁ ⟶ O'₁`.

Two things are inherited from the general form and are not repaired here. The coefficient
modules are written through the defining ideals `Iₖ` rather than as `f^*𝒥ₖ`, the comparison
being an isomorphism by Stacks 08MQ; this is the reading under which the library states
Stacks 08VW and Stacks 0CYE, so the obstruction class below is the class those tags are about.
And the one consequence of Stacks 08MQ that the proof still consumes is carried as the hypothesis
`hMQ`, stated with 08MQ's own hypotheses as antecedents, since Stacks 08MQ
is not in the library; see the scope section of
`StacksFrontier/Deformation/ToposThickening/FlatThickeningBoundary.lean`. Three others are no longer
hypotheses: the identification `I = f^*J` of Situation 08VV is proved without 08MQ by
`Deformation.ToposThickening.isIdealComparisonIsoOfFlat`, the third column's flat-lift
dictionary is proved by `Deformation.ToposThickening.isFlatLiftCorrespondence`, and the first
column's flatness criterion by
`Deformation.ToposThickening.isFlatOfFixedActionIdentity`; the last two are supplied here
through `Deformation.ToposThickening.FirstOrderThickeningComplex`
`.boundary_underlyingExtensionClass_eq_obstruction'`.

The construction of the `O'₁`-module structure on the pushout narrows the universe of sections
to `max v₂ u₂` (see the implementation notes of
`StacksFrontier/Deformation/ToposThickening/ExtensionPushout.lean`), so the instantiation is stated
at that universe; the base ringed topos is unconstrained, as are the two bases of the lower row.

## References

* [Stacks Project, Tag 08VY](https://stacks.math.columbia.edu/tag/08VY)
* [Stacks Project, Tag 08VX](https://stacks.math.columbia.edu/tag/08VX)
* [Stacks Project, Tag 08VW](https://stacks.math.columbia.edu/tag/08VW)
* [Stacks Project, Tag 08MM](https://stacks.math.columbia.edu/tag/08MM)
* [Stacks Project, Tag 08MJ](https://stacks.math.columbia.edu/tag/08MJ)
* [Stacks Project, Tag 08MI](https://stacks.math.columbia.edu/tag/08MI)
* [Stacks Project, Tag 08MQ](https://stacks.math.columbia.edu/tag/08MQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor)

universe v u v₂ u₂ vB uB wB vB' uB' wB' e

namespace Deformation.ToposThickening

variable {X : RingedTopos.{v, u, max v₂ u₂}} {Y : RingedTopos.{v₂, u₂, max v₂ u₂}}
  {B : RingedTopos.{vB, uB, wB}} {B' : RingedTopos.{vB', uB', wB'}}
  [X.J.HasSheafCompose (forget RingCat.{max v₂ u₂})]
  [Y.J.HasSheafCompose (forget RingCat.{max v₂ u₂})]
  [B.J.HasSheafCompose (forget RingCat.{wB})] [B'.J.HasSheafCompose (forget RingCat.{wB'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{max v₂ u₂} RingCat.{max v₂ u₂})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{max v₂ u₂} RingCat.{max v₂ u₂})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{wB} RingCat.{wB})]
  [B'.J.HasSheafCompose (forget₂ CommRingCat.{wB'} RingCat.{wB'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{max v₂ u₂})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{max v₂ u₂})]
  [B.J.HasSheafCompose (forget AddCommGrpCat.{wB})]
  [B'.J.HasSheafCompose (forget AddCommGrpCat.{wB'})]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{max v₂ u₂}]
  [HasSheafify Y.J AddCommGrpCat.{max v₂ u₂}] [HasWeakSheafify Y.J AddCommGrpCat.{max v₂ u₂}]
  {i : RingedToposHom X Y} {t : RingedToposHom B B'}

namespace FirstOrderThickeningComplex

variable (S : FirstOrderThickeningComplex i)
  (F : SheafOfModules.{max v₂ u₂} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i)))

/-- The data of Stacks 08MJ at the coefficient modules of Situation 08VX: the kernel modules are
`I₂ ⊗_O ℱ` and `I₁ ⊗_O ℱ`, the two prescribed action maps are the identity — the normalization
in which the obstruction class of Stacks 08VW and the class `ξ` of Stacks 08MI are read — and
the map of kernel modules is `(I₂ ⟶ I₁) ⊗ ℱ`. -/
noncomputable def coefficientPushoutData : S.lower.PushoutExtensionData :=
  S.lower.pushoutDataOfPushout
    (𝟙 (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).obj S.lower.second.I).obj F))
    (𝟙 (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).obj S.lower.first.I).obj F))
    (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).map S.lower.idealMap).app F)
    (by rw [Category.id_comp, Category.comp_id])

variable (E₂ : Abelian.YonedaExtension
    ((structureRestrict (reshapeHom i S.lower.O₂ S.lower.fSharp₂)).obj F)
    ((structureRestrict (reshapeHom i S.lower.O₂ S.lower.fSharp₂)).obj
      (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).obj S.lower.second.I))
          0)
  (hE₂ : (extensionActionMap S.lower.second E₂).1 =
    𝟙 (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).obj S.lower.second.I))

/-- **The module `h^*ℱ'₂`**: the extension of `ℱ` by `I₁ ⊗_O ℱ` over `O'₁` that the
functoriality of Stacks 08MJ produces from `ℱ'₂`, whose middle term is the pushout
`ℱ'₂ ⊔_{I₂ ⊗ ℱ} (I₁ ⊗ ℱ) = ℱ'₂ ⊗_{O'₂} O'₁`. Its canonical action map is the identity by
`Deformation.ToposThickening.MorphismOfFirstOrderThickenings.PushoutExtensionData`
`.extensionOne_actionMap`. -/
noncomputable def coefficientExtensionOne :
    Abelian.YonedaExtension ((structureRestrict i).obj F)
      ((structureRestrict i).obj (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj
          F).obj S.lower.first.I)) 0 :=
  (S.coefficientPushoutData F).extensionOne E₂ hE₂

/-- **The canonical map `ℱ'₂ ⟶ h^*ℱ'₂`** of Stacks 08MJ, read over `O'₂` along `h^♯`. -/
noncomputable def coefficientComparisonMap :
    E₂.Z.left ⟶ (S.lower.restrictedExtension (S.coefficientExtensionOne F E₂ hE₂)).Z.left :=
  (S.coefficientPushoutData F).comparisonMap E₂ hE₂

omit [X.J.HasSheafCompose (forget AddCommGrpCat)] [Y.J.HasSheafCompose (forget AddCommGrpCat)] in
/-- The canonical map `ℱ'₂ ⟶ h^*ℱ'₂` is `(I₂ ⟶ I₁) ⊗ ℱ` on kernel modules. -/
lemma f_comp_coefficientComparisonMap :
    E₂.f ≫ S.coefficientComparisonMap F E₂ hE₂ =
      (structureRestrict (reshapeHom i S.lower.O₂ S.lower.fSharp₂)).map
          (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).map S.idealMap₂₁) ≫
        (S.lower.restrictedExtension (S.coefficientExtensionOne F E₂ hE₂)).f := by
  ext U k
  exact (S.coefficientPushoutData F).comparisonSection_f E₂ hE₂ U k

omit [X.J.HasSheafCompose (forget AddCommGrpCat)] [Y.J.HasSheafCompose (forget AddCommGrpCat)] in
/-- The canonical map `ℱ'₂ ⟶ h^*ℱ'₂` is the identity on `ℱ`. -/
lemma coefficientComparisonMap_comp_g :
    S.coefficientComparisonMap F E₂ hE₂ ≫
        (S.lower.restrictedExtension (S.coefficientExtensionOne F E₂ hE₂)).g =
      E₂.g := by
  ext U x
  exact (S.coefficientPushoutData F).extQuotOne_comparisonSection E₂ hE₂ U x

section Situation

variable (T : FirstOrderThickeningComplex t) (f : RingedToposHom X B)
  (f₁ : RingedToposHom Y B') (f₂ : RingedToposHom (reshape Y S.lower.O₂)
    (reshape B' T.lower.O₂)) (f₃ : RingedToposHom (reshape Y S.O₃) (reshape B' T.O₃))
  (commf₁ : f₁.comp i = t.comp f)
  (commf₂ : f₂.comp (reshapeHom i S.lower.O₂ S.lower.fSharp₂) =
    (reshapeHom t T.lower.O₂ T.lower.fSharp₂).comp f)
  (commf₃ : f₃.comp S.thirdHom = T.thirdHom.comp f)

/-- **Stacks Project, Tag 08VY.** In Situation 08VX the modules `π^*ℱ` and `h^*ℱ'₂` are
`O'₁`-modules flat over `O_{ℬ'₁}` restricting to `ℱ` on `(Sh(C), O)`. Their difference
(Stacks 08VW) is an element `θ` of `Ext¹_O(ℱ, f^*𝒥₁ ⊗_O ℱ)` whose boundary in
`Ext²_O(ℱ, f^*𝒥₃ ⊗_O ℱ)` equals the obstruction (Stacks 08VW) to lifting `ℱ` to an `O'₃`-module
flat over `O_{ℬ'₃}`.

This is
`Deformation.ToposThickening.FirstOrderThickeningComplex`
`.boundary_underlyingExtensionClass_eq_obstruction'` at the two lifts of the source: `π^*ℱ` is the
trivial extension of Stacks 08MI attached to the canonical splitting `π`, and `h^*ℱ'₂` is the
extension `S.coefficientExtensionOne` that Stacks 08MJ produces from `ℱ'₂`, which receives from
`ℱ'₂` the canonical map `S.coefficientComparisonMap` satisfying the pushout identities. The
seven clauses of the conclusion are, in order: the canonical action map of `h^*ℱ'₂` and of
`π^*ℱ` is the identity, so the kernel of each of `h^*ℱ'₂ ⟶ ℱ` and `π^*ℱ ⟶ ℱ` is
`I₁ ⊗_O ℱ = f^*𝒥₁ ⊗_O ℱ` and each restricts to `ℱ`; each of `π^*ℱ` and `h^*ℱ'₂` is flat over
`O_{ℬ'₁}`; the class `θ = ξ_{h^*ℱ'₂}` is the difference of the two lifts under the bijection
`ℱ' ↦ ξ_{ℱ'}` of Stacks 08MI; the obstruction class is, by Stacks 08VW for the third column, the
obstruction to lifting `ℱ` to an `O'₃`-module flat over `O_{ℬ'₃}`; and the boundary of `θ` for
the coefficient sequence equals that obstruction class.

See the implementation notes for the two readings inherited from the general form: the
coefficient modules are written through the ideals `Iₖ`, which are `f^*𝒥ₖ` by Stacks 08MQ, and
every consequence of Stacks 08MQ that the proof consumes is now supplied rather than
assumed: this statement carries no stand-in hypothesis. -/
@[stacks 08VY "the tag's own statement, at the two lifts the source names: the trivial \
extension of 08MI for π^*ℱ and the 08MJ pushout of ℱ'₂ for h^*ℱ'₂. UNCONDITIONAL on Stacks \
08MQ: this declaration assumes none of 08MQ's consequences. All of them that it needs are \
proved and supplied -- `IsIdealTensorShortExact` by \
`FirstOrderThickeningComplex.isIdealTensorShortExact`, `IsFlatOfFixedActionIdentity` by \
`isFlatOfFixedActionIdentity`, `IsFlatLiftCorrespondence` by `isFlatLiftCorrespondence`, and \
`IsIdealComparisonIsoOfFlat` by `isIdealComparisonIsoOfFlat`. `IsIdealTensorShortExact` was \
FALSE as first stated -- refuted -- and is repaired \
with Situation 08VX's two horizontal squares, which its proof consumes twice each. The general \
form `boundary_underlyingExtensionClass_eq_obstruction` in `FlatThickeningBoundary.lean` still \
carries the binders, because the producer's module imports that file and discharging there \
would cycle; coefficients are written through the ideals Iₖ, which are f^*𝒥ₖ by 08MQ."]
theorem boundary_underlyingExtensionClass_eq_obstruction_pushout
    [HasExt.{e} (SheafOfModules.{max v₂ u₂} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i)))]
    [HasExt.{e} (SheafOfModules.{max v₂ u₂} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
    [HasExt.{e} (SheafOfModules.{max v₂ u₂} (Stacks.SheafOfModules.Tensor.ringSheaf S.O₃))]
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
    (hF : IsFlatOverBase i f F) :
    (extensionActionMap S.lower.first (S.coefficientExtensionOne F E₂ hE₂)).1 =
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
            ((sheafCompose Y.J (forget₂ CommRingCat.{max v₂ u₂} RingCat.{max v₂ u₂})).map
              f₁.fSharpInverseImage)).obj
            (trivialExtension S.lower.first π F
              (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).obj
                  S.lower.first.I)
              (𝟙 (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).obj
                  S.lower.first.I))).Z.left) ∧
      AlgebraicGeometry.SheafOfModules.IsFlat
          ((SheafOfModules.restrictScalars
            ((sheafCompose Y.J (forget₂ CommRingCat.{max v₂ u₂} RingCat.{max v₂ u₂})).map
              f₁.fSharpInverseImage)).obj (S.coefficientExtensionOne F E₂ hE₂).Z.left) ∧
      underlyingExtensionClass.{e} i S.lower.first π F
            (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).obj
                S.lower.first.I)
            (S.coefficientExtensionOne F E₂ hE₂) =
          splitRestrictionExtHom.{e} S.lower.first π F
              (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).obj
                  S.lower.first.I)
              (extensionClass.{_, _, _, _, _, _, e} F
                (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).obj
                    S.lower.first.I)
                (S.coefficientExtensionOne F E₂ hE₂)) -
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
                S.lower.first.I)
            (S.coefficientExtensionOne F E₂ hE₂)).comp
          (S.isIdealTensorShortExact T hS f f₁ f₂ f₃ commf₁ commf₂ commf₃ F
            hT hTSE hF hstrict₁ hstrict₂ hstrict₃ hf₁ hf₂ hf₃ commh commh₃₂).extClass
          (by decide) =
        existenceObstructionClass S.third F
          (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).obj S.third.I)
          (𝟙 (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).obj
            S.third.I)) :=
  S.boundary_underlyingExtensionClass_eq_obstruction' T f f₁ f₂ f₃ commf₁ commf₂ commf₃ F
    hS hT hTSE π hπ hstrict₁ hstrict₂ hstrict₃ hf₁ hf₂ hf₃ commh commh₃₂ hF E₂ hE₂
    (S.coefficientExtensionOne F E₂ hE₂) (S.coefficientComparisonMap F E₂ hE₂)
    (S.f_comp_coefficientComparisonMap F E₂ hE₂) (S.coefficientComparisonMap_comp_g F E₂ hE₂)

end Situation

end FirstOrderThickeningComplex

end Deformation.ToposThickening

end
