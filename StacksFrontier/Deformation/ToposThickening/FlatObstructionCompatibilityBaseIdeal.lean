module

public import StacksFrontier.Deformation.ToposThickening.FlatObstructionCompatibility
public import StacksFrontier.Deformation.ToposThickening.FlatThickeningComplexBaseIdealNaturality

/-!
# Compatibility of the flat lifting obstructions under a morphism of thickenings (Stacks 0CYE)

Let `f : (Sh(C), O) ⟶ (Sh(B), O_ℬ)` be a morphism of ringed topoi deformed in two ways by strict
flat first order thickenings, and let the two deformations be related by a morphism of
thickenings, as in Stacks 0CYD:

```
  (Sh(C'₁), O'₁)      --h-->  (Sh(C'₂), O'₂)
      |                           |
      f'₁                         f'₂
      v                           v
  (Sh(B'₁), O_{ℬ'₁})  --k-->  (Sh(B'₂), O_{ℬ'₂})
```

where `h` is a morphism of first order thickenings of `(Sh(C), O)`, `k` one of first order
thickenings of `(Sh(B), O_ℬ)`, each `f'ₖ` restricts to `f`, each `(f, f'ₖ)` is strict and each
`f'ₖ` is flat; and `ℱ` is an `O`-module flat over `O_ℬ`.

Each column carries the obstruction class of Stacks 08VW, the class `o(ℱ, f^*𝒥ₖ ⊗_O ℱ, 1)` of
Stacks 08MF whose vanishing is the existence of a lift of `ℱ` to the `k`-th thickening flat over
the `k`-th thickening of the base, `𝒥ₖ` being the defining ideal of that thickening. Stacks 0CYE
says that the canonical map `Ext²_O(ℱ, f^*𝒥₂ ⊗_O ℱ) ⟶ Ext²_O(ℱ, f^*𝒥₁ ⊗_O ℱ)` carries the class
of the second column to the class of the first.

## Main results

* `Deformation.ToposThickening.MorphismOfFirstOrderThickenings`
  `.existenceObstructionClass_first_basePullbackIdeal` (**Stacks 0CYE**): the map
  `Ext²_O(ℱ, f^*𝒥₂ ⊗_O ℱ) ⟶ Ext²_O(ℱ, f^*𝒥₁ ⊗_O ℱ)` induced by `f^*𝒥₂ ⟶ f^*𝒥₁` carries
  `o(ℱ, f^*𝒥₂ ⊗_O ℱ, 1)` to `o(ℱ, f^*𝒥₁ ⊗_O ℱ, 1)`.

## Implementation notes

The two thickenings of `(Sh(C), O)` are
`Deformation.ToposThickening.MorphismOfFirstOrderThickenings` (the data of Stacks 08MJ: two first
order thickenings presented on one site together with `h^♯ : O'₂ ⟶ O'₁` over `(Sh(C), O)`), and
so are the two thickenings of `(Sh(B), O_ℬ)`, with `k^♯ : O_{ℬ'₂} ⟶ O_{ℬ'₁}`. Presenting each
row on one site is what puts the two `Ext²` groups in one category, as in
`StacksFrontier/Deformation/ToposThickening/ObstructionCompatibility.lean`; it is how the source's
identification of the underlying topoi of a first order thickening is read, and it is the
presentation of Situation 08VX in
`StacksFrontier/Deformation/ToposThickening/FlatThickeningComplexSituation.lean`. The arrows `h`
and `k` of the source are the changes of coefficients
`AlgebraicGeometry.RingedToposHom.coefficientMorphism` along `h^♯` and `k^♯`, and the
commutativity of the square of Situation 0CYD is `f'₂ ∘ h = k ∘ f'₁`.

The class `o(ℱ, f^*𝒥ₖ ⊗_O ℱ, 1)` is read exactly as in Stacks 08VW
(`Deformation.ToposThickening.hasFlatLift_iff_basePullbackIdeal_obstruction_eq_zero`): the class of
Stacks 08MF for the coefficient module `f^*𝒥ₖ ⊗_O ℱ` and the action `Iₖ ⊗_O ℱ ⟶ f^*𝒥ₖ ⊗_O ℱ`
which is the identity under the identification `f^*𝒥ₖ = Iₖ` of Situation 08VV, the inverse of
`Deformation.ToposThickening.basePullbackIdealTensorIso`. The canonical map on `Ext²` is induced
by `f^*𝒥₂ ⟶ f^*𝒥₁`, the pullback along `f` of the map `𝒥₂ ⟶ 𝒥₁` of the lower row
(`Deformation.ToposThickening.basePullbackIdealOverThickenedMap`). The proof is the source's,
Stacks 0CYC; its commutation hypothesis is that under the identifications `f^*𝒥ₖ = Iₖ` the
map `f^*𝒥₂ ⟶ f^*𝒥₁` is the map `I₂ ⟶ I₁` of the upper row, which is
`Deformation.ToposThickening.basePullbackIdealIsoIdeal_hom_comp_idealMap`.

## References

* [Stacks Project, Tag 0CYE](https://stacks.math.columbia.edu/tag/0CYE)
* [Stacks Project, Tag 0CYD](https://stacks.math.columbia.edu/tag/0CYD)
* [Stacks Project, Tag 0CYC](https://stacks.math.columbia.edu/tag/0CYC)
* [Stacks Project, Tag 08VW](https://stacks.math.columbia.edu/tag/08VW)
* [Stacks Project, Tag 08MF](https://stacks.math.columbia.edu/tag/08MF)
* [Stacks Project, Tag 08MJ](https://stacks.math.columbia.edu/tag/08MJ)
* [Stacks Project, Tag 08MQ](https://stacks.math.columbia.edu/tag/08MQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)

universe v u w v₂ u₂ vB uB wB vB' uB' wB' e

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
  [HasWeakSheafify B.J AddCommGrpCat.{wB}] [B.J.WEqualsLocallyBijective AddCommGrpCat.{wB}]
  {i : RingedToposHom X Y} {t : RingedToposHom B B'}

/-- **Stacks 0CYE.** In Situation 0CYD — a morphism `h` of first order thickenings
`(Sh(C), O) ⟶ (Sh(C'₁), O'₁) ⟶ (Sh(C'₂), O'₂)` (the data `U`, with `h^♯ = U.hSharp`), a
morphism `k` of first order thickenings `(Sh(B), O_ℬ) ⟶ (Sh(B'₁), O_{ℬ'₁}) ⟶ (Sh(B'₂), O_{ℬ'₂})`
(the data `E`, with `k^♯ = E.hSharp`), morphisms `f'₁, f'₂` restricting to
`f : (Sh(C), O) ⟶ (Sh(B), O_ℬ)` (`r₁`, `r₂`) with `f'₂ ∘ h = k ∘ f'₁` (`comm`), both pairs
`(f, f'ₖ)` strict (`hs₁`, `hs₂`), both `f'ₖ` flat (`hf₁`, `hf₂`), and an `O`-module `ℱ` flat
over `O_ℬ` (`_hF`) — the obstruction class `o(ℱ, f^*𝒥₂ ⊗_O ℱ, 1)` maps to the obstruction class
`o(ℱ, f^*𝒥₁ ⊗_O ℱ, 1)` under the canonical map
`Ext²_O(ℱ, f^*𝒥₂ ⊗_O ℱ) ⟶ Ext²_O(ℱ, f^*𝒥₁ ⊗_O ℱ)`.

Here `𝒥ₖ` is the defining ideal of the `k`-th thickening of `(Sh(B), O_ℬ)`, the coefficient
module of the `k`-th column is `f^*𝒥ₖ ⊗_O ℱ`
(`Deformation.ToposThickening.basePullbackIdealOverThickened`), the action `1` of the `k`-th
column is the map `Iₖ ⊗_O ℱ ⟶ f^*𝒥ₖ ⊗_O ℱ` that is the identity under the identification
`f^*𝒥ₖ = Iₖ` of Situation 08VV (the inverse of
`Deformation.ToposThickening.basePullbackIdealTensorIso`), exactly as in Stacks 08VW, and the
canonical map is the one induced by `f^*𝒥₂ ⟶ f^*𝒥₁`, the pullback along `f` of the map
`𝒥₂ ⟶ 𝒥₁` of the lower row (`Deformation.ToposThickening.basePullbackIdealOverThickenedMap`).
The two thickenings of each row are presented on one site, as in Stacks 0CYC.

The proof is the source's: Stacks 0CYC at `Kₖ = f^*𝒥ₖ ⊗_O ℱ`, whose commutation hypothesis is
that `I₂ ⟶ I₁` is `f^*𝒥₂ ⟶ f^*𝒥₁` under the identifications `f^*𝒥ₖ = Iₖ`
(`Deformation.ToposThickening.basePullbackIdealIsoIdeal_hom_comp_idealMap`). The flatness of `ℱ`
over `O_ℬ` is part of the source's situation and is not needed for the conclusion. -/
@[stacks 0CYE]
theorem MorphismOfFirstOrderThickenings.existenceObstructionClass_first_basePullbackIdeal
    (U : MorphismOfFirstOrderThickenings i) (E : MorphismOfFirstOrderThickenings t)
    (f : RingedToposHom X B) (f₁ : RingedToposHom Y B')
    (f₂ : RingedToposHom (reshape Y U.O₂) (reshape B' E.O₂))
    (r₁ : f₁.comp i = t.comp f)
    (r₂ : f₂.comp (reshapeHom i U.O₂ U.fSharp₂) = (reshapeHom t E.O₂ E.fSharp₂).comp f)
    (comm : f₂.comp (RingedToposHom.coefficientMorphism (O := U.O₂) (O' := Y.O) Y.J U.hSharp) =
      (RingedToposHom.coefficientMorphism (O := E.O₂) (O' := B'.O) B'.J E.hSharp).comp f₁)
    (hs₁ : (MorphismOfThickenings.ofFirstOrderThickenings i t f f₁ U.first E.first r₁).IsStrict)
    (hs₂ : (MorphismOfThickenings.ofFirstOrderThickenings (reshapeHom i U.O₂ U.fSharp₂)
      (reshapeHom t E.O₂ E.fSharp₂) f f₂ U.second E.second r₂).IsStrict)
    (hf₁ : f₁.IsFlat) (hf₂ : f₂.IsFlat)
    [HasExt.{e} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i)))]
    [HasExt.{e} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
    [HasExt.{e} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf U.O₂))]
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i)))
    (_hF : IsFlatOverBase i f F) :
    existenceObstructionClass U.first F
        (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).obj
          (basePullbackIdealOverThickened i t f E.first))
        (basePullbackIdealTensorIso i t f f₁ U.first E.first r₁ hf₁ hs₁ F).inv =
      (existenceObstructionClass U.second F
          (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).obj
            (basePullbackIdealOverThickened i (reshapeHom t E.O₂ E.fSharp₂) f E.second))
          (basePullbackIdealTensorIso (reshapeHom i U.O₂ U.fSharp₂)
            (reshapeHom t E.O₂ E.fSharp₂) f f₂ U.second E.second r₂ hf₂ hs₂ F).inv).comp
        (Abelian.Ext.mk₀ (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).map
          (basePullbackIdealOverThickenedMap i E f)))
        (add_zero 2) := by
  refine U.existenceObstructionClass_first F _ _ _ _ _ ?_
  have key := congrArg (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).map)
    (basePullbackIdealIsoIdeal_hom_comp_idealMap U E f f₂ r₂ hf₂ hs₂ f₁ comm r₁ hf₁ hs₁)
  simp only [Functor.map_comp] at key
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  exact key.symm

end Deformation.ToposThickening

end
