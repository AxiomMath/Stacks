module

public import StacksFrontier.Deformation.ToposThickening.FlatLiftClassTorsor
public import StacksFrontier.Deformation.ToposThickening.FlatThickeningBoundaryCorrespondence
public import StacksFrontier.Deformation.ToposThickening.IdealProductSequence
public import StacksFrontier.Deformation.ToposThickening.IdealTensorShortExactness
public import StacksFrontier.Deformation.ToposThickening.ThickeningComplexCanonicalSplitting

/-!
# Short exact sequences of flat thickenings of ringed topoi, on one site

Let `f : (Sh(C), O) ⟶ (Sh(B), O_ℬ)` be a morphism of ringed topoi. Situation **Stacks 08VX**
fixes a commutative diagram

```
  (Sh(C'₁), O'₁)     --h-->  (Sh(C'₂), O'₂)     ------>  (Sh(C'₃), O'₃)
      |                          |                           |
      f'₁                        f'₂                         f'₃
      v                          v                           v
  (Sh(B'₁), O_{ℬ'₁}) ------->  (Sh(B'₂), O_{ℬ'₂}) ------>  (Sh(B'₃), O_{ℬ'₃})
```

in which the upper row is a short exact sequence of first order thickenings of `(Sh(C), O)`, the
lower row is a short exact sequence of first order thickenings of `(Sh(B), O_ℬ)`, each `f'ᵢ`
restricts to `f`, each pair `(f, f'ᵢ)` is a strict morphism of thickenings and each `f'ᵢ` is
flat; together with an `O'₂`-module `ℱ'₂` flat over `O_{ℬ'₂}`. It sets `ℱ = ℱ'₂ ⊗ O` and lets
`π : (Sh(C'₁), O'₁) ⟶ (Sh(C), O)` be the canonical splitting of Remark Stacks 08ML.

This file records the situation in the presentation in which the deformation theory of modules
over thickenings of ringed topoi is developed (Remark Stacks 08MM, Stacks 08MU, Stacks 08VW): a
first order thickening identifies the underlying topoi, so the three thickened structure sheaves
of each row are sheaves of rings on one site, and `O`-modules are modules over `i_*O` on that
site.

## Main definitions

* `Deformation.ToposThickening.FlatThickeningComplexSituation`: **Stacks 08VX**.
* `Deformation.ToposThickening.FlatThickeningComplexSituation.reduction`: the `O`-module
  `ℱ = ℱ'₂ ⊗ O = i₂^*ℱ'₂`.
* `Deformation.ToposThickening.FlatThickeningComplexSituation.F`: `ℱ`, presented on the
  thickened topos as a module over `i_*O`.
* `Deformation.ToposThickening.FlatThickeningComplexSituation.π`: the canonical splitting of
  Remark Stacks 08ML.
* `Deformation.ToposThickening.FlatThickeningComplexSituation.secondLift`: `ℱ'₂` as a flat lift
  of `ℱ` across the middle column.

## Main results

* `Deformation.ToposThickening.FlatThickeningComplexSituation.isFlatOverBase`: `ℱ` is flat over
  `O_ℬ`.

## References

* [Stacks Project, Tag 08VX](https://stacks.math.columbia.edu/tag/08VX)
* [Stacks Project, Tag 08ML](https://stacks.math.columbia.edu/tag/08ML)
* [Stacks Project, Tag 08M9](https://stacks.math.columbia.edu/tag/08M9)
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

/-- **Stacks 08VX.** A short exact sequence of first order thickenings `O'₃ ⟶ O'₂ ⟶ O'₁` of a
ringed topos `(Sh(C), O)`, over a short exact sequence of first order thickenings of a ringed
topos `(Sh(B), O_ℬ)`, by three strict flat deformations `f'₁, f'₂, f'₃` of one morphism
`f : (Sh(C), O) ⟶ (Sh(B), O_ℬ)` compatible with the two rows, together with an `O'₂`-module
`ℱ'₂` flat over `O_{ℬ'₂}`.

The first thickening of each row is `i : (Sh(C), O) ⟶ (Sh(C'₁), O'₁)`, respectively
`t : (Sh(B), O_ℬ) ⟶ (Sh(B'₁), O_{ℬ'₁})`, and the other two are presented on its site, as in
`Deformation.ToposThickening.FirstOrderThickeningComplex`.

Short exactness of each row is that of Stacks 08ML: the maps `I₃ ⟶ I₂ ⟶ I₁` of defining ideals
are the restrictions of the ring maps `O'₃ ⟶ O'₂ ⟶ O'₁`, and `0 ⟶ I₃ ⟶ I₂ ⟶ I₁ ⟶ 0` is a short
exact sequence of `O`-modules, read through the equivalence of topoi of the thickening as
modules over `i_*O` (respectively `t_*O_ℬ`) on the common underlying site. The squares of the
diagram are equalities of morphisms of ringed topoi: the horizontal arrows are the identity on
underlying topoi, so this is the source's identification of the underlying topoi of a
thickening and of its base (Stacks 08M7, `f = f'` on underlying topoi). -/
@[stacks 08VX "the situation: both rows short exact sequences of first order thickenings in the
sense of 08ML (exactness of `0 ⟶ I₃ ⟶ I₂ ⟶ I₁ ⟶ 0` of defining ideals as modules over the
base), each `f'ᵢ` restricting to `f`, each `(f, f'ᵢ)` strict, each `f'ᵢ` flat, and `ℱ'₂` an
`O'₂`-module flat over `O_{ℬ'₂}`"]
structure FlatThickeningComplexSituation (i : RingedToposHom X Y) (t : RingedToposHom B B') where
  /-- The upper row `O'₃ ⟶ O'₂ ⟶ O'₁`, a sequence of first order thickenings of `(Sh(C), O)`. -/
  upper : FirstOrderThickeningComplex i
  /-- The lower row, a sequence of first order thickenings of `(Sh(B), O_ℬ)`. -/
  lower : FirstOrderThickeningComplex t
  /-- The upper row is a short exact sequence of first order thickenings: its ideals form a short
  exact sequence `0 ⟶ I₃ ⟶ I₂ ⟶ I₁ ⟶ 0`. -/
  upper_shortExact :
    ∃ h : upper.IsComplex, (ShortComplex.mk upper.idealMap₃₂ upper.idealMap₂₁ h).ShortExact
  /-- The lower row is a short exact sequence of first order thickenings. -/
  lower_shortExact :
    ∃ h : lower.IsComplex, (ShortComplex.mk lower.idealMap₃₂ lower.idealMap₂₁ h).ShortExact
  /-- The morphism `f : (Sh(C), O) ⟶ (Sh(B), O_ℬ)`. -/
  f : RingedToposHom X B
  /-- The first vertical morphism `f'₁`. -/
  f₁ : RingedToposHom Y B'
  /-- The second vertical morphism `f'₂`. -/
  f₂ : RingedToposHom (reshape Y upper.lower.O₂) (reshape B' lower.lower.O₂)
  /-- The third vertical morphism `f'₃`. -/
  f₃ : RingedToposHom (reshape Y upper.O₃) (reshape B' lower.O₃)
  /-- `f'₁` restricts to `f`. -/
  restrict₁ : f₁.comp i = t.comp f
  /-- `f'₂` restricts to `f`. -/
  restrict₂ : f₂.comp (reshapeHom i upper.lower.O₂ upper.lower.fSharp₂) =
    (reshapeHom t lower.lower.O₂ lower.lower.fSharp₂).comp f
  /-- `f'₃` restricts to `f`. -/
  restrict₃ : f₃.comp upper.thirdHom = lower.thirdHom.comp f
  /-- The left square of the diagram commutes. -/
  comm₁₂ : f₂.comp upper.lowerHorizontalHom = lower.lowerHorizontalHom.comp f₁
  /-- The right square of the diagram commutes. -/
  comm₂₃ : f₃.comp upper.upperHorizontalHom = lower.upperHorizontalHom.comp f₂
  /-- `(f, f'₁)` is a strict morphism of thickenings. -/
  strict₁ : (MorphismOfThickenings.ofFirstOrderThickenings i t f f₁ upper.lower.first
    lower.lower.first restrict₁).IsStrict
  /-- `(f, f'₂)` is a strict morphism of thickenings. -/
  strict₂ : (MorphismOfThickenings.ofFirstOrderThickenings
    (reshapeHom i upper.lower.O₂ upper.lower.fSharp₂) (reshapeHom t lower.lower.O₂
      lower.lower.fSharp₂) f f₂ upper.lower.second lower.lower.second restrict₂).IsStrict
  /-- `(f, f'₃)` is a strict morphism of thickenings. -/
  strict₃ : (MorphismOfThickenings.ofFirstOrderThickenings upper.thirdHom lower.thirdHom f f₃
    upper.third lower.third restrict₃).IsStrict
  /-- `f'₁` is flat. -/
  flat₁ : f₁.IsFlat
  /-- `f'₂` is flat. -/
  flat₂ : f₂.IsFlat
  /-- `f'₃` is flat. -/
  flat₃ : f₃.IsFlat
  /-- The `O'₂`-module `ℱ'₂`. -/
  F' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf upper.lower.O₂)
  /-- `ℱ'₂` is flat over `O_{ℬ'₂}`. -/
  F'_isFlat : AlgebraicGeometry.SheafOfModules.IsFlat
    ((SheafOfModules.restrictScalars
      ((sheafCompose Y.J (forget₂ CommRingCat.{w} RingCat.{w})).map f₂.fSharpInverseImage)).obj F')

section FlatOverBase

open Stacks.SheafOfModules.FlatSquareZero (ringMap)

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify X.J AddCommGrpCat.{w}] in
/-- **A module flat over the base in the reduced presentation is flat over the base.** The
converse of `Deformation.ToposThickening.isFlat_reducedBaseModule_of_isFlatOverBase`: the two
structure maps into `i_*O` differ by the isomorphism
`Deformation.ToposThickening.reducedBaseRingIso` of their sources, and restriction of scalars
along an isomorphism preserves flatness. -/
theorem isFlatOverBase_of_isFlat_reducedBaseModule {X' : RingedTopos.{v₂, u₂, w}}
    {S : RingedTopos.{vB, uB, wB}} {S' : RingedTopos.{vB', uB', wB'}}
    [X'.J.HasSheafCompose (forget RingCat.{w})] [S.J.HasSheafCompose (forget RingCat.{wB})]
    [S'.J.HasSheafCompose (forget RingCat.{wB'})]
    [X'.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [S.J.HasSheafCompose (forget₂ CommRingCat.{wB} RingCat.{wB})]
    [S'.J.HasSheafCompose (forget₂ CommRingCat.{wB'} RingCat.{wB'})]
    [HasWeakSheafify X'.J AddCommGrpCat.{w}] [X'.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (i : RingedToposHom X X') (t : RingedToposHom S S') (f : RingedToposHom X S)
    (f' : RingedToposHom X' S') (hi : FirstOrderThickening i) (ht : FirstOrderThickening t)
    (comm : f'.comp i = t.comp f)
    (F : SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))
    (hF : AlgebraicGeometry.SheafOfModules.IsFlat (reducedBaseModule i t f f' comm F)) :
    IsFlatOverBase i f F := by
  let e := reducedBaseRingIso i t f f' comm hi ht
  have hsplit : reducedBaseModule i t f f' comm F =
      (SheafOfModules.restrictScalars (ringMap e.hom)).obj
        ((SheafOfModules.restrictScalars
          (ringMap ((pushforwardCommRingFunctor i.toToposHom).map f.fSharpInverseImage))).obj F) :=
    (congrArg (fun m ↦ (SheafOfModules.restrictScalars m).obj F)
      ((congrArg (fun z ↦ ringMap z) (reducedBaseRingIso_hom_comp i t f f' comm hi ht).symm).trans
        ((sheafCompose X'.J (forget₂ CommRingCat.{w} RingCat.{w})).map_comp _ _))).trans
    (congrArg (fun G ↦ G.obj F)
      (Stacks.Sheaves.RingedToposModules.restrictScalars_comp (ringMap e.hom)
        (ringMap ((pushforwardCommRingFunctor i.toToposHom).map f.fSharpInverseImage))).symm)
  rw [hsplit] at hF
  have hflat := isFlat_restrictScalars_of_iso e.symm _ hF
  refine AlgebraicGeometry.SheafOfModules.isFlat_of_iso
    (Stacks.SheafOfModules.restrictScalarsSplitIso (ringMap e.inv) (ringMap e.hom) ?_ _) hflat
  exact ((sheafCompose X'.J (forget₂ CommRingCat.{w} RingCat.{w})).map_comp e.inv e.hom).symm.trans
    ((congrArg (sheafCompose X'.J (forget₂ CommRingCat.{w} RingCat.{w})).map e.inv_hom_id).trans
      ((sheafCompose X'.J (forget₂ CommRingCat.{w} RingCat.{w})).map_id _))

end FlatOverBase

namespace FlatThickeningComplexSituation

variable {i : RingedToposHom X Y} {t : RingedToposHom B B'}
  (D : FlatThickeningComplexSituation i t)

/-- The second thickening `i₂ : (Sh(C), O) ⟶ (Sh(C'₂), O'₂)` of the upper row. -/
noncomputable abbrev i₂ : RingedToposHom X (reshape Y D.upper.lower.O₂) :=
  reshapeHom i D.upper.lower.O₂ D.upper.lower.fSharp₂

omit [HasSheafify Y.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasWeakSheafify X.J AddCommGrpCat.{w}] in
/-- The upper row is a complex. -/
theorem upper_isComplex : D.upper.IsComplex := D.upper_shortExact.choose

omit [HasSheafify Y.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasWeakSheafify X.J AddCommGrpCat.{w}] in
/-- The lower row is a complex. -/
theorem lower_isComplex : D.lower.IsComplex := D.lower_shortExact.choose

/-- **The canonical splitting `π : (Sh(C'₁), O'₁) ⟶ (Sh(C), O)` of Remark Stacks 08ML**, the
trivialization of the first thickening of the upper row through which the composite
`(Sh(C'₁), O'₁) ⟶ (Sh(C'₃), O'₃)` factors. -/
@[stacks 08VX "the canonical splitting `π` of the upper row (Remark 08ML)"]
noncomputable def π : Trivialization i := D.upper.canonicalTrivialization D.upper_isComplex

omit [HasSheafify Y.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasWeakSheafify X.J AddCommGrpCat.{w}] in
/-- The canonical splitting is the one the composite of the upper row factors through: the
composite `O'₃ ⟶ O'₂ ⟶ O'₁` is `O'₃ ⟶ O` followed by the splitting `O ⟶ O'₁` of `π`. -/
theorem π_spec :
    D.upper.upper.ringMapH ≫ D.upper.lower.ringMapH =
      D.upper.whole.ringMap₂ ≫ splittingRingHom i D.upper.lower.first D.π :=
  D.upper.upper_ringMapH_comp_lower_ringMapH_eq D.upper_isComplex

/-- **The `O`-module `ℱ = ℱ'₂ ⊗ O` of Stacks 08VX**: the pullback `i₂^*ℱ'₂` of `ℱ'₂` along the
second thickening of the upper row. -/
@[stacks 08VX "the module `ℱ = ℱ'₂ ⊗ O`"]
noncomputable def reduction : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  (pullbackModules D.i₂.toRingedToposModulesHom).obj D.F'

/-- `ℱ` presented on the thickened topos: the direct image `i_*ℱ`, a module over `i_*O`. This is
the form in which `O`-modules enter the deformation theory of
`Deformation.ToposThickening.FlatLift`. -/
noncomputable def F :
    SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i)) :=
  (pushforwardModuleFunctor i.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj
    D.reduction

/-- **`ℱ'₂` as a flat lift of `ℱ` across the middle column**: the module `ℱ'₂`, flat over
`O_{ℬ'₂}`, with the unit `ℱ'₂ ⟶ i₂_*i₂^*ℱ'₂` of the adjunction of Stacks 03D7, whose kernel is the
ideal product `I₂·ℱ'₂` (the sequence of
`Deformation.ToposThickening.idealProductShortComplex`). -/
noncomputable def secondLift : FlatLift D.i₂ D.f₂ D.upper.lower.second D.F where
  module' := D.F'
  π := D.i₂.pullbackAdjPushforwardModulesViaComparison.unit.app D.F'
  idealProduct_comp := idealProductSubmodule_unit_comp_zero D.upper.lower.second D.F'
  isFlat := D.F'_isFlat
  shortExact := idealProductShortComplex_shortExact D.upper.lower.second D.F'

/-- The second thickening of the lower row, `t₂ : (Sh(B), O_ℬ) ⟶ (Sh(B'₂), O_{ℬ'₂})`. -/
noncomputable abbrev t₂ : RingedToposHom B (reshape B' D.lower.lower.O₂) :=
  reshapeHom t D.lower.lower.O₂ D.lower.lower.fSharp₂

omit [HasSheafify Y.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasWeakSheafify X.J AddCommGrpCat.{w}] in
/-- The strictness of the middle column, in the form of Stacks 08MQ's hypotheses. -/
theorem isStrictPullbackIdealMap₂ :
    IsStrictPullbackIdealMap D.i₂ D.t₂ D.f D.f₂ D.upper.lower.second D.lower.lower.second
      D.restrict₂ :=
  (isStrictPullbackIdealMap_iff_isStrict _ _ _ _ _ _ _).mpr D.strict₂

/-- `ℱ` is flat over `O_ℬ` in the reduced presentation of the middle column: the reduction of a
module flat over `O_{ℬ'₂}`, by Stacks 08M4. -/
theorem isFlat_reducedBaseModule₂ :
    AlgebraicGeometry.SheafOfModules.IsFlat
      (reducedBaseModule D.i₂ D.t₂ D.f D.f₂ D.restrict₂ D.F) :=
  ((isFlat_baseModule_iff D.i₂ D.t₂ D.f D.f₂ D.upper.lower.second D.lower.lower.second
    D.restrict₂ D.F D.F' D.secondLift.π D.secondLift.idealProduct_comp
    D.secondLift.shortExact D.isStrictPullbackIdealMap₂).1 D.F'_isFlat).1

/-- **`ℱ` is flat over `O_ℬ`**: as the reduction of `ℱ'₂`, which is flat over `O_{ℬ'₂}`. -/
theorem isFlatOverBase : IsFlatOverBase i D.f D.F :=
  isFlatOverBase_of_isFlat_reducedBaseModule D.i₂ D.t₂ D.f D.f₂ D.upper.lower.second
    D.lower.lower.second D.restrict₂ D.F D.isFlat_reducedBaseModule₂

/-- **The sequence `0 ⟶ I₃ ⊗_O ℱ ⟶ I₂ ⊗_O ℱ ⟶ I₁ ⊗_O ℱ ⟶ 0` is short exact**, by
`Deformation.ToposThickening.FirstOrderThickeningComplex.isIdealTensorShortExact`. -/
theorem idealTensor_shortExact :
    (ShortComplex.mk (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj D.F).map
        D.upper.idealMap₃₂)
      (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj D.F).map
        D.upper.idealMap₂₁)
      (D.upper.idealTensor_comp_eq_zero D.upper_isComplex D.F)).ShortExact :=
  D.upper.isIdealTensorShortExact D.lower D.upper_isComplex D.f D.f₁ D.f₂ D.f₃ D.restrict₁
    D.restrict₂ D.restrict₃ D.F D.lower_isComplex D.lower_shortExact.choose_spec D.isFlatOverBase
    D.strict₁ D.strict₂ D.strict₃ D.flat₁ D.flat₂ D.flat₃ D.comm₁₂ D.comm₂₃

end FlatThickeningComplexSituation

end Deformation.ToposThickening

end
