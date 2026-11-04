module

public import StacksFrontier.Deformation.ToposThickening.FlatThickeningComplexBaseIdealNaturality
public import StacksFrontier.Deformation.ToposThickening.FlatThickeningComplexTrivialLift
public import StacksFrontier.Deformation.ToposThickening.FlatThickeningFlatLifts
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 08VY

In Situation **Stacks 08VX** the modules `π^*ℱ` and `h^*ℱ'₂` are `O'₁`-modules flat over
`O_{ℬ'₁}` restricting to `ℱ` on `(Sh(C), O)`. Their difference (**Stacks 08VW**) is an element
`θ` of `Ext¹_O(ℱ, f^*𝒥₁ ⊗_O ℱ)` whose boundary in `Ext²_O(ℱ, f^*𝒥₃ ⊗_O ℱ)` equals the
obstruction (**Stacks 08VW**) to lifting `ℱ` to an `O'₃`-module flat over `O_{ℬ'₃}`.

The situation is `Deformation.ToposThickening.FlatThickeningComplexSituation`, in the one-site
presentation of the deformation theory of modules over thickenings of ringed topoi (Remark
Stacks 08MM, Stacks 08MU, Stacks 08VW).

## Main definitions

* `Deformation.ToposThickening.FlatThickeningComplexSituation.baseIdealMap₃₂`,
  `.baseIdealMap₂₁`: the maps `f^*𝒥₃ ⟶ f^*𝒥₂ ⟶ f^*𝒥₁`, the maps `I₃ ⟶ I₂ ⟶ I₁` of the upper row
  read through the identifications `f^*𝒥ₖ = Iₖ` of Situation 08VV for the three columns
  (`Deformation.ToposThickening.basePullbackIdealIsoIdeal`).
* `Deformation.ToposThickening.FlatThickeningComplexSituation.inducedBaseIdealMap₃₂`,
  `.inducedBaseIdealMap₂₁`: the maps `f^*𝒥₃ ⟶ f^*𝒥₂ ⟶ f^*𝒥₁` induced by the maps
  `𝒥₃ ⟶ 𝒥₂ ⟶ 𝒥₁` of the lower row; they agree with the previous two
  (`.baseIdealMap₃₂_eq_inducedBaseIdealMap₃₂`, `.baseIdealMap₂₁_eq_inducedBaseIdealMap₂₁`).

## Main results

* `Deformation.ToposThickening.FlatThickeningComplexSituation.baseIdealTensor_shortExact`: the
  sequence `0 ⟶ f^*𝒥₃ ⊗_O ℱ ⟶ f^*𝒥₂ ⊗_O ℱ ⟶ f^*𝒥₁ ⊗_O ℱ ⟶ 0` is short exact.
* `.boundary_difference_trivialLift_pulledLift_eq_obstruction`: **Stacks 08VY**, the boundary of
  the difference `θ = [h^*ℱ'₂] - [π^*ℱ]` in `Ext²_O(ℱ, f^*𝒥₃ ⊗_O ℱ)` is the obstruction to
  lifting `ℱ` to an `O'₃`-module flat over `O_{ℬ'₃}`.

## References

* [Stacks Project, Tag 08VY](https://stacks.math.columbia.edu/tag/08VY)
* [Stacks Project, Tag 08VX](https://stacks.math.columbia.edu/tag/08VX)
* [Stacks Project, Tag 08VW](https://stacks.math.columbia.edu/tag/08VW)
* [Stacks Project, Tag 08MM](https://stacks.math.columbia.edu/tag/08MM)
* [Stacks Project, Tag 08MQ](https://stacks.math.columbia.edu/tag/08MQ)
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
  [HasWeakSheafify B.J AddCommGrpCat.{wB}] [B.J.WEqualsLocallyBijective AddCommGrpCat.{wB}]
  {i : RingedToposHom X Y} {t : RingedToposHom B B'}

namespace FlatThickeningComplexSituation

variable (D : FlatThickeningComplexSituation i t)

/-! ### The coefficient sequence `0 ⟶ f^*𝒥₃ ⊗ ℱ ⟶ f^*𝒥₂ ⊗ ℱ ⟶ f^*𝒥₁ ⊗ ℱ ⟶ 0` -/

/-- The identification `f^*𝒥₁ = I₁` of the first column (Situation 08VV). -/
noncomputable abbrev baseIdealIso₁ :
    basePullbackIdealOverThickened i t D.f D.lower.lower.first ≅ D.upper.lower.first.I :=
  basePullbackIdealIsoIdeal i t D.f D.f₁ D.upper.lower.first D.lower.lower.first D.restrict₁
    D.flat₁ D.strict₁

/-- The identification `f^*𝒥₂ = I₂` of the second column (Situation 08VV). -/
noncomputable abbrev baseIdealIso₂ :
    basePullbackIdealOverThickened D.i₂ D.t₂ D.f D.lower.lower.second ≅ D.upper.lower.second.I :=
  basePullbackIdealIsoIdeal D.i₂ D.t₂ D.f D.f₂ D.upper.lower.second D.lower.lower.second
    D.restrict₂ D.flat₂ D.strict₂

/-- The identification `f^*𝒥₃ = I₃` of the third column (Situation 08VV). -/
noncomputable abbrev baseIdealIso₃ :
    basePullbackIdealOverThickened D.upper.thirdHom D.lower.thirdHom D.f D.lower.third ≅
      D.upper.third.I :=
  basePullbackIdealIsoIdeal D.upper.thirdHom D.lower.thirdHom D.f D.f₃ D.upper.third D.lower.third
    D.restrict₃ D.flat₃ D.strict₃

/-- **The map `f^*𝒥₃ ⟶ f^*𝒥₂`**, the map `I₃ ⟶ I₂` of the upper row through the identifications
`f^*𝒥ₖ = Iₖ`. -/
noncomputable def baseIdealMap₃₂ :
    basePullbackIdealOverThickened D.upper.thirdHom D.lower.thirdHom D.f D.lower.third ⟶
      basePullbackIdealOverThickened D.i₂ D.t₂ D.f D.lower.lower.second :=
  homThroughIsos D.baseIdealIso₃ D.upper.idealMap₃₂ D.baseIdealIso₂

/-- **The map `f^*𝒥₂ ⟶ f^*𝒥₁`**, the map `I₂ ⟶ I₁` of the upper row through the identifications
`f^*𝒥ₖ = Iₖ`. -/
noncomputable def baseIdealMap₂₁ :
    basePullbackIdealOverThickened D.i₂ D.t₂ D.f D.lower.lower.second ⟶
      basePullbackIdealOverThickened i t D.f D.lower.lower.first :=
  homThroughIsos D.baseIdealIso₂ D.upper.idealMap₂₁ D.baseIdealIso₁

/-- **The map `f^*𝒥₂ ⟶ f^*𝒥₁` induced by the lower row**: `f^*` of the map `t₂^*𝒥₂ ⟶ t^*𝒥₁`
induced by `𝒥₂ ⟶ 𝒥₁` (`Deformation.ToposThickening.basePullbackIdealOverThickenedMap`). -/
noncomputable def inducedBaseIdealMap₂₁ :
    basePullbackIdealOverThickened D.i₂ D.t₂ D.f D.lower.lower.second ⟶
      basePullbackIdealOverThickened i t D.f D.lower.lower.first :=
  basePullbackIdealOverThickenedMap i D.lower.lower D.f

/-- **The map `f^*𝒥₃ ⟶ f^*𝒥₂` induced by the lower row**: `f^*` of the map `t₃^*𝒥₃ ⟶ t₂^*𝒥₂`
induced by `𝒥₃ ⟶ 𝒥₂` (`Deformation.ToposThickening.basePullbackIdealOverThickenedMap`). -/
noncomputable def inducedBaseIdealMap₃₂ :
    basePullbackIdealOverThickened D.upper.thirdHom D.lower.thirdHom D.f D.lower.third ⟶
      basePullbackIdealOverThickened D.i₂ D.t₂ D.f D.lower.lower.second :=
  basePullbackIdealOverThickenedMap D.i₂ D.lower.upper D.f

/-- **The map `f^*𝒥₂ ⟶ f^*𝒥₁` is induced by `𝒥₂ ⟶ 𝒥₁`**: through the identifications
`f^*𝒥ₖ = Iₖ`, the map `I₂ ⟶ I₁` of the upper row is the map induced by the lower row, as Stacks
08VT does on ringed spaces. -/
theorem baseIdealMap₂₁_eq_inducedBaseIdealMap₂₁ :
    D.baseIdealMap₂₁ = D.inducedBaseIdealMap₂₁ :=
  homThroughIsos_basePullbackIdealIsoIdeal_idealMap D.upper.lower D.lower.lower D.f D.f₂
    D.restrict₂ D.flat₂ D.strict₂ D.f₁ D.comm₁₂ D.restrict₁ D.flat₁ D.strict₁

/-- **The map `f^*𝒥₃ ⟶ f^*𝒥₂` is induced by `𝒥₃ ⟶ 𝒥₂`**: through the identifications
`f^*𝒥ₖ = Iₖ`, the map `I₃ ⟶ I₂` of the upper row is the map induced by the lower row. -/
theorem baseIdealMap₃₂_eq_inducedBaseIdealMap₃₂ :
    D.baseIdealMap₃₂ = D.inducedBaseIdealMap₃₂ :=
  homThroughIsos_basePullbackIdealIsoIdeal_idealMap D.upper.upper D.lower.upper D.f D.f₃
    D.restrict₃ D.flat₃ D.strict₃ D.f₂ D.comm₂₃ D.restrict₂ D.flat₂ D.strict₂

/-- The coefficient sequence is a complex. -/
theorem baseIdealTensor_comp_eq_zero :
    ((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj D.F).map D.baseIdealMap₃₂ ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj D.F).map
          D.baseIdealMap₂₁ = 0 := by
  rw [← CategoryTheory.Functor.map_comp]
  have h : D.baseIdealMap₃₂ ≫ D.baseIdealMap₂₁ = 0 := by
    rw [baseIdealMap₃₂, baseIdealMap₂₁, homThroughIsos, homThroughIsos, Category.assoc,
      Category.assoc, Iso.inv_hom_id_assoc,
      ← Category.assoc D.upper.idealMap₃₂, D.upper_isComplex, zero_comp, comp_zero]
  rw [h, CategoryTheory.Functor.map_zero]

/-- The identification of `0 ⟶ I₃ ⊗_O ℱ ⟶ I₂ ⊗_O ℱ ⟶ I₁ ⊗_O ℱ ⟶ 0` with
`0 ⟶ f^*𝒥₃ ⊗_O ℱ ⟶ f^*𝒥₂ ⊗_O ℱ ⟶ f^*𝒥₁ ⊗_O ℱ ⟶ 0` by the identifications `f^*𝒥ₖ = Iₖ` of the
three columns. -/
noncomputable def idealTensorIsoBaseIdealTensor :
    ShortComplex.mk (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj D.F).map
        D.upper.idealMap₃₂)
      (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj D.F).map
        D.upper.idealMap₂₁)
      (D.upper.idealTensor_comp_eq_zero D.upper_isComplex D.F) ≅
    ShortComplex.mk
      (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj D.F).map D.baseIdealMap₃₂)
      (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj D.F).map D.baseIdealMap₂₁)
      D.baseIdealTensor_comp_eq_zero := by
  refine ShortComplex.isoMk
    (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj D.F).mapIso
      D.baseIdealIso₃).symm
    (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj D.F).mapIso
      D.baseIdealIso₂).symm
    (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj D.F).mapIso
      D.baseIdealIso₁).symm ?_ ?_
  · change _ ≫ ((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj D.F).map
        (D.baseIdealIso₃.hom ≫ D.upper.idealMap₃₂ ≫ D.baseIdealIso₂.inv) = _ ≫ _
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, Iso.symm_hom,
      Functor.mapIso_inv, ← Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp, Iso.symm_hom, Functor.mapIso_inv]
  · change _ ≫ ((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj D.F).map
        (D.baseIdealIso₂.hom ≫ D.upper.idealMap₂₁ ≫ D.baseIdealIso₁.inv) = _ ≫ _
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, Iso.symm_hom,
      Functor.mapIso_inv, ← Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp, Iso.symm_hom, Functor.mapIso_inv]

/-- **The sequence `0 ⟶ f^*𝒥₃ ⊗_O ℱ ⟶ f^*𝒥₂ ⊗_O ℱ ⟶ f^*𝒥₁ ⊗_O ℱ ⟶ 0` is short exact**: through
the identifications `f^*𝒥ₖ ⊗_O ℱ = Iₖ ⊗_O ℱ` it is the sequence
`0 ⟶ I₃ ⊗_O ℱ ⟶ I₂ ⊗_O ℱ ⟶ I₁ ⊗_O ℱ ⟶ 0`, which is short exact because the lower row is short
exact, each `f'ₖ` is flat and `ℱ` is flat over `O_ℬ`
(`Deformation.ToposThickening.FlatThickeningComplexSituation.idealTensor_shortExact`). -/
theorem baseIdealTensor_shortExact :
    (ShortComplex.mk
      (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj D.F).map D.baseIdealMap₃₂)
      (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj D.F).map D.baseIdealMap₂₁)
      D.baseIdealTensor_comp_eq_zero).ShortExact :=
  ShortComplex.shortExact_of_iso D.idealTensorIsoBaseIdealTensor D.idealTensor_shortExact

/-! ### Stacks 08VY -/

/-- **Stacks Project, Tag 08VY.** In Situation **Stacks 08VX** — a short exact sequence of first
order thickenings `O'₃ ⟶ O'₂ ⟶ O'₁` of `(Sh(C), O)` over a short exact sequence of first order
thickenings of `(Sh(B), O_ℬ)`, every `(f, f'ₖ)` strict and every `f'ₖ` flat, and an `O'₂`-module
`ℱ'₂` flat over `O_{ℬ'₂}`, with `ℱ = ℱ'₂ ⊗ O` — let `π : (Sh(C'₁), O'₁) ⟶ (Sh(C), O)` be the
canonical splitting of Remark Stacks 08ML.

* `π^*ℱ` and `h^*ℱ'₂` are `O'₁`-modules flat over `O_{ℬ'₁}` (the first two conjuncts) restricting
  to `ℱ` on `(Sh(C), O)`: they are the flat lifts `trivialLift` and `pulledLift` of `ℱ` across the
  first column (the third and fourth conjuncts record their modules), whose maps to `i₁_*ℱ` are
  the canonical identifications (the fifth and sixth conjuncts): for `π^*ℱ = k^*ι_*ℱ`, with
  `π = ι^{-1} ∘ k` the canonical splitting, the transpose under `k^* ⊣ s^*` of `ι_*ℱ = s^*q^*ι_*ℱ`;
  for `h^*ℱ'₂`, the transpose under `h^* ⊣ h_*` of the unit `ℱ'₂ ⟶ i₂_*i₂^*ℱ'₂ = h_*i₁_*ℱ`.
* The maps `f^*𝒥₃ ⟶ f^*𝒥₂ ⟶ f^*𝒥₁` of the coefficient sequence below, defined as the maps
  `I₃ ⟶ I₂ ⟶ I₁` of the upper row read through the identifications `f^*𝒥ₖ = Iₖ`, are the maps
  induced by the maps `𝒥₃ ⟶ 𝒥₂ ⟶ 𝒥₁` of the lower row (the seventh and eighth conjuncts), as in
  Stacks 08VT.
* The isomorphism classes of flat lifts of `ℱ` across the first column form a principal
  homogeneous set under `Ext¹_O(ℱ, f^*𝒥₁ ⊗_O ℱ)` with the action of Stacks 08VW (2)
  (`Deformation.ToposThickening.exists_addTorsor_flatLiftClass_basePullbackIdeal`), and the
  difference `θ = [h^*ℱ'₂] - [π^*ℱ]` has for boundary along
  `0 ⟶ f^*𝒥₃ ⊗_O ℱ ⟶ f^*𝒥₂ ⊗_O ℱ ⟶ f^*𝒥₁ ⊗_O ℱ ⟶ 0` (short exact by
  `baseIdealTensor_shortExact`) the class `o(ℱ, f^*𝒥₃ ⊗_O ℱ, 1)` of Stacks 08VW (1) for the third
  column, which vanishes exactly when `ℱ` lifts to an `O'₃`-module flat over `O_{ℬ'₃}` (the last
  conjunct). -/
@[stacks 08VY]
theorem boundary_difference_trivialLift_pulledLift_eq_obstruction
    [HasExt.{e} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i)))]
    [HasExt.{e} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
    [HasExt.{e} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf D.upper.O₃))] :
    AlgebraicGeometry.SheafOfModules.IsFlat
        ((SheafOfModules.restrictScalars
          ((sheafCompose Y.J (forget₂ CommRingCat.{w} RingCat.{w})).map
            D.f₁.fSharpInverseImage)).obj D.trivialModule) ∧
      AlgebraicGeometry.SheafOfModules.IsFlat
        ((SheafOfModules.restrictScalars
          ((sheafCompose Y.J (forget₂ CommRingCat.{w} RingCat.{w})).map
            D.f₁.fSharpInverseImage)).obj D.pulledModule) ∧
      D.trivialLift.module' = D.trivialModule ∧ D.pulledLift.module' = D.pulledModule ∧
      D.trivialLift.π = D.trivialModuleIsoPullback.hom ≫
        (D.splittingChangeAdjunction.homEquiv _ _).symm
          (splitRestrictionRestrictScalarsIso i D.upper.lower.first D.π D.F).inv ∧
      D.pulledLift.π = (D.adjH.homEquiv _ _).symm
        (D.i₂.pullbackAdjPushforwardModulesViaComparison.unit.app D.F' ≫
          (D.upper.lower.restrictHIso D.F).inv) ∧
      D.baseIdealMap₃₂ = D.inducedBaseIdealMap₃₂ ∧ D.baseIdealMap₂₁ = D.inducedBaseIdealMap₂₁ ∧
      ∃ T : AddTorsor
          (Abelian.Ext.{e} D.F
            (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj D.F).obj
              (basePullbackIdealOverThickened i t D.f D.lower.lower.first)) 1)
          (FlatLiftClass i D.f₁ D.upper.lower.first D.F),
        (∀ (a : Abelian.Ext.{e} D.F
            (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj D.F).obj
              (basePullbackIdealOverThickened i t D.f D.lower.lower.first)) 1)
          (A B : FlatLift i D.f₁ D.upper.lower.first D.F),
          T.vadd a (Quotient.mk (flatLiftSetoid i D.f₁ D.upper.lower.first D.F) A) =
              Quotient.mk (flatLiftSetoid i D.f₁ D.upper.lower.first D.F) B ↔
            extensionClass D.F
                (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj D.F).obj
                  D.upper.lower.first.I)
                (B.fixedActionExtension i t D.f D.f₁ D.upper.lower.first D.lower.lower.first
                  D.restrict₁ D.F D.isStrictPullbackIdealMap₁ D.isFlat_reducedBaseModule₁) =
              (SheafOfModules.restrictScalars (structureRingMap i)).mapExtAddHom D.F
                  (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj D.F).obj
                    D.upper.lower.first.I) 1
                  (a.comp (Abelian.Ext.mk₀
                    (basePullbackIdealTensorIso i t D.f D.f₁ D.upper.lower.first D.lower.lower.first
                      D.restrict₁ D.flat₁ D.strict₁ D.F).hom) (add_zero 1)) +
                extensionClass D.F
                  (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj D.F).obj
                    D.upper.lower.first.I)
                  (A.fixedActionExtension i t D.f D.f₁ D.upper.lower.first D.lower.lower.first
                    D.restrict₁ D.F D.isStrictPullbackIdealMap₁ D.isFlat_reducedBaseModule₁)) ∧
        (@VSub.vsub _ _ T.toVSub
            (Quotient.mk (flatLiftSetoid i D.f₁ D.upper.lower.first D.F) D.pulledLift)
            (Quotient.mk (flatLiftSetoid i D.f₁ D.upper.lower.first D.F) D.trivialLift)).comp
            D.baseIdealTensor_shortExact.extClass (by decide) =
          existenceObstructionClass D.upper.third D.F
            (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj D.F).obj
              (basePullbackIdealOverThickened D.upper.thirdHom D.lower.thirdHom D.f D.lower.third))
            (basePullbackIdealTensorIso D.upper.thirdHom D.lower.thirdHom D.f D.f₃ D.upper.third
              D.lower.third D.restrict₃ D.flat₃ D.strict₃ D.F).inv ∧
        (HasFlatLift D.upper.thirdHom D.f₃ D.upper.third D.F ↔
          existenceObstructionClass D.upper.third D.F
            (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj D.F).obj
              (basePullbackIdealOverThickened D.upper.thirdHom D.lower.thirdHom D.f D.lower.third))
            (basePullbackIdealTensorIso D.upper.thirdHom D.lower.thirdHom D.f D.f₃ D.upper.third
              D.lower.third D.restrict₃ D.flat₃ D.strict₃ D.F).inv = 0) := by
  obtain ⟨T, hT⟩ := exists_addTorsor_flatLiftClass_basePullbackIdeal i t D.f D.f₁
    D.upper.lower.first D.lower.lower.first D.restrict₁ D.F D.strict₁ D.flat₁ D.isFlatOverBase
    ⟨D.trivialLift⟩
  refine ⟨D.trivialLift.isFlat, D.pulledLift.isFlat, rfl, rfl, D.trivialLift_π, D.pulledLift_π,
    D.baseIdealMap₃₂_eq_inducedBaseIdealMap₃₂, D.baseIdealMap₂₁_eq_inducedBaseIdealMap₂₁, T, hT, ?_,
    hasFlatLift_iff_basePullbackIdeal_obstruction_eq_zero D.upper.thirdHom D.lower.thirdHom D.f
      D.f₃ D.upper.third D.lower.third D.restrict₃ D.F D.strict₃ D.flat₃
      D.isFlatOverBase⟩
  let := T
  obtain ⟨-, -, -, -, hξ, -, hbd⟩ := D.upper.boundary_underlyingExtensionClass_eq_obstruction'
    D.lower D.f D.f₁ D.f₂ D.f₃ D.restrict₁ D.restrict₂ D.restrict₃ D.F D.upper_isComplex
    D.lower_isComplex D.lower_shortExact.choose_spec D.π D.π_spec D.strict₁ D.strict₂ D.strict₃
    D.flat₁ D.flat₂ D.flat₃ D.comm₁₂ D.comm₂₃ D.isFlatOverBase D.secondExtension
    D.secondExtension_actionMap D.pushoutDescent D.pushoutInclusion D.f_comp_pushoutInclusion'
    D.pushoutInclusion_comp_g'
  set θ := @VSub.vsub _ _ T.toVSub
    (Quotient.mk (flatLiftSetoid i D.f₁ D.upper.lower.first D.F) D.pulledLift)
    (Quotient.mk (flatLiftSetoid i D.f₁ D.upper.lower.first D.F) D.trivialLift)
  have hsplit := congrArg (splitRestrictionExtHom D.upper.lower.first D.π D.F
    (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj D.F).obj
      D.upper.lower.first.I))
    (D.fixedActionExtensionClass_pulledLift.symm.trans
      (((hT θ D.trivialLift D.pulledLift).1 (vsub_vadd _ _)).trans
        (congrArg (_ + ·) D.fixedActionExtensionClass_trivialLift)))
  rw [map_add, splitRestrictionExtHom_mapExtAddHom] at hsplit
  have hθξ : θ.comp (Abelian.Ext.mk₀
      (basePullbackIdealTensorIso i t D.f D.f₁ D.upper.lower.first D.lower.lower.first
        D.restrict₁ D.flat₁ D.strict₁ D.F).hom) (add_zero 1) =
      underlyingExtensionClass i D.upper.lower.first D.π D.F
        (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj D.F).obj
          D.upper.lower.first.I) D.pushoutDescent := by
    rw [hξ, hsplit]
    exact (add_sub_cancel_right _ _).symm
  have hθ : θ = (underlyingExtensionClass i D.upper.lower.first D.π D.F
      (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj D.F).obj
        D.upper.lower.first.I) D.pushoutDescent).comp (Abelian.Ext.mk₀
      (basePullbackIdealTensorIso i t D.f D.f₁ D.upper.lower.first D.lower.lower.first
        D.restrict₁ D.flat₁ D.strict₁ D.F).inv) (add_zero 1) := by
    rw [← hθξ, Abelian.Ext.comp_assoc_of_third_deg_zero, Abelian.Ext.mk₀_comp_mk₀, Iso.hom_inv_id,
      Abelian.Ext.comp_mk₀_id]
  have hnat := ShortComplex.ShortExact.extClass_naturality D.idealTensor_shortExact
    D.baseIdealTensor_shortExact D.idealTensorIsoBaseIdealTensor.hom
  rw [hθ, Abelian.Ext.comp_assoc_of_second_deg_zero]
  change _ = existenceObstructionClass D.upper.third D.F _
    (𝟙 _ ≫ (basePullbackIdealTensorIso D.upper.thirdHom D.lower.thirdHom D.f D.f₃ D.upper.third
      D.lower.third D.restrict₃ D.flat₃ D.strict₃ D.F).inv)
  rw [existenceObstructionClass_comp]
  exact (congrArg (fun x => (underlyingExtensionClass i D.upper.lower.first D.π D.F
      (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj D.F).obj
        D.upper.lower.first.I) D.pushoutDescent).comp x (by decide)) hnat.symm).trans
    ((Abelian.Ext.comp_assoc_of_third_deg_zero _ _ _ _).symm.trans
      (congrArg (fun y => y.comp (Abelian.Ext.mk₀ (basePullbackIdealTensorIso D.upper.thirdHom
        D.lower.thirdHom D.f D.f₃ D.upper.third D.lower.third D.restrict₃ D.flat₃ D.strict₃
          D.F).inv) (add_zero 2)) hbd))


end FlatThickeningComplexSituation

end Deformation.ToposThickening

end
