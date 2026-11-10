module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.ZariskiReadingPullbackTensorMateHeq

/-!
# Naturality squares of the mate in the monoidality chase at the base change of the Zariski reading

This file proves the hypotheses 16 to 19 of
`AlgebraicGeometry.Space.zariskiReadingTensorSquareMateAux`: the naturality of Stacks 03EL for the
reindexing at `T'` at the components of the mate, the comparison of the inverse of Stacks 04M0 at
`T'` with tensor products transposed to the counit, the naturality of Stacks 03EL for the morphism
of represented spaces at the counits, and Stacks 03EL along the two factorizations of the square of
`h`.  As for the hypotheses 12 to 15, each is a general lemma transported one factor at a time.

## Main results

* `AlgebraicGeometry.Space.zariskiReadingTensorSquareMate_16` … `_19`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

universe u

namespace AlgebraicGeometry.Space

open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf (ringedSpaceHom)

attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}


variable {T T' : BigFppfOver B S hS} (h : T' ⟶ T)
variable (N M : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
  (hN : N.IsQuasicoherentOnSite) (hM : M.IsQuasicoherentOnSite)

/-- Hypothesis 16 of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMateAux`: the naturality of
Stacks 03EL for the reindexing at `T'` at the components of the mate, as a term whose type fixes
the spelling of its factors. -/
theorem zariskiReadingTensorSquareMate_16Aux (h₀ : T' ⟶ T)
    (N₀ M₀ : Modules.{u, u} B S hS (yoneda.obj T)
    (isAlgebraicSpace_yoneda B S hS T)) (hN₀ : N₀.IsQuasicoherentOnSite)
    (hM₀ : M₀.IsQuasicoherentOnSite) :
    type_of% (fun a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 =>
          (comp_eq_comp_of_heq (Stacks.SheafOfModules.pullbackTensorIsoTransport_hom_naturality
          (representedReindexHom B S hS T') (representedReindexPullbackIso B S hS T')
          (Adjunction.equivalenceMateApp (representedReindexEquivalenceTopos T)
          (representedReindexEquivalenceTopos T')
          (representedSquareFactorizationIso B S hS h₀
          (relativelyRepresentable_yoneda_map B S hS h₀)).hom N₀)
          (Adjunction.equivalenceMateApp (representedReindexEquivalenceTopos T)
          (representedReindexEquivalenceTopos T')
          (representedSquareFactorizationIso B S hS h₀
          (relativelyRepresentable_yoneda_map B S hS h₀)).hom M₀)) a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 :
          HypothesisOf₂₀_16 (zariskiReadingTensorSquareMateAux h₀ N₀ M₀ hN₀ hM₀))) :=
  fun a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 =>
      (comp_eq_comp_of_heq (Stacks.SheafOfModules.pullbackTensorIsoTransport_hom_naturality
      (representedReindexHom B S hS T') (representedReindexPullbackIso B S hS T')
      (Adjunction.equivalenceMateApp (representedReindexEquivalenceTopos T)
      (representedReindexEquivalenceTopos T')
      (representedSquareFactorizationIso B S hS h₀
      (relativelyRepresentable_yoneda_map B S hS h₀)).hom N₀)
      (Adjunction.equivalenceMateApp (representedReindexEquivalenceTopos T)
      (representedReindexEquivalenceTopos T')
      (representedSquareFactorizationIso B S hS h₀
      (relativelyRepresentable_yoneda_map B S hS h₀)).hom M₀)) a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 :
      HypothesisOf₂₀_16 (zariskiReadingTensorSquareMateAux h₀ N₀ M₀ hN₀ hM₀))

/-- A factor of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMate_16`, as a term whose type
fixes the spelling of its factors. -/
theorem zariskiReadingTensorSquareMate_16_7Aux (h₀ : T' ⟶ T)
    (N₀ M₀ : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hN₀ : N₀.IsQuasicoherentOnSite) (hM₀ : M₀.IsQuasicoherentOnSite) :
    type_of% (fun a1 a2 a3 a4 a5 a6 a7 a8 => (Functor.map_heq_of_heq a1 a2 a3 a4 a5 a6 a7 a8 :
          HypothesisOf₁₀_7 (zariskiReadingTensorSquareMate_16Aux h₀ N₀ M₀ hN₀ hM₀))) :=
  fun a1 a2 a3 a4 a5 a6 a7 a8 => (Functor.map_heq_of_heq a1 a2 a3 a4 a5 a6 a7 a8 :
      HypothesisOf₁₀_7 (zariskiReadingTensorSquareMate_16Aux h₀ N₀ M₀ hN₀ hM₀))

/-- A factor of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMate_16`, as a term whose type
fixes the spelling of its factors. -/
theorem zariskiReadingTensorSquareMate_16_7_8Aux (h₀ : T' ⟶ T)
    (N₀ M₀ : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hN₀ : N₀.IsQuasicoherentOnSite) (hM₀ : M₀.IsQuasicoherentOnSite) :
    type_of% (fun a1 a2 a3 a4 a5 a6 a7 => (comp_heq_of_heq a1 a2 a3 a4 a5 a6 a7 : HypothesisOf₈_8
          (zariskiReadingTensorSquareMate_16_7Aux h₀ N₀ M₀ hN₀ hM₀))) :=
  fun a1 a2 a3 a4 a5 a6 a7 => (comp_heq_of_heq a1 a2 a3 a4 a5 a6 a7 : HypothesisOf₈_8
      (zariskiReadingTensorSquareMate_16_7Aux h₀ N₀ M₀ hN₀ hM₀))

/-- A factor of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMate_16`, as a term whose type
fixes the spelling of its factors. -/
theorem zariskiReadingTensorSquareMate_16_7_8_6Aux (h₀ : T' ⟶ T)
    (N₀ M₀ : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hN₀ : N₀.IsQuasicoherentOnSite) (hM₀ : M₀.IsQuasicoherentOnSite) :
    type_of% (fun a1 a2 a3 a4 a5 a6 a7 a8 => (NatTrans.app_heq_of_heq a1 a2 a3 a4 a5 a6 a7 a8 :
          HypothesisOf₇_6 (zariskiReadingTensorSquareMate_16_7_8Aux h₀ N₀ M₀ hN₀ hM₀))) :=
  fun a1 a2 a3 a4 a5 a6 a7 a8 => (NatTrans.app_heq_of_heq a1 a2 a3 a4 a5 a6 a7 a8 :
      HypothesisOf₇_6 (zariskiReadingTensorSquareMate_16_7_8Aux h₀ N₀ M₀ hN₀ hM₀))

/-- A factor of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMate_16`, as a term whose type
fixes the spelling of its factors. -/
theorem zariskiReadingTensorSquareMate_16_7_8_6_7Aux (h₀ : T' ⟶ T)
    (N₀ M₀ : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hN₀ : N₀.IsQuasicoherentOnSite) (hM₀ : M₀.IsQuasicoherentOnSite) :
    type_of% (fun a1 a2 a3 a4 a5 a6 a7 a8 => (Functor.map_heq_of_heq a1 a2 a3 a4 a5 a6 a7 a8 :
          HypothesisOf₈_7
          (zariskiReadingTensorSquareMate_16_7_8_6Aux h₀ N₀ M₀ hN₀ hM₀))) :=
  fun a1 a2 a3 a4 a5 a6 a7 a8 => (Functor.map_heq_of_heq a1 a2 a3 a4 a5 a6 a7 a8 : HypothesisOf₈_7
      (zariskiReadingTensorSquareMate_16_7_8_6Aux h₀ N₀ M₀ hN₀ hM₀))

/-- A factor of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMate_16`. -/
theorem zariskiReadingTensorSquareMate_16_7_8_6_7 : HypothesisOf₈_7
    (zariskiReadingTensorSquareMate_16_7_8_6Aux h N M hN hM) :=
  by apply zariskiReadingTensorSquareMate_16_7_8_6_7Aux h N M hN hM <;> rfl

/-- A factor of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMate_16`. -/
theorem zariskiReadingTensorSquareMate_16_7_8_6 : HypothesisOf₇_6
    (zariskiReadingTensorSquareMate_16_7_8Aux h N M hN hM) :=
  zariskiReadingTensorSquareMate_16_7_8_6Aux h N M hN hM rfl rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl
      (zariskiReadingTensorSquareMate_16_7_8_6_7 h N M hN hM) HEq.rfl

/-- A factor of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMate_16`, as a term whose type
fixes the spelling of its factors. -/
theorem zariskiReadingTensorSquareMate_16_7_8_7Aux (h₀ : T' ⟶ T)
    (N₀ M₀ : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hN₀ : N₀.IsQuasicoherentOnSite) (hM₀ : M₀.IsQuasicoherentOnSite) :
    type_of% (fun a1 a2 a3 a4 a5 a6 a7 a8 => (Functor.map_heq_of_heq a1 a2 a3 a4 a5 a6 a7 a8 :
          HypothesisOf₇_7
          (zariskiReadingTensorSquareMate_16_7_8Aux h₀ N₀ M₀ hN₀ hM₀))) :=
  fun a1 a2 a3 a4 a5 a6 a7 a8 => (Functor.map_heq_of_heq a1 a2 a3 a4 a5 a6 a7 a8 : HypothesisOf₇_7
      (zariskiReadingTensorSquareMate_16_7_8Aux h₀ N₀ M₀ hN₀ hM₀))

/-- A factor of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMate_16`. -/
theorem zariskiReadingTensorSquareMate_16_7_8_7 : HypothesisOf₇_7
    (zariskiReadingTensorSquareMate_16_7_8Aux h N M hN hM) :=
  by apply zariskiReadingTensorSquareMate_16_7_8_7Aux h N M hN hM <;> rfl

/-- A factor of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMate_16`. -/
theorem zariskiReadingTensorSquareMate_16_7_8 : HypothesisOf₈_8
    (zariskiReadingTensorSquareMate_16_7Aux h N M hN hM) :=
  zariskiReadingTensorSquareMate_16_7_8Aux h N M hN hM rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl
      (zariskiReadingTensorSquareMate_16_7_8_6 h N M hN hM)
      (zariskiReadingTensorSquareMate_16_7_8_7 h N M hN hM)

/-- A factor of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMate_16`. -/
theorem zariskiReadingTensorSquareMate_16_7 : HypothesisOf₁₀_7
    (zariskiReadingTensorSquareMate_16Aux h N M hN hM) :=
  zariskiReadingTensorSquareMate_16_7Aux h N M hN hM rfl rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl
      HEq.rfl (zariskiReadingTensorSquareMate_16_7_8 h N M hN hM)

/-- A factor of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMate_16`, as a term whose type
fixes the spelling of its factors. -/
theorem zariskiReadingTensorSquareMate_16_10Aux (h₀ : T' ⟶ T)
    (N₀ M₀ : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hN₀ : N₀.IsQuasicoherentOnSite) (hM₀ : M₀.IsQuasicoherentOnSite) :
    type_of% (fun a1 a2 a3 a4 a5 a6 a7 => (comp_heq_of_heq a1 a2 a3 a4 a5 a6 a7 : HypothesisOf₁₀_10
          (zariskiReadingTensorSquareMate_16Aux h₀ N₀ M₀ hN₀ hM₀))) :=
  fun a1 a2 a3 a4 a5 a6 a7 => (comp_heq_of_heq a1 a2 a3 a4 a5 a6 a7 : HypothesisOf₁₀_10
      (zariskiReadingTensorSquareMate_16Aux h₀ N₀ M₀ hN₀ hM₀))

/-- A factor of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMate_16`, as a term whose type
fixes the spelling of its factors. -/
theorem zariskiReadingTensorSquareMate_16_10_6Aux (h₀ : T' ⟶ T)
    (N₀ M₀ : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hN₀ : N₀.IsQuasicoherentOnSite) (hM₀ : M₀.IsQuasicoherentOnSite) :
    type_of% (fun a1 a2 a3 a4 a5 a6 a7 a8 => (NatTrans.app_heq_of_heq a1 a2 a3 a4 a5 a6 a7 a8 :
          HypothesisOf₇_6 (zariskiReadingTensorSquareMate_16_10Aux h₀ N₀ M₀ hN₀ hM₀))) :=
  fun a1 a2 a3 a4 a5 a6 a7 a8 => (NatTrans.app_heq_of_heq a1 a2 a3 a4 a5 a6 a7 a8 :
      HypothesisOf₇_6 (zariskiReadingTensorSquareMate_16_10Aux h₀ N₀ M₀ hN₀ hM₀))

/-- A factor of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMate_16`, as a term whose type
fixes the spelling of its factors. -/
theorem zariskiReadingTensorSquareMate_16_10_6_7Aux (h₀ : T' ⟶ T)
    (N₀ M₀ : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hN₀ : N₀.IsQuasicoherentOnSite) (hM₀ : M₀.IsQuasicoherentOnSite) :
    type_of% (fun a1 a2 a3 a4 a5 a6 a7 a8 => (Functor.map_heq_of_heq a1 a2 a3 a4 a5 a6 a7 a8 :
          HypothesisOf₈_7
          (zariskiReadingTensorSquareMate_16_10_6Aux h₀ N₀ M₀ hN₀ hM₀))) :=
  fun a1 a2 a3 a4 a5 a6 a7 a8 => (Functor.map_heq_of_heq a1 a2 a3 a4 a5 a6 a7 a8 : HypothesisOf₈_7
      (zariskiReadingTensorSquareMate_16_10_6Aux h₀ N₀ M₀ hN₀ hM₀))

/-- A factor of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMate_16`. -/
theorem zariskiReadingTensorSquareMate_16_10_6_7 : HypothesisOf₈_7
    (zariskiReadingTensorSquareMate_16_10_6Aux h N M hN hM) :=
  by apply zariskiReadingTensorSquareMate_16_10_6_7Aux h N M hN hM <;> rfl

/-- A factor of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMate_16`. -/
theorem zariskiReadingTensorSquareMate_16_10_6 : HypothesisOf₇_6
    (zariskiReadingTensorSquareMate_16_10Aux h N M hN hM) :=
  zariskiReadingTensorSquareMate_16_10_6Aux h N M hN hM rfl rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl
      (zariskiReadingTensorSquareMate_16_10_6_7 h N M hN hM) HEq.rfl

/-- A factor of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMate_16`, as a term whose type
fixes the spelling of its factors. -/
theorem zariskiReadingTensorSquareMate_16_10_7Aux (h₀ : T' ⟶ T)
    (N₀ M₀ : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hN₀ : N₀.IsQuasicoherentOnSite) (hM₀ : M₀.IsQuasicoherentOnSite) :
    type_of% (fun a1 a2 a3 a4 a5 a6 a7 a8 => (Functor.map_heq_of_heq a1 a2 a3 a4 a5 a6 a7 a8 :
          HypothesisOf₇_7
          (zariskiReadingTensorSquareMate_16_10Aux h₀ N₀ M₀ hN₀ hM₀))) :=
  fun a1 a2 a3 a4 a5 a6 a7 a8 => (Functor.map_heq_of_heq a1 a2 a3 a4 a5 a6 a7 a8 : HypothesisOf₇_7
      (zariskiReadingTensorSquareMate_16_10Aux h₀ N₀ M₀ hN₀ hM₀))

/-- A factor of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMate_16`. -/
theorem zariskiReadingTensorSquareMate_16_10_7 : HypothesisOf₇_7
    (zariskiReadingTensorSquareMate_16_10Aux h N M hN hM) :=
  by apply zariskiReadingTensorSquareMate_16_10_7Aux h N M hN hM <;> rfl

/-- A factor of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMate_16`. -/
theorem zariskiReadingTensorSquareMate_16_10 : HypothesisOf₁₀_10
    (zariskiReadingTensorSquareMate_16Aux h N M hN hM) :=
  zariskiReadingTensorSquareMate_16_10Aux h N M hN hM rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl
      (zariskiReadingTensorSquareMate_16_10_6 h N M hN hM)
      (zariskiReadingTensorSquareMate_16_10_7 h N M hN hM)

/-- Hypothesis 16 of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMateAux`: the naturality of
Stacks 03EL for the reindexing at `T'` at the components of the mate. -/
theorem zariskiReadingTensorSquareMate_16 : HypothesisOf₂₀_16
    (zariskiReadingTensorSquareMateAux h N M hN hM) :=
  zariskiReadingTensorSquareMate_16Aux h N M hN hM rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl
      (zariskiReadingTensorSquareMate_16_7 h N M hN hM) HEq.rfl HEq.rfl
      (zariskiReadingTensorSquareMate_16_10 h N M hN hM)

/-- Hypothesis 17 of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMateAux`: the comparison of
the inverse of Stacks 04M0 at `T'` with tensor products, transposed to the counit, as a term whose
type fixes the spelling of its factors. -/
theorem zariskiReadingTensorSquareMate_17Aux (h₀ : T' ⟶ T)
    (N₀ M₀ : Modules.{u, u} B S hS (yoneda.obj T)
    (isAlgebraicSpace_yoneda B S hS T)) (hN₀ : N₀.IsQuasicoherentOnSite)
    (hM₀ : M₀.IsQuasicoherentOnSite) :
    type_of% (fun a1 a2 a3 a4 a5 a6 a7 a8 =>
          (comp_eq_of_heq (comp_comp_eq_of_eq
          (pullbackTensorIsoTransport_representedReindex_hom_eq T' _ _)
        (Equivalence.functor_map_inverseTensor_comp_counit
            (representedSmallEtaleModuleEquivalence B S hS T')
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
              (representedSchemeCommRingStructureSheaf B S hS T'))
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
              (structureSheaf B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T')))
              ((smallEtaleRingedToposModulesHom B S hS
              (representedSpaceMap B S hS h₀)).pullbackModules.obj N₀)
              ((smallEtaleRingedToposModulesHom B S hS
              (representedSpaceMap B S hS h₀)).pullbackModules.obj M₀)
          (representedSmallEtaleModuleTensorIso B S hS T' _ _))) a1 a2 a3 a4 a5 a6 a7 a8 :
              HypothesisOf₂₀_17 (zariskiReadingTensorSquareMateAux h₀ N₀ M₀ hN₀ hM₀))) :=
  fun a1 a2 a3 a4 a5 a6 a7 a8 =>
      (comp_eq_of_heq (comp_comp_eq_of_eq
      (pullbackTensorIsoTransport_representedReindex_hom_eq T' _ _)
    (Equivalence.functor_map_inverseTensor_comp_counit
        (representedSmallEtaleModuleEquivalence B S hS T')
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (representedSchemeCommRingStructureSheaf B S hS T'))
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (structureSheaf B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T')))
          ((smallEtaleRingedToposModulesHom B S hS
          (representedSpaceMap B S hS h₀)).pullbackModules.obj N₀)
          ((smallEtaleRingedToposModulesHom B S hS
          (representedSpaceMap B S hS h₀)).pullbackModules.obj M₀)
      (representedSmallEtaleModuleTensorIso B S hS T' _ _))) a1 a2 a3 a4 a5 a6 a7 a8 :
          HypothesisOf₂₀_17 (zariskiReadingTensorSquareMateAux h₀ N₀ M₀ hN₀ hM₀))

/-- A factor of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMate_17`, as a term whose type
fixes the spelling of its factors. -/
theorem zariskiReadingTensorSquareMate_17_6Aux (h₀ : T' ⟶ T)
    (N₀ M₀ : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hN₀ : N₀.IsQuasicoherentOnSite) (hM₀ : M₀.IsQuasicoherentOnSite) :
    type_of% (fun a1 a2 a3 a4 a5 a6 a7 a8 => (Functor.map_heq_of_heq a1 a2 a3 a4 a5 a6 a7 a8 :
          HypothesisOf₈_6
          (zariskiReadingTensorSquareMate_17Aux h₀ N₀ M₀ hN₀ hM₀))) :=
  fun a1 a2 a3 a4 a5 a6 a7 a8 => (Functor.map_heq_of_heq a1 a2 a3 a4 a5 a6 a7 a8 : HypothesisOf₈_6
      (zariskiReadingTensorSquareMate_17Aux h₀ N₀ M₀ hN₀ hM₀))

/-- A factor of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMate_17`, as a term whose type
fixes the spelling of its factors. -/
theorem zariskiReadingTensorSquareMate_17_6_8Aux (h₀ : T' ⟶ T)
    (N₀ M₀ : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hN₀ : N₀.IsQuasicoherentOnSite) (hM₀ : M₀.IsQuasicoherentOnSite) :
    type_of% (fun a1 a2 a3 a4 a5 => (Iso.hom_heq_of_heq a1 a2 a3 a4 a5 : HypothesisOf₈_8
          (zariskiReadingTensorSquareMate_17_6Aux h₀ N₀ M₀ hN₀ hM₀))) :=
  fun a1 a2 a3 a4 a5 => (Iso.hom_heq_of_heq a1 a2 a3 a4 a5 : HypothesisOf₈_8
      (zariskiReadingTensorSquareMate_17_6Aux h₀ N₀ M₀ hN₀ hM₀))

/-- A factor of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMate_17`. -/
theorem zariskiReadingTensorSquareMate_17_6_8 : HypothesisOf₈_8
    (zariskiReadingTensorSquareMate_17_6Aux h N M hN hM) :=
  by apply zariskiReadingTensorSquareMate_17_6_8Aux h N M hN hM <;> rfl

/-- A factor of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMate_17`. -/
theorem zariskiReadingTensorSquareMate_17_6 : HypothesisOf₈_6
    (zariskiReadingTensorSquareMate_17Aux h N M hN hM) :=
  zariskiReadingTensorSquareMate_17_6Aux h N M hN hM rfl rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl
      HEq.rfl (zariskiReadingTensorSquareMate_17_6_8 h N M hN hM)

/-- A factor of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMate_17`, as a term whose type
fixes the spelling of its factors. -/
theorem zariskiReadingTensorSquareMate_17_7Aux (h₀ : T' ⟶ T)
    (N₀ M₀ : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hN₀ : N₀.IsQuasicoherentOnSite) (hM₀ : M₀.IsQuasicoherentOnSite) :
    type_of% (fun a1 a2 a3 a4 a5 a6 a7 => (comp_heq_of_heq a1 a2 a3 a4 a5 a6 a7 : HypothesisOf₈_7
          (zariskiReadingTensorSquareMate_17Aux h₀ N₀ M₀ hN₀ hM₀))) :=
  fun a1 a2 a3 a4 a5 a6 a7 => (comp_heq_of_heq a1 a2 a3 a4 a5 a6 a7 : HypothesisOf₈_7
      (zariskiReadingTensorSquareMate_17Aux h₀ N₀ M₀ hN₀ hM₀))

/-- A factor of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMate_17`, as a term whose type
fixes the spelling of its factors. -/
theorem zariskiReadingTensorSquareMate_17_7_6Aux (h₀ : T' ⟶ T)
    (N₀ M₀ : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hN₀ : N₀.IsQuasicoherentOnSite) (hM₀ : M₀.IsQuasicoherentOnSite) :
    type_of% (fun a1 a2 a3 a4 a5 => (Iso.hom_heq_of_heq a1 a2 a3 a4 a5 : HypothesisOf₇_6
          (zariskiReadingTensorSquareMate_17_7Aux h₀ N₀ M₀ hN₀ hM₀))) :=
  fun a1 a2 a3 a4 a5 => (Iso.hom_heq_of_heq a1 a2 a3 a4 a5 : HypothesisOf₇_6
      (zariskiReadingTensorSquareMate_17_7Aux h₀ N₀ M₀ hN₀ hM₀))

/-- A factor of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMate_17`. -/
theorem zariskiReadingTensorSquareMate_17_7_6 : HypothesisOf₇_6
    (zariskiReadingTensorSquareMate_17_7Aux h N M hN hM) :=
  by apply zariskiReadingTensorSquareMate_17_7_6Aux h N M hN hM <;> rfl

/-- A factor of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMate_17`. -/
theorem zariskiReadingTensorSquareMate_17_7 : HypothesisOf₈_7
    (zariskiReadingTensorSquareMate_17Aux h N M hN hM) :=
  zariskiReadingTensorSquareMate_17_7Aux h N M hN hM rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl
      (zariskiReadingTensorSquareMate_17_7_6 h N M hN hM) HEq.rfl

/-- Hypothesis 17 of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMateAux`: the comparison of
the inverse of Stacks 04M0 at `T'` with tensor products, transposed to the counit. -/
theorem zariskiReadingTensorSquareMate_17 : HypothesisOf₂₀_17
    (zariskiReadingTensorSquareMateAux h N M hN hM) :=
  zariskiReadingTensorSquareMate_17Aux h N M hN hM rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl
      (zariskiReadingTensorSquareMate_17_6 h N M hN hM)
      (zariskiReadingTensorSquareMate_17_7 h N M hN hM) HEq.rfl

/-- Hypothesis 18 of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMateAux`: the naturality of
Stacks 03EL for the morphism of represented spaces at the counits, as a term whose type fixes the
spelling of its factors. -/
theorem zariskiReadingTensorSquareMate_18Aux (h₀ : T' ⟶ T)
    (N₀ M₀ : Modules.{u, u} B S hS (yoneda.obj T)
    (isAlgebraicSpace_yoneda B S hS T)) (hN₀ : N₀.IsQuasicoherentOnSite)
    (hM₀ : M₀.IsQuasicoherentOnSite) :
    type_of% (fun a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 =>
          (comp_eq_comp_of_heq (Stacks.SheafOfModules.pullbackTensorIsoTransport_hom_naturality
          (smallEtaleRingedToposModulesHom B S hS (representedSpaceMap B S hS h₀)) (Iso.refl _)
          ((representedReindexEquivalenceTopos T).counit.app N₀)
          ((representedReindexEquivalenceTopos T).counit.app M₀)) a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 :
          HypothesisOf₂₀_18 (zariskiReadingTensorSquareMateAux h₀ N₀ M₀ hN₀ hM₀))) :=
  fun a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 =>
      (comp_eq_comp_of_heq (Stacks.SheafOfModules.pullbackTensorIsoTransport_hom_naturality
      (smallEtaleRingedToposModulesHom B S hS (representedSpaceMap B S hS h₀)) (Iso.refl _)
      ((representedReindexEquivalenceTopos T).counit.app N₀)
      ((representedReindexEquivalenceTopos T).counit.app M₀)) a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 :
      HypothesisOf₂₀_18 (zariskiReadingTensorSquareMateAux h₀ N₀ M₀ hN₀ hM₀))

/-- Hypothesis 18 of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMateAux`: the naturality of
Stacks 03EL for the morphism of represented spaces at the counits. -/
theorem zariskiReadingTensorSquareMate_18 : HypothesisOf₂₀_18
    (zariskiReadingTensorSquareMateAux h N M hN hM) :=
  by apply zariskiReadingTensorSquareMate_18Aux h N M hN hM <;> rfl

/-- Hypothesis 19 of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMateAux`: Stacks 03EL along
the two factorizations of the square of `h`, as a term whose type fixes the spelling of its
factors. -/
theorem zariskiReadingTensorSquareMate_19Aux (h₀ : T' ⟶ T)
    (N₀ M₀ : Modules.{u, u} B S hS (yoneda.obj T)
    (isAlgebraicSpace_yoneda B S hS T)) (hN₀ : N₀.IsQuasicoherentOnSite)
    (hM₀ : M₀.IsQuasicoherentOnSite) :
    type_of% (fun a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 =>
          (comp_eq_comp_of_heq (representedSquare_pullbackTensorIsoTransport B S hS h₀
          (relativelyRepresentable_yoneda_map B S hS h₀)
          ((representedReindexEquivalenceTopos T).inverse.obj N₀)
          ((representedReindexEquivalenceTopos T).inverse.obj M₀)) a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 :
          HypothesisOf₂₀_19 (zariskiReadingTensorSquareMateAux h₀ N₀ M₀ hN₀ hM₀))) :=
  fun a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 =>
      (comp_eq_comp_of_heq (representedSquare_pullbackTensorIsoTransport B S hS h₀
      (relativelyRepresentable_yoneda_map B S hS h₀)
      ((representedReindexEquivalenceTopos T).inverse.obj N₀)
      ((representedReindexEquivalenceTopos T).inverse.obj M₀)) a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 :
      HypothesisOf₂₀_19 (zariskiReadingTensorSquareMateAux h₀ N₀ M₀ hN₀ hM₀))

/-- A factor of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMate_19`, as a term whose type
fixes the spelling of its factors. -/
theorem zariskiReadingTensorSquareMate_19_7Aux (h₀ : T' ⟶ T)
    (N₀ M₀ : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hN₀ : N₀.IsQuasicoherentOnSite) (hM₀ : M₀.IsQuasicoherentOnSite) :
    type_of% (fun a1 a2 a3 a4 a5 a6 a7 a8 => (Functor.map_heq_of_heq a1 a2 a3 a4 a5 a6 a7 a8 :
          HypothesisOf₁₀_7 (zariskiReadingTensorSquareMate_19Aux h₀ N₀ M₀ hN₀ hM₀))) :=
  fun a1 a2 a3 a4 a5 a6 a7 a8 => (Functor.map_heq_of_heq a1 a2 a3 a4 a5 a6 a7 a8 :
      HypothesisOf₁₀_7 (zariskiReadingTensorSquareMate_19Aux h₀ N₀ M₀ hN₀ hM₀))

/-- A factor of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMate_19`. -/
theorem zariskiReadingTensorSquareMate_19_7 : HypothesisOf₁₀_7
    (zariskiReadingTensorSquareMate_19Aux h N M hN hM) :=
  by apply zariskiReadingTensorSquareMate_19_7Aux h N M hN hM <;> rfl

/-- A factor of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMate_19`, as a term whose type
fixes the spelling of its factors. -/
theorem zariskiReadingTensorSquareMate_19_8Aux (h₀ : T' ⟶ T)
    (N₀ M₀ : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hN₀ : N₀.IsQuasicoherentOnSite) (hM₀ : M₀.IsQuasicoherentOnSite) :
    type_of% (fun a1 a2 a3 a4 a5 a6 a7 => (comp_heq_of_heq a1 a2 a3 a4 a5 a6 a7 : HypothesisOf₁₀_8
          (zariskiReadingTensorSquareMate_19Aux h₀ N₀ M₀ hN₀ hM₀))) :=
  fun a1 a2 a3 a4 a5 a6 a7 => (comp_heq_of_heq a1 a2 a3 a4 a5 a6 a7 : HypothesisOf₁₀_8
      (zariskiReadingTensorSquareMate_19Aux h₀ N₀ M₀ hN₀ hM₀))

/-- A factor of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMate_19`, as a term whose type
fixes the spelling of its factors. -/
theorem zariskiReadingTensorSquareMate_19_8_7Aux (h₀ : T' ⟶ T)
    (N₀ M₀ : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hN₀ : N₀.IsQuasicoherentOnSite) (hM₀ : M₀.IsQuasicoherentOnSite) :
    type_of% (fun a1 a2 a3 a4 a5 a6 a7 => (comp_heq_of_heq a1 a2 a3 a4 a5 a6 a7 : HypothesisOf₇_7
          (zariskiReadingTensorSquareMate_19_8Aux h₀ N₀ M₀ hN₀ hM₀))) :=
  fun a1 a2 a3 a4 a5 a6 a7 => (comp_heq_of_heq a1 a2 a3 a4 a5 a6 a7 : HypothesisOf₇_7
      (zariskiReadingTensorSquareMate_19_8Aux h₀ N₀ M₀ hN₀ hM₀))

/-- A factor of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMate_19`, as a term whose type
fixes the spelling of its factors. -/
theorem zariskiReadingTensorSquareMate_19_8_7_6Aux (h₀ : T' ⟶ T)
    (N₀ M₀ : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hN₀ : N₀.IsQuasicoherentOnSite) (hM₀ : M₀.IsQuasicoherentOnSite) :
    type_of% (fun a1 a2 a3 a4 a5 a6 a7 a8 => (NatTrans.app_heq_of_heq a1 a2 a3 a4 a5 a6 a7 a8 :
          HypothesisOf₇_6 (zariskiReadingTensorSquareMate_19_8_7Aux h₀ N₀ M₀ hN₀ hM₀))) :=
  fun a1 a2 a3 a4 a5 a6 a7 a8 => (NatTrans.app_heq_of_heq a1 a2 a3 a4 a5 a6 a7 a8 :
      HypothesisOf₇_6 (zariskiReadingTensorSquareMate_19_8_7Aux h₀ N₀ M₀ hN₀ hM₀))

/-- A factor of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMate_19`, as a term whose type
fixes the spelling of its factors. -/
theorem zariskiReadingTensorSquareMate_19_8_7_6_7Aux (h₀ : T' ⟶ T)
    (N₀ M₀ : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hN₀ : N₀.IsQuasicoherentOnSite) (hM₀ : M₀.IsQuasicoherentOnSite) :
    type_of% (fun a1 a2 a3 a4 a5 a6 a7 a8 => (Functor.map_heq_of_heq a1 a2 a3 a4 a5 a6 a7 a8 :
          HypothesisOf₈_7
          (zariskiReadingTensorSquareMate_19_8_7_6Aux h₀ N₀ M₀ hN₀ hM₀))) :=
  fun a1 a2 a3 a4 a5 a6 a7 a8 => (Functor.map_heq_of_heq a1 a2 a3 a4 a5 a6 a7 a8 : HypothesisOf₈_7
      (zariskiReadingTensorSquareMate_19_8_7_6Aux h₀ N₀ M₀ hN₀ hM₀))

/-- A factor of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMate_19`, as a term whose type
fixes the spelling of its factors. -/
theorem zariskiReadingTensorSquareMate_19_8_7_6_7_8Aux (h₀ : T' ⟶ T)
    (N₀ M₀ : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hN₀ : N₀.IsQuasicoherentOnSite) (hM₀ : M₀.IsQuasicoherentOnSite) :
    type_of% (fun a1 a2 a3 a4 a5 a6 a7 a8 => (NatTrans.app_heq_of_heq a1 a2 a3 a4 a5 a6 a7 a8 :
          HypothesisOf₈_8 (zariskiReadingTensorSquareMate_19_8_7_6_7Aux h₀ N₀ M₀ hN₀ hM₀))) :=
  fun a1 a2 a3 a4 a5 a6 a7 a8 => (NatTrans.app_heq_of_heq a1 a2 a3 a4 a5 a6 a7 a8 :
      HypothesisOf₈_8 (zariskiReadingTensorSquareMate_19_8_7_6_7Aux h₀ N₀ M₀ hN₀ hM₀))

/-- A factor of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMate_19`. -/
theorem zariskiReadingTensorSquareMate_19_8_7_6_7_8 : HypothesisOf₈_8
    (zariskiReadingTensorSquareMate_19_8_7_6_7Aux h N M hN hM) :=
  by apply zariskiReadingTensorSquareMate_19_8_7_6_7_8Aux h N M hN hM <;> rfl

/-- A factor of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMate_19`. -/
theorem zariskiReadingTensorSquareMate_19_8_7_6_7 : HypothesisOf₈_7
    (zariskiReadingTensorSquareMate_19_8_7_6Aux h N M hN hM) :=
  zariskiReadingTensorSquareMate_19_8_7_6_7Aux h N M hN hM rfl rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl
      HEq.rfl (zariskiReadingTensorSquareMate_19_8_7_6_7_8 h N M hN hM)

/-- A factor of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMate_19`. -/
theorem zariskiReadingTensorSquareMate_19_8_7_6 : HypothesisOf₇_6
    (zariskiReadingTensorSquareMate_19_8_7Aux h N M hN hM) :=
  zariskiReadingTensorSquareMate_19_8_7_6Aux h N M hN hM rfl rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl
      (zariskiReadingTensorSquareMate_19_8_7_6_7 h N M hN hM) HEq.rfl

/-- A factor of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMate_19`, as a term whose type
fixes the spelling of its factors. -/
theorem zariskiReadingTensorSquareMate_19_8_7_7Aux (h₀ : T' ⟶ T)
    (N₀ M₀ : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hN₀ : N₀.IsQuasicoherentOnSite) (hM₀ : M₀.IsQuasicoherentOnSite) :
    type_of% (fun a1 a2 a3 a4 a5 a6 a7 a8 => (Functor.map_heq_of_heq a1 a2 a3 a4 a5 a6 a7 a8 :
          HypothesisOf₇_7
          (zariskiReadingTensorSquareMate_19_8_7Aux h₀ N₀ M₀ hN₀ hM₀))) :=
  fun a1 a2 a3 a4 a5 a6 a7 a8 => (Functor.map_heq_of_heq a1 a2 a3 a4 a5 a6 a7 a8 : HypothesisOf₇_7
      (zariskiReadingTensorSquareMate_19_8_7Aux h₀ N₀ M₀ hN₀ hM₀))

/-- A factor of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMate_19`, as a term whose type
fixes the spelling of its factors. -/
theorem zariskiReadingTensorSquareMate_19_8_7_7_8Aux (h₀ : T' ⟶ T)
    (N₀ M₀ : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hN₀ : N₀.IsQuasicoherentOnSite) (hM₀ : M₀.IsQuasicoherentOnSite) :
    type_of% (fun a1 a2 a3 a4 a5 a6 a7 a8 => (NatTrans.app_heq_of_heq a1 a2 a3 a4 a5 a6 a7 a8 :
          HypothesisOf₈_8 (zariskiReadingTensorSquareMate_19_8_7_7Aux h₀ N₀ M₀ hN₀ hM₀))) :=
  fun a1 a2 a3 a4 a5 a6 a7 a8 => (NatTrans.app_heq_of_heq a1 a2 a3 a4 a5 a6 a7 a8 :
      HypothesisOf₈_8 (zariskiReadingTensorSquareMate_19_8_7_7Aux h₀ N₀ M₀ hN₀ hM₀))

/-- A factor of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMate_19`. -/
theorem zariskiReadingTensorSquareMate_19_8_7_7_8 : HypothesisOf₈_8
    (zariskiReadingTensorSquareMate_19_8_7_7Aux h N M hN hM) :=
  by apply zariskiReadingTensorSquareMate_19_8_7_7_8Aux h N M hN hM <;> rfl

/-- A factor of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMate_19`. -/
theorem zariskiReadingTensorSquareMate_19_8_7_7 : HypothesisOf₇_7
    (zariskiReadingTensorSquareMate_19_8_7Aux h N M hN hM) :=
  zariskiReadingTensorSquareMate_19_8_7_7Aux h N M hN hM rfl rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl
      HEq.rfl (zariskiReadingTensorSquareMate_19_8_7_7_8 h N M hN hM)

/-- A factor of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMate_19`. -/
theorem zariskiReadingTensorSquareMate_19_8_7 : HypothesisOf₇_7
    (zariskiReadingTensorSquareMate_19_8Aux h N M hN hM) :=
  zariskiReadingTensorSquareMate_19_8_7Aux h N M hN hM rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl
      (zariskiReadingTensorSquareMate_19_8_7_6 h N M hN hM)
      (zariskiReadingTensorSquareMate_19_8_7_7 h N M hN hM)

/-- A factor of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMate_19`. -/
theorem zariskiReadingTensorSquareMate_19_8 : HypothesisOf₁₀_8
    (zariskiReadingTensorSquareMate_19Aux h N M hN hM) :=
  zariskiReadingTensorSquareMate_19_8Aux h N M hN hM rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl
      (zariskiReadingTensorSquareMate_19_8_7 h N M hN hM)

/-- A factor of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMate_19`, as a term whose type
fixes the spelling of its factors. -/
theorem zariskiReadingTensorSquareMate_19_9Aux (h₀ : T' ⟶ T)
    (N₀ M₀ : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hN₀ : N₀.IsQuasicoherentOnSite) (hM₀ : M₀.IsQuasicoherentOnSite) :
    type_of% (fun a1 a2 a3 a4 a5 a6 a7 a8 => (NatTrans.app_heq_of_heq a1 a2 a3 a4 a5 a6 a7 a8 :
          HypothesisOf₁₀_9 (zariskiReadingTensorSquareMate_19Aux h₀ N₀ M₀ hN₀ hM₀))) :=
  fun a1 a2 a3 a4 a5 a6 a7 a8 => (NatTrans.app_heq_of_heq a1 a2 a3 a4 a5 a6 a7 a8 :
      HypothesisOf₁₀_9 (zariskiReadingTensorSquareMate_19Aux h₀ N₀ M₀ hN₀ hM₀))

/-- A factor of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMate_19`. -/
theorem zariskiReadingTensorSquareMate_19_9 : HypothesisOf₁₀_9
    (zariskiReadingTensorSquareMate_19Aux h N M hN hM) :=
  by apply zariskiReadingTensorSquareMate_19_9Aux h N M hN hM <;> rfl

/-- A factor of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMate_19`, as a term whose type
fixes the spelling of its factors. -/
theorem zariskiReadingTensorSquareMate_19_10Aux (h₀ : T' ⟶ T)
    (N₀ M₀ : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hN₀ : N₀.IsQuasicoherentOnSite) (hM₀ : M₀.IsQuasicoherentOnSite) :
    type_of% (fun a1 a2 a3 a4 a5 a6 a7 => (comp_heq_of_heq a1 a2 a3 a4 a5 a6 a7 : HypothesisOf₁₀_10
          (zariskiReadingTensorSquareMate_19Aux h₀ N₀ M₀ hN₀ hM₀))) :=
  fun a1 a2 a3 a4 a5 a6 a7 => (comp_heq_of_heq a1 a2 a3 a4 a5 a6 a7 : HypothesisOf₁₀_10
      (zariskiReadingTensorSquareMate_19Aux h₀ N₀ M₀ hN₀ hM₀))

/-- A factor of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMate_19`, as a term whose type
fixes the spelling of its factors. -/
theorem zariskiReadingTensorSquareMate_19_10_6Aux (h₀ : T' ⟶ T)
    (N₀ M₀ : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hN₀ : N₀.IsQuasicoherentOnSite) (hM₀ : M₀.IsQuasicoherentOnSite) :
    type_of% (fun a1 a2 a3 a4 a5 a6 a7 a8 => (Functor.map_heq_of_heq a1 a2 a3 a4 a5 a6 a7 a8 :
          HypothesisOf₇_6
          (zariskiReadingTensorSquareMate_19_10Aux h₀ N₀ M₀ hN₀ hM₀))) :=
  fun a1 a2 a3 a4 a5 a6 a7 a8 => (Functor.map_heq_of_heq a1 a2 a3 a4 a5 a6 a7 a8 : HypothesisOf₇_6
      (zariskiReadingTensorSquareMate_19_10Aux h₀ N₀ M₀ hN₀ hM₀))

/-- A factor of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMate_19`. -/
theorem zariskiReadingTensorSquareMate_19_10_6 : HypothesisOf₇_6
    (zariskiReadingTensorSquareMate_19_10Aux h N M hN hM) :=
  by apply zariskiReadingTensorSquareMate_19_10_6Aux h N M hN hM <;> rfl

/-- A factor of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMate_19`. -/
theorem zariskiReadingTensorSquareMate_19_10 : HypothesisOf₁₀_10
    (zariskiReadingTensorSquareMate_19Aux h N M hN hM) :=
  zariskiReadingTensorSquareMate_19_10Aux h N M hN hM rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl
      (zariskiReadingTensorSquareMate_19_10_6 h N M hN hM) HEq.rfl

/-- Hypothesis 19 of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMateAux`: Stacks 03EL along
the two factorizations of the square of `h`. -/
theorem zariskiReadingTensorSquareMate_19 : HypothesisOf₂₀_19
    (zariskiReadingTensorSquareMateAux h N M hN hM) :=
  zariskiReadingTensorSquareMate_19Aux h N M hN hM rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl
      (zariskiReadingTensorSquareMate_19_7 h N M hN hM)
      (zariskiReadingTensorSquareMate_19_8 h N M hN hM)
      (zariskiReadingTensorSquareMate_19_9 h N M hN hM)
      (zariskiReadingTensorSquareMate_19_10 h N M hN hM)

end AlgebraicGeometry.Space
