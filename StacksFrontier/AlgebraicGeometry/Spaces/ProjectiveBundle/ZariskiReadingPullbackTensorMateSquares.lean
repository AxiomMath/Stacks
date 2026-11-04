module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.ZariskiReadingPullbackTensorMateHeq

/-!
# The squares of the mate in the monoidality chase at the base change of the Zariski reading

`AlgebraicGeometry.Space.zariskiReadingTensorSquareMateAux` is the implication from twenty squares
to the monoidality of the base change of the Zariski reading along `h : T' ⟶ T`, in the tensor
product sheaf.  This file proves its hypotheses 12 to 15: the transposes of the mate of
`AlgebraicGeometry.Space.representedSquareFactorizationIso` at `𝒩`, `ℳ` and `𝒩 ⊗ ℳ`, and the
comparison of the inverse of Stacks 04M0 at `T` with tensor products, transposed to the counit.
Each is the instance of a general lemma, transported to the spelling fixed by the instance one
factor at a time, so that no two spellings of a category of modules are compared inside a
composite.

## Main results

* `AlgebraicGeometry.Space.zariskiReadingTensorSquareMate_12` … `_15`.
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

/-- Hypothesis 12 of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMateAux`: the transpose of
the mate at `𝒩`, as a term whose type fixes the spelling of its factors. -/
def zariskiReadingTensorSquareMate_12Aux (h₀ : T' ⟶ T) (N₀ M₀ : Modules.{u, u} B S hS (yoneda.obj T)
    (isAlgebraicSpace_yoneda B S hS T)) (hN₀ : N₀.IsQuasicoherentOnSite)
    (hM₀ : M₀.IsQuasicoherentOnSite) :=
  fun a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 =>
      (comp_eq_comp_of_heq (Adjunction.map_equivalenceMateApp_comp_counit
      (representedReindexEquivalenceTopos T) (representedReindexEquivalenceTopos T')
    (representedSquareFactorizationTopos h₀) N₀) a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 :
        HypothesisOf₂₀_12 (zariskiReadingTensorSquareMateAux h₀ N₀ M₀ hN₀ hM₀))

/-- A factor of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMate_12`, as a term whose type
fixes the spelling of its factors. -/
def zariskiReadingTensorSquareMate_12_9Aux (h₀ : T' ⟶ T)
    (N₀ M₀ : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hN₀ : N₀.IsQuasicoherentOnSite) (hM₀ : M₀.IsQuasicoherentOnSite) :=
  fun a1 a2 a3 a4 a5 a6 a7 a8 => (NatTrans.app_heq_of_heq a1 a2 a3 a4 a5 a6 a7 a8 :
      HypothesisOf₁₀_9 (zariskiReadingTensorSquareMate_12Aux h₀ N₀ M₀ hN₀ hM₀))

/-- A factor of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMate_12`. -/
theorem zariskiReadingTensorSquareMate_12_9 : HypothesisOf₁₀_9
    (zariskiReadingTensorSquareMate_12Aux h N M hN hM) := by
  apply zariskiReadingTensorSquareMate_12_9Aux h N M hN hM
  all_goals rfl

/-- Hypothesis 12 of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMateAux`: the transpose of
the mate at `𝒩`. -/
theorem zariskiReadingTensorSquareMate_12 : HypothesisOf₂₀_12
    (zariskiReadingTensorSquareMateAux h N M hN hM) := by
  apply zariskiReadingTensorSquareMate_12Aux h N M hN hM
  any_goals exact zariskiReadingTensorSquareMate_12_9 h N M hN hM
  all_goals rfl

/-- Hypothesis 13 of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMateAux`: the transpose of
the mate at `ℳ`, as a term whose type fixes the spelling of its factors. -/
def zariskiReadingTensorSquareMate_13Aux (h₀ : T' ⟶ T) (N₀ M₀ : Modules.{u, u} B S hS (yoneda.obj T)
    (isAlgebraicSpace_yoneda B S hS T)) (hN₀ : N₀.IsQuasicoherentOnSite)
    (hM₀ : M₀.IsQuasicoherentOnSite) :=
  fun a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 =>
      (comp_eq_comp_of_heq (Adjunction.map_equivalenceMateApp_comp_counit
      (representedReindexEquivalenceTopos T) (representedReindexEquivalenceTopos T')
    (representedSquareFactorizationTopos h₀) M₀) a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 :
        HypothesisOf₂₀_13 (zariskiReadingTensorSquareMateAux h₀ N₀ M₀ hN₀ hM₀))

/-- A factor of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMate_13`, as a term whose type
fixes the spelling of its factors. -/
def zariskiReadingTensorSquareMate_13_9Aux (h₀ : T' ⟶ T)
    (N₀ M₀ : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hN₀ : N₀.IsQuasicoherentOnSite) (hM₀ : M₀.IsQuasicoherentOnSite) :=
  fun a1 a2 a3 a4 a5 a6 a7 a8 => (NatTrans.app_heq_of_heq a1 a2 a3 a4 a5 a6 a7 a8 :
      HypothesisOf₁₀_9 (zariskiReadingTensorSquareMate_13Aux h₀ N₀ M₀ hN₀ hM₀))

/-- A factor of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMate_13`. -/
theorem zariskiReadingTensorSquareMate_13_9 : HypothesisOf₁₀_9
    (zariskiReadingTensorSquareMate_13Aux h N M hN hM) := by
  apply zariskiReadingTensorSquareMate_13_9Aux h N M hN hM
  all_goals rfl

/-- Hypothesis 13 of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMateAux`: the transpose of
the mate at `ℳ`. -/
theorem zariskiReadingTensorSquareMate_13 : HypothesisOf₂₀_13
    (zariskiReadingTensorSquareMateAux h N M hN hM) := by
  apply zariskiReadingTensorSquareMate_13Aux h N M hN hM
  any_goals exact zariskiReadingTensorSquareMate_13_9 h N M hN hM
  all_goals rfl

/-- Hypothesis 14 of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMateAux`: the transpose of
the mate at `𝒩 ⊗ ℳ`, as a term whose type fixes the spelling of its factors. -/
def zariskiReadingTensorSquareMate_14Aux (h₀ : T' ⟶ T) (N₀ M₀ : Modules.{u, u} B S hS (yoneda.obj T)
    (isAlgebraicSpace_yoneda B S hS T)) (hN₀ : N₀.IsQuasicoherentOnSite)
    (hM₀ : M₀.IsQuasicoherentOnSite) :=
  fun a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 =>
      (comp_eq_comp_of_heq (Adjunction.map_equivalenceMateApp_comp_counit
      (representedReindexEquivalenceTopos T) (representedReindexEquivalenceTopos T')
    (representedSquareFactorizationTopos h₀)
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (structureSheaf B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))).obj N₀).obj M₀))
        a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 : HypothesisOf₂₀_14
        (zariskiReadingTensorSquareMateAux h₀ N₀ M₀ hN₀ hM₀))

/-- A factor of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMate_14`, as a term whose type
fixes the spelling of its factors. -/
def zariskiReadingTensorSquareMate_14_9Aux (h₀ : T' ⟶ T)
    (N₀ M₀ : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hN₀ : N₀.IsQuasicoherentOnSite) (hM₀ : M₀.IsQuasicoherentOnSite) :=
  fun a1 a2 a3 a4 a5 a6 a7 a8 => (NatTrans.app_heq_of_heq a1 a2 a3 a4 a5 a6 a7 a8 :
      HypothesisOf₁₀_9 (zariskiReadingTensorSquareMate_14Aux h₀ N₀ M₀ hN₀ hM₀))

/-- A factor of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMate_14`. -/
theorem zariskiReadingTensorSquareMate_14_9 : HypothesisOf₁₀_9
    (zariskiReadingTensorSquareMate_14Aux h N M hN hM) := by
  apply zariskiReadingTensorSquareMate_14_9Aux h N M hN hM
  all_goals rfl

/-- Hypothesis 14 of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMateAux`: the transpose of
the mate at `𝒩 ⊗ ℳ`. -/
theorem zariskiReadingTensorSquareMate_14 : HypothesisOf₂₀_14
    (zariskiReadingTensorSquareMateAux h N M hN hM) := by
  apply zariskiReadingTensorSquareMate_14Aux h N M hN hM
  any_goals exact zariskiReadingTensorSquareMate_14_9 h N M hN hM
  all_goals rfl

/-- Hypothesis 15 of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMateAux`: the comparison of
the inverse of Stacks 04M0 at `T` with tensor products, transposed to the counit, as a term whose
type fixes the spelling of its factors. -/
def zariskiReadingTensorSquareMate_15Aux (h₀ : T' ⟶ T) (N₀ M₀ : Modules.{u, u} B S hS (yoneda.obj T)
    (isAlgebraicSpace_yoneda B S hS T)) (hN₀ : N₀.IsQuasicoherentOnSite)
    (hM₀ : M₀.IsQuasicoherentOnSite) :=
  fun a1 a2 a3 a4 a5 a6 a7 a8 =>
      (comp_eq_of_heq (comp_comp_eq_of_eq
      (pullbackTensorIsoTransport_representedReindex_hom_eq T _ _)
    (Equivalence.functor_map_inverseTensor_comp_counit
        (representedSmallEtaleModuleEquivalence B S hS T)
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (representedSchemeCommRingStructureSheaf B S hS T))
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (structureSheaf B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))) N₀ M₀
      (representedSmallEtaleModuleTensorIso B S hS T _ _))) a1 a2 a3 a4 a5 a6 a7 a8 :
          HypothesisOf₂₀_15 (zariskiReadingTensorSquareMateAux h₀ N₀ M₀ hN₀ hM₀))

/-- A factor of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMate_15`, as a term whose type
fixes the spelling of its factors. -/
def zariskiReadingTensorSquareMate_15_6Aux (h₀ : T' ⟶ T)
    (N₀ M₀ : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hN₀ : N₀.IsQuasicoherentOnSite) (hM₀ : M₀.IsQuasicoherentOnSite) :=
  fun a1 a2 a3 a4 a5 a6 a7 a8 => (Functor.map_heq_of_heq a1 a2 a3 a4 a5 a6 a7 a8 : HypothesisOf₈_6
      (zariskiReadingTensorSquareMate_15Aux h₀ N₀ M₀ hN₀ hM₀))

/-- A factor of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMate_15`, as a term whose type
fixes the spelling of its factors. -/
def zariskiReadingTensorSquareMate_15_6_8Aux (h₀ : T' ⟶ T)
    (N₀ M₀ : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hN₀ : N₀.IsQuasicoherentOnSite) (hM₀ : M₀.IsQuasicoherentOnSite) :=
  fun a1 a2 a3 a4 a5 => (Iso.hom_heq_of_heq a1 a2 a3 a4 a5 : HypothesisOf₈_8
      (zariskiReadingTensorSquareMate_15_6Aux h₀ N₀ M₀ hN₀ hM₀))

/-- A factor of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMate_15`. -/
theorem zariskiReadingTensorSquareMate_15_6_8 : HypothesisOf₈_8
    (zariskiReadingTensorSquareMate_15_6Aux h N M hN hM) := by
  apply zariskiReadingTensorSquareMate_15_6_8Aux h N M hN hM
  all_goals rfl

/-- A factor of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMate_15`. -/
theorem zariskiReadingTensorSquareMate_15_6 : HypothesisOf₈_6
    (zariskiReadingTensorSquareMate_15Aux h N M hN hM) := by
  apply zariskiReadingTensorSquareMate_15_6Aux h N M hN hM
  any_goals exact zariskiReadingTensorSquareMate_15_6_8 h N M hN hM
  all_goals rfl

/-- A factor of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMate_15`, as a term whose type
fixes the spelling of its factors. -/
def zariskiReadingTensorSquareMate_15_7Aux (h₀ : T' ⟶ T)
    (N₀ M₀ : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hN₀ : N₀.IsQuasicoherentOnSite) (hM₀ : M₀.IsQuasicoherentOnSite) :=
  fun a1 a2 a3 a4 a5 a6 a7 => (comp_heq_of_heq a1 a2 a3 a4 a5 a6 a7 : HypothesisOf₈_7
      (zariskiReadingTensorSquareMate_15Aux h₀ N₀ M₀ hN₀ hM₀))

/-- A factor of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMate_15`, as a term whose type
fixes the spelling of its factors. -/
def zariskiReadingTensorSquareMate_15_7_6Aux (h₀ : T' ⟶ T)
    (N₀ M₀ : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hN₀ : N₀.IsQuasicoherentOnSite) (hM₀ : M₀.IsQuasicoherentOnSite) :=
  fun a1 a2 a3 a4 a5 => (Iso.hom_heq_of_heq a1 a2 a3 a4 a5 : HypothesisOf₇_6
      (zariskiReadingTensorSquareMate_15_7Aux h₀ N₀ M₀ hN₀ hM₀))

/-- A factor of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMate_15`. -/
theorem zariskiReadingTensorSquareMate_15_7_6 : HypothesisOf₇_6
    (zariskiReadingTensorSquareMate_15_7Aux h N M hN hM) := by
  apply zariskiReadingTensorSquareMate_15_7_6Aux h N M hN hM
  all_goals rfl

/-- A factor of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMate_15`. -/
theorem zariskiReadingTensorSquareMate_15_7 : HypothesisOf₈_7
    (zariskiReadingTensorSquareMate_15Aux h N M hN hM) := by
  apply zariskiReadingTensorSquareMate_15_7Aux h N M hN hM
  any_goals exact zariskiReadingTensorSquareMate_15_7_6 h N M hN hM
  all_goals rfl

/-- Hypothesis 15 of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMateAux`: the comparison of
the inverse of Stacks 04M0 at `T` with tensor products, transposed to the counit. -/
theorem zariskiReadingTensorSquareMate_15 : HypothesisOf₂₀_15
    (zariskiReadingTensorSquareMateAux h N M hN hM) := by
  apply zariskiReadingTensorSquareMate_15Aux h N M hN hM
  any_goals exact zariskiReadingTensorSquareMate_15_6 h N M hN hM
  any_goals exact zariskiReadingTensorSquareMate_15_7 h N M hN hM
  all_goals rfl

end AlgebraicGeometry.Space
