module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalPairFormsConnection
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalPairUnit

/-!
# The pair of the structure sheaf, with values in the completed forms

The connection of the pair `(M, ∇)` of [Stacks, Lemma 60.17.3, Tag 07JG] attached to a crystal,
read with values in the completed one-forms `Ω̂¹_D` of `D`, is
`...SmallSite.crystalPairFormsConnection`.  For the structure sheaf `𝒪_{X/S}` the module is `D`
itself, on the unit section (`...SmallSite.pairUnitEquiv`), and the connection is then
`∇ (r · 1) = 1 ⊗ d r`: the pair of `𝒪_{X/S}` is the structure module `(D, ∇ = 1 ⊗ d)` of the
ring with forms `D` of the situation.

## Main results

* `...SmallSite.crystalPairFormsConnection_unit_pairUnitEquiv` — `∇ (r · 1) = 1 ⊗ d r`.
* `...SmallSite.crystalPairFormsConnection_unit_horizontal` — `r ↦ r · 1` is horizontal from the
  structure module of `D`.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry Simplicial
open scoped TensorProduct

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open Crystalline

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.X] [IsAffine S.S.scheme]
  (hp : IsNilpotent (S.p : Γ(S.X, ⊤))) [WholeSpacePresentation S hp]

/-- **The pair of the structure sheaf, with values in the completed forms**: its connection is
`∇ (r · 1) = 1 ⊗ d r`. -/
theorem crystalPairFormsConnection_unit_pairUnitEquiv (r : pairRing hp) :
    crystalPairFormsConnection hp (quasiCoherentCrystalUnit S) (pairUnitEquiv hp r) =
      toCompletedTensor S.p ((wholeSpaceDPAlgebra hp).completedRing S.p 0)
        ((wholeSpaceDPAlgebra hp).forms S.p 1 0)
        (wholeSpaceSections hp (quasiCoherentCrystalUnit S) ⦋0⦌)
        (pairUnitOne hp ⊗ₜ (wholeSpaceDPAlgebra hp).differential S.p 0
          (show (wholeSpaceDPAlgebra hp).completedRing S.p 0 from r)) := by
  rw [crystalPairFormsConnection_eq, pairConnection_unit_pairUnitEquiv]
  show AdicCompletion.map _ _ (AdicCompletion.of _ _ _) = _
  rw [AdicCompletion.map_of, LinearMap.lTensor_tmul]
  exact congrArg (fun ω ↦ AdicCompletion.of _ _ (pairUnitOne hp ⊗ₜ ω))
    (crystalPairFormsEquiv_pairDerivation hp r)

/-- `r ↦ r · 1`, as a linear map over the completed ring `D̂(0)` of the cosimplicial degree
zero. -/
def pairUnitLinear :
    (wholeSpaceDPAlgebra hp).completedRing S.p 0 →ₗ[(wholeSpaceDPAlgebra hp).completedRing S.p 0]
      wholeSpaceSections hp (quasiCoherentCrystalUnit S) ⦋0⦌ :=
  LinearMap.toSpanSingleton _ _ (pairUnitOne hp)

/-- `pairUnitLinear` agrees with `pairUnitEquiv` pointwise. -/
theorem pairUnitLinear_apply (r : (wholeSpaceDPAlgebra hp).completedRing S.p 0) :
    pairUnitLinear hp r = pairUnitEquiv hp r := rfl

/-- `r ↦ r · 1` is bijective. -/
theorem pairUnitLinear_bijective : Function.Bijective (pairUnitLinear hp) :=
  (pairUnitEquiv hp).bijective

/-- **`r ↦ r · 1` is horizontal from the structure module `(D, ∇ = 1 ⊗ d)` of `D` to the pair of
the structure sheaf**, both read over the completed ring `D̂(0)` with values in its completed
forms. -/
theorem crystalPairFormsConnection_unit_horizontal
    (r : (wholeSpaceDPAlgebra hp).completedRing S.p 0) :
    crystalPairFormsConnection hp (quasiCoherentCrystalUnit S) (pairUnitLinear hp r) =
      AdicCompletion.map (DividedPowers.pAdicIdeal
          (A := (wholeSpaceDPAlgebra hp).completedRing S.p 0) S.p)
        (TensorProduct.map (pairUnitLinear hp)
          (LinearMap.id (R := (wholeSpaceDPAlgebra hp).completedRing S.p 0)
            (M := (wholeSpaceDPAlgebra hp).forms S.p 1 0)))
        (toCompletedTensor S.p ((wholeSpaceDPAlgebra hp).completedRing S.p 0)
          ((wholeSpaceDPAlgebra hp).forms S.p 1 0) ((wholeSpaceDPAlgebra hp).completedRing S.p 0)
          ((1 : (wholeSpaceDPAlgebra hp).completedRing S.p 0) ⊗ₜ
            (wholeSpaceDPAlgebra hp).differential S.p 0 r)) := by
  refine (crystalPairFormsConnection_unit_pairUnitEquiv hp r).trans ?_
  refine Eq.trans ?_ (AdicCompletion.map_of _ _ _).symm
  refine congrArg (AdicCompletion.of _ _) ?_
  refine Eq.trans ?_ (TensorProduct.map_tmul _ _ _ _).symm
  exact congrArg (· ⊗ₜ[(wholeSpaceDPAlgebra hp).completedRing S.p 0] _)
    (one_smul _ (pairUnitOne hp)).symm

end Crystalline.GlobalCrystallineSituation.SmallSite

end
