module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.EnvelopeBaseChangeRows
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalPairFormsConnection
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.WholeSpaceCompletedBaseChange
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.WholeSpaceTaylorExpansion

/-!
# The cosimplicial pair of a crystal in quasi-coherent modules

Let `ℱ` be a crystal in quasi-coherent `𝒪_{X/S}`-modules, in the situation of
[Stacks, Proposition 60.20.1, Tag 07JN], `M(•) = lim_e Γ(T(•)_e, ℱ)` its cosimplicial module over
the completed cosimplicial envelope `D(•)` and `∇` the connection of the pair `(M, ∇)` of
[Stacks, Lemma 60.17.3, Tag 07JG] attached to `ℱ`, read in the completed one-forms of `D = D(0)`
(`...SmallSite.crystalPairFormsConnection`).  The proof of
[Stacks, Proposition 60.21.3, Tag 07LG] equips every `M(b)` with the base change of `∇` along the
coprojection `σ_b : ⦋0⦌ ⟶ ⦋b⦌`, which makes sense because `ℱ` is a crystal:
`M(b) = D(b) ⊗̂_{D(0), σ_b} M(0)` (`...SmallSite.wholeSpaceBaseChangeEquiv`).  This module builds
that cosimplicial pair.  Its compatibility with the cosimplicial structure is the horizontality of
the coface `δ : ⦋0⦌ ⟶ ⦋1⦌, 0 ↦ 1`, which holds because `M(δ)` is the Taylor series of the crystal
(`...SmallSite.wholeSpace_taylorExpansion`) and the Taylor series of a connection is horizontal
(`Crystalline.CosimplicialCompletedModule.baseChangeConnection_map_delta_of_taylor`).

## Main definitions and results

* `...SmallSite.crystalCoprojectionBeta` — the crystal base change `D(b) ⊗̂_{D(0)} M(0) ≅ M(b)`
  along the coprojection.
* `...SmallSite.crystalPairFormsConnection_horizontal_delta` — **the coface `δ` is horizontal**
  for the base-change connections.
* `...SmallSite.crystalCosimplicialPair` — the cosimplicial pair `(M(•), ∇_•)`.

## References

* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Simplicial DividedPowers
open scoped TensorProduct

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.X] [IsAffine S.S.scheme]
  (hp : IsNilpotent (S.p : Γ(S.X, ⊤))) [WholeSpacePresentation S hp] (Fc : QuasiCoherentCrystal S)

/-- **The crystal base change along the coprojection `σ_b : ⦋0⦌ ⟶ ⦋b⦌`**:
`D(b) ⊗̂_{D(0)} M(0) ≅ M(b)`, `x ⊗ m ↦ x · σ_b(m)`; it is
`...SmallSite.wholeSpaceBaseChangeEquiv` at `σ_b`. -/
def crystalCoprojectionBeta (b : ℕ) :
    letI := (wholeSpaceDPAlgebra hp).coprojectionAlgebra S.p b
    CompletedConnection.baseChangeCarrier S.p ((wholeSpaceDPAlgebra hp).completedRing S.p 0)
        ((wholeSpaceDPAlgebra hp).completedRing S.p b)
        ((wholeSpaceCosimplicialModule hp Fc).carrier 0) ≃ₗ[
        (wholeSpaceDPAlgebra hp).completedRing S.p b]
      (wholeSpaceCosimplicialModule hp Fc).carrier b where
  toFun x := wholeSpaceBaseChangeEquiv hp Fc (m := ⦋0⦌) (n := ⦋b⦌)
    (CosimplicialDPAlgebra.coprojection b) x
  invFun y := (wholeSpaceBaseChangeEquiv hp Fc (m := ⦋0⦌) (n := ⦋b⦌)
    (CosimplicialDPAlgebra.coprojection b)).symm y
  map_add' x y := map_add (wholeSpaceBaseChangeEquiv hp Fc (m := ⦋0⦌) (n := ⦋b⦌)
    (CosimplicialDPAlgebra.coprojection b)) x y
  map_smul' r x := map_smul (wholeSpaceBaseChangeEquiv hp Fc (m := ⦋0⦌) (n := ⦋b⦌)
    (CosimplicialDPAlgebra.coprojection b)) r x
  left_inv x := (wholeSpaceBaseChangeEquiv hp Fc (m := ⦋0⦌) (n := ⦋b⦌)
    (CosimplicialDPAlgebra.coprojection b)).symm_apply_apply x
  right_inv y := (wholeSpaceBaseChangeEquiv hp Fc (m := ⦋0⦌) (n := ⦋b⦌)
    (CosimplicialDPAlgebra.coprojection b)).apply_symm_apply y

/-- The crystal base change on a pure tensor: `x ⊗ m ↦ x · σ_b(m)`. -/
theorem crystalCoprojectionBeta_of_tmul (b : ℕ)
    (x : (wholeSpaceDPAlgebra hp).completedRing S.p b)
    (m : (wholeSpaceCosimplicialModule hp Fc).carrier 0) :
    letI := (wholeSpaceDPAlgebra hp).coprojectionAlgebra S.p b
    crystalCoprojectionBeta hp Fc b
        (AdicCompletion.of (pAdicIdeal (A := (wholeSpaceDPAlgebra hp).completedRing S.p b) S.p)
          ((wholeSpaceDPAlgebra hp).completedRing S.p b ⊗[
              (wholeSpaceDPAlgebra hp).completedRing S.p 0]
            (wholeSpaceCosimplicialModule hp Fc).carrier 0)
          (x ⊗ₜ[(wholeSpaceDPAlgebra hp).completedRing S.p 0] m)) =
      x • (wholeSpaceCosimplicialModule hp Fc).map (CosimplicialDPAlgebra.coprojection b) m :=
  wholeSpaceBaseChangeEquiv_of_tmul hp Fc (m := ⦋0⦌) (n := ⦋b⦌)
    (CosimplicialDPAlgebra.coprojection b) x m

/-- **The coface `δ : ⦋0⦌ ⟶ ⦋1⦌, 0 ↦ 1` is horizontal** for the base change of the connection of
the pair of the crystal: `∇₁ (M(δ) m) = M(δ)_* (∇ m)`. This is
`Crystalline.CosimplicialCompletedModule.baseChangeConnection_map_delta_of_taylor` at the Taylor
expansion `...SmallSite.wholeSpace_taylorExpansion` of the crystal, the operators `θ_K` of
[Stacks, Tag 07JG] composing as `θ_L ∘ θ_K = θ_{K + L}` and giving the coordinate expansion of
the connection. -/
theorem crystalPairFormsConnection_horizontal_delta
    (m : (wholeSpaceCosimplicialModule hp Fc).carrier 0) :
    (wholeSpaceCosimplicialModule hp Fc).baseChangeConnection (crystalPairFormsConnection hp Fc)
        (crystalCoprojectionBeta hp Fc) 1
        ((wholeSpaceCosimplicialModule hp Fc).map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1) m) =
      (wholeSpaceCosimplicialModule hp Fc).tensorMap (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1) 1
        (crystalPairFormsConnection hp Fc m) := by
  classical
  exact (wholeSpaceCosimplicialModule hp Fc).baseChangeConnection_map_delta_of_taylor
    (crystalPairFormsConnection hp Fc) (crystalCoprojectionBeta hp Fc)
    (crystalCoprojectionBeta_of_tmul hp Fc) (wsCoordinate hp) (crystalTheta hp Fc)
    (fun K L m => crystalTheta_crystalTheta hp Fc K L m)
    (isCoordinateExpansion_crystalPairFormsConnection hp Fc)
    (finite_crystalTheta_notMem_pPowSmul hp Fc) (coordinateDifference_wsCoordinate_mem hp)
    (wholeSpace_taylorExpansion hp Fc) m

/-- **The cosimplicial pair of a crystal in quasi-coherent modules**: the cosimplicial module
`M(•) = lim_e Γ(T(•)_e, ℱ)` with, in each degree `b`, the base change along the coprojection of
the connection of the pair `(M, ∇)` of [Stacks, Lemma 60.17.3, Tag 07JG]. -/
def crystalCosimplicialPair : CosimplicialCompletedPair.{u, u, u} (wholeSpaceDPAlgebra hp) S.p :=
  (wholeSpaceCosimplicialModule hp Fc).baseChangePair (crystalPairFormsConnection hp Fc)
    (crystalCoprojectionBeta hp Fc) (crystalCoprojectionBeta_of_tmul hp Fc)
    (crystalPairFormsConnection_horizontal_delta hp Fc)
    (hasIntegrableConnection_crystalPairFormsConnection hp Fc)

end Crystalline.GlobalCrystallineSituation.SmallSite

end
