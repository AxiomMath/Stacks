module

public import
    StacksFrontier.AlgebraicGeometry.Crystalline.ModuleDifferentials.CompletionComparisonLevelwise
public import StacksFrontier.AlgebraicGeometry.Crystalline.ModuleDifferentials.CompletionLevelFormsExt

/-!
# The de Rham terms of a ring and of its completion agree after completion

Let `A → B` be a ring map, let the ideal `J` of `B` carry divided powers `δ`, let `p` be nilpotent
modulo `J`, write `B̂` for the `p`-adic completion with its divided powers `γ̂`, and let `N` be any
`B`-module.  The comparison `ν : Ω_{B/A,δ} ⟶ Ω_{B̂/A,γ̂}` of
`Crystalline.completionDifferentialsMap` induces in each degree a map

`N ⊗_B ⋀ⁱ_B Ω_{B/A,δ} ⟶ (B̂ ⊗_B N) ⊗_{B̂} ⋀ⁱ_{B̂} Ω_{B̂/A,γ̂}`,

pinned down by `n ⊗ (ω₁ ∧ ⋯ ∧ ω_i) ↦ (1 ⊗ n) ⊗ (ν ω₁ ∧ ⋯ ∧ ν ω_i)`, and the theorem below is that
**its `p`-adic completion is bijective**.

This is [Stacks, Lemma 60.20.1, Tag 07KK] in every exterior degree and after tensoring: the degree
one statement is `Crystalline.bijective_levelMap_completionDifferentialsBaseChange`, exterior
powers and a tensor factor preserve levelwise bijectivity
(`Crystalline.bijective_reduceModIdeal_exteriorPowerMap`,
`Crystalline.bijective_reduceModIdeal_lTensor`), extending scalars from `B` to `B̂` changes nothing
at any level (`Crystalline.bijective_reduceModIdeal_tensorUnit`), and levelwise bijectivity at the
deep levels passes to the completion
(`Crystalline.PAdicCompletion.bijective_mapAddHom_of_levelMap`).

The map is produced here as a composite of those four steps rather than abstractly, and the
theorem is stated for **any** additive map with the characterising value on tensors of wedges —
which is how a canonical map of de Rham complexes produced by [Stacks, Tag 07KJ] arrives.

## Main definitions

* `Crystalline.completedFormsFactor` — the degree-`i` comparison on the forms, out of the base
  change `B̂ ⊗_B ⋀ⁱ_B Ω_{B/A,δ}`.
* `Crystalline.completedDeRhamComparison` — the degreewise comparison of the two de Rham terms.

## Main results

* `Crystalline.eq_completedDeRhamComparison` — the characterisation on tensors of wedges.
* `Crystalline.bijective_mapAddHom_completedDeRhamComparison` and
  `Crystalline.bijective_mapAddHom_of_tmul_ιMulti` — the completed comparison is bijective.

## References

* [Stacks Project, Lemma 60.20.1, Tag 07KK](https://stacks.math.columbia.edu/tag/07KK)
* [Stacks Project, Remark 60.17.4, Tag 07KJ](https://stacks.math.columbia.edu/tag/07KJ)
-/

@[expose] public noncomputable section

open DividedPowers

open scoped TensorProduct

universe u v w

namespace Crystalline

section Degreewise

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable (J : Ideal B) (delta : DividedPowers J) (p : ℕ)
  (hp : IsNilpotent (Ideal.Quotient.mk J (p : B)))
variable (N : Type w) [AddCommGroup N] [Module B N]

/-- **The degree-`i` comparison on the forms**: the base change of the exterior power of
`Ω_{B/A,δ}` to `B̂`, followed by the exterior power of `ν`. -/
def completedFormsFactor (i : ℕ) :
    AdicCompletion (pAdicIdeal (A := B) p) B ⊗[B]
        (⋀[B]^i (dividedPowerDifferentials (A := A) delta))
      →ₗ[AdicCompletion (pAdicIdeal (A := B) p) B]
        ⋀[AdicCompletion (pAdicIdeal (A := B) p) B]^i
          (dividedPowerDifferentials (A := A)
            (DividedPowers.completedDividedPowers J delta p hp).1) :=
  (exteriorPower.map i (completionDifferentialsBaseChange (A := A) J delta p hp)).comp
    (ExteriorAlgebra.exteriorPowerBaseChange B (AdicCompletion (pAdicIdeal (A := B) p) B)
      (dividedPowerDifferentials (A := A) delta) i).toLinearMap

/-- The degree-`i` comparison carries `1 ⊗ (ω₁ ∧ ⋯ ∧ ω_i)` to `ν ω₁ ∧ ⋯ ∧ ν ω_i`. -/
theorem completedFormsFactor_one_tmul_ιMulti (i : ℕ)
    (v : Fin i → dividedPowerDifferentials (A := A) delta) :
    completedFormsFactor (A := A) J delta p hp i
        ((1 : AdicCompletion (pAdicIdeal (A := B) p) B) ⊗ₜ[B]
          exteriorPower.ιMulti B i v) =
      exteriorPower.ιMulti (AdicCompletion (pAdicIdeal (A := B) p) B) i
        (completionDifferentialsMap (A := A) J delta p hp ∘ v) := by
  change (exteriorPower.map i (completionDifferentialsBaseChange (A := A) J delta p hp))
      (ExteriorAlgebra.exteriorPowerBaseChange B (AdicCompletion (pAdicIdeal (A := B) p) B)
        (dividedPowerDifferentials (A := A) delta) i
        ((1 : AdicCompletion (pAdicIdeal (A := B) p) B) ⊗ₜ[B]
          exteriorPower.ιMulti B i v)) = _
  rw [ExteriorAlgebra.exteriorPowerBaseChange_tmul_ιMulti, one_smul,
    exteriorPower.map_apply_ιMulti]
  congr 1
  funext j
  exact (completionDifferentialsBaseChange_tmul (A := A) J delta p hp 1 (v j)).trans
    (one_smul _ _)

/-- **The degreewise comparison of the two de Rham terms**, factored as the unit of the base change
to `B̂`, the distribution of that base change over the tensor product, and the degree-`i`
comparison on the forms. -/
def completedDeRhamComparison (i : ℕ) :
    (N ⊗[B] (⋀[B]^i (dividedPowerDifferentials (A := A) delta))) →+
      ((AdicCompletion (pAdicIdeal (A := B) p) B ⊗[B] N)
        ⊗[AdicCompletion (pAdicIdeal (A := B) p) B]
          (⋀[AdicCompletion (pAdicIdeal (A := B) p) B]^i
            (dividedPowerDifferentials (A := A)
              (DividedPowers.completedDividedPowers J delta p hp).1))) :=
  (LinearMap.lTensor (AdicCompletion (pAdicIdeal (A := B) p) B ⊗[B] N)
      (completedFormsFactor (A := A) J delta p hp i)).toAddMonoidHom.comp
    (((TensorProduct.AlgebraTensorModule.distribBaseChange B
        (AdicCompletion (pAdicIdeal (A := B) p) B) N
        (⋀[B]^i (dividedPowerDifferentials (A := A) delta))).toLinearMap).toAddMonoidHom.comp
      (tensorUnit (pAdicIdeal (A := B) p)
        (X := N ⊗[B] (⋀[B]^i (dividedPowerDifferentials (A := A) delta)))).toAddMonoidHom)

/-- The degreewise comparison carries a tensor of a wedge to the expected tensor of a wedge. -/
theorem completedDeRhamComparison_tmul_ιMulti (i : ℕ) (n : N)
    (v : Fin i → dividedPowerDifferentials (A := A) delta) :
    completedDeRhamComparison (A := A) J delta p hp N i
        (n ⊗ₜ[B] exteriorPower.ιMulti B i v) =
      ((1 : AdicCompletion (pAdicIdeal (A := B) p) B) ⊗ₜ[B] n)
        ⊗ₜ[AdicCompletion (pAdicIdeal (A := B) p) B]
          exteriorPower.ιMulti (AdicCompletion (pAdicIdeal (A := B) p) B) i
            (completionDifferentialsMap (A := A) J delta p hp ∘ v) := by
  change (LinearMap.lTensor (AdicCompletion (pAdicIdeal (A := B) p) B ⊗[B] N)
      (completedFormsFactor (A := A) J delta p hp i))
    (TensorProduct.AlgebraTensorModule.distribBaseChange B
      (AdicCompletion (pAdicIdeal (A := B) p) B) N
      (⋀[B]^i (dividedPowerDifferentials (A := A) delta))
      ((1 : AdicCompletion (pAdicIdeal (A := B) p) B) ⊗ₜ[B]
        (n ⊗ₜ[B] exteriorPower.ιMulti B i v))) = _
  rw [TensorProduct.AlgebraTensorModule.distribBaseChange_tmul, LinearMap.lTensor_tmul,
    completedFormsFactor_one_tmul_ιMulti]

/-- **Any additive map with the characterising value on tensors of wedges is the degreewise
comparison.** -/
theorem eq_completedDeRhamComparison (i : ℕ)
    (Phi : (N ⊗[B] (⋀[B]^i (dividedPowerDifferentials (A := A) delta))) →+
      ((AdicCompletion (pAdicIdeal (A := B) p) B ⊗[B] N)
        ⊗[AdicCompletion (pAdicIdeal (A := B) p) B]
          (⋀[AdicCompletion (pAdicIdeal (A := B) p) B]^i
            (dividedPowerDifferentials (A := A)
              (DividedPowers.completedDividedPowers J delta p hp).1))))
    (hwedge : ∀ (n : N) (v : Fin i → dividedPowerDifferentials (A := A) delta),
      Phi (n ⊗ₜ[B] exteriorPower.ιMulti B i v) =
        ((1 : AdicCompletion (pAdicIdeal (A := B) p) B) ⊗ₜ[B] n)
          ⊗ₜ[AdicCompletion (pAdicIdeal (A := B) p) B]
            exteriorPower.ιMulti (AdicCompletion (pAdicIdeal (A := B) p) B) i
              (completionDifferentialsMap (A := A) J delta p hp ∘ v)) :
    Phi = completedDeRhamComparison (A := A) J delta p hp N i :=
  tensorExteriorPower_addMonoidHom_ext fun n v ↦
    (hwedge n v).trans
      (completedDeRhamComparison_tmul_ιMulti (A := A) J delta p hp N i n v).symm

/-- **The degree-`i` comparison on the forms inherits levelwise bijectivity from degree one**, by
`Crystalline.bijective_reduceModIdeal_exteriorPowerMap`. -/
theorem bijective_reduceModIdeal_completedFormsFactor (i n : ℕ)
    (hn : Function.Bijective
      ((completionDifferentialsBaseChange (A := A) J delta p hp).reduceModIdeal
        (pAdicIdeal (A := AdicCompletion (pAdicIdeal (A := B) p) B) p ^ n))) :
    Function.Bijective ((completedFormsFactor (A := A) J delta p hp i).reduceModIdeal
      (pAdicIdeal (A := AdicCompletion (pAdicIdeal (A := B) p) B) p ^ n)) := by
  refine PAdicCompletion.bijective_reduceModIdeal_of_levelMap p
    (AdicCompletion (pAdicIdeal (A := B) p) B)
    (completedFormsFactor (A := A) J delta p hp i) n
    (AdicCompletion (pAdicIdeal (A := B) p) B) ?_
  change Function.Bijective (PAdicCompletion.levelMap p
    (AdicCompletion (pAdicIdeal (A := B) p) B) (AdicCompletion (pAdicIdeal (A := B) p) B)
    ((exteriorPower.map i
        (completionDifferentialsBaseChange (A := A) J delta p hp)).toAddMonoidHom.comp
      (ExteriorAlgebra.exteriorPowerBaseChange B (AdicCompletion (pAdicIdeal (A := B) p) B)
        (dividedPowerDifferentials (A := A) delta) i).toLinearMap.toAddMonoidHom) n)
  refine PAdicCompletion.bijective_levelMap_comp p
    (AdicCompletion (pAdicIdeal (A := B) p) B) (AdicCompletion (pAdicIdeal (A := B) p) B)
    (AdicCompletion (pAdicIdeal (A := B) p) B) _ _ n ?_ ?_
  · exact PAdicCompletion.bijective_levelMap_of_bijective p _ _ _
      (ExteriorAlgebra.exteriorPowerBaseChange B (AdicCompletion (pAdicIdeal (A := B) p) B)
        (dividedPowerDifferentials (A := A) delta) i).bijective n
  · exact PAdicCompletion.bijective_levelMap_of_reduceModIdeal p
      (AdicCompletion (pAdicIdeal (A := B) p) B)
      (exteriorPower.map i (completionDifferentialsBaseChange (A := A) J delta p hp)) n
      (bijective_reduceModIdeal_exteriorPowerMap _
        (completionDifferentialsBaseChange (A := A) J delta p hp) i hn)
      (AdicCompletion (pAdicIdeal (A := B) p) B)

/-- **The `p`-adic completion of the degreewise comparison is bijective**, given a cutoff beyond
which the comparison on the forms is bijective. -/
theorem bijective_mapAddHom_completedDeRhamComparison_of (i cutoff : ℕ)
    (hcut : ∀ n : ℕ, cutoff ≤ n →
      Function.Bijective ((completedFormsFactor (A := A) J delta p hp i).reduceModIdeal
        (pAdicIdeal (A := AdicCompletion (pAdicIdeal (A := B) p) B) p ^ n))) :
    Function.Bijective (PAdicCompletion.mapAddHom p B
      (AdicCompletion (pAdicIdeal (A := B) p) B)
      (completedDeRhamComparison (A := A) J delta p hp N i)) := by
  refine PAdicCompletion.bijective_mapAddHom_of_levelMap p B
    (AdicCompletion (pAdicIdeal (A := B) p) B) _ cutoff (fun n hn ↦ ?_)
  change Function.Bijective (PAdicCompletion.levelMap p B
    (AdicCompletion (pAdicIdeal (A := B) p) B)
    ((LinearMap.lTensor (AdicCompletion (pAdicIdeal (A := B) p) B ⊗[B] N)
        (completedFormsFactor (A := A) J delta p hp i)).toAddMonoidHom.comp
      (((TensorProduct.AlgebraTensorModule.distribBaseChange B
          (AdicCompletion (pAdicIdeal (A := B) p) B) N
          (⋀[B]^i (dividedPowerDifferentials (A := A) delta))).toLinearMap).toAddMonoidHom.comp
        (tensorUnit (pAdicIdeal (A := B) p)
          (X := N ⊗[B] (⋀[B]^i (dividedPowerDifferentials (A := A) delta)))).toAddMonoidHom)) n)
  refine PAdicCompletion.bijective_levelMap_comp p B
    (AdicCompletion (pAdicIdeal (A := B) p) B)
    (AdicCompletion (pAdicIdeal (A := B) p) B) _ _ n ?_ ?_
  · refine PAdicCompletion.bijective_levelMap_comp p B
      (AdicCompletion (pAdicIdeal (A := B) p) B)
      (AdicCompletion (pAdicIdeal (A := B) p) B) _ _ n ?_ ?_
    · exact PAdicCompletion.bijective_levelMap_of_reduceModIdeal p B _ n
        (bijective_reduceModIdeal_tensorUnit (pAdicIdeal (A := B) p)
          (Submodule.fg_span_singleton _) n) _
    · exact PAdicCompletion.bijective_levelMap_of_bijective p _ _ _
        (TensorProduct.AlgebraTensorModule.distribBaseChange B
          (AdicCompletion (pAdicIdeal (A := B) p) B) N
          (⋀[B]^i (dividedPowerDifferentials (A := A) delta))).bijective n
  · exact PAdicCompletion.bijective_levelMap_of_reduceModIdeal p
      (AdicCompletion (pAdicIdeal (A := B) p) B) _ n
      (bijective_reduceModIdeal_lTensor _ (completedFormsFactor (A := A) J delta p hp i)
        (hcut n hn) (AdicCompletion (pAdicIdeal (A := B) p) B ⊗[B] N)) _

/-- **The `p`-adic completion of the degreewise comparison is bijective.** -/
theorem bijective_mapAddHom_completedDeRhamComparison [Fact p.Prime]
    [Algebra (DividedPowers.IntegersAtPrime p) A] (i : ℕ) :
    Function.Bijective (PAdicCompletion.mapAddHom p B
      (AdicCompletion (pAdicIdeal (A := B) p) B)
      (completedDeRhamComparison (A := A) J delta p hp N i)) :=
  bijective_mapAddHom_completedDeRhamComparison_of (A := A) J delta p hp N i
    (bijective_levelMap_completionDifferentialsBaseChange (A := A) J delta p hp).choose
    fun n hn ↦ bijective_reduceModIdeal_completedFormsFactor (A := A) J delta p hp i n
      (PAdicCompletion.bijective_reduceModIdeal_of_levelMap p
        (AdicCompletion (pAdicIdeal (A := B) p) B) _ n
        (AdicCompletion (pAdicIdeal (A := B) p) B)
        ((bijective_levelMap_completionDifferentialsBaseChange
          (A := A) J delta p hp).choose_spec n hn))

/-- **The `p`-adic completion of any additive map with the characterising value on tensors of
wedges is bijective.** -/
theorem bijective_mapAddHom_of_tmul_ιMulti [Fact p.Prime]
    [Algebra (DividedPowers.IntegersAtPrime p) A] (i : ℕ)
    (Phi : (N ⊗[B] (⋀[B]^i (dividedPowerDifferentials (A := A) delta))) →+
      ((AdicCompletion (pAdicIdeal (A := B) p) B ⊗[B] N)
        ⊗[AdicCompletion (pAdicIdeal (A := B) p) B]
          (⋀[AdicCompletion (pAdicIdeal (A := B) p) B]^i
            (dividedPowerDifferentials (A := A)
              (DividedPowers.completedDividedPowers J delta p hp).1))))
    (hwedge : ∀ (n : N) (v : Fin i → dividedPowerDifferentials (A := A) delta),
      Phi (n ⊗ₜ[B] exteriorPower.ιMulti B i v) =
        ((1 : AdicCompletion (pAdicIdeal (A := B) p) B) ⊗ₜ[B] n)
          ⊗ₜ[AdicCompletion (pAdicIdeal (A := B) p) B]
            exteriorPower.ιMulti (AdicCompletion (pAdicIdeal (A := B) p) B) i
              (completionDifferentialsMap (A := A) J delta p hp ∘ v)) :
    Function.Bijective (PAdicCompletion.mapAddHom p B
      (AdicCompletion (pAdicIdeal (A := B) p) B) Phi) := by
  rw [eq_completedDeRhamComparison (A := A) J delta p hp N i Phi hwedge]
  exact bijective_mapAddHom_completedDeRhamComparison (A := A) J delta p hp N i

end Degreewise

end Crystalline

end
