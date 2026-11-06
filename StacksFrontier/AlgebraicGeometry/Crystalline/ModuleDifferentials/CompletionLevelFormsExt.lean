module

public import StacksFrontier.AlgebraicGeometry.Crystalline.ModuleDifferentials.CompletionLevelForms

/-!
# Tensors of wedges determine a map, and determine the level identification in every degree

A map out of `M ⊗_R ⋀ⁱ_R X` is determined by its values on the tensors `m ⊗ ω₁ ∧ ⋯ ∧ ωᵢ`: those
generate the tensor product as an abelian group, because the wedges generate `⋀ⁱ_R X` over `R`
(`exteriorPower.ιMulti_span`) and a scalar may be moved across the tensor sign.  No linearity of
the map is asked for, which is the point — in the cosimplicial direction the maps whose equality
is wanted are semilinear over different rings, and an `R`-linear extensionality lemma does not
apply to them.

This is how naturality of `Crystalline.tensorExteriorPowerEquivOfBaseChange` across a square of
ring maps is checked: a square of such maps is an equation between two additive maps out of a
tensor product of an exterior power, so `Crystalline.tensorExteriorPower_addMonoidHom_ext`
reduces it to the tensors of wedges, where
`Crystalline.tensorExteriorPowerEquivOfBaseChange_tmul_ιMulti` and its `symm` companion compute
both sides.

## Main results

* `Crystalline.tensorExteriorPower_addMonoidHom_ext` — two additive maps out of
  `M ⊗_R ⋀ⁱ_R X` agreeing on `m ⊗ ω₁ ∧ ⋯ ∧ ωᵢ` are equal.
* `Crystalline.tensorExteriorPower_ext` — the same for `R`-linear maps.
* `Crystalline.tensorFormsCompletionLevelEquiv_unique` — **the level identification in degree
  `i`, after tensoring, is the unique additive map satisfying
  `Crystalline.tensorFormsCompletionLevelEquiv_tmul_ιMulti`.**  So a naturality square for it
  commutes as soon as both routes satisfy that equation, with no further property of the
  comparison `cmp` used.

## References

* [Stacks Project, Tag 07LF](https://stacks.math.columbia.edu/tag/07LF)
* [Stacks Project, Lemma 60.20.1, Tag 07KK](https://stacks.math.columbia.edu/tag/07KK)
-/

@[expose] public section

open scoped TensorProduct

universe u v

namespace Crystalline

/-! ### Tensors of wedges generate -/

section Ext

variable {R M X N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup X]
  [Module R X] [AddCommGroup N]

/-- **Two additive maps out of `M ⊗_R ⋀ⁱ_R X` agreeing on the tensors of wedges are equal.**
No linearity is asked of either map, which is what makes the lemma usable on the semilinear
comparisons of the cosimplicial direction. -/
public theorem tensorExteriorPower_addMonoidHom_ext {i : ℕ}
    {F G : M ⊗[R] ↥(⋀[R]^i X) →+ N}
    (h : ∀ (m : M) (v : Fin i → X),
      F (m ⊗ₜ exteriorPower.ιMulti R i v) = G (m ⊗ₜ exteriorPower.ιMulti R i v)) :
    F = G := by
  refine AddMonoidHom.ext fun z ↦ TensorProduct.inductionOn (motive := fun z ↦ F z = G z) z ?_ ?_
  · intro m x
    refine Submodule.span_induction (p := fun y _ ↦ ∀ w : M, F (w ⊗ₜ y) = G (w ⊗ₜ y))
      ?_ ?_ ?_ ?_
      (Eq.subst (motive := fun S ↦ x ∈ S) (exteriorPower.ιMulti_span R i X).symm
        Submodule.mem_top) m
    · rintro _ ⟨v, rfl⟩ w
      exact h w v
    · intro w
      rw [TensorProduct.tmul_zero, map_zero, map_zero]
    · intro y y' _ _ hy hy' w
      rw [TensorProduct.tmul_add, map_add, map_add, hy, hy']
    · intro r y _ hy w
      rw [← TensorProduct.smul_tmul]
      exact hy (r • w)
  · intro z z' hz hz'
    rw [map_add, map_add, hz, hz']

/-- **Two `R`-linear maps out of `M ⊗_R ⋀ⁱ_R X` agreeing on the tensors of wedges are equal.** -/
public theorem tensorExteriorPower_ext [Module R N] {i : ℕ}
    {F G : M ⊗[R] ↥(⋀[R]^i X) →ₗ[R] N}
    (h : ∀ (m : M) (v : Fin i → X),
      F (m ⊗ₜ exteriorPower.ιMulti R i v) = G (m ⊗ₜ exteriorPower.ιMulti R i v)) :
    F = G :=
  LinearMap.toAddMonoidHom_injective (tensorExteriorPower_addMonoidHom_ext h)

end Ext

/-! ### The level identification in degree `i` is determined -/

section Level

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable (J : Ideal B) (delta : DividedPowers J) (p : ℕ)
variable (hp : IsNilpotent (Ideal.Quotient.mk J (p : B)))
variable (cmp : DifferentialsCompletionComparison (A := A) J delta p hp) (e : ℕ)
variable (M : Type*) [AddCommGroup M]
  [Module (AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B) M]
  [Module (AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B ⧸
    DividedPowers.pAdicIdeal
      (A := AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B) p ^
      (cmp.quotientSystem.cutoff + e)) M]
  [IsScalarTower (AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B)
    (AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B ⧸
      DividedPowers.pAdicIdeal
        (A := AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B) p ^
        (cmp.quotientSystem.cutoff + e)) M]

/-- **The level identification in degree `i`, after tensoring, is the unique additive map
satisfying `Crystalline.tensorFormsCompletionLevelEquiv_tmul_ιMulti`.**

The equation pins the map on the tensors of wedges, and those generate the source as an abelian
group by `Crystalline.tensorExteriorPower_addMonoidHom_ext`.  So nothing about the choice of the
comparison `cmp` of [Stacks, Tag 07KK] can enter an argument about
`Crystalline.tensorFormsCompletionLevelEquiv` beyond that equation — in particular a naturality
square for it commutes as soon as both of its routes satisfy the equation. -/
public theorem tensorFormsCompletionLevelEquiv_unique (i : ℕ)
    (F : (M ⊗[AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B]
        dividedPowerDifferentialForms (A := A)
          (DividedPowers.completedDividedPowers J delta p hp).1 i) →+
      M ⊗[AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B]
        ↥(⋀[AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B]^i
          (AdicCompletion (DividedPowers.pAdicIdeal (A := B) p)
            (dividedPowerDifferentials (A := A) delta))))
    (hF : ∀ (m : M) (v : Fin i → dividedPowerDifferentials (A := A)
        (DividedPowers.completedDividedPowers J delta p hp).1),
      F (m ⊗ₜ exteriorPower.ιMulti
          (AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B) i v) =
        tensorExteriorPowerEquivOfBaseChange
          (completionDifferentialsReductionMap (A := A) J delta p
            (cmp.quotientSystem.cutoff + e))
          (isBaseChange_completionDifferentialsReductionMap (A := A) J delta p
            (cmp.quotientSystem.cutoff + e)) M i
          (m ⊗ₜ exteriorPower.ιMulti
            (AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B ⧸
              DividedPowers.pAdicIdeal
                (A := AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B) p ^
                (cmp.quotientSystem.cutoff + e)) i
            fun j ↦ completedDifferentialsLevelLinearEquiv (A := A) J delta p hp cmp e
              (Submodule.Quotient.mk (v j)))) :
    F = LinearMap.toAddMonoidHom
      (tensorFormsCompletionLevelEquiv (A := A) J delta p hp cmp e M i).toLinearMap :=
  tensorExteriorPower_addMonoidHom_ext fun m v ↦
    (hF m v).trans
      (tensorFormsCompletionLevelEquiv_tmul_ιMulti (A := A) J delta p hp cmp e M i m v).symm

end Level

end Crystalline

end
