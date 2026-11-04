module

public import StacksFrontier.AlgebraicGeometry.Crystalline.ModuleDifferentials.CompletionLevelSpan
public import StacksFrontier.AlgebraicGeometry.Crystalline.ModuleDifferentials.LevelFormsComposite

/-!
# Level independence of the level identification of [Stacks, Tag 07KK]

`Crystalline.completedDifferentialsLevelEquivAt` identifies

`Ω_{B̂/A,γ̂} / pᵏ  ≃+  Ω̂_{B/A,δ} / pᵏ`

at each level `k = cutoff + e` of a `Crystalline.DifferentialsCompletionComparison`, and
`Crystalline.tensorFormsCompletionLevelEquivAt` is its degree-`i` form after tensoring with a
module `M` over `B̂ ⧸ (p)^k`. The source `M ⊗_{B̂} Ωⁱ_{B̂/A,γ̂}` and the target
`M ⊗_{B̂} ⋀ⁱ_{B̂} Ω̂_{B/A,δ}` of the degree-`i` form do not depend on `k`, and neither does the
map: any two levels of one comparison give the same additive map.

## Main results

* `Crystalline.completedDifferentialsLevelEquiv_transition`: for `e ≤ e'`, the level
  identifications at `cutoff + e'` and `cutoff + e` commute with the transition maps.
* `Crystalline.completedDifferentialsLevelEquiv_mk_of_le` and
  `Crystalline.completedDifferentialsLevelEquivAt_mk_of_le`: a witness for the class of a
  differential at a larger level is a witness at a smaller one.
* `Crystalline.tensorFormsCompletionLevelEquivAt_level_independent_of_le` and
  `Crystalline.tensorFormsCompletionLevelEquivAt_level_independent`: the degree-`i`
  identification after tensoring is the same map at any two levels of one comparison.
* `Crystalline.tensorFormsLevelComposite_level_independent`: the same for the composite
  `Crystalline.tensorFormsLevelComposite` of three comparisons.

## References

* [Stacks Project, Lemma 60.20.1, Tag 07KK](https://stacks.math.columbia.edu/tag/07KK)
* [Stacks Project, Tag 07LF](https://stacks.math.columbia.edu/tag/07LF)
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace Crystalline

section Independence

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable (J : Ideal B) (delta : DividedPowers J) (p : ℕ)

/-! ### The level identification across two levels -/

variable (hp : IsNilpotent (Ideal.Quotient.mk J (p : B)))

/-- For `e ≤ e'`, the level identification of [Stacks, Tag 07KK] at `cutoff + e'` followed by the
transition of the completion `Ω̂_{B/A,δ}` down to `cutoff + e` is the transition of `Ω_{B̂/A,γ̂}`
followed by the level identification at `cutoff + e`. -/
public theorem completedDifferentialsLevelEquiv_transition
    (cmp : DifferentialsCompletionComparison (A := A) J delta p hp) {e e' : ℕ} (h : e ≤ e') :
    (AdicCompletion.transitionMap
        (DividedPowers.pAdicIdeal
          (A := AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B) p)
        (AdicCompletion (DividedPowers.pAdicIdeal (A := B) p)
          (dividedPowerDifferentials (A := A) delta))
        (Nat.add_le_add_left h cmp.quotientSystem.cutoff)).comp
      (completedDifferentialsLevelLinearEquiv (A := A) J delta p hp cmp e').toLinearMap =
    (completedDifferentialsLevelLinearEquiv (A := A) J delta p hp cmp e).toLinearMap.comp
      (AdicCompletion.transitionMap
        (DividedPowers.pAdicIdeal
          (A := AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B) p)
        (dividedPowerDifferentials (A := A)
          (DividedPowers.completedDividedPowers J delta p hp).1)
        (Nat.add_le_add_left h cmp.quotientSystem.cutoff)) :=
  completedDifferentialsModPow_ext J delta p hp _ fun b ↦
    (congrArg _ (completedDifferentialsLevelEquiv_d (A := A) J delta p hp cmp e' b)).trans
      (completedDifferentialsLevelEquiv_d (A := A) J delta p hp cmp e b).symm

/-- If the class of the differential `v` of `B̂` modulo `p^{cutoff+e'}` is sent by the level
identification to the class of the element `w` of the completion `Ω̂_{B/A,δ}`, then the same holds
modulo `p^{cutoff+e}` for every `e ≤ e'`. -/
public theorem completedDifferentialsLevelEquiv_mk_of_le
    (cmp : DifferentialsCompletionComparison (A := A) J delta p hp) {e e' : ℕ} (h : e ≤ e')
    (v : dividedPowerDifferentials (A := A)
      (DividedPowers.completedDividedPowers J delta p hp).1)
    (w : AdicCompletion (DividedPowers.pAdicIdeal (A := B) p)
      (dividedPowerDifferentials (A := A) delta))
    (hw : completedDifferentialsLevelEquiv (A := A) J delta p hp cmp e'
        (Submodule.Quotient.mk v) = Submodule.Quotient.mk w) :
    completedDifferentialsLevelEquiv (A := A) J delta p hp cmp e
      (Submodule.Quotient.mk v) = Submodule.Quotient.mk w := by
  exact (DFunLike.congr_fun
    (completedDifferentialsLevelEquiv_transition (A := A) J delta p hp cmp h)
    (Submodule.Quotient.mk v)).symm.trans (congrArg _ hw)

/-- If the level identification `Crystalline.completedDifferentialsLevelEquivAt` at the level `k'`
sends the class of `v` to the class of `w`, then so does the one at any level `k ≤ k'`. -/
public theorem completedDifferentialsLevelEquivAt_mk_of_le
    (cmp : DifferentialsCompletionComparison (A := A) J delta p hp) (e k e' k' : ℕ)
    (hk : cmp.quotientSystem.cutoff + e = k) (hk' : cmp.quotientSystem.cutoff + e' = k')
    (hle : k ≤ k')
    (v : dividedPowerDifferentials (A := A)
      (DividedPowers.completedDividedPowers J delta p hp).1)
    (w : AdicCompletion (DividedPowers.pAdicIdeal (A := B) p)
      (dividedPowerDifferentials (A := A) delta))
    (hw : completedDifferentialsLevelEquivAt (A := A) J delta p hp cmp e' k' hk'
        (Submodule.Quotient.mk v) = Submodule.Quotient.mk w) :
    completedDifferentialsLevelEquivAt (A := A) J delta p hp cmp e k hk
      (Submodule.Quotient.mk v) = Submodule.Quotient.mk w := by
  subst hk hk'
  exact completedDifferentialsLevelEquiv_mk_of_le (A := A) J delta p hp cmp
    (Nat.le_of_add_le_add_left hle) v w hw

/-! ### Level independence in degree `i` -/

section Degree

variable (cmp : DifferentialsCompletionComparison (A := A) J delta p hp) (e k e' k' : ℕ)
variable (hk : cmp.quotientSystem.cutoff + e = k) (hk' : cmp.quotientSystem.cutoff + e' = k')
variable (M : Type*) [AddCommGroup M]
  [Module (AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B) M]
  [Module (AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B ⧸
    DividedPowers.pAdicIdeal
      (A := AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B) p ^ k) M]
  [IsScalarTower (AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B)
    (AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B ⧸
      DividedPowers.pAdicIdeal
        (A := AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B) p ^ k) M]
  [Module (AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B ⧸
    DividedPowers.pAdicIdeal
      (A := AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B) p ^ k') M]
  [IsScalarTower (AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B)
    (AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B ⧸
      DividedPowers.pAdicIdeal
        (A := AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B) p ^ k') M]

/-- For levels `k ≤ k'` of one comparison, `Crystalline.tensorFormsCompletionLevelEquivAt` at `k`
and at `k'` are the same additive map. -/
public theorem tensorFormsCompletionLevelEquivAt_level_independent_of_le (hle : k ≤ k') (i : ℕ) :
    (tensorFormsCompletionLevelEquivAt (A := A) J delta p hp cmp e k hk M
        i).toLinearMap.toAddMonoidHom =
      (tensorFormsCompletionLevelEquivAt (A := A) J delta p hp cmp e' k' hk' M
        i).toLinearMap.toAddMonoidHom := by
  refine tensorExteriorPower_addMonoidHom_ext fun m v ↦ ?_
  have hex : ∀ j : Fin i, ∃ y : AdicCompletion (DividedPowers.pAdicIdeal (A := B) p)
      (dividedPowerDifferentials (A := A) delta),
      completedDifferentialsLevelEquivAt (A := A) J delta p hp cmp e' k' hk'
        (Submodule.Quotient.mk (v j)) = Submodule.Quotient.mk y := fun j ↦
    (Submodule.Quotient.mk_surjective _ _).imp fun _ ↦ Eq.symm
  choose w hw using hex
  exact (tensorFormsCompletionLevelEquivAt_tmul_ιMulti_of_mk (A := A) J delta p hp cmp e k hk M i
      m v w fun j ↦ completedDifferentialsLevelEquivAt_mk_of_le (A := A) J delta p hp cmp e k e'
        k' hk hk' hle (v j) (w j) (hw j)).trans
    (tensorFormsCompletionLevelEquivAt_tmul_ιMulti_of_mk (A := A) J delta p hp cmp e' k' hk' M i
      m v w hw).symm

/-- For any two levels `k` and `k'` of one comparison of [Stacks, Tag 07KK],
`Crystalline.tensorFormsCompletionLevelEquivAt` at `k` and at `k'` is the same additive map

`M ⊗_{B̂} Ωⁱ_{B̂/A,γ̂}  →  M ⊗_{B̂} ⋀ⁱ_{B̂} Ω̂_{B/A,δ}`

where `M` is a module over both `B̂/pᵏ` and `B̂/p^{k'}`. -/
public theorem tensorFormsCompletionLevelEquivAt_level_independent (i : ℕ) :
    (tensorFormsCompletionLevelEquivAt (A := A) J delta p hp cmp e k hk M
        i).toLinearMap.toAddMonoidHom =
      (tensorFormsCompletionLevelEquivAt (A := A) J delta p hp cmp e' k' hk' M
        i).toLinearMap.toAddMonoidHom := by
  rcases le_total k k' with hle | hle
  · exact tensorFormsCompletionLevelEquivAt_level_independent_of_le (A := A) J delta p hp cmp e k
      e' k' hk hk' M hle i
  · exact (tensorFormsCompletionLevelEquivAt_level_independent_of_le (A := A) J delta p hp cmp e'
      k' e k hk' hk M hle i).symm

end Degree

end Independence

/-! ### Level independence of the composite of the three comparisons -/

section Composite

variable {A : Type u} {E : Type v} {B : Type w} [CommRing A] [CommRing E] [CommRing B]
  [Algebra A E] [Algebra A B]
variable (Jenv : Ideal E) (deltaenv : DividedPowers Jenv) (p : ℕ)
variable (hpn : IsNilpotent (Ideal.Quotient.mk Jenv (p : E)))
variable (cmp : DifferentialsCompletionComparison (A := A) Jenv deltaenv p hpn)
variable (c : ℕ)
variable (hcontained : DividedPowers.pAdicIdeal
    (A := AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E) p ^ c ≤
  DividedPowers.completionIdeal Jenv p hpn)
variable (hstable : (DividedPowers.completedDividedPowers Jenv deltaenv p hpn).1.IsSubDPIdeal
  (DividedPowers.pAdicIdeal
    (A := AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E) p ^ c))
variable (J : Ideal B) (delta : DividedPowers J)
variable (f : B ≃ₐ[A] (AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E ⧸
    DividedPowers.pAdicIdeal
      (A := AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E) p ^ c))
variable (hf : delta.IsDPMorphism
  (completedLevelDividedPowers Jenv deltaenv p hpn c hcontained hstable) f.toAlgHom.toRingHom)
variable (hJ : J.map f.toAlgHom.toRingHom =
  (DividedPowers.completionIdeal Jenv p hpn).map
    (Ideal.Quotient.mk (DividedPowers.pAdicIdeal
      (A := AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E) p ^ c)))
variable (e k e' k' : ℕ)
variable (hk : cmp.quotientSystem.cutoff + e = k) (hk' : cmp.quotientSystem.cutoff + e' = k')
variable (M : Type*) [AddCommGroup M] [Module B M]
  [Module (AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E) M]
  [Module (AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E ⧸
    DividedPowers.pAdicIdeal
      (A := AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E) p ^ c) M]
  [IsScalarTower (AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E)
    (AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E ⧸
      DividedPowers.pAdicIdeal
        (A := AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E) p ^ c) M]
  [Module (AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E ⧸
    DividedPowers.pAdicIdeal
      (A := AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E) p ^ k) M]
  [IsScalarTower (AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E)
    (AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E ⧸
      DividedPowers.pAdicIdeal
        (A := AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E) p ^ k) M]
  [Module (AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E ⧸
    DividedPowers.pAdicIdeal
      (A := AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E) p ^ k') M]
  [IsScalarTower (AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E)
    (AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E ⧸
      DividedPowers.pAdicIdeal
        (A := AdicCompletion (DividedPowers.pAdicIdeal (A := E) p) E) p ^ k') M]
variable (hsm : ∀ (b : B) (m : M), b • m = f b • m)

/-- For any two levels `k` and `k'` of one comparison, the composite
`Crystalline.tensorFormsLevelComposite` at `k` and at `k'` is the same additive map. -/
public theorem tensorFormsLevelComposite_level_independent (i : ℕ) :
    (tensorFormsLevelComposite Jenv deltaenv p hpn cmp c hcontained hstable J delta f hf hJ e k
        hk M hsm i).toAddMonoidHom =
      (tensorFormsLevelComposite Jenv deltaenv p hpn cmp c hcontained hstable J delta f hf hJ e'
        k' hk' M hsm i).toAddMonoidHom :=
  AddMonoidHom.ext fun z ↦ DFunLike.congr_fun
    (tensorFormsCompletionLevelEquivAt_level_independent (A := A) Jenv deltaenv p hpn cmp e k e'
      k' hk hk' M i)
    (tensorFormsLevelEquiv (DividedPowers.completionIdeal Jenv p hpn)
      (DividedPowers.completedDividedPowers Jenv deltaenv p hpn).1 p c hcontained hstable M i
      ((tensorFormsEquivOfAlgEquiv delta
        (completedLevelDividedPowers Jenv deltaenv p hpn c hcontained hstable) f hf hJ hsm i).1 z))

end Composite

end Crystalline

end
