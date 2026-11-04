module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CurveExtTower
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LAdicTowerLimit

/-!
# A tower of `ℤ_ℓ`-modules whose levels are `H¹(X, ℤ/ℓⁿ⁺¹)` of a curve looks free

Let `X` be a smooth proper curve over an algebraically closed field in which the prime `ℓ` is
invertible, and `H : ℕᵒᵖ ⥤ ModuleCat ℤ_ℓ` a tower with additive identifications
`Φₙ : H(n) ≃+ H¹(X, ℤ/ℓⁿ⁺¹) = Ext¹(ℤ/ℓⁿ⁺¹_X, ℤ/ℓⁿ⁺¹_X)` under which the transition `H(n+1) → H(n)`
becomes, after the change of level `Stacks.EtaleCohomology.LevelChange.extMap`, composition with
the reduction `ℤ/ℓⁿ⁺²_X ⟶ ℤ/ℓⁿ⁺¹_X` followed by an automorphism. Then the transitions are onto,
their kernels are `ℓⁿ⁺¹ H(n+1)`, and the `ℓᵏ⁺¹`-torsion of `H(n+k+1)` is divisible by `ℓⁿ⁺¹`
(`Stacks.EtaleCohomology.TowerLimit.surjective_tr_of_ext`, `exists_eq_smul_of_tr_eq_zero_of_ext`,
`exists_eq_smul_of_smul_eq_zero_of_ext`): the hypotheses under which `lim H(n)` is a free
`ℤ_ℓ`-lattice with reductions `H(n)` (`Stacks.EtaleCohomology.TowerLimit.free`). These come from
`Stacks.EtaleCohomology.LevelChange.surjective_comp_reduction_ext_one` and its companions.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite

universe u v

namespace Stacks.EtaleCohomology.TowerLimit

open LevelChange ExtensionTorsor

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [IsProper f] {ℓ : ℕ} [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : k))
  {F : ℕᵒᵖ ⥤ ModuleCat.{v} ℤ_[ℓ]}
  (Φ : ∀ n, F.obj (op n) ≃+ Ext (unitSheaf (X := X) (ℓ ^ (n + 1))) (unitSheaf (ℓ ^ (n + 1))) 1)
  (h : ∀ n, ℓ ^ (n + 1) ∣ ℓ ^ (n + 1 + 1))
  (ψ : ∀ n, (restrict X (h n)).obj (unitSheaf (ℓ ^ (n + 1))) ≅
    (restrict X (h n)).obj (unitSheaf (ℓ ^ (n + 1))))
  (hsq : ∀ n (x : F.obj (op (n + 1))),
    extMap X (h n) (unitSheaf (ℓ ^ (n + 1))) 1 (Φ n (tr F (Nat.le_succ n) x)) =
      (Φ (n + 1) x).comp (Ext.mk₀ (reduction X (h n) ≫ (ψ n).hom)) (add_zero 1))

omit [Fact (Nat.Prime ℓ)] in
/-- For a natural number `ℓ`, `ℓⁿ⁺¹ · ℓ = ℓⁿ⁺²`. -/
theorem pow_mul_pow_succ (n : ℕ) : ℓ ^ (n + 1) * ℓ ^ 1 = ℓ ^ (n + 1 + 1) := by
  rw [← pow_add]

/-- The `ℤ_ℓ`-action by `ℓᵐ` on a `ℤ_ℓ`-module is the `ℕ`-action. -/
theorem pow_smul_eq_nsmul {M : Type*} [AddCommGroup M] [Module ℤ_[ℓ] M] (m : ℕ) (x : M) :
    (ℓ : ℤ_[ℓ]) ^ m • x = ℓ ^ m • x := by
  rw [← Nat.cast_smul_eq_nsmul ℤ_[ℓ], Nat.cast_pow]

/-- If `e x = ℓᵐ • y` for an additive equivalence `e`, then `x` is `ℓᵐ` times an element. -/
private theorem exists_eq_pow_smul_of_equiv_eq_nsmul {M N : Type*} [AddCommGroup M]
    [Module ℤ_[ℓ] M] [AddCommGroup N] (e : M ≃+ N) {m : ℕ} {x : M} {y : N}
    (hy : e x = ℓ ^ m • y) : ∃ z, x = (ℓ : ℤ_[ℓ]) ^ m • z :=
  ⟨e.symm y, e.injective (by rw [pow_smul_eq_nsmul, map_nsmul, e.apply_symm_apply, hy])⟩

include f hℓ hsq in
/-- **The transitions are onto.** -/
theorem surjective_tr_of_ext (n : ℕ) : Function.Surjective (tr F (Nat.le_succ n)) := by
  intro z
  obtain ⟨y, hy⟩ := surjective_comp_reduction_ext_one f hℓ (pow_mul_pow_succ n) (h n)
    ((extMap X (h n) (unitSheaf (ℓ ^ (n + 1))) 1 (Φ n z)).comp (Ext.mk₀ (ψ n).inv) (add_zero 1))
  refine ⟨(Φ (n + 1)).symm y, (Φ n).injective ((extMap_bijective X (h n) _ 1).1 ?_)⟩
  rw [hsq, AddEquiv.apply_symm_apply, ← Ext.mk₀_comp_mk₀, ← Ext.comp_assoc_of_third_deg_zero]
  have hy' : y.comp (Ext.mk₀ (reduction X (h n))) (add_zero 1) =
      ((extMap X (h n) (unitSheaf (ℓ ^ (n + 1))) 1 (Φ n z)).comp (Ext.mk₀ (ψ n).inv)
        (add_zero 1)) :=
    hy
  rw [hy', Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, Iso.inv_hom_id, Ext.comp_mk₀_id]

include f hℓ hsq in
/-- **The kernel of `H(n+1) → H(n)` is `ℓⁿ⁺¹ H(n+1)`.** -/
theorem exists_eq_smul_of_tr_eq_zero_of_ext (n : ℕ) (x : F.obj (op (n + 1)))
    (hx : tr F (Nat.le_succ n) x = 0) : ∃ y, x = (ℓ : ℤ_[ℓ]) ^ (n + 1) • y := by
  have h0 : (Φ (n + 1) x).comp (Ext.mk₀ (reduction X (h n))) (add_zero 1) = 0 := by
    have := hsq n x
    rw [hx, map_zero, map_zero] at this
    have h1 := congrArg (fun w => w.comp (Ext.mk₀ (ψ n).inv) (add_zero 1)) this.symm
    simp only [Ext.zero_comp] at h1
    rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, Category.assoc, Iso.hom_inv_id,
      Category.comp_id] at h1
    exact h1
  obtain ⟨y', hy'⟩ := exists_eq_nsmul_of_comp_reduction_eq_zero f hℓ (pow_mul_pow_succ n) (h n)
    _ h0
  exact exists_eq_pow_smul_of_equiv_eq_nsmul _ hy'

include f hℓ Φ in
/-- **The `ℓᵏ⁺¹`-torsion of `H(n+k+1)` is divisible by `ℓⁿ⁺¹`.** -/
theorem exists_eq_smul_of_smul_eq_zero_of_ext (n k' : ℕ) (x : F.obj (op (n + k' + 1)))
    (hx : (ℓ : ℤ_[ℓ]) ^ (k' + 1) • x = 0) : ∃ y, x = (ℓ : ℤ_[ℓ]) ^ (n + 1) • y := by
  have hN : ℓ ^ (n + 1) * ℓ ^ (k' + 1) = ℓ ^ (n + k' + 1 + 1) := by
    rw [← pow_add]; ring_nf
  have hx' : ℓ ^ (k' + 1) • Φ (n + k' + 1) x = 0 := by
    rw [← map_nsmul, ← pow_smul_eq_nsmul, hx, map_zero]
  obtain ⟨y, hy⟩ := exists_eq_nsmul_of_nsmul_eq_zero f hℓ hN _ hx'
  exact exists_eq_pow_smul_of_equiv_eq_nsmul _ hy

end Stacks.EtaleCohomology.TowerLimit

end
