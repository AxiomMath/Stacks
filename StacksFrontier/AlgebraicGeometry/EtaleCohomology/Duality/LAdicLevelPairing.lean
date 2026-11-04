module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LAdicPerfectPairing

/-!
# Perfect ℓ-adic pairings from perfect pairings of the levels of a tower

Let `M`, `M'` be finite `ℤ_p`-modules with projections `πₙ : M → Hₙ`, `π'ₙ : M' → H'ₙ` to the
levels of two towers (for instance `Hⁱ_c(X_k̄, F) → Hⁱ_c(X_k̄, Fₙ)`), such that, for one
exponent `K`,

* the kernel of `πₙ` is contained in `pⁿ⁺¹ M`, and
* `p^K Hₙ` is contained in the image of `πₙ`,

and likewise for `π'`. Given at every level a pairing `εₙ : Hₙ × H'ₙ → ℤ/pⁿ⁺¹` which is
nondegenerate on both sides, and endomorphisms `f`, `g` of `M`, `M'` lying over endomorphisms of
the levels under which `εₙ` scales by `c`, the pairing `B` on `M ⊗ ℚ_p × M' ⊗ ℚ_p` obtained by
compactness is perfect and satisfies `B (f v) (g w) = c B(v, w)`.

## Main results

* `Stacks.EtaleCohomology.LAdicPairing.exists_isPerfPair_extendScalars_of_levels`.
-/

@[expose] public noncomputable section

universe v

namespace Stacks.EtaleCohomology.LAdicPairing

variable {p : ℕ} [Fact p.Prime]

/-- If `π` has kernel in `pⁿ⁺¹ M` and `π (p^K a) = 0`, then `p^K a ∈ pⁿ⁺¹ M`. -/
private theorem exists_pow_smul_eq_of_map_nsmul_eq_zero {M H : Type*} [AddCommGroup M]
    [Module ℤ_[p] M] [AddCommGroup H] {n K : ℕ} (π : M →+ H)
    (hker : ∀ a, π a = 0 → ∃ a', a = (p ^ (n + 1)) • a') (a : M) (h0 : π ((p ^ K) • a) = 0) :
    ∃ a', (p : ℤ_[p]) ^ K • a = (p : ℤ_[p]) ^ (n + 1) • a' := by
  obtain ⟨a', ha'⟩ := hker _ h0
  exact ⟨a', by simpa only [← Nat.cast_pow, Nat.cast_smul_eq_nsmul] using ha'⟩

/-- **A perfect `ℚ_p`-pairing from perfect pairings of the levels of a tower.**  If the
projections `πₙ : M → Hₙ`, `π'ₙ : M' → H'ₙ` have kernel in `pⁿ⁺¹ M` (resp. `pⁿ⁺¹ M'`) and image
containing `p^K Hₙ` (resp. `p^K H'ₙ`), and the levels carry pairings `εₙ` with values in
`ℤ/pⁿ⁺¹`, nondegenerate on both sides and scaled by `c` under endomorphisms `φₙ`, `φ'ₙ` over `f`
and `g`, then there is a perfect pairing `B` of `M ⊗ ℚ_p` and `M' ⊗ ℚ_p` with
`B (f v) (g w) = c B(v, w)`. -/
theorem exists_isPerfPair_extendScalars_of_levels {M M' : ModuleCat.{v} ℤ_[p]}
    [Module.Finite ℤ_[p] M] [Module.Finite ℤ_[p] M'] (f : M ⟶ M) (g : M' ⟶ M') (c K : ℕ)
    {H H' : ℕ → Type*} [∀ n, AddCommGroup (H n)] [∀ n, AddCommGroup (H' n)]
    (π : ∀ n, M →+ H n) (π' : ∀ n, M' →+ H' n)
    (φ : ∀ n, H n →+ H n) (φ' : ∀ n, H' n →+ H' n)
    (hπ : ∀ n a, π n (f.hom a) = φ n (π n a)) (hπ' : ∀ n b, π' n (g.hom b) = φ' n (π' n b))
    (hker : ∀ n a, π n a = 0 → ∃ a', a = (p ^ (n + 1)) • a')
    (hker' : ∀ n b, π' n b = 0 → ∃ b', b = (p ^ (n + 1)) • b')
    (hrange : ∀ n (y : H n), ∃ a, π n a = (p ^ K) • y)
    (hrange' : ∀ n (y : H' n), ∃ b, π' n b = (p ^ K) • y)
    (ε : ∀ n, H n →+ H' n →+ ZMod (p ^ (n + 1)))
    (hl : ∀ n x, (∀ y, ε n x y = 0) → x = 0) (hr : ∀ n y, (∀ x, ε n x y = 0) → y = 0)
    (hε : ∀ n x y, ε n (φ n x) (φ' n y) = (c : ZMod (p ^ (n + 1))) * ε n x y) :
    ∃ B : (ModuleCat.extendScalars.{0, 0, v} (algebraMap ℤ_[p] ℚ_[p])).obj M →ₗ[ℚ_[p]]
        (ModuleCat.extendScalars.{0, 0, v} (algebraMap ℤ_[p] ℚ_[p])).obj M' →ₗ[ℚ_[p]] ℚ_[p],
      B.IsPerfPair ∧ ∀ v w,
        B (((ModuleCat.extendScalars.{0, 0, v} (algebraMap ℤ_[p] ℚ_[p])).map f).hom v)
          (((ModuleCat.extendScalars.{0, 0, v} (algebraMap ℤ_[p] ℚ_[p])).map g).hom w) =
          (c : ℚ_[p]) * B v w := by
  refine exists_isPerfPair_extendScalars_of_forall_zmodPow f g c K fun n => ?_
  cases n with
  | zero =>
    refine ⟨0, fun a _ => ⟨(p : ℤ_[p]) ^ K • a, by rw [pow_zero, one_smul]⟩,
      fun b _ => ⟨(p : ℤ_[p]) ^ K • b, by rw [pow_zero, one_smul]⟩, fun a b => ?_⟩
    simp only [AddMonoidHom.zero_apply, mul_zero]
  | succ m =>
    refine ⟨((ε m).compl₂ (π' m)).comp (π m), ?_, ?_, fun a b => ?_⟩
    · intro a ha
      refine exists_pow_smul_eq_of_map_nsmul_eq_zero _ (hker m) a (hl m _ fun y => ?_)
      obtain ⟨b, hb⟩ := hrange' m y
      simpa only [AddMonoidHom.comp_apply, AddMonoidHom.compl₂_apply, hb, map_nsmul,
        AddMonoidHom.nsmul_apply] using ha b
    · intro b hb
      refine exists_pow_smul_eq_of_map_nsmul_eq_zero _ (hker' m) b (hr m _ fun x => ?_)
      obtain ⟨a, ha⟩ := hrange m x
      simpa only [AddMonoidHom.comp_apply, AddMonoidHom.compl₂_apply, ha, map_nsmul,
        AddMonoidHom.nsmul_apply] using hb a
    · simp only [AddMonoidHom.comp_apply, AddMonoidHom.compl₂_apply, hπ, hπ']
      exact hε m _ _

end Stacks.EtaleCohomology.LAdicPairing
