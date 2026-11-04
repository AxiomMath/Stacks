module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LocalMonodromyGroupTheory

/-!
# Invariants of a power of a tame generator are invariants of an open subgroup

Let `ρ : G → GL_r(ℤ_ℓ)` be continuous, `J ⊆ G` a compact subgroup (an open subgroup of inertia),
`t : J → ℤ_ℓ` a continuous homomorphism (the `ℓ`-adic tame character) whose kernel `ρ` kills,
and `T ∈ J` with `t σ ∈ ℤ_ℓ · t T` for every `σ ∈ J`.  For every `m > 0` this file finds `N`
such that every `σ ∈ J` with `ρ σ ∈ Γ(ℓ ^ N)` fixes every vector fixed by `ρ(T) ^ m`.

This is how Grothendieck's local monodromy theorem meets the geometry in the proof of Weil II,
Théorème 1.8.4: the linear algebra of
`Stacks.EtaleCohomology.exists_norm_sq_mul_pow_eq_of_tame_monodromy` needs weight bounds on the
invariants of `T ^ m` for every `m > 0`, i.e. on the local invariants after a finite extension of
the local field, and here those invariants contain the invariants of `J ∩ ρ⁻¹ Γ(ℓ ^ N)`, the
inertia group of the finite étale cover of the curve which trivializes `ρ` modulo `ℓ ^ N`.

## Main results

* `Stacks.EtaleCohomology.exists_forall_mulVec_eq_of_pow_mulVec_eq`.

## References

* P. Deligne, *La conjecture de Weil II*, Publ. Math. IHÉS 52 (1980), 1.7, 1.8.4.
* [Stacks Project, Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)
-/

@[expose] public noncomputable section

open Matrix

namespace Stacks.EtaleCohomology

variable {ℓ : ℕ} [Fact ℓ.Prime] {r : ℕ}
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ρ : G →* GL (Fin r) ℤ_[ℓ]}

omit [IsTopologicalGroup G] in
/-- The elements of `J` whose tame character lies in `ℤ_ℓ · t(T ^ m)` form an open set. -/
theorem isOpen_setOf_exists_toAdd_eq_mul {J : Subgroup G} (t : J →* Multiplicative ℤ_[ℓ])
    (ht : Continuous t) (T : J)
    (hgen : ∀ σ : J, ∃ c : ℤ_[ℓ], Multiplicative.toAdd (t σ) = c * Multiplicative.toAdd (t T))
    {m : ℕ} (hm : 0 < m) :
    IsOpen {σ : J | ∃ c : ℤ_[ℓ], Multiplicative.toAdd (t σ) =
      c * Multiplicative.toAdd (t (T ^ m))} := by
  by_cases h0 : Multiplicative.toAdd (t T) = 0
  · convert isOpen_univ
    ext σ
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    obtain ⟨c, hc⟩ := hgen σ
    exact ⟨0, by rw [hc, h0, mul_zero, zero_mul]⟩
  set a : ℤ_[ℓ] := Multiplicative.toAdd (t (T ^ m)) with ha
  have ha0 : a ≠ 0 := by
    rw [ha, map_pow, toAdd_pow, nsmul_eq_mul]
    exact mul_ne_zero (Nat.cast_ne_zero.2 hm.ne') h0
  have hset : {σ : J | ∃ c : ℤ_[ℓ], Multiplicative.toAdd (t σ) = c * a} =
      (fun σ => Multiplicative.toAdd (t σ)) ⁻¹'
        Metric.closedBall 0 ((ℓ : ℝ) ^ (-(a.valuation : ℤ))) := by
    ext σ
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Metric.mem_closedBall, dist_zero_right]
    rw [← pow_dvd_iff_norm_le]
    have hspec := PadicInt.unitCoeff_spec ha0
    set u := PadicInt.unitCoeff ha0
    refine ⟨fun ⟨c, hc⟩ => ⟨c * u, ?_⟩, fun ⟨y, hy⟩ => ⟨y * ↑u⁻¹, ?_⟩⟩
    · rw [hc]
      conv_lhs => rw [hspec]
      ring
    · rw [hy]
      conv_rhs => rw [hspec]
      rw [mul_assoc, Units.inv_mul_cancel_left, mul_comm]
  rw [hset]
  exact (IsUltrametricDist.isOpen_closedBall 0
    (zpow_pos (Nat.cast_pos.2 (Fact.out : ℓ.Prime).pos) _).ne').preimage
    (continuous_toAdd.comp ht)

/-- If `J` is compact, an open subgroup of `J` containing `J ∩ ker ρ` contains
`J ∩ ρ⁻¹ Γ(ℓ ^ N)` for some `N`. -/
theorem exists_forall_mem_of_mem_congruenceSubgroup (hρ : Continuous ρ) {J : Subgroup G}
    [CompactSpace J] {H : Subgroup J} (hH : IsOpen (H : Set J))
    (hker : ∀ τ : J, ρ τ = 1 → τ ∈ H) :
    ∃ N : ℕ, ∀ σ : J, ρ σ ∈ congruenceSubgroup ℓ r N → σ ∈ H := by
  set C : ℕ → Set J := fun N =>
    (H : Set J)ᶜ ∩ ((congruenceSubgroup ℓ r N).comap (ρ.comp J.subtype) : Set J)
  have hclosed : ∀ N, IsClosed (C N) := fun N =>
    hH.isClosed_compl.inter (Subgroup.isClosed_of_isOpen _
      ((isOpen_congruenceSubgroup N).preimage (hρ.comp continuous_subtype_val)))
  have hempty : ∃ N, C N = ∅ := by
    by_contra hne
    push Not at hne
    have hmono : ∀ N, C (N + 1) ⊆ C N := fun N τ hτ => ⟨hτ.1, fun i j =>
      (pow_dvd_pow _ (Nat.le_succ N)).trans (hτ.2 i j)⟩
    obtain ⟨τ, hτ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C
      hmono hne (hclosed 0).isCompact hclosed
    rw [Set.mem_iInter] at hτ
    have h1 : ρ τ = 1 := by
      refine Units.ext (Matrix.ext fun i j => ?_)
      have h0 : ((ρ τ : GL (Fin r) ℤ_[ℓ]) : Matrix (Fin r) (Fin r) ℤ_[ℓ]) i j -
          (1 : Matrix (Fin r) (Fin r) ℤ_[ℓ]) i j = 0 :=
        eq_zero_of_forall_pow_dvd fun N => (hτ N).2 i j
      simpa [sub_eq_zero] using h0
    exact (hτ 0).1 (hker τ h1)
  obtain ⟨N, hN⟩ := hempty
  exact ⟨N, fun σ hσ => of_not_not fun hσH => hN.subset ⟨hσH, hσ⟩⟩

/-- **Invariants of a power of a tame generator are the invariants of an open subgroup.**  In the
situation of `Stacks.EtaleCohomology.mulVec_eq_of_tame`, for every `m > 0` there is `N` such that
every `σ ∈ J` with `ρ σ ∈ Γ(ℓ ^ N)` fixes every integral vector fixed by `ρ(T) ^ m`. -/
public theorem exists_forall_mulVec_eq_of_pow_mulVec_eq (hρ : Continuous ρ) {J : Subgroup G}
    [CompactSpace J] (t : J →* Multiplicative ℤ_[ℓ]) (ht : Continuous t)
    (hker : ∀ τ : J, t τ = 1 → ρ τ = 1) (T : J)
    (hgen : ∀ σ : J, ∃ c : ℤ_[ℓ], Multiplicative.toAdd (t σ) = c * Multiplicative.toAdd (t T))
    {m : ℕ} (hm : 0 < m) :
    ∃ N : ℕ, ∀ σ : J, ρ σ ∈ congruenceSubgroup ℓ r N → ∀ v : Fin r → ℤ_[ℓ],
      (((ρ T ^ m : GL (Fin r) ℤ_[ℓ])) : Matrix (Fin r) (Fin r) ℤ_[ℓ]) *ᵥ v = v →
      ((ρ σ : GL (Fin r) ℤ_[ℓ]) : Matrix (Fin r) (Fin r) ℤ_[ℓ]) *ᵥ v = v := by
  set Z : Set J := {σ | ∀ v : Fin r → ℤ_[ℓ],
      (((ρ T ^ m : GL (Fin r) ℤ_[ℓ])) : Matrix (Fin r) (Fin r) ℤ_[ℓ]) *ᵥ v = v →
      ((ρ σ : GL (Fin r) ℤ_[ℓ]) : Matrix (Fin r) (Fin r) ℤ_[ℓ]) *ᵥ v = v}
  let Zg : Subgroup J :=
    { carrier := Z
      one_mem' := fun v _ => by simp
      mul_mem' := fun {a b} ha hb v hv => by
        rw [Subgroup.coe_mul, map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, hb v hv, ha v hv]
      inv_mem' := fun {a} ha v hv => by
        conv_lhs => rw [← ha v hv]
        rw [Subgroup.coe_inv, Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel,
          map_one, Units.val_one, Matrix.one_mulVec] }
  have hsub : {σ : J | ∃ c : ℤ_[ℓ], Multiplicative.toAdd (t σ) =
      c * Multiplicative.toAdd (t (T ^ m))} ⊆ Z := by
    rintro σ ⟨c, hc⟩ v hv
    have hv' : (((ρ (T ^ m : J) : GL (Fin r) ℤ_[ℓ])) : Matrix (Fin r) (Fin r) ℤ_[ℓ]) *ᵥ v = v := by
      simpa [map_pow] using hv
    refine mulVec_eq_of_forall_exists_mul_pow_mem (h := ρ (T ^ m : J)) (fun N => ?_) hv'
    obtain ⟨k, hk⟩ := exists_pow_mul_mem_congruenceSubgroup hρ t ht hker (T ^ m) σ c hc N
    exact ⟨k, by simpa [map_mul, map_pow, map_inv] using hk⟩
  let Jm : Subgroup J :=
    { carrier := {σ : J | ∃ c : ℤ_[ℓ], Multiplicative.toAdd (t σ) =
        c * Multiplicative.toAdd (t (T ^ m))}
      mul_mem' := fun ⟨c, hc⟩ ⟨d, hd⟩ => ⟨c + d, by rw [map_mul, toAdd_mul, hc, hd, add_mul]⟩
      one_mem' := ⟨0, by simp⟩
      inv_mem' := fun ⟨c, hc⟩ => ⟨-c, by rw [map_inv, toAdd_inv, hc, neg_mul]⟩ }
  exact exists_forall_mem_of_mem_congruenceSubgroup hρ
    (Subgroup.isOpen_mono (H₁ := Jm) (H₂ := Zg) hsub
      (isOpen_setOf_exists_toAdd_eq_mul t ht T hgen hm))
    fun τ hτ v _ => by rw [hτ, Units.val_one, Matrix.one_mulVec]

end Stacks.EtaleCohomology

end
