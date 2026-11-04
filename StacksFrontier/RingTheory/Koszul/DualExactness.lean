module

public import StacksFrontier.RingTheory.Koszul.Semilinear
public import StacksFrontier.RingTheory.Koszul.TorComparison.TopHomology

/-!
# Exactness of the dual of the Koszul complex

Let `R` be a commutative ring, `f₁, …, f_n ∈ R` and `E = Rⁿ`. Applying `Hom_R(-, R)` to the
Koszul complex `K_•(f)` gives a cochain complex with `Hom_R(⋀ᵏ E, R)` in degree `k` and
differential `ψ ↦ ψ ∘ d_k` given by precomposition with the Koszul differential. This file
proves that this dual complex is exact in every degree `< n` when `f` is Koszul-regular, and
that its cohomology in the top degree `n` is `Hom_R(⋀ⁿ E, R) / J · Hom_R(⋀ⁿ E, R)`, where
`J = (f₁, …, f_n)`; the latter holds for every sequence.

The mechanism is the self-duality of the Koszul complex. The top exterior power `⋀ⁿ E` is free
of rank one (`Koszul.topEquiv`), so multiplication in the exterior algebra followed by
`Koszul.topEquiv` gives, for `a + b = n`, a pairing `⋀ᵃ E × ⋀ᵇ E → R`, and hence a map
`θ : ⋀ᵇ E → Hom_R(⋀ᵃ E, R)`. On the standard bases it sends the wedge `e_T` of a `b`-subset `T`
to a sign times the coordinate functional of the complement of `T`, so `θ` is bijective. Since
contraction is an antiderivation and a product landing in `⋀ⁿ⁺¹ E = 0` vanishes, `θ` intertwines
precomposition with the Koszul differential and the Koszul differential itself, up to the sign
`(-1)ᵃ`. Exactness of the dual complex in degree `k` is thereby exactness of `K_•(f)` in
homological degree `n - k`.

## Main definitions

* `Koszul.wedgePairing`: the map `⋀ᵇ(Rⁿ) → Hom_R(⋀ᵃ(Rⁿ), R)`, `ω ↦ (α ↦ top(α ∧ ω))`, for
  `a + b = n`.

## Main results

* `Koszul.wedgePairing_bijective`: the pairing is perfect.
* `Koszul.wedgePairing_d`: it intertwines the Koszul differential on both sides, up to sign.
* `Koszul.dual_d_zero_eq_zero`: for `f` Koszul-regular of positive length, a functional on
  `⋀⁰` killed by precomposition with `d₀` is zero.
* `Koszul.exists_dual_d_eq_of_comp_eq_zero`: for `f` Koszul-regular, the dual complex is exact
  in the degrees `1, …, n - 1`.
* `Koszul.mem_span_iff_exists_dual_d_eq`: a functional on the top exterior power is in the image
  of the dual differential exactly when its values lie in `(f₁, …, f_n)`.

## References

* [Stacks Project, Tag 0BQZ](https://stacks.math.columbia.edu/tag/0BQZ)
* [Stacks Project, Tag 0623](https://stacks.math.columbia.edu/tag/0623)
-/

@[expose] public noncomputable section

open scoped ExteriorAlgebra
open CategoryTheory

universe u

namespace Set.powersetCard

variable {α : Type*} [DecidableEq α] [Fintype α] {m n : ℕ}

/-- When the two cardinalities add up to the cardinality of the ambient type, an `m`-subset is
disjoint from an `n`-subset exactly when it is its complement. -/
theorem disjoint_iff_eq_compl (hm : m + n = Fintype.card α) (s : powersetCard α m)
    (t : powersetCard α n) : Disjoint s.val t.val ↔ s = compl hm t := by
  constructor
  · intro h
    apply Subtype.ext
    change s.val = t.valᶜ
    refine Finset.eq_of_subset_of_card_le (le_compl_iff_disjoint_right.mpr h) ?_
    rw [Finset.card_compl, card_eq s, card_eq t]
    omega
  · rintro rfl
    exact disjoint_compl_left

end Set.powersetCard

namespace Koszul

open Set.powersetCard

variable {R : Type u} [CommRing R]

/-! ### The wedge pairing on the exterior powers of `Rⁿ` -/

section Pairing

variable {n : ℕ}

/-- Elements of the exterior algebra of `Rⁿ` of degree `n + 1` vanish. -/
theorem eq_zero_of_mem_exteriorPower_succ {x : ExteriorAlgebra R (Fin n → R)}
    (hx : x ∈ ⋀[R]^(n + 1) (Fin n → R)) : x = 0 := by
  have : Subsingleton (⋀[R]^(n + 1) (Fin n → R)) :=
    exteriorPower.subsingleton_of_span_eq_top_of_card_lt
      (Pi.basisFun R (Fin n)) (Pi.basisFun R (Fin n)).span_eq (n + 1) (by simp)
  exact congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : ⋀[R]^(n + 1) (Fin n → R)) 0)

/-- The wedge pairing: for `a + b = n`, the element `ω ∈ ⋀ᵇ(Rⁿ)` is sent to the functional
`α ↦ top(α ∧ ω)` on `⋀ᵃ(Rⁿ)`, where `top = Koszul.topEquiv` identifies `⋀ⁿ(Rⁿ)` with `R`. -/
def wedgePairing {a b : ℕ} (hab : a + b = n) :
    (⋀[R]^b (Fin n → R)) →ₗ[R] Module.Dual R (⋀[R]^a (Fin n → R)) :=
  LinearMap.mk₂ R
    (fun ω α => topEquiv R n ⟨(α : ExteriorAlgebra R (Fin n → R)) * ω, by
      have h := ExteriorAlgebra.mul_mem_exteriorPower α.2 ω.2
      rwa [hab] at h⟩)
    (fun ω₁ ω₂ α => by rw [← map_add]; congr 1; ext; simp [mul_add])
    (fun c ω α => by change _ = c • _; rw [← map_smul]; congr 1; ext; simp)
    (fun ω α₁ α₂ => by rw [← map_add]; congr 1; ext; simp [add_mul])
    (fun c ω α => by change _ = c • _; rw [← map_smul]; congr 1; ext; simp)

/-- The wedge pairing evaluated through the product in the exterior algebra: if `α ∧ ω` is the
element `y` of the top exterior power, the pairing of `ω` and `α` is `top(y)`. -/
theorem wedgePairing_apply_of_mul_eq {a b : ℕ} (hab : a + b = n) (ω : ⋀[R]^b (Fin n → R))
    (α : ⋀[R]^a (Fin n → R)) {y : ⋀[R]^n (Fin n → R)}
    (h : (α : ExteriorAlgebra R (Fin n → R)) * ω = y) :
    wedgePairing hab ω α = topEquiv R n y :=
  congrArg (topEquiv R n) (Subtype.ext h)

/-- **The wedge pairing intertwines the Koszul differentials.** For `β ∈ ⋀ᵃ⁺¹` and `ω ∈ ⋀ᵇ⁺¹`
with `a + b + 1 = n`, `top(dβ ∧ ω) = (-1)ᵃ · top(β ∧ dω)`: the product `β ∧ ω` lies in
`⋀ⁿ⁺¹(Rⁿ) = 0`, and contraction is an antiderivation. -/
theorem wedgePairing_d {a b : ℕ} (h₁ : a + (b + 1) = n) (h₂ : a + 1 + b = n)
    (φ : Module.Dual R (Fin n → R)) (β : ⋀[R]^(a + 1) (Fin n → R))
    (ω : ⋀[R]^(b + 1) (Fin n → R)) :
    wedgePairing h₁ ω (d φ a β) = (-1) ^ a * wedgePairing h₂ (d φ b ω) β := by
  have hz : (β : ExteriorAlgebra R (Fin n → R)) * ω = 0 := by
    have h := ExteriorAlgebra.mul_mem_exteriorPower β.2 ω.2
    rw [show a + 1 + (b + 1) = n + 1 by omega] at h
    exact eq_zero_of_mem_exteriorPower_succ h
  have hc := contraction_mul_of_mem φ (a + 1) β.2 (ω : ExteriorAlgebra R (Fin n → R))
  rw [hz, map_zero, pow_succ, mul_neg_one, neg_smul, eq_comm, add_neg_eq_zero] at hc
  rw [← smul_eq_mul, ← map_smul]
  refine wedgePairing_apply_of_mul_eq h₁ ω _ (?_ : _ = (((-1 : R) ^ a • β :
    ⋀[R]^(a + 1) (Fin n → R)) : ExteriorAlgebra R (Fin n → R)) * (d φ b ω :
      ExteriorAlgebra R (Fin n → R)))
  rw [Submodule.coe_smul, smul_mul_assoc, d_apply_coe, d_apply_coe, hc]

/-- `Koszul.topEquiv` is `1` on the unique element of the standard basis of `⋀ⁿ(Rⁿ)`. -/
theorem topEquiv_basis_exteriorPower (u : Set.powersetCard (Fin n) n) :
    topEquiv R n ((Pi.basisFun R (Fin n)).exteriorPower n u) = 1 := by
  obtain rfl : u = topIndex n :=
    Subtype.ext (Finset.eq_univ_of_card _ (by rw [card_eq u, Fintype.card_fin]))
  rw [exteriorPower.basis_apply]
  exact exteriorPower.ιMultiDual_apply_diag R n _ _

/-- **The wedge pairing on the standard bases.** The pairing of the basis wedges `e_t` and
`e_s` is the sign of the shuffle sorting `s ⊔ t` when `s` and `t` are disjoint, and `0`
otherwise. -/
theorem wedgePairing_basis {a b : ℕ} (hab : a + b = n) (s : Set.powersetCard (Fin n) a)
    (t : Set.powersetCard (Fin n) b) :
    wedgePairing hab ((Pi.basisFun R (Fin n)).exteriorPower b t)
        ((Pi.basisFun R (Fin n)).exteriorPower a s) =
      if h : Disjoint s.val t.val then (((permOfDisjoint h).sign : ℤ) : R) else 0 := by
  subst hab
  split_ifs with h
  · rw [wedgePairing_apply_of_mul_eq rfl _ _ (y := ((permOfDisjoint h).sign : ℤ) •
      (Pi.basisFun R (Fin (a + b))).exteriorPower (a + b) (disjUnion h)), map_zsmul,
      topEquiv_basis_exteriorPower, zsmul_eq_mul, mul_one]
    simp only [exteriorPower.basis_apply, exteriorPower.ιMulti_family_apply_coe,
      ExteriorAlgebra.ιMulti_family_mul_of_disjoint R _ s t h, Units.smul_def,
      Submodule.coe_smul_of_tower]
  · rw [wedgePairing_apply_of_mul_eq rfl _ _ (y := 0), map_zero]
    simp only [exteriorPower.basis_apply, exteriorPower.ιMulti_family_apply_coe,
      ExteriorAlgebra.ιMulti_family_mul_of_not_disjoint R _ s t h, Submodule.coe_zero]

/-- **The wedge pairing is perfect**: for `a + b = n`, the map
`⋀ᵇ(Rⁿ) → Hom_R(⋀ᵃ(Rⁿ), R)` is bijective. It sends the basis wedge `e_t` to a sign times the
coordinate functional of the complement of `t`, hence a basis to a basis. -/
theorem wedgePairing_bijective {a b : ℕ} (hab : a + b = n) :
    Function.Bijective (wedgePairing (R := R) hab) := by
  classical
  have hc : a + b = Fintype.card (Fin n) := by rwa [Fintype.card_fin]
  have hd : ∀ t : Set.powersetCard (Fin n) b, Disjoint (compl hc t).val t.val :=
    fun t => (disjoint_iff_eq_compl hc _ _).2 rfl
  let w : Set.powersetCard (Fin n) b → Rˣ := fun t =>
    Units.map (Int.castRingHom R).toMonoidHom (Equiv.Perm.sign (permOfDisjoint (hd t)))
  let B' : Module.Basis (Set.powersetCard (Fin n) b) R
      (Module.Dual R (⋀[R]^a (Fin n → R))) :=
    (((Pi.basisFun R (Fin n)).exteriorPower a).dualBasis.reindex (compl hc).symm).unitsSMul w
  have key : wedgePairing hab =
      (((Pi.basisFun R (Fin n)).exteriorPower b).equiv B' (Equiv.refl _)).toLinearMap := by
    refine ((Pi.basisFun R (Fin n)).exteriorPower b).ext fun t => ?_
    rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply, Equiv.refl_apply]
    refine ((Pi.basisFun R (Fin n)).exteriorPower a).ext fun s => ?_
    rw [wedgePairing_basis, Module.Basis.unitsSMul_apply, Units.smul_def, LinearMap.smul_apply,
      Module.Basis.reindex_apply, Equiv.symm_symm, Module.Basis.dualBasis_apply_self, smul_eq_mul]
    by_cases hs : s = compl hc t
    · subst hs
      rw [dite_eq_left (hd t), ite_eq_left rfl, mul_one]
      simp [w]
    · rw [dite_eq_right (fun h => hs ((disjoint_iff_eq_compl hc _ _).1 h)), ite_eq_right hs,
        mul_zero]
  rw [key]
  exact LinearEquiv.bijective _

/-- A functional `top(- ∧ ω)` killed by precomposition with the Koszul differential comes from
an `ω` killed by the Koszul differential: this is `Koszul.wedgePairing_d` combined with the
injectivity of the next wedge pairing. -/
theorem d_eq_zero_of_wedgePairing_comp_d_eq_zero {a b : ℕ} (h₁ : a + (b + 1) = n)
    (h₂ : a + 1 + b = n) (φ : Module.Dual R (Fin n → R)) (ω : ⋀[R]^(b + 1) (Fin n → R))
    (h : wedgePairing h₁ ω ∘ₗ d φ a = 0) : d φ b ω = 0 := by
  apply (wedgePairing_bijective h₂).1
  rw [map_zero]
  refine LinearMap.ext fun β => ?_
  have hβ := LinearMap.congr_fun h β
  rw [LinearMap.comp_apply, wedgePairing_d h₁ h₂, LinearMap.zero_apply] at hβ
  rw [LinearMap.zero_apply]
  exact ((isUnit_neg_one (α := R)).pow a).mul_right_eq_zero.1 hβ

end Pairing

/-! ### Koszul regularity as exactness -/

/-- For a Koszul-regular sequence, every cycle of the Koszul complex in positive degree is a
boundary. -/
theorem exists_d_eq_of_isKoszulRegular {r : ℕ} {f : Fin r → R} (hf : IsKoszulRegular f) (p : ℕ)
    (z : ⋀[R]^(p + 1) (Fin r → R)) (hz : d (seqDual f) p z = 0) :
    ∃ w : ⋀[R]^(p + 2) (Fin r → R), d (seqDual f) (p + 1) w = z := by
  have he := (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr
    (hf (p + 1) (Nat.succ_ne_zero p))
  rw [HomologicalComplex.exactAt_iff' _ (p + 2) (p + 1) p (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff_ker_sub_range] at he
  simp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor'_obj_g,
    HomologicalComplex.shortComplexFunctor'_obj_f, seqComplex_d] at he
  exact he hz

/-! ### The dual Koszul complex -/

/-- **The dual Koszul complex is exact in degree `0`.** For a Koszul-regular sequence of
positive length `n`, a functional on `⋀⁰(Rⁿ)` killed by precomposition with the Koszul
differential `d₀` is zero. -/
theorem dual_d_zero_eq_zero {n : ℕ} (f : Fin n → R) (hf : IsKoszulRegular f) (hn : 0 < n)
    (φ : (⋀[R]^0 (Fin n → R)) →ₗ[R] R) (h : φ ∘ₗ d (seqDual f) 0 = 0) : φ = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h₀ : 0 + (m + 1) = m + 1 := by omega
  obtain ⟨ω, rfl⟩ := (wedgePairing_bijective h₀).2 φ
  obtain ⟨η, rfl⟩ := exists_d_eq_of_isKoszulRegular hf m ω
    (d_eq_zero_of_wedgePairing_comp_d_eq_zero h₀ (by omega) (seqDual f) ω h)
  obtain rfl : η = 0 := Subtype.ext (eq_zero_of_mem_exteriorPower_succ η.2)
  rw [map_zero, map_zero]

/-- **The dual Koszul complex is exact in degrees `1, …, n - 1`.** For a Koszul-regular
sequence of length `n` and `k + 1 < n`, a functional on `⋀ᵏ⁺¹(Rⁿ)` killed by precomposition with
the Koszul differential `d_{k+1}` is the precomposition of a functional on `⋀ᵏ(Rⁿ)` with `d_k`. -/
theorem exists_dual_d_eq_of_comp_eq_zero {n : ℕ} (f : Fin n → R) (hf : IsKoszulRegular f)
    {k : ℕ} (hk : k + 1 < n) (φ : (⋀[R]^(k + 1) (Fin n → R)) →ₗ[R] R)
    (h : φ ∘ₗ d (seqDual f) (k + 1) = 0) :
    ∃ ψ : (⋀[R]^k (Fin n → R)) →ₗ[R] R, ψ ∘ₗ d (seqDual f) k = φ := by
  obtain ⟨p, hp⟩ : ∃ p, n = k + 2 + p := ⟨n - (k + 2), by omega⟩
  have h₀ : k + (p + 1 + 1) = n := by omega
  have h₁ : k + 1 + (p + 1) = n := by omega
  obtain ⟨ω, rfl⟩ := (wedgePairing_bijective h₁).2 φ
  obtain ⟨η, rfl⟩ := exists_d_eq_of_isKoszulRegular hf p ω
    (d_eq_zero_of_wedgePairing_comp_d_eq_zero h₁ (by omega) (seqDual f) ω h)
  refine ⟨(-1 : R) ^ k • wedgePairing h₀ η, LinearMap.ext fun γ => ?_⟩
  rw [LinearMap.comp_apply, LinearMap.smul_apply, smul_eq_mul, wedgePairing_d h₀ h₁,
    ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]

/-- The Koszul differential of the top generator of `⋀ᵐ⁺¹(Rᵐ⁺¹)`. -/
theorem d_topGen {m : ℕ} (f : Fin (m + 1) → R) :
    d (seqDual f) m (topGen R (m + 1)) = ∑ i : Fin (m + 1), ((-1 : R) ^ i.val * f i) •
      exteriorPower.ιMulti R m (Pi.basisFun R (Fin (m + 1)) ∘ i.succAbove) := by
  apply Subtype.ext
  rw [d_apply_coe, topGen, exteriorPower.ιMulti_apply_coe, contraction_ιMulti,
    Submodule.coe_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Submodule.coe_smul, exteriorPower.ιMulti_apply_coe, Pi.basisFun_apply, seqDual_single]

/-- **The top cohomology of the dual Koszul complex.** For any sequence `f₁, …, f_{m+1}`, a
functional on the top exterior power `⋀ᵐ⁺¹(Rᵐ⁺¹)` is the precomposition of a functional on
`⋀ᵐ(Rᵐ⁺¹)` with the Koszul differential exactly when all its values lie in the ideal
`(f₁, …, f_{m+1})`. -/
theorem mem_span_iff_exists_dual_d_eq {m : ℕ} (f : Fin (m + 1) → R)
    (φ : (⋀[R]^(m + 1) (Fin (m + 1) → R)) →ₗ[R] R) :
    (∀ x, φ x ∈ Ideal.span (Set.range f)) ↔
      ∃ ψ : (⋀[R]^m (Fin (m + 1) → R)) →ₗ[R] R, ψ ∘ₗ d (seqDual f) m = φ := by
  constructor
  · intro hφ
    obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.1 (hφ (topGen R (m + 1)))
    refine ⟨(wedgePairing (show 1 + m = m + 1 by omega)).flip
      ⟨ExteriorAlgebra.ι R c, ι_mem_one c⟩, LinearMap.ext fun x => ?_⟩
    rw [LinearMap.comp_apply, LinearMap.flip_apply,
      wedgePairing_apply_of_mul_eq _ _ _ (y := seqDual f c • x)
        (by rw [Submodule.coe_smul, d_apply_coe]; exact ι_mul_contraction_of_mem_top _ _ x.2),
      map_smul, smul_eq_mul, seqDual_apply, hc]
    conv_rhs => rw [eq_smul_topGen x, map_smul, smul_eq_mul]
    exact mul_comm _ _
  · rintro ⟨ψ, rfl⟩ x
    rw [LinearMap.comp_apply, eq_smul_topGen x, map_smul, map_smul, smul_eq_mul, d_topGen,
      map_sum]
    refine Ideal.mul_mem_left _ _ (Submodule.sum_mem _ fun i _ => ?_)
    rw [map_smul, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩))

end Koszul

end
