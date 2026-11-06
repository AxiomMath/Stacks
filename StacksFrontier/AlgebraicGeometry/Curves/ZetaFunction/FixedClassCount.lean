module

public import StacksFrontier.AlgebraicGeometry.Curves.ZetaFunction.StableDivisorCount
public import StacksFrontier.RingTheory.PowerSeries.PermutationEulerProduct

/-!
# The number of invariant effective divisors of a Frobenius-semilinear automorphism

Let `C` be a smooth proper curve of genus `γ` over an algebraically closed field `Ω` of
characteristic `p` and `Ψ` a `q`-semilinear automorphism of `C` (`q = p ^ n`, `n ≥ 1`), permuting
the closed points by `σ`. Let `A d` be the number of `σ`-invariant effective divisors of degree
`d` (`Stacks.Zeta.invariantCount σ d`), `h` the number of `Ψ^*`-fixed classes in `Pic⁰(C)`, and
suppose `σ` has a periodic point. Then (`Stacks.Zeta.exists_period_invariantCount`):

* `h` is finite;
* the degrees of the `Ψ^*`-fixed classes are the multiples of some `δ ≥ 1`, and `A d = 0` unless
  `δ ∣ d`;
* for `δ ∣ d` and `d ≥ 2γ - 1`, `(q - 1) A d = h (q ^ (d + 1 - γ) - 1)`.

An invariant effective divisor has a fixed class of the same degree; each fixed class `c` of
degree `d ≥ 2γ - 1` carries `(q ^ h⁰(c) - 1)/(q - 1)` of them with `h⁰(c) = d + 1 - γ`
(`Stacks.Zeta.natCard_stableDivisors_mul` and Riemann–Roch), and the fixed classes of degree `d`
form a coset of the fixed part of `Pic⁰`. Finiteness of `h`: translating by a fixed class of
large degree embeds the fixed part of `Pic⁰` into the classes of the finitely many invariant
effective divisors of that degree.

The file also records the powers `Ψ ^ k` (in `Aut C`): they are `q ^ k`-semilinear, act on the
closed points by `σ ^ k` and on `Pic` by the iterates of `Ψ^*`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Zeta

/-! ### Powers of an automorphism -/

section Powers

variable {C : Scheme.{u}}

/-- The morphism underlying `Ψ ^ (k + 1)` in `Aut C` is that of `Ψ ^ k` followed by `Ψ`. -/
theorem aut_pow_succ_hom (Ψ : C ≅ C) (k : ℕ) :
    (Aut.of Ψ ^ (k + 1)).asIso.hom = (Aut.of Ψ ^ k).asIso.hom ≫ Ψ.hom := by
  rw [pow_succ', Aut.mul_asIso]
  rfl

/-- On underlying points, `Ψ ^ k` in `Aut C` acts as the `k`-th iterate of `Ψ`. -/
theorem aut_pow_hom_base (Ψ : C ≅ C) (k : ℕ) (x : C) :
    (Aut.of Ψ ^ k).asIso.hom.base x = Ψ.hom.base^[k] x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [aut_pow_succ_hom, Function.iterate_succ_apply', ← ih]
    rfl

/-- The `k`-th iterate of the permutation of closed points induced by `Ψ` is the `k`-th iterate
of `Ψ` on underlying points. -/
theorem iterate_closedPointPerm_val (Ψ : C ≅ C) (k : ℕ) (x : ClosedPoint C) :
    ((closedPointPerm Ψ)^[k] x).1 = Ψ.hom.base^[k] x.1 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]; rfl

/-- `Ψ ^ k` permutes the closed points by `σ ^ k`. -/
theorem closedPointPerm_aut_pow (Ψ : C ≅ C) (k : ℕ) :
    closedPointPerm (Aut.of Ψ ^ k).asIso = closedPointPerm Ψ ^ k :=
  Equiv.ext fun x => Subtype.ext ((aut_pow_hom_base Ψ k x.1).trans (by
    rw [Equiv.Perm.coe_pow, iterate_closedPointPerm_val]))

/-- `(Ψ ^ k)^*` is the `k`-th iterate of `Ψ^*` on `Pic`. -/
theorem schemePullbackClassHom_aut_pow (Ψ : C ≅ C) (k : ℕ) (c : Stacks.Picard.ofScheme C) :
    Stacks.Picard.schemePullbackClassHom (Aut.of Ψ ^ k).asIso.hom c =
      (Stacks.Picard.schemePullbackClassHom Ψ.hom)^[k] c := by
  induction k generalizing c with
  | zero => exact Stacks.Picard.schemePullbackClass_id C c
  | succ k ih =>
    rw [aut_pow_succ_hom, Function.iterate_succ_apply, ← ih]
    exact (Stacks.Picard.schemePullbackClass_comp _ _ c).symm

variable {Ω : Type u} [Field Ω] (g : C ⟶ Spec (.of Ω)) (p : ℕ) [hp : Fact p.Prime] [CharP Ω p]
  (n : ℕ) (Ψ : C ≅ C)
  (hΨ : Ψ.hom ≫ g = g ≫ Spec.map (CommRingCat.ofHom (iterateFrobenius Ω p n)))

include hΨ in
/-- **`Ψ ^ k` is `q ^ k`-semilinear.** -/
theorem aut_pow_hom_comp (k : ℕ) :
    (Aut.of Ψ ^ k).asIso.hom ≫ g =
      g ≫ Spec.map (CommRingCat.ofHom (iterateFrobenius Ω p (n * k))) := by
  induction k with
  | zero =>
    rw [Nat.mul_zero, iterateFrobenius_zero]
    show 𝟙 C ≫ g = g ≫ Spec.map (𝟙 _)
    rw [Spec.map_id, Category.id_comp, Category.comp_id]
  | succ k ih =>
    rw [aut_pow_succ_hom, Category.assoc, hΨ, ← Category.assoc, ih, Category.assoc,
      ← Spec.map_comp]
    congr 2
    ext c
    show (c ^ p ^ n) ^ p ^ (n * k) = c ^ p ^ (n * (k + 1))
    rw [← pow_mul, ← pow_add, Nat.mul_succ, Nat.add_comm]

end Powers

section Count

variable {Ω : Type u} [Field Ω] [IsAlgClosed Ω] {C : Scheme.{u}} (g : C ⟶ Spec (.of Ω))
  [IsProper g] [Smooth g] [IsCurve Ω g] (p : ℕ) [hp : Fact p.Prime] [CharP Ω p] (n : ℕ)
  (hn : 0 < n) (Ψ : C ≅ C)
  (hΨ : Ψ.hom ≫ g = g ≫ Spec.map (CommRingCat.ofHom (iterateFrobenius Ω p n)))

include hn hΨ in
/-- **The closed points fixed by `Ψ ^ k`, `k ≥ 1`, form a finite set.** -/
theorem finite_setOf_iterate_closedPointPerm {k : ℕ} (hk : 0 < k) :
    {y : ClosedPoint C | (closedPointPerm Ψ)^[k] y = y}.Finite := by
  refine ((finite_setOf_isClosed_fixed g p (n * k) (Nat.mul_pos hn hk) (Aut.of Ψ ^ k).asIso
    (aut_pow_hom_comp g p n Ψ hΨ k)).preimage Subtype.val_injective.injOn).subset fun y hy => ?_
  refine ⟨y.2, ?_⟩
  rw [aut_pow_hom_base, ← iterate_closedPointPerm_val]
  exact congrArg Subtype.val hy

variable [IsLocallyNoetherian C]

omit [IsAlgClosed Ω] [IsProper g] [IsLocallyNoetherian C] in
/-- **An invariant effective divisor has a fixed class.** -/
theorem schemePullbackClassHom_divisorClass_natDivisor {E : ClosedPoint C →₀ ℕ}
    (hE : ∀ y, E (closedPointPerm Ψ y) = E y) :
    Stacks.Picard.schemePullbackClassHom Ψ.hom (divisorClass g (natDivisor E)) =
      divisorClass g (natDivisor E) := by
  rw [schemePullbackClass_divisorClass]
  congr 1
  ext y
  rw [mapDomain_closedPointPerm_symm_apply, natDivisor_apply, natDivisor_apply, hE]

omit [IsLocallyNoetherian C] in
/-- **The degree of the class of an effective divisor is its degree.** -/
theorem picardDegree_divisorClass_natDivisor (E : ClosedPoint C →₀ ℕ) :
    Stacks.Picard.picardDegree g (topologicalKrullDim_le_one g) (divisorClass g (natDivisor E)) =
      ((Finsupp.degree E : ℕ) : ℤ) := by
  rw [picardDegree_divisorClass, Finsupp.mapRange.addMonoidHom_apply,
    Finsupp.sum_mapRange_index (fun _ => rfl), Finsupp.degree_apply, Nat.cast_sum]
  rfl

include hn hΨ in
/-- **The count of invariant effective divisors.** If `σ` has a periodic closed point, the
`Ψ^*`-fixed part of `Pic⁰` is finite, of cardinality `h`, and for some `δ ≥ 1` the number `A d`
of invariant effective divisors of degree `d` vanishes unless `δ ∣ d`, and
`(q - 1) A d = h (q ^ (d + 1 - γ) - 1)` when `δ ∣ d` and `d ≥ 2γ - 1`. -/
theorem exists_period_invariantCount
    (hper : ∃ x : ClosedPoint C, ∃ k, 0 < k ∧ (closedPointPerm Ψ)^[k] x = x) :
    Finite {c : Stacks.Picard.ofScheme C //
        Stacks.Picard.picardDegree g (topologicalKrullDim_le_one g) c = 0 ∧
        Stacks.Picard.schemePullbackClassHom Ψ.hom c = c} ∧
    ∃ δ : ℕ, 0 < δ ∧ ∀ d : ℕ, (¬ δ ∣ d → invariantCount (closedPointPerm Ψ) d = 0) ∧
      (δ ∣ d → 2 * genus g ≤ d + 1 →
        (((p ^ n : ℕ) : ℤ) - 1) * invariantCount (closedPointPerm Ψ) d =
          Nat.card {c : Stacks.Picard.ofScheme C //
            Stacks.Picard.picardDegree g (topologicalKrullDim_le_one g) c = 0 ∧
            Stacks.Picard.schemePullbackClassHom Ψ.hom c = c} *
            (((p ^ n : ℕ) : ℤ) ^ (d + 1 - genus g) - 1)) := by
  classical
  set σ := closedPointPerm Ψ with hσ
  set deg := Stacks.Picard.picardDegree g (topologicalKrullDim_le_one g)
  set P := Stacks.Picard.schemePullbackClassHom Ψ.hom
  set γ := genus g
  have hfin : ∀ m, 0 < m → {y | (⇑σ)^[m] y = y}.Finite := fun m hm =>
    finite_setOf_iterate_closedPointPerm g p n hn Ψ hΨ hm
  have hfinv : ∀ d, Finite (invariantSet σ d) := fun d => (finite_invariantSet hfin d).to_subtype
  have hq1 : 1 ≤ p ^ n := Nat.one_le_pow _ _ hp.out.pos
  have hq2 : 2 ≤ p ^ n := Nat.one_lt_pow hn.ne' hp.out.one_lt
  -- an invariant effective divisor has a fixed class of the same degree
  have hinv : ∀ {d : ℕ} {E : ClosedPoint C →₀ ℕ}, E ∈ invariantSet σ d →
      P (divisorClass g (natDivisor E)) = divisorClass g (natDivisor E) ∧
        deg (divisorClass g (natDivisor E)) = d := fun {d E} hE =>
    ⟨schemePullbackClassHom_divisorClass_natDivisor g Ψ hE.2,
      by rw [picardDegree_divisorClass_natDivisor, hE.1]⟩
  -- a fixed class of positive degree: the orbit of a periodic point
  have hex : ∃ d : ℕ, 0 < d ∧ ∃ c, P c = c ∧ deg c = d := by
    obtain ⟨x, k, hk, hx⟩ := hper
    have hxk : (⇑σ.symm)^[k] x = x := by
      conv_lhs => rw [← hx]
      exact Function.LeftInverse.iterate σ.left_inv k x
    set f : ℕ → Stacks.Picard.ofScheme C := fun i => pointClass g ((⇑σ.symm)^[i] x)
    refine ⟨k, hk, ∑ i ∈ Finset.range k, f i, ?_, ?_⟩
    · rw [map_sum]
      have h1 : ∀ i, P (f i) = f (i + 1) := fun i => by
        show Stacks.Picard.schemePullbackClass Ψ.hom (pointClass g _) = _
        rw [schemePullbackClass_pointClass, ← hσ]
        show pointClass g _ = pointClass g _
        rw [Function.iterate_succ_apply']
      simp only [h1]
      have h2 := Finset.sum_range_succ' f k
      rw [Finset.sum_range_succ, show f k = f 0 by simp only [f, hxk, Function.iterate_zero,
        id_eq]] at h2
      exact add_right_cancel h2.symm
    · rw [map_sum]
      simp only [f, deg, picardDegree_pointClass, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul, mul_one]
  set δ := Nat.find hex with hδdef
  obtain ⟨hδpos, c₀, hc₀P, hc₀deg⟩ := Nat.find_spec hex
  rw [← hδdef] at hc₀deg
  -- the degrees of fixed classes are the multiples of `δ`
  have hdvd : ∀ c, P c = c → (δ : ℤ) ∣ deg c := by
    intro c hc
    set e := deg c
    set c' := c - (e / δ) • c₀
    have hc'P : P c' = c' := by simp only [c', map_sub, map_zsmul, hc, hc₀P]
    have hc'deg : deg c' = e % δ := by
      simp only [c', map_sub, map_zsmul, hc₀deg, smul_eq_mul, Int.emod_def]
      ring
    have h0 : 0 ≤ e % δ := Int.emod_nonneg _ (by exact_mod_cast hδpos.ne')
    have hlt : e % δ < δ := Int.emod_lt_of_pos _ (by exact_mod_cast hδpos)
    refine Int.dvd_of_emod_eq_zero ?_
    by_contra hne
    have hmin := Nat.find_min hex (m := (e % δ).toNat) (by omega)
    exact hmin ⟨by omega, c', hc'P, by rw [hc'deg]; omega⟩
  have hexd : ∀ d : ℕ, δ ∣ d → ∃ c, P c = c ∧ deg c = d := by
    rintro d ⟨j, rfl⟩
    refine ⟨(j : ℤ) • c₀, by rw [map_zsmul, hc₀P], ?_⟩
    rw [map_zsmul, hc₀deg, smul_eq_mul]
    push_cast; ring
  -- fixed classes of degree `≥ γ` carry invariant effective divisors
  have hne : ∀ c, P c = c → (γ : ℤ) ≤ deg c → (stableDivisors g Ψ c).Nonempty := by
    intro c hc hdeg
    have h1 := one_le_h0 g c hdeg
    have key := natCard_stableDivisors_mul g p n hn Ψ hΨ c hc h1
    have hpos : 0 < (p ^ n) ^ h0 g c - 1 := by
      have : p ^ n ≤ (p ^ n) ^ h0 g c := Nat.le_self_pow (by omega) _
      omega
    rw [← key] at hpos
    have hcard : Nat.card (stableDivisors g Ψ c) ≠ 0 := fun h => by simp [h] at hpos
    exact Set.nonempty_coe_sort.1 (Nat.card_ne_zero.1 hcard).1
  set H0 := {c : Stacks.Picard.ofScheme C // deg c = 0 ∧ P c = c}
  -- the fixed classes of degree `d` are a coset of the fixed part of `Pic⁰`
  have hcoset : ∀ d : ℕ, δ ∣ d →
      Nonempty ({c : Stacks.Picard.ofScheme C // deg c = d ∧ P c = c} ≃ H0) := by
    intro d hd
    obtain ⟨cd, hcdP, hcddeg⟩ := hexd d hd
    exact ⟨{ toFun := fun c => ⟨c.1 - cd, by rw [map_sub, c.2.1, hcddeg, sub_self],
                by rw [map_sub, c.2.2, hcdP]⟩
             invFun := fun c => ⟨c.1 + cd, by rw [map_add, c.2.1, hcddeg, zero_add],
                by rw [map_add, c.2.2, hcdP]⟩
             left_inv := fun c => Subtype.ext (sub_add_cancel _ _)
             right_inv := fun c => Subtype.ext (add_sub_cancel_right _ _) }⟩
  -- finiteness of the fixed part of `Pic⁰`
  have hH0 : Finite H0 := by
    set d₁ := δ * (γ + 1)
    obtain ⟨c₁, hc₁P, hc₁deg⟩ := hexd d₁ (dvd_mul_right _ _)
    have hd₁ : (γ : ℤ) ≤ d₁ := by
      have : γ + 1 ≤ d₁ := Nat.le_mul_of_pos_left _ hδpos
      omega
    have hsel : ∀ c : H0, (stableDivisors g Ψ (c.1 + c₁)).Nonempty := fun c =>
      hne _ (by rw [map_add, c.2.2, hc₁P]) (by rw [map_add, c.2.1, hc₁deg, zero_add]; exact hd₁)
    refine Finite.of_injective (β := invariantSet σ d₁) (fun c => ⟨(hsel c).some, ?_, ?_⟩)
      fun c c' h => ?_
    · have h1 := picardDegree_divisorClass_natDivisor g (hsel c).some
      rw [(hsel c).some_mem.2, map_add, c.2.1, hc₁deg, zero_add] at h1
      exact_mod_cast h1.symm
    · exact (hsel c).some_mem.1
    · have h1 := (hsel c).some_mem.2
      have h2 := (hsel c').some_mem.2
      have h3 := congrArg Subtype.val h
      simp only at h3
      rw [h3, h2] at h1
      exact Subtype.ext (add_right_cancel h1.symm)
  refine ⟨hH0, δ, hδpos, fun d => ⟨fun hnd => ?_, fun hd h2γ => ?_⟩⟩
  · have : IsEmpty (invariantSet σ d) := ⟨fun E => by
      obtain ⟨hP, hdeg⟩ := hinv E.2
      have := hdvd _ hP
      rw [hdeg] at this
      exact hnd (Int.natCast_dvd_natCast.1 this)⟩
    exact Nat.card_of_isEmpty
  -- the tail formula
  set Hd := {c : Stacks.Picard.ofScheme C // deg c = d ∧ P c = c}
  obtain ⟨e⟩ := hcoset d hd
  have : Finite Hd := Finite.of_equiv _ e.symm
  let : Fintype Hd := Fintype.ofFinite Hd
  let F : invariantSet σ d → Hd := fun E => ⟨divisorClass g (natDivisor E.1), (hinv E.2).2,
    (hinv E.2).1⟩
  have hfib : ∀ c : Hd, {E // F E = c} ≃ stableDivisors g Ψ c.1 := fun c =>
    { toFun := fun E => ⟨E.1.1, E.1.2.2, congrArg Subtype.val E.2⟩
      invFun := fun E => ⟨⟨E.1, by
          refine ⟨?_, E.2.1⟩
          have h1 := picardDegree_divisorClass_natDivisor g E.1
          rw [E.2.2, c.2.1] at h1
          exact_mod_cast h1.symm⟩, Subtype.ext E.2.2⟩
      left_inv := fun E => rfl
      right_inv := fun E => rfl }
  have hcount : ∀ c : Hd, (((p ^ n : ℕ) : ℤ) - 1) * Nat.card {E // F E = c} =
      ((p ^ n : ℕ) : ℤ) ^ (d + 1 - γ) - 1 := by
    intro c
    rw [Nat.card_congr (hfib c)]
    have hh0 : (h0 g c.1 : ℤ) = deg c.1 + 1 - γ :=
      h0_eq_of_le g c.1 (by rw [c.2.1]; omega)
    rw [c.2.1] at hh0
    have hh0' : h0 g c.1 = d + 1 - γ := by omega
    have key := natCard_stableDivisors_mul g p n hn Ψ hΨ c.1 c.2.2 (by omega)
    rw [hh0'] at key
    have hle : 1 ≤ (p ^ n) ^ (d + 1 - γ) := Nat.one_le_pow _ _ (by omega)
    have := congrArg (Nat.cast : ℕ → ℤ) key
    rw [Nat.cast_mul, Nat.cast_sub hq1, Nat.cast_sub hle, Nat.cast_pow, Nat.cast_one] at this
    exact this
  rw [invariantCount, ← Nat.card_congr (Equiv.sigmaFiberEquiv F), Nat.card_sigma,
    Nat.cast_sum, Finset.mul_sum, Finset.sum_congr rfl fun c _ => hcount c, Finset.sum_const,
    Finset.card_univ, ← Nat.card_eq_fintype_card, Nat.card_congr e, nsmul_eq_mul]

end Count

end Stacks.Zeta

end
