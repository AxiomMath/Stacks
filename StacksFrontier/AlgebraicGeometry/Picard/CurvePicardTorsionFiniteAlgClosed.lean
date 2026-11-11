module

public import StacksFrontier.AlgebraicGeometry.Picard.BaseChangeCurveTorsionFinite
public import StacksFrontier.AlgebraicGeometry.Picard.TorsionSmoothProjectiveCurve.Unconditional
public import StacksFrontier.AlgebraicGeometry.HQuasiProjectiveDimensionOne.Basic

/-!
# The `n`-torsion of the Picard group of a smooth proper curve is finite, for every `n`

Let `X` be a smooth proper curve over an algebraically closed field `k`. For every integer
`n ≥ 1` the `n`-torsion `Pic(X)[n]` is finite, in every characteristic. Write `n = p ^ e · n'`
with `p` the characteristic exponent and `n'` prime to `p`. Then `Pic(X)[n']` is finite because
`n'` is invertible in `k` (`Stacks.Picard.finite_torsionBy_ofScheme_of_isCurve`), and
`Pic(X)[p ^ e]` is finite by clause (2) of [Stacks, Tag 0C1Z]
(`Stacks.Picard.exists_rank_torsionBy_prime_pow_addEquiv_pi_zmod_of_smoothProjectiveCurve`),
which applies because a proper curve is projective ([Stacks, Tag 0A26]). As `p ^ e` and `n'` are
coprime, `Pic(X)[n] = Pic(X)[p ^ e] + Pic(X)[n']`.

## Main results

* `Stacks.Picard.finite_setOf_nsmul_eq_zero_of_isCurve`: `Pic(X)[n]` is finite for `n ≥ 1`.

## References

* [Stacks Project, Tag 0C1Z](https://stacks.math.columbia.edu/tag/0C1Z)
* [Stacks Project, Tag 0A26](https://stacks.math.columbia.edu/tag/0A26)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Stacks.HQuasiProjectiveDimensionOne

universe u

namespace Stacks.Picard

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- In an abelian group, if the `a`-torsion and the `b`-torsion are finite for coprime `a` and
`b`, so is the `a b`-torsion: it is contained in the sum of the two. -/
theorem finite_setOf_mul_nsmul_eq_zero {A : Type*} [AddCommGroup A] {a b : ℕ}
    (hab : Nat.Coprime a b) (ha : {c : A | a • c = 0}.Finite)
    (hb : {c : A | b • c = 0}.Finite) : {c : A | (a * b) • c = 0}.Finite := by
  obtain ⟨u, v, huv⟩ := (Nat.isCoprime_iff_coprime.mpr hab : IsCoprime (a : ℤ) (b : ℤ))
  refine (Set.Finite.image2 (· + ·) hb ha).subset fun c hc => ?_
  have hc' : ((a : ℤ) * b) • c = 0 := by
    rw [Set.mem_ofPred_eq] at hc
    rw [← hc, ← natCast_zsmul, Nat.cast_mul]
  refine ⟨(u * a) • c, ?_, (v * b) • c, ?_, ?_⟩
  · change b • ((u * a) • c) = 0
    rw [← natCast_zsmul, smul_smul, show (b : ℤ) * (u * a) = u * (a * b) by ring, ← smul_smul,
      hc', smul_zero]
  · change a • ((v * b) • c) = 0
    rw [← natCast_zsmul, smul_smul, show (a : ℤ) * (v * b) = v * (a * b) by ring, ← smul_smul,
      hc', smul_zero]
  · change (u * a) • c + (v * b) • c = c
    rw [← add_smul, huv, one_smul]

/-- **`Pic(X)[n]` is finite for every `n ≥ 1`.** Let `X` be a smooth proper curve over an
algebraically closed field `k`; then for every positive integer `n` there are only finitely many
classes `c ∈ Pic(X)` with `n c = 0`, whatever the characteristic of `k`. -/
theorem finite_setOf_nsmul_eq_zero_of_isCurve [IsAlgClosed k] [IsCurve k f] [Smooth f]
    [IsProper f] (n : ℕ) (hn : 0 < n) : {c : ofScheme X | n • c = 0}.Finite := by
  have hunit : ∀ m : ℕ, IsUnit (m : k) → {c : ofScheme X | m • c = 0}.Finite := by
    intro m hm
    have := finite_torsionBy_ofScheme_of_isCurve f hm
    refine (Set.finite_range
      (fun c : Submodule.torsionBy ℤ (ofScheme X) (m : ℤ) => (c : ofScheme X))).subset ?_
    intro c hc
    refine ⟨⟨c, ?_⟩, rfl⟩
    rw [Submodule.mem_torsionBy_iff, natCast_zsmul]
    exact hc
  by_cases h0 : ringChar k = 0
  · have : CharZero k := (CharP.ringChar_zero_iff_CharZero k).mp h0
    exact hunit n (Ne.isUnit (Nat.cast_ne_zero.mpr hn.ne'))
  set p := ringChar k with hpdef
  have : CharP k p := ringChar.charP k
  have hpprime : p.Prime := (CharP.char_is_prime_or_zero k p).resolve_right h0
  have hppow : ∀ e : ℕ, {c : ofScheme X | (p ^ e) • c = 0}.Finite := by
    intro e
    rcases Nat.eq_zero_or_pos e with rfl | he
    · refine (Set.finite_singleton (0 : ofScheme X)).subset fun c hc => ?_
      rw [Set.mem_ofPred_eq, pow_zero, one_nsmul] at hc
      exact hc
    have : IsProjectiveVariety k f :=
      (isProjectiveVariety_iff k f).mpr ⟨IsCurve.toIsVariety,
        isProjectiveMorphism_of_isProper_of_topologicalKrullDim_le_one f
          (IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)).le⟩
    obtain ⟨r, -, hr⟩ :=
      exists_rank_torsionBy_prime_pow_addEquiv_pi_zmod_of_smoothProjectiveCurve k f p
        hpprime.pos
    obtain ⟨φ⟩ := hr e he
    have : NeZero (p ^ e) := ⟨pow_ne_zero _ hpprime.ne_zero⟩
    have : Finite (Submodule.torsionBy ℤ (ofScheme X) ((p : ℤ) ^ e)) :=
      Finite.of_equiv _ φ.symm.toEquiv
    refine (Set.finite_range
      (fun c : Submodule.torsionBy ℤ (ofScheme X) ((p : ℤ) ^ e) => (c : ofScheme X))).subset ?_
    intro c hc
    refine ⟨⟨c, ?_⟩, rfl⟩
    rw [Submodule.mem_torsionBy_iff, ← Nat.cast_pow, natCast_zsmul]
    exact hc
  obtain ⟨e, n', hn', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' p hpprime.one_lt.ne'
  have hcop : Nat.Coprime (p ^ e) n' :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hpprime).mpr hn')
  have hn'unit : IsUnit (n' : k) := by
    refine Ne.isUnit fun h => hn' ?_
    exact (CharP.cast_eq_zero_iff k p n').mp h
  exact finite_setOf_mul_nsmul_eq_zero hcop (hppow e) (hunit n' hn'unit)

end Stacks.Picard

end
