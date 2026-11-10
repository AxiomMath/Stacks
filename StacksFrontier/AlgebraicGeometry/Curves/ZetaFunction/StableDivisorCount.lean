module

public import StacksFrontier.AlgebraicGeometry.Curves.ZetaFunction.FrobeniusTwist

/-!
# Frobenius-stable effective divisors in a linear system

Let `C` be a smooth proper curve over an algebraically closed field `Ω` of characteristic `p` and
`Ψ` a `q`-semilinear automorphism of `C` (`q = p ^ n`, `n ≥ 1`), permuting the closed points by
`σ`. For a Picard class `c` fixed by `Ψ^*` with `h⁰(c) ≥ 1`,

`(q - 1) · #{E ≥ 0 : E ∘ σ = E, [E] = c} = q ^ h⁰(c) - 1`.

Indeed, writing `c = [D]` and `D ∘ σ = D + div u`, the effective divisors of class `c` are the
`D + div f` for `f` in `ℙ(L(D))`, and `D + div f` is `σ`-invariant exactly when the line of `f`
is stable under the twisted Frobenius `T f = u · τ f`; Lang's count
(`Stacks.Lang.natCard_stable_mul`) gives the number of stable lines.

## Main results

* `Stacks.Zeta.divOf_mul`, `Stacks.Zeta.divOf_algebraMap`,
  `Stacks.Zeta.exists_eq_smul_of_divOf_eq`: `div (f g) = div f + div g`, constants have trivial
  divisor, and two functions with the same divisor differ by a nonzero constant.
* `Stacks.Zeta.stableDivisors`: the `σ`-invariant effective divisors of a class.
* `Stacks.Zeta.natCard_stableDivisors_mul`: the count.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Zeta

variable {Ω : Type u} [Field Ω] [IsAlgClosed Ω] {C : Scheme.{u}} (g : C ⟶ Spec (.of Ω))
  [IsProper g] [Smooth g] [IsCurve Ω g] [IsLocallyNoetherian C]

omit [IsAlgClosed Ω] in
/-- The divisor of a product of nonzero rational functions is the sum of their divisors. -/
theorem divOf_mul {f f' : C.functionField} (hf : f ≠ 0) (hf' : f' ≠ 0) :
    divOf g (mul_ne_zero hf hf') = divOf g hf + divOf g hf' := by
  ext x
  simp only [divOf_apply, Finsupp.coe_add, Pi.add_apply, Scheme.ord_mul hf hf']

omit [IsAlgClosed Ω] in
/-- A nonzero constant function has zero divisor. -/
theorem divOf_algebraMap {c : Ω} (hc : c ≠ 0) :
    letI := ffAlg g
    divOf g ((map_ne_zero_iff _ (algebraMap Ω C.functionField).injective).2 hc) = 0 := by
  let := ffAlg g
  ext x
  rw [divOf_apply, ord_algebraMap_const g hc x, Finsupp.coe_zero, Pi.zero_apply]

/-- **Two functions with the same divisor differ by a nonzero constant.** -/
theorem exists_eq_smul_of_divOf_eq {f f' : C.functionField} (hf : f ≠ 0) (hf' : f' ≠ 0)
    (h : divOf g hf = divOf g hf') :
    letI := ffAlg g
    ∃ c : Ω, c ≠ 0 ∧ f = algebraMap Ω C.functionField c * f' := by
  let := ffAlg g
  have hq : f * f'⁻¹ ≠ 0 := mul_ne_zero hf (inv_ne_zero hf')
  obtain ⟨c, hc, hcq⟩ := exists_eq_algebraMap_of_ord_nonneg g hq fun x => by
    have h1 := Scheme.ord_mul (x := x.1) hq hf'
    rw [mul_assoc, inv_mul_cancel₀ hf', mul_one] at h1
    have h2 := congrArg (fun D : ClosedPoint C →₀ ℤ => D x) h
    simp only [divOf_apply] at h2
    omega
  refine ⟨c, hc, ?_⟩
  rw [← hcq, mul_assoc, inv_mul_cancel₀ hf', mul_one]

/-! ### The count -/

/-- An effective divisor (a finitely supported `ℕ`-valued function on the closed points), as a
divisor. -/
abbrev natDivisor : (ClosedPoint C →₀ ℕ) →+ (ClosedPoint C →₀ ℤ) :=
  Finsupp.mapRange.addMonoidHom (Nat.castAddMonoidHom ℤ)

omit [IsAlgClosed Ω] [IsProper g] [Smooth g] [IsCurve Ω g] [IsLocallyNoetherian C] in
/-- The coefficient of `natDivisor E` at a closed point `x` is `E x`, cast to `ℤ`. -/
theorem natDivisor_apply (E : ClosedPoint C →₀ ℕ) (x : ClosedPoint C) :
    natDivisor E x = (E x : ℤ) := rfl

omit [IsAlgClosed Ω] in
/-- Equal nonzero rational functions have equal divisors. -/
theorem divOf_congr {f f' : C.functionField} (h : f = f') (hf : f ≠ 0) (hf' : f' ≠ 0) :
    divOf g hf = divOf g hf' := by
  subst h; rfl

/-- The `σ`-invariant effective divisors of class `c`, `σ` the permutation of the closed points
induced by `Ψ`. -/
def stableDivisors (Ψ : C ≅ C) (c : Stacks.Picard.ofScheme C) : Set (ClosedPoint C →₀ ℕ) :=
  {E | (∀ y, E (closedPointPerm Ψ y) = E y) ∧ divisorClass g (natDivisor E) = c}

variable (p : ℕ) [hp : Fact p.Prime] [CharP Ω p] (n : ℕ) (hn : 0 < n) (Ψ : C ≅ C)
  (hΨ : Ψ.hom ≫ g = g ≫ Spec.map (CommRingCat.ofHom (iterateFrobenius Ω p n)))

include hn hΨ in
/-- **Counting the Frobenius-stable effective divisors of a fixed class.** If `Ψ^* c = c` and
`h⁰(c) ≥ 1`, then `(q - 1) · #{E ≥ 0 : E ∘ σ = E, [E] = c} = q ^ h⁰(c) - 1`, `q = p ^ n`. -/
theorem natCard_stableDivisors_mul (c : Stacks.Picard.ofScheme C)
    (hc : Stacks.Picard.schemePullbackClassHom Ψ.hom c = c) (h1 : 1 ≤ h0 g c) :
    (p ^ n - 1) * Nat.card (stableDivisors g Ψ c) = (p ^ n) ^ h0 g c - 1 := by
  classical
  let := ffAlg g
  obtain ⟨D, rfl⟩ := exists_divisorClass_eq g c
  set σ := closedPointPerm Ψ
  obtain ⟨u, hu, hdu⟩ := exists_divOf_eq_of_divisorClass_eq_zero g
    (D := D.mapDomain σ.symm - D)
    (by rw [map_sub, ← schemePullbackClass_divisorClass, hc, sub_self])
  have hD : D.mapDomain σ.symm = D + divOf g hu := by rw [hdu]; abel
  set V := rrSpace g D
  have : FiniteDimensional Ω V :=
    Module.finite_of_finrank_pos (by rw [finrank_rrSpace]; omega)
  set T := twistMap g p n Ψ hΨ D hu hD
  have hT := twistMap_injective g p n Ψ hΨ D hu hD
  have key := Stacks.Lang.natCard_stable_mul p n hn T hT
  rw [finrank_rrSpace] at key
  rw [← key]
  congr 1
  have hne : ∀ v : V, v ≠ 0 → (v : C.functionField) ≠ 0 := fun v hv h =>
    hv (Subtype.ext h)
  let ψ : Projectivization Ω V → (ClosedPoint C →₀ ℤ) := fun x =>
    D + divOf g (hne _ x.rep_nonzero)
  have hψmk : ∀ (v : V) (hv : v ≠ 0), ψ (Projectivization.mk Ω v hv) = D + divOf g (hne v hv) :=
    fun v hv => by
      obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep Ω v hv
      have h' : ((Projectivization.mk Ω v hv).rep : C.functionField) =
          algebraMap Ω C.functionField a * v := by
        rw [← ha]; rfl
      have ha0 : algebraMap Ω C.functionField a ≠ 0 :=
        (map_ne_zero_iff _ (algebraMap Ω C.functionField).injective).2 a.ne_zero
      change D + divOf g _ = _
      rw [divOf_congr g h' _ (mul_ne_zero ha0 (hne v hv)), divOf_mul g ha0 (hne v hv),
        divOf_algebraMap g a.ne_zero, zero_add]
  have hψnonneg : ∀ x y, 0 ≤ ψ x y := fun x y => by
    rcases (mem_rrSpace g).1 x.rep.2 with h | h
    · exact absurd h (hne _ x.rep_nonzero)
    · have := h y
      change 0 ≤ D y + C.ord _ y.1
      omega
  have hψclass : ∀ x, divisorClass g (ψ x) = divisorClass g D := fun x => by
    change divisorClass g (D + divOf g _) = _
    rw [map_add, divisorClass_divOf, add_zero]
  have hψinj : Function.Injective ψ := fun x x' h => by
    have h' : divOf g (hne _ x.rep_nonzero) = divOf g (hne _ x'.rep_nonzero) :=
      add_left_cancel h
    obtain ⟨a, -, ha⟩ := exists_eq_smul_of_divOf_eq g _ _ h'
    rw [← Projectivization.mk_rep x, ← Projectivization.mk_rep x',
      Projectivization.mk_eq_mk_iff']
    exact ⟨a, Subtype.ext (by rw [ha]; rfl)⟩
  have hψsurj : ∀ E : ClosedPoint C →₀ ℤ, (∀ y, 0 ≤ E y) →
      divisorClass g E = divisorClass g D → ∃ x, ψ x = E := fun E hE hcE => by
    obtain ⟨f, hf, hfE⟩ := exists_divOf_eq_of_divisorClass_eq_zero g (D := E - D)
      (by rw [map_sub, hcE, sub_self])
    have hfV : f ∈ V := (mem_rrSpace g).2 (Or.inr fun y => by
      have := congrArg (fun F : ClosedPoint C →₀ ℤ => F y) hfE
      simp only [divOf_apply, Finsupp.coe_sub, Pi.sub_apply] at this
      have := hE y
      omega)
    have hv : (⟨f, hfV⟩ : V) ≠ 0 := fun h => hf (congrArg Subtype.val h)
    refine ⟨Projectivization.mk Ω ⟨f, hfV⟩ hv, ?_⟩
    rw [hψmk]
    change D + divOf g hf = E
    rw [hfE]; abel
  have hψT : ∀ x, ψ (Projectivization.map T hT x) = (ψ x).mapDomain σ.symm := fun x => by
    conv_lhs => rw [← Projectivization.mk_rep x, Projectivization.map_mk, hψmk]
    have h' : ((T x.rep : V) : C.functionField) = u * tau Ψ x.rep :=
      twistMap_apply g p n Ψ hΨ D hu hD _
    have hτ0 : tau Ψ (x.rep : C.functionField) ≠ 0 :=
      (map_ne_zero_iff _ (tau Ψ).injective).2 (hne _ x.rep_nonzero)
    rw [divOf_congr g h' _ (mul_ne_zero hu hτ0), divOf_mul g hu hτ0, divOf_tau g Ψ,
      ← add_assoc, ← hD, ← Finsupp.mapDomain_add]
  have hstable : ∀ x, Stacks.Lang.IsStablePoint p n T hT x ↔ ∀ y, ψ x (σ y) = ψ x y :=
    fun x => by
      rw [Stacks.Lang.IsStablePoint, ← hψinj.eq_iff, hψT, Finsupp.ext_iff]
      exact forall_congr' fun y => by rw [mapDomain_closedPointPerm_symm_apply]
  have hcast : ∀ E : ClosedPoint C →₀ ℤ, (∀ y, 0 ≤ E y) →
      natDivisor (Finsupp.mapRange Int.toNat Int.toNat_zero E) = E := fun E hE => by
    ext y
    rw [natDivisor_apply, Finsupp.mapRange_apply, Int.toNat_of_nonneg (hE y)]
  let Φ : {x : Projectivization Ω V // Stacks.Lang.IsStablePoint p n T hT x} →
      stableDivisors g Ψ (divisorClass g D) := fun x =>
    ⟨Finsupp.mapRange Int.toNat Int.toNat_zero (ψ x.1), fun y => by
      simp only [Finsupp.mapRange_apply]
      exact congrArg Int.toNat (((hstable x.1).1 x.2) y), by
      rw [hcast _ (hψnonneg x.1), hψclass]⟩
  refine (Nat.card_congr (Equiv.ofBijective Φ ⟨?_, ?_⟩)).symm
  · intro x x' h
    have h' := congrArg (fun E : stableDivisors g Ψ (divisorClass g D) => natDivisor E.1) h
    simp only [Φ, hcast _ (hψnonneg _)] at h'
    exact Subtype.ext (hψinj h')
  · rintro ⟨E, hEσ, hEc⟩
    obtain ⟨x, hx⟩ := hψsurj (natDivisor E) (fun y => by rw [natDivisor_apply]; omega) hEc
    have hxs : Stacks.Lang.IsStablePoint p n T hT x := (hstable x).2 fun y => by
      rw [hx, natDivisor_apply, natDivisor_apply, hEσ]
    refine ⟨⟨x, hxs⟩, Subtype.ext ?_⟩
    change Finsupp.mapRange Int.toNat Int.toNat_zero (ψ x) = E
    ext y
    rw [Finsupp.mapRange_apply, hx, natDivisor_apply, Int.toNat_natCast]

end Stacks.Zeta

end
