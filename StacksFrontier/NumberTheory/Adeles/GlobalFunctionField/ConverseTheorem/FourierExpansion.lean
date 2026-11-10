module

public import StacksFrontier.NumberTheory.Adeles.GlobalFunctionField.ConverseTheorem.AdditiveCharacter

/-!
# The Fourier–Whittaker expansion of unramified cusp forms

Let `K` be a function field over a finite field `k` of characteristic `p`, with adele ring `A`,
and let `Λ` be a field in which `p` is invertible and which has enough `p`-th roots of unity
(for instance `Λ = Q̄_ℓ` with `ℓ ≠ p`, or any algebraically closed field of characteristic
`≠ p`). Fix a nontrivial adelic character `ψ` of `A / K` (see
`StacksFrontier.NumberTheory.Adeles.GlobalFunctionField.ConverseTheorem.AdditiveCharacter`).

A function `φ : A → Λ` invariant under `K + A(D)` for some divisor `D` is a function on the finite
group `A / (K + A(D))`, and its normalized integral over `A / K` is the average
`h¹(D)⁻¹ ∑_{g ∈ A / (K + A(D))} φ(g)`, which does not depend on `D` (the order `h¹(D)` of the
group is a power of `p`, hence invertible in `Λ`). We prove the Fourier inversion formula
`φ(z) = ∑_{ξ ∈ K} ψ(ξ z) ∫_{A/K} φ(y) ψ(-ξ y) dy` (a finite sum), using that the characters of
`A / (K + A(D))` are exactly the shifts `ψ(ξ ·)` trivial on `A(D)`.

For an unramified cusp form `f` on `GL₂(A)` (Stacks Tag 03VS), the function `y ↦ f(x n(y))`,
`n(y) = (1, y; 0, 1)`, is such a function, its integral over `A / K` is the constant term, which
vanishes, and right invariance under `diag(ξ, 1) ∈ GL₂(K)` relates the other Fourier coefficients
to the *Whittaker function* `W(x) = ∫_{A/K} f(x n(y)) ψ(-y) dy`. The result is the
Fourier–Whittaker expansion
`f(x) = ∑_{ξ ∈ Kˣ} W(x · diag(ξ, 1))`, with finitely many nonzero terms for each `x`.

## Main definitions

* `Stacks.Adeles.GlobalFunctionField.IsPeriodic` — invariance of a function under translation by
  a subgroup.
* `Stacks.Adeles.GlobalFunctionField.adeleAvg` — the normalized integral over `A / K` of a
  function invariant under some `K + A(D)`.
* `Stacks.Adeles.GlobalFunctionField.fourierCoeff` — `∫_{A/K} φ(y) ψ(-ξ y) dy`.
* `Stacks.Adeles.GlobalFunctionField.whittaker` — the Whittaker function of `f` with respect
  to `ψ`.
* `Stacks.Adeles.GlobalFunctionField.diagK` — `diag(u, 1) ∈ GL₂(K) ⊆ GL₂(A)`.

## Main results

* `Stacks.Adeles.GlobalFunctionField.adeleAvg_eq` — the average does not depend on the lattice.
* `Stacks.Adeles.GlobalFunctionField.fourier_inversion` — Fourier inversion on `A / K`.
* `Stacks.Adeles.GlobalFunctionField.IsUnramifiedCuspForm.whittaker_expansion` —
  `f(x) = ∑_{ξ ∈ Kˣ} W(x · diag(ξ, 1))`.

## References

* H. Jacquet, R. P. Langlands, *Automorphic forms on GL(2)*, LNM 114, Proposition 3.2.
* [Stacks Project, Tag 03VU](https://stacks.math.columbia.edu/tag/03VU)
-/

@[expose] public noncomputable section

open Matrix

universe u w

namespace Stacks.Adeles.GlobalFunctionField

section FiniteGroup

variable {Λ : Type*} [Field Λ]

/-- For a surjective homomorphism `π : G' → G` of finite groups,
`#G · ∑_{x ∈ G'} F(π x) = #G' · ∑_{y ∈ G} F(y)`: every fibre of `π` has `#G' / #G` elements. -/
public theorem card_mul_sum_comp_surjective {G' G : Type*} [AddGroup G'] [AddGroup G]
    [Fintype G'] [Fintype G] (π : G' →+ G) (hπ : Function.Surjective π) (F : G → Λ) :
    (Fintype.card G : Λ) * ∑ x, F (π x) = (Fintype.card G' : Λ) * ∑ y, F y := by
  classical
  set c := (Finset.univ.filter fun x : G' => π x = 0).card
  have hfib : ∀ y : G, (Finset.univ.filter fun x : G' => π x = y).card = c := fun y =>
    AddMonoidHom.card_fiber_eq_of_mem_range π (hπ y) ⟨0, map_zero π⟩
  have h1 : ∑ x, F (π x) = ∑ y, (c : Λ) * F y := by
    rw [Finset.sum_comp, Finset.image_univ_of_surjective hπ]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [hfib, nsmul_eq_mul]
  have h2 : Fintype.card G' = Fintype.card G * c := by
    rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := π) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)]
    simp only [hfib, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [h1, ← Finset.mul_sum, h2, Nat.cast_mul, mul_assoc]

end FiniteGroup

section Periodic

variable {G : Type*} [AddCommGroup G] {Λ : Type*}

/-- `φ` is invariant under translation by every element of the subgroup `H`. -/
public def IsPeriodic (φ : G → Λ) (H : AddSubgroup G) : Prop :=
  ∀ a, ∀ h ∈ H, φ (a + h) = φ a

public theorem IsPeriodic.mono {φ : G → Λ} {H H' : AddSubgroup G} (hφ : IsPeriodic φ H)
    (h : H' ≤ H) : IsPeriodic φ H' := fun a b hb => hφ a b (h hb)

public theorem IsPeriodic.sup {φ : G → Λ} {H H' : AddSubgroup G} (h₁ : IsPeriodic φ H)
    (h₂ : IsPeriodic φ H') : IsPeriodic φ (H ⊔ H') := by
  intro a b hb
  obtain ⟨y, hy, z, hz, rfl⟩ := AddSubgroup.mem_sup.1 hb
  rw [← add_assoc, h₂ _ z hz, h₁ a y hy]

/-- A periodic function takes the same value at `a` and at the chosen representative of the
class of `a`. -/
public theorem IsPeriodic.apply_out {φ : G → Λ} {H : AddSubgroup G} (hφ : IsPeriodic φ H)
    (a : G) : φ (Quotient.out (a : G ⧸ H)) = φ a := by
  have h : -Quotient.out (a : G ⧸ H) + a ∈ H :=
    QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' (a : G ⧸ H))
  rw [← hφ _ _ h, add_neg_cancel_left]

public theorem IsPeriodic.mul [Mul Λ] {φ φ' : G → Λ} {H : AddSubgroup G} (h : IsPeriodic φ H)
    (h' : IsPeriodic φ' H) : IsPeriodic (fun y => φ y * φ' y) H := fun a b hb => by
  simp only [h a b hb, h' a b hb]

public theorem IsPeriodic.add [Add Λ] {φ φ' : G → Λ} {H : AddSubgroup G} (h : IsPeriodic φ H)
    (h' : IsPeriodic φ' H) : IsPeriodic (fun y => φ y + φ' y) H := fun a b hb => by
  simp only [h a b hb, h' a b hb]

public theorem IsPeriodic.const_mul [Mul Λ] (c : Λ) {φ : G → Λ} {H : AddSubgroup G}
    (h : IsPeriodic φ H) : IsPeriodic (fun y => c * φ y) H := fun a b hb => by
  simp only [h a b hb]

public theorem IsPeriodic.comp_add_right {φ : G → Λ} {H : AddSubgroup G} (h : IsPeriodic φ H)
    (c : G) : IsPeriodic (fun y => φ (y + c)) H := fun a b hb => by
  simp only
  rw [add_right_comm, h _ b hb]

/-- A character trivial on `H` is `H`-periodic. -/
public theorem isPeriodic_addChar {M : Type*} [CommMonoid M] (θ : AddChar G M)
    {H : AddSubgroup G} (hθ : ∀ a ∈ H, θ a = 1) : IsPeriodic θ H := fun a b hb => by
  rw [AddChar.map_add_eq_mul, hθ b hb, mul_one]

end Periodic

section KFree

variable {K : Type u} [Field K]

/-- A sum over `Kˣ` of a function on `K` vanishing at `0` is the sum over `K`. -/
public theorem finsum_units_eq_finsum {M : Type*} [AddCommMonoid M] (g : K → M) (h0 : g 0 = 0) :
    ∑ᶠ u : Kˣ, g u = ∑ᶠ ξ : K, g ξ := by
  rw [← finsum_mem_range (f := g)
      (fun a b h => Units.ext h : Function.Injective (Units.val : Kˣ → K)),
    ← finsum_mem_inter_support g (Set.range _)]
  have : Set.range (Units.val : Kˣ → K) ∩ Function.support g = Function.support g := by
    refine Set.inter_eq_right.2 fun ξ hξ => ?_
    have hξ0 : ξ ≠ 0 := fun h => hξ (by rw [h, h0])
    exact ⟨Units.mk0 ξ hξ0, rfl⟩
  rw [this, finsum_mem_support]

end KFree

variable (k : Type u) [Field k] [Finite k] {K : Type u} [Field K] [Algebra k K]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
variable {Λ : Type w} [Field Λ]

section Average

variable (K) in
/-- The normalized sum `h¹(D)⁻¹ ∑_{g ∈ A / (K + A(D))} φ(g)`, evaluated at chosen
representatives `g.out`. For `φ` invariant under `K + A(D)` it is the integral of `φ` over
`A / K` against the Haar measure of total mass `1`. -/
public def avgOver (D : Place K →₀ ℤ) (φ : AdeleRing K → Λ) : Λ :=
  (hOne k K D : Λ)⁻¹ *
    ∑ᶠ g : AdeleRing K ⧸ (principal k K ⊔ adeleLattice K D), φ (Quotient.out g)

/-- The quotient `A / (K + A(D))` is a finite type. -/
private noncomputable instance fintypeQuotientPrincipalSupAdeleLattice (D : Place K →₀ ℤ) :
    Fintype (AdeleRing K ⧸ (principal k K ⊔ adeleLattice K D)) :=
  @Fintype.ofFinite _ (finite_quotient_principal_sup_adeleLattice k D)

public theorem avgOver_eq_sum (D : Place K →₀ ℤ) (φ : AdeleRing K → Λ)
    [Fintype (AdeleRing K ⧸ (principal k K ⊔ adeleLattice K D))] :
    avgOver k K D φ = (hOne k K D : Λ)⁻¹ *
      ∑ g : AdeleRing K ⧸ (principal k K ⊔ adeleLattice K D), φ (Quotient.out g) := by
  rw [avgOver, finsum_eq_sum_of_fintype]

public theorem hOne_eq_card (D : Place K →₀ ℤ)
    [Fintype (AdeleRing K ⧸ (principal k K ⊔ adeleLattice K D))] :
    hOne k K D = Fintype.card (AdeleRing K ⧸ (principal k K ⊔ adeleLattice K D)) := by
  rw [hOne, AddSubgroup.index, Nat.card_eq_fintype_card]

/-- `h¹(D) = [A : K + A(D)]` is a power of `p`, hence invertible in `Λ` when `p` is. -/
public theorem hOne_cast_ne_zero [NeZero (ringChar k : Λ)] (D : Place K →₀ ℤ) :
    (hOne k K D : Λ) ≠ 0 := by
  have : Fact (ringChar k).Prime := ⟨CharP.char_is_prime k (ringChar k)⟩
  set H := principal k K ⊔ adeleLattice K D
  have : Finite (AdeleRing K ⧸ H) := finite_quotient_principal_sup_adeleLattice k D
  have hp : IsPGroup (ringChar k) (Multiplicative (AdeleRing K ⧸ H)) := by
    intro g
    refine ⟨1, ?_⟩
    rw [pow_one]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.1 (exponent_dvd_ringChar k H) g
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hp
  rw [show hOne k K D = ringChar k ^ n from hn, Nat.cast_pow]
  exact pow_ne_zero _ (NeZero.ne _)

/-- The average does not change when the lattice is shrunk. -/
public theorem avgOver_eq_of_le [NeZero (ringChar k : Λ)] {D D' : Place K →₀ ℤ} (hD : D' ≤ D)
    {φ : AdeleRing K → Λ} (hφ : IsPeriodic φ (principal k K ⊔ adeleLattice K D)) :
    avgOver k K D' φ = avgOver k K D φ := by
  set H := principal k K ⊔ adeleLattice K D
  set H' := principal k K ⊔ adeleLattice K D'
  have hle : H' ≤ H := sup_le_sup_left (adeleLattice_mono k hD) _
  let π : AdeleRing K ⧸ H' →+ AdeleRing K ⧸ H :=
    QuotientAddGroup.map H' H (AddMonoidHom.id _) hle
  have hπ : Function.Surjective π := by
    intro g
    induction g using QuotientAddGroup.induction_on with | H a => exact ⟨a, rfl⟩
  have key := card_mul_sum_comp_surjective π hπ (fun g => φ (Quotient.out g))
  have hsum : ∑ x, φ (Quotient.out (π x)) = ∑ x : AdeleRing K ⧸ H', φ (Quotient.out x) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    induction x using QuotientAddGroup.induction_on with | H a => ?_
    rw [(hφ.mono hle).apply_out]
    exact hφ.apply_out a
  rw [hsum] at key
  have h1 := hOne_cast_ne_zero k (Λ := Λ) D
  have h2 := hOne_cast_ne_zero k (Λ := Λ) D'
  rw [hOne_eq_card k D] at h1
  rw [hOne_eq_card k D'] at h2
  rw [avgOver_eq_sum, avgOver_eq_sum, hOne_eq_card k D, hOne_eq_card k D']
  field_simp
  linear_combination key

variable (K) in
/-- The normalized integral over `A / K` of a function invariant under `K + A(D)` for some `D`:
the average over `A / (K + A(D))` for such a `D` (it does not depend on `D`, see
`Stacks.Adeles.GlobalFunctionField.adeleAvg_eq`). -/
public def adeleAvg (φ : AdeleRing K → Λ) : Λ :=
  avgOver k K (Classical.epsilon fun D => IsPeriodic φ (principal k K ⊔ adeleLattice K D)) φ

/-- `∫_{A/K} φ` is the average over `A / (K + A(D))` for any `D` with `φ` invariant under
`K + A(D)`. -/
public theorem adeleAvg_eq [NeZero (ringChar k : Λ)] {D : Place K →₀ ℤ} {φ : AdeleRing K → Λ}
    (hφ : IsPeriodic φ (principal k K ⊔ adeleLattice K D)) :
    adeleAvg k K φ = avgOver k K D φ := by
  set D₁ := Classical.epsilon fun D => IsPeriodic φ (principal k K ⊔ adeleLattice K D)
  have h1 : IsPeriodic φ (principal k K ⊔ adeleLattice K D₁) :=
    Classical.epsilon_spec (p := fun D => IsPeriodic φ (principal k K ⊔ adeleLattice K D)) ⟨D, hφ⟩
  rw [adeleAvg, ← avgOver_eq_of_le k (inf_le_right : D ⊓ D₁ ≤ D₁) h1,
    avgOver_eq_of_le k inf_le_left hφ]

omit [Field Λ] in
/-- Two functions periodic for some lattices are periodic for a common one. -/
public theorem IsPeriodic.inf_left {φ : AdeleRing K → Λ} {D : Place K →₀ ℤ}
    (hφ : IsPeriodic φ (principal k K ⊔ adeleLattice K D)) (D' : Place K →₀ ℤ) :
    IsPeriodic φ (principal k K ⊔ adeleLattice K (D ⊓ D')) :=
  hφ.mono (sup_le_sup_left (adeleLattice_mono k inf_le_left) _)

omit [Field Λ] in
public theorem IsPeriodic.inf_right {φ : AdeleRing K → Λ} {D : Place K →₀ ℤ}
    (hφ : IsPeriodic φ (principal k K ⊔ adeleLattice K D)) (D' : Place K →₀ ℤ) :
    IsPeriodic φ (principal k K ⊔ adeleLattice K (D' ⊓ D)) :=
  hφ.mono (sup_le_sup_left (adeleLattice_mono k inf_le_right) _)

/-- `∫ (φ + φ') = ∫ φ + ∫ φ'`. -/
public theorem adeleAvg_add [NeZero (ringChar k : Λ)] {φ φ' : AdeleRing K → Λ}
    {D D' : Place K →₀ ℤ} (hφ : IsPeriodic φ (principal k K ⊔ adeleLattice K D))
    (hφ' : IsPeriodic φ' (principal k K ⊔ adeleLattice K D')) :
    adeleAvg k K (fun y => φ y + φ' y) = adeleAvg k K φ + adeleAvg k K φ' := by
  have h₁ := hφ.inf_left k D'
  have h₂ := hφ'.inf_right k D
  rw [adeleAvg_eq k (h₁.add h₂), adeleAvg_eq k h₁, adeleAvg_eq k h₂]
  rw [avgOver_eq_sum, avgOver_eq_sum, avgOver_eq_sum, Finset.sum_add_distrib, mul_add]

/-- A finite sum of functions each periodic for some lattice is periodic for some lattice. -/
public theorem exists_isPeriodic_sum {ι : Type*} (s : Finset ι) (F : ι → AdeleRing K → Λ)
    (hF : ∀ i, ∃ D : Place K →₀ ℤ, IsPeriodic (F i) (principal k K ⊔ adeleLattice K D)) :
    ∃ D : Place K →₀ ℤ,
      IsPeriodic (fun y => ∑ i ∈ s, F i y) (principal k K ⊔ adeleLattice K D) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, fun a b _ => by simp⟩
  | insert i s hi ih =>
    obtain ⟨D₁, h₁⟩ := hF i
    obtain ⟨D₂, h₂⟩ := ih
    refine ⟨D₁ ⊓ D₂, fun a b hb => ?_⟩
    have e₁ := h₁.inf_left k D₂ a b hb
    have e₂ := h₂.inf_right k D₁ a b hb
    simp only [Finset.sum_insert hi] at e₂ ⊢
    rw [e₁, e₂]

/-- `∫ ∑ᵢ Fᵢ = ∑ᵢ ∫ Fᵢ` for finitely many functions each periodic for some lattice. -/
public theorem adeleAvg_sum [NeZero (ringChar k : Λ)] {ι : Type*} (s : Finset ι)
    (F : ι → AdeleRing K → Λ)
    (hF : ∀ i, ∃ D : Place K →₀ ℤ, IsPeriodic (F i) (principal k K ⊔ adeleLattice K D)) :
    adeleAvg k K (fun y => ∑ i ∈ s, F i y) = ∑ i ∈ s, adeleAvg k K (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [adeleAvg_eq k (D := 0) (fun _ _ _ => rfl), avgOver]
    simp
  | insert i s hi ih =>
    obtain ⟨D₁, h₁⟩ := hF i
    obtain ⟨D₂, h₂⟩ := exists_isPeriodic_sum k s F hF
    simp only [Finset.sum_insert hi]
    rw [adeleAvg_add k h₁ h₂, ih]

/-- `∫ c φ = c ∫ φ`. -/
public theorem adeleAvg_const_mul [NeZero (ringChar k : Λ)] (c : Λ) {φ : AdeleRing K → Λ}
    {D : Place K →₀ ℤ} (hφ : IsPeriodic φ (principal k K ⊔ adeleLattice K D)) :
    adeleAvg k K (fun y => c * φ y) = c * adeleAvg k K φ := by
  rw [adeleAvg_eq k (hφ.const_mul c), adeleAvg_eq k hφ]
  rw [avgOver_eq_sum, avgOver_eq_sum, ← Finset.mul_sum, mul_left_comm]

/-- Translation invariance: `∫ φ(y + a) dy = ∫ φ(y) dy`. -/
public theorem adeleAvg_comp_add_right [NeZero (ringChar k : Λ)] {φ : AdeleRing K → Λ}
    {D : Place K →₀ ℤ} (hφ : IsPeriodic φ (principal k K ⊔ adeleLattice K D)) (a : AdeleRing K) :
    adeleAvg k K (fun y => φ (y + a)) = adeleAvg k K φ := by
  set H := principal k K ⊔ adeleLattice K D
  rw [adeleAvg_eq k (hφ.comp_add_right a), adeleAvg_eq k hφ]
  rw [avgOver_eq_sum, avgOver_eq_sum]
  congr 1
  refine Fintype.sum_equiv (Equiv.addRight (a : AdeleRing K ⧸ H)) _ _ fun g => ?_
  simp only [Equiv.coe_addRight]
  have : g + (a : AdeleRing K ⧸ H) = ((Quotient.out g + a : AdeleRing K) : AdeleRing K ⧸ H) := by
    rw [QuotientAddGroup.mk_add, QuotientAddGroup.out_eq']
  rw [this, hφ.apply_out]

/-- Invariance under `K`-dilations: `∫ φ(ξ y) dy = ∫ φ(y) dy` for `ξ ∈ Kˣ` (the product
formula). -/
public theorem adeleAvg_comp_diag_mul [NeZero (ringChar k : Λ)] {ξ : K} (hξ : ξ ≠ 0)
    {φ : AdeleRing K → Λ} {D : Place K →₀ ℤ}
    (hφ : IsPeriodic φ (principal k K ⊔ adeleLattice K D)) :
    adeleAvg k K (fun y => φ (diag k K ξ * y)) = adeleAvg k K φ := by
  set H := principal k K ⊔ adeleLattice K D
  set H₁ := principal k K ⊔ adeleLattice K (D + principalDivisor k K ξ)
  have hmap : H₁.map (mulDiag k hξ).toAddMonoidHom = H := by
    rw [AddSubgroup.map_sup, map_mulDiag_principal, map_mulDiag_adeleLattice, add_sub_cancel_right]
  have hmem : ∀ b ∈ H₁, diag k K ξ * b ∈ H := fun b hb => by
    rw [← hmap]
    exact AddSubgroup.mem_map_of_mem _ hb
  have hφ₁ : IsPeriodic (fun y => φ (diag k K ξ * y)) H₁ := fun a b hb => by
    simp only
    rw [mul_add, hφ _ _ (hmem b hb)]
  rw [adeleAvg_eq k hφ₁, adeleAvg_eq k hφ]
  have hh : hOne k K (D + principalDivisor k K ξ) = hOne k K D := by
    rw [← hOne_sub_principalDivisor k (inv_ne_zero hξ) D, principalDivisor_inv k hξ,
      sub_neg_eq_add]
  rw [avgOver_eq_sum, avgOver_eq_sum, hh]
  congr 1
  let e : AdeleRing K ⧸ H₁ ≃+ AdeleRing K ⧸ H := QuotientAddGroup.congr H₁ H (mulDiag k hξ) hmap
  refine Fintype.sum_equiv e.toEquiv _ _ fun g => ?_
  have : e g = ((diag k K ξ * Quotient.out g : AdeleRing K) : AdeleRing K ⧸ H) := by
    conv_lhs => rw [← QuotientAddGroup.out_eq' g]
    rfl
  rw [AddEquiv.toEquiv_eq_coe, AddEquiv.coe_toEquiv, this, hφ.apply_out]

end Average

section Fourier

/-- The Fourier coefficient `∫_{A/K} φ(y) ψ(-ξ y) dy` of `φ` at `ξ ∈ K`. -/
public def fourierCoeff (ψ : AddChar (AdeleRing K) Λ) (φ : AdeleRing K → Λ) (ξ : K) : Λ :=
  adeleAvg k K fun y => φ y * ψ (diag k K (-ξ) * y)

/-- The product of a periodic function and a shift of an adelic character is periodic. -/
public theorem IsPeriodic.exists_mul_mulShift {φ : AdeleRing K → Λ} {D : Place K →₀ ℤ}
    (hφ : IsPeriodic φ (principal k K ⊔ adeleLattice K D)) {ψ : AddChar (AdeleRing K) Λ}
    (hψ : IsAdelicChar k K ψ) (ξ : K) :
    ∃ D' : Place K →₀ ℤ, IsPeriodic (fun y => φ y * ψ (diag k K ξ * y))
      (principal k K ⊔ adeleLattice K D') := by
  obtain ⟨hK, D'', hD''⟩ := hψ.mulShift k ξ
  exact ⟨D ⊓ D'', (hφ.inf_left k D'').mul (isPeriodic_addChar (ψ.mulShift (diag k K ξ))
    fun a ha => apply_eq_one_of_mem_sup k hK
      (fun b hb => hD'' b (adeleLattice_mono k inf_le_right hb)) ha)⟩

/-- A Fourier coefficient vanishes at `ξ` when `φ` is `A(D)`-periodic and `ψ(ξ ·)` is not
trivial on `A(D)`. -/
public theorem fourierCoeff_eq_zero [NeZero (ringChar k : Λ)] {ψ : AddChar (AdeleRing K) Λ}
    (hψ : IsAdelicChar k K ψ) {φ : AdeleRing K → Λ} {D : Place K →₀ ℤ}
    (hφ : IsPeriodic φ (principal k K ⊔ adeleLattice K D)) {ξ : K} {a : AdeleRing K}
    (ha : a ∈ adeleLattice K D) (hne : ψ (diag k K ξ * a) ≠ 1) : fourierCoeff k ψ φ ξ = 0 := by
  obtain ⟨D', hD'⟩ := hφ.exists_mul_mulShift k hψ (-ξ)
  set F := fun y => φ y * ψ (diag k K (-ξ) * y)
  have hshift : (fun y => F (y + a)) = fun y => ψ (diag k K (-ξ) * a) * F y := by
    ext y
    simp only [F]
    rw [hφ y a (AddSubgroup.mem_sup_right ha), mul_add, AddChar.map_add_eq_mul]
    ring
  have h := adeleAvg_comp_add_right k hD' a
  rw [hshift, adeleAvg_const_mul k _ hD'] at h
  have hu : ψ (diag k K (-ξ) * a) ≠ 1 := by
    rw [map_neg, neg_mul, AddChar.map_neg_eq_inv]
    exact fun h1 => hne (inv_eq_one.1 h1)
  exact eq_zero_of_mul_eq_self_left hu h

variable (K) in
/-- The `ξ ∈ K` for which `ψ(ξ ·)` is trivial on `A(D)`: for `ψ` trivial on `K`, these shifts are
the characters of the finite group `A / (K + A(D))`. -/
public def charKernel (ψ : AddChar (AdeleRing K) Λ) (D : Place K →₀ ℤ) : AddSubgroup K where
  carrier := {ξ | ∀ a ∈ adeleLattice K D, ψ (diag k K ξ * a) = 1}
  zero_mem' a _ := by simp
  add_mem' {ξ η} hξ hη a ha := by
    rw [map_add, add_mul, AddChar.map_add_eq_mul, hξ a ha, hη a ha, one_mul]
  neg_mem' {ξ} hξ a ha := by
    rw [map_neg, neg_mul, ← mul_neg]
    exact hξ _ ((adeleLattice K D).neg_mem ha)

public theorem mem_charKernel {ψ : AddChar (AdeleRing K) Λ} {D : Place K →₀ ℤ} {ξ : K} :
    ξ ∈ charKernel k K ψ D ↔ ∀ a ∈ adeleLattice K D, ψ (diag k K ξ * a) = 1 := Iff.rfl

/-- For `ξ` in `charKernel`, the shift `ψ(ξ ·)` is trivial on `K + A(D)`. -/
public theorem apply_eq_one_of_mem_charKernel {ψ : AddChar (AdeleRing K) Λ}
    (hψ : IsAdelicChar k K ψ) {D : Place K →₀ ℤ} {ξ : K} (hξ : ξ ∈ charKernel k K ψ D)
    {b : AdeleRing K} (hb : b ∈ principal k K ⊔ adeleLattice K D) : ψ (diag k K ξ * b) = 1 :=
  apply_eq_one_of_mem_sup k (ψ := ψ.mulShift (diag k K ξ)) (hψ.mulShift k ξ).1 hξ hb

/-- The shifts `ψ(ξ ·)`, `ξ ∈ charKernel`, are distinct characters trivial on `K + A(D)`. -/
public theorem mulShift_charKernel_injective {ψ : AddChar (AdeleRing K) Λ}
    (hψ : IsAdelicChar k K ψ) (hψ1 : ψ ≠ 1) (D : Place K →₀ ℤ) :
    Function.Injective fun ξ : charKernel k K ψ D =>
      (⟨ψ.mulShift (diag k K ξ), fun _ hb => apply_eq_one_of_mem_charKernel k hψ ξ.2 hb⟩ :
        {θ : AddChar (AdeleRing K) Λ // ∀ a ∈ principal k K ⊔ adeleLattice K D, θ a = 1}) :=
  fun ξ _ h => Subtype.ext ((existsUnique_eq_mulShift k hψ hψ1 (hψ.mulShift k ξ)).unique rfl
    (congrArg Subtype.val h))

public theorem finite_charKernel {ψ : AddChar (AdeleRing K) Λ} (hψ : IsAdelicChar k K ψ)
    (hψ1 : ψ ≠ 1) (D : Place K →₀ ℤ) : Finite (charKernel k K ψ D) := by
  have : Finite (AdeleRing K ⧸ (principal k K ⊔ adeleLattice K D)) :=
    finite_quotient_principal_sup_adeleLattice k D
  have := finite_trivialOn (Λ := Λ) (principal k K ⊔ adeleLattice K D)
  exact Finite.of_injective _ (mulShift_charKernel_injective k hψ hψ1 D)

/-- **`#charKernel = h¹(D)`**: the characters of `A / (K + A(D))` are exactly the shifts
`ψ(ξ ·)`, `ξ ∈ charKernel`, and there are `#(A / (K + A(D)))` of them. -/
public theorem natCard_charKernel [HasEnoughRootsOfUnity Λ (ringChar k)]
    {ψ : AddChar (AdeleRing K) Λ} (hψ : IsAdelicChar k K ψ) (hψ1 : ψ ≠ 1) (D : Place K →₀ ℤ) :
    Nat.card (charKernel k K ψ D) = hOne k K D := by
  have : NeZero (ringChar k) := ⟨CharP.char_ne_zero_of_finite k (ringChar k)⟩
  have : Finite (AdeleRing K ⧸ (principal k K ⊔ adeleLattice K D)) :=
    finite_quotient_principal_sup_adeleLattice k D
  have := finite_trivialOn (Λ := Λ) (principal k K ⊔ adeleLattice K D)
  have := finite_charKernel k hψ hψ1 D
  refine le_antisymm ?_ ?_
  · exact (Nat.card_le_card_of_injective _ (mulShift_charKernel_injective k hψ hψ1 D)).trans
      (natCard_trivialOn_le_index _)
  · have := HasEnoughRootsOfUnity.of_dvd Λ
      (exponent_dvd_ringChar k (principal k K ⊔ adeleLattice K D))
    have hθ : ∀ φ : Multiplicative (AdeleRing K ⧸ (principal k K ⊔ adeleLattice K D)) →* Λˣ,
        IsAdelicChar k K (charOfHom _ φ) :=
      fun φ => ⟨fun κ => charOfHom_eq_one_of_mem _ φ
        (AddSubgroup.mem_sup_left ((mem_principal k).2 ⟨κ, rfl⟩)),
        D, fun a ha => charOfHom_eq_one_of_mem _ φ (AddSubgroup.mem_sup_right ha)⟩
    choose ξ hξ using fun φ => (existsUnique_eq_mulShift k hψ hψ1 (hθ φ)).exists
    have hmem : ∀ φ, ξ φ ∈ charKernel k K ψ D := fun φ a ha => by
      rw [← AddChar.mulShift_apply, ← hξ φ]
      exact charOfHom_eq_one_of_mem _ φ (AddSubgroup.mem_sup_right ha)
    have hinj : Function.Injective fun φ => (⟨ξ φ, hmem φ⟩ : charKernel k K ψ D) := by
      intro φ φ' h
      apply charOfHom_injective _
      rw [hξ φ, hξ φ', show ξ φ = ξ φ' from congrArg Subtype.val h]
    have h2 : Nat.card (Multiplicative (AdeleRing K ⧸ (principal k K ⊔ adeleLattice K D)) →* Λˣ)
        ≤ Nat.card (charKernel k K ψ D) := Nat.card_le_card_of_injective _ hinj
    have h3 : Nat.card (Multiplicative (AdeleRing K ⧸ (principal k K ⊔ adeleLattice K D)) →* Λˣ)
        = Nat.card (Multiplicative (AdeleRing K ⧸ (principal k K ⊔ adeleLattice K D))) :=
      CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity _ _
    rwa [h3] at h2

/-- **Orthogonality**: `∑_{ξ ∈ charKernel} ψ(ξ b)` is `h¹(D)` for `b ∈ K + A(D)` and `0`
otherwise. -/
public theorem sum_charKernel_apply [HasEnoughRootsOfUnity Λ (ringChar k)]
    {ψ : AddChar (AdeleRing K) Λ} (hψ : IsAdelicChar k K ψ) (hψ1 : ψ ≠ 1) (D : Place K →₀ ℤ)
    [Fintype (charKernel k K ψ D)] [DecidablePred (· ∈ principal k K ⊔ adeleLattice K D)]
    (b : AdeleRing K) :
    ∑ ξ : charKernel k K ψ D, ψ (diag k K ξ * b) =
      if b ∈ principal k K ⊔ adeleLattice K D then (hOne k K D : Λ) else 0 := by
  split_ifs with hb
  · rw [Finset.sum_congr rfl fun ξ _ => apply_eq_one_of_mem_charKernel k hψ ξ.2 hb,
      Finset.sum_const, Finset.card_univ, nsmul_one, ← Nat.card_eq_fintype_card,
      natCard_charKernel k hψ hψ1 D]
  · obtain ⟨ξ₀, hξ₀, hne⟩ := exists_mulShift_apply_ne_one k hψ hψ1 hb
    set s := ∑ ξ : charKernel k K ψ D, ψ (diag k K ξ * b)
    have hs : s = s * ψ (diag k K ξ₀ * b) := by
      have e := Equiv.sum_comp (Equiv.addRight (⟨ξ₀, hξ₀⟩ : charKernel k K ψ D))
        (fun ξ : charKernel k K ψ D => ψ (diag k K ξ * b))
      simp only [Equiv.coe_addRight, AddSubgroup.coe_add, map_add, add_mul,
        AddChar.map_add_eq_mul, ← Finset.sum_mul] at e
      exact e.symm
    exact eq_zero_of_mul_eq_self_right hne hs.symm

/-- **Fourier inversion on `A / K`.** If `φ` is invariant under `K + A(D)`, its Fourier
coefficients vanish outside a finite set and `φ(z) = ∑_{ξ ∈ K} ψ(ξ z) ∫_{A/K} φ(y) ψ(-ξ y) dy`. -/
public theorem fourier_inversion [NeZero (ringChar k : Λ)] [HasEnoughRootsOfUnity Λ (ringChar k)]
    {ψ : AddChar (AdeleRing K) Λ} (hψ : IsAdelicChar k K ψ) (hψ1 : ψ ≠ 1) {D : Place K →₀ ℤ}
    {φ : AdeleRing K → Λ} (hφ : IsPeriodic φ (principal k K ⊔ adeleLattice K D))
    (z : AdeleRing K) :
    (Function.support (fourierCoeff k ψ φ)).Finite ∧
      φ z = ∑ᶠ ξ : K, ψ (diag k K ξ * z) * fourierCoeff k ψ φ ξ := by
  classical
  set S := charKernel k K ψ D
  set H := principal k K ⊔ adeleLattice K D
  have : Finite S := finite_charKernel k hψ hψ1 D
  let : Fintype S := Fintype.ofFinite S
  have hsupp : Function.support (fourierCoeff k ψ φ) ⊆ (S : Set K) := by
    intro ξ hξ
    by_contra hξS
    apply hξ
    rw [SetLike.mem_coe, mem_charKernel] at hξS
    push Not at hξS
    obtain ⟨a, ha, hne⟩ := hξS
    exact fourierCoeff_eq_zero k hψ hφ ha hne
  set T : Finset K := Finset.univ.map (Function.Embedding.subtype (· ∈ S))
  have hT : (S : Set K) ⊆ T := fun ξ hξ =>
    Finset.mem_map.2 ⟨⟨ξ, hξ⟩, Finset.mem_univ _, rfl⟩
  refine ⟨(T.finite_toSet).subset (hsupp.trans hT), ?_⟩
  rw [finsum_eq_sum_of_support_subset _ ((Function.support_mul_subset_right _ _).trans
    (hsupp.trans hT)), Finset.sum_map]
  simp only [Function.Embedding.subtype_apply]
  have hcoeff : ∀ ξ : S, fourierCoeff k ψ φ ξ = (hOne k K D : Λ)⁻¹ *
      ∑ g : AdeleRing K ⧸ H, φ (Quotient.out g) * ψ (diag k K (-(ξ : K)) * Quotient.out g) := by
    intro ξ
    have hper : IsPeriodic (fun y => φ y * ψ (diag k K (-(ξ : K)) * y)) H :=
      hφ.mul (isPeriodic_addChar (ψ.mulShift (diag k K (-(ξ : K))))
        fun b hb => apply_eq_one_of_mem_charKernel k hψ (S.neg_mem ξ.2) hb)
    rw [fourierCoeff, adeleAvg_eq k hper, avgOver_eq_sum]
  simp_rw [hcoeff]
  have hiff (g : AdeleRing K ⧸ H) : z - Quotient.out g ∈ H ↔ g = (z : AdeleRing K ⧸ H) := by
    rw [← H.neg_mem_iff, neg_sub, sub_eq_neg_add, ← QuotientAddGroup.eq,
      QuotientAddGroup.out_eq', eq_comm]
  calc φ z = (hOne k K D : Λ)⁻¹ * ∑ g : AdeleRing K ⧸ H,
        φ (Quotient.out g) * (if z - Quotient.out g ∈ H then (hOne k K D : Λ) else 0) := by
        rw [Finset.sum_eq_single (z : AdeleRing K ⧸ H)]
        · rw [ite_eq_left ((hiff _).2 rfl), hφ.apply_out, mul_comm,
            mul_inv_cancel_right₀ (hOne_cast_ne_zero k D)]
        · intro g _ hg
          rw [ite_eq_right (fun h => hg ((hiff g).1 h)), mul_zero]
        · exact fun h => absurd (Finset.mem_univ _) h
    _ = (hOne k K D : Λ)⁻¹ * ∑ g : AdeleRing K ⧸ H, φ (Quotient.out g) *
        ∑ ξ : S, ψ (diag k K ξ * (z - Quotient.out g)) := by
        congr 1
        refine Finset.sum_congr rfl fun g _ => ?_
        congr 1
        exact (sum_charKernel_apply k hψ hψ1 D (z - Quotient.out g)).symm
    _ = ∑ ξ : S, ψ (diag k K ξ * z) * ((hOne k K D : Λ)⁻¹ * ∑ g : AdeleRing K ⧸ H,
        φ (Quotient.out g) * ψ (diag k K (-(ξ : K)) * Quotient.out g)) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun ξ _ => ?_
        rw [mul_sub, sub_eq_add_neg, AddChar.map_add_eq_mul, ← neg_mul, ← map_neg]
        ring

end Fourier

section Whittaker

variable (K) in
/-- `diag(u, 1) ∈ GL₂(K)`, as an element of `GL₂(A)`. -/
public def diagK (u : Kˣ) : GL (Fin 2) (AdeleRing K) :=
  mapK (GeneralLinearGroup.map (diagP k K) (diagGL u))

public theorem diagK_eq_upperGL (u : Kˣ) :
    diagK k K u = upperGL (Units.map (diag k K).toMonoidHom u) 1 0 := by
  ext i j
  rw [diagK, coe_mapK_apply]
  fin_cases i <;> fin_cases j <;> simp [diagP, diagGL, Matrix.GeneralLinearGroup.map_apply]

/-- `diag(u, 1) n(y) = n(u y) diag(u, 1)`. -/
public theorem diagK_mul_upperRightHom (u : Kˣ) (y : AdeleRing K) :
    diagK k K u * GeneralLinearGroup.upperRightHom y =
      GeneralLinearGroup.upperRightHom (diag k K u * y) * diagK k K u := by
  rw [diagK_eq_upperGL, upperRightHom_eq_upperGL, upperRightHom_eq_upperGL, upperGL_mul,
    upperGL_mul]
  congr 1 <;> simp

variable (K) in
/-- The Whittaker function `W(x) = ∫_{A/K} f(x n(y)) ψ(-y) dy` of `f : GL₂(A) → Λ` with respect to
the additive character `ψ`. -/
public def whittaker (ψ : AddChar (AdeleRing K) Λ) (f : GL (Fin 2) (AdeleRing K) → Λ)
    (x : GL (Fin 2) (AdeleRing K)) : Λ :=
  fourierCoeff k ψ (fun y => f (x * GeneralLinearGroup.upperRightHom y)) 1

/-- For `f` right `GL₂(K)`-invariant and left `GL₂(O)`-invariant, `y ↦ f(x n(y))` is invariant
under `K + A(D)` for some `D`. -/
public theorem IsUnramifiedCuspForm.exists_isPeriodic {f : GL (Fin 2) (AdeleRing K) → Λ}
    (hf : IsUnramifiedCuspForm f) (x : GL (Fin 2) (AdeleRing K)) :
    ∃ D : Place K →₀ ℤ, IsPeriodic (fun y => f (x * GeneralLinearGroup.upperRightHom y))
      (principal k K ⊔ adeleLattice K D) := by
  obtain ⟨κ, α, δ, β, rfl⟩ := exists_iwasawa x
  refine ⟨idelDiv k K α - idelDiv k K δ, IsPeriodic.sup ?_ ?_⟩
  · intro y b hb
    obtain ⟨c, rfl⟩ := (mem_principal k).1 hb
    simp only
    rw [AddChar.map_add_eq_mul, ← mul_assoc]
    have := hf.right_invariant (GeneralLinearGroup.map (integralAdeles K).subtype κ *
      upperGL α δ β * GeneralLinearGroup.upperRightHom y)
      (GeneralLinearGroup.upperRightHom (diagP k K c))
    rwa [mapK_upperRightHom] at this
  · intro z y hy
    simp only
    rw [mul_assoc, mul_assoc, hf.left_invariant, hf.left_invariant]
    have hw : (α : AdeleRing K) * y * ((δ⁻¹ : (AdeleRing K)ˣ) : AdeleRing K) ∈
        integralAdeles K := by
      rw [← mem_adeleLattice_zero_iff]
      have h1 := (idele_mul_mem_adeleLattice_iff k α (E := idelDiv k K α - idelDiv k K δ)).2 hy
      rw [sub_sub_cancel_left] at h1
      have h2 := (idele_mul_mem_adeleLattice_iff k δ⁻¹ (E := -idelDiv k K δ)).2 h1
      rw [idelDiv_inv, sub_neg_eq_add, neg_add_cancel] at h2
      rwa [mul_comm] at h2
    rw [add_comm z y, AddChar.map_add_eq_mul, ← mul_assoc, upperGL_mul_upperRightHom, mul_assoc]
    have := hf.left_invariant (upperGL α δ β * GeneralLinearGroup.upperRightHom z)
      (GeneralLinearGroup.upperRightHom ⟨_, hw⟩)
    rwa [mapO_upperRightHom] at this

/-- The constant term of a cusp form vanishes: `∫_{A/K} f(x n(y)) dy = 0`. -/
public theorem IsUnramifiedCuspForm.adeleAvg_eq_zero [NeZero (ringChar k : Λ)]
    {f : GL (Fin 2) (AdeleRing K) → Λ} (hf : IsUnramifiedCuspForm f)
    (x : GL (Fin 2) (AdeleRing K)) :
    adeleAvg k K (fun y => f (x * GeneralLinearGroup.upperRightHom y)) = 0 := by
  classical
  obtain ⟨D, hD⟩ := IsUnramifiedCuspForm.exists_isPeriodic k hf x
  set H := principal k K ⊔ adeleLattice K D
  rw [adeleAvg_eq k hD, avgOver_eq_sum]
  have hprin : (principalAdeles K).toAddSubgroup = principal k K := by
    rw [principal, range_diag]
  set s : Finset (AdeleRing K) := Finset.univ.image fun g : AdeleRing K ⧸ H => Quotient.out g
  have hs : ∀ a : AdeleRing K, ∃! z ∈ s, a - z ∈ (principalAdeles K).toAddSubgroup ⊔
      adeleLattice K D := by
    intro a
    rw [hprin]
    refine ⟨Quotient.out (a : AdeleRing K ⧸ H), ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _),
      ?_⟩, ?_⟩
    · have := QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' (a : AdeleRing K ⧸ H))
      rwa [neg_add_eq_sub] at this
    · rintro z ⟨hz, hza⟩
      obtain ⟨g, -, rfl⟩ := Finset.mem_image.1 hz
      congr 1
      rw [← QuotientAddGroup.out_eq' g]
      refine (QuotientAddGroup.eq.2 ?_).symm
      rwa [← H.neg_mem_iff, neg_add_eq_sub, ← neg_sub, neg_neg]
  have hsum := hf.vanishing_constant_term x (adeleLattice K D) (isOpen_adeleLattice k D)
    (fun z y hy => hD z y (AddSubgroup.mem_sup_right hy)) s hs
  have hsum' : ∑ g : AdeleRing K ⧸ H,
      f (x * GeneralLinearGroup.upperRightHom (Quotient.out g)) = 0 := by
    rw [← hsum]
    exact (Finset.sum_image (f := fun z => f (x * GeneralLinearGroup.upperRightHom z))
      (s := (Finset.univ : Finset (AdeleRing K ⧸ H))) (g := Quotient.out)
      fun g _ g' _ h => Quotient.out_injective h).symm
  rw [hsum', mul_zero]

/-- Right translation by `diag(u, 1)` turns the Whittaker function into the Fourier coefficient
at `u⁻¹`: `W(x diag(u, 1)) = ∫_{A/K} f(x n(y)) ψ(-u⁻¹ y) dy`. -/
public theorem IsUnramifiedCuspForm.whittaker_mul_diagK [NeZero (ringChar k : Λ)]
    {f : GL (Fin 2) (AdeleRing K) → Λ} (hf : IsUnramifiedCuspForm f)
    {ψ : AddChar (AdeleRing K) Λ} (hψ : IsAdelicChar k K ψ) (x : GL (Fin 2) (AdeleRing K))
    (u : Kˣ) :
    whittaker k K ψ f (x * diagK k K u) =
      fourierCoeff k ψ (fun y => f (x * GeneralLinearGroup.upperRightHom y)) (u⁻¹ : Kˣ) := by
  obtain ⟨D, hD⟩ := IsUnramifiedCuspForm.exists_isPeriodic k hf x
  obtain ⟨D', hD'⟩ := hD.exists_mul_mulShift k hψ (-((u⁻¹ : Kˣ) : K))
  have hf' : ∀ y, f (x * diagK k K u * GeneralLinearGroup.upperRightHom y) =
      f (x * GeneralLinearGroup.upperRightHom (diag k K u * y)) := by
    intro y
    rw [mul_assoc, diagK_mul_upperRightHom, ← mul_assoc]
    exact hf.right_invariant _ _
  rw [whittaker, fourierCoeff, fourierCoeff, ← adeleAvg_comp_diag_mul k u.ne_zero hD']
  congr 1
  ext y
  rw [hf', ← mul_assoc, ← map_mul, Units.val_inv_eq_inv_val, neg_mul, inv_mul_cancel₀ u.ne_zero]

/-- **The Fourier–Whittaker expansion of an unramified cusp form.** For every `x ∈ GL₂(A)`, only
finitely many of the `W(x diag(ξ, 1))`, `ξ ∈ Kˣ`, are nonzero, and
`f(x) = ∑_{ξ ∈ Kˣ} W(x diag(ξ, 1))`, where `W` is the Whittaker function of `f` with respect to a
nontrivial adelic character `ψ`. -/
public theorem IsUnramifiedCuspForm.whittaker_expansion [NeZero (ringChar k : Λ)]
    [HasEnoughRootsOfUnity Λ (ringChar k)] {f : GL (Fin 2) (AdeleRing K) → Λ}
    (hf : IsUnramifiedCuspForm f) {ψ : AddChar (AdeleRing K) Λ} (hψ : IsAdelicChar k K ψ)
    (hψ1 : ψ ≠ 1) (x : GL (Fin 2) (AdeleRing K)) :
    (Function.support fun u : Kˣ => whittaker k K ψ f (x * diagK k K u)).Finite ∧
      f x = ∑ᶠ u : Kˣ, whittaker k K ψ f (x * diagK k K u) := by
  obtain ⟨D, hD⟩ := IsUnramifiedCuspForm.exists_isPeriodic k hf x
  obtain ⟨hfin, hinv⟩ := fourier_inversion k hψ hψ1 hD 0
  set c := fourierCoeff k ψ (fun y => f (x * GeneralLinearGroup.upperRightHom y))
  have hc0 : c 0 = 0 := by
    simpa only [c, fourierCoeff, neg_zero, map_zero, zero_mul, AddChar.map_zero_eq_one, mul_one]
      using IsUnramifiedCuspForm.adeleAvg_eq_zero k hf x
  simp_rw [IsUnramifiedCuspForm.whittaker_mul_diagK k hf hψ x]
  refine ⟨?_, ?_⟩
  · have : (Function.support fun u : Kˣ => c ((u⁻¹ : Kˣ) : K)) =
        (fun u : Kˣ => ((u⁻¹ : Kˣ) : K)) ⁻¹' Function.support c := rfl
    rw [this]
    exact hfin.preimage fun u _ u' _ h => inv_injective (Units.ext h)
  · have e1 : ∑ᶠ u : Kˣ, c ((u⁻¹ : Kˣ) : K) = ∑ᶠ u : Kˣ, c (u : K) :=
      finsum_comp_equiv (Equiv.inv Kˣ) (f := fun v : Kˣ => c v)
    rw [e1, finsum_units_eq_finsum c hc0]
    have h1 : ∀ ξ : K, ψ (diag k K ξ * 0) * c ξ = c ξ := fun ξ => by
      rw [mul_zero, AddChar.map_zero_eq_one, one_mul]
    simpa only [h1, AddChar.map_zero_eq_one, mul_one] using hinv

end Whittaker

end Stacks.Adeles.GlobalFunctionField

end
