module

public import Mathlib.GroupTheory.Transfer

/-!
# The transfer of a decomposition-group element, orbit by orbit

Let `H` be a subgroup of finite index of a group `G`, `φ : H →* A` a homomorphism to a
commutative group and `V = transfer φ : G →* A`. Mathlib computes `V(σ)` as a product over the
orbits of `⟨σ⟩` on `G / H`: the orbit of `gH`, of length `n`, contributes `φ(g⁻¹ σⁿ g)`
(`MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot`).

This file regroups that product along the orbits of a subgroup `D ∋ σ`. In the Galois setting
`G = Gal(M/F)`, `H = Gal(M/K)`, `D` the decomposition group of a place `𝔓` of `M` above a place
`w` of `F` and `σ ∈ D` a Frobenius element, the `D`-orbits on `G / H` are the places `v` of `K`
above `w` (the coset `gH` lying over the place of `K` below `g⁻¹ 𝔓`), the orbit of `v` has
`e_v f_v` elements, and `φ(g⁻¹ σⁿ g)`, for `n` a multiple of the residue degree `f_v`, is
`Frob_v ^ (n / f_v)` when `φ` is the restriction to an abelian extension `L / K` unramified at
`v`. The regrouped product is then `∏_{v | w} Frob_v ^ (e_v f_v / f_v) = ∏_{v | w} Frob_v ^ e_v`,
the transfer of Frobenius elements used in the proof of unramified reciprocity.

## Main results

* `Stacks.Adeles.GlobalFunctionField.transfer_eq_one_of_forall` — `V(τ) = 1` when
  `φ(g⁻¹ τⁿ g) = 1` whenever it is defined (the transfer kills inertia).
* `Stacks.Adeles.GlobalFunctionField.transfer_eq_prod_orbitRel_pow` — the transfer of `σ ∈ D`
  as a product over the `D`-orbits on `G / H`.
-/

@[expose] public noncomputable section

open MulAction Subgroup

namespace Stacks.Adeles.GlobalFunctionField

variable {G : Type*} [Group G] {H : Subgroup G} [H.FiniteIndex] {A : Type*} [CommGroup A]
  (φ : H →* A)

/-- **The transfer of `τ` is trivial if every `φ(g⁻¹ τⁿ g)` is.** -/
public theorem transfer_eq_one_of_forall {τ : G}
    (hτ : ∀ (g : G) (n : ℕ) (h : g⁻¹ * τ ^ n * g ∈ H), φ ⟨_, h⟩ = 1) :
    MonoidHom.transfer φ τ = 1 := by
  classical
  let := H.fintypeQuotientOfFiniteIndex
  rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot]
  exact Finset.prod_eq_one fun q _ => hτ _ _ _

/-- **An orbit is the fibre of the quotient map over its class.** -/
public theorem card_orbit_out_eq_card_filter {K α : Type*} [Group K] [MulAction K α] [Fintype α]
    [DecidableEq (Quotient (orbitRel K α))] (O : Quotient (orbitRel K α)) :
    Nat.card (orbit K O.out) =
      (Finset.univ.filter fun x : α => (Quotient.mk'' x : Quotient (orbitRel K α)) = O).card := by
  classical
  rw [Nat.card_eq_card_toFinset]
  congr 1
  ext x
  simp only [Set.mem_toFinset, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← orbitRel.Quotient.mem_orbit, orbitRel.Quotient.orbit_eq_orbit_out O Quotient.out_eq']

/-- **For `K ≤ D`, the representative of the `K`-class of `x` has the `D`-class of `x`.** -/
public theorem mk_out_orbitRel_of_le {M α : Type*} [Group M] [MulAction M α] {K D : Subgroup M}
    (hKD : K ≤ D) (x : α) :
    (Quotient.mk'' (Quotient.mk'' x : Quotient (orbitRel K α)).out : Quotient (orbitRel D α)) =
      Quotient.mk'' x := by
  obtain ⟨⟨k, hk⟩, hx⟩ :=
    Quotient.exact' (Quotient.out_eq' (Quotient.mk'' x : Quotient (orbitRel K α)))
  exact Quotient.sound' ⟨⟨k, hKD hk⟩, hx⟩

/-- **The transfer of an element of `D`, regrouped along the `D`-orbits on `G / H`.** Let
`σ ∈ D` and let `c : G / H → A`, `f : G / H → ℕ` be constant on `D`-orbits, such that
`φ(g⁻¹ σⁿ g)`, whenever it is defined, is `c(gH) ^ (n / f(gH))` with `f(gH) ∣ n`. Then
`transfer φ σ = ∏_O c(O) ^ (#O / f(O))`, the product over the `D`-orbits `O` on `G / H`. -/
public theorem transfer_eq_prod_orbitRel_pow (D : Subgroup G)
    [Fintype (Quotient (orbitRel D (G ⧸ H)))] {σ : G} (hσ : σ ∈ D) (c : G ⧸ H → A) (f : G ⧸ H → ℕ)
    (hD : ∀ d ∈ D, ∀ x : G ⧸ H, c (d • x) = c x ∧ f (d • x) = f x)
    (hc : ∀ (g : G) (n : ℕ) (h : g⁻¹ * σ ^ n * g ∈ H),
      f (g : G ⧸ H) ∣ n ∧ φ ⟨_, h⟩ = c (g : G ⧸ H) ^ (n / f (g : G ⧸ H))) :
    MonoidHom.transfer φ σ = ∏ O : Quotient (orbitRel D (G ⧸ H)),
      c O.out ^ (Nat.card (orbit D O.out) / f O.out) := by
  classical
  let := H.fintypeQuotientOfFiniteIndex
  -- `c` and `f` are constant on `D`-orbits.
  have horb : ∀ x y : G ⧸ H, y ∈ orbit D x → c y = c x ∧ f y = f x := by
    rintro x _ ⟨d, rfl⟩
    exact hD d d.2 x
  -- The `D`-orbit of the `⟨σ⟩`-orbit `q`.
  let π : Quotient (orbitRel (zpowers σ) (G ⧸ H)) → Quotient (orbitRel D (G ⧸ H)) :=
    fun q => Quotient.mk'' q.out
  have hπ : ∀ q, (π q).out ∈ orbit D q.out := fun q => Quotient.exact' (Quotient.out_eq' (π q))
  have hmk : ∀ x : G ⧸ H, π (Quotient.mk'' x) = Quotient.mk'' x :=
    mk_out_orbitRel_of_le (zpowers_le.2 hσ)
  -- The factor of each `⟨σ⟩`-orbit.
  set n : Quotient (orbitRel (zpowers σ) (G ⧸ H)) → ℕ :=
    fun q => Function.minimalPeriod (σ • ·) q.out with hn
  have hfac : ∀ q, f (π q).out ∣ n q ∧
      φ ⟨q.out.out⁻¹ * σ ^ n q * q.out.out,
        QuotientGroup.out_conj_pow_minimalPeriod_mem H σ q.out⟩ =
        c (π q).out ^ (n q / f (π q).out) := fun q => by
    obtain ⟨h1, h2⟩ := hc q.out.out (n q) (QuotientGroup.out_conj_pow_minimalPeriod_mem H σ q.out)
    rw [QuotientGroup.out_eq'] at h1 h2
    rw [(horb _ _ (hπ q)).1, (horb _ _ (hπ q)).2]
    exact ⟨h1, h2⟩
  rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot]
  refine (Finset.prod_congr rfl fun q _ => (hfac q).2).trans ?_
  rw [← Finset.prod_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ) (g := π)
    (fun _ _ => Finset.mem_univ _)]
  refine Finset.prod_congr rfl fun O _ => ?_
  -- Inside the fibre over `O`, every factor is a power of `c O.out`.
  have hfib : ∀ q ∈ (Finset.univ.filter fun q => π q = O),
      c (π q).out ^ (n q / f (π q).out) = c O.out ^ (n q / f O.out) := fun q hq => by
    rw [(Finset.mem_filter.1 hq).2]
  rw [Finset.prod_congr rfl hfib, Finset.prod_pow_eq_pow_sum]
  congr 1
  have hdvd : ∀ q ∈ (Finset.univ.filter fun q => π q = O), f O.out ∣ n q :=
    fun q hq => (Finset.mem_filter.1 hq).2 ▸ (hfac q).1
  rw [← Nat.sum_div hdvd]
  congr 1
  -- `#O` is the sum of the lengths of the `⟨σ⟩`-orbits it contains.
  rw [card_orbit_out_eq_card_filter, Finset.card_eq_sum_card_fiberwise (f := fun x : G ⧸ H =>
    (Quotient.mk'' x : Quotient (orbitRel (zpowers σ) (G ⧸ H))))
    (t := Finset.univ.filter fun q => π q = O)]
  · refine Finset.sum_congr rfl fun q hq => ?_
    simp only [hn]
    rw [minimalPeriod_eq_card, ← Nat.card_eq_fintype_card, card_orbit_out_eq_card_filter,
      Finset.filter_filter]
    congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun hx => ⟨?_, hx⟩, And.right⟩
    rw [← (Finset.mem_filter.1 hq).2, ← hx, hmk]
  · intro x hx
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hx ⊢
    rw [hmk, hx]

end Stacks.Adeles.GlobalFunctionField

end
