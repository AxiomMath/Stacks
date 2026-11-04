module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Data.Set.Card
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.GroupTheory.Index
public import Mathlib.Data.Set.Finite.Lattice

/-!
# Twisted fixed points of a group action

Let a finite group `H` act on a set `W`, let `ρ : W → X'` be a map whose fibres over the points
that matter are exactly the `H`-orbits, and let `F : W → W`, `F' : X' → X'` be compatible with
`ρ`. For `σ ∈ H` call `w` *`σ`-twisted* when `F w = σ • w`. Then the numbers of `σ`-twisted
points, summed over `σ ∈ H`, add up to exactly `|H|` times the number of fixed points of `F'`
in the image of `ρ`.

Indeed every `σ`-twisted point lies over a fixed point of `F'`. Counting pairs `(σ, w)` the other
way round, a point `w` over a fixed point has `F w` in its fibre, that is in its orbit, so the
`σ` with `σ • w = F w` form a coset of the stabilizer of `w`; and along an orbit the stabilizer
orders add up to `|H|` by the orbit-stabilizer theorem.

This is the counting identity behind both inequalities of the lower bound in Bombieri's proof of
the Riemann hypothesis for curves: for the Galois group of a cover of the projective line it
gives `∑_σ N_σ = |G| · #ℙ¹(𝔽_Q)`, and for the group of the cover of the curve it gives
`∑_{σ ∈ H} N_σ ≤ |H| · #X(𝔽_Q)`. No freeness of the action is needed, so ramification costs
nothing.

## Main results

* `Stacks.BombieriStepanov.sum_ncard_twisted_eq`: the identity above.
-/

@[expose] public noncomputable section

open MulAction

namespace Stacks.BombieriStepanov

variable {H W X' : Type*} [Group H] [Fintype H] [MulAction H W]

/-- The elements of `H` sending `w` to `v` are in bijection with the stabilizer of `w`, as soon as
one of them exists. -/
theorem card_filter_smul_eq_eq_card_stabilizer {w v : W} {σ₀ : H} (hσ₀ : σ₀ • w = v)
    [DecidablePred fun σ : H => σ • w = v] :
    (Finset.univ.filter fun σ : H => σ • w = v).card = Nat.card (stabilizer H w) := by
  rw [← Nat.card_eq_finsetCard]
  refine Nat.card_congr
    { toFun := fun σ => ⟨σ₀⁻¹ * σ.1, ?_⟩
      invFun := fun τ => ⟨σ₀ * τ.1, ?_⟩
      left_inv := fun σ => by simp
      right_inv := fun τ => by simp }
  · rw [mem_stabilizer_iff, mul_smul, (Finset.mem_filter.1 σ.2).2, ← hσ₀, inv_smul_smul]
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [mul_smul, (mem_stabilizer_iff).1 τ.2, hσ₀]

/-- Along a finite orbit the orders of the stabilizers add up to `|H|`. -/
theorem sum_card_stabilizer_orbit (w₀ : W) (hO : (orbit H w₀).Finite) :
    ∑ w ∈ hO.toFinset, Nat.card (stabilizer H w) = Fintype.card H := by
  have hstab : ∀ w ∈ hO.toFinset,
      Nat.card (stabilizer H w) * (orbit H w₀).ncard = Fintype.card H := by
    intro w hw
    rw [Set.Finite.mem_toFinset] at hw
    obtain ⟨g, rfl⟩ := hw
    rw [← orbit_smul g w₀, ← index_stabilizer, Subgroup.card_mul_index, Nat.card_eq_fintype_card]
  refine Nat.eq_of_mul_eq_mul_right ((Set.ncard_pos hO).2 ⟨w₀, mem_orbit_self w₀⟩) ?_
  rw [Finset.sum_mul, Finset.sum_congr rfl hstab, Finset.sum_const, smul_eq_mul,
    ← Set.ncard_eq_toFinset_card _ hO, mul_comm]

omit [Fintype H] in
/-- If every point with the same image under an `H`-invariant map `ρ` as `w` lies in the orbit of
`w`, then the fibre of `ρ` through `w` is that orbit. -/
theorem preimage_singleton_eq_orbit (ρ : W → X') (hρH : ∀ (h : H) (w : W), ρ (h • w) = ρ w)
    {w : W} (htrans : ∀ w', ρ w = ρ w' → ∃ h : H, h • w = w') :
    ρ ⁻¹' {ρ w} = orbit H w := by
  ext w'
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  refine ⟨fun h => htrans w' h.symm, ?_⟩
  rintro ⟨g, rfl⟩
  exact hρH g w

omit [Fintype H] in
/-- The preimage of a finite set under an `H`-invariant map whose fibres over it are single
orbits is finite. -/
theorem finite_preimage_of_forall_orbit [Finite H] (ρ : W → X') {D : Set X'} (hD : D.Finite)
    (hρH : ∀ (h : H) (w : W), ρ (h • w) = ρ w)
    (htrans : ∀ w w' : W, ρ w ∈ D → ρ w = ρ w' → ∃ h : H, h • w = w') :
    (ρ ⁻¹' D).Finite := by
  rw [← Set.biUnion_preimage_singleton]
  refine hD.biUnion fun x hx => ?_
  by_cases hx' : x ∈ Set.range ρ
  · obtain ⟨w, rfl⟩ := hx'
    rw [preimage_singleton_eq_orbit ρ hρH fun w' => htrans w w' hx]
    exact Set.finite_range _
  · rw [Set.preimage_singleton_eq_empty.2 hx']
    exact Set.finite_empty

/-- **Twisted fixed points.** Let a finite group `H` act on `W`, let `ρ : W → X'` be
`H`-invariant with the fibres of `ρ` over the fixed points of `F'` single orbits, and let
`F : W → W`, `F' : X' → X'` satisfy `ρ ∘ F = F' ∘ ρ`, with `F'` having finitely many fixed
points. Then `∑_{σ ∈ H} #{w | F w = σ • w} = |H| · #{x ∈ ρ(W) | F' x = x}`. -/
theorem sum_ncard_twisted_eq (ρ : W → X') (F : W → W) (F' : X' → X')
    (hρF : ∀ w, ρ (F w) = F' (ρ w)) (hρH : ∀ (h : H) (w : W), ρ (h • w) = ρ w)
    (htrans : ∀ w w' : W, F' (ρ w) = ρ w → ρ w = ρ w' → ∃ h : H, h • w = w')
    (hD : {x | F' x = x}.Finite) :
    ∑ σ : H, {w | F w = σ • w}.ncard =
      Fintype.card H * ({x | F' x = x} ∩ Set.range ρ).ncard := by
  classical
  set D := {x | F' x = x} ∩ Set.range ρ with hDdef
  have hDfin : D.Finite := hD.subset Set.inter_subset_left
  have hSfin : (ρ ⁻¹' D).Finite :=
    finite_preimage_of_forall_orbit ρ hDfin hρH fun w w' hw => htrans w w' hw.1
  set S := hSfin.toFinset with hSdef
  have hS : ∀ w, w ∈ S ↔ F' (ρ w) = ρ w := by
    intro w
    simp only [hSdef, Set.Finite.mem_toFinset, Set.mem_preimage, hDdef, Set.mem_inter_iff,
      Set.mem_ofPred_eq, Set.mem_range, exists_apply_eq_apply, and_true]
  have hcount : ∀ σ : H, {w | F w = σ • w}.ncard = (S.filter fun w => F w = σ • w).card := by
    intro σ
    rw [← Set.ncard_coe_finset]
    congr 1
    ext w
    simp only [Set.mem_ofPred_eq, Finset.coe_filter]
    exact ⟨fun h => ⟨by rw [hS, ← hρF, h, hρH], h⟩, fun h => h.2⟩
  have hswap : ∑ σ : H, (S.filter fun w => F w = σ • w).card =
      ∑ w ∈ S, (Finset.univ.filter fun σ : H => σ • w = F w).card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun σ _ => ?_
    simp only [eq_comm]
  have hcoset : ∀ w ∈ S, (Finset.univ.filter fun σ : H => σ • w = F w).card =
      Nat.card (stabilizer H w) := fun w hw =>
    card_filter_smul_eq_eq_card_stabilizer
      (htrans w (F w) ((hS w).1 hw) (by rw [hρF, (hS w).1 hw])).choose_spec
  have horbit : ∀ x ∈ hDfin.toFinset,
      ∑ w ∈ S.filter (fun w => ρ w = x), Nat.card (stabilizer H w) = Fintype.card H := by
    intro x hx
    rw [Set.Finite.mem_toFinset, hDdef] at hx
    obtain ⟨hFx, w₀, rfl⟩ := hx
    have hOfin : (orbit H w₀).Finite := Set.finite_range fun h : H => h • w₀
    have hfilter : S.filter (fun w => ρ w = ρ w₀) = hOfin.toFinset := by
      have hmem := preimage_singleton_eq_orbit ρ hρH (htrans w₀ · hFx)
      ext w
      simp +contextual [hS, ← hmem, (show F' (ρ w₀) = ρ w₀ from hFx)]
    rw [hfilter]
    exact sum_card_stabilizer_orbit w₀ hOfin
  rw [Finset.sum_congr rfl fun σ _ => hcount σ, hswap, Finset.sum_congr rfl hcoset,
    ← Finset.sum_fiberwise_of_maps_to (s := S) (t := hDfin.toFinset) (g := ρ)
      (fun w hw => by
        rw [Set.Finite.mem_toFinset, hDdef]
        exact ⟨(hS w).1 hw, w, rfl⟩),
    Finset.sum_congr rfl horbit, Finset.sum_const, smul_eq_mul, mul_comm,
    Set.ncard_eq_toFinset_card _ hDfin]

end Stacks.BombieriStepanov

end
