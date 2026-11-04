module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFibrePurityStable
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.DeligneConjectureConclusions

/-!
# The contragredient of `σ` satisfies the hypotheses on `σ` in Laumon's argument

The contragredient `σ^∨ = (σᵀ)⁻¹` of `σ` satisfies the hypotheses on `σ` in the proof of the
equal absolute values of the Fourier family ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH);
Kedlaya, *Fourier transforms and p-adic Weil II*, proof of Theorem 6.4):

* absolute irreducibility: a subspace `W` stable under `σ^∨` has its orthogonal `W^⊥` (for the
  standard dot product) stable under `σ`, so `W^⊥ = 0` or everything, whence `W = everything` or
  `W = 0` (`Stacks.EtaleCohomology.forall_eq_bot_or_eq_top_contragredient`);
* the same over every finite extension
  (`Stacks.EtaleCohomology.laumonStablyAbsIrr_contragredient`);
* purity: the Frobenius eigenvalues of `σ^∨` are the inverses of those of `σ`, so `σ^∨` is pure of
  weight `-β` when `σ` is pure of weight `β`
  (`Stacks.EtaleCohomology.norm_eq_rpow_of_isRoot_contragredient`).

## Main results

* `Stacks.EtaleCohomology.forall_eq_bot_or_eq_top_contragredient`.
* `Stacks.EtaleCohomology.laumonStablyAbsIrr_contragredient`.
* `Stacks.EtaleCohomology.norm_eq_rpow_of_isRoot_contragredient`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Matrix

universe u

namespace Stacks.EtaleCohomology

section Irreducible

variable {G : Type*} [Group G] {E : Type} [Field E] {m : ℕ} (σ : G →* GL (Fin m) E)
  (K : Type*) [Field K] [Algebra E K]

/-- **The contragredient of an absolutely irreducible representation is absolutely
irreducible**: if `W ⊆ K^m` is stable under all `σ^∨(g) = (σ(g)⁻¹)ᵀ`, its orthogonal for the dot
product is stable under all `σ(g)`, hence `0` (and then `W` is everything) or everything (and then
`W = 0`). -/
public theorem forall_eq_bot_or_eq_top_contragredient
    (h : ∀ W : Submodule K (Fin m → K),
      (∀ g, ∀ v ∈ W, (σ g).val.map (algebraMap E K) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤)
    (W : Submodule K (Fin m → K))
    (hW : ∀ g, ∀ v ∈ W, (contragredient σ g).val.map (algebraMap E K) *ᵥ v ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  classical
  let W' : Submodule K (Fin m → K) :=
    { carrier := {v | ∀ w ∈ W, v ⬝ᵥ w = 0}
      add_mem' := fun {v v'} hv hv' w hw => by
        rw [add_dotProduct, hv w hw, hv' w hw, add_zero]
      zero_mem' := fun w _ => zero_dotProduct w
      smul_mem' := fun c v hv w hw => by
        rw [smul_dotProduct, hv w hw, smul_zero] }
  have hmem : ∀ v, v ∈ W' ↔ ∀ w ∈ W, v ⬝ᵥ w = 0 := fun v => Iff.rfl
  have htr : ∀ g, ∀ w ∈ W, ((σ g).val.map (algebraMap E K))ᵀ *ᵥ w ∈ W := by
    intro g w hw
    have h1 := hW g⁻¹ w hw
    rwa [contragredient_val, map_inv, inv_inv, Matrix.transpose_map] at h1
  have hW' : ∀ g, ∀ v ∈ W', (σ g).val.map (algebraMap E K) *ᵥ v ∈ W' := by
    intro g v hv w hw
    rw [dotProduct_comm, dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm]
    exact hv _ (htr g w hw)
  rcases h W' hW' with hbot | htop
  · right
    by_contra hne
    obtain ⟨φ, hφ0, hφW⟩ := Submodule.exists_le_ker_of_lt_top W (lt_top_iff_ne_top.2 hne)
    let v : Fin m → K := fun i => φ (fun j => if i = j then 1 else 0)
    have hφ : ∀ w, φ w = v ⬝ᵥ w := fun w => by
      rw [LinearMap.pi_apply_eq_sum_univ φ w, dotProduct]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_eq_mul, mul_comm]
    have hv : v ∈ W' := fun w hw => by
      rw [← hφ]
      exact hφW hw
    rw [hbot, Submodule.mem_bot] at hv
    refine hφ0 (LinearMap.ext fun w => ?_)
    rw [hφ, hv, zero_dotProduct, LinearMap.zero_apply]
  · left
    rw [Submodule.eq_bot_iff]
    intro w hw
    funext i
    have h1 := (hmem (Pi.single i 1)).1 (htop ▸ Submodule.mem_top) w hw
    rwa [single_dotProduct, one_mul] at h1

end Irreducible

/-- **`σ^∨` stays absolutely irreducible over every finite extension** when `σ` does: the
pullback of `σ^∨` to `π₁(𝔸¹_{k'})` is the contragredient of the pullback of `σ`. -/
public theorem laumonStablyAbsIrr_contragredient {X : Scheme.{u}} [ConnectedSpace X]
    {k : Type u} [Field k] {e : X ⟶ Spec (.of (Polynomial k))} [IsIso e] {x : GeometricPoint X}
    {E : Type} [Field E] {m : ℕ} {σ : EtaleFundamentalGroup X x →* GL (Fin m) E}
    (hst : LaumonStablyAbsIrr k e x σ) : LaumonStablyAbsIrr k e x (contragredient σ) :=
  fun k' _ _ _ x' hx' K _ _ _ W hW =>
    forall_eq_bot_or_eq_top_contragredient _ K (hst k' x' hx' K) W hW

/-- **`σ^∨` is pure of weight `-β` when `σ` is pure of weight `β`**: the roots of the
characteristic polynomial of `σ^∨(g)` are the inverses of those of `σ(g)`. -/
public theorem norm_eq_rpow_of_isRoot_contragredient {G : Type*} [Group G] {E : Type} [Field E]
    {m : ℕ} (σ : G →* GL (Fin m) E) (ι' : E →+* ℂ) (g : G) (Q w : ℝ) (hQ : 0 ≤ Q)
    (h : ∀ z : ℂ, ((σ g).val.charpoly.map ι').IsRoot z → ‖z‖ = Q ^ (w / 2)) (z : ℂ)
    (hz : ((contragredient σ g).val.charpoly.map ι').IsRoot z) : ‖z‖ = Q ^ (-w / 2) := by
  rw [charpoly_contragredient, ← dualCharpoly_map] at hz
  have hmonic := (Matrix.charpoly_monic (σ g).val).map ι'
  have h0 : ((σ g).val.charpoly.map ι').coeff 0 ≠ 0 := by
    rw [Polynomial.coeff_map]
    exact (map_ne_zero ι').2 (charpoly_coeff_zero_ne_zero _)
  obtain ⟨-, hinv⟩ := isRoot_inv_of_isRoot_dualCharpoly hmonic h0 hz
  have h1 := h z⁻¹ hinv
  rw [norm_inv] at h1
  rw [← inv_inv ‖z‖, h1, ← Real.rpow_neg hQ, neg_div]

end Stacks.EtaleCohomology

end
