module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FiniteIndexSemisimple

/-!
# Semisimplicity from a normal subgroup of index prime to the characteristic

`Stacks.EtaleCohomology.exists_isCompl_of_normal_finiteIndex` averages the projection onto a
`G`-stable subspace over the cosets of a normal subgroup `N` of finite index, in characteristic
`0`. The averaging only divides by `[G : N]`, so it works over any field in which `[G : N]` is
invertible (Maschke's argument): if the restriction of `ρ` to `N` is semisimple, so is `ρ`.

## Main results

* `Stacks.EtaleCohomology.exists_isCompl_of_normal_index_ne_zero`: if `[G : N]` is invertible
  in `L` and the restriction of `ρ` to `N` is semisimple, every `G`-stable subspace has a
  `G`-stable complement.
-/

@[expose] public noncomputable section

namespace Stacks.EtaleCohomology

variable {L V : Type*} [Field L] [AddCommGroup V] [Module L V] {G : Type*} [Group G]

/-- A linear map preserving both summands of `W ⊕ C` commutes with the projection onto `W`. -/
public theorem mul_projection_comm {W C : Submodule L V} (h : IsCompl W C) {f : Module.End L V}
    (hfW : W ≤ W.comap f) (hfC : C ≤ C.comap f) :
    f * W.projection C h = W.projection C h * f := by
  set π : Module.End L V := W.projection C h
  refine LinearMap.ext fun v => ?_
  have hsplit : v = π v + (v - π v) := by abel
  have h₁ : π (f (π v)) = f (π v) :=
    Submodule.projection_apply_of_mem_left h (hfW (Submodule.projection_apply_mem h v))
  have h₂ : π (f (v - π v)) = 0 :=
    Submodule.projection_apply_of_mem_right h (hfC (Submodule.sub_projection_mem h v))
  change f (π v) = π (f v)
  conv_rhs => rw [hsplit, map_add, map_add, h₁, h₂, add_zero]

/-- Averaging the conjugates of an operator commuting with `ρ` on a normal subgroup `N` over
the cosets of `N` gives an operator commuting with `ρ`. -/
public theorem mul_sum_quotient_conj_comm (ρ : G →* Module.End L V) (N : Subgroup G) [N.Normal]
    [Fintype (G ⧸ N)] (π : Module.End L V) (hπN : ∀ n ∈ N, ρ n * π = π * ρ n) (g : G) :
    ρ g * ∑ q : G ⧸ N, ρ q.out * π * ρ q.out⁻¹ = (∑ q : G ⧸ N, ρ q.out * π * ρ q.out⁻¹) * ρ g := by
  let t : G → Module.End L V := fun h => ρ h * π * ρ h⁻¹
  have ht : ∀ h, ∀ n ∈ N, t (h * n) = t h := by
    intro h n hn
    have e₁ : ρ n * π * ρ n⁻¹ = π := by
      rw [hπN n hn, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
    calc t (h * n) = ρ h * (ρ n * π * ρ n⁻¹) * ρ h⁻¹ := by
          simp only [t, _root_.mul_inv_rev, map_mul, mul_assoc]
      _ = t h := by rw [e₁]
  have htq : ∀ h : G, ∀ q : G ⧸ N, (QuotientGroup.mk h : G ⧸ N) = q → t q.out = t h := by
    intro h q hq
    have hq' : (QuotientGroup.mk q.out : G ⧸ N) = QuotientGroup.mk h := by
      rw [QuotientGroup.out_eq', hq]
    obtain ⟨n, hn, hn'⟩ : ∃ n ∈ N, q.out = h * n :=
      ⟨h⁻¹ * q.out, QuotientGroup.eq.mp hq'.symm, by group⟩
    rw [hn', ht h n hn]
  have hρt : ∀ g h, ρ g * t h = t (g * h) * ρ g := by
    intro g h
    have e₂ : ρ g⁻¹ * ρ g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
    calc ρ g * t h = ρ g * ρ h * π * ρ h⁻¹ * (ρ g⁻¹ * ρ g) := by
          rw [e₂, mul_one]
          simp only [t, mul_assoc]
      _ = t (g * h) * ρ g := by simp only [t, _root_.mul_inv_rev, map_mul, mul_assoc]
  change ρ g * ∑ q : G ⧸ N, t q.out = (∑ q : G ⧸ N, t q.out) * ρ g
  rw [Finset.mul_sum, Finset.sum_mul]
  have h₁ : ∀ q : G ⧸ N, ρ g * t q.out = t ((QuotientGroup.mk g : G ⧸ N) * q).out * ρ g := by
    intro q
    rw [hρt, htq (g * q.out) _ (by rw [QuotientGroup.mk_mul, QuotientGroup.out_eq'])]
  simp_rw [h₁]
  exact Fintype.sum_equiv (Equiv.mulLeft (QuotientGroup.mk g : G ⧸ N)) _ _ fun q => rfl

/-- The kernel of a `ρ`-equivariant projection onto `W` is a `ρ`-stable complement of `W`. -/
public theorem exists_isCompl_of_equivariant_projection (ρ : G →* Module.End L V)
    {W : Submodule L V} (P : Module.End L V) (hPW : ∀ v, P v ∈ W) (hP : ∀ w ∈ W, P w = w)
    (hcomm : ∀ g, ρ g * P = P * ρ g) :
    ∃ W', IsCompl W W' ∧ ∀ g, W' ≤ W'.comap (ρ g) := by
  let P' : V →ₗ[L] W := P.codRestrict W hPW
  refine ⟨LinearMap.ker P', LinearMap.isCompl_of_proj fun x => Subtype.ext (hP x x.2),
    fun g v hv => ?_⟩
  have hv' : P v = 0 := congrArg Subtype.val (LinearMap.mem_ker.mp hv)
  rw [Submodule.mem_comap, LinearMap.mem_ker]
  apply Subtype.ext
  change P (ρ g v) = 0
  rw [← Module.End.mul_apply P, ← hcomm, Module.End.mul_apply, hv', map_zero]

/-- **Averaging over a normal subgroup of index invertible in the field**: if the restriction
of `ρ` to a normal subgroup `N` of finite index `[G : N]` invertible in `L` is semisimple, every
`G`-stable subspace has a `G`-stable complement. -/
public theorem exists_isCompl_of_normal_index_ne_zero (ρ : G →* Module.End L V)
    (N : Subgroup G) [N.Normal] [N.FiniteIndex] (hidx : (N.index : L) ≠ 0)
    (hN : ∀ W : Submodule L V, (∀ n ∈ N, W ≤ W.comap (ρ n)) →
      ∃ W', IsCompl W W' ∧ ∀ n ∈ N, W' ≤ W'.comap (ρ n))
    (W : Submodule L V) (hW : ∀ g, W ≤ W.comap (ρ g)) :
    ∃ W', IsCompl W W' ∧ ∀ g, W' ≤ W'.comap (ρ g) := by
  classical
  have : Fintype (G ⧸ N) := Fintype.ofFinite _
  obtain ⟨C, hWC, hC⟩ := hN W fun n _ => hW n
  set π : Module.End L V := W.projection C hWC
  have hπW : ∀ v, π v ∈ W := fun v => Submodule.projection_apply_mem hWC v
  have hπw : ∀ w ∈ W, π w = w := fun w hw => Submodule.projection_apply_of_mem_left hWC hw
  set Q : Module.End L V := ∑ q : G ⧸ N, ρ q.out * π * ρ q.out⁻¹ with hQ_def
  have hQcomm : ∀ g, ρ g * Q = Q * ρ g :=
    mul_sum_quotient_conj_comm ρ N π fun n hn => mul_projection_comm hWC (hW n) (hC n hn)
  have hQW : ∀ v, Q v ∈ W := by
    intro v
    rw [hQ_def, LinearMap.sum_apply]
    exact Submodule.sum_mem _ fun q _ => hW q.out (hπW _)
  have hQw : ∀ w ∈ W, Q w = (Fintype.card (G ⧸ N)) • w := by
    intro w hw
    rw [hQ_def, LinearMap.sum_apply]
    have : ∀ q : G ⧸ N, (ρ q.out * π * ρ q.out⁻¹) w = w := by
      intro q
      change ρ q.out (π (ρ q.out⁻¹ w)) = w
      rw [hπw _ (hW _ hw), map_apply_map_inv_apply]
    simp only [this, Finset.sum_const, Finset.card_univ]
  have hcard : (Fintype.card (G ⧸ N) : L) ≠ 0 := by
    rw [← Nat.card_eq_fintype_card]
    exact hidx
  refine exists_isCompl_of_equivariant_projection ρ ((Fintype.card (G ⧸ N) : L)⁻¹ • Q)
    (fun v => W.smul_mem _ (hQW v)) (fun w hw => ?_) fun g => ?_
  · rw [LinearMap.smul_apply, hQw w hw, ← Nat.cast_smul_eq_nsmul L, smul_smul,
      inv_mul_cancel₀ hcard, one_smul]
  · rw [mul_smul_comm, smul_mul_assoc, hQcomm]

end Stacks.EtaleCohomology

end
