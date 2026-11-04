module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CliffordSemisimple
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Semisimplicity of the restriction to a subgroup of finite index

Let `ρ : G → End(V)` be a representation over a field of characteristic `0`, and `N` a normal
subgroup of finite index of `G`. If the restriction of `ρ` to `N` is semisimple (every `N`-stable
subspace has an `N`-stable complement), so is `ρ`. Consequently the pullback `ρ ∘ Φ` of an
irreducible `ρ : G → GL_ι(L)` along `Φ : G₀ → G` whose image contains a normal subgroup of finite
index is semisimple.

## Main results

* `Stacks.EtaleCohomology.exists_isCompl_of_normal_finiteIndex`: a representation whose
  restriction to a normal subgroup of finite index is semisimple is semisimple.
* `Stacks.EtaleCohomology.exists_isCompl_comp_of_irreducible`: the pullback of an irreducible
  representation along a homomorphism whose image contains a normal subgroup of finite index is
  semisimple.
-/

@[expose] public noncomputable section

open Matrix

namespace Stacks.EtaleCohomology

section Averaging

variable {L V : Type*} [Field L] [AddCommGroup V] [Module L V] {G : Type*} [Group G]

/-- `ρ(g) * ρ(g⁻¹) = 1`. -/
private theorem map_mul_map_inv (ρ : G →* Module.End L V) (g : G) : ρ g * ρ g⁻¹ = 1 := by
  rw [← map_mul, mul_inv_cancel, map_one]

/-- `ρ(g⁻¹) * ρ(g) = 1`. -/
private theorem map_inv_mul_map (ρ : G →* Module.End L V) (g : G) : ρ g⁻¹ * ρ g = 1 := by
  rw [← map_mul, inv_mul_cancel, map_one]

/-- `ρ(g⁻¹) ∘ ρ(g) = 1`. -/
theorem map_inv_apply_map_apply (ρ : G →* Module.End L V) (g : G) (v : V) :
    ρ g⁻¹ (ρ g v) = v := by
  rw [← Module.End.mul_apply, map_inv_mul_map, Module.End.one_apply]

/-- `ρ(g) ∘ ρ(g⁻¹) = 1`. -/
theorem map_apply_map_inv_apply (ρ : G →* Module.End L V) (g : G) (v : V) :
    ρ g (ρ g⁻¹ v) = v := by
  rw [← Module.End.mul_apply, map_mul_map_inv, Module.End.one_apply]

/-- **Averaging over a normal subgroup of finite index** (characteristic `0`): if the restriction
of `ρ` to a normal subgroup `N` of finite index is semisimple, every `G`-stable subspace has a
`G`-stable complement. -/
public theorem exists_isCompl_of_normal_finiteIndex [CharZero L] (ρ : G →* Module.End L V)
    (N : Subgroup G) [N.Normal] [N.FiniteIndex]
    (hN : ∀ W : Submodule L V, (∀ n ∈ N, W ≤ W.comap (ρ n)) →
      ∃ W', IsCompl W W' ∧ ∀ n ∈ N, W' ≤ W'.comap (ρ n))
    (W : Submodule L V) (hW : ∀ g, W ≤ W.comap (ρ g)) :
    ∃ W', IsCompl W W' ∧ ∀ g, W' ≤ W'.comap (ρ g) := by
  classical
  have : Fintype (G ⧸ N) := Fintype.ofFinite _
  obtain ⟨C, hWC, hC⟩ := hN W fun n _ => hW n
  set π : Module.End L V := W.projection C hWC with hπ_def
  have hπW : ∀ v, π v ∈ W := fun v => Submodule.projection_apply_mem hWC v
  have hπw : ∀ w ∈ W, π w = w := fun w hw => Submodule.projection_apply_of_mem_left hWC hw
  have hπc : ∀ c ∈ C, π c = 0 := fun c hc => Submodule.projection_apply_of_mem_right hWC hc
  have hπN : ∀ n ∈ N, ρ n * π = π * ρ n := by
    intro n hn
    refine LinearMap.ext fun v => ?_
    have hsplit : v = π v + (v - π v) := by abel
    have h1 : π (ρ n (π v)) = ρ n (π v) := hπw _ (hW n (hπW v))
    have h2 : π (ρ n (v - π v)) = 0 := hπc _ (hC n hn (Submodule.sub_projection_mem hWC v))
    show ρ n (π v) = π (ρ n v)
    conv_rhs => rw [hsplit, map_add, map_add, h1, h2, add_zero]
  let t : G → Module.End L V := fun h => ρ h * π * ρ h⁻¹
  have ht : ∀ h, ∀ n ∈ N, t (h * n) = t h := by
    intro h n hn
    have e1 : ρ n * π * ρ n⁻¹ = π := by
      rw [hπN n hn, mul_assoc, map_mul_map_inv, mul_one]
    calc t (h * n) = ρ h * (ρ n * π * ρ n⁻¹) * ρ h⁻¹ := by
          simp only [t, _root_.mul_inv_rev, map_mul, mul_assoc]
      _ = t h := by rw [e1]
  have htq : ∀ h : G, ∀ q : G ⧸ N, (QuotientGroup.mk h : G ⧸ N) = q → t q.out = t h := by
    intro h q hq
    have hq' : (QuotientGroup.mk q.out : G ⧸ N) = QuotientGroup.mk h := by
      rw [QuotientGroup.out_eq', hq]
    obtain ⟨n, hn, hn'⟩ : ∃ n ∈ N, q.out = h * n :=
      ⟨h⁻¹ * q.out, QuotientGroup.eq.mp hq'.symm, by group⟩
    rw [hn', ht h n hn]
  have hρt : ∀ g h, ρ g * t h = t (g * h) * ρ g := by
    intro g h
    calc ρ g * t h = ρ g * ρ h * π * ρ h⁻¹ * (ρ g⁻¹ * ρ g) := by
          rw [map_inv_mul_map, mul_one]; simp only [t, mul_assoc]
      _ = t (g * h) * ρ g := by simp only [t, _root_.mul_inv_rev, map_mul, mul_assoc]
  set Q : Module.End L V := ∑ q : G ⧸ N, t q.out with hQ_def
  have hQcomm : ∀ g, ρ g * Q = Q * ρ g := by
    intro g
    rw [hQ_def, Finset.mul_sum, Finset.sum_mul]
    have h1 : ∀ q : G ⧸ N, ρ g * t q.out = t ((QuotientGroup.mk g : G ⧸ N) * q).out * ρ g := by
      intro q
      rw [hρt, htq (g * q.out) _ (by rw [QuotientGroup.mk_mul, QuotientGroup.out_eq'])]
    simp_rw [h1]
    exact Fintype.sum_equiv (Equiv.mulLeft (QuotientGroup.mk g : G ⧸ N)) _ _ fun q => rfl
  have hQW : ∀ v, Q v ∈ W := fun v => by
    rw [hQ_def, LinearMap.sum_apply]
    exact Submodule.sum_mem _ fun q _ => hW q.out (hπW _)
  have hQw : ∀ w ∈ W, Q w = (Fintype.card (G ⧸ N)) • w := by
    intro w hw
    rw [hQ_def, LinearMap.sum_apply]
    have : ∀ q : G ⧸ N, t q.out w = w := by
      intro q
      show ρ q.out (π (ρ q.out⁻¹ w)) = w
      rw [hπw _ (hW _ hw), map_apply_map_inv_apply]
    simp only [this, Finset.sum_const, Finset.card_univ]
  have hcard : (Fintype.card (G ⧸ N) : L) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  set P : Module.End L V := (Fintype.card (G ⧸ N) : L)⁻¹ • Q with hP_def
  have hPW : ∀ v, P v ∈ W := fun v => W.smul_mem _ (hQW v)
  let P' : V →ₗ[L] W := P.codRestrict W hPW
  have hP' : ∀ x : W, P' x = x := by
    intro x
    apply Subtype.ext
    show (Fintype.card (G ⧸ N) : L)⁻¹ • Q x = x
    rw [hQw x x.2, ← Nat.cast_smul_eq_nsmul L, smul_smul, inv_mul_cancel₀ hcard, one_smul]
  refine ⟨LinearMap.ker P', LinearMap.isCompl_of_proj hP', fun g v hv => ?_⟩
  have hv' : P v = 0 := congrArg Subtype.val (LinearMap.mem_ker.mp hv)
  rw [Submodule.mem_comap, LinearMap.mem_ker]
  apply Subtype.ext
  show P (ρ g v) = 0
  have hc : P (ρ g v) = ρ g (P v) := by
    show (Fintype.card (G ⧸ N) : L)⁻¹ • Q (ρ g v) =
      ρ g ((Fintype.card (G ⧸ N) : L)⁻¹ • Q v)
    rw [map_smul, ← Module.End.mul_apply Q, ← hQcomm, Module.End.mul_apply]
  rw [hc, hv', map_zero]

end Averaging

section Pullback

variable {L : Type*} [Field L] {ι : Type*} [Fintype ι] [DecidableEq ι] {G G₀ : Type*} [Group G]
  [Group G₀]

/-- The action of `GL_ι(L)` on `L^ι` by linear automorphisms. -/
def glToLinUnits : GL ι L →* (Module.End L (ι → L))ˣ :=
  Units.map (Matrix.toLinAlgEquiv' (R := L) (n := ι)).toRingEquiv.toMonoidHom

/-- **The pullback of an irreducible representation is semisimple** (characteristic `0`) along
`Φ : G₀ → G` whose image contains a normal subgroup `N` of finite index of `G`. -/
public theorem exists_isCompl_comp_of_irreducible [CharZero L] (ρ : G →* GL ι L) (Φ : G₀ →* G)
    (N : Subgroup G) [N.Normal] [N.FiniteIndex] (hNΦ : N ≤ Φ.range)
    (hirr : ∀ W : Submodule L (ι → L), (∀ g, ∀ v ∈ W, (ρ g).val *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤)
    (W : Submodule L (ι → L)) (hW : ∀ γ, ∀ v ∈ W, (ρ (Φ γ)).val *ᵥ v ∈ W) :
    ∃ W', IsCompl W W' ∧ ∀ γ, ∀ v ∈ W', (ρ (Φ γ)).val *ᵥ v ∈ W' := by
  classical
  let ρu : G →* (Module.End L (ι → L))ˣ := glToLinUnits.comp ρ
  have hρu : ∀ g v, ((ρu g : (Module.End L (ι → L))ˣ) : Module.End L (ι → L)) v = (ρ g).val *ᵥ v :=
    fun g v => Matrix.toLinAlgEquiv'_apply _ v
  let Γ : Subgroup (Module.End L (ι → L))ˣ := ρu.range
  let N' : Subgroup (Module.End L (ι → L))ˣ := N.map ρu
  have hN'Γ : N' ≤ Γ := Subgroup.map_le_range ρu N
  have hnormal : ∀ γ ∈ Γ, ∀ n ∈ N', γ * n * γ⁻¹ ∈ N' := by
    rintro _ ⟨g, rfl⟩ _ ⟨n, hn, rfl⟩
    exact ⟨g * n * g⁻¹, Subgroup.Normal.conj_mem inferInstance n hn g, by simp [map_mul, map_inv]⟩
  have hss : ∀ W, IsStableUnder (Units.val '' (Γ : Set (Module.End L (ι → L))ˣ)) W →
      ∃ W', IsCompl W W' ∧ IsStableUnder (Units.val '' (Γ : Set (Module.End L (ι → L))ˣ)) W' := by
    intro W hW
    rcases hirr W (fun g v hv => by
        rw [← hρu]
        exact hW _ ⟨ρu g, ⟨g, rfl⟩, rfl⟩ hv) with h | h
    · exact ⟨⊤, h ▸ isCompl_bot_top, fun s _ => le_top⟩
    · exact ⟨⊥, h ▸ isCompl_top_bot, fun s _ => bot_le⟩
  let ρ₀ : G₀ →* Module.End L (ι → L) := (Units.coeHom _).comp (ρu.comp Φ)
  have hρ₀ : ∀ γ v, ρ₀ γ v = (ρ (Φ γ)).val *ᵥ v := fun γ v => hρu (Φ γ) v
  let N₀ : Subgroup G₀ := N.comap Φ
  have : N₀.Normal := Subgroup.Normal.comap inferInstance Φ
  have : N₀.FiniteIndex := ⟨by
    rw [Subgroup.index_comap]
    exact (Subgroup.instFiniteIndex_subgroupOf N Φ.range).index_ne_zero⟩
  have hN₀ : ∀ W : Submodule L (ι → L), (∀ n ∈ N₀, W ≤ W.comap (ρ₀ n)) →
      ∃ W', IsCompl W W' ∧ ∀ n ∈ N₀, W' ≤ W'.comap (ρ₀ n) := by
    intro W hW
    have hWN' : IsStableUnder (Units.val '' (N' : Set (Module.End L (ι → L))ˣ)) W := by
      rintro _ ⟨_, ⟨n, hn, rfl⟩, rfl⟩
      obtain ⟨n₀, rfl⟩ := hNΦ hn
      exact hW n₀ hn
    obtain ⟨W', hc, hW'⟩ := exists_isCompl_of_normal Γ N' hN'Γ hnormal hss hWN'
    exact ⟨W', hc, fun n hn => hW' _ ⟨ρu (Φ n), ⟨Φ n, hn, rfl⟩, rfl⟩⟩
  obtain ⟨W', hc, hW'⟩ := exists_isCompl_of_normal_finiteIndex ρ₀ N₀ hN₀ W fun γ v hv => by
    show ρ₀ γ v ∈ W
    rw [hρ₀]
    exact hW γ v hv
  refine ⟨W', hc, fun γ v hv => ?_⟩
  rw [← hρ₀]
  exact hW' γ hv

end Pullback

end Stacks.EtaleCohomology

end
