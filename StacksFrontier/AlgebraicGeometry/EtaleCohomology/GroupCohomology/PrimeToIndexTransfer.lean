module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.DiscreteCochains

/-!
# Descending a degree-two cochain statement along a subgroup of invertible index

Let `G` be a topological group, `U` a subgroup of finite index `n`, and `M` a discrete
`G`-module on which `n` is invertible. If a locally constant `2`-cocycle of `G` with values in
`M` becomes a coboundary on `U`, then it is already a coboundary on `G`. This is the
restriction–corestriction argument `cor ∘ res = n`, carried out on cochains so that no transfer
map has to be constructed: the trivialization over `U` is turned into a trivialization over `G`
by an explicit formula summed over the right cosets of `U`.

## Main results

* `Stacks.GroupCohomology.exists_dOne_eq_of_transversal`: **the transfer**, with a system of
  representatives for the right cosets `U \ G` given as data.

## Implementation notes

Write `t = u(t) · s(t)` for the decomposition of `t ∈ G` along `G = ⨆ᵢ U sᵢ`, let `F` be the
cocycle, normalized so that `F (g, 1) = 0`, and let `y : U → M` trivialize `F` on `U`. The proof
has three steps.

The first is the auxiliary `1`-cochain `lam t = y (u t) - F (u t, s t)` on the whole of `G`,
which satisfies `F (w, t) = w • lam t - lam (w * t) + lam w` for `w ∈ U` and *arbitrary* `t ∈ G`
— the mixed coboundary relation, which is what the trivialization over `U` buys. It is locally
constant because `t ↦ u t` and `t ↦ s t` are continuous, the latter because the cosets are open.

The second is the two-variable function `X γ t = F (t, γ) - lam t + lam (t * γ)`. The correction
by `lam` makes it `U`-equivariant in `t`, `X γ (w * t) = w • X γ t` for `w ∈ U`, which is the
statement that `γ ↦ X γ` is a `1`-cochain with values in the module coinduced from `U`; and the
`lam` terms cancel in the `2`-cocycle identity, so `X` trivializes `F` there:
`X γ₂ (t * γ₁) - X (γ₁ * γ₂) t + X γ₁ t = t • F (γ₁, γ₂)`.

The third is the average `S γ = ∑ᵢ (sᵢ)⁻¹ • X γ sᵢ`. The `U`-equivariance of `X` makes the sum
behave like a norm: `γ₁ • S γ₂ = ∑ᵢ (sᵢ)⁻¹ • X γ₂ (sᵢ * γ₁)`, because right translation by `γ₁`
permutes the cosets, and feeding the cocycle identity for `X` into that gives
`dOne S = n • F`. Multiplying by an inverse of `n` on `M` finishes the proof.

## References

* [Stacks Project, Tag 03R8](https://stacks.math.columbia.edu/tag/03R8), part (2), where the
  subgroup is the preimage of a `p`-Sylow subgroup of a finite quotient and the coefficients are
  killed by `p`.
-/

@[expose] public section

open groupCohomology

universe u v

namespace Stacks.GroupCohomology

variable {G : Type u} [Group G]
  {M : Type v} [AddCommGroup M] [DistribMulAction G M]

/-- The action of a group element commutes with multiplication by an integer. -/
private lemma smul_zsmul (g : G) (k : ℤ) (m : M) : g • (k • m) = k • (g • m) :=
  (AddMonoidHom.mk' (fun m : M ↦ g • m) (smul_add g)).map_zsmul k m

/-- A `2`-cocycle satisfies `F (g, 1) = g • F (1, 1)`. -/
lemma isCocycle₂_apply_one {F : G × G → M} (hF : IsCocycle₂ F) (g : G) :
    F (g, 1) = g • F (1, 1) := by
  have h := hF g 1 1
  simp only [mul_one] at h
  exact add_right_cancel h

/-- A `2`-cocycle can be normalized so that `F (g, 1) = 0`, by subtracting the coboundary of the
constant `1`-cochain `F (1, 1)`. -/
lemma isCocycle₂_sub_dOne_const {F : G × G → M} (hF : IsCocycle₂ F) :
    IsCocycle₂ (fun p ↦ F p - dOne (fun _ : G ↦ F (1, 1)) p) ∧
      (∀ g : G, F (g, 1) - dOne (fun _ : G ↦ F (1, 1)) (g, 1) = 0) := by
  refine ⟨fun g h j ↦ ?_, fun g ↦ ?_⟩
  · have h1 := hF g h j
    have h2 := isCocycle₂_dOne (M := M) (fun _ : G ↦ F (1, 1)) g h j
    simp only [smul_sub]
    linear_combination (norm := abel) h1 - h2
  · rw [isCocycle₂_apply_one hF g]
    simp only [dOne_apply]
    abel

variable [TopologicalSpace G] [IsTopologicalGroup G]

section Transfer

variable (U : Subgroup G) {ι : Type u} [Fintype ι] (rep : ι → G) (idx : G → ι)

/-- The right-coset decomposition `t = u t * rep (idx t)`. -/
private def cosetPart : G → G := fun t ↦ t * (rep (idx t))⁻¹

/-- **The transfer on cochains.** If `F` is a locally constant `2`-cocycle of `G` with values in
`M`, normalized at `1`, whose restriction to a subgroup `U` is the coboundary of a locally
constant `1`-cochain `y`, and if the number `n` of right cosets of `U` is invertible on `M`, then
`F` is the coboundary of a locally constant `1`-cochain on `G`. -/
theorem exists_dOne_eq_of_transversal
    (hidx : IsLocallyConstant idx)
    (hmem : ∀ g : G, g * (rep (idx g))⁻¹ ∈ U)
    (hidx_rep : ∀ i, idx (rep i) = i)
    (hidx_mul : ∀ w ∈ U, ∀ g : G, idx (w * g) = idx g)
    (hrep_one : rep (idx 1) = 1)
    (k : ℤ) (hk : ∀ m : M, (k * (Fintype.card ι : ℤ)) • m = m)
    (F : G × G → M) (hFlc : IsLocallyConstant F) (hF : IsCocycle₂ F)
    (hF1 : ∀ g : G, F (g, 1) = 0)
    (y : G → M) (hylc : IsLocallyConstant y)
    (hy : ∀ w ∈ U, ∀ v ∈ U, w • y v - y (w * v) + y w = F (w, v)) :
    ∃ x : G → M, IsLocallyConstant x ∧ dOne x = F := by
  classical
  set s : G → G := fun t ↦ rep (idx t) with hs
  set u : G → G := fun t ↦ t * (s t)⁻¹ with hu
  have hu_mem : ∀ t, u t ∈ U := hmem
  have hu_eq : ∀ t, u t * s t = t := by intro t; simp [hu]
  have hs_mul : ∀ w ∈ U, ∀ t, s (w * t) = s t := by
    intro w hw t; simp only [hs, hidx_mul w hw t]
  have hu_mul : ∀ w ∈ U, ∀ t, u (w * t) = w * u t := by
    intro w hw t
    simp only [hu, hs_mul w hw t]
    group
  have hs_rep : ∀ i, s (rep i) = rep i := by intro i; simp [hs, hidx_rep]
  have hu_rep : ∀ i, u (rep i) = 1 := by intro i; simp [hu, hs_rep]
  have hs_one_of_mem : ∀ w ∈ U, s w = 1 := by
    intro w hw
    have : s w = s (w * 1) := by rw [mul_one]
    rw [this, hs_mul w hw 1]
    simpa [hs] using hrep_one
  have hu_one_of_mem : ∀ w ∈ U, u w = w := by
    intro w hw; simp [hu, hs_one_of_mem w hw]
  have hy_one : y 1 = 0 := by simpa [hF1] using hy 1 U.one_mem 1 U.one_mem
  have hsc : Continuous s := (hidx.comp rep).continuous
  have huc : Continuous u := continuous_id.mul hsc.inv
  set lam : G → M := fun t ↦ y (u t) - F (u t, s t) with hlam
  have hlamlc : IsLocallyConstant lam := by
    have h1 : IsLocallyConstant fun t ↦ y (u t) := hylc.comp_continuous huc
    have h2 : IsLocallyConstant fun t ↦ F (u t, s t) :=
      hFlc.comp_continuous (huc.prodMk hsc)
    exact h1.comp₂ h2 (· - ·)
  have hlam_mem : ∀ w ∈ U, lam w = y w := by
    intro w hw
    simp only [hlam, hu_one_of_mem w hw, hs_one_of_mem w hw, hF1, sub_zero]
  have key : ∀ w ∈ U, ∀ t : G, w • lam t - lam (w * t) + lam w = F (w, t) := by
    intro w hw t
    have h1 := hy w hw (u t) (hu_mem t)
    have h2 := hF w (u t) (s t)
    rw [hu_eq t] at h2
    have hlw : lam (w * t) = y (w * u t) - F (w * u t, s t) := by
      simp only [hlam, hu_mul w hw t, hs_mul w hw t]
    rw [hlw, hlam_mem w hw, show lam t = y (u t) - F (u t, s t) from rfl, smul_sub]
    linear_combination (norm := abel) h1 + h2
  set X : G → G → M := fun γ t ↦ F (t, γ) - lam t + lam (t * γ) with hX
  have hX_mem : ∀ w ∈ U, ∀ (γ t : G), X γ (w * t) = w • X γ t := by
    intro w hw γ t
    have k1 : lam (w * t) = w • lam t + lam w - F (w, t) := by
      rw [← key w hw t]; abel
    have k2 : lam (w * t * γ) = w • lam (t * γ) + lam w - F (w, t * γ) := by
      rw [mul_assoc, ← key w hw (t * γ)]; abel
    have k3 := hF w t γ
    simp only [hX, k1, k2, smul_sub, smul_add]
    linear_combination (norm := abel) k3
  have hX_coc : ∀ γ₁ γ₂ t : G, X γ₂ (t * γ₁) - X (γ₁ * γ₂) t + X γ₁ t = t • F (γ₁, γ₂) := by
    intro γ₁ γ₂ t
    have k3 := hF t γ₁ γ₂
    simp only [hX, mul_assoc]
    linear_combination (norm := abel) k3
  set S : G → M := fun γ ↦ ∑ i : ι, (rep i)⁻¹ • X γ (rep i) with hS
  have hXlc : ∀ t : G, IsLocallyConstant fun γ ↦ X γ t := by
    intro t
    have h1 : IsLocallyConstant fun γ ↦ F (t, γ) :=
      hFlc.comp_continuous (continuous_const.prodMk continuous_id)
    have h2 : IsLocallyConstant fun γ : G ↦ lam (t * γ) :=
      hlamlc.comp_continuous (continuous_const.mul continuous_id)
    exact (h1.comp₂ (IsLocallyConstant.const (lam t)) (· - ·)).comp₂ h2 (· + ·)
  have hSlc : IsLocallyConstant S := by
    have : ∀ (t : Finset ι), IsLocallyConstant fun γ ↦ ∑ i ∈ t, (rep i)⁻¹ • X γ (rep i) := by
      intro t
      induction t using Finset.induction with
      | empty =>
          simp only [Finset.sum_empty]
          exact IsLocallyConstant.const _
      | insert a t ha ih =>
          have hterm : IsLocallyConstant fun γ ↦ (rep a)⁻¹ • X γ (rep a) :=
            (hXlc (rep a)).comp fun m ↦ (rep a)⁻¹ • m
          simpa [Finset.sum_insert ha] using hterm.comp₂ ih (· + ·)
    simpa [hS] using this Finset.univ
  have hcomp : ∀ (γ : G) (i : ι), idx (rep (idx (rep i * γ)) * γ⁻¹) = i := by
    intro γ i
    set j := idx (rep i * γ) with hj
    have hw : (rep i * γ) * (rep j)⁻¹ ∈ U := hmem _
    have hrepj : rep j * γ⁻¹ = ((rep i * γ) * (rep j)⁻¹)⁻¹ * rep i := by
      have : rep j = ((rep i * γ) * (rep j)⁻¹)⁻¹ * (rep i * γ) := by group
      rw [this]; group
    rw [hrepj, hidx_mul _ (U.inv_mem hw) (rep i), hidx_rep]
  have hperm : ∀ γ : G, Function.Bijective fun i ↦ idx (rep i * γ) := by
    intro γ
    refine Function.bijective_iff_has_inverse.mpr ⟨fun i ↦ idx (rep i * γ⁻¹), ?_, ?_⟩
    · exact hcomp γ
    · intro i
      simpa using hcomp γ⁻¹ i
  have hshift : ∀ γ₁ γ₂ : G, γ₁ • S γ₂ = ∑ i : ι, (rep i)⁻¹ • X γ₂ (rep i * γ₁) := by
    intro γ₁ γ₂
    rw [hS, Finset.smul_sum]
    refine (Fintype.sum_bijective _ (hperm γ₁) _ _ fun i ↦ ?_).symm
    set j := idx (rep i * γ₁) with hj
    have hw : (rep i * γ₁) * (rep j)⁻¹ ∈ U := hmem _
    have hrw : rep i * γ₁ = ((rep i * γ₁) * (rep j)⁻¹) * rep j := by group
    rw [hrw, hX_mem _ hw, smul_smul, show (rep i)⁻¹ * ((rep i * γ₁) * (rep j)⁻¹) =
      γ₁ * (rep j)⁻¹ by group, ← smul_smul]
  have hdS : dOne S = fun p ↦ ((Fintype.card ι : ℤ)) • F p := by
    funext p
    obtain ⟨γ₁, γ₂⟩ := p
    have hstep : ∀ i : ι, (rep i)⁻¹ • X γ₂ (rep i * γ₁) =
        (rep i)⁻¹ • X (γ₁ * γ₂) (rep i) - (rep i)⁻¹ • X γ₁ (rep i) + F (γ₁, γ₂) := by
      intro i
      have : X γ₂ (rep i * γ₁) = X (γ₁ * γ₂) (rep i) - X γ₁ (rep i) + rep i • F (γ₁, γ₂) := by
        rw [← hX_coc γ₁ γ₂ (rep i)]; abel
      rw [this, smul_add, smul_sub, smul_smul, inv_mul_cancel, one_smul]
    have h0 : γ₁ • S γ₂ = S (γ₁ * γ₂) - S γ₁ + ((Fintype.card ι : ℤ)) • F (γ₁, γ₂) := by
      rw [hshift γ₁ γ₂]
      simp only [hstep, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_univ]
      rw [Nat.cast_smul_eq_nsmul]
    simp only [dOne_apply]
    rw [h0]
    abel
  refine ⟨fun γ ↦ k • S γ, hSlc.comp fun m ↦ k • m, ?_⟩
  funext p
  obtain ⟨γ₁, γ₂⟩ := p
  have h1 : dOne (fun γ ↦ k • S γ) (γ₁, γ₂) = k • dOne S (γ₁, γ₂) := by
    simp only [dOne_apply, smul_zsmul, smul_sub, smul_add]
  rw [h1, hdS, smul_smul, hk]

end Transfer

end Stacks.GroupCohomology

end
