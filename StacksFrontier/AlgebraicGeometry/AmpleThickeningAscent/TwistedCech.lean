module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.QuasiAffineAscent

/-!
# The twisted Čech lift along a first-order thickening

Let `k : Y ⟶ Y'` be a first-order thickening, let `U i` be finitely many affine opens of `Y'`
with affine pairwise intersections, and let `w i j` be functions on the overlaps satisfying the
cocycle rule `w i l = w i j * w j l`. A family `ρ i` of functions on the opens `k⁻¹(U i)` of `Y`
that transforms by `ρ i = (w i j)ⁿ ρ j` is the family of coordinates of a section of `𝓛ⁿ` on `Y`
for the invertible module `𝓛` on `Y'` with transition functions `w`. If one member `ρ a` of the
family vanishes nowhere and the others vanish exactly off `k⁻¹(U a)`, then some power
`ρ i ^ (N + 1)` is the image of a family `f i` of functions on the `U i` that transforms by
`(w i j) ^ (n (N + 1))`.

## Main results

* `Stacks.AmpleThickeningAscent.exists_twisted_lift`: the lift.

## References

* [Stacks Project, Tag 09MS](https://stacks.math.columbia.edu/tag/09MS)
* [Stacks Project, Tag 09MW](https://stacks.math.columbia.edu/tag/09MW)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.Thickenings

universe u

namespace Stacks.AmpleThickeningAscent

variable {Y Y' : Scheme.{u}} {k : Y ⟶ Y'}

/-- Let `k : Y ⟶ Y'` be a first-order thickening, `U i` finitely many affine opens of `Y'` with
affine pairwise intersections, and `w i j` functions on the overlaps satisfying the cocycle rule
on triple overlaps. If a family `ρ i` of functions on the `k⁻¹(U i)` transforms by
`ρ i = (w i j)ⁿ ρ j` and `Y.basicOpen (ρ i) = k⁻¹(U i ⊓ U a)` for every `i`, then for some `N`
there is a family `f i` of functions on the `U i` that transforms by `(w i j) ^ (n (N + 1))` with
`k.app (U i) (f i) = ρ i ^ (N + 1)`. -/
theorem exists_twisted_lift (hk : IsFirstOrderThickening k) {ι : Type*} [Finite ι]
    (U : ι → Y'.Opens) (hUaff : ∀ i, IsAffineOpen (U i))
    (hPaff : ∀ i j, IsAffineOpen (U i ⊓ U j))
    (w : ∀ i j, Γ(Y', U i ⊓ U j))
    (hcoc : ∀ i j l, (w i j |_ₗ (U i ⊓ U j ⊓ U l) ⟪inf_le_left⟫ ) *
        (w j l |_ₗ (U i ⊓ U j ⊓ U l) ⟪le_inf (inf_le_left.trans inf_le_right) inf_le_right⟫ )
      = w i l |_ₗ (U i ⊓ U j ⊓ U l) ⟪le_inf (inf_le_left.trans inf_le_left) inf_le_right⟫ )
    (n : ℕ) (a : ι) (ρ : ∀ i, Γ(Y, k ⁻¹ᵁ U i))
    (hρ : ∀ i j, ρ i |_ₗ (k ⁻¹ᵁ (U i ⊓ U j)) ⟪k.preimage_mono inf_le_left⟫
      = (k.app (U i ⊓ U j) (w i j)) ^ n *
          ρ j |_ₗ (k ⁻¹ᵁ (U i ⊓ U j)) ⟪k.preimage_mono inf_le_right⟫ )
    (hD : ∀ i, Y.basicOpen (ρ i) = k ⁻¹ᵁ (U i ⊓ U a)) :
    ∃ N : ℕ, ∃ f : ∀ i, Γ(Y', U i),
      (∀ i j, f i |_ₗ (U i ⊓ U j) ⟪inf_le_left⟫
        = (w i j) ^ (n * (N + 1)) * f j |_ₗ (U i ⊓ U j) ⟪inf_le_right⟫) ∧
      ∀ i, k.app (U i) (f i) = ρ i ^ (N + 1) := by
  classical
  have : IsClosedImmersion k := hk.1
  have hT : IsThickening k := hk.isThickening
  have hinj : ∀ {V₁ V₂ : Y'.Opens}, k ⁻¹ᵁ V₁ = k ⁻¹ᵁ V₂ → V₁ = V₂ := fun {V₁ V₂} h => by
    rw [← hT.opensCongr_preimage V₁, ← hT.opensCongr_preimage V₂, h]
  let res : ∀ {A B : Y'.Opens}, B ≤ A → Γ(Y', A) →+* Γ(Y', B) :=
    fun {A B} h => (Y'.presheaf.map (homOfLE h).op).hom
  have res_eq : ∀ {A B : Y'.Opens} (h : B ≤ A) (x : Γ(Y', A)), res h x = x |_ₗ B ⟪h⟫ :=
    fun _ _ => rfl
  have res_res : ∀ {A B C : Y'.Opens} (h₁ : B ≤ A) (h₂ : C ≤ B) (x : Γ(Y', A)),
      res h₂ (res h₁ x) = res (h₂.trans h₁) x :=
    fun h₁ h₂ x => TopCat.Presheaf.restrict_restrict h₂ h₁ x
  let resY : ∀ {A B : Y.Opens}, B ≤ A → Γ(Y, A) →+* Γ(Y, B) :=
    fun {A B} h => (Y.presheaf.map (homOfLE h).op).hom
  have resY_res : ∀ {A B C : Y.Opens} (h₁ : B ≤ A) (h₂ : C ≤ B) (x : Γ(Y, A)),
      resY h₂ (resY h₁ x) = resY (h₂.trans h₁) x :=
    fun h₁ h₂ x => TopCat.Presheaf.restrict_restrict h₂ h₁ x
  have app_res : ∀ {A B : Y'.Opens} (h : B ≤ A) (x : Γ(Y', A)),
      k.app B (res h x) = resY (k.preimage_mono h) (k.app A x) :=
    fun h x => app_restrict k h (k.preimage_mono h) x
  choose β hβ using fun i => Scheme.Hom.app_surjective k (U i) (hUaff i) (ρ i)
  obtain ⟨γ, hγ⟩ := Scheme.Hom.app_surjective k (U a) (hUaff a) (ρ a)
  let W : ι → Y'.Opens := fun i => U i ⊓ U a
  have hWi : ∀ i, W i ≤ U i := fun i => inf_le_left
  have hWeq : ∀ i, W i = Y'.basicOpen (β i) := fun i =>
    hinj (by rw [Scheme.preimage_basicOpen, hβ i, hD i])
  let g : ∀ i, Γ(Y', W i) := fun i => w i a ^ n * res inf_le_right γ
  have hg : ∀ i, k.app (W i) (g i) = resY (k.preimage_mono (hWi i)) (ρ i) := by
    intro i
    simp only [g, map_mul, map_pow, app_res, hγ]
    exact (hρ i a).symm
  have hstep : ∀ i, ∃ (m : ℕ) (F : Γ(Y', U i)), (k.app (U i)) F = 0 ∧
      res (hWi i) F = (res (hWi i) (β i)) ^ m * (res (hWi i) (β i) - g i) := by
    intro i
    obtain ⟨m, y, hy⟩ := exists_eq_pow_mul_of_isAffineOpen' (hUaff i) (β i) (hWi i)
      (hWeq i) (res (hWi i) (β i) - g i)
    have hezero : (k.app (W i)) (res (hWi i) (β i) - g i) = 0 := by
      rw [map_sub, app_res, hβ i, hg i, sub_self]
    have hy' : res (hWi i) y = (res (hWi i) (β i)) ^ m * (res (hWi i) (β i) - g i) := hy
    have hy0 : resY (k.preimage_mono (hWi i)) ((k.app (U i)) y) = 0 := by
      rw [← app_res (hWi i), hy', map_mul, map_pow, hezero, mul_zero]
    obtain ⟨p, hp⟩ := exists_pow_mul_eq_zero_of_res_eq_zero ((hUaff i).preimage k).isCompact
      ((k.app (U i)) y) (ρ i) (k.preimage_mono (hWi i)) (hD i).symm hy0
    refine ⟨p + m, β i ^ p * y, ?_, ?_⟩
    · rwa [map_mul, map_pow, hβ i]
    · rw [map_mul, map_pow, hy', ← mul_assoc, ← pow_add]
  choose m F hF0 hFe using hstep
  obtain ⟨M, hM⟩ := Finite.exists_le m
  have hGstep : ∀ i, ∃ G : Γ(Y', U i), (k.app (U i)) G = 0 ∧
      res (hWi i) G = (res (hWi i) (β i)) ^ M * (res (hWi i) (β i) - g i) := by
    intro i
    refine ⟨β i ^ (M - m i) * F i, ?_, ?_⟩
    · rw [map_mul, map_pow, hF0 i, mul_zero]
    · rw [map_mul, map_pow, hFe i, ← mul_assoc, ← pow_add, Nat.sub_add_cancel (hM i)]
  choose G hG0 hGe using hGstep
  let P : ι → ι → Y'.Opens := fun i j => U i ⊓ U j
  let Q : ι → ι → Y'.Opens := fun i j => U i ⊓ U j ⊓ U a
  have hQP : ∀ i j, Q i j ≤ P i j := fun i j => inf_le_left
  have hQW : ∀ i j, Q i j ≤ W i := fun i j => le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have hQWj : ∀ i j, Q i j ≤ W j :=
    fun i j => le_inf (inf_le_left.trans inf_le_right) inf_le_right
  let x : ∀ i j, Γ(Y', P i j) := fun i j => res inf_le_left (β i)
  let y : ∀ i j, Γ(Y', P i j) := fun i j => w i j ^ n * res inf_le_right (β j)
  let gx : ∀ i j, Γ(Y', P i j) := fun i j => res inf_le_left (G i)
  let gy : ∀ i j, Γ(Y', P i j) := fun i j => w i j ^ (n * (M + 1)) * res inf_le_right (G j)
  have hkx : ∀ i j, k.app (P i j) (x i j) = resY (k.preimage_mono inf_le_left) (ρ i) :=
    fun i j => by simp only [x, app_res, hβ i]
  have hky : ∀ i j, k.app (P i j) (y i j) = resY (k.preimage_mono inf_le_left) (ρ i) := by
    intro i j
    simp only [y, map_mul, map_pow, app_res, hβ j]
    exact (hρ i j).symm
  have hxy : ∀ i j, k.app (P i j) (x i j - y i j) = 0 := fun i j => by
    rw [map_sub, hkx, hky, sub_self]
  have hgy0 : ∀ i j, k.app (P i j) (gy i j) = 0 := fun i j => by
    simp only [gy, map_mul, app_res, hG0 j, map_zero, mul_zero]
  have hpairstep : ∀ i j, ∃ q : ℕ,
      x i j ^ q * (x i j ^ M * (x i j - y i j) - (gx i j - gy i j)) = 0 := by
    intro i j
    have hQ : Q i j = Y'.basicOpen (x i j) := by
      change Q i j = Y'.basicOpen (res inf_le_left (β i))
      rw [res_eq, basicOpen_restrict_eq, ← hWeq i]
      exact le_antisymm (le_inf inf_le_left (le_inf (inf_le_left.trans inf_le_left) inf_le_right))
        (le_inf inf_le_left (inf_le_right.trans inf_le_right))
    have hxQ : res (hQP i j) (x i j) = res (hQW i j) (res (hWi i) (β i)) := by
      simp only [x, res_res]
    have hyQ : res (hQP i j) (y i j) =
        res (hQP i j) (w i j) ^ n * res (hQWj i j) (res (hWi j) (β j)) := by
      simp only [y, map_mul, map_pow, res_res]
    have hgxQ : res (hQP i j) (gx i j) = res (hQW i j) (res (hWi i) (G i)) := by
      simp only [gx, res_res]
    have hgyQ : res (hQP i j) (gy i j) =
        res (hQP i j) (w i j) ^ (n * (M + 1)) * res (hQWj i j) (res (hWi j) (G j)) := by
      simp only [gy, map_mul, map_pow, res_res]
    have hcocQ : res (hQP i j) (w i j) * res (hQWj i j) (w j a) =
        res (hQW i j) (w i a) :=
      hcoc i j a
    have hgQ : res (hQW i j) (g i) =
        res (hQP i j) (w i j) ^ n * res (hQWj i j) (g j) := by
      simp only [g, map_mul, map_pow, res_res]
      rw [← hcocQ, mul_pow, mul_assoc]
    refine exists_pow_mul_sub_eq_zero hk (hPaff i j) (hQP i j) (x i j) (y i j) (gx i j)
      (gy i j) (res (hQW i j) (g i)) M hQ (hxy i j) ?_ ?_ ?_
    · change k.app (Q i j) (res (hQP i j) (y i j) - res (hQW i j) (g i)) = 0
      rw [map_sub, app_res, hky, resY_res, app_res, hg i, resY_res, sub_self]
    · change res (hQP i j) (gx i j) =
        (res (hQP i j) (x i j)) ^ M * (res (hQP i j) (x i j) - res (hQW i j) (g i))
      rw [hgxQ, hxQ, hGe i, map_mul, map_pow, map_sub]
    · change res (hQP i j) (gy i j) =
        (res (hQP i j) (y i j)) ^ M * (res (hQP i j) (y i j) - res (hQW i j) (g i))
      rw [hgyQ, hGe j, hyQ, hgQ, map_mul, map_pow, map_sub]
      ring
  choose q hq using hpairstep
  obtain ⟨K, hK⟩ := Finite.exists_le fun p : ι × ι => q p.1 p.2
  let f : ∀ i, Γ(Y', U i) := fun i =>
    β i ^ (K + M + 1) - ((K + M + 1 : ℕ) : Γ(Y', U i)) * (β i ^ K * G i)
  refine ⟨K + M, f, fun i j => ?_, fun i => ?_⟩
  · have key := corrected_lift_eq hk (hPaff i j) (x i j) (y i j) (gx i j) (gy i j) K M
      (hxy i j) (hgy0 i j) (Thickenings.pow_mul_eq_zero_of_le (hK (i, j)) (hq i j))
    change res inf_le_left (f i) = w i j ^ (n * (K + M + 1)) * res inf_le_right (f j)
    simp only [f, map_sub, map_mul, map_pow, map_natCast]
    change x i j ^ (K + M + 1) - ((K + M + 1 : ℕ) : Γ(Y', P i j)) * (x i j ^ K * gx i j) = _
    rw [key]
    simp only [y, gy]
    ring
  · simp only [f, map_sub, map_mul, map_pow, map_natCast, hG0 i, mul_zero, sub_zero, hβ i]

end Stacks.AmpleThickeningAscent

end
