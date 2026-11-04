module

public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.TautologicalKernelTopChern
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.Formula
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.Injective

/-!
# The class of a section of a projective bundle

Let `π : P ⟶ U` be flat, proper, of relative dimension `n`, and a projective tower of fibre
dimension `n` with twist `ℳ` locally on `U` (for instance a base change of the projective bundle
of a finite locally free module of rank `n + 1` with `𝒪(1)`). Let `𝒞` be finite locally free of
rank `n + 1` on `U` and let

  `0 ⟶ ℱ ⟶ π^*𝒞 ⟶ ℳ ⟶ 0`

be a short exact sequence, so that `ℱ` has rank `n`. Write `ξ = c₁(ℳ)`. For a section
`σ : U ⟶ P` of `π` and an invertible `ℒ ≅ σ^*ℳ` on `U` the class of `σ` is

  `σ_*β = ∑_{i = 0}^{n} c_{n-i}(ℱ^∨) ∩ π^*(c₁(ℒ)^i ∩ β)`

for every `β ∈ A_*(U)`. This is the computation in the proof of [Stacks, Tag 0FGR]: there `π` is
the second projection `P ×_X P ⟶ P` of a projective bundle `P ⟶ X`, `σ` is the diagonal and `ℱ`
is the pullback of the kernel of `p^*ℰ ⟶ 𝒪_P(1)` along the first projection; the source obtains
the formula as a top Chern class of `ℱ^∨ ⊗ π^*ℒ`, whose section vanishes exactly along the
diagonal.

## The proof

Write `f(s, j)(γ) = π_*(ξ^s ∩ c_j(ℱ^∨) ∩ π^*γ)`. The Whitney recursion
`c_{j+1}(ℱ^∨) = c_{j+1}(π^*𝒞^∨) + ξ ∩ c_j(ℱ^∨)` of
`Stacks.Chow.GenuineChern.chernFamily_dualKernel_succ` and the vanishing half of Stacks 02TW give
`f(s, j + 1) = f(s + 1, j)` for `s < n`. Hence `f(s, j)` is `f(s + j, 0) = 0` when `s + j < n`,
it is `f(0, s + j) = 0` when `s ≤ n < s + j` (the class `c_{s+j}(ℱ^∨)` vanishing above the rank),
and it is the identity when `s + j = n` (`pushforward_capPow_chernFamily_dualKernel`).

So the right hand side `y` of the formula satisfies `π_*(ξ^s ∩ y) = c₁(ℒ)^s ∩ β` for `s ≤ n`, and
so does `σ_*β`, since `ξ^s ∩ σ_*β = σ_*(c₁(σ^*ℳ)^s ∩ β)` (Stacks 02SU) and `π ∘ σ = 1`. A class
`x` on `P` with `π_*(ξ^s ∩ x) = 0` for all `s ≤ n` vanishes: by Stacks 02TX it is
`∑_i ξ^i ∩ π^*α_i`, and the pushforwards determine the `α_i` by a triangular system with ones on
the diagonal (Stacks 02TW).

## Main results

* `Stacks.Chow.GenuineChern.dualKernelProjection_eq` — `f(s, j)` for `s ≤ n`.
* `Stacks.Chow.GenuineChern.eq_zero_of_forall_pushforward_capPow` — the uniqueness.
* `Stacks.Chow.GenuineChern.properChowPushforward_section_eq_sum` — the class of a section.

## References

* [Stacks Project, Tag 0FGR](https://stacks.math.columbia.edu/tag/0FGR)
* [Stacks Project, Tag 02TX](https://stacks.math.columbia.edu/tag/02TX)
* [Stacks Project, Tag 02TW](https://stacks.math.columbia.edu/tag/02TW)
* [Stacks Project, Tag 02UI](https://stacks.math.columbia.edu/tag/02UI)
* [Stacks Project, Tag 02SU](https://stacks.math.columbia.edu/tag/02SU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ReflexiveModules (dualSheaf)

universe u

namespace Stacks.Chow.GenuineChern

variable (C : ChowSituation.{u})

/-! ### Uniqueness of a class with given pushforwards -/

section Uniqueness

variable {U P : Scheme.{u}} (sU : U ⟶ C.S) [LocallyOfFiniteType sU]
  (sP : P ⟶ C.S) [LocallyOfFiniteType sP] (π : P ⟶ U) [Flat π]
  [IsProper π] (hsP : π ≫ sU = sP) (n : ℕ) (hπ : AlgebraicGeometry.RelativeDimension π n)
  {M : P.Modules}
  [AlgebraicGeometry.SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property M]

include hπ in
/-- **A class on a projective tower is determined by its pushforwards.** If `x ∈ A_{k+n}(P)`
satisfies `π_*(ξ^{n-m} ∩ x) = 0` for every `m ≤ n`, where `ξ = c₁(ℳ)`, then `x = 0`. By
Stacks 02TX `x = ∑_i ξ^i ∩ π^*α_i`, and `π_*(ξ^{n-m} ∩ ξ^i ∩ π^*α_i)` is `0` for `i < m` and
`α_m` for `i = m` (Stacks 02TW), so the `α_i` vanish by descending induction. -/
theorem eq_zero_of_forall_pushforward_capPow (htower : IsLocallyProjectiveTower n π M) (k : ℤ)
    (x : chowGroup C sP (k + n))
    (hx : ∀ (m : ℕ) (hm : m ≤ n),
      properChowPushforward C sP sU π hsP (k + m)
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sP sU π hsP _)
          (capPow C sP (invCap C sP M) (n - m) (k + n) (k + m) (by omega) x) = 0) :
    x = 0 := by
  obtain ⟨β, rfl⟩ := htower.bundleMap_surjective C (affineBundleSurjectivity C) sU sP hsP hπ k x
  set ξ := invCap C sP M
  -- the operation `π_*(ξ^{n-m} ∩ -)` applied to the `i`-th summand
  have hterm : ∀ (i : Fin (n + 1)) (m : ℕ) (hm : m ≤ n),
      properChowPushforward C sP sU π hsP (k + m)
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sP sU π hsP _)
          (capPow C sP ξ (n - m) (k + n) (k + m) (by omega)
            (bundleTerm C sU sP π hsP n hπ ξ k i (β i))) =
        bundleProjection C sU sP π hsP n hπ ξ ((i : ℕ) + (n - m)) (k + (i : ℕ)) (k + m)
          (by omega) (β i) := by
    intro i m hm
    simp only [bundleTerm, bundleProjection, AddMonoidHom.coe_comp, Function.comp_apply]
    rw [capPow_capPow]
  have hexp : ∀ {s s' : ℕ} (e : s = s') (a b : ℤ) (h : a + n = b + s) (y : chowGroup C sU a),
      bundleProjection C sU sP π hsP n hπ ξ s a b h y =
        bundleProjection C sU sP π hsP n hπ ξ s' a b (e ▸ h) y := by
    intro s s' e a b h y; subst e; rfl
  -- one step of the downward induction
  have step : ∀ i : Fin (n + 1), (∀ i' : Fin (n + 1), (i : ℕ) < i' → β i' = 0) → β i = 0 := by
    intro i hi
    have hle : (i : ℕ) ≤ n := Nat.lt_succ_iff.mp i.isLt
    have h0 := hx i hle
    rw [bundleMap_apply, map_sum, map_sum] at h0
    rw [Finset.sum_congr rfl fun j _ ↦ hterm j i hle] at h0
    rw [Finset.sum_eq_single i (fun j _ hj ↦ ?_) (by simp)] at h0
    · rw [hexp (show (i : ℕ) + (n - i) = n by omega)] at h0
      rw [← htower.bundleProjection_self C sU sP hsP hπ (k + (i : ℕ)) (β i)]
      exact h0
    · rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hj) with hlt | hgt
      · exact bundleProjection_eq_zero_of_lt C sU sP π hsP n hπ ξ _ (by omega) _ _ _ _
      · rw [hi j hgt, map_zero]
  have all : ∀ d : ℕ, ∀ i : Fin (n + 1), n - d ≤ (i : ℕ) → β i = 0 := by
    intro d
    induction d with
    | zero =>
      intro i hi
      exact step i fun i' hi' ↦ absurd i'.isLt (by omega)
    | succ d ih =>
      intro i hi
      by_cases h : n - d ≤ (i : ℕ)
      · exact ih i h
      · exact step i fun i' hi' ↦ ih i' (by omega)
  have hβ : β = 0 := funext fun i ↦ all n i (by omega)
  rw [hβ, map_zero]

/-- `π_*(ξ^s ∩ x) = 0` for `s < n` if `x` is heterogeneously equal to `π^*y`. -/
private theorem pushforward_capPow_eq_zero_of_heq (s : ℕ) (hs : s < n) {a k : ℤ} (m : ℤ)
    (h : a = m + s) (hk : a = k + n) (x : chowGroup C sP a) (y : chowGroup C sU k)
    (hxy : x ≍ bundlePullback C sU sP π hsP n hπ k y) :
    properChowPushforward C sP sU π hsP m
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sP sU π hsP m)
        (capPow C sP (invCap C sP M) s a m h x) = 0 := by
  refine Eq.trans ?_ (bundleProjection_eq_zero_of_lt C sU sP π hsP n hπ (invCap C sP M) s
    hs k m (by omega) y)
  simp only [bundleProjection, AddMonoidHom.coe_comp, Function.comp_apply]
  congr 1
  exact eq_of_heq (capPow_heq C sP _ _ _ rfl (by omega) rfl hxy)

end Uniqueness

/-! ### The pushforwards `π_*(ξ^s ∩ c_j(ℱ^∨) ∩ π^*(-))` -/

section DualKernel

variable {U P : Scheme.{u}} (sU : U ⟶ C.S) [LocallyOfFiniteType sU]
  (sP : P ⟶ C.S) [LocallyOfFiniteType sP] (π : P ⟶ U) [Flat π]
  [IsProper π] (hsP : π ≫ sU = sP) (n : ℕ) (hπ : AlgebraicGeometry.RelativeDimension π n)
  (𝒞 : U.Modules)
  [h𝒞 : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒞 (n + 1)]
  (S : ShortComplex P.Modules) (hS : S.ShortExact)
  [hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₁ n]
  [hM : AlgebraicGeometry.SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property S.X₃]
  (e₂ : S.X₂ ≅ (Scheme.Modules.pullback π).obj 𝒞)
  (htower : IsLocallyProjectiveTower n π S.X₃)

/-- **The operation `f(s, j) = π_*(ξ^s ∩ c_j(ℱ^∨) ∩ π^*(-)) : A_k(U) ⟶ A_m(U)`**, for
`k + n - j = m + s`, where `ξ = c₁(ℳ)` and `ℱ` is the kernel of `π^*𝒞 ⟶ ℳ`. -/
def dualKernelProjection (s j : ℕ) (k m : ℤ) (h : k + n - j = m + s) :
    chowGroup C sU k →+ chowGroup C sU m :=
  haveI := Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFreeOfRank_dualSheaf S.X₁ n hF
  (properChowPushforward C sP sU π hsP m
      (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sP sU π hsP m)).comp
    ((capPow C sP (invCap C sP S.X₃) s (k + n - j) m h).comp
      ((chernFamily C sP (dualSheaf S.X₁) n (k + n) j).comp
        (bundlePullback C sU sP π hsP n hπ k)))

include hS e₂ in
/-- **The shift `f(s, j + 1) = f(s + 1, j)` for `s < n`**: the Whitney recursion
`c_{j+1}(ℱ^∨) = c_{j+1}(π^*𝒞^∨) + ξ ∩ c_j(ℱ^∨)` (Stacks 02UI), the first summand pushing forward
to zero by the vanishing half of Stacks 02TW. -/
theorem dualKernelProjection_succ (s j : ℕ) (hs : s < n) (k m : ℤ)
    (h : k + n - ((j + 1 : ℕ) : ℤ) = m + s) (h' : k + n - j = m + ((s + 1 : ℕ) : ℤ))
    (β : chowGroup C sU k) :
    dualKernelProjection C sU sP π hsP n hπ S s (j + 1) k m h β =
      dualKernelProjection C sU sP π hsP n hπ S (s + 1) j k m h' β := by
  have hFd := Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFreeOfRank_dualSheaf
    S.X₁ n hF
  have hG : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₂ (n + 1) :=
    rank_of_iso e₂.symm rfl (isFiniteLocallyFreeOfRank_pullback π 𝒞 (n + 1))
  have hGd := Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFreeOfRank_dualSheaf
    S.X₂ (n + 1) hG
  have h𝒞d := Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFreeOfRank_dualSheaf
    𝒞 (n + 1) h𝒞
  simp only [dualKernelProjection, AddMonoidHom.coe_comp, Function.comp_apply]
  rw [chernFamily_dualKernel_succ C sP S hS n, map_add, map_add]
  -- the new summand vanishes, by the vanishing half of Stacks 02TW
  have hint := intertwines_chernFamily C sU (dualSheaf 𝒞) (n + 1) sP π hsP n hπ
    (dualSheaf S.X₂) (dualMiddleIso π n 𝒞 S e₂) k (j + 1) β
  have hb : properChowPushforward C sP sU π hsP m
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sP sU π hsP m)
        (capPow C sP (invCap C sP S.X₃) s (k + n - ((j + 1 : ℕ) : ℤ)) m h
          (chernFamily C sP (dualSheaf S.X₂) (n + 1) (k + n) (j + 1)
            (bundlePullback C sU sP π hsP n hπ k β))) = 0 := by
    refine pushforward_capPow_eq_zero_of_heq C sU sP π hsP n hπ s hs m h (by push_cast; omega) _
      (chernFamily C sU (dualSheaf 𝒞) (n + 1) k (j + 1) β) ?_
    exact (gradedDegreeCast_heq _ _).symm.trans (heq_of_eq hint).symm
  rw [hb, zero_add]
  congr 1
  rw [capPow_succ_apply]
  refine eq_of_heq (capPow_heq C sP _ _ _ rfl (by push_cast; ring) rfl ?_)
  refine heq_apply_of_degree C sP sP (fun d => d + 1) (fun d => d)
    (fun d => (invCap C sP S.X₃).capOnChow C sP d) (by push_cast; ring) ?_
  exact (chowGroupCast_heq C sP _ _).trans (chowGroupCast_heq C sP _ _).symm

include hS e₂ in
/-- **`f(s, j) = 0` for `s + j < n`**: by the shift, `f(s, j) = f(s + j, 0)`, which vanishes by
Stacks 02TW. -/
theorem dualKernelProjection_eq_zero_of_lt (j : ℕ) :
    ∀ (s : ℕ) (_ : s + j < n) (k m : ℤ) (h : k + n - j = m + s) (β : chowGroup C sU k),
      dualKernelProjection C sU sP π hsP n hπ S s j k m h β = 0 := by
  induction j with
  | zero =>
    intro s hs k m h β
    simp only [dualKernelProjection, AddMonoidHom.coe_comp, Function.comp_apply]
    rw [chernFamily_apply_zero, gradedCap_one_apply_zero]
    exact pushforward_capPow_eq_zero_of_heq C sU sP π hsP n hπ s (by omega) m _
      (by push_cast at h; omega) _ β (gradedDegreeCast_heq _ _)
  | succ j ih =>
    intro s hs k m h β
    rw [dualKernelProjection_succ C sU sP π hsP n hπ 𝒞 S hS e₂ s j (by omega) k m h
      (by push_cast at h ⊢; omega)]
    exact ih (s + 1) (by omega) k m _ β

include hS e₂ in
/-- **`f(s, j) = 0` for `s ≤ n < s + j`**: by the shift, `f(s, j) = f(0, s + j)`, and
`c_{s+j}(ℱ^∨) = 0` above the rank `n` of `ℱ^∨`. -/
theorem dualKernelProjection_eq_zero_of_gt (s : ℕ) :
    ∀ (j : ℕ) (_ : s ≤ n) (_ : n < s + j) (k m : ℤ) (h : k + n - j = m + s)
      (β : chowGroup C sU k), dualKernelProjection C sU sP π hsP n hπ S s j k m h β = 0 := by
  induction s with
  | zero =>
    intro j _ hj k m h β
    have := Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFreeOfRank_dualSheaf
      S.X₁ n hF
    simp only [dualKernelProjection, AddMonoidHom.coe_comp, Function.comp_apply]
    simp only [chernCapFamilyOnChow_of_gt C (chernCap C) sP (dualSheaf S.X₁) n (k + n)
      (i := j) (by omega), AddMonoidHom.zero_apply, map_zero]
  | succ s ih =>
    intro j hs hj k m h β
    rw [← dualKernelProjection_succ C sU sP π hsP n hπ 𝒞 S hS e₂ s j (by omega) k m
      (by push_cast at h ⊢; omega) h]
    exact ih (j + 1) (by omega) (by omega) k m _ β

include hS e₂ htower in
/-- **`f(s, j)` is the identity for `s + j = n`**: this is
`Stacks.Chow.GenuineChern.pushforward_capPow_chernFamily_dualKernel`, read with the target
degree transported. -/
theorem dualKernelProjection_eq_of_eq (s j : ℕ) (hsj : s + j = n) (k m : ℤ)
    (h : k + n - j = m + s) (β : chowGroup C sU k) :
    dualKernelProjection C sU sP π hsP n hπ S s j k m h β =
      chowGroupCast C sU (by omega) β := by
  obtain rfl : m = k := by omega
  exact pushforward_capPow_chernFamily_dualKernel C sU sP π hsP n hπ 𝒞 S hS e₂ htower m β j s hsj

include hS e₂ htower in
/-- **`f(s, j)` for `s ≤ n`**: the identity if `s + j = n`, and zero otherwise. -/
theorem dualKernelProjection_eq (s j : ℕ) (hs : s ≤ n) (k m : ℤ)
    (h : k + n - j = m + s) (β : chowGroup C sU k) :
    dualKernelProjection C sU sP π hsP n hπ S s j k m h β =
      if hsj : s + j = n then chowGroupCast C sU (by omega) β else 0 := by
  split_ifs with hsj
  · exact dualKernelProjection_eq_of_eq C sU sP π hsP n hπ 𝒞 S hS e₂ htower s j hsj k m h β
  · rcases lt_or_gt_of_ne hsj with hlt | hgt
    · exact dualKernelProjection_eq_zero_of_lt C sU sP π hsP n hπ 𝒞 S hS e₂ j s hlt k m h β
    · exact dualKernelProjection_eq_zero_of_gt C sU sP π hsP n hπ 𝒞 S hS e₂ s j hs hgt k m h β

/-! ### The class of a section -/

include hS e₂ htower in
/-- **The class of a section of a projective tower.** Let `π : P ⟶ U` be a flat proper
projective tower of fibre dimension `n` with twist `ℳ`, `0 ⟶ ℱ ⟶ π^*𝒞 ⟶ ℳ ⟶ 0` short exact with
`𝒞` of rank `n + 1`, `σ : U ⟶ P` a proper section of `π` and `ℒ ≅ σ^*ℳ`. Then for every
`β ∈ A_{k+n}(U)`

  `σ_*β = ∑_{i = 0}^{n} c_{n-i}(ℱ^∨) ∩ π^*(c₁(ℒ)^i ∩ β)`  in  `A_{k+n}(P)`. -/
theorem properChowPushforward_section_eq_sum (σ : U ⟶ P) [IsProper σ] (hσ : σ ≫ π = 𝟙 U)
    (hσs : σ ≫ sP = sU) (L : U.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible U.sheaf.obj U.ringCatSheaf.property L]
    (eL : L ≅ (Scheme.Modules.pullback σ).obj S.X₃) (k : ℤ) (β : chowGroup C sU (k + n)) :
    haveI := Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFreeOfRank_dualSheaf
      S.X₁ n hF
    properChowPushforward C sU sP σ hσs (k + n)
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sU sP σ hσs _) β =
      ∑ i : Fin (n + 1), chowGroupCast C sP (by have := i.isLt; omega)
        (chernFamily C sP (dualSheaf S.X₁) n (k + n - (i : ℕ) + n) (n - i)
          (bundlePullback C sU sP π hsP n hπ (k + n - (i : ℕ))
            (capPow C sU (invCap C sU L) i (k + n) (k + n - (i : ℕ)) (by ring) β))) := by
  have hFd := Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFreeOfRank_dualSheaf
    S.X₁ n hF
  have := isInvertible_pullback σ S.X₃
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_pushforward_capPow C sU sP π hsP n hπ htower k _ fun m hm ↦ ?_
  rw [map_sub, map_sub, sub_eq_zero]
  -- the left hand side: `π_*(ξ^{n-m} ∩ σ_*β) = c₁(ℒ)^{n-m} ∩ β`
  have hpush : ∀ (d : ℤ) (y : chowGroup C sU d),
      properChowPushforward C sP sU π hsP d
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sP sU π hsP d)
          (properChowPushforward C sU sP σ hσs d
            (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sU sP σ hσs d) y) =
        y := by
    intro d y
    have hcomp := DFunLike.congr_fun (properChowPushforward_comp C sU sP sU σ π hσs hsP d
      (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sU sP σ hσs d)
      (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sP sU π hsP d)) y
    rw [AddMonoidHom.comp_apply] at hcomp
    rw [hcomp, properChowPushforward_congr C sU sU (σ ≫ π) (𝟙 U) hσ _ (Category.id_comp sU) d _
      (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sU sU _ _ d),
      properChowPushforward_id]
    rfl
  rw [← properChowPushforward_capPow C sU sP σ hσs S.X₃, hpush,
    ← capPow_invCap_congr C sU eL]
  -- the right hand side
  rw [map_sum, map_sum]
  have hterm : ∀ i : Fin (n + 1),
      properChowPushforward C sP sU π hsP (k + m)
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sP sU π hsP _)
          (capPow C sP (invCap C sP S.X₃) (n - m) (k + n) (k + m) (by omega)
            (chowGroupCast C sP (by have := i.isLt; omega)
              (chernFamily C sP (dualSheaf S.X₁) n (k + n - (i : ℕ) + n) (n - i)
                (bundlePullback C sU sP π hsP n hπ (k + n - (i : ℕ))
                  (capPow C sU (invCap C sU L) i (k + n) (k + n - (i : ℕ)) (by ring) β))))) =
        dualKernelProjection C sU sP π hsP n hπ S (n - m) (n - i) (k + n - (i : ℕ)) (k + m)
          (by have := i.isLt; omega)
          (capPow C sU (invCap C sU L) i (k + n) (k + n - (i : ℕ)) (by ring) β) := by
    intro i
    rw [capPow_cast]
    rfl
  rw [Finset.sum_congr rfl fun i _ ↦ hterm i]
  rw [Finset.sum_congr rfl fun (i : Fin (n + 1)) _ ↦
    dualKernelProjection_eq C sU sP π hsP n hπ 𝒞 S hS e₂ htower (n - m) (n - (i : ℕ)) (by omega)
      _ _ _ _]
  rw [Finset.sum_eq_single ⟨n - m, by omega⟩ (fun i _ hi ↦ dite_eq_right fun h ↦ hi (Fin.ext (by
    simp only; omega))) (by simp), dite_eq_left (by simp only; omega)]
  refine eq_of_heq (HEq.trans ?_ (chowGroupCast_heq C sU _ _).symm)
  exact capPow_heq C sU _ _ _ rfl rfl (by simp only; omega) HEq.rfl

end DualKernel

end Stacks.Chow.GenuineChern

end
