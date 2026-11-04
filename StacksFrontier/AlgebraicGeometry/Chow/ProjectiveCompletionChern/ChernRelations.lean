module

public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveCompletionChern.ChernClasses
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassArbitraryRank.TotalChernClass
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.SplittingPrinciplePerfect
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.ChernCommutation
public import StacksFrontier.AlgebraicGeometry.Chow.ChernWhitney.InvertibleSubsheaf
public import StacksFrontier.AlgebraicGeometry.Modules.PullbackShortExactFlatScheme

/-!
# Relations between the Chern classes on the projective completion

Let `E = Proj_X(Sym^*(𝒞)[T])` with `𝒞` of rank `r`, `h = c₁(𝒪_E(1))` and
`𝒦 = Ker(π^*(𝒞 ⊕ 𝒪_X) ⟶ 𝒪_E(1))`. The Whitney formula for the tautological sequence gives
`c(π^*(𝒞 ⊕ 𝒪_X)) = c(𝒦)(1 + h)`, and `c(π^*(𝒞 ⊕ 𝒪_X)) = c(π^*𝒞)` vanishes above degree `r`.
Hence

* `c_r(𝒦) h = 0`, and
* `c_r(𝒦) = ∑_{j = 0}^{r} (-1)^j h^j c_{r-j}(π^*(𝒞 ⊕ 𝒪_X))`.

## Main results

* `Stacks.Chow.ProjectiveCompletion.homComponent_rank_mul_firstChernTotal`: `c_r(𝒦) h = 0`.
* `Stacks.Chow.ProjectiveCompletion.homComponent_rank_eq_sum`: the expansion of `c_r(𝒦)`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Finset

universe u

namespace Stacks.Chow

namespace TotalChowClass

variable {C : ChowSituation.{u}} {Y : Scheme.{u}} {sY : Y ⟶ C.S} [LocallyOfFiniteType sY]

/-- Multiplying by a class of degree one on the left shifts the homogeneous components. -/
theorem homComponent_succ_mul_of_isHomogeneous_one {h : TotalChowClass C sY}
    (hh : h.IsHomogeneous 1) (w : TotalChowClass C sY) (n : ℕ) :
    homComponent (n + 1) (h * w) = h * homComponent n w := by
  rw [homComponent_mul, Finset.sum_eq_single n]
  · rw [show n + 1 - n = 1 by omega, hh.homComponent_eq_ite, if_pos rfl]
  · intro j hj hjn
    rw [hh.homComponent_eq_ite, if_neg (by have := mem_range.1 hj; omega), zero_mul]
  · intro hn
    exact absurd (mem_range.2 (by omega)) hn

/-- Multiplying by a class of degree one on the right shifts the homogeneous components. -/
theorem homComponent_succ_mul_of_isHomogeneous_one_right {h : TotalChowClass C sY}
    (hh : h.IsHomogeneous 1) (w : TotalChowClass C sY) (n : ℕ) :
    homComponent (n + 1) (w * h) = homComponent n w * h := by
  rw [homComponent_mul, Finset.sum_eq_single 1]
  · rw [show n + 1 - 1 = n by omega, hh.homComponent_eq_ite, if_pos rfl]
  · intro j _ hj1
    rw [hh.homComponent_eq_ite, if_neg hj1, mul_zero]
  · intro hn
    exact absurd (mem_range.2 (by omega)) hn

/-- A product with a class of degree one on the left has no component of degree zero. -/
theorem homComponent_zero_mul_of_isHomogeneous_one {h : TotalChowClass C sY}
    (hh : h.IsHomogeneous 1) (w : TotalChowClass C sY) : homComponent 0 (h * w) = 0 := by
  rw [homComponent_mul, Finset.sum_range_one, hh.homComponent_eq_ite, if_neg (by omega), zero_mul]

/-- **Dividing by `1 + h`.** If `h` has degree one and `v = (1 + h) u`, then
`u_n = ∑_{j ≤ n} (-1)^j h^j v_{n-j}`. -/
theorem homComponent_eq_sum_of_eq_one_add_mul {h u v : TotalChowClass C sY}
    (hh : h.IsHomogeneous 1) (hv : v = (1 + h) * u) (n : ℕ) :
    homComponent n u =
      ∑ j ∈ range (n + 1), ((-1 : ℤ) ^ j) • (h ^ j * homComponent (n - j) v) := by
  have hstep : ∀ m, homComponent m v = homComponent m u + homComponent m (h * u) := by
    intro m
    rw [hv, add_mul, one_mul, map_add]
  induction n with
  | zero =>
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, one_mul,
        one_smul, Nat.sub_zero]
      rw [hstep 0, homComponent_zero_mul_of_isHomogeneous_one hh, add_zero]
  | succ n ih =>
      rw [Finset.sum_range_succ']
      simp only [pow_zero, one_smul, one_mul, Nat.sub_zero]
      rw [hstep (n + 1), homComponent_succ_mul_of_isHomogeneous_one hh, ih, Finset.mul_sum,
        add_left_comm, ← Finset.sum_add_distrib, Finset.sum_eq_zero, add_zero]
      intro j _
      have hj' : n + 1 - (j + 1) = n - j := by omega
      rw [hj', mul_smul_comm, ← mul_assoc, ← pow_succ', pow_succ (-1 : ℤ), mul_neg_one,
        neg_smul, neg_add_cancel]

end TotalChowClass

namespace ProjectiveCompletion

variable {X : Scheme.{u}} (𝒞 : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} 𝒞] (r : ℕ)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒞 r]

attribute [local instance] isFiniteLocallyFreeOfRank_kernelModule

/-- `π^*(𝒞 ⊕ 𝒪_X)` is finite locally free of rank `r + 1`. -/
theorem isFiniteLocallyFreeOfRank_pullbackModule :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (proj 𝒞)).obj (module 𝒞)) (r + 1) :=
  have := isFiniteLocallyFreeOfRank_module 𝒞 r
  AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (proj 𝒞) (module 𝒞) (r + 1)

attribute [local instance] isFiniteLocallyFreeOfRank_pullbackModule

variable (C : ChowSituation.{u}) (sE : space 𝒞 ⟶ C.S) [LocallyOfFiniteType sE]

/-- **The Whitney formula for the tautological sequence**: `c(π^*(𝒞 ⊕ 𝒪_X)) = c(𝒦)(1 + h)`. -/
theorem totalChern_pullbackModule :
    totalChern C sE ((Scheme.Modules.pullback (proj 𝒞)).obj (module 𝒞)) (r + 1) =
      totalChern C sE (kernelModule 𝒞) r * (1 + TotalChowClass.firstChernTotal C sE (twist 𝒞)) := by
  have h1 := isFiniteLocallyFreeOfRank_one_of_isInvertible (twist 𝒞)
  have h := @totalChern_eq_mul_of_shortExact C _ sE _ _ (shortExact_taut 𝒞) r 1
    (isFiniteLocallyFreeOfRank_kernelModule 𝒞 r) h1
  rw [← totalChern_eq_one_add_firstChernTotal C sE (twist 𝒞)]
  exact h

/-- **The component of degree `r + 1` of `c(π^*(𝒞 ⊕ 𝒪_X))` vanishes.** -/
theorem homComponent_totalChern_pullbackModule :
    TotalChowClass.homComponent (r + 1)
      (totalChern C sE ((Scheme.Modules.pullback (proj 𝒞)).obj (module 𝒞)) (r + 1)) = 0 := by
  set S := (ShortComplex.mk (C := X.Modules) (inl 𝒞) (snd 𝒞) (inl_snd 𝒞)).map
    (Scheme.Modules.pullback (proj 𝒞)) with hS
  have := isFiniteLocallyFreeOfRank_unit (X := X)
  have hSE : S.ShortExact := Scheme.Modules.shortExact_map_pullback_of_finiteLocallyFree (proj 𝒞)
    _ (shortExact_inl_snd 𝒞)
    (GenuineChern.isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank
      (SheafOfModules.unit X.ringCatSheaf) 1)
  have h₁ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (proj 𝒞)).obj 𝒞) r :=
    AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (proj 𝒞) 𝒞 r
  have h₃ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (proj 𝒞)).obj (SheafOfModules.unit X.ringCatSheaf)) 1 :=
    AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (proj 𝒞) _ 1
  have hW := @totalChern_eq_mul_of_shortExact C _ sE _ S hSE r 1 h₁ h₃
  have h1 : totalChern C sE ((Scheme.Modules.pullback (proj 𝒞)).obj
      (SheafOfModules.unit X.ringCatSheaf)) 1 = 1 :=
    totalChern_eq_one_of_iso_unit C sE _ (Scheme.Modules.pullbackUnitIso (proj 𝒞))
  have key : totalChern C sE ((Scheme.Modules.pullback (proj 𝒞)).obj (module 𝒞)) (r + 1) =
      totalChern C sE ((Scheme.Modules.pullback (proj 𝒞)).obj 𝒞) r := by
    refine hW.trans ?_
    exact (congrArg (fun c => totalChern C sE ((Scheme.Modules.pullback (proj 𝒞)).obj 𝒞) r * c)
      h1).trans (mul_one _)
  rw [key]
  refine TotalChowClass.ext fun p ↦ ?_
  rw [TotalChowClass.homComponent_apply]
  split_ifs with hp
  · subst hp
    exact totalChern_apply_of_lt C sE _ r (by omega)
  · rfl

/-- **`c_r(𝒦) h = 0`**. -/
theorem homComponent_rank_mul_firstChernTotal :
    TotalChowClass.homComponent r (totalChern C sE (kernelModule 𝒞) r) *
      TotalChowClass.firstChernTotal C sE (twist 𝒞) = 0 := by
  have h := homComponent_totalChern_pullbackModule 𝒞 r C sE
  rw [totalChern_pullbackModule, mul_add, mul_one, map_add,
    TotalChowClass.homComponent_succ_mul_of_isHomogeneous_one_right
      (TotalChowClass.isHomogeneous_firstChernTotal C sE (twist 𝒞))] at h
  have h0 : TotalChowClass.homComponent (r + 1) (totalChern C sE (kernelModule 𝒞) r) = 0 := by
    refine TotalChowClass.ext fun p ↦ ?_
    rw [TotalChowClass.homComponent_apply]
    split_ifs with hp
    · subst hp
      exact totalChern_apply_of_lt C sE (kernelModule 𝒞) r (by omega)
    · rfl
  rw [h0, zero_add] at h
  exact h

/-- **The expansion of `c_r(𝒦)`**: `c_r(𝒦) = ∑_{j ≤ r} (-1)^j h^j c_{r-j}(π^*(𝒞 ⊕ 𝒪_X))`. -/
theorem homComponent_rank_eq_sum :
    TotalChowClass.homComponent r (totalChern C sE (kernelModule 𝒞) r) =
      ∑ j ∈ range (r + 1), ((-1 : ℤ) ^ j) •
        (TotalChowClass.firstChernTotal C sE (twist 𝒞) ^ j *
          TotalChowClass.homComponent (r - j)
            (totalChern C sE ((Scheme.Modules.pullback (proj 𝒞)).obj (module 𝒞)) (r + 1))) := by
  refine TotalChowClass.homComponent_eq_sum_of_eq_one_add_mul
    (TotalChowClass.isHomogeneous_firstChernTotal C sE (twist 𝒞)) ?_ r
  rw [totalChern_pullbackModule, add_mul, one_mul, mul_add, mul_one,
    (TotalChowClass.commute_firstChernTotal_totalChern C sE (twist 𝒞) (kernelModule 𝒞) r).eq]

end ProjectiveCompletion

end Stacks.Chow

end
