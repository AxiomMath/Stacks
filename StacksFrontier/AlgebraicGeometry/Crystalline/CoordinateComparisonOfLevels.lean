module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedComparisonOfLevels
public import StacksFrontier.AlgebraicGeometry.Crystalline.CoordinateOperatorsInfinite
public import StacksFrontier.AlgebraicGeometry.Crystalline.FirstOrderComparisonOfCoordinates

/-!
# The coordinate expansion of the connection assembled from coordinate data at the levels

Let `M = lim_e M_e` be a tower of shifted quotients over a divided power ring `D`, as in
`Crystalline.CompletedFirstOrderComparison.ofLevels`, and suppose each level carries the
first-order comparison datum `x ↦ 1 ⊗ x - ∑_c d x_c ⊗ θ_c(x)` of
`Crystalline.coordinateComparison`, the operators `θ_c` being the reductions of operators on `M`.
Then the connection of the completed comparison datum assembled from the levels is

`∇ m = ∑_c (-θ_c(m)) ⊗ d x_c`,

the sum converging `p`-adically: the coordinate operators of the connection are the `-θ_c`. This
is the expansion `∇(m) = ∑ θ_i(m) d x_i` of the proof of [Stacks, Lemma 60.17.3, Tag 07JG], read
off the Taylor expansion, the sign coming from `ξ_c = x_c ⊗ 1 - 1 ⊗ x_c ↦ -d x_c`.

## Main results

* `Crystalline.eval_eq_of_completedLevelProj_eq` — two elements of the completed base change with
  the same readout at the level `n` agree at the step `n` of the `p`-adic filtration.
* `Crystalline.isCoordinateExpansion_ofLevels` — the coordinate operators of the assembled
  connection are the `-θ_c`.

## References

* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
-/

@[expose] public section

open scoped TensorProduct

universe u w uI

noncomputable section

namespace Crystalline

section Expansion

variable {A : Type u} [CommRing A] {D : DividedPowerRing.{u}} {g : A →+* D} {Omega : Type u}
  [AddCommGroup Omega] [Module D Omega] [Module Dᵐᵒᵖ Omega] [IsCentralScalar D Omega]
  {d : DividedPowerDerivation A D g Omega} {p : ℕ}
  (M₀ : Type w) [AddCommGroup M₀] [Module (D : Type u) M₀]
  (lev : ℕ → Type w) [∀ n, AddCommGroup (lev n)] [∀ n, Module (D : Type u) (lev n)]
  (trans : ∀ n, lev (n + 1) →ₗ[(D : Type u)] lev n) (N : ℕ)
  (r : ∀ n, M₀ →ₗ[(D : Type u)] lev n)
  (hsurj : ∀ n, Function.Surjective (r n))
  (hker : ∀ n, LinearMap.ker (r n) =
    DividedPowers.pAdicIdeal (A := (D : Type u)) p ^ (N + n) •
      (⊤ : Submodule (D : Type u) M₀))
  (hcomp : ∀ n, trans n ∘ₗ r (n + 1) = r n)

include hsurj hker in
/-- **Two elements of the completed base change with the same readout at the level `n` agree at
the step `n` of the `p`-adic filtration.** -/
theorem eval_eq_of_completedLevelProj_eq {z z' : CompletedFirstOrderTensor D Omega p M₀} (n : ℕ)
    (h : completedLevelProj M₀ lev N r hsurj hker n z =
      completedLevelProj M₀ lev N r hsurj hker n z') :
    AdicCompletion.eval _ _ n z = AdicCompletion.eval _ _ n z' := by
  have hm : z.val (N + n) = z'.val (N + n) :=
    (shiftedLevelQuot_bijective (DividedPowers.pAdicIdeal (A := (D : Type u)) p)
      (firstOrderExtension D Omega ⊗[D] M₀) (fun n ↦ firstOrderExtension D Omega ⊗[D] lev n) N
      (tensorLevelProj (firstOrderExtension D Omega) M₀ lev r)
      (ker_tensorLevelProj (firstOrderExtension D Omega) M₀ lev N r hsurj hker)
      (tensorLevelProj_surjective (firstOrderExtension D Omega) M₀ lev r hsurj) n).1 h
  rw [AdicCompletion.eval_apply, AdicCompletion.eval_apply,
    ← AdicCompletion.transitionMap_comp_eval_apply _ _ (Nat.le_add_left n N) z,
    ← AdicCompletion.transitionMap_comp_eval_apply _ _ (Nat.le_add_left n N) z']
  exact congrArg _ hm

variable {ι : Type uI} (dx : ι → Omega) (θlev : ∀ n, lev n →+ (ι →₀ lev n))
  (hleib : ∀ n (a : (D : Type u)) (x : lev n), ∃ δ : ι →₀ (D : Type u),
    (∀ c, θlev n (a • x) c = a • θlev n x c + δ c • x) ∧
    (TrivSqZeroExt.inr (d a) : firstOrderExtension D Omega) ⊗ₜ[D] x =
      -δ.sum fun c b ↦ (TrivSqZeroExt.inr (dx c) : firstOrderExtension D Omega) ⊗ₜ (b • x))
  (hnat : ∀ n (x : lev (n + 1)),
    θlev n (trans n x) = (θlev (n + 1) x).mapRange (trans n) (map_zero _))
  (θ : ι → M₀ → M₀) (hθ : ∀ n c m, r n (θ c m) = θlev n (r n m) c)

include hsurj hker hcomp hθ in
/-- **The coordinate operators of the assembled connection are the `-θ_c`.** -/
theorem isCoordinateExpansion_ofLevels :
    IsCoordinateExpansion p (D : Type u) Omega dx
      (CompletedFirstOrderComparison.ofLevels M₀ lev trans N r hsurj hker hcomp
        (fun n ↦ coordinateComparison D Omega d dx (θlev n) (hleib n))
        (fun n x ↦ lTensor_coordinateComparisonFun D Omega dx (θlev (n + 1)) (θlev n) (trans n)
          (hnat n) x)).completedConnection
      (fun c m ↦ -θ c m) := by
  classical
  intro m
  refine hasSum_adicCompletion_of_eval_eventually_eq _
    (Submodule.fg_span_singleton _) _ _ fun n ↦ ⟨(θlev n (r n m)).support, fun s hs ↦ ?_⟩
  let w : firstOrderExtension D Omega ⊗[D] M₀ := (1 : firstOrderExtension D Omega) ⊗ₜ m -
    ∑ c ∈ s, (TrivSqZeroExt.inr (dx c) : firstOrderExtension D Omega) ⊗ₜ θ c m
  have hw : ∑ c ∈ s, toCompletedTensor p (D : Type u) Omega M₀ ((-θ c m) ⊗ₜ[D] dx c) =
      AdicCompletion.map (DividedPowers.pAdicIdeal (A := (D : Type u)) p)
        (firstOrderDifferentialComm D Omega M₀)
        (AdicCompletion.of (DividedPowers.pAdicIdeal (A := (D : Type u)) p) _ w) := by
    rw [AdicCompletion.map_of, ← map_sum]
    congr 1
    simp only [w, map_sub, map_sum, firstOrderDifferentialComm_tmul, TrivSqZeroExt.snd_one,
      TrivSqZeroExt.snd_inr, TensorProduct.tmul_zero, zero_sub, TensorProduct.neg_tmul,
      Finset.sum_neg_distrib]
  refine (congrArg (AdicCompletion.eval _ _ n) hw).trans ?_
  have hlev : completedLevelProj M₀ lev N r hsurj hker n
      (AdicCompletion.of (DividedPowers.pAdicIdeal (A := (D : Type u)) p) _ w) =
      completedLevelProj M₀ lev N r hsurj hker n
        (completedLevelComparisonFun M₀ lev trans N r hsurj hker hcomp
          (fun n ↦ coordinateComparison D Omega d dx (θlev n) (hleib n))
          (fun n x ↦ lTensor_coordinateComparisonFun D Omega dx (θlev (n + 1)) (θlev n)
            (trans n) (hnat n) x) m) := by
    refine Eq.trans ?_ (completedLevelProj_completedLevelComparisonFun M₀ lev trans N r hsurj hker
      hcomp _ _ m n).symm
    rw [completedLevelProj_of, coordinateComparison_apply,
      coordinateComparisonFun_eq D Omega dx _ _ s hs]
    simp only [w, tensorLevelProj, map_sub, map_sum, LinearMap.lTensor_tmul, hθ]
  have he := eval_eq_of_completedLevelProj_eq M₀ lev N r hsurj hker n hlev
  rw [AdicCompletion.eval_apply, AdicCompletion.eval_apply] at he
  show AdicCompletion.eval _ _ n
      (AdicCompletion.map _ (firstOrderDifferentialComm D Omega M₀) _) =
    AdicCompletion.eval _ _ n (AdicCompletion.map _ (firstOrderDifferentialComm D Omega M₀)
      (completedLevelComparisonFun M₀ lev trans N r hsurj hker hcomp
          (fun n ↦ coordinateComparison D Omega d dx (θlev n) (hleib n))
          (fun n x ↦ lTensor_coordinateComparisonFun D Omega dx (θlev (n + 1)) (θlev n)
            (trans n) (hnat n) x) m))
  rw [AdicCompletion.eval_apply, AdicCompletion.eval_apply, AdicCompletion.map_val_apply,
    AdicCompletion.map_val_apply, he]

end Expansion

end Crystalline

end
