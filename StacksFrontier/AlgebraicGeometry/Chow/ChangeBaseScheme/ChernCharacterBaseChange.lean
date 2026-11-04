module

public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.PowerSumBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.RationalIntersection.SecondAdamsTotalChern

/-!
# Base change of `CH_*(X) ⊗ 𝐐` commutes with the Chern character

Let `B` be a flat base change of Chow situations `g : S' ⟶ S` with dimension shift `c`
([Stacks, Tag 0FVG]), and `X` locally of finite type over `S` with base change
`X' = X ×_S S'`. Base change of Chow groups ([Stacks, Tag 0FVJ]) gives a `𝐐`-linear map

  `g^* : CH_*(X) ⊗ 𝐐 ⟶ CH_*(X') ⊗ 𝐐`,

`CH_k(X) ⊗ 𝐐 ⟶ CH_{k+c}(X') ⊗ 𝐐` (`Stacks.Chow.rationalBaseChangeChowPullback`). Since base
change commutes with Chern classes ([Stacks, Tag 0FVN]), it commutes with the Chern character:

  `g^*(ch(α) ∩ β) = ch(α') ∩ g^*β`

for `α ∈ K_0(Vect(X)) ⊗ 𝐐` with pullback `α'` to `X'`.

## Main results

* `Stacks.Chow.TotalChowClass.baseChangeCompatible_powerSumKHom` — the power sums `P_p(α)`,
  `α ∈ K_0(Vect(X))`, commute with base change.
* `Stacks.Chow.rationalBaseChangeChowPullback_chernCharacterCap`,
  `Stacks.Chow.rationalBaseChangeChowPullback_rationalChernCharacterCap` — base change commutes
  with the Chern character.

## References

* [Stacks Project, Tag 0FVJ](https://stacks.math.columbia.edu/tag/0FVJ)
* [Stacks Project, Tag 0FVN](https://stacks.math.columbia.edu/tag/0FVN)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace Stacks.Chow

variable (B : FlatBaseChangeSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ B.base.S)
  [LocallyOfFiniteType sX]

namespace TotalChowClass

/-- **The power sums of classes of `K_0(Vect(X))` commute with base change**: `P_p(α)` on `X`
and `P_p(α')` on `X'` are compatible with base change, `α'` the pullback of `α` to `X'`. -/
theorem baseChangeCompatible_powerSumKHom (p : ℕ) (a : VectorBundleKZero X) :
    BaseChangeCompatible (powerSumKHom B.base sX p a)
      (powerSumKHom B.baseChange (pullback.snd sX B.g) p
        (VectorBundleKZero.pullback (pullback.fst sX B.g) a)) := by
  induction a using induction_on_classOf with
  | hclass M hM =>
    have := hM
    have := isFiniteLocallyFree_pullbackObj M (pullback.fst sX B.g)
    rw [VectorBundleKZero.pullback_classOf, powerSumKHom_classOf, powerSumKHom_classOf]
    exact baseChangeCompatible_powerSumOfFiniteLocallyFree B sX M _ (Iso.refl _) p
  | hzero => simpa using BaseChangeCompatible.zero
  | hadd a b ha hb => simpa using ha.add hb
  | hneg a ha => simpa using ha.neg

end TotalChowClass

local notation "CHQ(" C ", " s ")" =>
  DirectSum ℤ fun j : ℤ => ℚ ⊗[ℤ] chowGroup C s j

/-- **Base change on `CH_*(X) ⊗ 𝐐`**: the `𝐐`-linear map
`CH_*(X) ⊗ 𝐐 ⟶ CH_*(X') ⊗ 𝐐` induced in each degree by the base-change map
`CH_k(X) ⟶ CH_{k+c}(X')` of [Stacks, Tag 0FVJ]. -/
def rationalBaseChangeChowPullback :
    CHQ(B.base, sX) →ₗ[ℚ] CHQ(B.baseChange, pullback.snd sX B.g) :=
  DirectSum.toModule ℚ ℤ _ fun n =>
    DirectSum.lof ℚ ℤ (fun j : ℤ => ℚ ⊗[ℤ] chowGroup B.baseChange (pullback.snd sX B.g) j)
        (n + B.c) ∘ₗ
      (baseChangeChowPullback B sX n).toIntLinearMap.baseChange ℚ

/-- On the degree-`n` summand, `rationalBaseChangeChowPullback` is the base change to `𝐐` of
`baseChangeChowPullback` in degree `n`, landing in degree `n + c`. -/
theorem rationalBaseChangeChowPullback_lof (n : ℤ) (t : ℚ ⊗[ℤ] chowGroup B.base sX n) :
    rationalBaseChangeChowPullback B sX
        (DirectSum.lof ℚ ℤ (fun j : ℤ => ℚ ⊗[ℤ] chowGroup B.base sX j) n t) =
      DirectSum.lof ℚ ℤ (fun j : ℤ => ℚ ⊗[ℤ] chowGroup B.baseChange (pullback.snd sX B.g) j)
        (n + B.c) ((baseChangeChowPullback B sX n).toIntLinearMap.baseChange ℚ t) := by
  simp only [rationalBaseChangeChowPullback, DirectSum.toModule_lof, LinearMap.comp_apply]

/-- `g^*(r ⊗ α) = r ⊗ g^*α`, in degree `n + c`. -/
theorem rationalBaseChangeChowPullback_of_tmul (n : ℤ) (r : ℚ) (α : chowGroup B.base sX n) :
    rationalBaseChangeChowPullback B sX
        (DirectSum.of (fun j : ℤ => ℚ ⊗[ℤ] chowGroup B.base sX j) n (r ⊗ₜ α)) =
      DirectSum.of (fun j : ℤ => ℚ ⊗[ℤ] chowGroup B.baseChange (pullback.snd sX B.g) j)
        (n + B.c) (r ⊗ₜ baseChangeChowPullback B sX n α) := by
  rw [← DirectSum.lof_eq_of ℚ, rationalBaseChangeChowPullback_lof, LinearMap.baseChange_tmul,
    AddMonoidHom.coe_toIntLinearMap, DirectSum.lof_eq_of]

/-- **Base change commutes with `ch_p(α) ∩ -`** on `CH_*(X) ⊗ 𝐐`, for `α ∈ K_0(Vect(X))`. -/
theorem rationalBaseChangeChowPullback_rationalChowCap (a : VectorBundleKZero X) (p : ℕ)
    (x : CHQ(B.base, sX)) :
    rationalBaseChangeChowPullback B sX
        (rationalChowCap B.base (gysinSystemOfInvertible B.base) sX p
          (chernCharacterVectorBundle B.base sX a p) x) =
      rationalChowCap B.baseChange (gysinSystemOfInvertible B.baseChange) (pullback.snd sX B.g) p
        (chernCharacterVectorBundle B.baseChange (pullback.snd sX B.g)
          (VectorBundleKZero.pullback (pullback.fst sX B.g) a) p)
        (rationalBaseChangeChowPullback B sX x) := by
  have h := TotalChowClass.baseChangeCompatible_powerSumKHom B sX p a
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | of k t =>
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add t t' ht ht' => simp only [map_add, ht, ht']
  | tmul r α =>
    rw [chernCharacterVectorBundle_apply, chernCharacterVectorBundle_apply,
      rationalChowCap_of_tmul, rationalBaseChangeChowPullback_of_tmul,
      rationalBaseChangeChowPullback_of_tmul, rationalChowCap_of_tmul]
    exact of_tmul_eq_of_tmul_of_heq B.baseChange (pullback.snd sX B.g) (by ring) _ (h.heq k p α)

/-- **Base change commutes with the Chern character**:
`g^*(ch(α) ∩ β) = ch(α') ∩ g^*β` for `α ∈ K_0(Vect(X))` and `β ∈ CH_*(X) ⊗ 𝐐`, when the
relative dimension functions of `X` over `S` and of `X'` over `S'` are bounded below (so that the
operators `ch(-) ∩ -` are the sums over all degrees). -/
theorem rationalBaseChangeChowPullback_chernCharacterCap
    (hX : BddBelow (Set.range (relativeDimension B.base.dimensionFunction sX)))
    (hX' : BddBelow (Set.range
      (relativeDimension B.baseChange.dimensionFunction (pullback.snd sX B.g))))
    (a : VectorBundleKZero X) (β : CHQ(B.base, sX)) :
    rationalBaseChangeChowPullback B sX (chernCharacterCap B.base sX a β) =
      chernCharacterCap B.baseChange (pullback.snd sX B.g)
        (VectorBundleKZero.pullback (pullback.fst sX B.g) a)
        (rationalBaseChangeChowPullback B sX β) := by
  obtain ⟨lo, hlo⟩ := hX
  obtain ⟨lo', hlo'⟩ := hX'
  have hX₁ : ∀ x : X, lo ≤ relativeDimension B.base.dimensionFunction sX x :=
    fun x => hlo ⟨x, rfl⟩
  have hX₂ : ∀ x : (pullback sX B.g : Scheme.{u}),
      lo' ≤ relativeDimension B.baseChange.dimensionFunction (pullback.snd sX B.g) x :=
    fun x => hlo' ⟨x, rfl⟩
  refine LinearMap.congr_fun (f := rationalBaseChangeChowPullback B sX ∘ₗ
      chernCharacterCap B.base sX a)
    (g := chernCharacterCap B.baseChange (pullback.snd sX B.g)
        (VectorBundleKZero.pullback (pullback.fst sX B.g) a) ∘ₗ
      rationalBaseChangeChowPullback B sX) (DirectSum.linearMap_ext ℚ fun k => ?_) β
  refine LinearMap.ext fun t => ?_
  set N : ℕ := (k - lo).toNat + (k + B.c - lo').toNat
  have hN : ∀ p : ℕ, (p : ℤ) ≤ k - lo → p ∈ Finset.range (N + 1) := fun p hp => by
    rw [Finset.mem_range]; omega
  have hN' : ∀ p : ℕ, (p : ℤ) ≤ k + B.c - lo' → p ∈ Finset.range (N + 1) := fun p hp => by
    rw [Finset.mem_range]; omega
  simp only [LinearMap.comp_apply]
  rw [chernCharacterCap_lof_eq_sum B.base sX lo hX₁ a k t _ hN, map_sum,
    rationalBaseChangeChowPullback_lof,
    chernCharacterCap_lof_eq_sum B.baseChange (pullback.snd sX B.g) lo' hX₂ _ (k + B.c) _ _ hN']
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [rationalBaseChangeChowPullback_rationalChowCap, rationalBaseChangeChowPullback_lof]

/-- **Base change commutes with the Chern character on `K_0(Vect(X)) ⊗ 𝐐`**:
`g^*(ch(x) ∩ β) = ch(x') ∩ g^*β`, under the hypotheses of
`Stacks.Chow.rationalBaseChangeChowPullback_chernCharacterCap`. -/
theorem rationalBaseChangeChowPullback_rationalChernCharacterCap
    (hX : BddBelow (Set.range (relativeDimension B.base.dimensionFunction sX)))
    (hX' : BddBelow (Set.range
      (relativeDimension B.baseChange.dimensionFunction (pullback.snd sX B.g))))
    (x : ℚ ⊗[ℤ] VectorBundleKZero X) (β : CHQ(B.base, sX)) :
    rationalBaseChangeChowPullback B sX (rationalChernCharacterCap B.base sX x β) =
      rationalChernCharacterCap B.baseChange (pullback.snd sX B.g)
        ((VectorBundleKZero.pullback (pullback.fst sX B.g)).toIntLinearMap.baseChange ℚ x)
        (rationalBaseChangeChowPullback B sX β) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | tmul r a =>
    rw [rationalChernCharacterCap_tmul, LinearMap.baseChange_tmul,
      AddMonoidHom.coe_toIntLinearMap, rationalChernCharacterCap_tmul, LinearMap.smul_apply,
      LinearMap.smul_apply, map_smul, rationalBaseChangeChowPullback_chernCharacterCap B sX hX hX']
  | add x y hx hy =>
    rw [map_add, LinearMap.add_apply, map_add, hx, hy, map_add, map_add, LinearMap.add_apply]

end Stacks.Chow

end
