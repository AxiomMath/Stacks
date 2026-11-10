module

public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.CapRuleFlat
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.FirstChernComm
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.InvertibleCap
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.ModuleFacts

/-!
# The Chern class cap products commute with the first Chern class of an invertible module

Let `X` be locally of finite type over the base of chapter 42, `ℱ` finite locally free of rank
`r` and `ℒ` invertible on `X`. Then

  `c_j(ℱ) ∩ c₁(ℒ) ∩ α = c₁(ℒ) ∩ c_j(ℱ) ∩ α`,  `0 ≤ j ≤ r`,

for the cap products `Stacks.Chow.GenuineChern.chernCap` of [Stacks, Tag 02U6].

## Main definitions

* `Stacks.Chow.GenuineChern.ChowLowering` — a homomorphism `A_a ⟶ A_b` for every `a = b + e`.
* `Stacks.Chow.GenuineChern.ChernTermsCompatibleWithLowering` — such operations on the base and
  on the bundle carry the summands of the relation of Stacks 02U6 to each other.

## Main results

* `Stacks.Chow.GenuineChern.isChernCapFamily_lowering` — the operations carry a family solving
  the relation for `α` to a family solving it for the image of `α`.
* `Stacks.Chow.GenuineChern.chernTermsCompatibleWithLowering_of` — compatibility follows from
  compatibility with `π^*` and with the cap of the twist.
* `Stacks.Chow.GenuineChern.chernCap_invCap_comm` — `c_j(ℱ) ∩ c₁(ℒ) ∩ α = c₁(ℒ) ∩ c_j(ℱ) ∩ α`.

## References

* [Stacks Project, Tag 02U6](https://stacks.math.columbia.edu/tag/02U6)
* [Stacks Project, Tag 02SS](https://stacks.math.columbia.edu/tag/02SS)
* [Stacks Project, Tag 02TJ](https://stacks.math.columbia.edu/tag/02TJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow.GenuineChern

variable (C : ChowSituation.{u})

/-! ### Operations lowering degrees -/

/-- A homomorphism of Chow groups lowering the degree by `e`, given for every pair of degrees
`a = b + e`. -/
abbrev ChowLowering {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (e : ℤ) :=
  ∀ a b : ℤ, a = b + e → (chowGroup C sX a →+ chowGroup C sX b)

section Lowering

variable {C} {X : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX] {e : ℤ}

/-- A lowering operation absorbs a transport of its source degree. -/
theorem ChowLowering.apply_chowGroupCast (φ : ChowLowering C sX e) {a a' b : ℤ}
    (h : a' = b + e) (ha : a = a') (x : chowGroup C sX a) :
    φ a' b h (chowGroupCast C sX ha x) = φ a b (ha.trans h) x := by
  subst ha; rfl

/-- A lowering operation absorbs a transport of its target degree. -/
theorem ChowLowering.chowGroupCast_apply (φ : ChowLowering C sX e) {a b b' : ℤ}
    (h : a = b + e) (hb : b = b') (x : chowGroup C sX a) :
    chowGroupCast C sX hb (φ a b h x) = φ a b' (hb ▸ h) x := by
  subst hb; rfl

/-- A lowering operation respects heterogeneous equality. -/
theorem ChowLowering.heq_apply (φ : ChowLowering C sX e) {a a' b b' : ℤ} (h : a = b + e)
    (h' : a' = b' + e) (ha : a = a') (hb : b = b') {x : chowGroup C sX a}
    {x' : chowGroup C sX a'} (hx : x ≍ x') : φ a b h x ≍ φ a' b' h' x' := by
  subst ha hb; cases hx; rfl

end Lowering

/-- The cap operator commutes with a transport of degrees. -/
theorem capOnChow_chowGroupCast {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (O : ChernCapOperator C sX) {m m' : ℤ} (h : m = m') (h' : m + 1 = m' + 1)
    (x : chowGroup C sX (m + 1)) :
    O.capOnChow C sX m' (chowGroupCast C sX h' x) =
      chowGroupCast C sX h (O.capOnChow C sX m x) := by
  subst h; rfl

/-- The cap operator `ξ ∩ -` as an operation lowering degrees by one. -/
def capLowering {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (O : ChernCapOperator C sX) : ChowLowering C sX 1 := fun _ b h ↦
  (O.capOnChow C sX b).comp (chowGroupCast C sX h).toAddMonoidHom

/-- The lowering operation `ξ ∩ -` acts by the cap operator, after transporting the source degree
to `b + 1`. -/
@[simp]
theorem capLowering_apply {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (O : ChernCapOperator C sX) (a b : ℤ) (h : a = b + 1) (x : chowGroup C sX a) :
    capLowering C sX O a b h x = O.capOnChow C sX b (chowGroupCast C sX h x) :=
  rfl

/-! ### Transport of the relation of Stacks 02U6 -/

section Relation

variable {X P : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sP : P ⟶ C.S) [LocallyOfFiniteType sP] (π : P ⟶ X) [LocallyOfFiniteType π] [Flat π]
  (hsP : π ≫ sX = sP) (r : ℕ) (hπ : AlgebraicGeometry.RelativeDimension π (r - 1))
  (hfac : ∀ k : ℤ, FlatPullbackFactorsThroughRationalEquivalence C sP sX π hsP (r - 1) hπ k)
  (twist : ChernCapOperator C sP) (e : ℤ) (φ : ChowLowering C sX e) (ψ : ChowLowering C sP e)

/-- **The summands of the relation of Stacks 02U6 are compatible with two lowering
operations**: `ψ` on the bundle carries the `i`-th summand in degree `k` to the `i`-th summand in
degree `k'` of the image under `φ`, for `k = k' + e`. -/
def ChernTermsCompatibleWithLowering : Prop :=
  ∀ (k k' : ℤ) (hk : k = k' + e) (i : ℕ) (hi : i ≤ r)
    (x : chowGroup C sX (k - ((r - i : ℕ) : ℤ))),
    ψ _ _ (by omega) (projectiveBundleChernTerm C sX sP π hsP r hπ hfac twist k i hi x) =
      projectiveBundleChernTerm C sX sP π hsP r hπ hfac twist k' i hi (φ _ _ (by omega) x)

/-- **Lowering operations carry the relation of Stacks 02U6.** If `φ` and `ψ` are compatible
with the summands of the relation and `c` solves the relation for `α ∈ A_k(X)`, then
`j ↦ φ(c_j)` solves it for `φ(α) ∈ A_{k'}(X)`, `k = k' + e`. -/
theorem isChernCapFamily_lowering
    (hcompat : ChernTermsCompatibleWithLowering C sX sP π hsP r hπ hfac twist e φ ψ)
    (k k' : ℤ) (hk : k = k' + e) (α : chowGroup C sX k)
    (c : ∀ j : Fin (r + 1), chowGroup C sX (k - (j : ℤ)))
    (hc : IsChernCapFamily C sX sP π hsP r hπ hfac twist k α c) :
    IsChernCapFamily C sX sP π hsP r hπ hfac twist k' (φ k k' hk α)
      (fun j ↦ φ (k - (j : ℤ)) (k' - (j : ℤ)) (by omega) (c j)) := by
  refine ⟨?_, ?_⟩
  · rw [ChowLowering.chowGroupCast_apply, ← hc.1, ChowLowering.apply_chowGroupCast]
  · change ∑ i : Fin (r + 1), (-1 : ℤ) ^ i.val •
        projectiveBundleChernTerm C sX sP π hsP r hπ hfac twist k' i.val
          (Nat.lt_succ_iff.mp i.isLt)
          (φ (k - ((r - i.val : ℕ) : ℤ)) (k' - ((r - i.val : ℕ) : ℤ)) (by omega)
            (c ⟨r - i.val, by omega⟩)) = 0
    have hsum : ∑ i : Fin (r + 1), (-1 : ℤ) ^ i.val •
        projectiveBundleChernTerm C sX sP π hsP r hπ hfac twist k' i.val
          (Nat.lt_succ_iff.mp i.isLt)
          (φ (k - ((r - i.val : ℕ) : ℤ)) (k' - ((r - i.val : ℕ) : ℤ)) (by omega)
            (c ⟨r - i.val, by omega⟩)) =
        ψ _ _ (by omega) (∑ i : Fin (r + 1), (-1 : ℤ) ^ i.val •
          projectiveBundleChernTerm C sX sP π hsP r hπ hfac twist k i.val
            (Nat.lt_succ_iff.mp i.isLt) (c ⟨r - i.val, by omega⟩)) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [map_zsmul, hcompat k k' hk]
    rw [hsum, hc.2, map_zero]

/-- The `i`-th summand of the relation of Stacks 02U6 is `ξ^i ∩ π^*(-)`, read in the degrees of
`Stacks.Chow.capPow`. -/
theorem projectiveBundleChernTerm_eq_capPow (k : ℤ) (i : ℕ) (hi : i ≤ r)
    (x : chowGroup C sX (k - ((r - i : ℕ) : ℤ))) :
    projectiveBundleChernTerm C sX sP π hsP r hπ hfac twist k i hi x =
      capPow C sP twist i (k - ((r - i : ℕ) : ℤ) + ((r - 1 : ℕ) : ℤ))
        (k + ((r - 1 : ℕ) : ℤ) - (r : ℤ)) (by omega)
        (projectiveBundlePullback C sX sP π hsP r hπ hfac (k - ((r - i : ℕ) : ℤ)) x) := by
  simp only [projectiveBundleChernTerm, AddMonoidHom.coe_comp, Function.comp_apply,
    AddEquiv.coe_toAddMonoidHom]
  rw [← capPow_eq_iteratedChernCapOnChow, capPow_cast]

/-- **A lowering operation commuting with one cap commutes with every power of it.** -/
theorem lowering_capPow
    (hξ : ∀ (b c : ℤ) (h : b = c + e) (x : chowGroup C sP (b + 1)),
      ψ b c h (twist.capOnChow C sP b x) =
        twist.capOnChow C sP c (ψ (b + 1) (c + 1) (by omega) x))
    (s : ℕ) (a m : ℤ) (h : a = m + s) (a' m' : ℤ) (h' : a' = m' + s) (ha : a = a' + e)
    (hm : m = m' + e) (x : chowGroup C sP a) :
    ψ m m' hm (capPow C sP twist s a m h x) = capPow C sP twist s a' m' h' (ψ a a' ha x) := by
  induction s generalizing m m' with
  | zero =>
    rw [capPow_zero_apply, capPow_zero_apply, ChowLowering.apply_chowGroupCast,
      ChowLowering.chowGroupCast_apply]
  | succ s ih =>
    rw [capPow_succ_apply', capPow_succ_apply', hξ,
      ih (m + 1) _ (m' + 1) (by push_cast at h' ⊢; omega)]

/-- **Compatibility with the summands from compatibility with `π^*` and with the twist.** If
`ψ ∘ π^* = π^* ∘ φ` and `ψ` commutes with `ξ ∩ -`, then `φ` and `ψ` are compatible with the
summands of the relation of Stacks 02U6. -/
theorem chernTermsCompatibleWithLowering_of
    (hpull : ∀ (a b : ℤ) (h : a = b + e) (x : chowGroup C sX a),
      ψ (a + ((r - 1 : ℕ) : ℤ)) (b + ((r - 1 : ℕ) : ℤ)) (by omega)
          (projectiveBundlePullback C sX sP π hsP r hπ hfac a x) =
        projectiveBundlePullback C sX sP π hsP r hπ hfac b (φ a b h x))
    (hξ : ∀ (b c : ℤ) (h : b = c + e) (x : chowGroup C sP (b + 1)),
      ψ b c h (twist.capOnChow C sP b x) =
        twist.capOnChow C sP c (ψ (b + 1) (c + 1) (by omega) x)) :
    ChernTermsCompatibleWithLowering C sX sP π hsP r hπ hfac twist e φ ψ := by
  intro k k' hk i hi x
  rw [projectiveBundleChernTerm_eq_capPow, projectiveBundleChernTerm_eq_capPow,
    lowering_capPow C sP twist e ψ hξ i _ _ _ (k' - ((r - i : ℕ) : ℤ) + ((r - 1 : ℕ) : ℤ)) _
      (by omega) (by omega), hpull (k - ((r - i : ℕ) : ℤ)) (k' - ((r - i : ℕ) : ℤ)) (by omega)]

end Relation

/-! ### The first Chern class of an invertible module -/

section Invertible

variable {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]

/-- **Stacks 02SS, as a compatibility of lowering operations.** Flat pullback carries
`c₁(ℒ) ∩ -` to `c₁(π^*ℒ) ∩ -`. -/
theorem capLowering_invCap_flatPullbackChow {P : Scheme.{u}} (sP : P ⟶ C.S)
    [LocallyOfFiniteType sP] (π : P ⟶ X) [LocallyOfFiniteType π] [Flat π] (hsP : π ≫ sX = sP)
    (d : ℕ) (hπ : AlgebraicGeometry.RelativeDimension π d)
    (hfac : ∀ k : ℤ, FlatPullbackFactorsThroughRationalEquivalence C sP sX π hsP d hπ k)
    (a b : ℤ) (h : a = b + 1) (x : chowGroup C sX a) :
    haveI := isInvertible_pullback π L
    capLowering C sP (invCap C sP ((Scheme.Modules.pullback π).obj L)) (a + d) (b + d)
        (by omega) (flatPullbackChow C sP sX π hsP d hπ a (hfac a) x) =
      flatPullbackChow C sP sX π hsP d hπ b (hfac b)
        (capLowering C sX (invCap C sX L) a b h x) := by
  have := isInvertible_pullback π L
  exact (eq_of_heq (flatPullbackChow_firstChernClassCapChow_heq C sP sX π hsP d hπ hfac L _
    (Iso.refl _) b (chowGroupCast C sX h x) _ ((chowGroupCast_heq C sP _ _).trans
      (flatPullbackChow_heq_of_degree C sP sX π hsP d hπ h (hfac a) (hfac (b + 1))
        (chowGroupCast_heq C sX h x).symm)))).symm

/-- **Stacks 02TJ, as a compatibility of lowering operations.** `c₁(ℒ) ∩ -` commutes with the
cap `c₁(ℳ) ∩ -` of any invertible module. -/
theorem capLowering_invCap_comm (M : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M]
    (b c : ℤ) (h : b = c + 1) (x : chowGroup C sX (b + 1)) :
    capLowering C sX (invCap C sX L) b c h ((invCap C sX M).capOnChow C sX b x) =
      (invCap C sX M).capOnChow C sX c
        (capLowering C sX (invCap C sX L) (b + 1) (c + 1) (by omega) x) := by
  rw [capLowering_apply, ← capOnChow_chowGroupCast C sX (invCap C sX M) h (by omega)]
  exact invCap_capOnChow_comm C sX c L M _

end Invertible

/-! ### The Chern class cap products commute with the first Chern class -/

section Comm

variable {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]

/-- **The family of `c₁(ℒ) ∩ α`**, for a module `ℰ` of rank `n + 1`: its `j`-th member is
`c₁(ℒ) ∩ c_j(ℰ) ∩ α`. -/
theorem bundleChernCapFamily_invCap (E : X.Modules) (n : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (n + 1)] (k : ℤ)
    (α : chowGroup C sX (k + 1)) :
    bundleChernCapFamily E n C sX k ((invCap C sX L).capOnChow C sX k α) =
      fun j : Fin (n + 1 + 1) ↦ (invCap C sX L).capOnChow C sX (k - (j : ℤ))
        (chowGroupCast C sX (by omega) (bundleChernCapFamily E n C sX (k + 1) α j)) := by
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E
    (n + 1)
  let := flat_bundleProj E n
  let := locallyOfFiniteType_bundleProj E n
  have := isInvertible_pullback (bundleProj E) L
  have hcompat := chernTermsCompatibleWithLowering_of C sX (bundleProj E ≫ sX) (bundleProj E) rfl
    (n + 1) (relativeDimension_bundleProj E n)
    (fun k ↦ flatPullbackFactorsThroughRationalEquivalence_general C _ sX _ rfl _ _ k)
    (bundleTwistCap E C sX) 1 (capLowering C sX (invCap C sX L))
    (capLowering C _ (invCap C _ ((Scheme.Modules.pullback (bundleProj E)).obj L)))
    (fun a b h x ↦ capLowering_invCap_flatPullbackChow C sX L (bundleProj E ≫ sX) (bundleProj E)
      rfl (n + 1 - 1) (relativeDimension_bundleProj E n)
      (fun k ↦ flatPullbackFactorsThroughRationalEquivalence_general C _ sX _ rfl _ _ k) a b h x)
    (fun b c h x ↦ capLowering_invCap_comm C (bundleProj E ≫ sX)
      ((Scheme.Modules.pullback (bundleProj E)).obj L) (bundleTwist E) b c h x)
  have hfam := isChernCapFamily_lowering C sX (bundleProj E ≫ sX) (bundleProj E) rfl (n + 1)
    (relativeDimension_bundleProj E n)
    (fun k ↦ flatPullbackFactorsThroughRationalEquivalence_general C _ sX _ rfl _ _ k)
    (bundleTwistCap E C sX) 1 _ _ hcompat (k + 1) k rfl α _
    (isChernCapFamily_bundleChernCapFamily E n C sX (k + 1) α)
  exact (eq_bundleChernCapFamily_of_isChernCapFamily E n C sX k _ _ hfam).symm

/-- **The Chern class cap products commute with the first Chern class of an invertible
module.** For `ℱ` finite locally free of rank `r` and `ℒ` invertible on `X`, and
`α ∈ A_{k+1}(X)`,

  `c_j(ℱ) ∩ c₁(ℒ) ∩ α = c₁(ℒ) ∩ c_j(ℱ) ∩ α`  in  `A_{k-j}(X)`. -/
theorem chernCap_invCap_comm (F : X.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r] (k : ℤ)
    (j : Fin (r + 1)) (α : chowGroup C sX (k + 1)) :
    chernCap C r sX F k j ((invCap C sX L).capOnChow C sX k α) =
      (invCap C sX L).capOnChow C sX (k - (j : ℤ))
        (chowGroupCast C sX (by omega) (chernCap C r sX F (k + 1) j α)) := by
  cases r with
  | zero =>
    have hj : k = k - ((j : ℕ) : ℤ) := by simp
    rw [chernCap_zero, chernCap_zero, chowGroupCast_chowGroupCast,
      capOnChow_chowGroupCast C sX _ hj]
  | succ n =>
    rw [chernCap_succ, chernCap_succ, bundleChernCap_apply, bundleChernCap_apply,
      bundleChernCapFamily_invCap]

end Comm

end Stacks.Chow.GenuineChern

end
