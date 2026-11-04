module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.VectorBundleFlatPullback
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.CapRuleFlatGeneral
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Vanishing
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.TwistFormula
public import StacksFrontier.AlgebraicGeometry.Chow.GysinPushforwardChernCap
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.LocalizationSequence
public import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.DualTotalChern

/-!
# The top Chern class of `π^*𝒞 ⊗ 𝒪(-1)` on the projective completion

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S` and let `𝒞` be a finite locally free `𝒪_X`-module of rank `r`. Write
`π : E = 𝐏(𝒞 ⊕ 𝒪_X) ⟶ X` for the projective completion of the vector bundle
`C = Spec_X(Sym(𝒞))`, `ξ = c₁(𝒪_E(1))`, `V ⊆ E` for the complement of the divisor at infinity,
which is `C`, and `p : V ⟶ X` for the projection. The module

  `ℰ = π^*𝒞 ⊗ 𝒪_E(-1)`

carries the canonical map `ℰ ⟶ 𝒪_E` whose Koszul complex resolves the zero section, and this
file computes the action of its top Chern class: for every `α ∈ CH_*(E)`,

  `p^*(π_*(c_r(ℰ) ∩ α)) = (-1)^r α|_V`

in `CH_*(V)`. This is the cap-product computation in the proof of Stacks 0FEF.

## The proof

By Stacks 02UD, `c_r(ℰ) ∩ π^*β = ∑_j (-1)^j ξ^j ∩ π^*(c_{r-j}(𝒞) ∩ β)`, since `c₁(𝒪(-1)) = -ξ`
and the Chern classes commute with flat pullback (Stacks 02U8) and with `ξ`. Hence:

* by Stacks 02TW only the summand `j = r` survives pushforward, and
  `π_*(c_r(ℰ) ∩ π^*β) = (-1)^r β`;
* by the relation of Stacks 02U6 for the module `𝒞 ⊕ 𝒪_X` of rank `r + 1`, whose Chern classes
  are those of `𝒞` (Stacks 02UG), `ξ ∩ c_r(ℰ) ∩ π^*β = 0`;
* `ξ ∩ -` is the pushforward of the Gysin map of the divisor at infinity (Stacks 02T9), so its
  values restrict to zero on `V` (Stacks 02RX).

By the projective space bundle formula (Stacks 02TX) every class on `E` is
`∑_i ξ^i ∩ π^*β_i`; the summands with `i ≥ 1` contribute to neither side, and on the summand
`i = 0` both sides are `(-1)^r p^*β_0`, the restriction of `π^*β_0` to `V` being `p^*β_0`.

This replaces the reduction of the source to integral closed subschemes `W` either disjoint from
`C` or of the form `π^{-1}(Y)` ("details omitted"): those two kinds of `W` span the same classes
as the summands `i ≥ 1` and `i = 0` of the projective space bundle formula.

## Main definitions

* `Stacks.ProjectiveCompletion.koszulModule` — the module `π^*𝒞 ⊗ 𝒪_E(-1)`.

## Main results

* `Stacks.Chow.capPow_invCap_dualSheaf` — `c₁(ℒ^∨)^s ∩ - = (-1)^s c₁(ℒ)^s ∩ -`.
* `Stacks.Chow.chernCap_capPow_heq` — Chern class caps commute with powers of `c₁(ℒ)`.
* `Stacks.Chow.chernCap_tensorDual_bundlePullback` — the expansion of `c_r(π^*𝒞 ⊗ ℳ^∨) ∩ π^*β`
  along a flat morphism `π`.
* `Stacks.Chow.pushforward_chernCap_tensorDual_bundlePullback` — `π_*(c_r(ℰ) ∩ π^*β) = (-1)^r β`
  along a locally projective tower.
* `Stacks.Chow.flatPullback_pushforward_chernCap_tensorDual` — the identity displayed above along
  a locally projective tower, granted `ξ ∩ c_r(ℰ) ∩ π^*β = 0` and `(ξ ∩ y)|_V = 0`.
* `Stacks.Chow.capOnChow_chernCap_tensorDual_bundlePullback_of_relation` — `ξ ∩ c_r(ℰ) ∩ π^*β = 0`
  along a tower on which the relation of Stacks 02U6 for `𝒞 ⊕ 𝒪_U` holds.
* `Stacks.Chow.restrict_capOnChow_eq_zero_of_range_zeroScheme` — `(c₁(ℳ) ∩ y)|_V = 0` when `V` is
  the complement of the zero scheme of a section of `ℳ`.
* `Stacks.Chow.capOnChow_chernCap_koszulModule_bundlePullback` — `ξ ∩ c_r(ℰ) ∩ π^*β = 0` on `E`.
* `Stacks.Chow.restrict_complementOpen_capOnChow` — `(ξ ∩ y)|_V = 0` on `E`.
* `Stacks.Chow.flatPullback_pushforward_chernCap_koszulModule` — the identity displayed above on
  `E`.

## Implementation notes

The computation is carried out for an arbitrary flat proper `π : P ⟶ U` which is a projective
tower of fibre dimension `r` locally on `U`, with an arbitrary twist `ℳ`, the two properties of
the projective completion that are not formal — the vanishing of `ξ ∩ c_r(ℰ)` on pulled-back
classes and of `ξ ∩ -` on `V` — being taken as hypotheses there. Both are reduced to properties
of the tower, the relation of Stacks 02U6 for `𝒞 ⊕ 𝒪_U` and a section of `ℳ` whose zero scheme is
the complement of `V`, which hold for `E` itself and, locally projective towers being stable under
base change, for every `X' ×_X E`; the latter is
`StacksFrontier.AlgebraicGeometry.Chow.ZeroSectionKoszul.TopChernCapBaseChange`.

## References

* [Stacks Project, Tag 0FEF](https://stacks.math.columbia.edu/tag/0FEF)
* [Stacks Project, Tag 02UD](https://stacks.math.columbia.edu/tag/02UD)
* [Stacks Project, Tag 02U6](https://stacks.math.columbia.edu/tag/02U6)
* [Stacks Project, Tag 02UG](https://stacks.math.columbia.edu/tag/02UG)
* [Stacks Project, Tag 02TW](https://stacks.math.columbia.edu/tag/02TW)
* [Stacks Project, Tag 02TX](https://stacks.math.columbia.edu/tag/02TX)
* [Stacks Project, Tag 02T9](https://stacks.math.columbia.edu/tag/02T9)
* [Stacks Project, Tag 02RX](https://stacks.math.columbia.edu/tag/02RX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace Stacks.ProjectiveCompletion

variable {X : Scheme.{u}} (E : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]

/-- **The module `π^*ℰ ⊗ 𝒪_P(-1)`** on the projective completion `π : P = 𝐏(ℰ ⊕ 𝒪_X) ⟶ X`, with
`𝒪_P(-1)` the dual of the twist. It carries the canonical map to `𝒪_P` induced by the
tautological quotient `π^*ℰ ⟶ 𝒪_P(1)`, whose Koszul complex resolves the zero section. -/
abbrev koszulModule : (projectiveCompletion E).Modules :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor (projectiveCompletion E).sheaf).obj
    ((Scheme.Modules.pullback (projectiveCompletionProj E)).obj E)).obj
      (dualSheaf (Stacks.Chow.bundleTwist (completionModule E)))

end Stacks.ProjectiveCompletion

namespace Stacks.Chow

open Stacks.ProjectiveCompletion

/-! ### Powers of a first Chern class -/

section Generic

variable (C : ChowSituation.{u}) {T : Scheme.{u}} (q : T ⟶ C.S) [LocallyOfFiniteType q]

/-- **Powers of the first Chern class of a dual**: `c₁(ℒ^∨)^s ∩ - = (-1)^s c₁(ℒ)^s ∩ -`, by
Stacks 02SP for the dual, `c₁(ℒ^∨) = -c₁(ℒ)`. -/
theorem capPow_invCap_dualSheaf (N : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property N]
    (s : ℕ) (a m : ℤ) (h : a = m + s) (x : chowGroup C q a) :
    capPow C q (invCap C q (dualSheaf N)) s a m h x =
      ((-1 : ℤ) ^ s) • capPow C q (invCap C q N) s a m h x := by
  induction s generalizing a with
  | zero => simp
  | succ s ih =>
    rw [capPow_succ_apply, capPow_succ_apply, invCap_capOnChow_dualSheaf, map_neg, ih,
      pow_succ, mul_neg_one, neg_smul]

/-- **The Chern class caps commute with the powers of a first Chern class**:
`c_j(ℱ) ∩ c₁(ℒ)^s ∩ x = c₁(ℒ)^s ∩ c_j(ℱ) ∩ x`, the two sides being read in the same degree. -/
theorem chernCap_capPow_heq (F : T.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r] (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (j : Fin (r + 1)) (s : ℕ) (a m : ℤ) (h : a = m + s) (x : chowGroup C q a) :
    GenuineChern.chernCap C r q F m j (capPow C q (invCap C q L) s a m h x) ≍
      capPow C q (invCap C q L) s (a - (j : ℤ)) (m - (j : ℤ)) (by omega)
        (GenuineChern.chernCap C r q F a j x) := by
  induction s generalizing a with
  | zero =>
    rw [capPow_zero_apply, capPow_zero_apply]
    refine HEq.trans ?_ (chowGroupCast_heq C q _ _).symm
    exact TotalChowClass.chernCap_heq C q F r j (by simpa using h.symm)
      (chowGroupCast_heq C q _ x)
  | succ s ih =>
    rw [capPow_succ_apply, capPow_succ_apply]
    refine (ih (a - 1) _ _).trans ?_
    refine GenuineChern.capPow_heq C q _ _ _ rfl (by ring) rfl ?_
    rw [GenuineChern.chernCap_invCap_comm C q L F r (a - 1) j]
    refine capOnChow_heq C q _ (by ring) ?_
    refine (chowGroupCast_heq C q _ _).trans (HEq.trans ?_ (chowGroupCast_heq C q _ _).symm)
    exact TotalChowClass.chernCap_heq C q F r j (by ring) (chowGroupCast_heq C q _ x)

end Generic

/-- Restriction to an open of a flat pullback along `π` is the flat pullback along `V ⟶ U`. -/
private theorem chowGroupOpensRestrict_bundlePullback (C : ChowSituation.{u}) {U P : Scheme.{u}}
    (sU : U ⟶ C.S) [LocallyOfFiniteType sU] (sP : P ⟶ C.S) [LocallyOfFiniteType sP]
    (π : P ⟶ U) [LocallyOfFiniteType π] [Flat π] (hsP : π ≫ sU = sP) (r : ℕ)
    (hπ : AlgebraicGeometry.RelativeDimension π r) (V : P.Opens)
    (hV : AlgebraicGeometry.RelativeDimension (V.ι ≫ π) r) (m : ℤ) (b : chowGroup C sU m) :
    chowGroupOpensRestrictOfIsOpenImmersion C sP V (m + r)
      (bundlePullback C sU sP π hsP r hπ m b) =
    bundlePullback C sU (V.ι ≫ sP) (V.ι ≫ π) (by rw [Category.assoc, hsP]) r hV m b := by
  have heq : ∀ x, chowGroupOpensRestrictOfIsOpenImmersion C sP V (m + r) x =
      chowGroupRestrict C sP (V.ι ≫ sP) V.ι rfl _ x := by
    intro x
    obtain ⟨c, rfl⟩ := QuotientAddGroup.mk'_surjective _ x
    rfl
  rw [heq]
  exact chowGroupRestrict_bundlePullback C sU _ _ hsP r _ V _ m b

/-! ### The computation along a projective tower -/

section Tower

variable (C : ChowSituation.{u}) {U P : Scheme.{u}} (sU : U ⟶ C.S) [LocallyOfFiniteType sU]
  (sP : P ⟶ C.S) [LocallyOfFiniteType sP] (π : P ⟶ U) [LocallyOfFiniteType π] [Flat π]
  [IsProper π] (hsP : π ≫ sU = sP) (r : ℕ) (hπ : AlgebraicGeometry.RelativeDimension π r)
  (M : P.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property M]
  (𝒞 : U.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒞 r]
  (ℰ : P.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} ℰ r]

omit [IsProper π] in
/-- **The expansion of `c_r(π^*𝒞 ⊗ ℳ^∨) ∩ π^*β`** (Stacks 02UD), for a module `ℰ` isomorphic to
`π^*𝒞 ⊗ ℳ^∨` with `ℳ` invertible and `ξ = c₁(ℳ)`:

  `c_r(ℰ) ∩ π^*β = ∑_j (-1)^j ξ^j ∩ π^*(c_{r-j}(𝒞) ∩ β)`. -/
theorem chernCap_tensorDual_bundlePullback
    (eℰ : ℰ ≅ ((Stacks.SheafOfModules.Tensor.sheafTensor P.sheaf).obj
      ((Scheme.Modules.pullback π).obj 𝒞)).obj (dualSheaf M))
    (m : ℤ) (β : chowGroup C sU m) :
    GenuineChern.chernCap C r sP ℰ (m + r) (Fin.last r)
        (bundlePullback C sU sP π hsP r hπ m β) =
      ∑ j : Fin (r + 1), ((-1 : ℤ) ^ (j : ℕ)) •
        capPow C sP (invCap C sP M) j (m - ((r - j : ℕ) : ℤ) + r) (m + r - r)
          (by have := j.isLt; omega)
          (bundlePullback C sU sP π hsP r hπ (m - ((r - j : ℕ) : ℤ))
            (GenuineChern.chernCap C r sU 𝒞 m ⟨r - j, by omega⟩ β)) := by
  have := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank 𝒞 r π
  let : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (R := P.ringCatSheaf) (((Stacks.SheafOfModules.Tensor.sheafTensor P.sheaf).obj
        ((Scheme.Modules.pullback π).obj 𝒞)).obj (dualSheaf M)) r :=
    GenuineChern.isFiniteLocallyFreeOfRank_sheafTensor _ r _
  rw [GenuineChern.chernCap_congr C sP r eℰ, GenuineChern.chernCap_sheafTensor C sP
    ((Scheme.Modules.pullback π).obj 𝒞) r _ (m + r) (Fin.last r)]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hj := j.isLt
  simp only [Fin.val_last, Nat.sub_self, zero_add, Nat.choose_self, Nat.cast_one, one_smul]
  rw [capPow_invCap_dualSheaf, map_zsmul, map_zsmul]
  congr 1
  refine eq_of_heq ((chowGroupCast_heq C _ _ _).trans ?_)
  refine (chernCap_capPow_heq C _ _ r _ _ _ _ _ _ _).trans ?_
  refine GenuineChern.capPow_heq C _ _ _ _ rfl (by simp only; omega)
    (by simp only; omega) ?_
  exact GenuineChern.chernCap_flatPullback_heq_general C sU sP π hsP r hπ 𝒞 r
    ((Scheme.Modules.pullback π).obj 𝒞) (Iso.refl _) m ⟨r - j, by omega⟩ β

/-- A Chern class cap product read at two equal indices. -/
theorem chernCap_heq_of_index_eq {T : Scheme.{u}} (q : T ⟶ C.S) [LocallyOfFiniteType q]
    (F : T.Modules) (n : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F n] (k : ℤ)
    {i i' : Fin (n + 1)} (h : i = i') (x : chowGroup C q k) :
    GenuineChern.chernCap C n q F k i x ≍ GenuineChern.chernCap C n q F k i' x := by
  subst h; rfl

/-- **The pushforward of the top Chern class** (Stacks 02TW along a locally projective tower of
fibre dimension `r` with twist `ℳ`): `π_*(c_r(π^*𝒞 ⊗ ℳ^∨) ∩ π^*β) = (-1)^r β`. -/
theorem pushforward_chernCap_tensorDual_bundlePullback
    (htower : IsLocallyProjectiveTower r π M)
    (eℰ : ℰ ≅ ((Stacks.SheafOfModules.Tensor.sheafTensor P.sheaf).obj
      ((Scheme.Modules.pullback π).obj 𝒞)).obj (dualSheaf M))
    (m : ℤ) (β : chowGroup C sU m) :
    properChowPushforward C sP sU π hsP (m + r - r)
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ sU _ hsP _)
        (GenuineChern.chernCap C r sP ℰ (m + r) (Fin.last r)
          (bundlePullback C sU sP π hsP r hπ m β)) =
      ((-1 : ℤ) ^ r) • chowGroupCast C sU (by ring) β := by
  rw [chernCap_tensorDual_bundlePullback C sU sP π hsP r hπ M 𝒞 ℰ eℰ, map_sum]
  simp only [map_zsmul]
  have hterm : ∀ j : Fin (r + 1),
      properChowPushforward C sP sU π hsP (m + r - r)
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ sU _ hsP _)
          (capPow C sP (invCap C sP M) j (m - ((r - j : ℕ) : ℤ) + r) (m + r - r)
            (by have := j.isLt; omega)
            (bundlePullback C sU sP π hsP r hπ (m - ((r - j : ℕ) : ℤ))
              (GenuineChern.chernCap C r sU 𝒞 m ⟨r - j, by omega⟩ β))) =
        if hsn : (j : ℕ) = r then chowGroupCast C sU (by simp only; omega)
          (GenuineChern.chernCap C r sU 𝒞 m ⟨r - j, by omega⟩ β) else 0 := by
    intro j
    split_ifs with hsn
    · have hj : j = Fin.last r := Fin.ext hsn
      subst hj
      refine eq_of_heq (HEq.trans ?_ (chowGroupCast_heq C sU _ _).symm)
      refine HEq.trans ?_ (heq_of_eq (htower.bundleProjection_self C sU sP hsP hπ
        (m - ((r - (Fin.last r : ℕ) : ℕ) : ℤ)) _))
      refine heq_apply_of_degree C _ _ (fun d ↦ d) (fun d ↦ d)
        (fun d ↦ properChowPushforward C sP sU π hsP d
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ sU _ hsP _))
        (by simp) ?_
      exact GenuineChern.capPow_heq C _ _ _ _ rfl (by simp) (by simp) HEq.rfl
    · exact bundleProjection_eq_zero_of_lt C sU sP π hsP r hπ (invCap C sP M) j
        (lt_of_le_of_ne (Nat.lt_succ_iff.mp j.isLt) hsn) _ _ _ _
  simp only [hterm]
  rw [Fin.sum_univ_castSucc]
  have hzero : ∀ i : Fin r, ((-1 : ℤ) ^ (i.castSucc : ℕ)) •
      (if hsn : (i.castSucc : ℕ) = r then chowGroupCast C sU (by simp only; omega)
        (GenuineChern.chernCap C r sU 𝒞 m ⟨r - i.castSucc, by omega⟩ β) else 0 :
          chowGroup C sU (m + r - r)) = 0 := by
    intro i
    rw [dite_eq_right (by simp only [Fin.val_castSucc]; omega), smul_zero]
  rw [Finset.sum_eq_zero fun i _ ↦ hzero i, zero_add, dite_eq_left (by simp)]
  congr 1
  refine eq_of_heq ((chowGroupCast_heq C sU _ _).trans (HEq.trans ?_
    (chowGroupCast_heq C sU _ _).symm))
  refine (chernCap_heq_of_index_eq C sU 𝒞 r m (i' := 0) (Fin.ext (by simp)) β).trans ?_
  have h0 := GenuineChern.chernCap_zero_apply C sU 𝒞 m r β
  exact (chowGroupCast_heq C sU _ _).symm.trans (heq_of_eq h0)

variable (V : P.Opens) (hV : AlgebraicGeometry.RelativeDimension (V.ι ≫ π) r)

/-- The summands `ξ^{s+1} ∩ π^*b` of the projective space bundle formula contribute to neither
side of `flatPullback_pushforward_chernCap_tensorDual`, granted `ξ ∩ c_r(ℰ) ∩ π^*b = 0` and
`(ξ ∩ y)|_V = 0`. -/
theorem flatPullback_pushforward_chernCap_capPow_succ
    (hrel : ∀ (m d : ℤ) (hd : m + r - r = d + 1) (β : chowGroup C sU m),
      (invCap C sP M).capOnChow C sP d (chowGroupCast C sP hd
        (GenuineChern.chernCap C r sP ℰ (m + r) (Fin.last r)
          (bundlePullback C sU sP π hsP r hπ m β))) = 0)
    (hres : ∀ (d : ℤ) (y : chowGroup C sP (d + 1)),
      chowGroupOpensRestrictOfIsOpenImmersion C sP V d ((invCap C sP M).capOnChow C sP d y) = 0)
    (k m : ℤ) (s : ℕ) (h : m + r = k + r + ((s + 1 : ℕ) : ℤ)) (b : chowGroup C sU m) :
    chowGroupCast C _ (by ring) (bundlePullback C sU (V.ι ≫ sP) (V.ι ≫ π)
      (by rw [Category.assoc, hsP]) r hV (k + r - r)
      (properChowPushforward C sP sU π hsP (k + r - r)
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ sU _ hsP _)
        (GenuineChern.chernCap C r sP ℰ (k + r) (Fin.last r)
          (capPow C sP (invCap C sP M) (s + 1) (m + r) (k + r) h
            (bundlePullback C sU sP π hsP r hπ m b))))) =
      ((-1 : ℤ) ^ r) • chowGroupOpensRestrictOfIsOpenImmersion C sP V (k + r)
          (capPow C sP (invCap C sP M) (s + 1) (m + r) (k + r) h
            (bundlePullback C sU sP π hsP r hπ m b)) := by
  have hcap : GenuineChern.chernCap C r sP ℰ (k + r) (Fin.last r)
      (capPow C sP (invCap C sP M) (s + 1) (m + r) (k + r) h
        (bundlePullback C sU sP π hsP r hπ m b)) = 0 := by
    refine chowGroup_eq_zero_of_heq_zero C (by simp only [Fin.val_last])
      ((chernCap_capPow_heq C _ _ r _ _ _ _ _ _ _).trans (heq_of_eq ?_))
    rw [capPow_succ_apply]
    refine (congrArg _ ?_).trans (map_zero _)
    exact hrel m _ (by simp only [Fin.val_last]; ring) b
  have hres' : chowGroupOpensRestrictOfIsOpenImmersion C sP V (k + r)
      (capPow C sP (invCap C sP M) (s + 1) (m + r) (k + r) h
        (bundlePullback C sU sP π hsP r hπ m b)) = 0 := by
    rw [capPow_succ_apply']
    exact hres _ _
  rw [hcap, hres', map_zero, map_zero, map_zero, smul_zero]

/-- The summand `π^*b` of the projective space bundle formula: both sides of
`flatPullback_pushforward_chernCap_tensorDual` are `(-1)^r p^*b`. -/
theorem flatPullback_pushforward_chernCap_pullback (htower : IsLocallyProjectiveTower r π M)
    (eℰ : ℰ ≅ ((Stacks.SheafOfModules.Tensor.sheafTensor P.sheaf).obj
      ((Scheme.Modules.pullback π).obj 𝒞)).obj (dualSheaf M))
    (k m : ℤ) (hm : m = k) (h : m + r = k + r) (b : chowGroup C sU m) :
    chowGroupCast C _ (by ring) (bundlePullback C sU (V.ι ≫ sP) (V.ι ≫ π)
      (by rw [Category.assoc, hsP]) r hV (k + r - r)
      (properChowPushforward C sP sU π hsP (k + r - r)
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ sU _ hsP _)
        (GenuineChern.chernCap C r sP ℰ (k + r) (Fin.last r)
          (chowGroupCast C _ h (bundlePullback C sU sP π hsP r hπ m b))))) =
      ((-1 : ℤ) ^ r) • chowGroupOpensRestrictOfIsOpenImmersion C sP V (k + r)
          (chowGroupCast C _ h (bundlePullback C sU sP π hsP r hπ m b)) := by
  subst hm
  rw [chowGroupCast_rfl, pushforward_chernCap_tensorDual_bundlePullback C sU sP π hsP r hπ M 𝒞
    ℰ htower eℰ, map_zsmul, map_zsmul,
    chowGroupOpensRestrict_bundlePullback C sU sP π hsP r hπ V hV m b]
  congr 1
  exact eq_of_heq ((chowGroupCast_heq C _ _ _).trans
    (flatPullbackChow_heq_of_degree C _ sU _ _ r _ (by ring) _ _ (chowGroupCast_heq C _ _ _)))

/-- **The cap-product identity of Stacks 0FEF along a locally projective tower.** Let
`π : P ⟶ U` be flat, proper, of relative dimension `r` and a projective tower of fibre
dimension `r` locally on `U` with twist `ℳ`, `ξ = c₁(ℳ)`, let `𝒞` be locally free of rank `r`
on `U`, `ℰ ≅ π^*𝒞 ⊗ ℳ^∨` and `V ⊆ P` an open with `p : V ⟶ U` of relative dimension `r`. If
`ξ ∩ c_r(ℰ) ∩ π^*β = 0` for every `β` and `(ξ ∩ y)|_V = 0` for every `y`, then for every
`α ∈ CH_{k+r}(P)`

  `p^*(π_*(c_r(ℰ) ∩ α)) = (-1)^r α|_V`. -/
theorem flatPullback_pushforward_chernCap_tensorDual (htower : IsLocallyProjectiveTower r π M)
    (eℰ : ℰ ≅ ((Stacks.SheafOfModules.Tensor.sheafTensor P.sheaf).obj
      ((Scheme.Modules.pullback π).obj 𝒞)).obj (dualSheaf M))
    (hrel : ∀ (m d : ℤ) (hd : m + r - r = d + 1) (β : chowGroup C sU m),
      (invCap C sP M).capOnChow C sP d (chowGroupCast C sP hd
        (GenuineChern.chernCap C r sP ℰ (m + r) (Fin.last r)
          (bundlePullback C sU sP π hsP r hπ m β))) = 0)
    (hres : ∀ (d : ℤ) (y : chowGroup C sP (d + 1)),
      chowGroupOpensRestrictOfIsOpenImmersion C sP V d ((invCap C sP M).capOnChow C sP d y) = 0)
    (k : ℤ) (α : chowGroup C sP (k + r)) :
    chowGroupCast C _ (by ring) (bundlePullback C sU (V.ι ≫ sP) (V.ι ≫ π)
      (by rw [Category.assoc, hsP]) r hV (k + r - r)
      (properChowPushforward C sP sU π hsP (k + r - r)
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ sU _ hsP _)
        (GenuineChern.chernCap C r sP ℰ (k + r) (Fin.last r) α))) =
      ((-1 : ℤ) ^ r) • chowGroupOpensRestrictOfIsOpenImmersion C sP V (k + r) α := by
  obtain ⟨β, rfl⟩ := htower.bundleMap_surjective C (affineBundleSurjectivity C) sU sP hsP hπ k α
  rw [bundleMap_apply]
  simp only [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  induction i using Fin.cases with
  | zero =>
    exact flatPullback_pushforward_chernCap_pullback C sU sP π hsP r hπ M 𝒞 ℰ V hV htower eℰ k _
      (by simp only [Fin.val_zero, Nat.cast_zero, add_zero])
      (by simp only [Fin.val_zero, Nat.cast_zero, add_zero]) (β 0)
  | succ j =>
    exact flatPullback_pushforward_chernCap_capPow_succ C sU sP π hsP r hπ M ℰ V hV hrel hres k _ j
      (by simp only [Fin.val_succ]; push_cast; ring) _

/-! ### The relation of Stacks 02U6 for `𝒞 ⊕ 𝒪` on the tower -/

/-- The `j`-th Chern class of `𝒞 ⊕ 𝒪_U` is that of `𝒞` for `j ≤ r`, and the top one vanishes
(Stacks 02UG for the sequence `0 ⟶ 𝒪_U ⟶ 𝒞 ⊕ 𝒪_U ⟶ 𝒞 ⟶ 0`). -/
theorem chernCap_completionModule (k : ℤ) :
    (∀ α : chowGroup C sU k,
        GenuineChern.chernCap C (r + 1) sU (completionModule 𝒞) k (Fin.last (r + 1)) α = 0) ∧
      ∀ (j : Fin (r + 1)) (α : chowGroup C sU k),
        GenuineChern.chernCap C (r + 1) sU (completionModule 𝒞) k j.castSucc α =
          GenuineChern.chernCap C r sU 𝒞 k j α := by
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (completionSequence 𝒞).X₂ (r + 1) := isFiniteLocallyFreeOfRank_completionModule 𝒞 r
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (completionSequence 𝒞).X₃ r := ‹_›
  have h := GenuineChern.chernCap_eq_of_shortExact_of_iso_unit C sU (completionSequence 𝒞)
    (shortExact_completionSequence 𝒞) (Iso.refl _) r
  exact ⟨fun α ↦ h.1 k α, fun j α ↦ h.2 k j α⟩

omit [IsProper π] in
/-- The summand `ξ^{j+1} ∩ π^*(c_{r-j}(𝒞) ∩ β)` of `ξ ∩ c_r(π^*𝒞 ⊗ ℳ^∨) ∩ π^*β`, read in degree
`d`, with `ξ = c₁(ℳ)`. -/
abbrev tensorDualCapTerm (m d : ℤ) (hd : m + r - r = d + 1) (β : chowGroup C sU m)
    (j : Fin (r + 1)) : chowGroup C sP d :=
  capPow C sP (invCap C sP M) (j + 1) (m - ((r - j : ℕ) : ℤ) + r) d
    (by have := j.isLt; push_cast; omega)
    (bundlePullback C sU sP π hsP r hπ (m - ((r - j : ℕ) : ℤ))
      (GenuineChern.chernCap C r sU 𝒞 m ⟨r - j, by omega⟩ β))

omit [IsProper π] in
/-- `ξ ∩ c_r(π^*𝒞 ⊗ ℳ^∨) ∩ π^*β = ∑_j (-1)^j ξ^{j+1} ∩ π^*(c_{r-j}(𝒞) ∩ β)`, by the expansion
`Stacks.Chow.chernCap_tensorDual_bundlePullback`. -/
theorem capOnChow_chernCap_tensorDual_eq_sum
    (eℰ : ℰ ≅ ((Stacks.SheafOfModules.Tensor.sheafTensor P.sheaf).obj
      ((Scheme.Modules.pullback π).obj 𝒞)).obj (dualSheaf M))
    (m d : ℤ) (hd : m + r - r = d + 1) (β : chowGroup C sU m) :
    (invCap C sP M).capOnChow C sP d (chowGroupCast C sP hd
      (GenuineChern.chernCap C r sP ℰ (m + r) (Fin.last r)
        (bundlePullback C sU sP π hsP r hπ m β))) =
      ∑ j : Fin (r + 1), ((-1 : ℤ) ^ (j : ℕ)) •
        tensorDualCapTerm C sU sP π hsP r hπ M 𝒞 m d hd β j := by
  rw [chernCap_tensorDual_bundlePullback C sU sP π hsP r hπ M 𝒞 ℰ eℰ, map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [map_zsmul, map_zsmul]
  congr 1
  rw [chowGroupCast_capPow, ← capPow_succ_apply']

omit [IsProper π] in
/-- A summand of the relation of Stacks 02U6 for a module of rank `r + 1` on the tower is a power
of `ξ` applied to a pulled-back class. -/
theorem chowGroupCast_projectiveBundleChernTerm (m d : ℤ)
    (he : m + ((r + 1 - 1 : ℕ) : ℤ) - ((r + 1 : ℕ) : ℤ) = d) (i : ℕ) (hi : i ≤ r + 1)
    (y : chowGroup C sU (m - ((r + 1 - i : ℕ) : ℤ))) :
    chowGroupCast C sP he (projectiveBundleChernTerm C sU sP π hsP (r + 1) hπ
      (fun k ↦ flatPullbackFactorsThroughRationalEquivalence_general C sP sU π hsP _ _ k)
      (invCap C sP M) m i hi y) =
    capPow C sP (invCap C sP M) i (m - ((r + 1 - i : ℕ) : ℤ) + r) d
      (by push_cast at he ⊢; omega) (bundlePullback C sU sP π hsP r hπ _ y) := by
  refine eq_of_heq ((chowGroupCast_heq C _ _ _).trans ?_)
  simp only [projectiveBundleChernTerm, AddMonoidHom.comp_apply]
  refine (heq_of_eq (capPow_eq_iteratedChernCapOnChow C _ _ i _ _).symm).trans ?_
  refine GenuineChern.capPow_heq C _ _ _ _ rfl (by simp only [List.length_replicate]; omega)
    he ?_
  refine (chowGroupCast_heq C _ _ _).trans ?_
  exact flatPullbackChow_heq_congr C _ sU _ _ hsP hsP rfl (by omega) _ _ rfl _ _ _ _ HEq.rfl

/-- The members of the family of Stacks 02U6 of `𝒞 ⊕ 𝒪` at equal indices. -/
theorem bundleChernCapFamily_heq_of_eq (k : ℤ) (β : chowGroup C sU k)
    {i i' : Fin (r + 1 + 1)} (h : i = i') :
    bundleChernCapFamily (completionModule 𝒞) r C sU k β i ≍
      bundleChernCapFamily (completionModule 𝒞) r C sU k β i' := by
  subst h; rfl

omit [IsProper π] in
/-- The summand of index `j + 1` of the relation of Stacks 02U6 for `𝒞 ⊕ 𝒪_U` on the tower is
`ξ^{j+1} ∩ π^*(c_{r-j}(𝒞) ∩ β)`. -/
theorem capPow_bundleChernCapFamily_succ (m d : ℤ) (hd : m + r - r = d + 1)
    (β : chowGroup C sU m) (j : Fin (r + 1)) :
    capPow C sP (invCap C sP M) ((j.succ : Fin (r + 1 + 1)) : ℕ)
      (m - ((r + 1 - (j.succ : Fin (r + 1 + 1)) : ℕ) : ℤ) + r) d (by
        have := j.isLt; simp only [Fin.val_succ]; push_cast at hd ⊢; omega)
      (bundlePullback C sU sP π hsP r hπ _ (bundleChernCapFamily (completionModule 𝒞) r C sU m β
        ⟨r + 1 - (j.succ : Fin (r + 1 + 1)), by omega⟩)) =
    tensorDualCapTerm C sU sP π hsP r hπ M 𝒞 m d hd β j := by
  refine eq_of_heq (GenuineChern.capPow_heq C _ _ _ _ (by simp) (by
    simp only [Fin.val_succ]; omega) rfl ?_)
  refine flatPullbackChow_heq_congr C _ sU _ _ hsP hsP rfl rfl _ _
    (by simp only [Fin.val_succ]; omega) _ _ _ _ ?_
  refine (bundleChernCapFamily_heq_of_eq C sU r 𝒞 m β
    (i' := (⟨r - j, by omega⟩ : Fin (r + 1)).castSucc)
    (Fin.ext (by simp only [Fin.val_succ, Fin.val_castSucc]; omega))).trans ?_
  show GenuineChern.chernCap C (r + 1) sU (completionModule 𝒞) m _ β ≍ _
  rw [(chernCap_completionModule C sU r 𝒞 m).2]

/-- The summand of index `0` of the relation of Stacks 02U6 for `𝒞 ⊕ 𝒪_U` vanishes, the top Chern
class of `𝒞 ⊕ 𝒪_U` being zero. -/
theorem bundleChernCapFamily_completionModule_zero (m : ℤ) (β : chowGroup C sU m) :
    bundleChernCapFamily (completionModule 𝒞) r C sU m β ⟨r + 1 - (0 : Fin (r + 1 + 1)),
      by simp⟩ = 0 := by
  refine eq_of_heq ((bundleChernCapFamily_heq_of_eq C sU r 𝒞 m β
    (i' := Fin.last (r + 1)) (Fin.ext (by simp))).trans ?_)
  show GenuineChern.chernCap C (r + 1) sU (completionModule 𝒞) m (Fin.last (r + 1)) β ≍ _
  rw [(chernCap_completionModule C sU r 𝒞 m).1 β]
  exact (chowGroupCast_heq C sU (by simp) (0 : chowGroup C sU _)).symm.trans
    (heq_of_eq (map_zero _))

omit [IsProper π] in
/-- **`ξ ∩ c_r(π^*𝒞 ⊗ ℳ^∨) ∩ π^*β = 0` from the relation of Stacks 02U6 for `𝒞 ⊕ 𝒪_U`.** If the
family `(c_j(𝒞 ⊕ 𝒪_U) ∩ β)_j` satisfies the relation of Stacks 02U6 on `P` for `ξ = c₁(ℳ)` — as it
does on the projective completion, and on every base change of it — then `ξ` kills
`c_r(ℰ) ∩ π^*β`: the Chern classes of `𝒞 ⊕ 𝒪_U` are those of `𝒞` with a vanishing top one
(Stacks 02UG), so the relation is `-ξ ∩ c_r(ℰ) ∩ π^*β = 0` by Stacks 02UD. -/
theorem capOnChow_chernCap_tensorDual_bundlePullback_of_relation
    (eℰ : ℰ ≅ ((Stacks.SheafOfModules.Tensor.sheafTensor P.sheaf).obj
      ((Scheme.Modules.pullback π).obj 𝒞)).obj (dualSheaf M))
    (m d : ℤ) (hd : m + r - r = d + 1) (β : chowGroup C sU m)
    (hrel : ProjectiveBundleChernRelation C sU sP π hsP (r + 1) hπ
      (fun k ↦ flatPullbackFactorsThroughRationalEquivalence_general C sP sU π hsP _ _ k)
      (invCap C sP M) m (bundleChernCapFamily (completionModule 𝒞) r C sU m β)) :
    (invCap C sP M).capOnChow C sP d (chowGroupCast C sP hd
      (GenuineChern.chernCap C r sP ℰ (m + r) (Fin.last r)
        (bundlePullback C sU sP π hsP r hπ m β))) = 0 := by
  have he : m + ((r + 1 - 1 : ℕ) : ℤ) - ((r + 1 : ℕ) : ℤ) = d := by push_cast at hd ⊢; omega
  set c := bundleChernCapFamily (completionModule 𝒞) r C sU m β with hc
  set T := fun (i : Fin (r + 1 + 1)) ↦ projectiveBundleChernTerm C sU sP π hsP (r + 1) hπ
    (fun k ↦ flatPullbackFactorsThroughRationalEquivalence_general C sP sU π hsP _ _ k)
    (invCap C sP M) m i.val (Nat.lt_succ_iff.mp i.isLt) with hT
  have hrel' : ∑ i : Fin (r + 1 + 1), (-1 : ℤ) ^ i.val • T i (c ⟨r + 1 - i.val, by omega⟩) = 0 :=
    hrel
  have hsucc : ∀ j : Fin (r + 1),
      chowGroupCast C _ he (T j.succ (c ⟨r + 1 - (j.succ : Fin (r + 1 + 1)).val, by omega⟩)) =
        tensorDualCapTerm C sU sP π hsP r hπ M 𝒞 m d hd β j := fun j ↦
    (chowGroupCast_projectiveBundleChernTerm C sU sP π hsP r hπ M m d he _ _ _).trans
      (capPow_bundleChernCapFamily_succ C sU sP π hsP r hπ M 𝒞 m d hd β j)
  have h0 : c ⟨r + 1 - (0 : Fin (r + 1 + 1)).val, by omega⟩ = 0 :=
    bundleChernCapFamily_completionModule_zero C sU r 𝒞 m β
  have key : ∑ j : Fin (r + 1), ((-1 : ℤ) ^ (j : ℕ)) •
        tensorDualCapTerm C sU sP π hsP r hπ M 𝒞 m d hd β j =
      -chowGroupCast C _ he
        (∑ i : Fin (r + 1 + 1), (-1 : ℤ) ^ i.val • T i (c ⟨r + 1 - i.val, by omega⟩)) := by
    rw [map_sum]
    conv_rhs => rw [Fin.sum_univ_succ, h0, map_zero, smul_zero, map_zero, zero_add]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_zsmul, hsucc j, Fin.val_succ, pow_succ, mul_neg_one, neg_smul, neg_neg]
  rw [capOnChow_chernCap_tensorDual_eq_sum C sU sP π hsP r hπ M 𝒞 ℰ eℰ, key, hrel', map_zero,
    neg_zero]

end Tower

/-! ### The first Chern class of a module with a section, away from its zero scheme -/

/-- **`c₁(ℳ) ∩ -` restricts to zero away from the zero scheme of a section**: if `s` is a section
of the invertible module `ℳ` whose zero scheme `Z(s)` is the complement of the open `V`, then
`(c₁(ℳ) ∩ y)|_V = 0`, because `c₁(ℳ) ∩ y` is pushed forward from `Z(s)` (Stacks 02T9) and
classes supported on the complement of `V` restrict to zero on `V` (Stacks 02RX). -/
theorem restrict_capOnChow_eq_zero_of_range_zeroScheme (C : ChowSituation.{u}) {P : Scheme.{u}}
    (sP : P ⟶ C.S) [LocallyOfFiniteType sP] (M : P.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property M]
    (s : Γ(M, ⊤)) (V : P.Opens)
    (hV : Set.range (Stacks.Divisors.zeroScheme P M s).subschemeι.base = (Set.range V.ι.base)ᶜ)
    (d : ℤ) (y : chowGroup C sP (d + 1)) :
    chowGroupOpensRestrictOfIsOpenImmersion C sP V d ((invCap C sP M).capOnChow C sP d y) = 0 := by
  obtain ⟨α, rfl⟩ := QuotientAddGroup.mk'_surjective _ y
  rw [invCap_capOnChow_mk, ← properChowPushforward_gysinHomomorphismOfInvertible C sP d M s α]
  exact (exact_chowPushforward_chowGroupOpensRestrict C sP
    ((Stacks.Divisors.zeroScheme P M s).subschemeι ≫ sP)
    (Stacks.Divisors.zeroScheme P M s).subschemeι rfl V hV d _).mpr ⟨_, rfl⟩

/-! ### The projective completion -/

section Completion

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (𝒞 : X.Modules) (r : ℕ) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒞 r]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} 𝒞]
  [Flat (projectiveCompletionProj 𝒞)] [LocallyOfFiniteType (projectiveCompletionProj 𝒞)]

omit [Flat (projectiveCompletionProj 𝒞)] in
/-- The projection of the projective completion of a module of rank `r` has relative
dimension `r`. -/
theorem relativeDimension_projectiveCompletionProj' :
    AlgebraicGeometry.RelativeDimension (projectiveCompletionProj 𝒞) r :=
  relativeDimension_projectiveCompletionProj 𝒞 r

/-- The module `π^*𝒞 ⊗ 𝒪_E(-1)` has rank `r`. -/
instance isFiniteLocallyFreeOfRank_koszulModule :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (koszulModule 𝒞) r :=
  haveI := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank 𝒞 r (projectiveCompletionProj 𝒞)
  GenuineChern.isFiniteLocallyFreeOfRank_sheafTensor _ r _

/-- The first Chern class cap operator `ξ = c₁(𝒪_E(1)) ∩ -` on the projective completion. -/
abbrev completionTwistCap : ChernCapOperator C (projectiveCompletionProj 𝒞 ≫ sX) :=
  invCap C (projectiveCompletionProj 𝒞 ≫ sX) (bundleTwist (completionModule 𝒞))

/-- The flat pullback `π^* : CH_m(X) ⟶ CH_{m+r}(E)` along the projective completion. -/
abbrev completionPullback (m : ℤ) :
    chowGroup C sX m →+ chowGroup C (projectiveCompletionProj 𝒞 ≫ sX) (m + r) :=
  bundlePullback C sX (projectiveCompletionProj 𝒞 ≫ sX) (projectiveCompletionProj 𝒞) rfl r
    (relativeDimension_projectiveCompletionProj' 𝒞 r) m

/-- **The expansion of `c_r(π^*𝒞 ⊗ 𝒪(-1)) ∩ π^*β`** (Stacks 02UD):

  `c_r(ℰ) ∩ π^*β = ∑_j (-1)^j ξ^j ∩ π^*(c_{r-j}(𝒞) ∩ β)`. -/
theorem chernCap_koszulModule_bundlePullback (m : ℤ) (β : chowGroup C sX m) :
    GenuineChern.chernCap C r (projectiveCompletionProj 𝒞 ≫ sX) (koszulModule 𝒞) (m + r)
        (Fin.last r) (completionPullback C sX 𝒞 r m β) =
      ∑ j : Fin (r + 1), ((-1 : ℤ) ^ (j : ℕ)) •
        capPow C (projectiveCompletionProj 𝒞 ≫ sX) (completionTwistCap C sX 𝒞) j
          (m - ((r - j : ℕ) : ℤ) + r) (m + r - r) (by have := j.isLt; omega)
          (completionPullback C sX 𝒞 r (m - ((r - j : ℕ) : ℤ))
            (GenuineChern.chernCap C r sX 𝒞 m ⟨r - j, by omega⟩ β)) :=
  chernCap_tensorDual_bundlePullback C sX _ _ rfl r _ _ 𝒞 _ (Iso.refl _) m β

omit [Flat (projectiveCompletionProj 𝒞)] [LocallyOfFiniteType (projectiveCompletionProj 𝒞)] in
/-- The cap operator of the twist in the relation of Stacks 02U6 is `ξ`. -/
theorem bundleTwistCap_completionModule :
    bundleTwistCap (completionModule 𝒞) C sX = completionTwistCap C sX 𝒞 :=
  rfl

/-- **The top Chern class of `π^*𝒞 ⊗ 𝒪(-1)` is killed by `ξ` on pulled-back classes**:
`ξ ∩ c_r(ℰ) ∩ π^*β = 0`. This is the relation of Stacks 02U6 for `𝒞 ⊕ 𝒪_X` on `E`, whose
Chern classes are those of `𝒞` (Stacks 02UG). -/
theorem capOnChow_chernCap_koszulModule_bundlePullback (m d : ℤ) (hd : m + r - r = d + 1)
    (β : chowGroup C sX m) :
    (completionTwistCap C sX 𝒞).capOnChow C _ d (chowGroupCast C _ hd
      (GenuineChern.chernCap C r (projectiveCompletionProj 𝒞 ≫ sX) (koszulModule 𝒞) (m + r)
        (Fin.last r) (completionPullback C sX 𝒞 r m β))) = 0 :=
  capOnChow_chernCap_tensorDual_bundlePullback_of_relation C sX _ _ rfl r
    (relativeDimension_projectiveCompletionProj' 𝒞 r) _ 𝒞 _ (Iso.refl _) m d hd β
    (isChernCapFamily_bundleChernCapFamily (completionModule 𝒞) r C sX m β).2

omit [Flat (projectiveCompletionProj 𝒞)] [LocallyOfFiniteType (projectiveCompletionProj 𝒞)] in
/-- **The divisor at infinity is the complement of `V`**. -/
theorem range_infinityDivisor_eq_compl :
    Set.range (Stacks.ProjectiveCompletion.infinityDivisor 𝒞).subschemeι.base =
      (Set.range (complementOpen 𝒞).ι.base)ᶜ := by
  have hsurj : Function.Surjective
      (Stacks.ProjectiveCompletion.infinityDivisorIso 𝒞).inv.base := fun x ↦
    ⟨(Stacks.ProjectiveCompletion.infinityDivisorIso 𝒞).hom.base x, by
      rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]
      rfl⟩
  rw [← infinityDivisorIso_inv_infinityEmbedding 𝒞, Scheme.Hom.comp_base, TopCat.coe_comp,
    Set.range_comp, hsurj.range_eq, Set.image_univ]
  exact range_infinityEmbedding 𝒞

omit [Flat (projectiveCompletionProj 𝒞)] [LocallyOfFiniteType (projectiveCompletionProj 𝒞)] in
/-- **The first Chern class of the twist restricts to zero on `V`**: `(ξ ∩ y)|_V = 0`, because
`ξ ∩ y` is pushed forward from the divisor at infinity (Stacks 02T9), the complement of `V`
(Stacks 02RX). -/
theorem restrict_complementOpen_capOnChow (d : ℤ)
    (y : chowGroup C (projectiveCompletionProj 𝒞 ≫ sX) (d + 1)) :
    chowGroupOpensRestrictOfIsOpenImmersion C (projectiveCompletionProj 𝒞 ≫ sX) (complementOpen 𝒞)
      d ((completionTwistCap C sX 𝒞).capOnChow C _ d y) = 0 :=
  restrict_capOnChow_eq_zero_of_range_zeroScheme C (projectiveCompletionProj 𝒞 ≫ sX)
    (bundleTwist (completionModule 𝒞)) (infinityTwistSection 𝒞) (complementOpen 𝒞)
    (range_infinityDivisor_eq_compl 𝒞) d y

omit [Flat (projectiveCompletionProj 𝒞)] in
/-- The projection `p : V ⟶ X` of the complement of the divisor at infinity has relative
dimension `r`. -/
theorem relativeDimension_complementOpen_ι_comp :
    AlgebraicGeometry.RelativeDimension ((complementOpen 𝒞).ι ≫ projectiveCompletionProj 𝒞) r :=
  relativeDimension_of_isAffineSpaceBundle _ r (isAffineSpaceBundle_complementOpen 𝒞 r)

/-- The flat pullback `p^* : CH_m(X) ⟶ CH_{m+r}(V)` along `p : V ⟶ X`. -/
abbrev complementPullback (m : ℤ) :
    chowGroup C sX m →+ chowGroup C ((complementOpen 𝒞).ι ≫ projectiveCompletionProj 𝒞 ≫ sX)
      (m + r) :=
  bundlePullback C sX ((complementOpen 𝒞).ι ≫ projectiveCompletionProj 𝒞 ≫ sX)
    ((complementOpen 𝒞).ι ≫ projectiveCompletionProj 𝒞) (by rw [Category.assoc]) r
    (relativeDimension_complementOpen_ι_comp 𝒞 r) m

/-- The restriction of `π^*β` to `V` is `p^*β`. -/
theorem restrict_completionPullback (m : ℤ) (β : chowGroup C sX m) :
    chowGroupOpensRestrictOfIsOpenImmersion C (projectiveCompletionProj 𝒞 ≫ sX)
        (complementOpen 𝒞) (m + r) (completionPullback C sX 𝒞 r m β) =
      complementPullback C sX 𝒞 r m β := by
  exact chowGroupOpensRestrict_bundlePullback C sX _ _ rfl r _ (complementOpen 𝒞) _ m β

/-- **The cap-product identity of Stacks 0FEF, before the Koszul resolution.** For every
`α ∈ CH_{k+r}(E)`,

  `p^*(π_*(c_r(π^*𝒞 ⊗ 𝒪(-1)) ∩ α)) = (-1)^r α|_V`

in `CH_{k+r}(V)`, `V ⊆ E` being the complement of the divisor at infinity and `p : V ⟶ X` its
projection. -/
theorem flatPullback_pushforward_chernCap_koszulModule (k : ℤ)
    (α : chowGroup C (projectiveCompletionProj 𝒞 ≫ sX) (k + r)) :
    chowGroupCast C _ (by ring) (complementPullback C sX 𝒞 r (k + r - r)
      (properChowPushforward C (projectiveCompletionProj 𝒞 ≫ sX) sX (projectiveCompletionProj 𝒞)
        rfl (k + r - r)
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ sX _ rfl _)
        (GenuineChern.chernCap C r (projectiveCompletionProj 𝒞 ≫ sX) (koszulModule 𝒞) (k + r)
          (Fin.last r) α))) =
      ((-1 : ℤ) ^ r) • chowGroupOpensRestrictOfIsOpenImmersion C
        (projectiveCompletionProj 𝒞 ≫ sX) (complementOpen 𝒞) (k + r) α :=
  flatPullback_pushforward_chernCap_tensorDual C sX _ _ rfl r
    (relativeDimension_projectiveCompletionProj' 𝒞 r) _ 𝒞 _ (complementOpen 𝒞)
    (relativeDimension_complementOpen_ι_comp 𝒞 r)
    (isLocallyProjectiveTower_bundle (completionModule 𝒞) r) (Iso.refl _)
    (capOnChow_chernCap_koszulModule_bundlePullback C sX 𝒞 r)
    (restrict_complementOpen_capOnChow C sX 𝒞) k α

end Completion

end Stacks.Chow

end
