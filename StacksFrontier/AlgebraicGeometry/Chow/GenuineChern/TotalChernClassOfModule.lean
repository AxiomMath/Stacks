module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FirstChernClassCanonical
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.TotalChernClassOfModule
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.BivariantChernClass

/-!
# The Chern classes and the total Chern class of a finite locally free module, unconditionally

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be a scheme
locally of finite type over `S` and let `ℰ` be a finite locally free `𝒪_X`-module of rank `r`.
[Stacks, Tag 0FE1] defines

* for `0 ≤ i ≤ r`, the *`i`-th Chern class* `c_i(ℰ) ∈ A^i(X)`, the bivariant class of degree `i`
  constructed in [Stacks, Tag 0B7H]: the rule assigning to `f : X' ⟶ X` the operation
  `c_i(f^*ℰ) ∩ - : A_k(X') ⟶ A_{k-i}(X')`;
* the *total Chern class* `c(ℰ) = c_0(ℰ) + c_1(ℰ) + ⋯ + c_r(ℰ)`, viewed as a nonhomogeneous
  bivariant class on `X`.

This file states both with nothing supplied from outside: the bivariant group is
`Stacks.Chow.CanonicalBivariantClass`, the group `A^i(X ⟶ X)` of Stacks 0B76 at the canonical
Gysin system `Stacks.Chow.canonicalGysinSystem` (the first Chern class rule of an invertible
module, with the vanishing of Stacks 02TO proved), and the operations are the Chern class cap
products `Stacks.Chow.GenuineChern.chernCap` of Stacks 02U6, read off the projective space bundle
formula. The naturality facts that the proof of Stacks 0B7H cites are the theorems
`Stacks.Chow.GenuineChern.chernCap_properNaturality` (Stacks 02U9),
`Stacks.Chow.GenuineChern.chernCap_flatNaturality` (Stacks 02U8),
`Stacks.Chow.GenuineChern.chernCap_gysinNaturality` (Stacks 0B7G) and
`Stacks.Chow.GenuineChern.gysinSystemOfInvertible_isNaturalUnderInverseIso` (the isomorphism case
of Stacks 02TA, read at the canonical system as
`Stacks.Chow.canonicalGysinSystem_isNaturalUnderInverseIso`), the same four that build
`Stacks.Chow.GenuineChern.chernClass`; here they are discharged, not carried.

## Main definitions

* `Stacks.Chow.canonicalChernClass` — **Stacks 0FE1**, the `i`-th Chern class
  `c_i(ℰ) ∈ A^i(X)`, for `0 ≤ i ≤ r`.
* `Stacks.Chow.canonicalTotalChernClass` — **Stacks 0FE1**, the total Chern class
  `c(ℰ) = c_0(ℰ) + ⋯ + c_r(ℰ)` as an element of `A^*(X ⟶ X) = ⊕_p A^p(X ⟶ X)`.

## Main results

* `Stacks.Chow.isChernClassBivariant_canonicalChernClass` — the characterization of Stacks 0B7H:
  on every test scheme `g : T ⟶ X`, `c_i(ℰ)` caps by `c_i(g^*ℰ) ∩ -`; and
  `Stacks.Chow.eq_canonicalChernClass` — it is the only class of degree `i` that does.
* `Stacks.Chow.canonicalTotalChernClass_apply_coe`,
  `Stacks.Chow.canonicalTotalChernClass_apply_eq_zero` — the components of `c(ℰ)`.
* `Stacks.Chow.isTotalChernClass_canonicalTotalChernClass`,
  `Stacks.Chow.eq_canonicalTotalChernClass` — `c(ℰ)` is the unique total Chern class of `ℰ`.

## Implementation notes

The two definitions are the values of `Stacks.Chow.chernClass` and `Stacks.Chow.totalChernClass`
of `StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.TotalChernClassOfModule` at the canonical
Gysin system and the genuine cap products, with every hypothesis of those declarations proved. So
the lemmas proved there about the conditional forms specialize here without a new argument. The
naturality theorems are stated for `Stacks.Chow.gysinSystemOfInvertible`, which is
`Stacks.Chow.canonicalGysinSystem` by
`Stacks.Chow.gysinSystemOfInvertible_eq_canonicalGysinSystem`.

## References

* [Stacks Project, Tag 0FE1](https://stacks.math.columbia.edu/tag/0FE1)
* [Stacks Project, Tag 0B7H](https://stacks.math.columbia.edu/tag/0B7H)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 02U6](https://stacks.math.columbia.edu/tag/02U6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

open GenuineChern

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (F : X.Modules) (r : ℕ) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r]

/-! ### The Gysin identity of the genuine Chern class operations, at the canonical Gysin system -/

/-- The Gysin identity of Stacks 0B7G for the genuine Chern class operations, read against the
canonical Gysin system. -/
theorem chernCap_gysinNaturality_canonicalGysinSystem (i : Fin (r + 1)) :
    IdentityCapRule.GysinNaturality C sX (i : ℤ)
      (chernIdentityCapRuleOfRank C sX F r (chernCap C r) i) (canonicalGysinSystem C) := by
  rw [← gysinSystemOfInvertible_eq_canonicalGysinSystem]
  exact chernCap_gysinNaturality C sX F r i

/-! ### The `i`-th Chern class -/

/-- **Stacks 0FE1, the `i`-th Chern class.** For a module `ℰ` that is finite locally free of rank
`r` on `X` and `0 ≤ i ≤ r`, the `i`-th Chern class `c_i(ℰ) ∈ A^i(X)`: the bivariant class of
degree `i` for `𝟙 X` constructed in Stacks 0B7H, which assigns to `f : X' ⟶ X` the operation
`c_i(f^*ℰ) ∩ - : A_k(X') ⟶ A_{k-i}(X')` of Stacks 02U6. It lives in the group of Stacks 0B76 at
the canonical Gysin system, and every naturality fact the construction needs is proved. -/
@[stacks 0FE1 "c_i(E) ∈ A^i(X), the degree-i bivariant class of Stacks 0B7H, with the genuine \
cap products of Stacks 02U6 and the canonical Gysin system; nothing assumed"]
def canonicalChernClass (i : Fin (r + 1)) :
    CanonicalBivariantClass C sX sX (𝟙 X) (Category.id_comp sX) (i : ℤ) :=
  chernClass C sX F r (canonicalGysinSystem C) (chernCap C r)
    (chernCap_properNaturality C sX F r) (chernCap_flatNaturality C sX F r)
    (chernCap_gysinNaturality_canonicalGysinSystem C sX F r)
    (canonicalGysinSystem_isNaturalUnderInverseIso C) i

/-- **Stacks 0B7H.** The `i`-th Chern class of `ℰ` caps by `c_i(g^*ℰ) ∩ -` on every test scheme
`g : T ⟶ X`, once its value on the chosen pullback `X ×_X T` is pushed forward to `T`. -/
theorem isChernClassBivariant_canonicalChernClass (i : Fin (r + 1)) :
    IsChernClassBivariant C sX F r (canonicalGysinSystem C) (chernCap C r)
      (pullbackPreservesRank_of_isFiniteLocallyFreeOfRank F r) i
      (canonicalChernClass C sX F r i) :=
  isChernClassBivariant_chernClass C sX F r _ _ _ _ _ _ i

/-- The cap operation of the `i`-th Chern class on a test scheme `g : T ⟶ X`: intersection with
`c_i(g^*ℰ)`, transported to the chosen pullback `X ×_X T`. -/
theorem canonicalChernClass_cap (i : Fin (r + 1)) {T : Scheme.{u}} (g : T ⟶ X)
    [LocallyOfFiniteType g] (k : ℤ) :
    (canonicalChernClass C sX F r i).cap g k =
      chernClassBivariantCap C sX F r (chernCap C r)
        (pullbackPreservesRank_of_isFiniteLocallyFreeOfRank F r) i g k :=
  chernClass_cap C sX F r _ _ _ _ _ _ i g k

/-- The `i`-th Chern class of `ℰ` is the only bivariant class of degree `i` for `𝟙 X` satisfying
the characterization of Stacks 0B7H. -/
theorem eq_canonicalChernClass (i : Fin (r + 1))
    (c : CanonicalBivariantClass C sX sX (𝟙 X) (Category.id_comp sX) (i : ℤ))
    (hc : IsChernClassBivariant C sX F r (canonicalGysinSystem C) (chernCap C r)
      (pullbackPreservesRank_of_isFiniteLocallyFreeOfRank F r) i c) :
    c = canonicalChernClass C sX F r i :=
  eq_chernClass C sX F r _ _ _ _ _ _ i c hc

/-! ### The total Chern class -/

/-- **Stacks 0FE1, the total Chern class.** For a module `ℰ` that is finite locally free of rank
`r` on `X`, the total Chern class `c(ℰ) = c_0(ℰ) + c_1(ℰ) + ⋯ + c_r(ℰ)`: the formal sum of the
`r + 1` Chern classes of Stacks 0B7H, viewed as a nonhomogeneous bivariant class on `X`, that is,
as an element of `A^*(X ⟶ X) = ⊕_p A^p(X ⟶ X)` at the canonical Gysin system. Nothing is
assumed. -/
@[stacks 0FE1 "c(E) = c_0(E) + ... + c_r(E), the formal sum of the c_i(E) as a nonhomogeneous \
bivariant class on X, with the genuine cap products and the canonical Gysin system; nothing \
assumed"]
def canonicalTotalChernClass :
    nonhomogeneousBivariantGroup C (canonicalGysinSystem C) sX sX (𝟙 X) (Category.id_comp sX) :=
  bivariantFormalSum C (canonicalGysinSystem C) sX sX (𝟙 X) (Category.id_comp sX) r
    (canonicalChernClass C sX F r)

/-- The total Chern class is the conditional `Stacks.Chow.totalChernClass` with all its hypotheses
discharged. -/
theorem canonicalTotalChernClass_eq_totalChernClass :
    canonicalTotalChernClass C sX F r =
      totalChernClass C sX F r (canonicalGysinSystem C) (chernCap C r)
        (chernCap_properNaturality C sX F r) (chernCap_flatNaturality C sX F r)
        (chernCap_gysinNaturality_canonicalGysinSystem C sX F r)
        (canonicalGysinSystem_isNaturalUnderInverseIso C) :=
  rfl

/-- The degree-`i` component of the total Chern class is `c_i(ℰ)`, for `0 ≤ i ≤ r`. -/
theorem canonicalTotalChernClass_apply_coe (i : Fin (r + 1)) :
    canonicalTotalChernClass C sX F r (i : ℤ) = canonicalChernClass C sX F r i :=
  bivariantFormalSum_apply_coe C _ sX sX (𝟙 X) (Category.id_comp sX) r _ i

/-- The total Chern class of a module of rank `r` has no component in a degree outside
`0, …, r`. -/
theorem canonicalTotalChernClass_apply_eq_zero (p : ℤ) (hp : p < 0 ∨ (r : ℤ) < p) :
    canonicalTotalChernClass C sX F r p = 0 :=
  bivariantFormalSum_apply_eq_zero C _ sX sX (𝟙 X) (Category.id_comp sX) r _ p hp

/-- The total Chern class of `ℰ` is a total Chern class in the sense of
`Stacks.Chow.IsTotalChernClass`: its degree-`i` component satisfies the characterization of
Stacks 0B7H for `0 ≤ i ≤ r`, and it has no other component. -/
theorem isTotalChernClass_canonicalTotalChernClass :
    IsTotalChernClass C (canonicalGysinSystem C) sX r F (chernCap C r)
      (pullbackPreservesRank_of_isFiniteLocallyFreeOfRank F r)
      (canonicalTotalChernClass C sX F r) :=
  isTotalChernClass_totalChernClass C sX F r (canonicalGysinSystem C) (chernCap C r)
    (chernCap_properNaturality C sX F r) (chernCap_flatNaturality C sX F r)
    (chernCap_gysinNaturality_canonicalGysinSystem C sX F r)
    (canonicalGysinSystem_isNaturalUnderInverseIso C)

/-- **Uniqueness.** Every total Chern class of `ℰ` at the canonical Gysin system is
`Stacks.Chow.canonicalTotalChernClass`. -/
theorem eq_canonicalTotalChernClass
    {t : nonhomogeneousBivariantGroup C (canonicalGysinSystem C) sX sX (𝟙 X)
      (Category.id_comp sX)}
    (ht : IsTotalChernClass C (canonicalGysinSystem C) sX r F (chernCap C r)
      (pullbackPreservesRank_of_isFiniteLocallyFreeOfRank F r) t) :
    t = canonicalTotalChernClass C sX F r :=
  eq_totalChernClass C sX F r (canonicalGysinSystem C) (chernCap C r)
    (chernCap_properNaturality C sX F r) (chernCap_flatNaturality C sX F r)
    (chernCap_gysinNaturality_canonicalGysinSystem C sX F r)
    (canonicalGysinSystem_isNaturalUnderInverseIso C) ht

end Stacks.Chow

end
