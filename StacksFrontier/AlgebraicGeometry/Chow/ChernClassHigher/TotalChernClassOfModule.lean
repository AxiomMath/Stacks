module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.BivariantClass
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.TotalChernClass

/-!
# The Chern classes and the total Chern class of a finite locally free module

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be a scheme
locally of finite type over `S` and let `ℰ` be a finite locally free `O_X`-module of rank `r`.
**Stacks 0FE1** names two objects:

* for `0 ≤ i ≤ r`, the *`i`-th Chern class* `c_i(ℰ) ∈ A^i(X)`, which *is* the bivariant class of
  degree `i` constructed in Stacks 0B7H;
* the *total Chern class* `c(ℰ) = c_0(ℰ) + c_1(ℰ) + ⋯ + c_r(ℰ)`, the formal sum of those `r + 1`
  homogeneous classes, read as a nonhomogeneous bivariant class on `X`.

Both halves are assembled here out of pieces that already exist. The homogeneous class is
`Stacks.Chow.chernClassBivariant`, the construction of Stacks 0B7H, and the formal sum of a
family of homogeneous classes is `Stacks.Chow.bivariantFormalSum`. The point of this file is the
*instantiation*: the summands of the total Chern class are the classes Stacks 0B7H actually
constructs, not classes supplied as a parameter together with the hypothesis that they satisfy
the characterization of Stacks 0B7H. Consequently the hypothesis of
`Stacks.Chow.isTotalChernClass_bivariantFormalSum` is discharged below by
`Stacks.Chow.isChernClassBivariant_chernClassBivariant` instead of being carried.

## Main definitions

* `Stacks.Chow.chernClass` — **Stacks 0FE1**, the `i`-th Chern class `c_i(ℰ) ∈ A^i(X)` of a
  finite locally free module of rank `r`, for `0 ≤ i ≤ r`: the bivariant class of degree `i`
  constructed in Stacks 0B7H.
* `Stacks.Chow.totalChernClass` — **Stacks 0FE1**, the total Chern class
  `c(ℰ) = c_0(ℰ) + ⋯ + c_r(ℰ)` as a nonhomogeneous bivariant class on `X`, that is, as an element
  of `A^*(X ⟶ X) = ⊕_p A^p(X ⟶ X)`.

## Main results

* `Stacks.Chow.isChernClassBivariant_chernClass` — the `i`-th Chern class satisfies the
  characterization of Stacks 0B7H, and `Stacks.Chow.eq_chernClass` — it is the only bivariant
  class of degree `i` that does.
* `Stacks.Chow.totalChernClass_apply_coe`, `Stacks.Chow.totalChernClass_apply_eq_zero` — the
  components of the total Chern class: `c_i(ℰ)` in degree `i` for `0 ≤ i ≤ r`, and `0` in every
  other degree.
* `Stacks.Chow.isTotalChernClass_totalChernClass` — the class constructed here is a total Chern
  class of `ℰ` in the sense of `Stacks.Chow.IsTotalChernClass`.
* `Stacks.Chow.eq_totalChernClass` — it is the only one, so the formal sum of the classes of
  Stacks 0B7H is *the* total Chern class.
* `Stacks.Chow.totalChernClass_cap` — the cap operation of its degree-`i` component:
  intersection with `c_i(g^*ℰ)` on each test scheme, pushed forward to the chosen pullback.

## Implementation notes

### Which parameters and hypotheses are carried, and which tag each is

Exactly the ones that `Stacks.Chow.chernClassBivariant`, the library's form of Stacks 0B7H, carries;
nothing is added and nothing is weakened. They are:

* `cap : Stacks.Chow.HigherChernCapRule C r` — the Chern class operations on Chow groups. This is
  **Stacks 0B7G**, built there from the cap product on cycles of Stacks 02U5 and its invariance
  under rational equivalence, Stacks 02U7. None of the three is in this repository, so the
  operations enter as *data*.
* `hproper` — **axiom (1) of Stacks 0B76**, read on the test schemes: the projection formula of
  **Stacks 02U9** for the rule `α ↦ c_i(g^*ℰ) ∩ α`.
* `hflat` — **axiom (2) of Stacks 0B76**, read on the test schemes: the flat-pullback identity of
  **Stacks 02U8** for that rule.
* `hgysin` — **axiom (3) of Stacks 0B76**, read on the test schemes: the Gysin identity of
  **Stacks 0B7G** for that rule.
* `hiso` — the isomorphism case of **Stacks 02TA** for the Gysin system, needed to transport the
  Gysin identity from a test scheme `T` to the chosen pullback `X ×_X T`; see the implementation
  notes of `StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.BivariantClass`.

The three naturality hypotheses are stated here for every degree `0 ≤ i ≤ r` at once, since the
total Chern class involves all `r + 1` homogeneous classes simultaneously. None of them is the
conclusion of anything proved below: `hproper`, `hflat` and `hgysin` are identities satisfied by
the *cap rule on the test schemes*, a family of maps between Chow groups, whereas the conclusions
below are statements about bivariant classes on the chosen pullbacks
(`Stacks.Chow.IsChernClassBivariant`, `Stacks.Chow.IsTotalChernClass`); `hiso` is a property of
the Gysin system alone, in which neither `ℰ` nor the Chern operations occur.

### Why the formal-sum machinery lives elsewhere

`StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.TotalChernClass` constructs the graded group
`⊕_p A^p(X ⟶ Y)`, the formal sum of a family of homogeneous classes, the predicate
`Stacks.Chow.IsTotalChernClass` and the uniqueness of a class satisfying it. All of that is
general and carries no `@[stacks]` attribute: it is about an arbitrary family of classes. What
Stacks 0FE1 defines is the value of that machinery at the family of Stacks 0B7H classes, which is
what this file supplies.

## References

* [Stacks Project, Tag 0FE1](https://stacks.math.columbia.edu/tag/0FE1)
* [Stacks Project, Tag 0B7H](https://stacks.math.columbia.edu/tag/0B7H)
* [Stacks Project, Tag 0B7G](https://stacks.math.columbia.edu/tag/0B7G)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 02U8](https://stacks.math.columbia.edu/tag/02U8)
* [Stacks Project, Tag 02U9](https://stacks.math.columbia.edu/tag/02U9)
* [Stacks Project, Tag 02TA](https://stacks.math.columbia.edu/tag/02TA)
* [Stacks Project, Tag 02QL](https://stacks.math.columbia.edu/tag/02QL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (F : X.Modules) (r : ℕ) (G : GysinSystem C) (cap : HigherChernCapRule C r)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r]
  (hproper : ∀ i : Fin (r + 1), IdentityCapRule.ProperNaturality C sX (i : ℤ)
    (chernIdentityCapRuleOfRank C sX F r cap i))
  (hflat : ∀ i : Fin (r + 1), IdentityCapRule.FlatNaturality C sX (i : ℤ)
    (chernIdentityCapRuleOfRank C sX F r cap i))
  (hgysin : ∀ i : Fin (r + 1), IdentityCapRule.GysinNaturality C sX (i : ℤ)
    (chernIdentityCapRuleOfRank C sX F r cap i) G)
  (hiso : G.IsNaturalUnderInverseIso)

/-! ### The `i`-th Chern class -/

/-- **Stacks 0FE1, the `i`-th Chern class.** For `0 ≤ i ≤ r`, the `i`-th Chern class
`c_i(ℰ) ∈ A^i(X)` of a module `ℰ` that is finite locally free of rank `r`: it *is* the bivariant
class of degree `i` for `𝟙 X` constructed in Stacks 0B7H, namely the rule assigning to
`f : X' ⟶ X` the operation `c_i(f^*ℰ) ∩ - : CH_k(X') ⟶ CH_{k-i}(X')`. -/
@[stacks 0FE1 "c_i(E) is the degree-i bivariant class of Stacks 0B7H"]
def chernClass (i : Fin (r + 1)) :
    BivariantClass C G sX sX (𝟙 X) (Category.id_comp sX) (i : ℤ) :=
  chernClassBivariant C sX F r G cap i (hproper i) (hflat i) (hgysin i) hiso

/-- **Stacks 0B7H.** The `i`-th Chern class of `ℰ` satisfies the characterization of Stacks 0B7H:
on every test scheme `g : T ⟶ X` and in every degree, pushing `c_i(ℰ) ∩ α` forward along the
projection `X ×_X T ⟶ T` gives `c_i(g^*ℰ) ∩ α`. -/
theorem isChernClassBivariant_chernClass (i : Fin (r + 1)) :
    IsChernClassBivariant C sX F r G cap
      (pullbackPreservesRank_of_isFiniteLocallyFreeOfRank F r) i
      (chernClass C sX F r G cap hproper hflat hgysin hiso i) :=
  isChernClassBivariant_chernClassBivariant C sX F r G cap i (hproper i) (hflat i) (hgysin i) hiso

/-- The cap operation of the `i`-th Chern class: intersection with `c_i(g^*ℰ)` on the test scheme
`g : T ⟶ X`, transported to the chosen pullback `X ×_X T`. -/
theorem chernClass_cap (i : Fin (r + 1)) {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g]
    (k : ℤ) :
    (chernClass C sX F r G cap hproper hflat hgysin hiso i).cap g k =
      chernClassBivariantCap C sX F r cap
        (pullbackPreservesRank_of_isFiniteLocallyFreeOfRank F r) i g k :=
  chernClassBivariant_cap C sX F r G cap i (hproper i) (hflat i) (hgysin i) hiso g k

/-- The `i`-th Chern class of `ℰ` is the only bivariant class of degree `i` for `𝟙 X` satisfying
the characterization of Stacks 0B7H. -/
theorem eq_chernClass (i : Fin (r + 1))
    (c : BivariantClass C G sX sX (𝟙 X) (Category.id_comp sX) (i : ℤ))
    (hc : IsChernClassBivariant C sX F r G cap
      (pullbackPreservesRank_of_isFiniteLocallyFreeOfRank F r) i c) :
    c = chernClass C sX F r G cap hproper hflat hgysin hiso i :=
  eq_chernClassBivariant C sX F r G cap i (hproper i) (hflat i) (hgysin i) hiso c hc

/-! ### The total Chern class -/

/-- **Stacks 0FE1, the total Chern class.** The total Chern class
`c(ℰ) = c_0(ℰ) + c_1(ℰ) + ⋯ + c_r(ℰ)` of a module `ℰ` that is finite locally free of rank `r`:
the formal sum of the `r + 1` Chern classes of Stacks 0B7H, viewed as a nonhomogeneous bivariant
class on `X`, that is, as an element of `A^*(X ⟶ X) = ⊕_p A^p(X ⟶ X)`. -/
@[stacks 0FE1 "c(E) = c_0(E) + ... + c_r(E) is the formal sum of the c_i(E)"]
def totalChernClass : nonhomogeneousBivariantGroup C G sX sX (𝟙 X) (Category.id_comp sX) :=
  bivariantFormalSum C G sX sX (𝟙 X) (Category.id_comp sX) r
    (chernClass C sX F r G cap hproper hflat hgysin hiso)

/-- The degree-`i` component of the total Chern class is `c_i(ℰ)`, for `0 ≤ i ≤ r`. -/
theorem totalChernClass_apply_coe (i : Fin (r + 1)) :
    totalChernClass C sX F r G cap hproper hflat hgysin hiso (i : ℤ) =
      chernClass C sX F r G cap hproper hflat hgysin hiso i :=
  bivariantFormalSum_apply_coe C G sX sX (𝟙 X) (Category.id_comp sX) r _ i

/-- The total Chern class of a module of rank `r` has no component in a degree outside
`0, …, r`. -/
theorem totalChernClass_apply_eq_zero (p : ℤ) (hp : p < 0 ∨ (r : ℤ) < p) :
    totalChernClass C sX F r G cap hproper hflat hgysin hiso p = 0 :=
  bivariantFormalSum_apply_eq_zero C G sX sX (𝟙 X) (Category.id_comp sX) r _ p hp

/-- **Stacks 0FE1.** The formal sum of the Chern classes of Stacks 0B7H is a total Chern class of
`ℰ`: its degree-`i` component is the `i`-th bivariant Chern class for `0 ≤ i ≤ r`, and it has no
other component. The hypothesis of `Stacks.Chow.isTotalChernClass_bivariantFormalSum` is
discharged by Stacks 0B7H, not carried. -/
theorem isTotalChernClass_totalChernClass :
    IsTotalChernClass C G sX r F cap
      (pullbackPreservesRank_of_isFiniteLocallyFreeOfRank F r)
      (totalChernClass C sX F r G cap hproper hflat hgysin hiso) :=
  isTotalChernClass_bivariantFormalSum C G sX r F cap
    (pullbackPreservesRank_of_isFiniteLocallyFreeOfRank F r) _
    (isChernClassBivariant_chernClass C sX F r G cap hproper hflat hgysin hiso)

/-- **Uniqueness.** A nonhomogeneous bivariant class on `X` that is a total Chern class of `ℰ` is
the class constructed above, so the formal sum of the Chern classes of Stacks 0B7H is *the* total
Chern class of `ℰ`. -/
theorem eq_totalChernClass
    {t : nonhomogeneousBivariantGroup C G sX sX (𝟙 X) (Category.id_comp sX)}
    (ht : IsTotalChernClass C G sX r F cap
      (pullbackPreservesRank_of_isFiniteLocallyFreeOfRank F r) t) :
    t = totalChernClass C sX F r G cap hproper hflat hgysin hiso :=
  eq_of_isTotalChernClass C G sX r F cap
    (pullbackPreservesRank_of_isFiniteLocallyFreeOfRank F r) ht
    (isTotalChernClass_totalChernClass C sX F r G cap hproper hflat hgysin hiso)

/-- The cap operation of the degree-`i` component of the total Chern class: intersection with
`c_i(g^*ℰ)` on the test scheme `g : T ⟶ X`, transported to the chosen pullback `X ×_X T`. -/
theorem totalChernClass_cap (i : Fin (r + 1)) {T : Scheme.{u}} (g : T ⟶ X)
    [LocallyOfFiniteType g] (k : ℤ) :
    (totalChernClass C sX F r G cap hproper hflat hgysin hiso (i : ℤ)).cap g k =
      chernClassBivariantCap C sX F r cap
        (pullbackPreservesRank_of_isFiniteLocallyFreeOfRank F r) i g k :=
  IsTotalChernClass.cap_eq C G sX r F
    (isTotalChernClass_totalChernClass C sX F r G cap hproper hflat hgysin hiso) i g k

end Stacks.Chow

end
