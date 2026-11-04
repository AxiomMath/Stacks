module

public import StacksFrontier.AlgebraicGeometry.InvertibleClasses.Basic
public import StacksFrontier.AlgebraicGeometry.Perfect.VectorBundleKGroup
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.SplittingPrinciple

/-!
# The total Chern class of a Weil cohomology theory

In the standing situation of Stacks Section 45.12, Tag 0FI5 asserts that there is a unique rule
assigning to every object `X` of `𝒞` a total Chern class
`c^A : K₀(Vect(X)) ⟶ ∏_{i ≥ 0} A^i(X)` which is multiplicative on sums, compatible with
pullback, and sends an invertible module `ℒ` to `1 + c₁^A(ℒ)`. This file writes that rule's three
properties down, proves the uniqueness half, and constructs the Chern classes of a single finite
locally free module of positive constant rank from the projective bundle formula.

## Main definitions

* `Stacks.WeilCohomology.IsTotalChernClass`: the three properties of Tag 0FI5 — multiplicativity
  on sums, compatibility with pullback, and the value on an invertible module — together with the
  requirement that the `n`-th component lie in `A^n(X)`.
* `Stacks.WeilCohomology.ChernSetup.chernTuple`: the tuple of classes the projective bundle
  formula produces, the preimage of `-(-1)^{r+1} c₁^A(𝒪_P(1))^{r+1}` under its bijection.
* `Stacks.WeilCohomology.ChernSetup.chernClass`: **the Chern classes `c_j^A(ℰ)`** of a finite
  locally free module of constant rank `r + 1`.

## Main results

* `Stacks.WeilCohomology.HasInvertibleFiltration.exists_classOf_eq_sum`: a module with a
  filtration whose successive quotients are invertible is finite locally free, and its class in
  `K₀(Vect(X))` is the sum of the classes of those quotients.
* `Stacks.WeilCohomology.ChernSetup.chernClass_zero`: `c_0^A(ℰ) = 1`.
* `Stacks.WeilCohomology.ChernSetup.sum_chernClass_eq_zero`: **equation 45.12.1.1**,
  `∑_{i=0}^{r+1} (-1)^i c₁^A(𝒪_P(1))^i ∪ p^* c^A_{r+1-i}(ℰ) = 0`, the relation that defines the
  Chern classes.
* `Stacks.WeilCohomology.eq_of_isTotalChernClass`: **the uniqueness half of Tag 0FI5.** Two rules
  with the three properties agree on the class of every finite locally free module of constant
  rank.

## The uniqueness argument

The source reduces to constant rank by condition (2), then inducts on the rank. Here the splitting
principle of Tag 0FI7 does the induction once and for all: for a module `ℰ` of constant rank `r`
it produces `p : P ⟶ X` with `p^*` injective on `A` and a filtration of `p^*ℰ` of length `r` with
invertible successive quotients. In `K₀(Vect(P))` the filtration gives
`[p^*ℰ] = ∑_j [ℒ_j]`, so property (1) writes `c^A([p^*ℰ])` as a convolution of the
`c^A([ℒ_j])`, each of which property (3) pins down. Property (2) identifies that with
`p^*c^A([ℰ])`, and injectivity of `p^*` finishes.

## What is covered of Tag 0FI5, and what is not

Covered: the uniqueness half, for the class of a finite locally free module of constant rank; and
the construction of the individual Chern classes of such a module, with a real body — they are
the components of the preimage of an explicit element under the bijection of condition (4), and
nothing is chosen out of an existence statement.

Not covered: the existence half of the rule on all of `K₀(Vect(X))`. Extending the classes of a
single module to a rule on `K₀` requires multiplicativity in short exact sequences, which the
source deduces from condition (5) and the geometry of the closed immersion `𝐏(𝓕) ⟶ 𝐏(ℰ)` as an
effective Cartier divisor; condition (5) and clause (3)(c) are not part of
`Stacks.WeilCohomology.ChernSetup` and that geometry has no form in this repository.

Two further departures, both recorded in the attribute strings:

* **Constant rank.** The source reduces an arbitrary finite locally free module to constant rank
  with condition (2), the splitting `A(U ⨿ V) = A(U) × A(V)`. That condition is not in the
  situation and the reduction is unavailable, so constant rank is a hypothesis.
* **Property (2) on generators.** The source states `f^* ∘ c^A = c^A ∘ f^*` with the right-hand
  `f^*` the induced map on `K₀(Vect(-))`. That map does not exist in this repository: it needs
  the pullback of a short exact sequence of finite locally free modules to stay exact, which
  holds because such a sequence is locally split and is nowhere formalised. Property (2) is
  therefore stated on the generators `[ℰ]`, which is the form the source's own proof uses; the
  two agree as soon as the `K₀`-level map exists, since both sides are additive.

## Implementation notes

`∏_{i ≥ 0} A^i(X)` is read as the family of components, `ℕ → A(X)` with the `n`-th component in
`A^n(X)`; property (1) is then the convolution `c_n(α + β) = ∑_{i + j = n} c_i(α) c_j(β)`, which
is the product of that family spelled out. This avoids constructing the completed graded ring,
whose only role in the source is to carry that product.

The sign in equation 45.12.1.1 is an integer acting by `zsmul` rather than `(-1 : A(X))^i`. That
is what makes the sign commute past `c₁^A(𝒪_P(1))^i` in a ring that is not commutative, by
`mul_smul_comm`, and past `p^*` by `map_zsmul`.

## References

* [Stacks Project, Tag 0FI5](https://stacks.math.columbia.edu/tag/0FI5)
* [Stacks Project, Tag 0FI4](https://stacks.math.columbia.edu/tag/0FI4)
* [Stacks Project, Tag 0FI7](https://stacks.math.columbia.edu/tag/0FI7)
* [Stacks Project, Tag 0FDK](https://stacks.math.columbia.edu/tag/0FDK)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe u v v₁ w

namespace Stacks.WeilCohomology

/-! ### Reading a filtration in the `K`-group -/

/-- The `K`-group of Tag 0FDK is stated with `Stacks.FiniteLocallyFree.IsFiniteLocallyFree`,
while `AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank` produces the other predicate
of Tag 01C6 (2); the two agree, and this is the direction used below. -/
private theorem stacksFlf {X : Scheme.{u}} {M : X.Modules}
    (h : SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) M) :
    Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} M :=
  (Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry M).mpr h

/-- The same identification in the other direction. -/
private theorem agFlf {X : Scheme.{u}} {M : X.Modules}
    (h : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} M) :
    SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) M :=
  (Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry M).mp h

/-- An invertible module is finite locally free: on a scheme it is finite locally free of rank
one by Tag 0B8M. -/
private theorem stacksFlf_of_isInvertible {X : Scheme.{u}} (L : X.Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L) :
    Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} L := by
  have := hL
  have h1 : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1 :=
    inferInstance
  exact stacksFlf h1.isFiniteLocallyFree

/-- **A filtration with invertible successive quotients, read in `K₀(Vect(X))`.** A module
carrying one is finite locally free, and its class is the sum of the classes of the quotients. -/
theorem HasInvertibleFiltration.exists_classOf_eq_sum {X : Scheme.{u}} {E : X.Modules} {r : ℕ}
    (h : HasInvertibleFiltration X E r) :
    SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E ∧
      ∃ L : Fin r → X.Modules,
        (∀ j, AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)) ∧
          VectorBundleKZero.classOf X E = ∑ j, VectorBundleKZero.classOf X (L j) := by
  induction h with
  | nil E hE =>
      have hzero : SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
          (0 : X.Modules) :=
        agFlf (VectorBundleKZero.isFiniteLocallyFree_zero X)
      have hfree : SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E :=
        SheafOfModules.IsFiniteLocallyFree.of_iso (h := hzero) ((isZero_zero _).iso hE)
      refine ⟨hfree, Fin.elim0, fun j => j.elim0, ?_⟩
      simpa using
        VectorBundleKZero.classOf_eq_of_iso (hE.iso (isZero_zero _)) (stacksFlf hfree)
  | @step E F L r f g w hS hL hE hF ih =>
      obtain ⟨hFfree, L', hL', hsum⟩ := ih
      have := hS.mono_f
      have := hS.epi_g
      have hsplit := VectorBundleKZero.classOf_shortExact f g w (stacksFlf hFfree)
        (stacksFlf hE) (stacksFlf_of_isInvertible L hL) hS.exact
      refine ⟨hE, Fin.snoc L' L, ?_, ?_⟩
      · intro j
        refine Fin.lastCases ?_ ?_ j
        · simpa using hL
        · intro i
          simpa using hL' i
      · rw [hsplit, hsum, Fin.sum_univ_castSucc]
        simp

/-! ### The rule of Tag 0FI5 and its uniqueness -/

variable {C : Type w} [Category.{v₁} C] {S : C ⥤ Scheme.{u}}

/-- **The three properties of Tag 0FI5's total Chern class.** A rule `c` assigns to every object
`X` of `𝒞` and every class `α` of `K₀(Vect(X))` the components `c X α n` of its total Chern
class, the `n`-th lying in `A^n(X)`; it is multiplicative on sums, compatible with pullback on
the classes of modules, and takes the value `1 + c₁^A(ℒ)` on an invertible module. -/
structure IsTotalChernClass (𝔄 : ChernSetup.{u, v, v₁, w} C S)
    (c : ∀ X : C, VectorBundleKZero (S.obj X) → ℕ → 𝔄.A X) : Prop where
  /-- The `n`-th component lies in `A^n(X)`, so that `c` lands in `∏_{i ≥ 0} A^i(X)`. -/
  mem_grade : ∀ (X : C) (α : VectorBundleKZero (S.obj X)) (n : ℕ), c X α n ∈ 𝔄.grade X n
  /-- **Property (1).** `c^A(α + β) = c^A(α) c^A(β)`, componentwise. -/
  map_add : ∀ (X : C) (α β : VectorBundleKZero (S.obj X)) (n : ℕ),
    c X (α + β) n = ∑ p ∈ Finset.antidiagonal n, c X α p.1 * c X β p.2
  /-- **Property (1).** `c^A(0) = 1`. -/
  map_zero : ∀ (X : C) (n : ℕ), c X 0 n = if n = 0 then 1 else 0
  /-- **Property (2).** `f^* ∘ c^A = c^A ∘ f^*`, on the class of a module. -/
  map_pull : ∀ {X Y : C} (f : X ⟶ Y) (E : (S.obj Y).Modules) (n : ℕ),
    𝔄.pull f (c Y (VectorBundleKZero.classOf (S.obj Y) E) n) =
      c X (VectorBundleKZero.classOf (S.obj X)
        ((Scheme.Modules.pullback (S.map f)).obj E)) n
  /-- **Property (3).** `c^A([ℒ]) = 1 + c₁^A(ℒ)` for an invertible module `ℒ`. -/
  invertible : ∀ (X : C) (L : (S.obj X).Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj X).presheaf
      (S.obj X).ringCatSheaf.2 L) (n : ℕ),
    c X (VectorBundleKZero.classOf (S.obj X) L) n =
      if n = 0 then 1 else if n = 1 then 𝔄.c₁ X (picardClassOf (S.obj X) L hL) else 0

/-- Two rules with the three properties agree on a sum of classes of invertible modules:
property (1) turns the sum into a convolution of values that property (3) pins down. -/
private theorem eq_on_sum_classOf_invertible {𝔄 : ChernSetup.{u, v, v₁, w} C S}
    {c c' : ∀ X : C, VectorBundleKZero (S.obj X) → ℕ → 𝔄.A X}
    (hc : IsTotalChernClass 𝔄 c) (hc' : IsTotalChernClass 𝔄 c') (P : C) (k : ℕ) :
    ∀ (L : Fin k → (S.obj P).Modules)
      (_ : ∀ j, AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj P).presheaf
        (S.obj P).ringCatSheaf.2 (L j)) (n : ℕ),
      c P (∑ j, VectorBundleKZero.classOf (S.obj P) (L j)) n =
        c' P (∑ j, VectorBundleKZero.classOf (S.obj P) (L j)) n := by
  induction k with
  | zero =>
      intro L _ n
      simp [hc.map_zero, hc'.map_zero]
  | succ k ih =>
      intro L hL n
      rw [Fin.sum_univ_castSucc, hc.map_add, hc'.map_add]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [ih (fun j => L j.castSucc) (fun j => hL _) p.1,
        hc.invertible P (L (Fin.last k)) (hL _) p.2,
        hc'.invertible P (L (Fin.last k)) (hL _) p.2]

/-- **The uniqueness half of Stacks Tag 0FI5.** Properties (1), (2) and (3) determine the total
Chern class of the class of a finite locally free module of constant rank: any two rules with
those properties agree there.

The splitting principle of Tag 0FI7 supplies `p : P ⟶ X` with `p^*` injective on `A` and a
filtration of `p^*ℰ` with invertible successive quotients. That filtration writes `[p^*ℰ]` as a
sum of classes of invertible modules in `K₀(Vect(P))`, where properties (1) and (3) determine the
total Chern class; property (2) identifies the result with `p^*c^A([ℰ])`, and `p^*` is
injective. -/
@[stacks 0FI5 "uniqueness, for the class of a module of constant rank; the existence half of the
rule on all of K₀ needs condition (5), which `ChernSetup` does not carry, and property (2) is stated
on generators — see the module documentation"]
theorem eq_of_isTotalChernClass {𝔄 : ChernSetup.{u, v, v₁, w} C S}
    {c c' : ∀ X : C, VectorBundleKZero (S.obj X) → ℕ → 𝔄.A X}
    (hc : IsTotalChernClass 𝔄 c) (hc' : IsTotalChernClass 𝔄 c') (X : C)
    (E : (S.obj X).Modules) (r : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r) (n : ℕ) :
    c X (VectorBundleKZero.classOf (S.obj X) E) n =
      c' X (VectorBundleKZero.classOf (S.obj X) E) n := by
  obtain ⟨P, p, -, hinj, hfil⟩ :=
    𝔄.exists_injective_hasInvertibleFiltration X Unit (fun _ => E) (fun _ => r) fun _ => hE
  obtain ⟨-, L, hL, hsum⟩ := (hfil ()).exists_classOf_eq_sum
  refine hinj ?_
  rw [hc.map_pull p E n, hc'.map_pull p E n, hsum]
  exact eq_on_sum_classOf_invertible hc hc' P _ L hL n

/-! ### The Chern classes of a module of constant rank -/

namespace ChernSetup

variable (𝔄 : ChernSetup.{u, v, v₁, w} C S) (X : C) (E : (S.obj X).Modules) (r : ℕ)
  (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1))

/-- The element of `A(𝐏(ℰ))` that the Chern classes are defined to resolve: minus the top term
`(-1)^{r+1} c₁^A(𝒪_P(1))^{r+1}` of equation 45.12.1.1. -/
def topTerm : 𝔄.A (𝔄.bundleDatum X E r hE).bundle :=
  -(((-1 : ℤ) ^ (r + 1)) •
    𝔄.c₁ (𝔄.bundleDatum X E r hE).bundle (𝔄.bundleDatum X E r hE).twistClass ^ (r + 1))

/-- **The tuple of Chern classes of a finite locally free module of constant rank `r + 1`**, as
the projective bundle formula produces it: the unique `(a_0, …, a_r)` with
`∑_i c₁^A(𝒪_P(1))^i ∪ p^*(a_i) = -(-1)^{r+1} c₁^A(𝒪_P(1))^{r+1}`. This is a real body — the
inverse of the bijection of condition (4) — and not a choice out of an existence statement. -/
def chernTuple : Fin (r + 1) → 𝔄.A X :=
  (Equiv.ofBijective _ (𝔄.bijective_bundleFormula X E r hE)).symm (𝔄.topTerm X E r hE)

/-- The defining property of the tuple. -/
theorem bundleFormula_chernTuple :
    𝔄.bundleFormula X E r hE (𝔄.chernTuple X E r hE) = 𝔄.topTerm X E r hE :=
  (Equiv.ofBijective _ (𝔄.bijective_bundleFormula X E r hE)).apply_symm_apply _

/-- **The Chern classes `c_j^A(ℰ)` of a finite locally free module of constant rank `r + 1`.**
The zeroth is `1`, those in degrees `1, …, r + 1` are the entries of `chernTuple` with the signs
of equation 45.12.1.1, and the rest vanish.

This is the construction half of Tag 0FI5 for a single module: a real body, the inverse of the
bijection of condition (4) applied to an explicit element. It is not yet a rule on `K₀(Vect(X))`;
see the module documentation. -/
@[stacks 0FI5 "the Chern classes of one finite locally free module of constant positive rank;
not yet the rule on K₀"]
def chernClass (j : ℕ) : 𝔄.A X :=
  if hj : j = 0 then 1
  else if h : j ≤ r + 1 then
    ((-1 : ℤ) ^ (r + 1 - j)) • 𝔄.chernTuple X E r hE ⟨r + 1 - j, by omega⟩
  else 0

/-- `c_0^A(ℰ) = 1`. -/
@[simp] theorem chernClass_zero : 𝔄.chernClass X E r hE 0 = 1 := by
  simp [chernClass]

/-- The Chern classes in degrees `1, …, r + 1` are the signed entries of the tuple. -/
theorem chernClass_of_le {j : ℕ} (hj : j ≠ 0) (h : j ≤ r + 1) :
    𝔄.chernClass X E r hE j =
      ((-1 : ℤ) ^ (r + 1 - j)) • 𝔄.chernTuple X E r hE ⟨r + 1 - j, by omega⟩ := by
  unfold chernClass
  split_ifs with h1
  · exact absurd h1 hj
  · rfl

/-- **Equation 45.12.1.1**, the relation that defines the Chern classes:
`∑_{i=0}^{r+1} (-1)^i c₁^A(𝒪_P(1))^i ∪ p^*c^A_{r+1-i}(ℰ) = 0` in `A(𝐏(ℰ))`.

The term at `i = r + 1` is `(-1)^{r+1} c₁^A(𝒪_P(1))^{r+1}`, because `c_0^A(ℰ) = 1`; the terms
below it reproduce the projective bundle formula applied to the tuple, the two signs cancelling,
and that is `-(-1)^{r+1} c₁^A(𝒪_P(1))^{r+1}` by construction. -/
@[stacks 0FI5 "equation 45.12.1.1, the relation defining the Chern classes"]
theorem sum_chernClass_eq_zero :
    ∑ i : Fin (r + 2), ((-1 : ℤ) ^ (i : ℕ)) •
        (𝔄.c₁ (𝔄.bundleDatum X E r hE).bundle (𝔄.bundleDatum X E r hE).twistClass ^ (i : ℕ) *
          𝔄.pull (𝔄.bundleDatum X E r hE).proj (𝔄.chernClass X E r hE (r + 1 - (i : ℕ)))) = 0 := by
  have hlow : ∀ i : Fin (r + 1),
      ((-1 : ℤ) ^ ((i.castSucc : Fin (r + 2)) : ℕ)) •
          (𝔄.c₁ (𝔄.bundleDatum X E r hE).bundle (𝔄.bundleDatum X E r hE).twistClass ^
              ((i.castSucc : Fin (r + 2)) : ℕ) *
            𝔄.pull (𝔄.bundleDatum X E r hE).proj
              (𝔄.chernClass X E r hE (r + 1 - ((i.castSucc : Fin (r + 2)) : ℕ)))) =
        𝔄.c₁ (𝔄.bundleDatum X E r hE).bundle (𝔄.bundleDatum X E r hE).twistClass ^ (i : ℕ) *
          𝔄.pull (𝔄.bundleDatum X E r hE).proj (𝔄.chernTuple X E r hE i) := by
    intro i
    have hi : (i : ℕ) ≤ r := Nat.lt_succ_iff.1 i.isLt
    have hcast : ((i.castSucc : Fin (r + 2)) : ℕ) = (i : ℕ) := rfl
    have hri : r + 1 - (r + 1 - (i : ℕ)) = i := by omega
    have hidx : (⟨r + 1 - (r + 1 - (i : ℕ)), by omega⟩ : Fin (r + 1)) = i := Fin.ext hri
    rw [hcast, 𝔄.chernClass_of_le X E r hE (by omega) (by omega), hidx]
    rw [map_zsmul, mul_smul_comm, smul_smul, ← pow_add, hri, ← two_mul, pow_mul]
    simp
  rw [Fin.sum_univ_castSucc, Finset.sum_congr rfl fun i _ => hlow i]
  have hlast : ((Fin.last (r + 1) : Fin (r + 2)) : ℕ) = r + 1 := rfl
  rw [hlast, Nat.sub_self, 𝔄.chernClass_zero X E r hE, map_one]
  have hsum : ∑ i : Fin (r + 1),
      𝔄.c₁ (𝔄.bundleDatum X E r hE).bundle (𝔄.bundleDatum X E r hE).twistClass ^ (i : ℕ) *
        𝔄.pull (𝔄.bundleDatum X E r hE).proj (𝔄.chernTuple X E r hE i) =
      𝔄.topTerm X E r hE := 𝔄.bundleFormula_chernTuple X E r hE
  rw [hsum, topTerm, mul_one]
  abel

end ChernSetup

end Stacks.WeilCohomology

end
