module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.InvertiblePullback.Basic
public import StacksFrontier.AlgebraicGeometry.PicardGroup.Scheme
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleQuotients.Basic
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree

/-!
# The standing situation for Chern classes in a Weil cohomology theory

Section 45.12 of the Stacks Project fixes a category `𝒞` of schemes, a contravariant functor `A`
from `𝒞` to graded algebras, and an additive first Chern class `c₁^A : Pic(X) ⟶ A¹(X)`, subject
to five conditions; every statement of the section is read in that situation. This file writes the
situation down.

The two pieces of data are `Stacks.WeilCohomology.BundleDatum`, the projective bundle `𝐏(ℰ)` of a
finite locally free module with its projection and its tautological sequence, and
`Stacks.WeilCohomology.ChernSetup`, the graded invariant together with the conditions.

## Main definitions

* `Stacks.WeilCohomology.BundleDatum`: the projective bundle of a finite locally free module of
  rank `r + 1`, as an object of `𝒞`: its projection, which is flat, the invertible module
  `𝒪_{𝐏(ℰ)}(1)`, and the tautological short exact sequence
  `0 ⟶ 𝓕 ⟶ p^*ℰ ⟶ 𝒪_{𝐏(ℰ)}(1) ⟶ 0` with `𝓕` finite locally free of rank `r`.
* `Stacks.WeilCohomology.BundleDatum.twistClass`: the class of `𝒪_{𝐏(ℰ)}(1)` in `Pic(𝐏(ℰ))`.
* `Stacks.WeilCohomology.ChernSetup`: the standing situation — the graded rings `A(X)`, the
  pullback ring maps, the first Chern class, the projective bundles, and the conditions.

## Main results

* `Stacks.WeilCohomology.ChernSetup.injective_pull_proj`: **pullback along the projection of a
  projective bundle is injective on `A`.** This is the consequence of the projective bundle
  formula that the splitting principle consumes, and it is a consequence and not an assumption:
  a class `a` is the image of the tuple `(a, 0, …, 0)` under the formula's bijection.

## Which clauses of the source are transcribed

The source's standing situation has three clauses on `𝒞` and five conditions on `A`. Transcribed
here are clause (3)(a) — the projection `𝐏(ℰ) ⟶ X` is a morphism of `𝒞` — as the `bundle` and
`proj` fields, condition (1) — `c₁^A(ℒ)` is central — as `c₁_central`, and condition (4) — the
projective bundle formula — as `bijective_bundleFormula`, together with the graded ring structure
of `A(X)` and the functoriality of `f^*`.

Not transcribed are clause (1) (objects are quasi-compact and quasi-separated), clause (2) and
condition (2) (open and closed subobjects, and the splitting `A(U ⨿ V) = A(U) × A(V)` they index),
clauses (3)(b) and (3)(c) (functoriality of `𝐏` and the closed immersion `𝐏(𝓕) ⟶ 𝐏(ℰ)`), condition
(3) (`f^*c₁^A(ℒ) = c₁^A(f^*ℒ)`) and condition (5) (the vanishing on an effective Cartier divisor).
Omitting a condition only makes the results below more general; what it costs is recorded with
each of them. Concretely, condition (2) is what the source uses to reduce an arbitrary finite
locally free module to one of constant rank, so results that the source states for an arbitrary
module are stated here for one of constant rank.

## Implementation notes

The tautological sequence is a **field** of `BundleDatum` rather than a construction. The reason
is that `𝒪_{𝐏(ℰ)}(1)` has no name in this repository: Tag 01NR's twist datum
`Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData` is stated but has no inhabitant, so the
relative twists of a projective bundle do not exist as terms, and neither does the surjection
`p^*ℰ ⟶ 𝒪_{𝐏(ℰ)}(1)` or the local freeness of its kernel. The projective bundle itself does
exist — `Stacks.RelativeProj.projectiveBundleToBase`, which carries Tag 01OB — but without the
twist it cannot be given a `BundleDatum`. The source presupposes all of this; so the situation
carries it, and a reader must supply it to use the results.

Flatness of the projection is likewise a field. It is not decoration: extending a filtration of
the tautological kernel to one of `p^*ℰ` requires the tautological sequence to stay exact after a
further pullback, which is exactness of flat pullback, Tag 02N4.

The category `𝒞` is presented as a functor `S : 𝒞 ⥤ Scheme` rather than as a subcategory of
schemes, which is how the source's "category of schemes" is read: the objects of `𝒞` are indexed
by `𝒞` and their schemes by `S`, and a morphism of `𝒞` has an underlying morphism of schemes.

The grading of `A(X)` is recorded by the family of additive subgroups `grade X i` together with
`one_mem` and `mul_mem`; the source's further assertion that `A(X)` is the internal direct sum of
them is not needed below and is not required. `A(X)` is a ring and not an algebra over a
commutative ring, which is the source's "unital, associative, not necessarily commutative
`𝐙`-algebra".

Invertibility is `AlgebraicGeometry.SheafOfModules.IsInvertible`, the class carrying Tag 01CS in
which short exact sequences of module sheaves are stated; `Stacks.SheafOfModules.IsInvertible` is
the class the Picard group of Tag 01CX is built from, and the two are exchanged by
`Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible`, which is what
`BundleDatum.twistClass` does.

## References

* [Stacks Project, Tag 0FI4](https://stacks.math.columbia.edu/tag/0FI4)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 01CX](https://stacks.math.columbia.edu/tag/01CX)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v v₁ w

namespace Stacks.WeilCohomology

/-! ### The Picard class of an invertible module -/

/-- **The class in `Pic(X)` of an invertible `𝒪_X`-module**, at the spelling of invertibility in
which short exact sequences of module sheaves are stated. Both classes carry Tag 01CS; the
Picard group of Tag 01CX is built from the other one, and this is where the two are exchanged. -/
def picardClassOf (X : Scheme.{u}) (L : X.Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L) :
    X.picardGroup :=
  X.picardClass L
    ((Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
      X.presheaf X.ringCatIsSheaf L).mpr hL)

/-! ### The projective bundle of a finite locally free module -/

/-- **The projective bundle of a finite locally free module of rank `r + 1`.** For an object `X`
of `𝒞` and a module `ℰ` on it, this is the object `𝐏(ℰ)` of `𝒞`, its projection `p` — a flat
morphism of schemes — the invertible module `𝒪_{𝐏(ℰ)}(1)`, and the tautological short exact
sequence `0 ⟶ 𝓕 ⟶ p^*ℰ ⟶ 𝒪_{𝐏(ℰ)}(1) ⟶ 0` whose kernel is finite locally free of rank `r`. -/
structure BundleDatum {C : Type w} [Category.{v₁} C] (S : C ⥤ Scheme.{u}) (X : C)
    (E : (S.obj X).Modules) (r : ℕ) where
  /-- The projective bundle `𝐏(ℰ)`, an object of `𝒞` by clause (3)(a) of the source. -/
  bundle : C
  /-- Its projection `p : 𝐏(ℰ) ⟶ X`, a morphism of `𝒞`. -/
  proj : bundle ⟶ X
  /-- The projection is flat. -/
  flat : Flat (S.map proj)
  /-- The tautological invertible module `𝒪_{𝐏(ℰ)}(1)`. -/
  twist : (S.obj bundle).Modules
  /-- It is invertible. -/
  twist_isInvertible : AlgebraicGeometry.SheafOfModules.IsInvertible
    (S.obj bundle).presheaf (S.obj bundle).ringCatSheaf.2 twist
  /-- The kernel `𝓕` of the tautological surjection. -/
  sub : (S.obj bundle).Modules
  /-- Its inclusion into `p^*ℰ`. -/
  incl : sub ⟶ (Scheme.Modules.pullback (S.map proj)).obj E
  /-- The tautological surjection `p^*ℰ ⟶ 𝒪_{𝐏(ℰ)}(1)`. -/
  quot : (Scheme.Modules.pullback (S.map proj)).obj E ⟶ twist
  /-- The two maps compose to zero. -/
  incl_comp_quot : incl ≫ quot = 0
  /-- The tautological sequence is short exact. -/
  shortExact : (ShortComplex.mk incl quot incl_comp_quot).ShortExact
  /-- The kernel is finite locally free of rank `r`, one less than the rank of `ℰ`. -/
  sub_rank : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} sub r

attribute [instance] BundleDatum.flat

namespace BundleDatum

variable {C : Type w} [Category.{v₁} C] {S : C ⥤ Scheme.{u}} {X : C}
  {E : (S.obj X).Modules} {r : ℕ}

/-- **The class of `𝒪_{𝐏(ℰ)}(1)` in `Pic(𝐏(ℰ))`.** -/
def twistClass (D : BundleDatum S X E r) : (S.obj D.bundle).picardGroup :=
  picardClassOf (S.obj D.bundle) D.twist D.twist_isInvertible

end BundleDatum

/-! ### The standing situation -/

/-- **The standing situation of Stacks Section 45.12.** A contravariant functor `A` from a
category `𝒞` of schemes to graded rings, an additive first Chern class `c₁^A : Pic(X) ⟶ A¹(X)`
whose values are central, the projective bundle of every finite locally free module of positive
constant rank, and the projective bundle formula.

Which clauses of the source are transcribed, and what omitting the others costs, is recorded in
the module documentation. -/
structure ChernSetup (C : Type w) [Category.{v₁} C] (S : C ⥤ Scheme.{u}) where
  /-- The graded ring `A(X)`. -/
  A : C → Type v
  /-- `A(X)` is a unital associative, not necessarily commutative, ring. -/
  [ring : ∀ X, Ring (A X)]
  /-- The grading `A(X) = ⨁_{i ≥ 0} A^i(X)`, as a family of additive subgroups. -/
  grade : ∀ X : C, ℕ → AddSubgroup (A X)
  /-- The unit is in degree zero. -/
  one_mem : ∀ X : C, (1 : A X) ∈ grade X 0
  /-- Multiplication adds degrees. -/
  mul_mem : ∀ (X : C) (i j : ℕ) {a b : A X}, a ∈ grade X i → b ∈ grade X j →
    a * b ∈ grade X (i + j)
  /-- The pullback `f^* : A(X) ⟶ A(X')` of a morphism `f : X' ⟶ X` of `𝒞`. -/
  pull : ∀ {X Y : C}, (X ⟶ Y) → (A Y →+* A X)
  /-- Pullback along an identity is the identity. -/
  pull_id : ∀ X : C, pull (𝟙 X) = RingHom.id (A X)
  /-- Pullback is contravariantly functorial. -/
  pull_comp : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), pull (f ≫ g) = (pull f).comp (pull g)
  /-- Pullback preserves degrees. -/
  pull_grade : ∀ {X Y : C} (f : X ⟶ Y) (i : ℕ) {a : A Y}, a ∈ grade Y i →
    pull f a ∈ grade X i
  /-- The first Chern class `c₁^A : Pic(X) ⟶ A¹(X)`, an additive map. -/
  c₁ : ∀ X : C, (S.obj X).picardGroup →+ A X
  /-- Its values lie in degree one. -/
  c₁_mem : ∀ (X : C) (L : (S.obj X).picardGroup), c₁ X L ∈ grade X 1
  /-- **Axiom (1).** The first Chern class of an invertible module is central in `A(X)`. -/
  c₁_central : ∀ (X : C) (L : (S.obj X).picardGroup) (a : A X), c₁ X L * a = a * c₁ X L
  /-- **Clause (3)(a).** The projective bundle of a finite locally free module of rank `r + 1`,
  with its projection, its tautological invertible module and its tautological sequence. -/
  bundleDatum : ∀ (X : C) (E : (S.obj X).Modules) (r : ℕ),
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1) →
      BundleDatum S X E r
  /-- **Axiom (4), the projective bundle formula.** For `ℰ` of constant rank `r + 1` with
  projective bundle `p : P ⟶ X`, the map `(a₀, …, a_r) ↦ ∑ c₁^A(𝒪_P(1))^i ∪ p^*(a_i)` from
  `r + 1` copies of `A(X)` to `A(P)` is bijective. -/
  bijective_bundleFormula : ∀ (X : C) (E : (S.obj X).Modules) (r : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1)),
    Function.Bijective fun a : Fin (r + 1) → A X =>
      ∑ i : Fin (r + 1),
        c₁ (bundleDatum X E r hE).bundle (bundleDatum X E r hE).twistClass ^ (i : ℕ) *
          pull (bundleDatum X E r hE).proj (a i)

attribute [instance] ChernSetup.ring

namespace ChernSetup

variable {C : Type w} [Category.{v₁} C] {S : C ⥤ Scheme.{u}} (𝔄 : ChernSetup.{u, v, v₁, w} C S)

/-- The projective bundle formula's map, named so that its bijectivity can be applied to a
tuple. -/
def bundleFormula (X : C) (E : (S.obj X).Modules) (r : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1))
    (a : Fin (r + 1) → 𝔄.A X) : 𝔄.A (𝔄.bundleDatum X E r hE).bundle :=
  ∑ i : Fin (r + 1),
    𝔄.c₁ (𝔄.bundleDatum X E r hE).bundle (𝔄.bundleDatum X E r hE).twistClass ^ (i : ℕ) *
      𝔄.pull (𝔄.bundleDatum X E r hE).proj (a i)

/-- The projective bundle formula sends the tuple `(a, 0, …, 0)` to `p^*a`: every term past the
first has a zero factor, and the first has `c₁^A(𝒪_P(1))^0 = 1`. -/
theorem bundleFormula_single (X : C) (E : (S.obj X).Modules) (r : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1))
    (a : 𝔄.A X) :
    𝔄.bundleFormula X E r hE (Pi.single 0 a) = 𝔄.pull (𝔄.bundleDatum X E r hE).proj a := by
  classical
  rw [bundleFormula, Finset.sum_eq_single (0 : Fin (r + 1))]
  · simp
  · intro i _ hi
    simp [Pi.single_eq_of_ne hi]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **Pullback along the projection of a projective bundle is injective on `A`.**

This is the clause of the projective bundle formula that the splitting principle uses, and it is
a consequence of condition (4) rather than a further assumption: `p^*a` is the image of the tuple
`(a, 0, …, 0)` under the formula's bijection, so two classes with the same pullback have equal
tuples and are therefore equal. -/
theorem injective_pull_proj (X : C) (E : (S.obj X).Modules) (r : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1)) :
    Function.Injective (𝔄.pull (𝔄.bundleDatum X E r hE).proj) := by
  classical
  intro a b hab
  have h : 𝔄.bundleFormula X E r hE (Pi.single 0 a) = 𝔄.bundleFormula X E r hE (Pi.single 0 b) :=
    (𝔄.bundleFormula_single X E r hE a).trans
      (hab.trans (𝔄.bundleFormula_single X E r hE b).symm)
  have := (𝔄.bijective_bundleFormula X E r hE).injective h
  simpa using congrFun this (0 : Fin (r + 1))

end ChernSetup

end Stacks.WeilCohomology

end
