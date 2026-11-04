module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.CategoryTheory.Category.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# The cycle class map of a first Chern class in cohomology

Section 45.14 of the Stacks Project fixes data `(D0)`, `(D1)`, `(D2')` — a Tate line, a
contravariant functor `H^*` to graded commutative `F`-algebras, and a first Chern class
`c_1^H : Pic(X) → H^2(X)(1)` — and Tag 0FIF asserts that, granted the axioms `(A1)` – `(A4)`,
there is exactly one rule assigning to every smooth projective `X` over `k` a graded ring
homomorphism `γ : CH^*(X) → ⨁_{i ≥ 0} H^{2i}(X)(i)`, compatible with pullbacks, whose
composition with the Chern character is the cohomological Chern character `ch^H` of Tag 0FIE.
This file writes that rule's three properties down, constructs it, and proves it unique.

The source's proof is the whole content: the Chern character gives a ring isomorphism
`K₀(Vect(X)) ⊗ ℚ ≅ CH^*(X) ⊗ ℚ`, `α ↦ ch(α) ∩ [X]` (Chow Homology, Tags 0FEY and 0FEM), and `γ`
is `ch^H` transported along its inverse. Compatibility with pullbacks is inherited from the two
maps being transported, and the grading comes from the second Adams operator: a cycle class of
codimension `i` corresponds to a `2^i`-eigenvector of `ψ²`, and `ch^H` of such an eigenvector
lies in `H^{2i}(X)(i)` by Tag 0FIA.

## Main definitions

* `Stacks.WeilCohomology.CycleClassSetup`: the inputs the source's proof consumes — the three
  contravariant functors `K₀(Vect(-)) ⊗ ℚ`, `CH^*(-) ⊗ ℚ` and `⨁_{i ≥ 0} H^{2i}(-)(i)` with
  their gradings, the cohomological Chern character of Tag 0FIE, the Chern character
  isomorphism of Tags 0FEY and 0FEM, and the second Adams operator of Tag 0FEJ with the two
  eigenvalue statements.
* `Stacks.WeilCohomology.IsCycleClassRule`: the three properties of Tag 0FIF's rule — graded,
  compatible with pullbacks, and `γ(ch(α) ∩ [X]) = ch^H(α)`.
* `Stacks.WeilCohomology.CycleClassSetup.cycleClassMap`: **the cycle class map `γ`**, the
  cohomological Chern character transported along the inverse of the Chern character
  isomorphism.

## Main results

* `Stacks.WeilCohomology.CycleClassSetup.isCycleClassRule_cycleClassMap`: **the existence half
  of Tag 0FIF.** The transported map has the three properties.
* `Stacks.WeilCohomology.eq_of_isCycleClassRule`: **the uniqueness half of Tag 0FIF.** Two rules
  with those properties are equal — indeed the third property alone determines the rule, since
  the Chern character isomorphism is surjective.

## The statement as printed, and the statement proved

The source writes the defining property as `ch^H(α) = γ(ch(α))`. That does not typecheck as
printed: `ch(α)` is a Chern character, and what the proof substitutes into `γ` is the cycle
class `ch(α) ∩ [X]`, which lives in `CH^*(X) ⊗ ℚ` and not in `CH^*(X)`. The form proved here is
the one the proof defines, `γ(ch(α) ∩ [X]) = ch^H(α)`, with `γ` taken on `CH^*(X) ⊗ ℚ`.

Taking `γ` there rather than on `CH^*(X)` is the same choice: the source's rule on `CH^*(X)` is
the composition of this one with `CH^*(X) → CH^*(X) ⊗ ℚ`, and the defining equation, which is an
equation between classes in `CH^*(X) ⊗ ℚ`, determines the rule exactly where it is stated here.
The grading clause is read the same way, `γ(CH^i(X) ⊗ ℚ) ⊆ H^{2i}(X)(i)`.

## The dictionary

`𝒞` is the category of smooth projective schemes over `k`, and for an object `X`:

* `K X` is `K₀(Vect(X)) ⊗ ℚ` and `kPull` is pullback of finite locally free modules;
* `CH X` is `CH^*(X) ⊗ ℚ`, `chPull` is the Gysin pullback `f^!`, and `chGrade X i` is the
  codimension-`i` part;
* `A X` is `⨁_{i ≥ 0} H^{2i}(X)(i)`, a commutative ring because its summands sit in even
  degrees and a `ℚ`-algebra because `F` has characteristic zero, `aPull` is `f^*`, and
  `aGrade X i` is `H^{2i}(X)(i)`;
* `chH` is the cohomological Chern character `ch^H` of Tag 0FIE and `chH_pull` its
  compatibility with pullbacks, which is the other half of that tag;
* `chCap` is `α ↦ ch(α) ∩ [X]`, an isomorphism by Chow Homology, Tag 0FEY, and a ring
  isomorphism by Chow Homology, Tag 0FEM; `chCap_pull` is Chow Homology's compatibility of
  Chern classes with the Gysin maps;
* `adams` is the second Adams operator `ψ²` of Chow Homology, Tag 0FEJ;
* `adams_symm_chCap` is the statement of Chow Homology, Section 42.58 (Tag 0FEX) that a
  codimension-`i` cycle class corresponds to a `2^i`-eigenvector of `ψ²`;
* `chH_mem_aGrade` is the consequence of Tag 0FIA used by the proof: the cohomological Chern
  character of a `2^i`-eigenvector of `ψ²` lies in `H^{2i}(X)(i)`.

Everything in that list is a hypothesis because it belongs to a different tag; none of it is
part of what Tag 0FIF asserts.

## Implementation notes

The gradings are families of additive subgroups rather than a direct sum decomposition, as in
`Stacks.WeilCohomology.ChernSetup`: the two clauses used below are membership statements, and
the decomposition is not needed. Functoriality of the three pullbacks is likewise not assumed —
`f ↦ f^*` is used one morphism at a time — so the results hold for any family of ring maps with
the stated compatibilities.

`cycleClassMap` has a real body: it is `ch^H` composed with the inverse of a given ring
isomorphism, not a map chosen out of the existence statement it proves.

## References

* [Stacks Project, Tag 0FIF](https://stacks.math.columbia.edu/tag/0FIF)
* [Stacks Project, Tag 0FIE](https://stacks.math.columbia.edu/tag/0FIE)
* [Stacks Project, Tag 0FIA](https://stacks.math.columbia.edu/tag/0FIA)
* [Stacks Project, Tag 0FEY](https://stacks.math.columbia.edu/tag/0FEY)
* [Stacks Project, Tag 0FEM](https://stacks.math.columbia.edu/tag/0FEM)
* [Stacks Project, Tag 0FEJ](https://stacks.math.columbia.edu/tag/0FEJ)
-/

@[expose] public section

universe v v₁ w

namespace Stacks.WeilCohomology

open CategoryTheory

/-- **The inputs of Tag 0FIF.** The three contravariant functors the lemma relates, with the
gradings of the outer two, the cohomological Chern character, the Chern character isomorphism
`K₀(Vect(X)) ⊗ ℚ ≅ CH^*(X) ⊗ ℚ`, and the second Adams operator together with the two eigenvalue
statements the grading argument uses. See the module documentation for the dictionary. -/
structure CycleClassSetup (C : Type w) [Category.{v₁} C] where
  /-- `K₀(Vect(X)) ⊗ ℚ`, the rational Grothendieck ring of finite locally free modules. -/
  K : C → Type v
  /-- It is a commutative ring. -/
  [kRing : ∀ X, CommRing (K X)]
  /-- Pullback `f^* : K₀(Vect(Y)) ⊗ ℚ ⟶ K₀(Vect(X)) ⊗ ℚ`. -/
  kPull : ∀ {X Y : C}, (X ⟶ Y) → (K Y →+* K X)
  /-- `CH^*(X) ⊗ ℚ`, the rational Chow ring. -/
  CH : C → Type v
  /-- It is a commutative ring. -/
  [chRing : ∀ X, CommRing (CH X)]
  /-- The Gysin pullback `f^! : CH^*(Y) ⊗ ℚ ⟶ CH^*(X) ⊗ ℚ`. -/
  chPull : ∀ {X Y : C}, (X ⟶ Y) → (CH Y →+* CH X)
  /-- The codimension grading, `chGrade X i` being `CH^i(X) ⊗ ℚ`. -/
  chGrade : ∀ X : C, ℕ → AddSubgroup (CH X)
  /-- `⨁_{i ≥ 0} H^{2i}(X)(i)`, the even Tate-twisted cohomology. -/
  A : C → Type v
  /-- It is a commutative ring, its summands sitting in even degrees. -/
  [aRing : ∀ X, CommRing (A X)]
  /-- The cohomological pullback `f^*`. -/
  aPull : ∀ {X Y : C}, (X ⟶ Y) → (A Y →+* A X)
  /-- The grading, `aGrade X i` being `H^{2i}(X)(i)`. -/
  aGrade : ∀ X : C, ℕ → AddSubgroup (A X)
  /-- **Tag 0FIE.** The cohomological Chern character `ch^H`, a ring homomorphism. -/
  chH : ∀ X : C, K X →+* A X
  /-- **Tag 0FIE.** It is compatible with pullbacks. -/
  chH_pull : ∀ {X Y : C} (f : X ⟶ Y) (α : K Y), aPull f (chH Y α) = chH X (kPull f α)
  /-- **Tags 0FEY and 0FEM.** The Chern character `α ↦ ch(α) ∩ [X]` is an isomorphism of rings
  `K₀(Vect(X)) ⊗ ℚ ≅ CH^*(X) ⊗ ℚ`. -/
  chCap : ∀ X : C, K X ≃+* CH X
  /-- It is compatible with the Gysin pullbacks, Chern classes being so. -/
  chCap_pull : ∀ {X Y : C} (f : X ⟶ Y) (α : K Y), chPull f (chCap Y α) = chCap X (kPull f α)
  /-- **Tag 0FEJ.** The second Adams operator `ψ²`. -/
  adams : ∀ X : C, K X →+* K X
  /-- **Chow Homology, Section 42.58 (Tag 0FEX).** The class of `K₀(Vect(X)) ⊗ ℚ` answering to a
  cycle class of codimension `i` is a `2^i`-eigenvector of `ψ²`. -/
  adams_symm_chCap : ∀ (X : C) (i : ℕ) (a : CH X), a ∈ chGrade X i →
    adams X ((chCap X).symm a) = (2 ^ i : ℕ) • (chCap X).symm a
  /-- **Tag 0FIA.** The cohomological Chern character of a `2^i`-eigenvector of `ψ²` lies in
  `H^{2i}(X)(i)`. -/
  chH_mem_aGrade : ∀ (X : C) (i : ℕ) (α : K X), adams X α = (2 ^ i : ℕ) • α →
    chH X α ∈ aGrade X i

attribute [instance] CycleClassSetup.kRing CycleClassSetup.chRing CycleClassSetup.aRing

variable {C : Type w} [Category.{v₁} C]

/-- **The three properties of Tag 0FIF's cycle class map.** A rule `γ` assigns to every object
`X` of `𝒞` a ring homomorphism `CH^*(X) ⊗ ℚ ⟶ ⨁_{i ≥ 0} H^{2i}(X)(i)`; it is graded, compatible
with pullbacks, and sends `ch(α) ∩ [X]` to `ch^H(α)`. -/
structure IsCycleClassRule (S : CycleClassSetup.{v, v₁, w} C)
    (γ : ∀ X : C, S.CH X →+* S.A X) : Prop where
  /-- `γ` is graded: a cycle class of codimension `i` goes to `H^{2i}(X)(i)`. -/
  mem_aGrade : ∀ (X : C) (i : ℕ) {a : S.CH X}, a ∈ S.chGrade X i → γ X a ∈ S.aGrade X i
  /-- `γ` is compatible with pullbacks: `f^* ∘ γ = γ ∘ f^!`. -/
  map_pull : ∀ {X Y : C} (f : X ⟶ Y) (a : S.CH Y), S.aPull f (γ Y a) = γ X (S.chPull f a)
  /-- The defining equation `γ(ch(α) ∩ [X]) = ch^H(α)`. -/
  chH_eq : ∀ (X : C) (α : S.K X), γ X (S.chCap X α) = S.chH X α

namespace CycleClassSetup

variable (S : CycleClassSetup.{v, v₁, w} C)

/-- **The cycle class map `γ : CH^*(X) ⊗ ℚ ⟶ ⨁_{i ≥ 0} H^{2i}(X)(i)` of Tag 0FIF**: the
cohomological Chern character transported along the inverse of the Chern character isomorphism
of Tags 0FEY and 0FEM. -/
def cycleClassMap (X : C) : S.CH X →+* S.A X :=
  (S.chH X).comp (S.chCap X).symm

/-- The cycle class map sends `ch(α) ∩ [X]` to the cohomological Chern character `ch^H(α)`. -/
@[simp] theorem cycleClassMap_chCap (X : C) (α : S.K X) :
    S.cycleClassMap X (S.chCap X α) = S.chH X α := by
  simp [cycleClassMap]

/-- **The existence half of Stacks Tag 0FIF.** The transported cohomological Chern character is
graded, compatible with pullbacks, and satisfies `γ(ch(α) ∩ [X]) = ch^H(α)`.

The grading is the source's Adams operator argument: a class of codimension `i` answers to a
`2^i`-eigenvector of `ψ²`, whose cohomological Chern character lies in `H^{2i}(X)(i)` by Tag
0FIA. Compatibility with pullbacks is that of `ch^H` and of the Chern character isomorphism, the
latter transported through its inverse. The defining equation holds by construction. -/
@[stacks 0FIF "existence: the rule, constructed rather than chosen, together with its three \
  properties — graded, compatible with pullbacks, and `γ(ch(α) ∩ [X]) = ch^H(α)`. The source \
  prints that equation as `ch^H(α) = γ(ch(α))`, which typechecks only after capping with `[X]`; \
  the form proved is the one the source's own proof defines, and `γ` is correspondingly taken \
  on `CH^*(X) ⊗ ℚ`, where the equation lives. Tag 0FIE (`ch^H`), Tags 0FEY and 0FEM (the ring \
  isomorphism `K₀(Vect(X)) ⊗ ℚ ≅ CH^*(X) ⊗ ℚ`), Tag 0FEJ (`ψ²`) and Tags 0FEX and 0FIA (the two \
  eigenvalue statements) are hypotheses, carried by `CycleClassSetup`"]
theorem isCycleClassRule_cycleClassMap : IsCycleClassRule S S.cycleClassMap where
  mem_aGrade X i _ ha := S.chH_mem_aGrade X i _ (S.adams_symm_chCap X i _ ha)
  map_pull {X Y} f a := by
    have h : S.kPull f ((S.chCap Y).symm a) = (S.chCap X).symm (S.chPull f a) := by
      have hc := S.chCap_pull f ((S.chCap Y).symm a)
      rw [RingEquiv.apply_symm_apply] at hc
      rw [hc, RingEquiv.symm_apply_apply]
    simpa [cycleClassMap, h] using S.chH_pull f ((S.chCap Y).symm a)
  chH_eq X α := S.cycleClassMap_chCap X α

end CycleClassSetup

/-- **The uniqueness half of Stacks Tag 0FIF.** Two rules with the three properties are equal.

Only the defining equation is used: the Chern character isomorphism of Tags 0FEY and 0FEM is
surjective, so a rule is determined by its values on the classes `ch(α) ∩ [X]`. -/
@[stacks 0FIF "uniqueness: the defining equation `γ(ch(α) ∩ [X]) = ch^H(α)` alone determines \
  the rule, the Chern character isomorphism of Tags 0FEY and 0FEM being surjective. As in the \
  existence half the equation is the corrected form of the source's `ch^H(α) = γ(ch(α))` and \
  `γ` is taken on `CH^*(X) ⊗ ℚ`"]
theorem eq_of_isCycleClassRule {S : CycleClassSetup.{v, v₁, w} C}
    {γ γ' : ∀ X : C, S.CH X →+* S.A X} (h : IsCycleClassRule S γ) (h' : IsCycleClassRule S γ') :
    γ = γ' := by
  funext X
  ext a
  rw [← (S.chCap X).apply_symm_apply a, h.chH_eq, h'.chH_eq]

end Stacks.WeilCohomology

end
