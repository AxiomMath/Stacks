module

public import StacksFrontier.AlgebraicGeometry.FiberRank.ConstantRank
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.ChernSeries
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.RankReduction
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.SubbundleDivisor
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.WhitneyFormula

/-!
# The standing situation of Stacks Section 45.12, with the clauses `ChernSetup` leaves out

`Stacks.WeilCohomology.ChernSetup` transcribes clause (3)(a), condition (1) and condition (4) of
the standing situation of Stacks Section 45.12 (Tag 0FI4). Tag 0FI5 is stated *in that situation*
and its proof uses the rest of it, so this file adds the rest, as
`Stacks.WeilCohomology.ChernSituation`, and develops the total Chern class of a module of
constant rank in it.

## Main definitions

* `Stacks.WeilCohomology.ChernSituation`: **the standing situation**, `ChernSetup` together with
  the clauses and conditions of Section 45.12 it does not record.
* `Stacks.WeilCohomology.RationalChernSituation`: **the standing situation with
  `𝐐`-coefficients**, which is the situation Tag 0FI9 is read in: the above together with the
  condition that `A(X)` is a `𝐐`-algebra compatibly with the grading, so that the rationals lie
  in `A^0(X)`.
* `Stacks.WeilCohomology.ChernSituation.chernSeries`: the total Chern class of a finite locally
  free module of constant rank, as an element of the group
  `Stacks.WeilCohomology.UnitalCentralSeries`.

## Main results

* `Stacks.WeilCohomology.ChernSetup.pow_c₁_mem_grade`: `c₁^A(ℒ)^k ∈ A^k(X)`.
* `Stacks.WeilCohomology.ChernSituation.c₁_divisorClass`: the first Chern class of the divisor
  class of `𝐏(𝓕) ⊂ 𝐏(ℰ)` is `c₁^A(𝒪_P(1)) - p^*c₁^A(ℒ)`.
* `Stacks.WeilCohomology.ChernSituation.chernSeries_eq_of_rank`: the total Chern class does not
  depend on which constant rank is exhibited.
* `Stacks.WeilCohomology.ChernSituation.chernClass_mem_grade`: **`c_j^A(ℰ) ∈ A^j(X)`.**
* `Stacks.WeilCohomology.ChernSituation.pull_chernClass`: **`f^*c_j^A(ℰ) = c_j^A(f^*ℰ)`.**
* `Stacks.WeilCohomology.ChernSituation.chernSeries_coeff_invertible`: **property (3) of Tag 0FI5
  for one invertible module**, `c^A(ℒ) = 1 + c₁^A(ℒ)`.

## What each field is

Of the source's three clauses on `𝒞` and five conditions on `A`, `ChernSetup` records clause (1),
clause (2), clause (3)(a), condition (1), condition (2) and condition (4), together with the
source's grading `A(X) = ⨁_{i ≥ 0} A^i(X)`. The three fields here are the rest, and **each is the
source's own statement**: no field asserts anything the source derives.

Tag 0FI5 is stated over these three as hypotheses rather than over this structure, in
`Stacks.WeilCohomology.existsUnique_isTotalChernClass_of_source`; the structure is assembled
inside that proof. It is kept because the whole development of this directory is written over it.

* `pull_c₁_pullback` is **condition (3)** exactly as the source states it,
  `f^*c₁^A(ℒ) = c₁^A(f^*ℒ)`, at `f^*ℒ` itself. The form with an isomorphism `f^*ℒ ≅ ℒ'` built in,
  which is what the consumers use, is no longer a field: it is the theorem
  `Stacks.WeilCohomology.ChernSituation.pull_c₁`, because `c₁^A` is a function on `Pic` and an
  isomorphism of invertible modules is equality of Picard classes.

* `exists_bundleCompare_bundleObject` is **clause (3)(b)** and only that: the morphism
  `𝐏(f^*ℰ) ⟶ 𝐏(ℰ)` induced by `f` is a morphism of `𝒞`, which is
  `Stacks.WeilCohomology.IsBundleCompare` — over `f`, and the constructed
  `Stacks.Chow.bundleBaseChangeHom` on schemes. That it carries `c₁^A(𝒪_P(1))` to
  `c₁^A(𝒪_{P'}(1))` is not part of this field but the theorem
  `Stacks.WeilCohomology.ChernSituation.exists_bundleCompare`, from the base change of the twist
  and condition (3).
* `exists_divisorDatum_bundleObject` is **clause (3)(c) and condition (5)**, for the closed
  immersion `i : 𝐏(𝓕) ⟶ 𝐏(ℰ)` a surjection `ℰ ⟶ 𝓕` with invertible kernel `ℒ` induces. Clause
  (3)(c) is only the closure property, `Stacks.WeilCohomology.IsBundleEmbedding`; the
  identification `i^*c₁^A(𝒪_P(1)) = c₁^A(𝒪_{P'}(1))` is the theorem
  `Stacks.WeilCohomology.ChernSituation.exists_divisorDatum`, and condition (5) is stated at the
  divisor module rather than at `𝒪_P(1) ⊗ (p^*ℒ)^{⊗ -1}`. Four facts that accompany it are
  proved rather than carried by the field.

  The first is that the middle term of the sequence has rank one more than `𝓕`. It is no longer
  produced by the field but *asked of* it: the rank of `ℰ` is a hypothesis, and the consumer
  `Stacks.WeilCohomology.ChernSituation.chernSeries_mul_of_invertibleSub` discharges it from
  `AlgebraicGeometry.SheafOfModules.rank_add_of_shortExact`, rank additivity at a point of the
  scheme, the pointless case being the one where `A(X)` is the zero ring by
  `subsingleton_of_isEmpty`.

  The second is the divisor class itself. The field no longer posits a class
  `D ∈ Pic(𝐏(ℰ))` together with the equation `c₁^A(D) = c₁^A(𝒪_P(1)) - p^*c₁^A(ℒ)`; it states
  condition (5) at the class `𝒪_P(1) ⊗ (p^*ℒ)^{⊗ -1}`, written out in `Pic(𝐏(ℰ))`, and that
  equation is then a *theorem* — `c₁^A` is additive on `Pic` and condition (3) turns
  `c₁^A(p^*ℒ)` into `p^*c₁^A(ℒ)` — namely
  `Stacks.WeilCohomology.ChernSituation.c₁_divisorClass`. What remains carried is only the
  source's identification of `𝒪_P(𝐏(𝓕))` with `ℒ^{⊗ -1} ⊗ 𝒪_P(1)`. **That is no longer carried.**
  Condition (5) is stated at `c₁^A` of the divisor module itself, characterized
  divisor-theoretically by `Stacks.WeilCohomology.IsSubbundleDivisorModule`, and the
  identification is the theorem
  `Stacks.WeilCohomology.BundleObject.twistClass_eq_picardClassOf_add`: `𝐏(ℰ)` is the constructed
  `Stacks.Chow.bundle`, through the clause-(3)(a) field
  `Stacks.WeilCohomology.SourceChernSetup.bundleObject`, so `𝐏(𝓕) ⊂ 𝐏(ℰ)` carries an actual divisor
  whose class can be computed — which is what
  `Stacks.Chow.GenuineChern.exists_relativeEffectiveCartierDivisor_bundleEmbedding` computes, from
  the description of `𝐏(𝓕)` as the zero scheme of a regular section, exactly as the source does.

Condition (4) read with the grading is **no longer a field**. That the tuple the projective
bundle formula resolves a class of `A^n(P)` into has its `i`-th entry in `A^{n-i}(X)` is the
theorem `Stacks.WeilCohomology.SourceChernSetup.mem_grade_of_bundleFormula` below, proved from
condition
(4) together with `Stacks.WeilCohomology.SourceChernSetup.isInternal_grade` — the source's own
`A = ⨁_{i ≥ 0} A^i`, transcribed in `ChernSetup`. It was a field until that grading was.

The one condition of the section that `ChernSituation` does not record is the `𝐐`-algebra
structure of `A(X)`, which only Tag 0FI9 and what follows it read the section under: it is the
field `algebraMap_mem_grade_zero` of `Stacks.WeilCohomology.RationalChernSituation`, together
with the `𝐐`-algebra structure itself as that structure's instance field `algebra`. It is kept
out of `ChernSituation` because Tag 0FI5 does not need it, and a field is a hypothesis of every
theorem stated over the structure.

## What the situation no longer carries

The source's sentence "it suffices to check this after pulling back by the morphism
`𝐏(ℰ^∨) → X`. Thus we may assume we have an invertible submodule `ℒ ⊂ ℰ` such that both `ℰ/ℒ`
and `ℱ/ℒ` are finite locally free" was a field `exists_splitInvertibleSub` here. It is **no
longer a field**: it is proved, as
`Stacks.WeilCohomology.ChernSituation.exists_splitInvertibleSub`, in
`StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.InvertibleSubSplitting`. `𝐏(ℰ^∨)` is
clause (3)(a) at `ℰ^∨`, which is finite locally free of the same rank; injectivity of `p^*` is
condition (4) through `ChernSetup.injective_pull_proj`; and the three sequences are the duals of
the tautological sequence of `𝐏(ℰ^∨)`, of the kernel sequence of `p^*(ℱ^∨) ⟶ 𝒪_P(1)`, and of
the kernel-of-a-composite sequence relating the two.

The field was moreover *unsatisfiable*, which is why the theorem that replaces it fixes the
ranks of `ℱ` and `𝒢` where the field left them merely finite locally free: it demanded a
constant rank of `ℱ/ℒ`, and over an `X` with two open and closed pieces on which `ℱ` has ranks
`5` and `17` that quotient has ranks `4` and `16`. A field that cannot be inhabited makes every
theorem over the structure vacuous, and that is worse than an unproved hypothesis, because no
type-checking detects it.

The reduction of an arbitrary finite locally free module to constant rank is **not** carried here.
`Stacks.WeilCohomology.SourceChernSetup.eq_of_pull_constantRank`,
`Stacks.WeilCohomology.SourceChernSetup.exists_pull_eq_constantRank`,
`Stacks.WeilCohomology.SourceChernSetup.mem_grade_of_pull_constantRank` and
`Stacks.WeilCohomology.SourceChernSetup.subsingleton_of_isEmpty` — `A(X)` separated by, patched
from and graded by its restrictions along the morphisms of `𝒞` along which a finite family of
finite locally free modules acquires constant ranks, and `A(X)` the zero ring when `X` has no
points — are *theorems* about a bare `Stacks.WeilCohomology.ChernSetup`, proved in
`StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.RankReduction` from clause (1), clause
(2) in full and condition (2) read as a splitting of graded rings, together with the local
constancy of the rank of a finite locally free module. They were four fields of this structure
until the second sentence of clause (2) and the graded half of condition (2) were transcribed in
`Stacks.WeilCohomology.SourceChernSetup`; what made them irreducible then was exactly the absence
of those two. They are still available by the same names on a `ChernSituation`, through its
`SourceChernSetup`.

Nothing about Chern classes is carried. Everything in this file and in
`StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.ShortExactMultiplicativity` and
`StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.KZeroRule` is proved from the fields
above and from `ChernSetup`.

## References

* [Stacks Project, Tag 0FI4](https://stacks.math.columbia.edu/tag/0FI4)
* [Stacks Project, Tag 0FI5](https://stacks.math.columbia.edu/tag/0FI5)
* [Stacks Project, Tag 0ESW](https://stacks.math.columbia.edu/tag/0ESW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v v₁ w

namespace Stacks.WeilCohomology

/-- **The standing situation of Stacks Section 45.12.** `Stacks.WeilCohomology.ChernSetup`
together with the clauses and conditions of the section it does not record: condition (3) as the
source states it, condition (4) read with the grading, clause (3)(b), and clause (3)(c) with
condition (5).

What each field is, and which of them carry a fact the source proves elsewhere rather than
assumes, is set out in the module documentation. -/
structure ChernSituation (C : Type w) [Category.{v₁} C] (S : C ⥤ Scheme.{u})
    extends SourceChernSetup.{u, v, v₁, w} C S where
  /-- **Condition (3), exactly as the source states it.** `f^*c₁^A(ℒ) = c₁^A(f^*ℒ)`.

  The invertible module on the source is `f^*ℒ` itself and not an arbitrary module isomorphic to
  it: that refinement is `Stacks.WeilCohomology.ChernSituation.pull_c₁`, a theorem, because
  `c₁^A` is a function on `Pic` and isomorphic invertible modules have the same Picard class. -/
  pull_c₁_pullback : ∀ {X Y : C} (f : X ⟶ Y) (L : (S.obj Y).Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj Y).presheaf
      (S.obj Y).ringCatSheaf.2 L),
    pull f (c₁ Y (picardClassOf (S.obj Y) L hL)) =
      c₁ X (picardClassOf (S.obj X) ((Scheme.Modules.pullback (S.map f)).obj L)
        (isInvertible_pullback_obj (S.map f) L hL))
  /-- **Clause (3)(b), exactly as the source states it.** For `f : X' ⟶ X` in `𝒞` the induced
  morphism `𝐏(f^*ℰ) ⟶ 𝐏(ℰ)` is a morphism of `𝒞`: that is
  `Stacks.WeilCohomology.IsBundleCompare`, which asks only that the morphism lies over `f` and
  that its morphism of schemes is the constructed `Stacks.Chow.bundleBaseChangeHom`.

  The module on `X'` is `f^*ℰ` itself, which is the source's single instance; the finite local
  freeness of `f^*ℰ` is a hypothesis only so that the clause-(3)(a) datum of `f^*ℰ` can be named,
  and it is implied by that of `ℰ`, so demanding it for every proof demands nothing.

  Read at an *arbitrary* module `ℰ'` with an isomorphism `f^*ℰ ≅ ℰ'` this would say more than the
  source does — at `f = 𝟙 X` it would be the closure of `𝒞` under the `𝐏(ℰ') ⟶ 𝐏(ℰ)` induced by
  an arbitrary `ℰ ≅ ℰ'`, which clauses (1), (2) and (3) do not supply. That form is not assumed:
  it is the theorem `Stacks.WeilCohomology.ChernSituation.chernSeries_eq_of_iso`, which gets the
  invariance of the total Chern class under an isomorphism out of multiplicativity in the short
  exact sequence `0 ⟶ ℰ ⟶ ℰ' ⟶ 0 ⟶ 0` instead of out of a comparison of projective bundles.

  The identification of twists that accompanies the clause is the theorem
  `Stacks.WeilCohomology.ChernSituation.exists_bundleCompare`. -/
  exists_bundleCompare_bundleObject : ∀ (X X' : C) (f : X' ⟶ X) (E : (S.obj X).Modules) (r : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1))
    (hE' : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (S.map f)).obj E) (r + 1)),
      ∃ g : (bundleObject X' ((Scheme.Modules.pullback (S.map f)).obj E) r hE').bundle ⟶
          (bundleObject X E r hE).bundle,
        IsBundleCompare f (bundleObject X E r hE)
          (bundleObject X' ((Scheme.Modules.pullback (S.map f)).obj E) r hE') (Iso.refl _) g
  /-- **Clause (3)(c), and condition (5), both as the source states them.**

  Clause (3)(c) is the closure property `Stacks.WeilCohomology.IsBundleEmbedding`: the induced
  closed immersion `𝐏(𝓕) ⟶ 𝐏(ℰ)` is a morphism of `𝒞`. The identification of twists that
  accompanies it is the theorem
  `Stacks.WeilCohomology.ChernSituation.exists_divisorDatum`, from
  `Stacks.Chow.GenuineChern.bundleEmbeddingTwistIso`.

  **Condition (5) is stated at `c₁^A(𝒪_P(𝐏(𝓕)))`**, where `𝒪_P(𝐏(𝓕))` is characterized
  divisor-theoretically — `Stacks.WeilCohomology.IsSubbundleDivisorModule`: an invertible module
  on `𝐏(ℰ)` with a section whose zero scheme is a relative effective Cartier divisor over the
  base, identified with `𝐏(𝓕)`. `𝒪_P(1)` does not occur in it. The source's identification
  `𝒪_P(𝐏(𝓕)) ≅ 𝒪_P(1) ⊗ (p^*ℒ)^{⊗ -1}`, which this field used to *assume* by stating condition
  (5) at the explicit class, is now derived — it is
  `Stacks.WeilCohomology.BundleObject.twistClass_eq_picardClassOf_add`, from the description of
  `𝐏(𝓕)` as the zero scheme of a regular section, exactly as the source gets it. -/
  exists_divisorDatum_bundleObject : ∀ (X : C) (T : ShortComplex (S.obj X).Modules)
    (hT : T.ShortExact)
    (_hL : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj X).presheaf
      (S.obj X).ringCatSheaf.2 T.X₁) (r : ℕ)
    (hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} T.X₃ (r + 1))
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} T.X₂
      (r + 1 + 1)),
      ∃ i : (bundleObject X T.X₃ r hF).bundle ⟶ (bundleObject X T.X₂ (r + 1) hE).bundle,
        IsBundleEmbedding T hT (bundleObject X T.X₂ (r + 1) hE) (bundleObject X T.X₃ r hF) i ∧
          ∀ (L : (@Stacks.Chow.bundle (S.obj X) T.X₂
              (bundleObject X T.X₂ (r + 1) hE).isFiniteLocallyFree).Modules)
            (hLinv : AlgebraicGeometry.SheafOfModules.IsInvertible
              (@Stacks.Chow.bundle (S.obj X) T.X₂
                (bundleObject X T.X₂ (r + 1) hE).isFiniteLocallyFree).presheaf
              (@Stacks.Chow.bundle (S.obj X) T.X₂
                (bundleObject X T.X₂ (r + 1) hE).isFiniteLocallyFree).ringCatSheaf.2 L),
            IsSubbundleDivisorModule T hT
              (bundleObject X T.X₂ (r + 1) hE).isFiniteLocallyFree
              (bundleObject X T.X₃ r hF).isFiniteLocallyFree L hLinv →
            ∀ a : A (bundleObject X T.X₂ (r + 1) hE).bundle, pull i a = 0 →
              a * c₁ (bundleObject X T.X₂ (r + 1) hE).bundle
                (picardClassOf (S.obj (bundleObject X T.X₂ (r + 1) hE).bundle)
                  ((Scheme.Modules.pullback
                      (bundleObject X T.X₂ (r + 1) hE).iso.hom).obj L)
                  (isInvertible_pullback_obj _ L hLinv)) = 0

/-- **The standing situation of Stacks Section 45.12 with `𝐐`-coefficients.**
`Stacks.WeilCohomology.ChernSituation` together with the one further condition Tag 0FI9 reads the
section under: `A(X)` is a `𝐐`-algebra for every object `X` of `𝒞`, compatibly with the grading
`A` takes its values in, so that the rationals lie in `A^0(X)`.

This is a **condition of the source**, like the other fields, and not a result. The source reads
`A` as a contravariant functor to *graded* rings, and Tag 0FI9 states its Chern character with
`𝐐`-coefficients: without the two read together, the target `∏_{i ≥ 0} A^i(X)` of that tag's
statement is not a ring the formula `r^A + ∑_{i ≥ 1} (1/i!) P_i(c_1^A, …, c_i^A)` lands in. Nor
is it a consequence of the other fields: the grading of `𝐐[t]` by its `𝐙`-submodules — degree
zero the subgroup `𝐙` — satisfies every one of them while the rationals are not in degree zero.
So it is recorded here as a field, where the section's other conditions are, rather than carried
as a hypothesis by the theorems that need it. -/
structure RationalChernSituation (C : Type w) [Category.{v₁} C] (S : C ⥤ Scheme.{u})
    extends ChernSituation.{u, v, v₁, w} C S where
  /-- `A(X)` is a `𝐐`-algebra. -/
  [algebra : ∀ X : C, Algebra ℚ (A X)]
  /-- The `𝐐`-algebra structure read with the grading: the rationals lie in `A^0(X)`. -/
  algebraMap_mem_grade_zero : ∀ (X : C) (q : ℚ), algebraMap ℚ (A X) q ∈ grade X 0

attribute [instance] RationalChernSituation.algebra

/-! ### The section's three remaining conditions, and the situation they build

`Stacks.WeilCohomology.ChernSetup` records the data the source fixes together with clause (1),
clause (2), clause (3)(a), condition (1), condition (2), condition (4) and the grading. The three
`Prop`s below are the rest of Section 45.12, each in the source's own form, and
`Stacks.WeilCohomology.chernSituationOfSource` assembles them into a
`Stacks.WeilCohomology.ChernSituation`.

They are named so that the tags of the section can be stated over the source's conditions without
a structure argument, and without writing the three conditions out once per tag:
`Stacks.WeilCohomology.existsUnique_isTotalChernClass_of_source` (Tag 0FI5) and
`Stacks.WeilCohomology.existsUnique_isChernCharacter_of_source` (Tag 0FI9) both take exactly these
three and call the one construction. -/

section OfSource

variable {C : Type w} [Category.{v₁} C] {S : C ⥤ Scheme.{u}}

/-- **Condition (3) of Section 45.12**, exactly as the source states it:
`f^*c₁^A(ℒ) = c₁^A(f^*ℒ)`, at `f^*ℒ` itself. -/
def PullbackFirstChernCondition (𝔄 : SourceChernSetup.{u, v, v₁, w} C S) : Prop :=
  ∀ {X Y : C} (f : X ⟶ Y) (L : (S.obj Y).Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj Y).presheaf
      (S.obj Y).ringCatSheaf.2 L),
    𝔄.pull f (𝔄.c₁ Y (picardClassOf (S.obj Y) L hL)) =
      𝔄.c₁ X (picardClassOf (S.obj X) ((Scheme.Modules.pullback (S.map f)).obj L)
        (isInvertible_pullback_obj (S.map f) L hL))

/-- **Clause (3)(b) of Section 45.12, exactly as the source states it**: for `f : X' ⟶ X` in `𝒞`
the induced morphism `𝐏(f^*ℰ) ⟶ 𝐏(ℰ)` is a morphism of `𝒞`, which is
`Stacks.WeilCohomology.IsBundleCompare` — over `f`, and the constructed
`Stacks.Chow.bundleBaseChangeHom` on schemes. Nothing about twists, and the module on `X'` is
`f^*ℰ` itself rather than an arbitrary module isomorphic to it. The field
`Stacks.WeilCohomology.ChernSituation.exists_bundleCompare_bundleObject` records why the
arbitrary-isomorphism form is not assumed and where the development gets it instead. -/
def BundleCompareClause (𝔄 : SourceChernSetup.{u, v, v₁, w} C S) : Prop :=
  ∀ (X X' : C) (f : X' ⟶ X) (E : (S.obj X).Modules) (r : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1))
    (hE' : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (S.map f)).obj E) (r + 1)),
      ∃ g : (𝔄.bundleObject X' ((Scheme.Modules.pullback (S.map f)).obj E) r hE').bundle ⟶
          (𝔄.bundleObject X E r hE).bundle,
        IsBundleCompare f (𝔄.bundleObject X E r hE)
          (𝔄.bundleObject X' ((Scheme.Modules.pullback (S.map f)).obj E) r hE') (Iso.refl _) g

/-- **Clause (3)(c) of Section 45.12 together with condition (5)**, both as the source states
them: the induced closed immersion `𝐏(𝓕) ⟶ 𝐏(ℰ)` is a morphism of `𝒞`
(`Stacks.WeilCohomology.IsBundleEmbedding`), and a class of `A(𝐏(ℰ))` killed by `i^*` is killed by
multiplication with `c₁^A(𝒪_P(𝐏(𝓕)))`, read at the divisor module characterized
divisor-theoretically by `Stacks.WeilCohomology.IsSubbundleDivisorModule`. `𝒪_P(1)` does not occur
in it. -/
def DivisorDatumClause (𝔄 : SourceChernSetup.{u, v, v₁, w} C S) : Prop :=
  ∀ (X : C) (T : ShortComplex (S.obj X).Modules) (hT : T.ShortExact)
    (_hL : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj X).presheaf
      (S.obj X).ringCatSheaf.2 T.X₁) (r : ℕ)
    (hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} T.X₃ (r + 1))
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} T.X₂
      (r + 1 + 1)),
      ∃ i : (𝔄.bundleObject X T.X₃ r hF).bundle ⟶ (𝔄.bundleObject X T.X₂ (r + 1) hE).bundle,
        IsBundleEmbedding T hT (𝔄.bundleObject X T.X₂ (r + 1) hE)
            (𝔄.bundleObject X T.X₃ r hF) i ∧
          ∀ (L : (@Stacks.Chow.bundle (S.obj X) T.X₂
              (𝔄.bundleObject X T.X₂ (r + 1) hE).isFiniteLocallyFree).Modules)
            (hLinv : AlgebraicGeometry.SheafOfModules.IsInvertible
              (@Stacks.Chow.bundle (S.obj X) T.X₂
                (𝔄.bundleObject X T.X₂ (r + 1) hE).isFiniteLocallyFree).presheaf
              (@Stacks.Chow.bundle (S.obj X) T.X₂
                (𝔄.bundleObject X T.X₂ (r + 1) hE).isFiniteLocallyFree).ringCatSheaf.2 L),
            IsSubbundleDivisorModule T hT
              (𝔄.bundleObject X T.X₂ (r + 1) hE).isFiniteLocallyFree
              (𝔄.bundleObject X T.X₃ r hF).isFiniteLocallyFree L hLinv →
            ∀ a : 𝔄.A (𝔄.bundleObject X T.X₂ (r + 1) hE).bundle, 𝔄.pull i a = 0 →
              a * 𝔄.c₁ (𝔄.bundleObject X T.X₂ (r + 1) hE).bundle
                (picardClassOf (S.obj (𝔄.bundleObject X T.X₂ (r + 1) hE).bundle)
                  ((Scheme.Modules.pullback
                      (𝔄.bundleObject X T.X₂ (r + 1) hE).iso.hom).obj L)
                  (isInvertible_pullback_obj _ L hLinv)) = 0

/-- **The standing situation of Stacks Section 45.12, built from the source's conditions.**

`Stacks.WeilCohomology.ChernSetup` together with condition (3), clause (3)(b), and clause (3)(c)
with condition (5). This is the one place the situation is assembled; the tags of the section are
stated over the three conditions and call this. -/
def chernSituationOfSource (𝔄 : SourceChernSetup.{u, v, v₁, w} C S)
    (hpull : PullbackFirstChernCondition 𝔄) (hcompare : BundleCompareClause 𝔄)
    (hdivisor : DivisorDatumClause 𝔄) : ChernSituation.{u, v, v₁, w} C S where
  toSourceChernSetup := 𝔄
  pull_c₁_pullback := hpull
  exists_bundleCompare_bundleObject := hcompare
  exists_divisorDatum_bundleObject := hdivisor

/-- The underlying `SourceChernSetup` of `chernSituationOfSource 𝔄 hpull hcompare hdivisor` is
`𝔄`. -/
@[simp]
theorem chernSituationOfSource_toSourceChernSetup (𝔄 : SourceChernSetup.{u, v, v₁, w} C S)
    (hpull : PullbackFirstChernCondition 𝔄) (hcompare : BundleCompareClause 𝔄)
    (hdivisor : DivisorDatumClause 𝔄) :
    (chernSituationOfSource 𝔄 hpull hcompare hdivisor).toSourceChernSetup = 𝔄 := rfl

end OfSource

/-! ### Powers of a first Chern class are homogeneous -/

namespace ChernSetup

variable {C : Type w} [Category.{v₁} C] {S : C ⥤ Scheme.{u}}

/-- A power of a first Chern class lies in the degree equal to the exponent: `c₁^A(ℒ)` lies in
degree one and multiplication adds degrees. -/
theorem pow_c₁_mem_grade (𝔄 : ChernSetup.{u, v, v₁, w} C S) (X : C)
    (L : (S.obj X).picardGroup) (k : ℕ) : 𝔄.c₁ X L ^ k ∈ 𝔄.grade X k := by
  induction k with
  | zero => simpa using 𝔄.one_mem X
  | succ k ih => rw [pow_succ]; exact 𝔄.mul_mem X k 1 ih (𝔄.c₁_mem X L)

/-- **Condition (4) read with the grading: the tuple the projective bundle formula resolves a
class of `A^n(P)` into is homogeneous, with the `i`-th entry in `A^{n-i}(X)`.**

This is a **theorem**, not a condition. It is the source's own remark that condition (4) is a
bijection of *graded* rings — a graded bijection is bijective in each degree — and what it needs
is exactly `Stacks.WeilCohomology.SourceChernSetup.isInternal_grade`, which is the source's
`A = ⨁_{i ≥ 0} A^i`. It is what the clause `c^A : K₀(Vect(X)) ⟶ ∏_{i ≥ 0} A^i(X)` of Tag 0FI5
consumes, and it was a field of the standing situation until the grading was transcribed.

The argument. Decompose each `a i` into its homogeneous components and collect by *total* degree:
the tuple `b d` whose `i`-th entry is the degree-`(d - i)` component of `a i` has
`∑ c₁^A(𝒪_P(1))^i ∪ p^*(b d i) ∈ A^d(P)`, because `c₁^A(𝒪_P(1))^i` is of degree `i` and pullback
preserves degrees. Summing the `b d` over `d` recovers `a`, and the formula is additive in the
tuple, so `F(a) = ∑_d F(b d)` exhibits `F(a)` as a sum of homogeneous pieces of pairwise distinct
degrees. `F(a)` lies in `A^n(P)`, so uniqueness of the decomposition kills every `d ≠ n` and
`F(a) = F(b n)`; condition (4) is injective, so `a = b n`, whose `i`-th entry lies in
`A^{n-i}(X)`. -/
theorem _root_.Stacks.WeilCohomology.SourceChernSetup.mem_grade_of_bundleFormula
    (𝔄 : SourceChernSetup.{u, v, v₁, w} C S) (X : C)
    (E : (S.obj X).Modules) (r : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1))
    (a : Fin (r + 1) → 𝔄.A X) (n : ℕ)
    (h : (∑ i : Fin (r + 1),
        𝔄.c₁ (𝔄.bundleDatum X E r hE).bundle (𝔄.bundleDatum X E r hE).twistClass ^ (i : ℕ) *
          𝔄.pull (𝔄.bundleDatum X E r hE).proj (a i)) ∈
      𝔄.grade (𝔄.bundleDatum X E r hE).bundle n) :
    ∀ (i : Fin (r + 1)) (k : ℕ), (i : ℕ) + k = n → a i ∈ 𝔄.grade X k := by
  classical
  let dX : DirectSum.Decomposition (𝔄.grade X) :=
    (𝔄.isInternal_grade X).chooseDecomposition _
  let dP : DirectSum.Decomposition (𝔄.grade (𝔄.bundleDatum X E r hE).bundle) :=
    (𝔄.isInternal_grade (𝔄.bundleDatum X E r hE).bundle).chooseDecomposition _
  set D : Fin (r + 1) → DirectSum ℕ (fun d => (𝔄.grade X d : Type v)) :=
    fun i => DirectSum.decompose (𝔄.grade X) (a i) with hD
  set N : ℕ :=
    max ((Finset.univ.biUnion fun i : Fin (r + 1) => (D i).support).sup id + r + 1) (n + 1)
    with hN
  set b : ℕ → Fin (r + 1) → 𝔄.A X :=
    fun d i => if (i : ℕ) ≤ d then ((D i (d - (i : ℕ)) : 𝔄.grade X (d - (i : ℕ))) : 𝔄.A X) else 0
    with hb
  have hbval : ∀ (d : ℕ) (i : Fin (r + 1)), (i : ℕ) ≤ d →
      b d i = ((D i (d - (i : ℕ)) : 𝔄.grade X (d - (i : ℕ))) : 𝔄.A X) := by
    intro d i hid
    simp only [hb, ite_eq_left hid]
  have hbmem : ∀ (d : ℕ) (i : Fin (r + 1)), (i : ℕ) ≤ d → b d i ∈ 𝔄.grade X (d - (i : ℕ)) := by
    intro d i hid
    rw [hbval d i hid]
    exact (D i (d - (i : ℕ))).2
  have hb0 : ∀ (d : ℕ) (i : Fin (r + 1)), ¬ (i : ℕ) ≤ d → b d i = 0 := by
    intro d i hid
    simp only [hb, ite_eq_right hid]
  have hNn : n < N := lt_of_lt_of_le (Nat.lt_succ_self n) (le_max_right _ _)
  have hFb : ∀ d : ℕ, 𝔄.bundleFormula X E r hE (b d) ∈
      𝔄.grade (𝔄.bundleDatum X E r hE).bundle d := by
    intro d
    rw [ChernSetup.bundleFormula]
    refine AddSubgroup.sum_mem _ fun i _ => ?_
    rcases le_or_gt (i : ℕ) d with hid | hid
    · have hmul := 𝔄.mul_mem (𝔄.bundleDatum X E r hE).bundle (i : ℕ) (d - (i : ℕ))
        (𝔄.pow_c₁_mem_grade (𝔄.bundleDatum X E r hE).bundle
          (𝔄.bundleDatum X E r hE).twistClass (i : ℕ))
        (𝔄.pull_grade (𝔄.bundleDatum X E r hE).proj (d - (i : ℕ)) (hbmem d i hid))
      rwa [show (i : ℕ) + (d - (i : ℕ)) = d from by omega] at hmul
    · rw [hb0 d i (by omega), map_zero, mul_zero]
      exact AddSubgroup.zero_mem _
  have hsum : ∀ i : Fin (r + 1), ∑ d ∈ Finset.range N, b d i = a i := by
    intro i
    have hiR : (i : ℕ) ≤ r := Nat.lt_succ_iff.mp i.2
    have hdrop : ∑ d ∈ Finset.range N, b d i = ∑ d ∈ Finset.Ico (i : ℕ) N, b d i := by
      refine (Finset.sum_subset (fun d hd => ?_) (fun d hd hdn => ?_)).symm
      · exact Finset.mem_range.mpr (Finset.mem_Ico.mp hd).2
      · exact hb0 d i fun hid => hdn (Finset.mem_Ico.mpr ⟨hid, Finset.mem_range.mp hd⟩)
    rw [hdrop, Finset.sum_Ico_eq_sum_range]
    have hval : ∀ e ∈ Finset.range (N - (i : ℕ)),
        b ((i : ℕ) + e) i = ((D i e : 𝔄.grade X e) : 𝔄.A X) := by
      intro e _
      rw [hbval _ i (Nat.le_add_right (i : ℕ) e), Nat.add_sub_cancel_left]
    rw [Finset.sum_congr rfl hval]
    refine Eq.trans (Finset.sum_subset (fun e he => ?_) (fun e _ hes => ?_)).symm
      (DirectSum.sum_support_decompose (𝔄.grade X) (a i))
    · refine Finset.mem_range.mpr ?_
      have hle : e ≤ (Finset.univ.biUnion fun j : Fin (r + 1) => (D j).support).sup id :=
        Finset.le_sup (f := id) (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, he⟩)
      have hNle : (Finset.univ.biUnion fun j : Fin (r + 1) => (D j).support).sup id + r + 1 ≤ N :=
        le_max_left _ _
      omega
    · have hz : D i e = 0 := by
        by_contra hne
        exact hes (DFinsupp.mem_support_iff.mpr hne)
      rw [hz]
      rfl
  have hadd : ∑ d ∈ Finset.range N, 𝔄.bundleFormula X E r hE (b d) =
      𝔄.bundleFormula X E r hE a := by
    rw [ChernSetup.bundleFormula]
    have hstep : ∀ d : ℕ, 𝔄.bundleFormula X E r hE (b d) =
        ∑ i : Fin (r + 1),
          𝔄.c₁ (𝔄.bundleDatum X E r hE).bundle (𝔄.bundleDatum X E r hE).twistClass ^ (i : ℕ) *
            𝔄.pull (𝔄.bundleDatum X E r hE).proj (b d i) := fun d => rfl
    rw [Finset.sum_congr rfl fun d _ => hstep d, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.mul_sum, ← map_sum, hsum i]
  have hn : 𝔄.bundleFormula X E r hE a ∈ 𝔄.grade (𝔄.bundleDatum X E r hE).bundle n := h
  have hdc : ∀ (d : ℕ) (x : 𝔄.A (𝔄.bundleDatum X E r hE).bundle)
      (hx : x ∈ 𝔄.grade (𝔄.bundleDatum X E r hE).bundle d),
      (DirectSum.decomposeAddEquiv (𝔄.grade (𝔄.bundleDatum X E r hE).bundle)) x =
        DirectSum.of (fun d => (𝔄.grade (𝔄.bundleDatum X E r hE).bundle d : Type v)) d
          ⟨x, hx⟩ := fun d x hx => by
    rw [DirectSum.decomposeAddEquiv_apply]
    exact DirectSum.decompose_coe (𝔄.grade (𝔄.bundleDatum X E r hE).bundle) (i := d) ⟨x, hx⟩
  have hdec : (DirectSum.decomposeAddEquiv
        (𝔄.grade (𝔄.bundleDatum X E r hE).bundle)) (𝔄.bundleFormula X E r hE a) =
      ∑ d ∈ Finset.range N,
        DirectSum.of (fun d => (𝔄.grade (𝔄.bundleDatum X E r hE).bundle d : Type v)) d
          ⟨𝔄.bundleFormula X E r hE (b d), hFb d⟩ := by
    rw [← hadd, map_sum]
    exact Finset.sum_congr rfl fun d _ => hdc d _ _
  have hdec' := hdc n _ hn
  have hvan : ∀ m ∈ Finset.range N, m ≠ n → 𝔄.bundleFormula X E r hE (b m) = 0 := by
    intro m hm hmn
    have heval := congrArg
      (fun f : DirectSum ℕ (fun d => (𝔄.grade (𝔄.bundleDatum X E r hE).bundle d : Type v)) =>
        f m) (hdec'.symm.trans hdec)
    have hLHS : (DirectSum.of
        (fun d => (𝔄.grade (𝔄.bundleDatum X E r hE).bundle d : Type v)) n
          ⟨𝔄.bundleFormula X E r hE a, hn⟩) m = 0 := by
      rw [DirectSum.of_apply, dite_eq_right (Ne.symm hmn)]
    have hRHS : (∑ d ∈ Finset.range N,
        DirectSum.of (fun d => (𝔄.grade (𝔄.bundleDatum X E r hE).bundle d : Type v)) d
          ⟨𝔄.bundleFormula X E r hE (b d), hFb d⟩) m =
        ⟨𝔄.bundleFormula X E r hE (b m), hFb m⟩ := by
      rw [DFinsupp.finsetSum_apply]
      refine (Finset.sum_eq_single m (fun d _ hdm => ?_) (fun hmm => absurd hm hmm)).trans ?_
      · rw [DirectSum.of_apply, dite_eq_right hdm]
      · rw [DirectSum.of_apply, dite_eq_left rfl]
    rw [hLHS, hRHS] at heval
    simpa using (Subtype.ext_iff.mp heval).symm
  have hFan : 𝔄.bundleFormula X E r hE a = 𝔄.bundleFormula X E r hE (b n) := by
    rw [← hadd]
    exact Finset.sum_eq_single n (fun d hd hdn => hvan d hd hdn)
      (fun hnn => absurd (Finset.mem_range.mpr hNn) hnn)
  have hab : a = b n := (𝔄.bijective_bundleFormula X E r hE).injective hFan
  intro i k hik
  have hik' : (i : ℕ) ≤ n := by omega
  have hai : a i = b n i := by rw [hab]
  rw [hai, show k = n - (i : ℕ) from by omega]
  exact hbmem n i hik'

end ChernSetup

/-! ### The total Chern class of a module of constant rank -/

namespace ChernSituation

variable {C : Type w} [Category.{v₁} C] {S : C ⥤ Scheme.{u}}
  (𝔖 : ChernSituation.{u, v, v₁, w} C S)

/-! ### Condition (3) under an isomorphism of invertible modules -/

/-- **Condition (3), `f^*c₁^A(ℒ) = c₁^A(ℒ')` for any `ℒ'` isomorphic to `f^*ℒ`.**

This is the form every consumer uses, and it is a **theorem**, not a condition: the field
`pull_c₁_pullback` is the source's condition (3) at `f^*ℒ` itself, and `c₁^A` is a function on
`Pic(X)`, where an isomorphism of invertible modules *is* equality of classes
(`Stacks.WeilCohomology.picardClassOf_eq_of_iso`, from
`AlgebraicGeometry.Scheme.picardClass_eq_iff`). So the invariance of `c₁^A` under an isomorphism
of invertible modules costs nothing beyond the source's condition. -/
theorem pull_c₁ {X Y : C} (f : X ⟶ Y) (L : (S.obj Y).Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj Y).presheaf
      (S.obj Y).ringCatSheaf.2 L) (L' : (S.obj X).Modules)
    (hL' : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj X).presheaf
      (S.obj X).ringCatSheaf.2 L')
    (e : (Scheme.Modules.pullback (S.map f)).obj L ≅ L') :
    𝔖.pull f (𝔖.c₁ Y (picardClassOf (S.obj Y) L hL)) =
      𝔖.c₁ X (picardClassOf (S.obj X) L' hL') := by
  rw [𝔖.pull_c₁_pullback f L hL,
    picardClassOf_eq_of_iso (S.obj X) _ L' (isInvertible_pullback_obj (S.map f) L hL) hL' e]

/-! ### The two fields that mention the projective bundle, read at `bundleDatum`

Each field of the structure is stated at the clause-(3)(a) datum `bundleObject`. These two
theorems are the same statements read at the datum `bundleDatum` of the underlying
`Stacks.WeilCohomology.ChernSetup`, and they are the form everything below and in the rest of this
directory uses. They hold by `Stacks.WeilCohomology.SourceChernSetup.bundleDatum_eq`, which
identifies that datum with the one constructed from `bundleObject`, together with
`Stacks.WeilCohomology.BundleObject.toBundleDatum_bundle`,
`Stacks.WeilCohomology.BundleObject.toBundleDatum_proj` and
`Stacks.WeilCohomology.BundleObject.toBundleDatum_twistClass`. -/

/-- **Clause (3)(b) with the identification of twists: `g^*c₁^A(𝒪_P(1)) = c₁^A(𝒪_{P'}(1))`.**

This is a **theorem**, not a condition. The field `exists_bundleCompare_bundleObject` is the
source's clause (3)(b) alone — the induced morphism `𝐏(f^*ℰ) ⟶ 𝐏(ℰ)` is a morphism of `𝒞`. That
it carries `c₁^A(𝒪_{𝐏(ℰ)}(1))` to `c₁^A(𝒪_{𝐏(f^*ℰ)}(1))`, which the field used to assume, comes
from `Stacks.WeilCohomology.BundleObject.nonempty_pullback_twist_of_isBundleCompare` — the base
change of the twist, `Stacks.Chow.bundleBaseChange` — together with condition (3) in the form
`Stacks.WeilCohomology.ChernSituation.pull_c₁`. -/
theorem exists_bundleCompare (X X' : C) (f : X' ⟶ X) (E : (S.obj X).Modules) (r : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1))
    (hE' : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (S.map f)).obj E) (r + 1)) :
    ∃ g : (𝔖.bundleDatum X' ((Scheme.Modules.pullback (S.map f)).obj E) r hE').bundle ⟶
        (𝔖.bundleDatum X E r hE).bundle,
      g ≫ (𝔖.bundleDatum X E r hE).proj =
          (𝔖.bundleDatum X' ((Scheme.Modules.pullback (S.map f)).obj E) r hE').proj ≫ f ∧
        𝔖.pull g (𝔖.c₁ (𝔖.bundleDatum X E r hE).bundle (𝔖.bundleDatum X E r hE).twistClass) =
          𝔖.c₁ (𝔖.bundleDatum X' ((Scheme.Modules.pullback (S.map f)).obj E) r hE').bundle
            (𝔖.bundleDatum X' ((Scheme.Modules.pullback (S.map f)).obj E) r hE').twistClass := by
  rw [𝔖.bundleDatum_eq X E r hE, 𝔖.bundleDatum_eq X' _ r hE']
  obtain ⟨g, hg⟩ := 𝔖.exists_bundleCompare_bundleObject X X' f E r hE hE'
  obtain ⟨φ⟩ := BundleObject.nonempty_pullback_twist_of_isBundleCompare f
    (𝔖.bundleObject X E r hE)
    (𝔖.bundleObject X' ((Scheme.Modules.pullback (S.map f)).obj E) r hE') (Iso.refl _) g hg
  exact ⟨g, hg.comp_proj,
    𝔖.pull_c₁ g (𝔖.bundleObject X E r hE).twist (𝔖.bundleObject X E r hE).twist_isInvertible
      (𝔖.bundleObject X' ((Scheme.Modules.pullback (S.map f)).obj E) r hE').twist
      (𝔖.bundleObject X' ((Scheme.Modules.pullback (S.map f)).obj E) r hE').twist_isInvertible φ⟩

/-- **Clause (3)(c) with the identification of twists, together with condition (5).**

The identification `i^*c₁^A(𝒪_P(1)) = c₁^A(𝒪_{P'}(1))` is no longer assumed: the field
`exists_divisorDatum_bundleObject` carries only the closure property clause (3)(c) states, and
`Stacks.WeilCohomology.BundleObject.nonempty_pullback_twist_of_isBundleEmbedding` —
`Stacks.Chow.GenuineChern.bundleEmbeddingTwistIso` carried through the clause-(3)(a)
identifications — with condition (3) in the form
`Stacks.WeilCohomology.ChernSituation.pull_c₁` supplies it.

Condition (5) is still taken from the field at the explicit class; what remains to be done there
is recorded on the field. -/
theorem exists_divisorDatum (X : C) (T : ShortComplex (S.obj X).Modules) (hT : T.ShortExact)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj X).presheaf
      (S.obj X).ringCatSheaf.2 T.X₁) (r : ℕ)
    (hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} T.X₃ (r + 1))
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} T.X₂
      (r + 1 + 1)) :
    ∃ i : (𝔖.bundleDatum X T.X₃ r hF).bundle ⟶ (𝔖.bundleDatum X T.X₂ (r + 1) hE).bundle,
      i ≫ (𝔖.bundleDatum X T.X₂ (r + 1) hE).proj = (𝔖.bundleDatum X T.X₃ r hF).proj ∧
        𝔖.pull i (𝔖.c₁ (𝔖.bundleDatum X T.X₂ (r + 1) hE).bundle
            (𝔖.bundleDatum X T.X₂ (r + 1) hE).twistClass) =
          𝔖.c₁ (𝔖.bundleDatum X T.X₃ r hF).bundle (𝔖.bundleDatum X T.X₃ r hF).twistClass ∧
        ∀ a : 𝔖.A (𝔖.bundleDatum X T.X₂ (r + 1) hE).bundle, 𝔖.pull i a = 0 →
          a * 𝔖.c₁ (𝔖.bundleDatum X T.X₂ (r + 1) hE).bundle
              ((𝔖.bundleDatum X T.X₂ (r + 1) hE).twistClass -
                picardClassOf (S.obj (𝔖.bundleDatum X T.X₂ (r + 1) hE).bundle)
                  ((Scheme.Modules.pullback
                      (S.map (𝔖.bundleDatum X T.X₂ (r + 1) hE).proj)).obj T.X₁)
                  (isInvertible_pullback_obj _ T.X₁ hL)) = 0 := by
  rw [𝔖.bundleDatum_eq X T.X₂ (r + 1) hE, 𝔖.bundleDatum_eq X T.X₃ r hF]
  obtain ⟨i, hi, hdiv⟩ := 𝔖.exists_divisorDatum_bundleObject X T hT hL r hF hE
  obtain ⟨φ⟩ := BundleObject.nonempty_pullback_twist_of_isBundleEmbedding T hT
    (𝔖.bundleObject X T.X₂ (r + 1) hE) (𝔖.bundleObject X T.X₃ r hF) i hi
  obtain ⟨L, hLinv, hdivmod, ⟨eT⟩⟩ := exists_isSubbundleDivisorModule T hT hL r hF
    (𝔖.bundleObject X T.X₂ (r + 1) hE).isFiniteLocallyFree
    (𝔖.bundleObject X T.X₃ r hF).isFiniteLocallyFree
  have hclass := eq_sub_of_add_eq'
    ((𝔖.bundleObject X T.X₂ (r + 1) hE).twistClass_eq_picardClassOf_add T.X₁ hL L hLinv eT)
  refine ⟨i, hi.comp_proj,
    𝔖.pull_c₁ i (𝔖.bundleObject X T.X₂ (r + 1) hE).twist
      (𝔖.bundleObject X T.X₂ (r + 1) hE).twist_isInvertible
      (𝔖.bundleObject X T.X₃ r hF).twist (𝔖.bundleObject X T.X₃ r hF).twist_isInvertible φ,
    fun a ha => ?_⟩
  have h := hdiv L hLinv hdivmod a ha
  rwa [hclass] at h

/-- **The first Chern class of the divisor class of `𝐏(𝓕) ⊂ 𝐏(ℰ)` is
`c₁^A(𝒪_P(1)) - p^*c₁^A(ℒ)`.**

Condition (5) is carried in `exists_divisorDatum` at the class `𝒪_P(1) ⊗ (p^*ℒ)^{⊗ -1}` of
`Pic(𝐏(ℰ))`, which is what the source's `𝒪_P(𝐏(𝓕))` is. Its first Chern class is not a further
assumption: `c₁^A` is additive on `Pic(𝐏(ℰ))`, and condition (3) identifies `c₁^A(p^*ℒ)` with
`p^*c₁^A(ℒ)`. This is the form the Whitney computation
`Stacks.WeilCohomology.ChernSetup.chernClass_add_one_of_invertibleSub` consumes. -/
theorem c₁_divisorClass (X : C) (L : (S.obj X).Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj X).presheaf
      (S.obj X).ringCatSheaf.2 L) (E : (S.obj X).Modules) (r : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1)) :
    𝔖.c₁ (𝔖.bundleDatum X E r hE).bundle
        ((𝔖.bundleDatum X E r hE).twistClass -
          picardClassOf (S.obj (𝔖.bundleDatum X E r hE).bundle)
            ((Scheme.Modules.pullback (S.map (𝔖.bundleDatum X E r hE).proj)).obj L)
            (isInvertible_pullback_obj _ L hL)) =
      𝔖.c₁ (𝔖.bundleDatum X E r hE).bundle (𝔖.bundleDatum X E r hE).twistClass -
        𝔖.pull (𝔖.bundleDatum X E r hE).proj (𝔖.c₁ X (picardClassOf (S.obj X) L hL)) := by
  rw [map_sub, 𝔖.pull_c₁ (𝔖.bundleDatum X E r hE).proj L hL _
    (isInvertible_pullback_obj _ L hL) (Iso.refl _)]

/-- **The total Chern class of a finite locally free module of constant rank**, as an element of
the group of unital central series: `1` in rank zero, and `1 + c_1^A(ℰ) + … + c_r^A(ℰ)` in rank
`r + 1`. The components are central by
`Stacks.WeilCohomology.ChernSetup.chernClass_central` and the constant term is `1` by
`Stacks.WeilCohomology.ChernSetup.chernClass_zero`. -/
def chernSeries (X : C) (E : (S.obj X).Modules) (m : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E m) :
    UnitalCentralSeries (𝔖.A X) :=
  match m, hE with
  | 0, _ => 1
  | (r + 1), hE =>
      UnitalCentralSeries.ofCoeff (𝔖.chernClass X E r hE)
        (fun n => Subring.mem_center_iff.2 fun b => (𝔖.chernClass_central X E r hE n b).symm)
        (𝔖.chernClass_zero X E r hE)

/-- A module of rank zero has total Chern class `1`. -/
theorem chernSeries_rank_zero (X : C) (E : (S.obj X).Modules)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E 0) :
    𝔖.chernSeries X E 0 hE = 1 := rfl

/-- In positive rank the components of the total Chern class are the Chern classes. -/
theorem chernSeries_coeff_succ (X : C) (E : (S.obj X).Modules) (r : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1))
    (n : ℕ) : (𝔖.chernSeries X E (r + 1) hE).coeff n = 𝔖.chernClass X E r hE n := by
  exact UnitalCentralSeries.coeff_ofCoeff _ _ (𝔖.chernClass_zero X E r hE) n

/-- **The total Chern class does not depend on the rank witness.** Two constant ranks of one
module agree as soon as the object has a point, and if it has none then `A(X)` is the zero ring by
condition (2) at the empty decomposition. -/
theorem chernSeries_eq_of_rank (X : C) (E : (S.obj X).Modules) (m m' : ℕ)
    (hm : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E m)
    (hm' : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E m') :
    𝔖.chernSeries X E m hm = 𝔖.chernSeries X E m' hm' := by
  rcases isEmpty_or_nonempty (S.obj X) with hX | hX
  · exact (UnitalCentralSeries.subsingleton (𝔖.subsingleton_of_isEmpty X hX)).elim _ _
  · obtain ⟨x⟩ := hX
    have hmm : m = m' :=
      AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_unique E hm hm' x
    subst hmm
    rfl

/-- `topTerm` is `-((-1)^(r+1) • c₁^A(𝒪_P(1))^(r+1))`, by definition. -/
private theorem topTerm_eq_neg_smul_pow (X : C) (E : (S.obj X).Modules) (r : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1)) :
    𝔖.topTerm X E r hE =
      -(((-1 : ℤ) ^ (r + 1)) •
        𝔖.c₁ (𝔖.bundleDatum X E r hE).bundle (𝔖.bundleDatum X E r hE).twistClass ^ (r + 1)) :=
  rfl

/-- **The Chern classes are homogeneous**: `c_j^A(ℰ) ∈ A^j(X)`. The element the projective bundle
formula resolves is `-(-1)^{r+1} c₁^A(𝒪_P(1))^{r+1}`, which lies in `A^{r+1}(P)`; so the tuple it
resolves to has its `i`-th entry in `A^{r+1-i}(X)` by condition (4) read with the grading, and
`c_j^A(ℰ)` is, up to sign, the entry at `i = r + 1 - j`. -/
theorem chernClass_mem_grade (X : C) (E : (S.obj X).Modules) (r : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1))
    (j : ℕ) : 𝔖.chernClass X E r hE j ∈ 𝔖.grade X j := by
  have htop : 𝔖.topTerm X E r hE ∈
      𝔖.grade (𝔖.bundleDatum X E r hE).bundle (r + 1) := by
    rw [𝔖.topTerm_eq_neg_smul_pow X E r hE]
    exact AddSubgroup.neg_mem _ (AddSubgroup.zsmul_mem _
      (𝔖.pow_c₁_mem_grade (𝔖.bundleDatum X E r hE).bundle
        (𝔖.bundleDatum X E r hE).twistClass (r + 1)) _)
  have htuple : ∀ (i : Fin (r + 1)) (k : ℕ), (i : ℕ) + k = r + 1 →
      𝔖.chernTuple X E r hE i ∈ 𝔖.grade X k := by
    refine 𝔖.mem_grade_of_bundleFormula X E r hE (𝔖.chernTuple X E r hE) (r + 1) ?_
    change 𝔖.bundleFormula X E r hE (𝔖.chernTuple X E r hE) ∈ _
    rw [𝔖.bundleFormula_chernTuple X E r hE]
    exact htop
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [𝔖.chernClass_zero X E r hE]
    exact 𝔖.one_mem X
  rcases le_or_gt j (r + 1) with hle | hgt
  · rw [𝔖.chernClass_of_le X E r hE (by omega) hle]
    exact AddSubgroup.zsmul_mem _ (htuple ⟨r + 1 - j, by omega⟩ j (by simp; omega)) _
  · rw [𝔖.chernClass_of_gt X E r hE hgt]
    exact AddSubgroup.zero_mem _

/-- **The Chern classes are compatible with pullback**, which is the source's
`f^*c_i^A(ℰ) = c_i^A(f^*ℰ)`. Clause (3)(b) supplies a morphism `g : 𝐏(f^*ℰ) ⟶ 𝐏(ℰ)` over `f`
carrying `c₁^A(𝒪_P(1))` to `c₁^A(𝒪_{P'}(1))`; pulling equation 45.12.1.1 for `ℰ` back along `g`
is equation 45.12.1.1 for `f^*ℰ` with the family `f^*c_i^A(ℰ)`, which therefore is the family of
Chern classes of `f^*ℰ` by
`Stacks.WeilCohomology.ChernSetup.chernClass_eq_of_relation`. -/
theorem pull_chernClass (X X' : C) (f : X' ⟶ X) (E : (S.obj X).Modules) (r : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1))
    (hE' : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (S.map f)).obj E) (r + 1)) (j : ℕ) :
    𝔖.pull f (𝔖.chernClass X E r hE j) =
      𝔖.chernClass X' ((Scheme.Modules.pullback (S.map f)).obj E) r hE' j := by
  set E' := (Scheme.Modules.pullback (S.map f)).obj E
  obtain ⟨g, hg, htw⟩ := 𝔖.exists_bundleCompare X X' f E r hE hE'
  have hcomp : ∀ a : 𝔖.A X, 𝔖.pull g (𝔖.pull (𝔖.bundleDatum X E r hE).proj a) =
      𝔖.pull (𝔖.bundleDatum X' E' r hE').proj (𝔖.pull f a) := by
    intro a
    rw [← RingHom.comp_apply, ← 𝔖.pull_comp g (𝔖.bundleDatum X E r hE).proj, hg,
      𝔖.pull_comp (𝔖.bundleDatum X' E' r hE').proj f, RingHom.comp_apply]
  refine 𝔖.chernClass_eq_of_relation X' E' r hE'
    (fun k => 𝔖.pull f (𝔖.chernClass X E r hE k)) ?_ ?_ ?_ j
  · rw [𝔖.chernClass_zero X E r hE, map_one]
  · intro k hk
    rw [𝔖.chernClass_of_gt X E r hE hk, map_zero]
  · have hzero : 𝔖.pull g (∑ i : Fin (r + 2), ((-1 : ℤ) ^ (i : ℕ)) •
        (𝔖.c₁ (𝔖.bundleDatum X E r hE).bundle (𝔖.bundleDatum X E r hE).twistClass ^ (i : ℕ) *
          𝔖.pull (𝔖.bundleDatum X E r hE).proj
            (𝔖.chernClass X E r hE (r + 1 - (i : ℕ))))) = 0 := by
      rw [𝔖.sum_chernClass_eq_zero X E r hE, map_zero]
    rw [map_sum] at hzero
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) hzero
    rw [map_zsmul, map_mul, map_pow, htw, hcomp]

/-- **The total Chern class of a module of constant rank is compatible with pullback.** -/
theorem pull_chernSeries_coeff (X X' : C) (f : X' ⟶ X) (E : (S.obj X).Modules) (m : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E m)
    (hE' : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (S.map f)).obj E) m) (n : ℕ) :
    𝔖.pull f ((𝔖.chernSeries X E m hE).coeff n) =
      (𝔖.chernSeries X' ((Scheme.Modules.pullback (S.map f)).obj E) m hE').coeff n := by
  set E' := (Scheme.Modules.pullback (S.map f)).obj E
  revert hE hE'
  cases m with
  | zero =>
      intro hE hE'
      rw [𝔖.chernSeries_rank_zero X E hE, 𝔖.chernSeries_rank_zero X' E' hE']
      simp only [UnitalCentralSeries.coeff_one]
      split_ifs
      · exact map_one (𝔖.pull f)
      · exact map_zero (𝔖.pull f)
  | succ r =>
      intro hE hE'
      rw [𝔖.chernSeries_coeff_succ X E r hE n, 𝔖.chernSeries_coeff_succ X' E' r hE' n,
        𝔖.pull_chernClass X X' f E r hE hE' n]


/-- **Property (3) of Tag 0FI5 for a single invertible module**: `c^A(ℒ) = 1 + c₁^A(ℒ)`.
The projective bundle of an invertible module has a tautological sequence whose kernel has rank
zero, so `𝒪_P(1)` is the pullback of `ℒ`; condition (3) identifies `c₁^A(𝒪_P(1))` with
`p^*c₁^A(ℒ)`, and the single entry of the Chern tuple is the class `p^*` carries to
`c₁^A(𝒪_P(1))`. -/
theorem chernSeries_coeff_invertible (X : C) (L : (S.obj X).Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj X).presheaf
      (S.obj X).ringCatSheaf.2 L)
    (h1 : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1) (n : ℕ) :
    (𝔖.chernSeries X L 1 h1).coeff n =
      if n = 0 then 1 else
        if n = 1 then 𝔖.c₁ X (picardClassOf (S.obj X) L hL) else 0 := by
  have hquot : IsIso (𝔖.bundleDatum X L 0 h1).quot := by
    have hsub : IsZero (𝔖.bundleDatum X L 0 h1).sub :=
      isZero_of_isFiniteLocallyFreeOfRank_zero _ (𝔖.bundleDatum X L 0 h1).sub_rank
    have hincl : (𝔖.bundleDatum X L 0 h1).incl = 0 := hsub.eq_zero_of_src _
    have hmono : Mono (𝔖.bundleDatum X L 0 h1).quot :=
      (ShortComplex.exact_iff_mono _ hincl).1 (𝔖.bundleDatum X L 0 h1).shortExact.exact
    have hepi : Epi (𝔖.bundleDatum X L 0 h1).quot :=
      (𝔖.bundleDatum X L 0 h1).shortExact.epi_g
    exact isIso_of_mono_of_epi _
  have hkey : 𝔖.chernTuple X L 0 h1 0 = 𝔖.c₁ X (picardClassOf (S.obj X) L hL) := by
    refine 𝔖.injective_pull_proj X L 0 h1 ?_
    have hbf := 𝔖.bundleFormula_chernTuple X L 0 h1
    rw [ChernSetup.bundleFormula, Fin.sum_univ_one] at hbf
    have htop : 𝔖.topTerm X L 0 h1 =
        𝔖.c₁ (𝔖.bundleDatum X L 0 h1).bundle (𝔖.bundleDatum X L 0 h1).twistClass := by
      rw [𝔖.topTerm_eq_neg_smul_pow X L 0 h1]
      simp
    rw [htop] at hbf
    simp only [Fin.val_zero, pow_zero, one_mul] at hbf
    rw [hbf, 𝔖.pull_c₁ (𝔖.bundleDatum X L 0 h1).proj L hL (𝔖.bundleDatum X L 0 h1).twist
      (𝔖.bundleDatum X L 0 h1).twist_isInvertible (asIso (𝔖.bundleDatum X L 0 h1).quot)]
    rfl
  rw [𝔖.chernSeries_coeff_succ X L 0 h1 n]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [𝔖.chernClass_zero X L 0 h1, ite_eq_left rfl]
  rcases le_or_gt n 1 with hle | hgt
  · have hn1 : n = 1 := by omega
    subst hn1
    rw [𝔖.chernClass_of_le X L 0 h1 (by omega) (by omega), ite_eq_right one_ne_zero,
      ite_eq_left rfl]
    simpa using hkey
  · rw [𝔖.chernClass_of_gt X L 0 h1 (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

end ChernSituation

end Stacks.WeilCohomology

end
