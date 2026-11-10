module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.StandingSituation
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.WeakChernClasses.RankReduction
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.WeakChernClasses.WhitneyFormula

/-!
# The standing situation of Stacks Section 45.12 in the weak setting

The standing situation of Stacks Section 45.12, with the clauses `ChernSetup` leaves out, over
`Stacks.WeilCohomology.Weak.ChernSetup`: the projective bundle formula, condition (4), is only
asked to be injective and to resolve the top power `c₁^A(𝒪_P(1))^{r+1}` of the twist class. The
results use condition (4) only through these two properties.

## References

* [Stacks Project, Tag 0FI4](https://stacks.math.columbia.edu/tag/0FI4)
* [Stacks Project, Tag 0FI5](https://stacks.math.columbia.edu/tag/0FI5)
* [Stacks Project, Tag 0ESW](https://stacks.math.columbia.edu/tag/0ESW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v v₁ w

namespace Stacks.WeilCohomology.Weak

/-- **The standing situation of Stacks Section 45.12.** `Stacks.WeilCohomology.Weak.ChernSetup`
together with the clauses and conditions of the section it does not record: condition (3) as the
source states it, condition (4) read with the grading, clause (3)(b), and clause (3)(c) with
condition (5).

What each field is, and which of them carry a fact the source proves elsewhere rather than
assumes, is set out in the module documentation. -/
structure ChernSituation (C : Type w) [Category.{v₁} C] (S : C ⥤ Scheme.{u})
    extends ChernSetup.{u, v, v₁, w} C S where
  /-- **Condition (3), exactly as the source states it.** `f^*c₁^A(ℒ) = c₁^A(f^*ℒ)`.

  The invertible module on the source is `f^*ℒ` itself and not an arbitrary module isomorphic to
  it: that refinement is `Stacks.WeilCohomology.Weak.ChernSituation.pull_c₁`, a theorem, because
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
  it is the theorem `Stacks.WeilCohomology.Weak.ChernSituation.chernSeries_eq_of_iso`, which gets
  the invariance of the total Chern class under an isomorphism out of multiplicativity in the short
  exact sequence `0 ⟶ ℰ ⟶ ℰ' ⟶ 0 ⟶ 0` instead of out of a comparison of projective bundles.

  The identification of twists is the theorem
  `Stacks.WeilCohomology.Weak.ChernSituation.exists_bundleCompare`. -/
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
  closed immersion `𝐏(𝓕) ⟶ 𝐏(ℰ)` is a morphism of `𝒞`. The identification of twists is the
  theorem `Stacks.WeilCohomology.Weak.ChernSituation.exists_divisorDatum`, from
  `Stacks.Chow.GenuineChern.bundleEmbeddingTwistIso`.

  **Condition (5) is stated at `c₁^A(𝒪_P(𝐏(𝓕)))`**, where `𝒪_P(𝐏(𝓕))` is characterized
  divisor-theoretically — `Stacks.WeilCohomology.IsSubbundleDivisorModule`: an invertible module
  on `𝐏(ℰ)` with a section whose zero scheme is a relative effective Cartier divisor over the
  base, identified with `𝐏(𝓕)`. `𝒪_P(1)` does not occur in it. The source's identification
  `𝒪_P(𝐏(𝓕)) ≅ 𝒪_P(1) ⊗ (p^*ℒ)^{⊗ -1}` is the theorem
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
`Stacks.WeilCohomology.Weak.ChernSituation` together with the one further condition Tag 0FI9
reads the section under: `A(X)` is a `𝐐`-algebra for every object `X` of `𝒞`, compatibly with the
grading `A` takes its values in, so that the rationals lie in `A^0(X)`.

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

`Stacks.WeilCohomology.Weak.ChernSetup` records the data the source fixes together with clause
(1), clause (2), clause (3)(a), condition (1), condition (2), condition (4) and the grading. The
three `Prop`s below are the rest of Section 45.12, each in the source's own form, and
`Stacks.WeilCohomology.Weak.chernSituationOfSource` assembles them into a
`Stacks.WeilCohomology.Weak.ChernSituation`. -/

section OfSource

variable {C : Type w} [Category.{v₁} C] {S : C ⥤ Scheme.{u}}

/-- **Condition (3) of Section 45.12**, exactly as the source states it:
`f^*c₁^A(ℒ) = c₁^A(f^*ℒ)`, at `f^*ℒ` itself. -/
def PullbackFirstChernCondition (𝔚 : ChernSetup.{u, v, v₁, w} C S) : Prop :=
  ∀ {X Y : C} (f : X ⟶ Y) (L : (S.obj Y).Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj Y).presheaf
      (S.obj Y).ringCatSheaf.2 L),
    𝔚.pull f (𝔚.c₁ Y (picardClassOf (S.obj Y) L hL)) =
      𝔚.c₁ X (picardClassOf (S.obj X) ((Scheme.Modules.pullback (S.map f)).obj L)
        (isInvertible_pullback_obj (S.map f) L hL))

/-- **Clause (3)(b) of Section 45.12, exactly as the source states it**: for `f : X' ⟶ X` in `𝒞`
the induced morphism `𝐏(f^*ℰ) ⟶ 𝐏(ℰ)` is a morphism of `𝒞`, which is
`Stacks.WeilCohomology.IsBundleCompare` — over `f`, and the constructed
`Stacks.Chow.bundleBaseChangeHom` on schemes. Nothing about twists, and the module on `X'` is
`f^*ℰ` itself rather than an arbitrary module isomorphic to it. The field
`Stacks.WeilCohomology.Weak.ChernSituation.exists_bundleCompare_bundleObject` records why the
arbitrary-isomorphism form is not assumed and where the development gets it instead. -/
def BundleCompareClause (𝔚 : ChernSetup.{u, v, v₁, w} C S) : Prop :=
  ∀ (X X' : C) (f : X' ⟶ X) (E : (S.obj X).Modules) (r : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1))
    (hE' : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (S.map f)).obj E) (r + 1)),
      ∃ g : (𝔚.bundleObject X' ((Scheme.Modules.pullback (S.map f)).obj E) r hE').bundle ⟶
          (𝔚.bundleObject X E r hE).bundle,
        IsBundleCompare f (𝔚.bundleObject X E r hE)
          (𝔚.bundleObject X' ((Scheme.Modules.pullback (S.map f)).obj E) r hE') (Iso.refl _) g

/-- **Clause (3)(c) of Section 45.12 together with condition (5)**, both as the source states
them: the induced closed immersion `𝐏(𝓕) ⟶ 𝐏(ℰ)` is a morphism of `𝒞`
(`Stacks.WeilCohomology.IsBundleEmbedding`), and a class of `A(𝐏(ℰ))` killed by `i^*` is killed by
multiplication with `c₁^A(𝒪_P(𝐏(𝓕)))`, read at the divisor module characterized
divisor-theoretically by `Stacks.WeilCohomology.IsSubbundleDivisorModule`. `𝒪_P(1)` does not occur
in it. -/
def DivisorDatumClause (𝔚 : ChernSetup.{u, v, v₁, w} C S) : Prop :=
  ∀ (X : C) (T : ShortComplex (S.obj X).Modules) (hT : T.ShortExact)
    (_hL : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj X).presheaf
      (S.obj X).ringCatSheaf.2 T.X₁) (r : ℕ)
    (hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} T.X₃ (r + 1))
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} T.X₂
      (r + 1 + 1)),
      ∃ i : (𝔚.bundleObject X T.X₃ r hF).bundle ⟶ (𝔚.bundleObject X T.X₂ (r + 1) hE).bundle,
        IsBundleEmbedding T hT (𝔚.bundleObject X T.X₂ (r + 1) hE)
            (𝔚.bundleObject X T.X₃ r hF) i ∧
          ∀ (L : (@Stacks.Chow.bundle (S.obj X) T.X₂
              (𝔚.bundleObject X T.X₂ (r + 1) hE).isFiniteLocallyFree).Modules)
            (hLinv : AlgebraicGeometry.SheafOfModules.IsInvertible
              (@Stacks.Chow.bundle (S.obj X) T.X₂
                (𝔚.bundleObject X T.X₂ (r + 1) hE).isFiniteLocallyFree).presheaf
              (@Stacks.Chow.bundle (S.obj X) T.X₂
                (𝔚.bundleObject X T.X₂ (r + 1) hE).isFiniteLocallyFree).ringCatSheaf.2 L),
            IsSubbundleDivisorModule T hT
              (𝔚.bundleObject X T.X₂ (r + 1) hE).isFiniteLocallyFree
              (𝔚.bundleObject X T.X₃ r hF).isFiniteLocallyFree L hLinv →
            ∀ a : 𝔚.A (𝔚.bundleObject X T.X₂ (r + 1) hE).bundle, 𝔚.pull i a = 0 →
              a * 𝔚.c₁ (𝔚.bundleObject X T.X₂ (r + 1) hE).bundle
                (picardClassOf (S.obj (𝔚.bundleObject X T.X₂ (r + 1) hE).bundle)
                  ((Scheme.Modules.pullback
                      (𝔚.bundleObject X T.X₂ (r + 1) hE).iso.hom).obj L)
                  (isInvertible_pullback_obj _ L hLinv)) = 0

/-- **The standing situation of Stacks Section 45.12, built from the source's conditions.**

`Stacks.WeilCohomology.Weak.ChernSetup` together with condition (3), clause (3)(b), and clause
(3)(c) with condition (5). -/
def chernSituationOfSource (𝔚 : ChernSetup.{u, v, v₁, w} C S)
    (hpull : PullbackFirstChernCondition 𝔚) (hcompare : BundleCompareClause 𝔚)
    (hdivisor : DivisorDatumClause 𝔚) : ChernSituation.{u, v, v₁, w} C S where
  toChernSetup := 𝔚
  pull_c₁_pullback := hpull
  exists_bundleCompare_bundleObject := hcompare
  exists_divisorDatum_bundleObject := hdivisor

/-- The `ChernSetup` underlying `chernSituationOfSource 𝔚 hpull hcompare hdivisor` is `𝔚`. -/
@[simp]
theorem chernSituationOfSource_toChernSetup (𝔚 : ChernSetup.{u, v, v₁, w} C S)
    (hpull : PullbackFirstChernCondition 𝔚) (hcompare : BundleCompareClause 𝔚)
    (hdivisor : DivisorDatumClause 𝔚) :
    (chernSituationOfSource 𝔚 hpull hcompare hdivisor).toChernSetup = 𝔚 := rfl

end OfSource

/-! ### Powers of a first Chern class are homogeneous -/

namespace ChernSetup

variable {C : Type w} [Category.{v₁} C] {S : C ⥤ Scheme.{u}}

/-- A power of a first Chern class lies in the degree equal to the exponent: `c₁^A(ℒ)` lies in
degree one and multiplication adds degrees. -/
theorem pow_c₁_mem_grade (𝔚 : ChernSetup.{u, v, v₁, w} C S) (X : C)
    (L : (S.obj X).picardGroup) (k : ℕ) : 𝔚.c₁ X L ^ k ∈ 𝔚.grade X k := by
  induction k with
  | zero => simpa using 𝔚.one_mem X
  | succ k ih => rw [pow_succ]; exact 𝔚.mul_mem X k 1 ih (𝔚.c₁_mem X L)

/-- **Condition (4) read with the grading: the tuple the projective bundle formula resolves a
class of `A^n(P)` into is homogeneous, with the `i`-th entry in `A^{n-i}(X)`.**

This is a **theorem**, not a condition: the projective bundle formula is graded and injective,
and `A = ⨁_{i ≥ 0} A^i` is `Stacks.WeilCohomology.Weak.ChernSetup.isInternal_grade`. It is what
the clause `c^A : K₀(Vect(X)) ⟶ ∏_{i ≥ 0} A^i(X)` of Tag 0FI5 consumes.

The argument. Decompose each `a i` into its homogeneous components and collect by *total* degree:
the tuple `b d` whose `i`-th entry is the degree-`(d - i)` component of `a i` has
`∑ c₁^A(𝒪_P(1))^i ∪ p^*(b d i) ∈ A^d(P)`, because `c₁^A(𝒪_P(1))^i` is of degree `i` and pullback
preserves degrees. Summing the `b d` over `d` recovers `a`, and the formula is additive in the
tuple, so `F(a) = ∑_d F(b d)` exhibits `F(a)` as a sum of homogeneous pieces of pairwise distinct
degrees. `F(a)` lies in `A^n(P)`, so uniqueness of the decomposition kills every `d ≠ n` and
`F(a) = F(b n)`; condition (4) is injective, so `a = b n`, whose `i`-th entry lies in
`A^{n-i}(X)`. -/
theorem mem_grade_of_bundleFormula (𝔚 : ChernSetup.{u, v, v₁, w} C S) (X : C)
    (E : (S.obj X).Modules) (r : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1))
    (a : Fin (r + 1) → 𝔚.A X) (n : ℕ)
    (h : (∑ i : Fin (r + 1),
        𝔚.c₁ (𝔚.bundleDatum X E r hE).bundle (𝔚.bundleDatum X E r hE).twistClass ^ (i : ℕ) *
          𝔚.pull (𝔚.bundleDatum X E r hE).proj (a i)) ∈
      𝔚.grade (𝔚.bundleDatum X E r hE).bundle n) :
    ∀ (i : Fin (r + 1)) (k : ℕ), (i : ℕ) + k = n → a i ∈ 𝔚.grade X k := by
  classical
  let dX : DirectSum.Decomposition (𝔚.grade X) :=
    (𝔚.isInternal_grade X).chooseDecomposition _
  let dP : DirectSum.Decomposition (𝔚.grade (𝔚.bundleDatum X E r hE).bundle) :=
    (𝔚.isInternal_grade (𝔚.bundleDatum X E r hE).bundle).chooseDecomposition _
  set D : Fin (r + 1) → DirectSum ℕ (fun d => (𝔚.grade X d : Type v)) :=
    fun i => DirectSum.decompose (𝔚.grade X) (a i) with hD
  set N : ℕ :=
    max ((Finset.univ.biUnion fun i : Fin (r + 1) => (D i).support).sup id + r + 1) (n + 1)
    with hN
  set b : ℕ → Fin (r + 1) → 𝔚.A X :=
    fun d i => if (i : ℕ) ≤ d then ((D i (d - (i : ℕ)) : 𝔚.grade X (d - (i : ℕ))) : 𝔚.A X) else 0
    with hb
  have hbval : ∀ (d : ℕ) (i : Fin (r + 1)), (i : ℕ) ≤ d →
      b d i = ((D i (d - (i : ℕ)) : 𝔚.grade X (d - (i : ℕ))) : 𝔚.A X) := by
    intro d i hid
    simp only [hb, ite_eq_left hid]
  have hbmem : ∀ (d : ℕ) (i : Fin (r + 1)), (i : ℕ) ≤ d → b d i ∈ 𝔚.grade X (d - (i : ℕ)) := by
    intro d i hid
    rw [hbval d i hid]
    exact (D i (d - (i : ℕ))).2
  have hb0 : ∀ (d : ℕ) (i : Fin (r + 1)), ¬ (i : ℕ) ≤ d → b d i = 0 := by
    intro d i hid
    simp only [hb, ite_eq_right hid]
  have hNn : n < N := lt_of_lt_of_le (Nat.lt_succ_self n) (le_max_right _ _)
  have hFb : ∀ d : ℕ, 𝔚.bundleFormula X E r hE (b d) ∈
      𝔚.grade (𝔚.bundleDatum X E r hE).bundle d := by
    intro d
    rw [ChernSetup.bundleFormula]
    refine AddSubgroup.sum_mem _ fun i _ => ?_
    rcases le_or_gt (i : ℕ) d with hid | hid
    · have hmul := 𝔚.mul_mem (𝔚.bundleDatum X E r hE).bundle (i : ℕ) (d - (i : ℕ))
        (𝔚.pow_c₁_mem_grade (𝔚.bundleDatum X E r hE).bundle
          (𝔚.bundleDatum X E r hE).twistClass (i : ℕ))
        (𝔚.pull_grade (𝔚.bundleDatum X E r hE).proj (d - (i : ℕ)) (hbmem d i hid))
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
        b ((i : ℕ) + e) i = ((D i e : 𝔚.grade X e) : 𝔚.A X) := by
      intro e _
      rw [hbval _ i (Nat.le_add_right (i : ℕ) e), Nat.add_sub_cancel_left]
    rw [Finset.sum_congr rfl hval]
    refine Eq.trans (Finset.sum_subset (fun e he => ?_) (fun e _ hes => ?_)).symm
      (DirectSum.sum_support_decompose (𝔚.grade X) (a i))
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
  have hadd : ∑ d ∈ Finset.range N, 𝔚.bundleFormula X E r hE (b d) =
      𝔚.bundleFormula X E r hE a := by
    rw [ChernSetup.bundleFormula]
    have hstep : ∀ d : ℕ, 𝔚.bundleFormula X E r hE (b d) =
        ∑ i : Fin (r + 1),
          𝔚.c₁ (𝔚.bundleDatum X E r hE).bundle (𝔚.bundleDatum X E r hE).twistClass ^ (i : ℕ) *
            𝔚.pull (𝔚.bundleDatum X E r hE).proj (b d i) := fun d => rfl
    rw [Finset.sum_congr rfl fun d _ => hstep d, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.mul_sum, ← map_sum, hsum i]
  have hn : 𝔚.bundleFormula X E r hE a ∈ 𝔚.grade (𝔚.bundleDatum X E r hE).bundle n := h
  have hvan : ∀ m ∈ Finset.range N, m ≠ n → 𝔚.bundleFormula X E r hE (b m) = 0 := by
    intro m hm hmn
    have h1 := DirectSum.decompose_of_mem_ne (𝔚.grade (𝔚.bundleDatum X E r hE).bundle) hn
      (Ne.symm hmn)
    have h2 := Finset.sum_eq_single m
      (fun d _ hdm => DirectSum.decompose_of_mem_ne (𝔚.grade (𝔚.bundleDatum X E r hE).bundle)
        (hFb d) hdm) (fun hmm => absurd hm hmm)
    rw [← hadd, DirectSum.decompose_sum, DFinsupp.finsetSum_apply,
      AddSubmonoidClass.coe_finsetSum, h2,
      DirectSum.decompose_of_mem_same _ (hFb m)] at h1
    exact h1
  have hFan : 𝔚.bundleFormula X E r hE a = 𝔚.bundleFormula X E r hE (b n) := by
    rw [← hadd]
    exact Finset.sum_eq_single n (fun d hd hdn => hvan d hd hdn)
      (fun hnn => absurd (Finset.mem_range.mpr hNn) hnn)
  have hab : a = b n := 𝔚.injective_bundleFormula' X E r hE hFan
  intro i k hik
  have hik' : (i : ℕ) ≤ n := by omega
  have hai : a i = b n i := by rw [hab]
  rw [hai, show k = n - (i : ℕ) from by omega]
  exact hbmem n i hik'

end ChernSetup

/-! ### The total Chern class of a module of constant rank -/

namespace ChernSituation

variable {C : Type w} [Category.{v₁} C] {S : C ⥤ Scheme.{u}}
  (𝔗 : ChernSituation.{u, v, v₁, w} C S)

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
    𝔗.pull f (𝔗.c₁ Y (picardClassOf (S.obj Y) L hL)) =
      𝔗.c₁ X (picardClassOf (S.obj X) L' hL') := by
  rw [𝔗.pull_c₁_pullback f L hL,
    picardClassOf_eq_of_iso (S.obj X) _ L' (isInvertible_pullback_obj (S.map f) L hL) hL' e]

/-! ### The two fields that mention the projective bundle, read at `bundleDatum`

Each field of the structure is stated at the clause-(3)(a) datum `bundleObject`, because a field
cannot mention `Stacks.WeilCohomology.Weak.ChernSetup.bundleDatum`, which is a definition on
`ChernSetup`. These two theorems are the same statements read at that definition, and they are
the form everything below and in the rest of this directory uses. They hold by
`Stacks.WeilCohomology.BundleObject.toBundleDatum_bundle`,
`Stacks.WeilCohomology.BundleObject.toBundleDatum_proj` and
`Stacks.WeilCohomology.BundleObject.toBundleDatum_twistClass`. -/

/-- **Clause (3)(b) with the identification of twists: `g^*c₁^A(𝒪_P(1)) = c₁^A(𝒪_{P'}(1))`.**

This is a **theorem**, not a condition. The field `exists_bundleCompare_bundleObject` is the
source's clause (3)(b) alone — the induced morphism `𝐏(f^*ℰ) ⟶ 𝐏(ℰ)` is a morphism of `𝒞`. That
it carries `c₁^A(𝒪_{𝐏(ℰ)}(1))` to `c₁^A(𝒪_{𝐏(f^*ℰ)}(1))` comes from
`Stacks.WeilCohomology.BundleObject.nonempty_pullback_twist_of_isBundleCompare` — the base change
of the twist, `Stacks.Chow.bundleBaseChange` — together with condition (3) in the form
`Stacks.WeilCohomology.Weak.ChernSituation.pull_c₁`. -/
theorem exists_bundleCompare (X X' : C) (f : X' ⟶ X) (E : (S.obj X).Modules) (r : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1))
    (hE' : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (S.map f)).obj E) (r + 1)) :
    ∃ g : (𝔗.bundleDatum X' ((Scheme.Modules.pullback (S.map f)).obj E) r hE').bundle ⟶
        (𝔗.bundleDatum X E r hE).bundle,
      g ≫ (𝔗.bundleDatum X E r hE).proj =
          (𝔗.bundleDatum X' ((Scheme.Modules.pullback (S.map f)).obj E) r hE').proj ≫ f ∧
        𝔗.pull g (𝔗.c₁ (𝔗.bundleDatum X E r hE).bundle (𝔗.bundleDatum X E r hE).twistClass) =
          𝔗.c₁ (𝔗.bundleDatum X' ((Scheme.Modules.pullback (S.map f)).obj E) r hE').bundle
            (𝔗.bundleDatum X' ((Scheme.Modules.pullback (S.map f)).obj E) r hE').twistClass := by
  obtain ⟨g, hg⟩ := 𝔗.exists_bundleCompare_bundleObject X X' f E r hE hE'
  obtain ⟨φ⟩ := BundleObject.nonempty_pullback_twist_of_isBundleCompare f
    (𝔗.bundleObject X E r hE)
    (𝔗.bundleObject X' ((Scheme.Modules.pullback (S.map f)).obj E) r hE') (Iso.refl _) g hg
  exact ⟨g, hg.comp_proj,
    𝔗.pull_c₁ g (𝔗.bundleObject X E r hE).twist (𝔗.bundleObject X E r hE).twist_isInvertible
      (𝔗.bundleObject X' ((Scheme.Modules.pullback (S.map f)).obj E) r hE').twist
      (𝔗.bundleObject X' ((Scheme.Modules.pullback (S.map f)).obj E) r hE').twist_isInvertible φ⟩

/-- **Clause (3)(c) with the identification of twists, together with condition (5).**

The identification `i^*c₁^A(𝒪_P(1)) = c₁^A(𝒪_{P'}(1))` is not assumed: the field
`exists_divisorDatum_bundleObject` carries only the closure property clause (3)(c) states, and
`Stacks.WeilCohomology.BundleObject.nonempty_pullback_twist_of_isBundleEmbedding` —
`Stacks.Chow.GenuineChern.bundleEmbeddingTwistIso` carried through the clause-(3)(a)
identifications — with condition (3) in the form
`Stacks.WeilCohomology.Weak.ChernSituation.pull_c₁` supplies it. Condition (5) is read at the
explicit class `𝒪_P(1) ⊗ (p^*ℒ)^{⊗ -1}` through
`Stacks.WeilCohomology.BundleObject.twistClass_eq_picardClassOf_add`. -/
theorem exists_divisorDatum (X : C) (T : ShortComplex (S.obj X).Modules) (hT : T.ShortExact)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj X).presheaf
      (S.obj X).ringCatSheaf.2 T.X₁) (r : ℕ)
    (hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} T.X₃ (r + 1))
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} T.X₂
      (r + 1 + 1)) :
    ∃ i : (𝔗.bundleDatum X T.X₃ r hF).bundle ⟶ (𝔗.bundleDatum X T.X₂ (r + 1) hE).bundle,
      i ≫ (𝔗.bundleDatum X T.X₂ (r + 1) hE).proj = (𝔗.bundleDatum X T.X₃ r hF).proj ∧
        𝔗.pull i (𝔗.c₁ (𝔗.bundleDatum X T.X₂ (r + 1) hE).bundle
            (𝔗.bundleDatum X T.X₂ (r + 1) hE).twistClass) =
          𝔗.c₁ (𝔗.bundleDatum X T.X₃ r hF).bundle (𝔗.bundleDatum X T.X₃ r hF).twistClass ∧
        ∀ a : 𝔗.A (𝔗.bundleDatum X T.X₂ (r + 1) hE).bundle, 𝔗.pull i a = 0 →
          a * 𝔗.c₁ (𝔗.bundleDatum X T.X₂ (r + 1) hE).bundle
              ((𝔗.bundleDatum X T.X₂ (r + 1) hE).twistClass -
                picardClassOf (S.obj (𝔗.bundleDatum X T.X₂ (r + 1) hE).bundle)
                  ((Scheme.Modules.pullback
                      (S.map (𝔗.bundleDatum X T.X₂ (r + 1) hE).proj)).obj T.X₁)
                  (isInvertible_pullback_obj _ T.X₁ hL)) = 0 := by
  obtain ⟨i, hi, hdiv⟩ := 𝔗.exists_divisorDatum_bundleObject X T hT hL r hF hE
  obtain ⟨φ⟩ := BundleObject.nonempty_pullback_twist_of_isBundleEmbedding T hT
    (𝔗.bundleObject X T.X₂ (r + 1) hE) (𝔗.bundleObject X T.X₃ r hF) i hi
  obtain ⟨L, hLinv, hdivmod, ⟨eT⟩⟩ := exists_isSubbundleDivisorModule T hT hL r hF
    (𝔗.bundleObject X T.X₂ (r + 1) hE).isFiniteLocallyFree
    (𝔗.bundleObject X T.X₃ r hF).isFiniteLocallyFree
  have hclass := eq_sub_of_add_eq'
    ((𝔗.bundleObject X T.X₂ (r + 1) hE).twistClass_eq_picardClassOf_add T.X₁ hL L hLinv eT)
  refine ⟨i, hi.comp_proj,
    𝔗.pull_c₁ i (𝔗.bundleObject X T.X₂ (r + 1) hE).twist
      (𝔗.bundleObject X T.X₂ (r + 1) hE).twist_isInvertible
      (𝔗.bundleObject X T.X₃ r hF).twist (𝔗.bundleObject X T.X₃ r hF).twist_isInvertible φ,
    fun a ha => ?_⟩
  have h := hdiv L hLinv hdivmod a ha
  rwa [hclass] at h

/-- **The first Chern class of the divisor class of `𝐏(𝓕) ⊂ 𝐏(ℰ)` is
`c₁^A(𝒪_P(1)) - p^*c₁^A(ℒ)`.**

Condition (5) is carried in `exists_divisorDatum` at the class `𝒪_P(1) ⊗ (p^*ℒ)^{⊗ -1}` of
`Pic(𝐏(ℰ))`, which is what the source's `𝒪_P(𝐏(𝓕))` is. Its first Chern class is not a further
assumption: `c₁^A` is additive on `Pic(𝐏(ℰ))`, and condition (3) identifies `c₁^A(p^*ℒ)` with
`p^*c₁^A(ℒ)`. This is the form the Whitney computation
`Stacks.WeilCohomology.Weak.ChernSetup.chernClass_add_one_of_invertibleSub` consumes. -/
theorem c₁_divisorClass (X : C) (L : (S.obj X).Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj X).presheaf
      (S.obj X).ringCatSheaf.2 L) (E : (S.obj X).Modules) (r : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1)) :
    𝔗.c₁ (𝔗.bundleDatum X E r hE).bundle
        ((𝔗.bundleDatum X E r hE).twistClass -
          picardClassOf (S.obj (𝔗.bundleDatum X E r hE).bundle)
            ((Scheme.Modules.pullback (S.map (𝔗.bundleDatum X E r hE).proj)).obj L)
            (isInvertible_pullback_obj _ L hL)) =
      𝔗.c₁ (𝔗.bundleDatum X E r hE).bundle (𝔗.bundleDatum X E r hE).twistClass -
        𝔗.pull (𝔗.bundleDatum X E r hE).proj (𝔗.c₁ X (picardClassOf (S.obj X) L hL)) := by
  rw [map_sub, 𝔗.pull_c₁ (𝔗.bundleDatum X E r hE).proj L hL _
    (isInvertible_pullback_obj _ L hL) (Iso.refl _)]

/-- **The total Chern class of a finite locally free module of constant rank**, as an element of
the group of unital central series: `1` in rank zero, and `1 + c_1^A(ℰ) + … + c_r^A(ℰ)` in rank
`r + 1`. The components are central by
`Stacks.WeilCohomology.Weak.ChernSetup.chernClass_central` and the constant term is `1` by
`Stacks.WeilCohomology.Weak.ChernSetup.chernClass_zero`. -/
def chernSeries (X : C) (E : (S.obj X).Modules) (m : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E m) :
    UnitalCentralSeries (𝔗.A X) :=
  match m, hE with
  | 0, _ => 1
  | (r + 1), hE =>
      UnitalCentralSeries.ofCoeff (𝔗.chernClass X E r hE)
        (fun n => Subring.mem_center_iff.2 fun b => (𝔗.chernClass_central X E r hE n b).symm)
        (𝔗.chernClass_zero X E r hE)

/-- A module of rank zero has total Chern class `1`. -/
theorem chernSeries_rank_zero (X : C) (E : (S.obj X).Modules)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E 0) :
    𝔗.chernSeries X E 0 hE = 1 := rfl

/-- In positive rank the components of the total Chern class are the Chern classes. -/
theorem chernSeries_coeff_succ (X : C) (E : (S.obj X).Modules) (r : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1))
    (n : ℕ) : (𝔗.chernSeries X E (r + 1) hE).coeff n = 𝔗.chernClass X E r hE n := by
  have h : 𝔗.chernSeries X E (r + 1) hE =
      UnitalCentralSeries.ofCoeff (𝔗.chernClass X E r hE)
        (fun k => Subring.mem_center_iff.2 fun b => (𝔗.chernClass_central X E r hE k b).symm)
        (𝔗.chernClass_zero X E r hE) := rfl
  rw [h, UnitalCentralSeries.coeff_ofCoeff]

/-- **The total Chern class does not depend on the rank witness.** Two constant ranks of one
module agree as soon as the object has a point, and if it has none then `A(X)` is the zero ring by
condition (2) at the empty decomposition. -/
theorem chernSeries_eq_of_rank (X : C) (E : (S.obj X).Modules) (m m' : ℕ)
    (hm : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E m)
    (hm' : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E m') :
    𝔗.chernSeries X E m hm = 𝔗.chernSeries X E m' hm' := by
  rcases isEmpty_or_nonempty (S.obj X) with hX | hX
  · exact (UnitalCentralSeries.subsingleton (𝔗.subsingleton_of_isEmpty X hX)).elim _ _
  · obtain ⟨x⟩ := hX
    have hmm : m = m' :=
      AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_unique E hm hm' x
    subst hmm
    rfl

/-- `topTerm` unfolds to `-((-1)^(r+1) • c₁^A(𝒪_P(1))^(r+1))`. -/
private theorem topTerm_eq (X : C) (E : (S.obj X).Modules) (r : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1)) :
    𝔗.topTerm X E r hE =
      -(((-1 : ℤ) ^ (r + 1)) •
        𝔗.c₁ (𝔗.bundleDatum X E r hE).bundle (𝔗.bundleDatum X E r hE).twistClass ^ (r + 1)) :=
  rfl

/-- **The Chern classes are homogeneous**: `c_j^A(ℰ) ∈ A^j(X)`. The element the projective bundle
formula resolves is `-(-1)^{r+1} c₁^A(𝒪_P(1))^{r+1}`, which lies in `A^{r+1}(P)`; so the tuple it
resolves to has its `i`-th entry in `A^{r+1-i}(X)` by condition (4) read with the grading, and
`c_j^A(ℰ)` is, up to sign, the entry at `i = r + 1 - j`. -/
theorem chernClass_mem_grade (X : C) (E : (S.obj X).Modules) (r : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1))
    (j : ℕ) : 𝔗.chernClass X E r hE j ∈ 𝔗.grade X j := by
  have htop : 𝔗.topTerm X E r hE ∈
      𝔗.grade (𝔗.bundleDatum X E r hE).bundle (r + 1) := by
    rw [topTerm_eq]
    exact AddSubgroup.neg_mem _ (AddSubgroup.zsmul_mem _
      (𝔗.pow_c₁_mem_grade (𝔗.bundleDatum X E r hE).bundle
        (𝔗.bundleDatum X E r hE).twistClass (r + 1)) _)
  have htuple : ∀ (i : Fin (r + 1)) (k : ℕ), (i : ℕ) + k = r + 1 →
      𝔗.chernTuple X E r hE i ∈ 𝔗.grade X k := by
    refine 𝔗.mem_grade_of_bundleFormula X E r hE (𝔗.chernTuple X E r hE) (r + 1) ?_
    change 𝔗.bundleFormula X E r hE (𝔗.chernTuple X E r hE) ∈ _
    rw [𝔗.bundleFormula_chernTuple X E r hE]
    exact htop
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [𝔗.chernClass_zero X E r hE]
    exact 𝔗.one_mem X
  rcases le_or_gt j (r + 1) with hle | hgt
  · rw [𝔗.chernClass_of_le X E r hE (by omega) hle]
    exact AddSubgroup.zsmul_mem _ (htuple ⟨r + 1 - j, by omega⟩ j (by simp; omega)) _
  · rw [𝔗.chernClass_of_gt X E r hE hgt]
    exact AddSubgroup.zero_mem _

/-- **The Chern classes are compatible with pullback**, which is the source's
`f^*c_i^A(ℰ) = c_i^A(f^*ℰ)`. Clause (3)(b) supplies a morphism `g : 𝐏(f^*ℰ) ⟶ 𝐏(ℰ)` over `f`
carrying `c₁^A(𝒪_P(1))` to `c₁^A(𝒪_{P'}(1))`; pulling equation 45.12.1.1 for `ℰ` back along `g`
is equation 45.12.1.1 for `f^*ℰ` with the family `f^*c_i^A(ℰ)`, which therefore is the family of
Chern classes of `f^*ℰ` by
`Stacks.WeilCohomology.Weak.ChernSetup.chernClass_eq_of_relation`. -/
theorem pull_chernClass (X X' : C) (f : X' ⟶ X) (E : (S.obj X).Modules) (r : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1))
    (hE' : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (S.map f)).obj E) (r + 1)) (j : ℕ) :
    𝔗.pull f (𝔗.chernClass X E r hE j) =
      𝔗.chernClass X' ((Scheme.Modules.pullback (S.map f)).obj E) r hE' j := by
  set E' := (Scheme.Modules.pullback (S.map f)).obj E
  obtain ⟨g, hg, htw⟩ := 𝔗.exists_bundleCompare X X' f E r hE hE'
  have hcomp : ∀ a : 𝔗.A X, 𝔗.pull g (𝔗.pull (𝔗.bundleDatum X E r hE).proj a) =
      𝔗.pull (𝔗.bundleDatum X' E' r hE').proj (𝔗.pull f a) := by
    intro a
    rw [← RingHom.comp_apply, ← 𝔗.pull_comp g (𝔗.bundleDatum X E r hE).proj, hg,
      𝔗.pull_comp (𝔗.bundleDatum X' E' r hE').proj f, RingHom.comp_apply]
  refine 𝔗.chernClass_eq_of_relation X' E' r hE'
    (fun k => 𝔗.pull f (𝔗.chernClass X E r hE k)) ?_ ?_ ?_ j
  · rw [𝔗.chernClass_zero X E r hE, map_one]
  · intro k hk
    rw [𝔗.chernClass_of_gt X E r hE hk, map_zero]
  · have hzero : 𝔗.pull g (∑ i : Fin (r + 2), ((-1 : ℤ) ^ (i : ℕ)) •
        (𝔗.c₁ (𝔗.bundleDatum X E r hE).bundle (𝔗.bundleDatum X E r hE).twistClass ^ (i : ℕ) *
          𝔗.pull (𝔗.bundleDatum X E r hE).proj
            (𝔗.chernClass X E r hE (r + 1 - (i : ℕ))))) = 0 := by
      rw [𝔗.sum_chernClass_eq_zero X E r hE, map_zero]
    rw [map_sum] at hzero
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) hzero
    rw [map_zsmul, map_mul, map_pow, htw, hcomp]

/-- **The total Chern class of a module of constant rank is compatible with pullback.** -/
theorem pull_chernSeries_coeff (X X' : C) (f : X' ⟶ X) (E : (S.obj X).Modules) (m : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E m)
    (hE' : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (S.map f)).obj E) m) (n : ℕ) :
    𝔗.pull f ((𝔗.chernSeries X E m hE).coeff n) =
      (𝔗.chernSeries X' ((Scheme.Modules.pullback (S.map f)).obj E) m hE').coeff n := by
  set E' := (Scheme.Modules.pullback (S.map f)).obj E
  revert hE hE'
  cases m with
  | zero =>
      intro hE hE'
      rw [𝔗.chernSeries_rank_zero X E hE, 𝔗.chernSeries_rank_zero X' E' hE']
      simp only [UnitalCentralSeries.coeff_one]
      split_ifs
      · exact map_one (𝔗.pull f)
      · exact map_zero (𝔗.pull f)
  | succ r =>
      intro hE hE'
      rw [𝔗.chernSeries_coeff_succ X E r hE n, 𝔗.chernSeries_coeff_succ X' E' r hE' n,
        𝔗.pull_chernClass X X' f E r hE hE' n]


/-- **Property (3) of Tag 0FI5 for a single invertible module**: `c^A(ℒ) = 1 + c₁^A(ℒ)`.
The projective bundle of an invertible module has a tautological sequence whose kernel has rank
zero, so `𝒪_P(1)` is the pullback of `ℒ`; condition (3) identifies `c₁^A(𝒪_P(1))` with
`p^*c₁^A(ℒ)`, and the single entry of the Chern tuple is the class `p^*` carries to
`c₁^A(𝒪_P(1))`. -/
theorem chernSeries_coeff_invertible (X : C) (L : (S.obj X).Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj X).presheaf
      (S.obj X).ringCatSheaf.2 L)
    (h1 : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1) (n : ℕ) :
    (𝔗.chernSeries X L 1 h1).coeff n =
      if n = 0 then 1 else
        if n = 1 then 𝔗.c₁ X (picardClassOf (S.obj X) L hL) else 0 := by
  have hquot : IsIso (𝔗.bundleDatum X L 0 h1).quot := by
    have hsub : IsZero (𝔗.bundleDatum X L 0 h1).sub :=
      isZero_of_isFiniteLocallyFreeOfRank_zero _ (𝔗.bundleDatum X L 0 h1).sub_rank
    have hincl : (𝔗.bundleDatum X L 0 h1).incl = 0 := hsub.eq_zero_of_src _
    have hmono : Mono (𝔗.bundleDatum X L 0 h1).quot :=
      (ShortComplex.exact_iff_mono _ hincl).1 (𝔗.bundleDatum X L 0 h1).shortExact.exact
    have hepi : Epi (𝔗.bundleDatum X L 0 h1).quot :=
      (𝔗.bundleDatum X L 0 h1).shortExact.epi_g
    exact isIso_of_mono_of_epi _
  have hkey : 𝔗.chernTuple X L 0 h1 0 = 𝔗.c₁ X (picardClassOf (S.obj X) L hL) := by
    refine 𝔗.injective_pull_proj X L 0 h1 ?_
    have hbf := 𝔗.bundleFormula_chernTuple X L 0 h1
    rw [ChernSetup.bundleFormula, Fin.sum_univ_one] at hbf
    have htop : 𝔗.topTerm X L 0 h1 =
        𝔗.c₁ (𝔗.bundleDatum X L 0 h1).bundle (𝔗.bundleDatum X L 0 h1).twistClass := by
      rw [topTerm_eq]
      simp
    rw [htop] at hbf
    simp only [Fin.val_zero, pow_zero, one_mul] at hbf
    rw [hbf, 𝔗.pull_c₁ (𝔗.bundleDatum X L 0 h1).proj L hL (𝔗.bundleDatum X L 0 h1).twist
      (𝔗.bundleDatum X L 0 h1).twist_isInvertible (asIso (𝔗.bundleDatum X L 0 h1).quot)]
    rfl
  rw [𝔗.chernSeries_coeff_succ X L 0 h1 n]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [𝔗.chernClass_zero X L 0 h1, ite_eq_left rfl]
  rcases le_or_gt n 1 with hle | hgt
  · have hn1 : n = 1 := by omega
    subst hn1
    rw [𝔗.chernClass_of_le X L 0 h1 (by omega) (by omega), ite_eq_right one_ne_zero,
      ite_eq_left rfl]
    simpa using hkey
  · rw [𝔗.chernClass_of_gt X L 0 h1 (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

end ChernSituation

end Stacks.WeilCohomology.Weak

end
