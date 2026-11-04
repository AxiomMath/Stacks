module

public import
  StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.AlgebraicFieldExtensionFiniteStageDivisibility
public import StacksFrontier.AlgebraicGeometry.ClosurePointDimension.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.BaseChange
public import
  StacksFrontier.AlgebraicGeometry.WeilCohomology.FurtherProperties.RationalPointsBaseChange
public import
  StacksFrontier.AlgebraicGeometry.WeilCohomology.FurtherProperties.RationalPointsCurveJacobian
public import
  StacksFrontier.AlgebraicGeometry.WeilCohomology.FurtherProperties.RationalPointsDimensionZero

/-!
# Stacks Tag 0FH7, assembled

Let `k` be a field, let `X` be a geometrically irreducible smooth proper scheme over `k`, let
`x, x'` be `k`-rational points of `X` and let `n` be an integer invertible in `k`. Then there is a
finite separable extension `K/k` over which the pullback of `[x] - [x']` is divisible by `n` in
`CH_0(X_K)`.

That is the statement of Stacks Tag 0FH7, and
`Stacks.WeilCohomology.exists_finiteSeparable_rationalPointChowClass_sub_eq_zsmul` below proves it
from three hypotheses the source does not have. The section "What this carries beyond the source"
lists them, says which tag would discharge each, and says where each is used. **The tag is
deliberately not registered on anything in this file**, precisely because of those three.

## The assembly

The three steps of the source's proof are already in this library, and this file is their
composition.

1. **Over the separable closure.** `Stacks.WeilCohomology.rationalPointDifferenceDivisible_one`
   proves the curve case, `Stacks.WeilCohomology.rationalPointDifferenceDivisible_of_dimOne`
   runs the induction on the dimension up from it and
   `Stacks.WeilCohomology.rationalPointDifferenceDivisible_zero` settles dimension zero
   separately, giving in every dimension a class `γ` of `CH_0(X_{k^sep})` with
   `[y] - [y'] = n γ` for the two induced `k^sep`-rational points `y, y'`.
2. **The two points base change to the two points.**
   `Stacks.WeilCohomology.baseChangeChowPullbackOfIsPullback_rationalPointChowClass_sub` identifies
   `[y] - [y']` with the flat base change of `[x] - [x']`, the induced points being the canonical
   lifts `pullback.lift (g ≫ x) (𝟙 _)`.
3. **Descent to a finite stage.**
   `Stacks.Chow.exists_finiteSeparable_baseChangeChowPullback_eq_zsmul`, which is Stacks Tag 0FH6
   applied to that one equation, replaces `k^sep` by a finite separable subextension.

## Main results

* `Stacks.WeilCohomology.exists_finiteSeparable_rationalPointChowClass_sub_eq_zsmul` — the
  conclusion of Stacks Tag 0FH7, with the three carried hypotheses explicit.

## What this carries beyond the source

Three hypotheses. Two of them are `Prop`-valued definitions that say exactly what they assert and
are documented at their own declarations; the third is already disclosed upstream. **No dimension
hypothesis is carried**: the statement below quantifies over exactly the schemes the tag does.

Three conditions that used to be here have been **discharged**, and the list below no longer
carries them or a number for them.

* That a smooth morphism with `topologicalKrullDim X = 1` is smooth of relative dimension one is
  the content of **Stacks Tags 01V9 and 02G1** — a smooth morphism is locally standard smooth, of
  relative dimension the fibre dimension — and is now proved by
  `Stacks.Curves.smoothOfRelativeDimension_one_of_topologicalKrullDim_eq_one`.
* That a proper smooth geometrically irreducible scheme over a field has that field for its ring
  of global functions is clause (7) of **Stacks Tag 0BUG**, as
  `Stacks.AlgebraicGeometry.ProperSectionsGeom.isIso_globalSections_of_isProper` carries it, and is
  now proved by `Stacks.WeilCohomology.curveHasOneDimensionalSections`.

The first two are supplied inside `Stacks.WeilCohomology.rationalPointDifferenceDivisible_one`,
which takes neither as an argument.

* The **dimension bookkeeping**, which used to be the binders `d : ℕ`, `hd : 1 ≤ d` and `hdim`
  pinning `topologicalKrullDim X` to `d`, is gone. `hd` is gone because dimension zero is now
  proved rather than excluded, by `Stacks.WeilCohomology.rationalPointDifferenceDivisible_zero`:
  a zero-dimensional proper smooth geometrically irreducible `k`-scheme has an isomorphism for its
  structure morphism (`AlgebraicGeometry.isIso_of_topologicalKrullDim_eq_zero`), hence a
  monomorphism, so the two points coincide and the difference is zero. `d` and `hdim` are gone
  because a nonempty proper scheme over a field has a natural-number dimension outright, by
  `AlgebraicGeometry.exists_topologicalKrullDim_eq_natCast_of_isProper`, and a `k`-rational point
  supplies the nonemptiness; the numeral the induction recurses on is produced inside the proof
  instead of being asked for. The induction itself is unchanged and is still based at dimension
  one, with dimension zero taken by the separate case; it is the *statement* that no longer
  mentions a dimension.

1. `hJac : Stacks.WeilCohomology.HasJacobianParametrizations (SeparableClosure k) n`.
   **Stacks Tag 0BA0** would discharge it: the degree-zero Picard group of a smooth proper curve is
   the group of rational points of an abelian variety. No declaration of that tag exists in any
   build target of this repository. Consumed inside
   `Stacks.WeilCohomology.rationalPointDifferenceDivisible_one`, to produce the abelian variety and
   the divisibility in `Pic(X)`. Satisfiable:
   `Stacks.WeilCohomology.jacobianParametrization_of_degreeZero_trivial`.

2. `h03RP`, the étale clause `Stacks.Groupoids.EtaleZPowIdOfIsUnit` of **Stacks Tag 03RP**:
   multiplication by an integer invertible in the ground field is étale on an abelian variety.
   Disclosed upstream and propagated here unchanged, not re-disclosed. Consumed by
   `Stacks.Groupoids.exists_comp_zpow_id_left_eq_of_isSepClosed`. Satisfiable:
   `Stacks.Groupoids.etaleZPowIdOfIsUnit_of_isIso_hom`.

3. `hBertini : Stacks.WeilCohomology.BertiniDivisorReduction (SeparableClosure k)`, the one-step
   geometric reduction of the induction: a smooth geometrically irreducible divisor of dimension
   one less through both points. This is the Bertini step of the proof of Stacks Tag 0FH7 itself,
   whose geometric input in this library is the depth condition of **Stacks Tag 0FD9**. Consumed by
   `Stacks.WeilCohomology.rationalPointDifferenceDivisible_succ`.

Two further deviations are in the direction that strengthens the statement rather than weakening
it, and are not hypotheses:

* properness is assumed in place of the source's projectivity, which is weaker
  (`AlgebraicGeometry.isProper_of_isProjectiveMorphism` supplies it from projectivity);
* `n` is an arbitrary integer and `hn` is the source's hypothesis that it is invertible in `k`,
  spent only where the source spends it.

## Implementation notes

`Stacks.Chow.fieldChowSituation k` is the Chow situation whose base is `Spec k`, so a `k`-rational
point is a section of `f` in the sense of `Stacks.WeilCohomology.rationalPointChowClass`, and the
flat base change along `k → k^sep` is read through the canonical cartesian square, i.e. through
`Stacks.Chow.baseChangeChowPullbackOfIsPullback` at the square
`CategoryTheory.IsPullback.of_hasPullback`. That is the square the descent of step 3 and the
point-class identification of step 2 both use, so no comparison between two presentations of the
base change is needed.

The three hypotheses `QuasiCompact`, `LocallyOfFiniteType` and `CompactSpace` that step 3 asks of
`Over.mk f` are supplied by hand rather than found by instance search, which does not see through
`CategoryTheory.Over.mk`; each is the corresponding instance for `f` itself, `CompactSpace` coming
from `AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace` over the compact base `Spec k`.

The invertibility of `n` is assumed over `k`, as the source assumes it, and transported to
`k^sep` by `IsUnit.map` along the structure map, the integer cast commuting with it.

The dimension is never a hypothesis but it is still needed twice inside the proof, and both uses
are discharged there. The numeral the induction recurses on comes from
`AlgebraicGeometry.exists_topologicalKrullDim_eq_natCast_of_isProper`, applied to `f` and to the
nonemptiness of `X` that the rational point `x` supplies. The induction of step 1 then runs over
`k^sep` and asks for the dimension of `X_{k^sep}`, not of `X`; that is supplied by
`AlgebraicGeometry.topologicalKrullDim_baseChange`, the dimension clause of **Stacks Tag 0BY9**,
which is the invariance of a *scheme*'s topological Krull dimension under base change along an
arbitrary extension of the ground field, for any scheme locally of finite type over it.
Properness, which is already assumed, supplies that finiteness, so the invariance costs this
statement no hypothesis.

No `@[stacks]` attribute appears in this file. Registering Stacks Tag 0FH7 here would assert the
tag's statement, and what is proved is the tag's statement *plus three hypotheses*; the
registration would therefore be false. The tags that are registered in this library for the
pieces used stay where they are: Stacks Tag 0FH6 on
`Stacks.Chow.chowColimitAddEquiv_algebraicExtensionSystem`, and so on.

## References

* [Stacks Project, Tag 01V9](https://stacks.math.columbia.edu/tag/01V9)
* [Stacks Project, Tag 02G1](https://stacks.math.columbia.edu/tag/02G1)
* [Stacks Project, Tag 03RP](https://stacks.math.columbia.edu/tag/03RP)
* [Stacks Project, Tag 0BA0](https://stacks.math.columbia.edu/tag/0BA0)
* [Stacks Project, Tag 0BUG](https://stacks.math.columbia.edu/tag/0BUG)
* [Stacks Project, Tag 0BY9](https://stacks.math.columbia.edu/tag/0BY9)
* [Stacks Project, Tag 0CKV](https://stacks.math.columbia.edu/tag/0CKV)
* [Stacks Project, Tag 0FD9](https://stacks.math.columbia.edu/tag/0FD9)
* [Stacks Project, Tag 0FH6](https://stacks.math.columbia.edu/tag/0FH6)
* [Stacks Project, Tag 0FH7](https://stacks.math.columbia.edu/tag/0FH7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

namespace Stacks.WeilCohomology

/-- Over a separably closed field, rational point differences are `n`-divisible in every
dimension. -/
theorem rationalPointDifferenceDivisible_of_isSepClosed (K : Type u) [Field K] [IsSepClosed K]
    (n : ℤ) (hn : IsUnit ((n : ℤ) : K))
    (h03RP : ∀ (A : Over (Spec (.of K))) [CategoryTheory.GrpObj A]
      [AlgebraicGeometry.IsAbelianVariety K A], Stacks.Groupoids.EtaleZPowIdOfIsUnit K A)
    (hJac : HasJacobianParametrizations K n) (hBertini : BertiniDivisorReduction K) (d : ℕ) :
    RationalPointDifferenceDivisible K n d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact rationalPointDifferenceDivisible_zero K n
  · exact rationalPointDifferenceDivisible_of_dimOne K n
      (rationalPointDifferenceDivisible_one K n hn h03RP hJac) hBertini d hd

/-- **The conclusion of Stacks Tag 0FH7, assembled, with its carried hypotheses explicit.** Let `k`
be a field, let `X` be proper, smooth and geometrically irreducible over `k`, let `x, x'` be
`k`-rational points of `X` and let `n` be an integer invertible in `k`. Then there is a finite
separable extension `K/k` and a class `δ` of `CH_0(X_K)` with

`base change of ([x] - [x']) = n δ`   in   `CH_0(X_K)`,

which is the divisibility by `n` the tag asserts, over the finite separable extension it asserts.

The proof is the source's three steps: the induction on the dimension over the separable closure
(`Stacks.WeilCohomology.rationalPointDifferenceDivisible_of_dimOne` based at
`Stacks.WeilCohomology.rationalPointDifferenceDivisible_one`, with
`Stacks.WeilCohomology.rationalPointDifferenceDivisible_zero` for dimension zero), the
identification of the base change of `[x] - [x']` with the difference of the classes of the two
induced `k^sep`-rational points
(`Stacks.WeilCohomology.baseChangeChowPullbackOfIsPullback_rationalPointChowClass_sub`), and the
descent of that one equation to a finite separable stage
(`Stacks.Chow.exists_finiteSeparable_baseChangeChowPullback_eq_zsmul`, which is Stacks Tag 0FH6).

**The three hypotheses carried beyond the source's, each with the tag that would discharge it and
the place it is used.** No dimension hypothesis is among them: the binders are exactly `k`, `f`,
`n`, `hn`, the three below, and the two points with their section properties.

* `hJac : Stacks.WeilCohomology.HasJacobianParametrizations (SeparableClosure k) n` — the Jacobian
  of a smooth proper curve as an abelian variety, **Stacks Tag 0BA0**. Used in
  `Stacks.WeilCohomology.rationalPointDifferenceDivisible_one`. Satisfiable in a degenerate case:
  `Stacks.WeilCohomology.jacobianParametrization_of_degreeZero_trivial`.
* `h03RP` — the étale clause `Stacks.Groupoids.EtaleZPowIdOfIsUnit` of **Stacks Tag 03RP**,
  disclosed upstream and propagated unchanged. Used by
  `Stacks.Groupoids.exists_comp_zpow_id_left_eq_of_isSepClosed`.
* `hBertini : Stacks.WeilCohomology.BertiniDivisorReduction (SeparableClosure k)` — the one-step
  divisor reduction of the induction, whose geometric input is the depth condition of **Stacks Tag
  0FD9**. Used by `Stacks.WeilCohomology.rationalPointDifferenceDivisible_succ`.
Properness replaces the source's projectivity, which only strengthens the statement.

**Discharged, and so absent from the list above.** Three conditions that used to be carried are
now proved. Two of them are conditions on the curve, both supplied inside
`Stacks.WeilCohomology.rationalPointDifferenceDivisible_one`, which takes neither as an argument:
that smooth plus dimension one gives smooth of relative dimension one, **Stacks Tags 01V9 and
02G1**, by `Stacks.Curves.smoothOfRelativeDimension_one_of_topologicalKrullDim_eq_one`; and that
`H^0(X, 𝒪_X) = k` on a proper smooth geometrically irreducible scheme over `k`, **Stacks Tag
0BUG** (7), by `Stacks.WeilCohomology.curveHasOneDimensionalSections`. The third is the dimension
bookkeeping, formerly the binders `d`, `hd : 1 ≤ d` and `hdim`:
`Stacks.WeilCohomology.rationalPointDifferenceDivisible_zero` proves dimension zero instead of
excluding it, and `AlgebraicGeometry.exists_topologicalKrullDim_eq_natCast_of_isProper` produces
the numeral the induction recurses on from properness and the nonemptiness the point `x` gives,
so neither the numeral nor the pin has to be asked for.

Stacks Tag 0FH7 is **not** registered on this declaration, and must not be: the three items above
are not hypotheses of the tag. -/
theorem exists_finiteSeparable_rationalPointChowClass_sub_eq_zsmul (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ (fieldChowSituation k).S)
    [IsProper f] [Smooth f] [GeometricallyIrreducible f]
    (n : ℤ) (hn : IsUnit ((n : ℤ) : k))
    (h03RP : ∀ (A : Over (Spec (.of (SeparableClosure k)))) [CategoryTheory.GrpObj A]
      [AlgebraicGeometry.IsAbelianVariety (SeparableClosure k) A],
      Stacks.Groupoids.EtaleZPowIdOfIsUnit (SeparableClosure k) A)
    (hJac : HasJacobianParametrizations (SeparableClosure k) n)
    (hBertini : BertiniDivisorReduction (SeparableClosure k))
    (x x' : (fieldChowSituation k).S ⟶ X)
    (hx : x ≫ f = 𝟙 (fieldChowSituation k).S)
    (hx' : x' ≫ f = 𝟙 (fieldChowSituation k).S) :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K) (_ : FiniteDimensional k K)
        (_ : Algebra.IsSeparable k K)
        (δ : chowGroup (fieldChowSituation K)
          (pullback.snd f (fieldExtensionBaseChangeSituation k K).g) 0),
      baseChangeChowPullbackOfIsPullback (fieldExtensionBaseChangeSituation k K) rfl f
          (IsPullback.of_hasPullback f (fieldExtensionBaseChangeSituation k K).g) 0
          (rationalPointChowClass k f x hx - rationalPointChowClass k f x' hx') = n • δ := by
  have hn' : IsUnit ((n : ℤ) : SeparableClosure k) := by
    rw [← map_intCast (algebraMap k (SeparableClosure k)) n]
    exact hn.map _
  obtain ⟨d, hdim⟩ := exists_topologicalKrullDim_eq_natCast_of_isProper k f
    (Nonempty.map (fun p ↦ x.base p) inferInstance)
  have : QuasiCompact (Over.mk f).hom := (inferInstance : QuasiCompact f)
  have : LocallyOfFiniteType (Over.mk f).hom := (inferInstance : LocallyOfFiniteType f)
  have : CompactSpace ↥(Over.mk f).left :=
    QuasiCompact.compactSpace_of_compactSpace (Over.mk f).hom
  set g := (fieldExtensionBaseChangeSituation k (SeparableClosure k)).g
  have hg : ∀ (y : (fieldChowSituation k).S ⟶ X), y ≫ f = 𝟙 (fieldChowSituation k).S →
      (g ≫ y) ≫ f = 𝟙 (fieldChowSituation (SeparableClosure k)).S ≫ g := fun y hy ↦ by
    rw [Category.assoc, hy, Category.comp_id, Category.id_comp]
  have hdim' : topologicalKrullDim (pullback f g : Scheme.{u}) = (d : WithBot ℕ∞) :=
    (topologicalKrullDim_baseChange k (SeparableClosure k) (pullback.fst f g)
      (pullback.snd f g) f (IsPullback.of_hasPullback _ _)).trans hdim
  let y : (fieldChowSituation (SeparableClosure k)).S ⟶ pullback f g :=
    pullback.lift (g ≫ x) (𝟙 _) (hg x hx)
  let y' : (fieldChowSituation (SeparableClosure k)).S ⟶ pullback f g :=
    pullback.lift (g ≫ x') (𝟙 _) (hg x' hx')
  obtain ⟨γ, hγ⟩ := rationalPointDifferenceDivisible_of_isSepClosed (SeparableClosure k) n hn'
    h03RP hJac hBertini d (pullback.snd f g) hdim' y y' (pullback.lift_snd _ _ _)
    (pullback.lift_snd _ _ _)
  exact exists_finiteSeparable_baseChangeChowPullback_eq_zsmul k (Over.mk f) 0 n
    (rationalPointChowClass k f x hx - rationalPointChowClass k f x' hx') γ
    ((baseChangeChowPullbackOfIsPullback_rationalPointChowClass_sub k (SeparableClosure k) f
      (IsPullback.of_hasPullback f g) x hx x' hx' y
      (pullback.lift_snd _ _ _) (pullback.lift_fst _ _ _) y' (pullback.lift_snd _ _ _)
      (pullback.lift_fst _ _ _)).trans hγ)

end Stacks.WeilCohomology

end
