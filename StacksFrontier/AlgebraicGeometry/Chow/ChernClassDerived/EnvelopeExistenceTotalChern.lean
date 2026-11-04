module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.EnvelopeDescentChowCohomologyCriterion
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassComplexLocallyBounded
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDataBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.LocallyBoundedComparison
public import StacksFrontier.AlgebraicGeometry.Chow.ChowCohomologySeriesRingConstruction
public import StacksCore.Tactic.StacksAttribute

/-!
# The total Chern class of a perfect derived object: existence

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, Stacks 02QL, let `X` be a
scheme locally of finite type over `S` and let `E` be an object of `D(𝒪_X)` whose Chern classes
are defined in the sense of Stacks 0F9E (1): there is an envelope `g : Y ⟶ X`, Stacks 0GU5, and a
locally bounded complex `ℰ^•` of finite locally free `𝒪_Y`-modules representing `Lg^*E`.
**Stacks 0GUD** asserts that there are unique classes `c_p(E) ∈ A^p(X)` whose restrictions along
every such envelope are the components of the total Chern class `c(ℰ^•)` of the presenting
complex. This file is the **existence half for the total Chern class**;
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.EnvelopeExistencePowerSum` is the existence
half for the power sums `P_p` and the Chern character, and
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.EnvelopeUniqueness` is the uniqueness half
for all of them.

## Main results

* `Stacks.Chow.chowCohomologyRestriction_totalChernClassComplex` — **step 2 of the source's proof
  for the total Chern class**: the restriction map of Stacks 0B7F carries the degree-`p`
  component of `c(ℰ^•)` to the degree-`p` component of `c(w^*ℰ^•)`.
* `Stacks.Chow.chowCohomologyRestriction_totalChernClassComplex_eq` — the hypothesis of
  Stacks 0GUC for the total Chern class: the two restrictions of `c_p(ℰ^•)` to `Y ×_X Y` agree.
* `Stacks.Chow.existsUnique_chowCohomologyRestriction_eq_totalChernClassComplex` and
  `Stacks.Chow.existsUnique_chowCohomologyRestriction_eq_totalChernClassComplexLocallyBounded` —
  **Stacks 0GUD, existence for the total Chern class**: along an envelope there is a unique class
  of `A^p(X)` whose restriction is the degree-`p` component of `c(ℰ^•)`.

## Main definitions

* `Stacks.Chow.chowCohomologySeriesRingCongr`, `Stacks.Chow.totalChernClassSeriesCongr` — a
  series ring of Stacks 0FEL and a total Chern class datum read against an equal presentation of
  the structure morphism of their scheme over the base, as
  `Stacks.Chow.powerSumClassRuleCongr` does for a power sum datum.

## Implementation notes

### What the multiplicative step needs, and what it does not need

The total Chern class of a complex is the alternating **product** `∏_n c(ℰ^n)^{(-1)^n}` of Stacks
0ESZ, so restricting it needs the restriction map of Stacks 0B7F to be multiplicative for the
Cauchy product in which that product is formed. That is
`Stacks.Chow.chernClassKGroup_chowCohomologyRestriction`, and it holds for any series rings whose
degreewise product and unit are those of Stacks 0B7E; its proof is the degreewise multiplicativity
`Stacks.Chow.chowCohomologyRestriction_chowCohomologyGradedProductRule`, which carries no
hypothesis at all. So the multiplicativity is **not** the obstruction that the implementation notes
of `StacksFrontier.AlgebraicGeometry.Chow.ChernClassDataBaseChange` and of
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.EnvelopeExistencePowerSum` describe.

What *is* carried is the existence of the series rings themselves. By
`Stacks.Chow.nonempty_chowCohomologySeriesRing_iff_isComm` a
`Stacks.Chow.ChowCohomologySeriesRing` whose degreewise product is the product of Stacks 0B7E
exists if and only if `Stacks.Chow.GradedChowProductRule.IsComm` holds for that product, so
carrying such a ring on a scheme carries commutativity of its Chow cohomology in every pair of
non-negative degrees. The source does not assert that: the warning after Stacks 0B7E is that
commutativity of `A^*(X)` is not clear, and the product in which the source forms `c(ℰ^•)` is
that of the completed ring `A^*(X)^∧` of Stacks 0FE0, which is composition of bivariant classes
and is not asserted commutative either — what makes the source's alternating product
unambiguous is Stacks 02UA, by which the Chern classes generate a commutative (indeed central)
subalgebra of `A^*(X)`. Commutativity of the whole of `A^*(X)` is therefore a hypothesis of this
formalization and not of the source, and the attribute below says so.

That hypothesis is **not needed**, and
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.CentralTotalChernClass` is the same
existence statement without it:
`Stacks.Chow.existsUnique_chowCohomologyRestriction_eq_centralTotalChernClassComplexLocallyBounded`
forms the alternating product of Stacks 0ESZ in `Stacks.Chow.CentralUnitalSeries`, the series with
coefficients central in `A^*(X)`, which is a commutative group with no hypothesis at all — the
subalgebra Stacks 02UA and Remark 0ESW put the Chern classes in. The statements here are kept
because they are the ones a *carried* series ring gives, and their attribute records exactly the
price of that ring; a reader who wants the tag without the price should use the central version.

It is carried on **`Y` and `Y ×_X Y` only**, never on `X`: the class produced on `X` is a bare
component of `A^p(X)`, so no product on `A^*(X)` is named in the conclusion. In particular the
statements below are not vacuous — and they are not an instance of the vacuity of
`Stacks.Chow.forall_mem_center_of_heq_comm` of
`StacksFrontier.AlgebraicGeometry.Chow.ChowCohomologyCenterUnderCommutativity`, which concerns the
*centrality* clause of Stacks 0FAC (1) and not a construction.

### The pullback on `K_0(Vect)`

The total Chern class of a complex is the Chern class map of Stacks 0FEL evaluated at the
alternating class `∑_n (-1)^n [ℰ^n]` of `K_0(Vect(Y))`, and
`Stacks.Chow.chernClassKGroup_chowCohomologyRestriction` compares the two Chern class maps across
a ring map `pK : K_0(Vect(Y)) ⟶ K_0(Vect(Y'))` which is compatible with the classes of finite
locally free modules. No such map is constructed in this repository, so it is carried, exactly as
in that theorem; `Stacks.Chow.map_alternatingKClass` is what the compatibility buys, namely that
`pK` takes the alternating class of a complex to the alternating class of its pullback.

### Everything else is as in the power sum case

The window of degrees is taken as data rather than a compactness hypothesis on `Y ×_X Y`; one
datum on `Y ×_X Y` suffices for both projections, the transport between the two presentations of
its structure morphism being absorbed by `Stacks.Chow.totalChernClassSeriesCongr`; and the
statements are made at a bare envelope with a complex on its source rather than at an envelope
presentation of an object of `D(𝒪_X)`, which is the more general statement.

## References

* [Stacks Project, Tag 0GUD](https://stacks.math.columbia.edu/tag/0GUD)
* [Stacks Project, Tag 0GUC](https://stacks.math.columbia.edu/tag/0GUC)
* [Stacks Project, Tag 0GU5](https://stacks.math.columbia.edu/tag/0GU5)
* [Stacks Project, Tag 0F9E](https://stacks.math.columbia.edu/tag/0F9E)
* [Stacks Project, Tag 0ESZ](https://stacks.math.columbia.edu/tag/0ESZ)
* [Stacks Project, Tag 0FEL](https://stacks.math.columbia.edu/tag/0FEL)
* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
* [Stacks Project, Tag 0B7E](https://stacks.math.columbia.edu/tag/0B7E)
* [Stacks Project, Tag 0B7F](https://stacks.math.columbia.edu/tag/0B7F)
* [Stacks Project, Tag 02UA](https://stacks.math.columbia.edu/tag/02UA)
* [Stacks Project, Tag 02QL](https://stacks.math.columbia.edu/tag/02QL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

open ChowCohomologySeriesRing

attribute [local instance] HasDerivedCategory.standard

/-! ### The data against an equal presentation of the structure morphism -/

section RingCongr

variable (C : ChowSituation.{u}) (G : GysinSystem C) {Z : Scheme.{u}} {s s' : Z ⟶ C.S}
  [LocallyOfFiniteType s] [LocallyOfFiniteType s']
  {hiso : G.IsNaturalUnderInverseIso}

/-- **A series ring of Stacks 0FEL read against an equal presentation of the structure
morphism.** A ring for `s : Z ⟶ S` is a ring for any `s'` equal to it: the two are the same type,
presented differently, and the transport is the substitution of the equality. -/
def chowCohomologySeriesRingCongr (h : s = s') (R : ChowCohomologySeriesRing C G s) :
    ChowCohomologySeriesRing C G s' := by
  subst h
  exact R

/-- A transported series ring is built on the product of Stacks 0B7E as soon as the original
one is. -/
theorem chowCohomologySeriesRingCongr_gradedMul (h : s = s') {R : ChowCohomologySeriesRing C G s}
    (hmul : R.gradedMul = chowCohomologyGradedProductRule hiso) :
    (chowCohomologySeriesRingCongr C G h R).gradedMul
      = chowCohomologyGradedProductRule (sX := s') hiso := by
  subst h
  exact hmul

/-- A transported series ring has the unit series of Stacks 0B7E as soon as the original one
does. -/
theorem chowCohomologySeriesRingCongr_one (h : s = s') {R : ChowCohomologySeriesRing C G s}
    (hone : R.one = chowCohomologySeriesOne hiso) :
    (chowCohomologySeriesRingCongr C G h R).one = chowCohomologySeriesOne (sX := s') hiso := by
  subst h
  exact hone

/-- **A total Chern class datum read against an equal presentation of the structure morphism.** -/
def totalChernClassSeriesCongr (h : s = s') {R : ChowCohomologySeriesRing C G s}
    (D : TotalChernClassSeries C G s R) :
    TotalChernClassSeries C G s' (chowCohomologySeriesRingCongr C G h R) := by
  subst h
  exact D

/-- The component of the total Chern class of a complex computed with a transported datum is the
component computed with the original one, read through the transport of the Chow cohomology
groups. -/
theorem bivariantClassCongrBase_totalChernClassComplex (h : s = s')
    {R : ChowCohomologySeriesRing C G s} (D : TotalChernClassSeries C G s R)
    (P : CochainComplex Z.Modules ℤ) (a : ℤ) (k : ℕ) (p : ℕ) :
    bivariantClassCongrBase C G (𝟙 Z) h.symm h.symm (hv := Category.id_comp s')
        (hv' := Category.id_comp s) (p : ℤ)
        ((totalChernClassComplex C G s' (totalChernClassSeriesCongr C G h D) P a k).1 p) =
      (totalChernClassComplex C G s D P a k).1 p := by
  subst h
  rfl

end RingCongr

/-! ### The alternating class of a complex under a pullback on `K_0(Vect)` -/

section AlternatingKClass

variable {X X' : Scheme.{u}} (f : X' ⟶ X)

/-- **A ring map on `K_0(Vect)` compatible with the classes of finite locally free modules takes
the alternating class of a complex to the alternating class of its pullback.** The alternating
class of Stacks 0ESZ is the sum `∑_n (-1)^n [ℰ^n]`, and a ring map is additive and commutes with
integer multiples, so the compatibility on each term of the complex suffices. -/
theorem map_alternatingKClass
    (pK : AlgebraicGeometry.VectorBundleKZero X →+* AlgebraicGeometry.VectorBundleKZero X')
    (pKClassOf : ∀ E : X.Modules,
      Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E →
        pK (AlgebraicGeometry.VectorBundleKZero.classOf X E)
          = AlgebraicGeometry.VectorBundleKZero.classOf X'
            ((Scheme.Modules.pullback f).obj E))
    (P : CochainComplex X.Modules ℤ) (a : ℤ) (k : ℕ)
    (hflf : ∀ i ∈ Finset.range (k + 1),
      Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
        (P.X (a + (i : ℤ)))) :
    pK (alternatingKClass X P a k) =
      alternatingKClass X'
        (((Scheme.Modules.pullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) a k := by
  rw [alternatingKClass, alternatingKClass, map_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [map_zsmul, pKClassOf _ (hflf i hi)]
  rfl

end AlternatingKClass

/-! ### The restriction of the total Chern class of a complex -/

section BaseChange

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X X' : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (f : X' ⟶ X) [LocallyOfFiniteType f]
  (hgys : G.IsNaturalUnderBaseChangeIso) (hiso : G.IsNaturalUnderInverseIso)

/-- The components of the total Chern class of a complex are the values of the Chern class map of
Stacks 0FEL at the alternating class of the complex. -/
theorem totalChernClassComplex_val {R : ChowCohomologySeriesRing C G sX}
    (D : TotalChernClassSeries C G sX R) (P : CochainComplex X.Modules ℤ) (a : ℤ) (k : ℕ) :
    (totalChernClassComplex C G sX D P a k).1 = chernClassKGroup D (alternatingKClass X P a k) :=
  rfl

/-- **The base change clause for the total Chern class of a complex, Stacks 0ESZ.** The
restriction map of Stacks 0B7F carries the degree-`p` component of the total Chern class
`c(ℰ^•)` of a complex of finite locally free modules to the degree-`p` component of the total
Chern class of the pulled back complex:

  `f^*(c_p(ℰ^•)) = c_p(f^*ℰ^•)`.

This is step 2 of the source's proof of Stacks 0GUD for the total Chern class, and the clause the
implementation notes of `StacksFrontier.AlgebraicGeometry.Chow.ChernClassDataBaseChange` report as
missing. It is the multiplicativity of the restriction map for the Cauchy product,
`Stacks.Chow.chernClassKGroup_chowCohomologyRestriction`, together with
`Stacks.Chow.map_alternatingKClass`; the hypotheses are the two series rings being built on the
product and unit of Stacks 0B7E, the base change compatibility of the two total Chern class data,
and the carried pullback on `K_0(Vect)`. -/
theorem chowCohomologyRestriction_totalChernClassComplex
    {R : ChowCohomologySeriesRing C G sX} {R' : ChowCohomologySeriesRing C G (f ≫ sX)}
    (hmul : R.gradedMul = chowCohomologyGradedProductRule hiso)
    (hmul' : R'.gradedMul = chowCohomologyGradedProductRule (sX := f ≫ sX) hiso)
    (hone : R.one = chowCohomologySeriesOne hiso)
    (hone' : R'.one = chowCohomologySeriesOne (sX := f ≫ sX) hiso)
    {D : TotalChernClassSeries C G sX R} {D' : TotalChernClassSeries C G (f ≫ sX) R'}
    (pbCh : TotalChernClassSeries.IsBaseChangeCompatible C G sX f hgys D D')
    (pK : AlgebraicGeometry.VectorBundleKZero X →+* AlgebraicGeometry.VectorBundleKZero X')
    (pKClassOf : ∀ E : X.Modules,
      Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E →
        pK (AlgebraicGeometry.VectorBundleKZero.classOf X E)
          = AlgebraicGeometry.VectorBundleKZero.classOf X'
            ((Scheme.Modules.pullback f).obj E))
    (P : CochainComplex X.Modules ℤ) (a : ℤ) (k : ℕ)
    (hflf : ∀ i ∈ Finset.range (k + 1),
      Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
        (P.X (a + (i : ℤ)))) (p : ℕ) :
    chowCohomologyRestriction C G sX f (p : ℤ) hgys
        ((totalChernClassComplex C G sX D P a k).1 p) =
      (totalChernClassComplex C G (f ≫ sX) D'
        (((Scheme.Modules.pullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
        a k).1 p := by
  rw [totalChernClassComplex_val, totalChernClassComplex_val,
    chernClassKGroup_chowCohomologyRestriction C G sX f hgys hiso hmul hmul' hone hone' pK pbCh
      pKClassOf, map_alternatingKClass f pK pKClassOf P a k hflf]

end BaseChange

/-! ### The descent hypothesis for the total Chern class of a complex -/

section Descent

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (g : Y ⟶ X) [LocallyOfFiniteType g]
  (hgys : G.IsNaturalUnderBaseChangeIso) (hiso : G.IsNaturalUnderInverseIso)

/-- **The two restrictions of `c_p(ℰ^•)` to `Y ×_X Y` agree.** Let `ℰ^•` be a complex of finite
locally free modules on `Y` bounded in the degrees `a, …, a + k`, let `R` and `D` be a series ring
of Stacks 0FEL built on the product of Stacks 0B7E and a total Chern class datum on `Y`, and `RZ`,
`DZ` the same on `Y ×_X Y`, with `D` and `DZ` base change compatible along both projections, and
suppose that the total Chern classes of the two pullbacks of `ℰ^•` to `Y ×_X Y` agree in degree
`p`. Then the two restrictions of `c_p(ℰ^•)` agree, in the shape
`Stacks.Chow.existsUnique_chowCohomologyRestriction_eq_of_restriction_eq` consumes.

Each restriction is the corresponding component of the total Chern class of the pulled back
complex by `Stacks.Chow.chowCohomologyRestriction_totalChernClassComplex`, and the transport
between the two presentations of the structure morphism of `Y ×_X Y` is absorbed into the data by
`Stacks.Chow.bivariantClassCongrBase_totalChernClassComplex`, which is why one series ring and one
datum on `Y ×_X Y` suffice. -/
theorem chowCohomologyRestriction_totalChernClassComplex_eq
    {R : ChowCohomologySeriesRing C G (g ≫ sX)}
    {RZ : ChowCohomologySeriesRing C G (pullback.fst g g ≫ (g ≫ sX))}
    (hmul : R.gradedMul = chowCohomologyGradedProductRule hiso)
    (hmulZ : RZ.gradedMul
      = chowCohomologyGradedProductRule (sX := pullback.fst g g ≫ (g ≫ sX)) hiso)
    (hone : R.one = chowCohomologySeriesOne hiso)
    (honeZ : RZ.one = chowCohomologySeriesOne (sX := pullback.fst g g ≫ (g ≫ sX)) hiso)
    {D : TotalChernClassSeries C G (g ≫ sX) R}
    {DZ : TotalChernClassSeries C G (pullback.fst g g ≫ (g ≫ sX)) RZ}
    (pbChfst : TotalChernClassSeries.IsBaseChangeCompatible C G (g ≫ sX) (pullback.fst g g) hgys
      D DZ)
    (pbChsnd : TotalChernClassSeries.IsBaseChangeCompatible C G (g ≫ sX) (pullback.snd g g) hgys
      D (totalChernClassSeriesCongr C G
        (selfPullbackSnd_comp_structureMorphism_eq C sX g).symm DZ))
    (pKfst pKsnd : AlgebraicGeometry.VectorBundleKZero Y →+*
      AlgebraicGeometry.VectorBundleKZero (pullback g g))
    (pKClassOffst : ∀ E : Y.Modules,
      Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := Y.ringCatSheaf) E →
        pKfst (AlgebraicGeometry.VectorBundleKZero.classOf Y E)
          = AlgebraicGeometry.VectorBundleKZero.classOf (pullback g g)
            ((Scheme.Modules.pullback (pullback.fst g g)).obj E))
    (pKClassOfsnd : ∀ E : Y.Modules,
      Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := Y.ringCatSheaf) E →
        pKsnd (AlgebraicGeometry.VectorBundleKZero.classOf Y E)
          = AlgebraicGeometry.VectorBundleKZero.classOf (pullback g g)
            ((Scheme.Modules.pullback (pullback.snd g g)).obj E))
    (P : CochainComplex Y.Modules ℤ) (a : ℤ) (k : ℕ)
    (hflf : ∀ i ∈ Finset.range (k + 1),
      Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := Y.ringCatSheaf)
        (P.X (a + (i : ℤ))))
    (p : ℕ)
    (hPP : (totalChernClassComplex C G (pullback.fst g g ≫ (g ≫ sX)) DZ
          (((Scheme.Modules.pullback (pullback.fst g g)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) a k).1 p =
        (totalChernClassComplex C G (pullback.fst g g ≫ (g ≫ sX)) DZ
          (((Scheme.Modules.pullback (pullback.snd g g)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) a k).1 p) :
    chowCohomologyRestriction C G (g ≫ sX) (pullback.fst g g) (p : ℤ) hgys
        ((totalChernClassComplex C G (g ≫ sX) D P a k).1 p) =
      bivariantClassCongrBase C G (𝟙 (pullback g g))
        (selfPullbackSnd_comp_structureMorphism_eq C sX g)
        (selfPullbackSnd_comp_structureMorphism_eq C sX g) (hv := Category.id_comp _)
        (hv' := Category.id_comp _) (p : ℤ)
        (chowCohomologyRestriction C G (g ≫ sX) (pullback.snd g g) (p : ℤ) hgys
          ((totalChernClassComplex C G (g ≫ sX) D P a k).1 p)) := by
  rw [chowCohomologyRestriction_totalChernClassComplex C G (g ≫ sX) (pullback.fst g g) hgys hiso
      hmul hmulZ hone honeZ pbChfst pKfst pKClassOffst P a k hflf p,
    chowCohomologyRestriction_totalChernClassComplex C G (g ≫ sX) (pullback.snd g g) hgys hiso
      hmul (chowCohomologySeriesRingCongr_gradedMul C G
        (selfPullbackSnd_comp_structureMorphism_eq C sX g).symm hmulZ)
      hone (chowCohomologySeriesRingCongr_one C G
        (selfPullbackSnd_comp_structureMorphism_eq C sX g).symm honeZ)
      pbChsnd pKsnd pKClassOfsnd P a k hflf p,
    bivariantClassCongrBase_totalChernClassComplex C G
      (selfPullbackSnd_comp_structureMorphism_eq C sX g).symm DZ]
  exact hPP

/-! ### Existence at a bare envelope -/

variable (hgysP : G.IsNaturalUnderProperPushforward)
  (hgysC : G.IsNaturalUnderPullbackCompPushforward) (hgE : IsEnvelope g)

include hgysP hgysC hgE in
/-- **Existence of the class `c_p` descending along an envelope, for a complex bounded in a range
of degrees.** Let `g : Y ⟶ X` be an envelope and let `ℰ^•` be a complex of finite locally free
modules on `Y` bounded in the degrees `a, …, a + k` whose total Chern class is compatible with
restriction to `Y ×_X Y` in the sense of
`Stacks.Chow.chowCohomologyRestriction_totalChernClassComplex_eq`. Then there is a unique class in
`A^p(X)` whose restriction of Stacks 0B7F along `g` is the degree-`p` component of `c(ℰ^•)`.

This is the engine of the existence half of Stacks 0GUD for the total Chern class: Stacks 0GUC on
Chow cohomology, `Stacks.Chow.existsUnique_chowCohomologyRestriction_eq_of_restriction_eq`, whose
descent condition is the equality of the two restrictions. No object of the
derived category is mentioned, which makes it more general than the tag's statement. -/
theorem existsUnique_chowCohomologyRestriction_eq_totalChernClassComplex
    {R : ChowCohomologySeriesRing C G (g ≫ sX)}
    {RZ : ChowCohomologySeriesRing C G (pullback.fst g g ≫ (g ≫ sX))}
    (hmul : R.gradedMul = chowCohomologyGradedProductRule hiso)
    (hmulZ : RZ.gradedMul
      = chowCohomologyGradedProductRule (sX := pullback.fst g g ≫ (g ≫ sX)) hiso)
    (hone : R.one = chowCohomologySeriesOne hiso)
    (honeZ : RZ.one = chowCohomologySeriesOne (sX := pullback.fst g g ≫ (g ≫ sX)) hiso)
    {D : TotalChernClassSeries C G (g ≫ sX) R}
    {DZ : TotalChernClassSeries C G (pullback.fst g g ≫ (g ≫ sX)) RZ}
    (pbChfst : TotalChernClassSeries.IsBaseChangeCompatible C G (g ≫ sX) (pullback.fst g g) hgys
      D DZ)
    (pbChsnd : TotalChernClassSeries.IsBaseChangeCompatible C G (g ≫ sX) (pullback.snd g g) hgys
      D (totalChernClassSeriesCongr C G
        (selfPullbackSnd_comp_structureMorphism_eq C sX g).symm DZ))
    (pKfst pKsnd : AlgebraicGeometry.VectorBundleKZero Y →+*
      AlgebraicGeometry.VectorBundleKZero (pullback g g))
    (pKClassOffst : ∀ E : Y.Modules,
      Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := Y.ringCatSheaf) E →
        pKfst (AlgebraicGeometry.VectorBundleKZero.classOf Y E)
          = AlgebraicGeometry.VectorBundleKZero.classOf (pullback g g)
            ((Scheme.Modules.pullback (pullback.fst g g)).obj E))
    (pKClassOfsnd : ∀ E : Y.Modules,
      Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := Y.ringCatSheaf) E →
        pKsnd (AlgebraicGeometry.VectorBundleKZero.classOf Y E)
          = AlgebraicGeometry.VectorBundleKZero.classOf (pullback g g)
            ((Scheme.Modules.pullback (pullback.snd g g)).obj E))
    (P : CochainComplex Y.Modules ℤ) (a : ℤ) (k : ℕ)
    (hflf : ∀ i ∈ Finset.range (k + 1),
      Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := Y.ringCatSheaf)
        (P.X (a + (i : ℤ))))
    (p : ℕ)
    (hPP : (totalChernClassComplex C G (pullback.fst g g ≫ (g ≫ sX)) DZ
          (((Scheme.Modules.pullback (pullback.fst g g)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) a k).1 p =
        (totalChernClassComplex C G (pullback.fst g g ≫ (g ≫ sX)) DZ
          (((Scheme.Modules.pullback (pullback.snd g g)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) a k).1 p) :
    ∃! c : chowCohomologyComponent C G sX (p : ℤ),
      chowCohomologyRestriction C G sX g (p : ℤ) hgys c =
        (totalChernClassComplex C G (g ≫ sX) D P a k).1 p :=
  existsUnique_chowCohomologyRestriction_eq_of_restriction_eq C G sX g (p : ℤ)
    hgys hgysP hgysC hgE _
    (chowCohomologyRestriction_totalChernClassComplex_eq C G sX g hgys hiso hmul hmulZ hone
      honeZ pbChfst pbChsnd pKfst pKsnd pKClassOffst pKClassOfsnd P a k hflf p hPP)

include hgysP hgysC hgE in
/-- **Stacks 0GUD, existence for the total Chern class.** Let `g : Y ⟶ X` be an envelope with `Y`
quasi-compact and let `ℰ^•` be a locally bounded complex of finite locally free modules on `Y`
whose total Chern class is compatible with restriction to `Y ×_X Y`. There is a **unique** class
in `A^p(X)` whose restriction of Stacks 0B7F along `g` is the degree-`p` component of `c(ℰ^•)`:

  `res : A^p(X) ⟶ A^p(Y)`,  `res(c_p(E)) = c_p(ℰ^•)`.

Applied to an envelope presentation `H` of an object `E` of `D(𝒪_X)`, Stacks 0F9E (1), at
`g = H.f` and `ℰ^• = H.P`, this is the existence of the components of the total Chern class
`c(E)` of the tag, whose uniqueness is
`Stacks.Chow.eq_of_restriction_eq_totalChernClassComplexLocallyBounded`.

It is `Stacks.Chow.existsUnique_chowCohomologyRestriction_eq_totalChernClassComplex` read at the
class of the locally bounded case, `Stacks.Chow.totalChernClassComplexLocallyBounded`: a window of
degrees outside which the complex vanishes identifies that class with the bounded-window class, by
`Stacks.Chow.totalChernClassComplexLocallyBounded_eq`. -/
theorem existsUnique_chowCohomologyRestriction_eq_totalChernClassComplexLocallyBounded
    [CompactSpace Y] {R : ChowCohomologySeriesRing C G (g ≫ sX)}
    {RZ : ChowCohomologySeriesRing C G (pullback.fst g g ≫ (g ≫ sX))}
    (hmul : R.gradedMul = chowCohomologyGradedProductRule hiso)
    (hmulZ : RZ.gradedMul
      = chowCohomologyGradedProductRule (sX := pullback.fst g g ≫ (g ≫ sX)) hiso)
    (hone : R.one = chowCohomologySeriesOne hiso)
    (honeZ : RZ.one = chowCohomologySeriesOne (sX := pullback.fst g g ≫ (g ≫ sX)) hiso)
    {D : TotalChernClassSeries C G (g ≫ sX) R}
    {DZ : TotalChernClassSeries C G (pullback.fst g g ≫ (g ≫ sX)) RZ}
    (pbChfst : TotalChernClassSeries.IsBaseChangeCompatible C G (g ≫ sX) (pullback.fst g g) hgys
      D DZ)
    (pbChsnd : TotalChernClassSeries.IsBaseChangeCompatible C G (g ≫ sX) (pullback.snd g g) hgys
      D (totalChernClassSeriesCongr C G
        (selfPullbackSnd_comp_structureMorphism_eq C sX g).symm DZ))
    (pKfst pKsnd : AlgebraicGeometry.VectorBundleKZero Y →+*
      AlgebraicGeometry.VectorBundleKZero (pullback g g))
    (pKClassOffst : ∀ E : Y.Modules,
      Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := Y.ringCatSheaf) E →
        pKfst (AlgebraicGeometry.VectorBundleKZero.classOf Y E)
          = AlgebraicGeometry.VectorBundleKZero.classOf (pullback g g)
            ((Scheme.Modules.pullback (pullback.fst g g)).obj E))
    (pKClassOfsnd : ∀ E : Y.Modules,
      Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := Y.ringCatSheaf) E →
        pKsnd (AlgebraicGeometry.VectorBundleKZero.classOf Y E)
          = AlgebraicGeometry.VectorBundleKZero.classOf (pullback g g)
            ((Scheme.Modules.pullback (pullback.snd g g)).obj E))
    (P : CochainComplex Y.Modules ℤ) (hP : IsLocallyBoundedFiniteLocallyFree P) {a : ℤ} {k : ℕ}
    (hvanish : ∀ n : ℤ, (n < a ∨ a + (k : ℤ) < n) → IsZero (P.X n)) (p : ℕ)
    (hPP : (totalChernClassComplex C G (pullback.fst g g ≫ (g ≫ sX)) DZ
          (((Scheme.Modules.pullback (pullback.fst g g)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) a k).1 p =
        (totalChernClassComplex C G (pullback.fst g g ≫ (g ≫ sX)) DZ
          (((Scheme.Modules.pullback (pullback.snd g g)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) a k).1 p) :
    ∃! c : chowCohomologyComponent C G sX (p : ℤ),
      chowCohomologyRestriction C G sX g (p : ℤ) hgys c =
        (totalChernClassComplexLocallyBounded C G (g ≫ sX) D P hP).1 p := by
  rw [totalChernClassComplexLocallyBounded_eq C G (g ≫ sX) D P hP hvanish]
  exact existsUnique_chowCohomologyRestriction_eq_totalChernClassComplex C G sX g hgys hiso hgysP
    hgysC hgE hmul hmulZ hone honeZ pbChfst pbChsnd pKfst pKsnd pKClassOffst pKClassOfsnd P a k
    (fun i _ => isFiniteLocallyFree_X_of_isLocallyBounded hP _) p hPP

end Descent

end Stacks.Chow

end
