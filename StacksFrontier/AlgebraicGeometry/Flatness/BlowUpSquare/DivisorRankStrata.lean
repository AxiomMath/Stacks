module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.RankDecomposition
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodOverEtaPerfect
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.LocallyFreeLocus
public import StacksCore.Tactic.StacksAttribute

/-!
# Rank strata on the subscheme of the divisor of a complex-and-divisor modification

Let `(X, D, M)` be a triple as in Situation 0F8S, let `b : X' ⟶ X` be a morphism along which the
pullback `D' = b⁻¹D` of the effective Cartier divisor is defined, and let
`Q = Lη_{ℐ'}Lb^*M` be the object of `D(𝒪_{X'})` of Stacks tag 0F8U.  Let `i : T ⟶ D'` be the
closed immersion of Stacks tag 0F8X and let `ρ = (ρ_n)_{n ∈ ℤ}` be ranks.  Stacks tag 0F8Y
asserts that the locus `T(ρ) ⊆ T` where the cohomology sheaves of `Li^*Q` have the ranks `ρ` is
open and closed, that it contains `D' ∩ b⁻¹(W(ρ))` — where `W(ρ) ⊆ X` is the maximal open over
which the cohomology sheaves of `M` are locally free of the ranks `ρ` — and that the cohomology
sheaves of `Li^*Q` are locally free of those ranks on it.

The mathematical content is the rank stratification of a *family* of finite locally free
modules indexed by `ℤ`, and that is what the first half of this file proves: the stratum is
closed because each single-degree stratum is a fibre of a locally constant function, and it is
open because near every point only finitely many of those conditions are not already satisfied.
The second half reads that off in Situation 0F8S.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.rankStratumSet`: the locus where every member of a family
  of finite locally free modules has a prescribed rank.
* `AlgebraicGeometry.ComplexAndDivisorSituation.cohomologySheaf`: the cohomology sheaf `H^n(M)`
  of the perfect object of a triple.
* `AlgebraicGeometry.ComplexAndDivisorSituation.etaDerivedPullbackRestrict` and
  `etaDerivedPullbackRestrictHomology`: the object `Li^*Q` of `D(𝒪_T)` for a morphism
  `T ⟶ X'`, and its cohomology sheaves `H^n(Li^*Q)`.
* `AlgebraicGeometry.ComplexAndDivisorSituation.locallyFreeLocusCohomologySheaf`: the
  restriction of `H^n(M)` to the locally free locus `W ⊆ X`, which is where the ranks of the
  cohomology sheaves of `M` are defined.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isClosed_rankStratumSet`,
  `isOpen_rankStratumSet` and `isClopen_rankStratumSet`: the rank locus of a family of finite
  locally free modules is closed, and open as soon as the family is locally bounded.
* `AlgebraicGeometry.Scheme.Modules.exists_free_nbhd_of_mem_rankStratumSet`: on the rank locus
  every member of the family is free of the prescribed rank near each point.
* `AlgebraicGeometry.ComplexAndDivisorSituation.exists_isClopen_rankStratum_etaDerivedPullback`:
  **Stacks tag 0F8Y**, for a morphism `b` whose pullback of the divisor is defined and the
  closed immersion `T ⟶ D'` of Stacks tag 0F8X with its conclusions (2) and (3).

## The data of tag 0F8Y

Tag 0F8Y reads "let `i : T → D'` be as in Lemma 0F8X".  Its one-line source proof uses the
closed immersion together with exactly two of its properties: conclusion (2) of Stacks tag
0F8X, that the cohomology sheaves of `Li^*Q` are finite locally free on `T`, and conclusion
(3), that their ranks at a point of `T` above `W` agree with the ranks of the cohomology sheaves
of `M` there.  Those are the hypotheses `hQ` and `hrank` below.  They are the instance at the
pulled-back triple of parts (2) and (3) of Stacks tag 0GTZ.  Stacks tag 08DW, the comparison
of a derived pullback with termwise base change on a complex of finite free modules, is proved
in both of its own parts — part (1) in
`StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullback`, part (2) there
and in `StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineSchemePullbackComparison`.  What
parts (2) and (3) of tag 0GTZ need beyond it is the chart-level comparison
`AlgebraicGeometry.ComplexAndDivisorSituation.ChartDecalage`, whose three identifications the
module documentation of
`StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodTripleEtaPerfect` lists individually.

A third hypothesis is `hbd`, the local boundedness of the family `H^n(Li^*Q)`: near every point
of `T` all but finitely many of these sheaves have rank zero.  It follows from perfectness of
`Li^*Q`, which holds because `Q` is perfect
(`AlgebraicGeometry.ComplexAndDivisorSituation.isPerfect_etaDerivedPullbackObject`) and derived
pullback preserves perfectness
(`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback`), through the
passage from a local strictly perfect model to the vanishing of the cohomology sheaves outside a
finite range of degrees and then from vanishing to rank zero.  Without local boundedness the
conclusion is false as stated: an intersection of infinitely many open and closed subsets need
not be open.

Finally `hM`, the finite local freeness of the cohomology sheaves of `M` over `W`, is what gives
the ranks that define `W(ρ)`.  The second assertion of Stacks tag 0GT1 is proved as
`Stacks.Cohomology.PerfectComplexes.isFiniteLocallyFree_homology_restrict_locus`, over the
universe-lifted sheaf of modules on the finite free locus
`Stacks.Cohomology.PerfectComplexes.cohomologyFiniteFreeLocus`, whose stalks are the
universe-lifted ones.  `W` is `AlgebraicGeometry.RingedSpace.cohomologyFiniteFreeLocus`, a second
definition of the same locus through the plain stalks of
`StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.CohomologyFiniteFreeLocus`, and `hM`
asks for `AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree` of the restriction of `H^n(M)`
to the open subscheme `W`.  Three legs separate the two: the identification of the two loci, the
transfer of finite local freeness across the universe lift, and the two spellings of restriction
— of which only the last exists, as
`AlgebraicGeometry.RingedSpace.restrictModulesIsoRestrictFunctor`.  The plain-stalk route avoids
the first two: it asks for `AlgebraicGeometry.RingedSpace.IsFiniteLocallyFreeOver (H^n(M)) W`,
the converse of the maximality half
`AlgebraicGeometry.RingedSpace.subset_cohomologyFiniteFreeLocus` that
`AlgebraicGeometry.ComplexAndDivisorSituation.le_locallyFreeLocus` already reads off.

`b` is a variable here, as it is in every other statement of this section.  That is a
generalization, not a weakening: the statement below applies to the morphism tag 0GTY produces,
`AlgebraicGeometry.ComplexAndDivisorSituation.goodBlowupToBase`, and tag 0F8Y read at it is
`AlgebraicGeometry.ComplexAndDivisorSituation.exists_isClopen_rankStratum_goodBlowupToBase` of
`GoodBlowupRankStrata.lean`.

## Implementation notes

`W(ρ)` is read as the rank stratum of the family `H^n(M)|_W` on the open subscheme `W`, rather
than as a separate "maximal open subscheme where `H^i(M)` is locally free of rank `ρ_i`": over
`W` the cohomology sheaves of `M` are finite locally free, so their ranks are defined there and
nowhere else, and the stratum is open and closed in `W` hence open in `X`.  The containment of
the conclusion is a containment of *open* subschemes of `T`, for which scheme-theoretic and
set-theoretic containment agree, so it is stated as the latter.

The ranks are natural numbers rather than the integers of the source.  A negative rank is never
attained by a finite locally free module on a nonempty scheme, so the integer-indexed statement
adds only the empty stratum.

## References

* [Stacks Project, Tag 0F8Y](https://stacks.math.columbia.edu/tag/0F8Y)
* [Stacks Project, Tag 0F8S](https://stacks.math.columbia.edu/tag/0F8S)
* [Stacks Project, Tag 0F8U](https://stacks.math.columbia.edu/tag/0F8U)
* [Stacks Project, Tag 0F8X](https://stacks.math.columbia.edu/tag/0F8X)
* [Stacks Project, Tag 0GTZ](https://stacks.math.columbia.edu/tag/0GTZ)
* [Stacks Project, Tag 0B37](https://stacks.math.columbia.edu/tag/0B37)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace StrictlyPerfect

universe u d

namespace AlgebraicGeometry.Scheme.Modules

variable {T : Scheme.{u}}

/-- The locus on which every member of a family `F` of finite locally free modules indexed by
the integers has a prescribed rank `ρ`. -/
def rankStratumSet (F : ℤ → T.Modules)
    (hF : ∀ n : ℤ, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (F n))
    (ρ : ℤ → ℕ) : Set T :=
  ⋂ n : ℤ, (@rankStratum T (F n) (hF n) (ρ n) : Set T)

/-- Membership in the rank locus is the prescription of every rank. -/
theorem mem_rankStratumSet {F : ℤ → T.Modules}
    {hF : ∀ n : ℤ, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (F n)}
    {ρ : ℤ → ℕ} {t : T} :
    t ∈ rankStratumSet F hF ρ ↔ ∀ n : ℤ, @finiteLocallyFreeRank T (F n) (hF n) t = ρ n := by
  simp only [rankStratumSet, Set.mem_iInter]
  rfl

/-- The rank locus is closed: it is an intersection of fibres of locally constant functions. -/
theorem isClosed_rankStratumSet (F : ℤ → T.Modules)
    (hF : ∀ n : ℤ, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (F n))
    (ρ : ℤ → ℕ) : IsClosed (rankStratumSet F hF ρ) :=
  isClosed_iInter fun n => (@isClopen_rankStratum T (F n) (hF n) (ρ n)).1

/-- The rank locus is open as soon as the family is **locally bounded**: near every point all
but finitely many of its members have rank zero.  Only finitely many conditions then cut the
locus out near a point of it, each of them an open condition, the remaining ones holding
throughout a neighbourhood because they hold with the value zero on both sides. -/
theorem isOpen_rankStratumSet (F : ℤ → T.Modules)
    (hF : ∀ n : ℤ, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (F n))
    (ρ : ℤ → ℕ)
    (hbd : ∀ t : T, ∃ V : T.Opens, t ∈ V ∧ ∃ s : Finset ℤ, ∀ n ∉ s, ∀ v ∈ V,
      @finiteLocallyFreeRank T (F n) (hF n) v = 0) :
    IsOpen (rankStratumSet F hF ρ) := by
  rw [isOpen_iff_forall_mem_open]
  intro t ht
  obtain ⟨V, htV, s, hs⟩ := hbd t
  refine ⟨(V : Set T) ∩ ⋂ n ∈ s, (@rankStratum T (F n) (hF n) (ρ n) : Set T), ?_,
    V.isOpen.inter (isOpen_biInter_finset fun n _ =>
      (@isClopen_rankStratum T (F n) (hF n) (ρ n)).2),
    ⟨htV, Set.mem_iInter₂.2 fun n _ => mem_rankStratumSet.1 ht n⟩⟩
  intro v hv
  refine mem_rankStratumSet.2 fun n => ?_
  by_cases hn : n ∈ s
  · exact Set.mem_iInter₂.1 hv.2 n hn
  · rw [hs n hn v hv.1, ← hs n hn t htV]
    exact mem_rankStratumSet.1 ht n

/-- **The rank locus of a locally bounded family of finite locally free modules is open and
closed.** -/
theorem isClopen_rankStratumSet (F : ℤ → T.Modules)
    (hF : ∀ n : ℤ, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (F n))
    (ρ : ℤ → ℕ)
    (hbd : ∀ t : T, ∃ V : T.Opens, t ∈ V ∧ ∃ s : Finset ℤ, ∀ n ∉ s, ∀ v ∈ V,
      @finiteLocallyFreeRank T (F n) (hF n) v = 0) :
    IsClopen (rankStratumSet F hF ρ) :=
  ⟨isClosed_rankStratumSet F hF ρ, isOpen_rankStratumSet F hF ρ hbd⟩

/-- On the rank locus every member of the family is free of the prescribed rank near each
point. -/
theorem exists_free_nbhd_of_mem_rankStratumSet (F : ℤ → T.Modules)
    (hF : ∀ n : ℤ, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (F n))
    (ρ : ℤ → ℕ) (n : ℤ) (t : T) (ht : t ∈ rankStratumSet F hF ρ) :
    ∃ (V : T.Opens) (_ : t ∈ V) (I : Type u), Nonempty (I ≃ Fin (ρ n)) ∧
      Nonempty (_root_.SheafOfModules.free.{u} I ≅ (toRingSheafModule (F n)).over V) := by
  obtain ⟨V, htV, -, I, hI, he⟩ :=
    @exists_free_nbhd_of_mem_rankStratum T (F n) (hF n) (ρ n) t (mem_rankStratumSet.1 ht n)
  exact ⟨V, htV, I, hI, he⟩

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.ComplexAndDivisorSituation

attribute [local instance 10000] HasDerivedCategory.standard

/-- The cohomology sheaf `H^n(M)` of the perfect object of a triple as in Situation 0F8S, read
in the model of `D(𝒪_X)` that the triple carries. -/
def cohomologySheaf (S : ComplexAndDivisorSituation.{u, d}) (n : ℤ) : S.X.Modules :=
  (@DerivedCategory.homologyFunctor (OXMod.{u, u} S.X.toRingedSpace) _ _ S.hasDerivedCategory
    n).obj S.M

/-- The restriction of `H^n(M)` to the locally free locus `W ⊆ X`.  Over `W` the cohomology
sheaves of `M` are finite locally free, so this is the module whose rank the ranks `ρ` of
Stacks tag 0F8Y prescribe. -/
def locallyFreeLocusCohomologySheaf (S : ComplexAndDivisorSituation.{u, d}) (n : ℤ) :
    S.locallyFreeLocus.toScheme.Modules :=
  (Scheme.Modules.restrictFunctor S.locallyFreeLocus.ι).obj (S.cohomologySheaf n)

/-- The derived restriction `Li^*Q` of the object `Q = Lη_{ℐ'}Lb^*M` of Stacks tag 0F8U along a
morphism `j : T ⟶ X'`, formed in the standard model of `D(𝒪_T)`. -/
def etaDerivedPullbackRestrict (S : ComplexAndDivisorSituation.{u, d}) {X' : Scheme.{u}}
    (b : X' ⟶ S.X) (hb : Stacks.Divisors.IsPullbackDefined b S.D) {T : Scheme.{u}}
    (j : T ⟶ X') : DerivedCategory T.Modules :=
  (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
    j.toLRSHom.toShHom).obj (S.etaDerivedPullbackObject b hb)

/-- The cohomology sheaf `H^n(Li^*Q)` of the derived restriction of `Q = Lη_{ℐ'}Lb^*M`. -/
def etaDerivedPullbackRestrictHomology (S : ComplexAndDivisorSituation.{u, d}) {X' : Scheme.{u}}
    (b : X' ⟶ S.X) (hb : Stacks.Divisors.IsPullbackDefined b S.D) {T : Scheme.{u}}
    (j : T ⟶ X') (n : ℤ) : T.Modules :=
  (DerivedCategory.homologyFunctor T.Modules n).obj (S.etaDerivedPullbackRestrict b hb j)

/-- **Stacks tag 0F8Y.**  In Situation 0F8S let `b : X' ⟶ X` be a morphism along which the
pullback `D' = b⁻¹D` of the effective Cartier divisor is defined, let
`Q = Lη_{ℐ'}Lb^*M` be as in Stacks tag 0F8U, let `i : T ⟶ D'` be as in Stacks tag 0F8X and let
`ρ = (ρ_n)_{n ∈ ℤ}` be ranks.  Then there is an open and closed `T(ρ) ⊆ T` which contains the
inverse image in `T` of `W(ρ)`, the rank-`ρ` stratum of the cohomology sheaves of `M` on the
locally free locus `W`, and on which `H^n(Li^*Q)` is free of rank `ρ_n` near every point.

`T(ρ)` is the rank stratum of the family `H^n(Li^*Q)`, as in the source.  It is open and closed
by `AlgebraicGeometry.Scheme.Modules.isClopen_rankStratumSet`; the containment is the rank
agreement `hrank` of tag 0F8X (3) read against the definition of `W(ρ)`, which is the source's
own one-line proof; and the local freeness is
`AlgebraicGeometry.Scheme.Modules.exists_free_nbhd_of_mem_rankStratumSet`. -/
@[stacks 0F8Y "the rank stratum `T(ρ)` is open and closed, contains the inverse image of \
`W(ρ)` and has `H^n(Li^*Q)` free of rank `ρ_n`. The data are the ones tag 0F8Y is given, \
over an arbitrary `b` along which the pullback of `D` is defined: the morphism `i : T → D'` of \
tag 0F8X together with its parts (2) and (3), which are the binders `hQ` and `hrank` and are \
the instance at the pulled-back triple of parts (2) and (3) of tag 0GTZ, which need the \
chart-level comparison AlgebraicGeometry.ComplexAndDivisorSituation.ChartDecalage over and \
above tag 08DW --- that tag being proved in both its parts; plus `hbd`, the local boundedness \
of `H^n(Li^*Q)`, a consequence of perfectness of `Li^*Q`, and `hM`, the finite local freeness \
of `H^n(M)` over `W`, which tag 0GT1's second assertion gives over the universe-lifted locus \
of Stacks.Cohomology.PerfectComplexes.cohomologyFiniteFreeLocus rather than over the open \
subscheme `W` built from AlgebraicGeometry.RingedSpace.cohomologyFiniteFreeLocus. For the \
morphism tag 0GTY produces see \
AlgebraicGeometry.ComplexAndDivisorSituation.exists_isClopen_rankStratum_goodBlowupToBase"]
theorem exists_isClopen_rankStratum_etaDerivedPullback
    (S : ComplexAndDivisorSituation.{u, d}) {X' : Scheme.{u}} (b : X' ⟶ S.X)
    (hb : Stacks.Divisors.IsPullbackDefined b S.D) {T : Scheme.{u}}
    (i : T ⟶ (S.D.comap b).subscheme) (ρ : ℤ → ℕ)
    (hQ : ∀ n : ℤ, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (S.etaDerivedPullbackRestrictHomology b hb (i ≫ (S.D.comap b).subschemeι) n))
    (hbd : ∀ t : T, ∃ V : T.Opens, t ∈ V ∧ ∃ s : Finset ℤ, ∀ n ∉ s, ∀ v ∈ V,
      @Scheme.Modules.finiteLocallyFreeRank T
        (S.etaDerivedPullbackRestrictHomology b hb (i ≫ (S.D.comap b).subschemeι) n)
        (hQ n) v = 0)
    (hM : ∀ n : ℤ, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (S.locallyFreeLocusCohomologySheaf n))
    (hrank : ∀ (n : ℤ) (t : T)
      (hw : ((i ≫ (S.D.comap b).subschemeι) ≫ b).base t ∈ S.locallyFreeLocus),
      @Scheme.Modules.finiteLocallyFreeRank T
          (S.etaDerivedPullbackRestrictHomology b hb (i ≫ (S.D.comap b).subschemeι) n)
          (hQ n) t =
        @Scheme.Modules.finiteLocallyFreeRank S.locallyFreeLocus.toScheme
          (S.locallyFreeLocusCohomologySheaf n) (hM n)
          ⟨((i ≫ (S.D.comap b).subschemeι) ≫ b).base t, hw⟩) :
    ∃ Tρ : Set T, IsClopen Tρ ∧
      (∀ (t : T) (hw : ((i ≫ (S.D.comap b).subschemeι) ≫ b).base t ∈ S.locallyFreeLocus),
        (⟨((i ≫ (S.D.comap b).subschemeι) ≫ b).base t, hw⟩ : S.locallyFreeLocus.toScheme) ∈
            Scheme.Modules.rankStratumSet S.locallyFreeLocusCohomologySheaf hM ρ →
          t ∈ Tρ) ∧
      ∀ (n : ℤ) (t : T), t ∈ Tρ →
        ∃ (V : T.Opens) (_ : t ∈ V) (I : Type u), Nonempty (I ≃ Fin (ρ n)) ∧
          Nonempty (_root_.SheafOfModules.free.{u} I ≅
            (Scheme.Modules.toRingSheafModule
              (S.etaDerivedPullbackRestrictHomology b hb
                (i ≫ (S.D.comap b).subschemeι) n)).over V) := by
  refine ⟨Scheme.Modules.rankStratumSet
      (S.etaDerivedPullbackRestrictHomology b hb (i ≫ (S.D.comap b).subschemeι)) hQ ρ,
    Scheme.Modules.isClopen_rankStratumSet _ hQ ρ hbd, ?_,
    fun n t ht => Scheme.Modules.exists_free_nbhd_of_mem_rankStratumSet _ hQ ρ n t ht⟩
  intro t hw hmem
  refine Scheme.Modules.mem_rankStratumSet.2 fun n => ?_
  rw [hrank n t hw]
  exact Scheme.Modules.mem_rankStratumSet.1 hmem n

end AlgebraicGeometry.ComplexAndDivisorSituation

end
