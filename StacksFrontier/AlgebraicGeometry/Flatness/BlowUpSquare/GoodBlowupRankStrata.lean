module

public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.DivisorRankStrata
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodBlowupLocallyFree

/-!
# Stacks tag 0F8Y at the morphism of tag 0GTY

Let `(X, D, M)` be a triple as in Situation 0F8S, let `b : X' ⟶ X` be the morphism of Stacks tag
0GTY with `D' = b⁻¹D`, let `Q = Lη_{ℐ'}Lb^*M` be the object of Stacks tag 0F8U, let `i : T ⟶ D'`
be the closed immersion of Stacks tag 0F8X and let `ρ = (ρ_n)_{n ∈ ℤ}` be ranks.  Stacks tag
0F8Y asserts that the locus `T(ρ) ⊆ T` where the cohomology sheaves of `Li^*Q` have the ranks
`ρ` is open and closed, contains `D' ∩ b⁻¹(W(ρ))`, and carries those cohomology sheaves locally
free of the ranks `ρ`.

`DivisorRankStrata.lean` proves this for an arbitrary morphism `b` along which the pullback of
`D` is defined.  This file reads it off at the morphism of tag 0GTY, whose pullback of `D` is
defined by `AlgebraicGeometry.ComplexAndDivisorSituation.isPullbackDefined_goodBlowupToBase`.

## Main results

* `AlgebraicGeometry.ComplexAndDivisorSituation.exists_isClopen_rankStratum_goodBlowupToBase`:
  **Stacks tag 0F8Y for the morphism of tag 0GTY.**

## The closed immersion `i` and its two properties

Tag 0F8Y reads "let `i : T → D'` be as in Lemma 0F8X": the closed immersion and the two
properties of it that the one-line source proof uses — that the cohomology sheaves of `Li^*Q` are
finite locally free (part (2) of tag 0F8X, the hypothesis `hQ`) and that their ranks over a point
of `W` agree with the ranks of the cohomology sheaves of `M` there (part (3), the hypothesis
`hrank`) — are the data tag 0F8Y is given.  Parts (2) and (3) are the instance at the
pulled-back triple of parts (2) and (3) of Stacks tag 0GTZ.  Stacks tag 08DW, the comparison
of a derived pullback with termwise base change on a complex of finite free modules, is formalized
in both of its own parts — part (1) in
`StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullback`, part (2) there
and in `StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineSchemePullbackComparison`.  What
parts (2) and (3) of tag 0GTZ need beyond it is the chart-level comparison
`AlgebraicGeometry.ComplexAndDivisorSituation.ChartDecalage`, whose three identifications the
module documentation of
`StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodTripleEtaPerfect` lists individually.

Two further hypotheses make the statement go through.  `hbd` is the local boundedness of the
family `H^n(Li^*Q)`: near every point of `T` all but finitely many of these sheaves have rank
zero.  Without it the conclusion is false as stated — an intersection of infinitely many open
and closed subsets need not be open — and it follows from perfectness of `Li^*Q`, hence from
Stacks tag 0F8U for `Q`.  `hM` is the finite local freeness of the cohomology sheaves of `M`
over `W`, which is what gives the ranks defining `W(ρ)`.  Tag 0GT1's second assertion is formalized
as `Stacks.Cohomology.PerfectComplexes.isFiniteLocallyFree_homology_restrict_locus`, over the
universe-lifted sheaf of modules on the universe-lifted locus
`Stacks.Cohomology.PerfectComplexes.cohomologyFiniteFreeLocus`; `W` is built from the plain-stalk
locus `AlgebraicGeometry.RingedSpace.cohomologyFiniteFreeLocus`, and the module documentation of
`StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.DivisorRankStrata` names the three legs
between them.

## References

* [Stacks Project, Tag 0F8Y](https://stacks.math.columbia.edu/tag/0F8Y)
* [Stacks Project, Tag 0F8S](https://stacks.math.columbia.edu/tag/0F8S)
* [Stacks Project, Tag 0F8U](https://stacks.math.columbia.edu/tag/0F8U)
* [Stacks Project, Tag 0F8X](https://stacks.math.columbia.edu/tag/0F8X)
* [Stacks Project, Tag 0GTY](https://stacks.math.columbia.edu/tag/0GTY)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace StrictlyPerfect

universe u d

namespace AlgebraicGeometry.ComplexAndDivisorSituation

attribute [local instance 10000] HasDerivedCategory.standard

variable (S : ComplexAndDivisorSituation.{u, d})

/-- **Stacks tag 0F8Y for the morphism `b : X' ⟶ X` of Stacks tag 0GTY.**  Let `b` be the
morphism of tag 0GTY, `D' = b⁻¹D`, `Q = Lη_{ℐ'}Lb^*M` the object of tag 0F8U, `i : T ⟶ D'` the
closed immersion of tag 0F8X and `ρ = (ρ_n)_{n ∈ ℤ}` ranks.  Then there is an open and closed
`T(ρ) ⊆ T` which contains the inverse image in `T` of `W(ρ)`, the rank-`ρ` stratum of the
cohomology sheaves of `M` on the locally free locus `W`, and on which `H^n(Li^*Q)` is free of
rank `ρ_n` near every point.

This is
`AlgebraicGeometry.ComplexAndDivisorSituation.exists_isClopen_rankStratum_etaDerivedPullback`
read at `AlgebraicGeometry.ComplexAndDivisorSituation.goodBlowupToBase`, whose pullback of `D` is
defined by
`AlgebraicGeometry.ComplexAndDivisorSituation.isPullbackDefined_goodBlowupToBase`.  `T(ρ)` is the
rank stratum of the family `H^n(Li^*Q)`, as in the source. -/
@[stacks 0F8Y "the rank stratum `T(ρ)` is open and closed, contains the inverse image of \
`W(ρ)` and has `H^n(Li^*Q)` free of rank `ρ_n`, stated for the morphism `b` of tag 0GTY \
itself, namely AlgebraicGeometry.ComplexAndDivisorSituation.goodBlowupToBase. The data are the \
ones tag 0F8Y is given: the closed immersion `i : T → D'` of tag 0F8X together with its parts \
(2) and (3), which are the binders `hQ` and `hrank` and are the instance at the pulled-back \
triple of parts (2) and (3) of tag 0GTZ, which need the chart-level comparison \
AlgebraicGeometry.ComplexAndDivisorSituation.ChartDecalage over and above tag 08DW --- that tag \
being formalized in both its parts; plus `hbd`, the local boundedness of the family \
`H^n(Li^*Q)`, a consequence of perfectness of `Li^*Q`, and `hM`, the finite local freeness of \
`H^n(M)` over `W`, which tag 0GT1's second assertion gives over the universe-lifted locus of \
Stacks.Cohomology.PerfectComplexes.cohomologyFiniteFreeLocus rather than over the open \
subscheme `W` built from AlgebraicGeometry.RingedSpace.cohomologyFiniteFreeLocus"]
theorem exists_isClopen_rankStratum_goodBlowupToBase
    {T : Scheme.{u}} (i : T ⟶ (S.D.comap S.goodBlowupToBase).subscheme) (ρ : ℤ → ℕ)
    (hQ : ∀ n : ℤ, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (S.etaDerivedPullbackRestrictHomology S.goodBlowupToBase
        S.isPullbackDefined_goodBlowupToBase
        (i ≫ (S.D.comap S.goodBlowupToBase).subschemeι) n))
    (hbd : ∀ t : T, ∃ V : T.Opens, t ∈ V ∧ ∃ s : Finset ℤ, ∀ n ∉ s, ∀ v ∈ V,
      @Scheme.Modules.finiteLocallyFreeRank T
        (S.etaDerivedPullbackRestrictHomology S.goodBlowupToBase
          S.isPullbackDefined_goodBlowupToBase
          (i ≫ (S.D.comap S.goodBlowupToBase).subschemeι) n)
        (hQ n) v = 0)
    (hM : ∀ n : ℤ, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (S.locallyFreeLocusCohomologySheaf n))
    (hrank : ∀ (n : ℤ) (t : T)
      (hw : ((i ≫ (S.D.comap S.goodBlowupToBase).subschemeι) ≫ S.goodBlowupToBase).base t ∈
        S.locallyFreeLocus),
      @Scheme.Modules.finiteLocallyFreeRank T
          (S.etaDerivedPullbackRestrictHomology S.goodBlowupToBase
            S.isPullbackDefined_goodBlowupToBase
            (i ≫ (S.D.comap S.goodBlowupToBase).subschemeι) n)
          (hQ n) t =
        @Scheme.Modules.finiteLocallyFreeRank S.locallyFreeLocus.toScheme
          (S.locallyFreeLocusCohomologySheaf n) (hM n)
          ⟨((i ≫ (S.D.comap S.goodBlowupToBase).subschemeι) ≫ S.goodBlowupToBase).base t, hw⟩) :
    ∃ Tρ : Set T, IsClopen Tρ ∧
      (∀ (t : T) (hw : ((i ≫ (S.D.comap S.goodBlowupToBase).subschemeι) ≫
          S.goodBlowupToBase).base t ∈ S.locallyFreeLocus),
        (⟨((i ≫ (S.D.comap S.goodBlowupToBase).subschemeι) ≫ S.goodBlowupToBase).base t, hw⟩ :
              S.locallyFreeLocus.toScheme) ∈
            Scheme.Modules.rankStratumSet S.locallyFreeLocusCohomologySheaf hM ρ →
          t ∈ Tρ) ∧
      ∀ (n : ℤ) (t : T), t ∈ Tρ →
        ∃ (V : T.Opens) (_ : t ∈ V) (I : Type u), Nonempty (I ≃ Fin (ρ n)) ∧
          Nonempty (_root_.SheafOfModules.free.{u} I ≅
            (Scheme.Modules.toRingSheafModule
              (S.etaDerivedPullbackRestrictHomology S.goodBlowupToBase
                S.isPullbackDefined_goodBlowupToBase
                (i ≫ (S.D.comap S.goodBlowupToBase).subschemeι) n)).over V) :=
  S.exists_isClopen_rankStratum_etaDerivedPullback S.goodBlowupToBase
    S.isPullbackDefined_goodBlowupToBase i ρ hQ hbd hM hrank

end AlgebraicGeometry.ComplexAndDivisorSituation

end
