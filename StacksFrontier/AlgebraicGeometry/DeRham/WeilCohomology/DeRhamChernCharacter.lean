module

public import StacksFrontier.AlgebraicGeometry.DeRham.WeilCohomology.DeRhamTotalChernClass
public import StacksFrontier.AlgebraicGeometry.DeRham.WeilCohomology.DeRhamSourceChernSetup
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.ChernCharacterExistence
import StacksCore.Tactic.StacksAttribute

/-!
# The de Rham Chern character (Tag 0FWB)

There is a unique rule which assigns to every quasi-compact and quasi-separated scheme `X` over
`𝐐` a Chern character `ch^{dR} : K₀(Vect(X)) ⟶ ∏_{i ≥ 0} H^{2i}_{dR}(X/𝐐)` such that

1. `ch^{dR}` is a ring map,
2. `f^* ∘ ch^{dR} = ch^{dR} ∘ f^*` for every morphism `f : X' ⟶ X` of quasi-compact and
   quasi-separated schemes over `𝐐`,
3. `ch^{dR}([ℒ]) = exp(c₁^{dR}(ℒ))` for `ℒ ∈ Pic(X)`.

The proof is the source's: exactly as for Tag 0FW9, the category of quasi-compact and
quasi-separated schemes over `𝐐` with `A(X) = ⨁_i H^{2i}_{dR}(X/𝐐)` satisfies the axioms of
Section 0FI4 (`Stacks.DeRhamChern.sourceChernSetup` over `Spec 𝐐`, with the projective bundle
formula `Stacks.DeRhamChern.bundleFormula_qcqs` of Proposition 0FMT); moreover `A(X)` is a
`𝐐`-algebra (`Stacks.DeRhamChern.algebraRat`), so Proposition 0FI9 applies.

## Main results

* `Stacks.DeRhamChern.sourceChernSetupRat`: the de Rham situation over `𝐐`.
* `Stacks.DeRhamChern.existsUnique_deRhamChernCharacter`: **Tag 0FWB**.

## References

* [Stacks Project, Tag 0FWB](https://stacks.math.columbia.edu/tag/0FWB)
* [Stacks Project, Tag 0FI9](https://stacks.math.columbia.edu/tag/0FI9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.WeilCohomology Stacks.DeRhamBaseChange

attribute [local instance] Stacks.Cohomology.Generators.picardGroupAddCommGroup

namespace Stacks.DeRhamChern

/-- The base `Spec 𝐐`. -/
abbrev specRat : Scheme.{0} := Spec (CommRingCat.of ℚ)

/-- **The standing situation of Section 45.12 for even-degree de Rham cohomology over `𝐐`**:
quasi-compact and quasi-separated schemes over `𝐐` with `A(X) = ⨁_i H^{2i}_{dR}(X/𝐐)`. -/
abbrev sourceChernSetupRat :
    SourceChernSetup.{0, 0, 0, 1} (QCQSScheme specRat).FullSubcategory
      (QCQSScheme.toScheme specRat) :=
  sourceChernSetup specRat (bundleFormula_qcqs specRat)

/-- **Stacks Project, Tag 0FWB.** There is a unique rule which assigns to every quasi-compact and
quasi-separated scheme `X` over `𝐐` a Chern character
`ch^{dR} : K₀(Vect(X)) ⟶ ∏_{i ≥ 0} H^{2i}_{dR}(X/𝐐)` such that (1) `ch^{dR}` is a ring map,
(2) `f^* ∘ ch^{dR} = ch^{dR} ∘ f^*` for every morphism `f : X' ⟶ X` of quasi-compact and
quasi-separated schemes over `𝐐`, and (3) `ch^{dR}([ℒ]) = exp(c₁^{dR}(ℒ))` for `ℒ ∈ Pic(X)`.

An element of `∏_{i ≥ 0} H^{2i}_{dR}(X/𝐐)` is the sequence of its components, the `i`-th read in
`⨁_j H^{2j}_{dR}(X/𝐐)` and lying in `H^{2i}_{dR}(X/𝐐)`; the properties are
`Stacks.DeRhamChern.IsDeRhamChernCharacter`. The proof is the source's: the category of
quasi-compact and quasi-separated schemes over `𝐐` with `A(X) = ⨁_i H^{2i}_{dR}(X/𝐐)` satisfies
the axioms of Section 45.12, and `A(X)` is a `𝐐`-algebra, so Proposition 0FI9 applies. -/
@[stacks 0FWB "the unique rule ch^dR : K_0(Vect(X)) -> prod_i H^{2i}_dR(X/Q) on quasi-compact \
  quasi-separated schemes X over Q, with (1) ch^dR a ring map, (2) f^* ch^dR = ch^dR f^* on all \
  of K_0 for every morphism f : X' -> X of quasi-compact quasi-separated schemes over Q, (3) \
  ch^dR([L]) = exp(c_1^dR(L)) for L in Pic(X); prod H^{2i} read as sequences of components in \
  ⨁ H^{2j} with the i-th in H^{2i}. Proved from Tag 0FI9 at the standing situation \
  sourceChernSetupRat, whose axioms are all proved: (1) Tag 0FM3, (2) the clopen splitting, \
  (3) Tag 0FMD, (4) Proposition 0FMT, (5) Lemmas 0FMX and 0FMY, clauses (1)-(3)(c) of the \
  category"]
theorem existsUnique_deRhamChernCharacter :
    ∃! ch : ∀ X : (QCQSScheme specRat).FullSubcategory,
        VectorBundleKZero X.obj.left → ℕ → evenDeRhamRing X.obj.hom,
      IsDeRhamChernCharacter (QCQSScheme specRat).ι ch :=
  (existsUnique_congr fun ch => isChernCharacterOnLocallyFree_chernSetup_iff
    (hQ := fun X => algebraRat X.obj.hom) (QCQSScheme specRat).ι
    (fun X E r hE => (QCQSScheme.bundleObject X E r hE).toBundleDatum)
    (bundleFormula_qcqs specRat) ch).mp
    (@existsUnique_isChernCharacter_of_source _ _ _ sourceChernSetupRat
      (fun X => algebraRat X.obj.hom) (fun X q => algebraMap_rat_mem_grade_zero X.obj.hom q)
      (pullbackFirstChernCondition_sourceChernSetup specRat (bundleFormula_qcqs specRat))
      (bundleCompareClause_sourceChernSetup specRat (bundleFormula_qcqs specRat))
      (divisorDatumClause_sourceChernSetup specRat (bundleFormula_qcqs specRat)))

end Stacks.DeRhamChern

end
