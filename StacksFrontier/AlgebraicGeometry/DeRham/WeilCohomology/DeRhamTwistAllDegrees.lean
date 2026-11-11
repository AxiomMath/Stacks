module

public import StacksFrontier.AlgebraicGeometry.DeRham.WeilCohomology.DeRhamSplittingTwist
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.TwistFormulaAllDegrees
import StacksCore.Tactic.StacksAttribute

/-!
# The Chern classes of a twist for de Rham Chern classes, in every degree (Tag 0FWA)

Tag 0FWA says that the analogues of Weil Cohomology Theories, Lemmas 0FI7 (splitting principle)
and 0FI8 (Chern classes of tensor products) hold for de Rham Chern classes on quasi-compact and
quasi-separated schemes, because by the proof of Tag 0FW9 the category of such schemes with
`A(X) = ⨁_i H^{2i}_{dR}(X/𝐙)` satisfies all the axioms of Section 0FI4
(`Stacks.DeRhamChern.deRhamSourceChernSetup`).

The splitting principle is `Stacks.DeRhamChern.exists_injective_pull_hasInvertibleFiltration`.
This file states the twist formula in every degree `i`:
`c^{dR}_i(ℰ ⊗ ℒ) = ∑_{j=0}^{i} binom(r - i + j, j) c^{dR}_{i-j}(ℰ) ∪ c₁^{dR}(ℒ)^j`.

## Main results

* `Stacks.DeRhamChern.IsDeRhamTotalChernClass.apply_classOf_tensorObj_invertible_of_any`:
  **Tag 0FWA**, the Chern classes of a twist, for every degree.

## References

* [Stacks Project, Tag 0FWA](https://stacks.math.columbia.edu/tag/0FWA)
* [Stacks Project, Tag 0FI8](https://stacks.math.columbia.edu/tag/0FI8)
* [Stacks Project, Tag 0FW9](https://stacks.math.columbia.edu/tag/0FW9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.WeilCohomology Stacks.DeRhamBaseChange

attribute [local instance] Stacks.Cohomology.Generators.picardGroupAddCommGroup

namespace Stacks.DeRhamChern

/-- **Stacks Project, Tag 0FWA: the Chern classes of a twist for de Rham Chern classes.** Let
`c^{dR}` be the de Rham total Chern class of Tag 0FW9 (by that lemma there is exactly one rule with
its three properties), let `X` be a quasi-compact and quasi-separated scheme, `ℰ` a finite locally
free `𝒪_X`-module of constant rank `r` and `ℒ` an invertible `𝒪_X`-module. Then for every `i`

`c^{dR}_i(ℰ ⊗ ℒ) = ∑_{j=0}^{i} binom(r - i + j, j) c^{dR}_{i-j}(ℰ) ∪ c₁^{dR}(ℒ)^j`

in `H^{2i}_{dR}(X/𝐙)`, the binomial coefficient written `(r + j - i).choose j`: it equals
`binom(r - i + j, j)` whenever `r - i + j ≥ 0`, and otherwise `i - j > r` and the factor
`c^{dR}_{i-j}(ℰ)` vanishes. This is Tag 0FI8 in the de Rham situation of the proof of Tag 0FW9;
the splitting principle half of Tag 0FWA is
`Stacks.DeRhamChern.exists_injective_pull_hasInvertibleFiltration`. -/
@[stacks 0FWA "the analogue of Weil Cohomology Theories, Lemma 0FI8 (chern classes of tensor \
products) holds for de Rham Chern classes on quasi-compact and quasi-separated schemes: for the \
de Rham total Chern class c^dR of Tag 0FW9, E finite locally free of constant rank r, L \
invertible and every i, c^dR_i(E (x) L) = sum_{j=0}^i binom(r-i+j, j) c^dR_{i-j}(E) cup \
c_1^dR(L)^j, binom(r-i+j, j) written (r + j - i).choose j in N, which agrees with it wherever \
c^dR_{i-j}(E) is nonzero. The analogue of Lemma 0FI7 is \
exists_injective_pull_hasInvertibleFiltration"]
theorem IsDeRhamTotalChernClass.apply_classOf_tensorObj_invertible_of_any
    {c : ∀ X : (QCQSScheme (Spec (CommRingCat.of ℤ))).FullSubcategory,
      VectorBundleKZero ((QCQSScheme (Spec (CommRingCat.of ℤ))).ι.obj X).left → ℕ →
        evenDeRhamRing ((QCQSScheme (Spec (CommRingCat.of ℤ))).ι.obj X).hom}
    (hc : IsDeRhamTotalChernClass (QCQSScheme (Spec (CommRingCat.of ℤ))).ι c)
    (X : (QCQSScheme (Spec (CommRingCat.of ℤ))).FullSubcategory)
    (E L : ((QCQSScheme (Spec (CommRingCat.of ℤ))).ι.obj X).left.Modules) (r : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} E r)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible
      ((QCQSScheme (Spec (CommRingCat.of ℤ))).ι.obj X).left.presheaf
      ((QCQSScheme (Spec (CommRingCat.of ℤ))).ι.obj X).left.ringCatSheaf.2 L)
    (i : ℕ) :
    c X (VectorBundleKZero.classOf _
        (Scheme.Modules.tensorObjRingedSpace
          ((QCQSScheme (Spec (CommRingCat.of ℤ))).ι.obj X).left E L)) i =
      ∑ j ∈ Finset.range (i + 1), (r + j - i).choose j •
        (c X (VectorBundleKZero.classOf _ E) (i - j) *
          c₁ (QCQSScheme (Spec (CommRingCat.of ℤ))).ι X
            (picardClassOf ((QCQSScheme (Spec (CommRingCat.of ℤ))).ι.obj X).left L hL) ^ j) :=
  ((isTotalChernClassOnLocallyFree_chernSetup_iff (QCQSScheme (Spec (CommRingCat.of ℤ))).ι
    (fun X E r hE => (QCQSScheme.bundleObject X E r hE).toBundleDatum)
    (bundleFormula_qcqs (Spec (CommRingCat.of ℤ))) c).mpr
      hc).apply_classOf_tensorObj_invertible_of_any X E L r hE hL i

end Stacks.DeRhamChern

end
