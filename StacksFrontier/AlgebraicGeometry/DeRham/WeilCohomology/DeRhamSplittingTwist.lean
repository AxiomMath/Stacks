module

public import StacksFrontier.AlgebraicGeometry.DeRham.WeilCohomology.DeRhamTotalChernClass
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.TwistFormula
import StacksCore.Tactic.StacksAttribute

/-!
# The splitting principle and Chern classes of twists for de Rham Chern classes (Tag 0FWA)

The category of quasi-compact and quasi-separated schemes with `A(X) = ⨁_i H^{2i}_{dR}(X/𝐙)`
satisfies all the axioms of Section 0FI4 (`Stacks.DeRhamChern.deRhamSourceChernSetup`, the proof
of Tag 0FW9). Hence the general results of that section hold for de Rham cohomology:

* the splitting principle, Tag 0FI7: for finitely many finite locally free modules `ℰ_i` of
  ranks `r_i` on a quasi-compact and quasi-separated scheme `X` there is a morphism `p : P ⟶ X`
  of quasi-compact and quasi-separated schemes with `p^* : ⨁_i H^{2i}_{dR}(X/𝐙) ⟶
  ⨁_i H^{2i}_{dR}(P/𝐙)` injective and each `p^*ℰ_i` filtered with invertible successive
  quotients;
* the Chern classes of a twist, Tag 0FI8:
  `c^{dR}_i(ℰ ⊗ ℒ) = ∑_{j=0}^{i} binom(r - i + j, j) c^{dR}_{i-j}(ℰ) ∪ c₁^{dR}(ℒ)^j`.

## Main results

* `Stacks.DeRhamChern.exists_injective_pull_hasInvertibleFiltration`: **Tag 0FWA**, the
  splitting principle.
* `Stacks.DeRhamChern.IsDeRhamTotalChernClass.apply_classOf_tensorObj_invertible`: the Chern
  classes of a twist in degrees `i ≤ r`; every degree is
  `Stacks.DeRhamChern.IsDeRhamTotalChernClass.apply_classOf_tensorObj_invertible_of_any`
  (**Tag 0FWA**).

## References

* [Stacks Project, Tag 0FWA](https://stacks.math.columbia.edu/tag/0FWA)
* [Stacks Project, Tag 0FI7](https://stacks.math.columbia.edu/tag/0FI7)
* [Stacks Project, Tag 0FI8](https://stacks.math.columbia.edu/tag/0FI8)
* [Stacks Project, Tag 0FW9](https://stacks.math.columbia.edu/tag/0FW9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.WeilCohomology Stacks.DeRhamBaseChange

attribute [local instance] Stacks.Cohomology.Generators.picardGroupAddCommGroup

namespace Stacks.DeRhamChern

/-- **Stacks Project, Tag 0FWA: the splitting principle for de Rham cohomology.** Let `X` be a
quasi-compact and quasi-separated scheme and let `ℰ_i` be a finite collection of locally free
`𝒪_X`-modules of ranks `r_i`. There is a morphism `p : P ⟶ X` of quasi-compact and
quasi-separated schemes such that

1. `p^* : ⨁_i H^{2i}_{dR}(X/𝐙) ⟶ ⨁_i H^{2i}_{dR}(P/𝐙)` is injective,
2. each `p^*ℰ_i` has a filtration whose successive quotients `ℒ_{i,1}, …, ℒ_{i,r_i}` are
   invertible `𝒪_P`-modules.

The projection is moreover flat. This is Tag 0FI7 in the de Rham situation of the proof of
Tag 0FW9. -/
@[stacks 0FWA "the analogue of Weil Cohomology Theories, Lemma 0FI7 (splitting principle) holds \
for de Rham Chern classes on quasi-compact and quasi-separated schemes: for a finite collection \
of locally free O_X-modules E_i of ranks r_i there is p : P -> X with p^* injective on \
(+)_i H^{2i}_dR(-/Z) and each p^*E_i filtered with invertible successive quotients"]
theorem exists_injective_pull_hasInvertibleFiltration
    (X : (QCQSScheme (Spec (CommRingCat.of ℤ))).FullSubcategory) (I : Type*) [Finite I]
    (E : I → ((QCQSScheme.toScheme (Spec (CommRingCat.of ℤ))).obj X).Modules) (r : I → ℕ)
    (hE : ∀ i, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} (E i) (r i)) :
    ∃ (P : (QCQSScheme (Spec (CommRingCat.of ℤ))).FullSubcategory) (p : P ⟶ X),
      Flat ((QCQSScheme.toScheme (Spec (CommRingCat.of ℤ))).map p) ∧
      Function.Injective (pull (QCQSScheme (Spec (CommRingCat.of ℤ))).ι p) ∧
      ∀ i, HasInvertibleFiltration ((QCQSScheme.toScheme (Spec (CommRingCat.of ℤ))).obj P)
        ((Scheme.Modules.pullback ((QCQSScheme.toScheme (Spec (CommRingCat.of ℤ))).map p)).obj
          (E i)) (r i) :=
  deRhamSourceChernSetup.toChernSetup.exists_injective_hasInvertibleFiltration X I E r hE

/-- **The Chern classes of a twist for de Rham Chern classes, in degrees at most the rank.** Let
`c^{dR}` be the de Rham total Chern class of Tag 0FW9 (by that lemma there is exactly one rule with
its three properties), let `X` be a quasi-compact and quasi-separated scheme, `ℰ` a finite locally
free `𝒪_X`-module of constant rank `r` and `ℒ` an invertible `𝒪_X`-module. Then for `i ≤ r`

`c^{dR}_i(ℰ ⊗ ℒ) = ∑_{j=0}^{i} binom(r - i + j, j) c^{dR}_{i-j}(ℰ) ∪ c₁^{dR}(ℒ)^j`

in `H^{2i}_{dR}(X/𝐙)`, with the binomial coefficient written `(r - i + j).choose j`. This is
Tag 0FI8 in the de Rham situation of the proof of Tag 0FW9. The formula in every degree `i` is
`Stacks.DeRhamChern.IsDeRhamTotalChernClass.apply_classOf_tensorObj_invertible_of_any`. -/
theorem IsDeRhamTotalChernClass.apply_classOf_tensorObj_invertible
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
    (i : ℕ) (hi : i ≤ r) :
    c X (VectorBundleKZero.classOf _
        (Scheme.Modules.tensorObjRingedSpace
          ((QCQSScheme (Spec (CommRingCat.of ℤ))).ι.obj X).left E L)) i =
      ∑ j ∈ Finset.range (i + 1), (r - i + j).choose j •
        (c X (VectorBundleKZero.classOf _ E) (i - j) *
          c₁ (QCQSScheme (Spec (CommRingCat.of ℤ))).ι X
            (picardClassOf ((QCQSScheme (Spec (CommRingCat.of ℤ))).ι.obj X).left L hL) ^ j) :=
  ((isTotalChernClassOnLocallyFree_chernSetup_iff (QCQSScheme (Spec (CommRingCat.of ℤ))).ι
    (fun X E r hE => (QCQSScheme.bundleObject X E r hE).toBundleDatum)
    (bundleFormula_qcqs (Spec (CommRingCat.of ℤ))) c).mpr hc).apply_classOf_tensorObj_invertible
      X E L r hE hL i hi

end Stacks.DeRhamChern

end
