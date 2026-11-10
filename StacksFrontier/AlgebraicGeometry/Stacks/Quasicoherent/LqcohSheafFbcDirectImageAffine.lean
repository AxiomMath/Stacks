module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AffineDirectImageVanishing
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AffineFlatBaseChangeSections
public import
  StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentHigherDirectImage
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeAffineCriterion
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeRule
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeWeakSerre

/-!
# Clauses (1) and (4) of Stacks 076Z for the rule `LQCoh^fbc`

Let `LQCoh^fbc` be the rule (`AlgebraicGeometry.Stack.lqcohSheafFbcModuleRule`) of locally
quasi-coherent modules on the étale sites with the flat base change property of **Stacks 0762**.
It satisfies clauses (1) and (4) of the criterion of **Stacks 076Z**.

* **Clause (1)**: `LQCoh^fbc(𝒪_𝒳)` is a weak Serre subcategory of `Mod(𝒳_étale, 𝒪_𝒳)`.
* **Clause (4)**: for a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks represented by affine schemes
  the higher direct images `Rⁱf_*` preserve `LQCoh^fbc`.

## Main results

* `isWeakSerre_lqcohSheafFbcModuleRule`: clause (1).
* `lqcohSheafFbcModuleRule_stackModuleDirectImage_of_isAffineRepresentable`: the direct image
  along a 1-morphism of algebraic stacks representable by affine schemes preserves `LQCoh^fbc`.
* `preservesHigherDirectImagesOfAffine_lqcohSheafFbcModuleRule`: clause (4).

All three are in the namespace `AlgebraicGeometry.Stack`.

## References

* [Stacks Project, Tag 0765](https://stacks.math.columbia.edu/tag/0765)
* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
* [Stacks Project, Tag 076Z](https://stacks.math.columbia.edu/tag/076Z)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u t

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

/-- **Clause (1) of Stacks 076Z for `LQCoh^fbc`**: at every algebraic stack the rule cuts out a
weak Serre subcategory of `Mod(𝒳_étale, 𝒪_𝒳)` (**Stacks 0771** part (2), étale half). -/
theorem isWeakSerre_lqcohSheafFbcModuleRule :
    StackModuleRule.IsWeakSerre .etale (lqcohSheafFbcModuleRule.{u, t} B E h S hS) :=
  fun 𝒳 ↦ isWeakSerreClass_lqcohSheafFbcEtaleModules B E h S hS 𝒳

/-- **The direct image along a 1-morphism of algebraic stacks represented by affine schemes
preserves `LQCoh^fbc`.** For `f : 𝒳 ⟶ 𝒴` with `𝒳` and `𝒴` representable by affine schemes and `F`
locally quasi-coherent on `𝒳_étale` with the flat base change property, `f_*F` is locally
quasi-coherent with the flat base change property. -/
theorem lqcohSheafFbcModuleRule_stackModuleDirectImage_of_isAffineRepresentable
    {𝒳 𝒴 : AlgebraicStacks.{u, t} B S hS} (f : 𝒳 ⟶ 𝒴)
    (h𝒳 : AlgebraicStacks.IsAffineRepresentable B S hS 𝒳)
    (h𝒴 : AlgebraicStacks.IsAffineRepresentable B S hS 𝒴)
    (F : StackModules B S hS .etale 𝒳) (hF : lqcohSheafFbcModuleRule B E h S hS 𝒳 F) :
    lqcohSheafFbcModuleRule B E h S hS 𝒴 ((stackModuleDirectImage B S hS f .etale).obj F) := by
  have hlqc := isLocallyQuasicoherent_stackModuleDirectImage_of_isAffineRepresentable B S hS E h
    f h𝒳 h𝒴 F hF.1
  exact ⟨hlqc, hasSheafFlatBaseChangeProperty_of_isIso_restrictionBaseChange B E h S hS _ _ _
    fun {_ _} φ hy hy' hφ ↦ isIso_restrictionBaseChange_stackModuleDirectImage B S hS @Flat .etale
      f h𝒳 h𝒴 F (fun _ _ ψ hx hx' hψ ↦
        isIso_restrictionBaseChange_of_flat B E h S hS _ _ F.val hF ψ hψ hx hx') φ hy hy' hφ⟩

/-- **Clause (4) of Stacks 076Z for `LQCoh^fbc`**: for a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic
stacks representable by affine schemes the higher direct images `Rⁱf_*`, computed in the étale
topology, carry `LQCoh^fbc(𝒪_𝒳)` into `LQCoh^fbc(𝒪_𝒴)` in every degree. -/
theorem preservesHigherDirectImagesOfAffine_lqcohSheafFbcModuleRule :
    StackModuleRule.PreservesHigherDirectImagesOfAffine
      (stackModuleDirectImageData.{u, t} B S hS .etale)
      (lqcohSheafFbcModuleRule.{u, t} B E h S hS) := by
  rintro 𝒳 𝒴 f h𝒳 h𝒴 (_ | i) F hF
  · have := isWeakSerre_lqcohSheafFbcModuleRule B E h S hS 𝒴
    exact (lqcohSheafFbcModuleRule B E h S hS 𝒴).prop_of_iso
        ((StackModuleDirectImage.higherDirectImageZeroIso B S hS _ f).app F).symm
        (lqcohSheafFbcModuleRule_stackModuleDirectImage_of_isAffineRepresentable B E h S hS f h𝒳
          h𝒴 F hF)
  · exact lqcohSheafFbcModuleRule_of_isZero B E h S hS 𝒴
      (isZero_stackModuleHigherDirectImage_of_isAffineRepresentable B E h S hS f h𝒳 h𝒴 F hF.1
        (i + 1) (Nat.succ_pos i))

end AlgebraicGeometry.Stack
