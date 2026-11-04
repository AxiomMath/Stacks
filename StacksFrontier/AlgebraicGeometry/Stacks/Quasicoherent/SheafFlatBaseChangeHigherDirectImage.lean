module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FppfModuleHigherDirectImageBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeAffineChartLocality
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactMorphismPermanence
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationEquivalenceInvariance

/-!
# Higher direct images of the faithful `LQCoh^fbc`: reduction to the affine case

Let `f : 𝒳 ⟶ 𝒴` be a quasi-compact and quasi-separated 1-morphism of algebraic stacks over `S`
and `ℱ` a module on the fppf site of `𝒳` in the faithful `LQCoh^fbc(𝒪_𝒳)`, at module universe
`u + 1`. Stacks 0771 part (4)(b) says that every `Rⁱf_* ℱ`, computed in the fppf topology, lies in
`LQCoh^fbc(𝒪_𝒴)`. The source's proof is Stacks 0770: reduce to an affine target along the
base change of higher direct images (Stacks 075H), then to an affine source by the relative Čech
spectral sequence (Stacks 072G), and conclude by the affine case.

This file assembles that argument for the fppf reading, from two inputs at the targets
`Sch/V`, `V` affine: the weak Serre property of `LQCoh^fbc(𝒪_{Sch/V})` (Stacks 0771 part (2)) and
the affine case (higher direct images along 1-morphisms between stacks representable by affine
schemes carry the class into the class). Everything else is proved:

* the reduction to an affine target is pointwise: membership of `Rⁱf_* ℱ` is detected on the
  charts `y : Sch/V ⟶ 𝒴` of the objects of `𝒴` over affine schemes
  (`AlgebraicGeometry.Stack.sheafFlatBaseChangeModuleRule_of_objectStackMap`), and along such a
  chart higher direct images commute with base change
  (`AlgebraicGeometry.Stack.AlgebraicStacks.fppfHigherDirectImageBaseChangeIso`, Stacks 075H);
* the base change of `f` is again quasi-compact and quasi-separated (Stacks 050V, 04YW), the
  inverse image of `ℱ` stays in the class (Stacks 0771 part (3)), and over the affine target
  `Sch/V` the reduction to the affine case is the theorem
  `sheafFlatBaseChange_higherDirectImage_of_isAffineRepresentable_target`.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.sheafFlatBaseChange_higherDirectImage_of_affine`.

## References

* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
* [Stacks Project, Tag 0770](https://stacks.math.columbia.edu/tag/0770)
* [Stacks Project, Tag 075H](https://stacks.math.columbia.edu/tag/075H)
* [Stacks Project, Tag 072G](https://stacks.math.columbia.edu/tag/072G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)

attribute [local instance] hasSheafify_fppfAssociatedTopology
  wEqualsLocallyBijective_fppfAssociatedTopology

/-- **Stacks 0771 part (4)(b), reduced to the affine case**, for the faithful `LQCoh^fbc` at
module universe `u + 1`, in the fppf topology. Suppose `LQCoh^fbc(𝒪_{Sch/V})` is a weak Serre
subcategory for every affine `V` (Stacks 0771 part (2) at those targets) and the higher direct
images along every 1-morphism between stacks representable by affine schemes carry the class
into the class (the affine case). Then for every quasi-compact quasi-separated `f : 𝒳 ⟶ 𝒴` the
higher direct images `Rⁱf_*` carry `LQCoh^fbc(𝒪_𝒳)` into `LQCoh^fbc(𝒪_𝒴)`. -/
theorem sheafFlatBaseChange_higherDirectImage_of_affine
    (hSerre : ∀ V : BigFppfOver B S hS, IsAffine ((BigFppfOver.toScheme B S hS).obj V) →
      (sheafFlatBaseChangeModuleRule B S hS E h (schemeStack.{u, w} B S hS V)).IsWeakSerreClass)
    (hAffine : AffineHigherDirectImagesMapInto.{u, w} B S hS
      (sheafFlatBaseChangeModuleRule.{u, w} B S hS E h))
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hqc : IsQuasiCompactMorphism B S hS f) (hqs : IsQuasiSeparated B S hS f) :
    HigherDirectImagesMapInto B S hS (sheafFlatBaseChangeModuleRule B S hS E h) f := by
  intro i F hF
  refine sheafFlatBaseChangeModuleRule_of_objectStackMap _ fun y hy => ?_
  let g := objectStackMap B S hS 𝒴 y
  have := hSerre _ hy
  have : (schemeStack.{u, w} B S hS (𝒴.val.val.p.obj y)).val.val.p.Faithful :=
    inferInstanceAs (Over.forget (𝒴.val.val.p.obj y)).Faithful
  let P := twoFibreProductSquareAlgebraicStacks B S hS f g
  have hP := isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS f g
  have hqc' : IsQuasiCompactMorphism B S hS P.snd :=
    isQuasiCompactMorphism_baseChange B S hS f g P.swap (Bicategory.isTwoFibreProduct_swap hP) hqc
  have hqs' : IsQuasiSeparated B S hS P.snd :=
    isQuasiSeparated_baseChange_of_isTwoFibreProduct B S hS f g P hP hqs
  have hmem := sheafFlatBaseChange_higherDirectImage_of_isAffineRepresentable_target B S hS E h
    (isAffineRepresentable_schemeStack.{u, w} B S hS _ hy)
    (fun f' h𝒳 => hAffine f' h𝒳 (isAffineRepresentable_schemeStack.{u, w} B S hS _ hy))
    P.snd hqc' hqs' i _ (sheafFlatBaseChange_fppfModulePullback B S hS E h P.fst F hF)
  exact (sheafFlatBaseChangeModuleRule B S hS E h _).prop_of_iso
    (fppfHigherDirectImageBaseChangeIso B S hS f g i F).symm hmem

end AlgebraicGeometry.Stack.AlgebraicStacks

end
