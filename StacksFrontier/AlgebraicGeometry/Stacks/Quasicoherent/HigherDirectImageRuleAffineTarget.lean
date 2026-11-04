module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.HigherDirectImageRuleCechNerve
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactQuasiSeparatedCechAffineLevel
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeInverseImage

/-!
# The reduction of Stacks 0770 / 076Z to the affine case, over an affine target

Let `M` be a rule assigning to each algebraic stack a subcategory of its fppf modules
(`AlgebraicGeometry.Stack.AlgebraicStacks.ModuleRule`) and let `𝒴` be an algebraic stack
representable by an affine scheme. If `M_𝒴` is a weak Serre subcategory, if inverse images along
the projections of relative Čech nerves preserve `M`, and if the higher direct images along every
1-morphism into `𝒴` from a stack representable by an affine scheme carry `M` into `M_𝒴`, then so
do the higher direct images along every quasi-compact quasi-separated 1-morphism into `𝒴`.

This is the second half of the source's proof of Stacks 076Z, read in the fppf topology as
Stacks 0770 instructs: three applications of the relative Čech spectral sequence of Stacks 072G
part (2)(b) (`higherDirectImagesMapInto_of_cechAffineLevel`) along the geometry of
`cechAffineLevel_three_of_isQuasiCompactMorphism`. It discharges, in a stronger form, the
hypothesis `hcech` of `higherDirectImage_mem_of_quasiCompact_quasiSeparated`: no Čech
presentation of the source is asked for.

## Main definitions

* `sheafFlatBaseChangeModuleRule`: the faithful `LQCoh^fbc` at module universe `u + 1`, as a rule.

## Main results

* `higherDirectImagesMapInto_of_isAffineRepresentable_target`: the reduction above, for a
  rule `M` over a target representable by an affine scheme.
* `sheafFlatBaseChange_fppfModulePullback`: the faithful `LQCoh^fbc` at module universe `u + 1`
  is stable under inverse image along every 1-morphism of algebraic stacks (Stacks 0771
  part (3)).
* `sheafFlatBaseChange_higherDirectImage_of_isAffineRepresentable_target`: the reduction for the
  faithful `LQCoh^fbc` at module universe `u + 1`, over an affine target, from its weak Serre
  property on the target and its affine case.

## References

* [Stacks Project, Tag 076Z](https://stacks.math.columbia.edu/tag/076Z)
* [Stacks Project, Tag 0770](https://stacks.math.columbia.edu/tag/0770)
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

attribute [local instance] hasSheafify_fppfAssociatedTopology
  wEqualsLocallyBijective_fppfAssociatedTopology

/-- **Stacks 0770 / 076Z over an affine target.** Let `M` be a rule with `M_𝒴` a weak Serre
subcategory, `𝒴` representable by an affine scheme, inverse images along the projections of
relative Čech nerves preserving `M`, and the affine case: the higher direct images along every
1-morphism into `𝒴` from a stack representable by an affine scheme carry `M` into `M_𝒴`. Then the
higher direct images along every quasi-compact quasi-separated `f : 𝒳 ⟶ 𝒴` carry `M_𝒳` into
`M_𝒴`. -/
theorem higherDirectImagesMapInto_of_isAffineRepresentable_target (M : ModuleRule.{u, w} B S hS)
    {𝒴 : AlgebraicStacks.{u, w} B S hS} [(M 𝒴).IsWeakSerreClass]
    (h𝒴 : IsAffineRepresentable B S hS 𝒴)
    (hpull : ∀ {𝒰 𝒳 : AlgebraicStacks.{u, w} B S hS} (c : 𝒰 ⟶ 𝒳) (n : ℕ)
      (F : fppfModules B S hS 𝒳), M 𝒳 F →
        M (cechNerveStack B S hS c n)
          ((fppfModulePullback B S hS (cechNerveStackProjection B S hS c n)).obj F))
    (hAffine : ∀ {𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴),
      IsAffineRepresentable B S hS 𝒳 → HigherDirectImagesMapInto B S hS M f)
    {𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hqc : IsQuasiCompactMorphism B S hS f) (hqs : IsQuasiSeparated B S hS f) :
    HigherDirectImagesMapInto B S hS M f :=
  higherDirectImagesMapInto_of_cechAffineLevel B S hS M hpull hAffine 3
    (cechAffineLevel_three_of_isQuasiCompactMorphism B S hS f h𝒴 hqc hqs) f

variable (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)

/-- The faithful `LQCoh^fbc` at module universe `u + 1`, read as a rule in the sense of
Stacks 0770: to each algebraic stack the subcategory of its fppf modules which are locally
quasi-coherent with the flat base change property of Stacks 0762. -/
abbrev sheafFlatBaseChangeModuleRule : ModuleRule.{u, w} B S hS :=
  fun 𝒵 => lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS 𝒵

/-- **Stacks 0771 part (3) for the faithful `LQCoh^fbc` at module universe `u + 1`, in the shape
of the reduction:** the inverse image along any 1-morphism of algebraic stacks carries a module
locally quasi-coherent with the flat base change property of Stacks 0762 into one. -/
theorem sheafFlatBaseChange_fppfModulePullback {𝒳 𝒵 : AlgebraicStacks.{u, w} B S hS}
    (g : 𝒵 ⟶ 𝒳) (F : fppfModules B S hS 𝒳)
    (hF : lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS 𝒳 F) :
    lqcohSheafFbcFppfModules.{u, w, u + 1} B E h S hS 𝒵
      ((fppfModulePullback B S hS g).obj F) :=
  isLocallyQuasicoherentWithSheafFlatBaseChangeUnivLE_modulePullback B E h S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids 𝒵.val.val.p 𝒵.val.isFiberedInGroupoids
    (CatFiberedInGroupoids.homFunctor g.hom) (CatFiberedInGroupoids.homFunctor_comp_p g.hom)
    B.topology le_rfl F hF

/-- **The reduction of Stacks 0771 part (4)(b) to the affine case, over an affine target**, for
the faithful `LQCoh^fbc` at module universe `u + 1`, in the fppf topology. If `LQCoh^fbc(𝒪_𝒴)` is
a weak Serre subcategory of `Mod(𝒪_𝒴)` for the target `𝒴`, representable by an affine scheme, and
the higher direct images along every 1-morphism into `𝒴` from a stack representable by an affine
scheme carry `LQCoh^fbc` into `LQCoh^fbc(𝒪_𝒴)`, then so do those along every quasi-compact
quasi-separated `f : 𝒳 ⟶ 𝒴`. The two hypotheses are Stacks 0771 part (2) on `𝒴` and the affine
case of the proof of Stacks 0765 / 0771; the pullback stability the reduction also uses is
`AlgebraicGeometry.Stack.AlgebraicStacks.sheafFlatBaseChange_fppfModulePullback`. -/
theorem sheafFlatBaseChange_higherDirectImage_of_isAffineRepresentable_target
    {𝒴 : AlgebraicStacks.{u, w} B S hS}
    [(sheafFlatBaseChangeModuleRule B S hS E h 𝒴).IsWeakSerreClass]
    (h𝒴 : IsAffineRepresentable B S hS 𝒴)
    (hAffine : ∀ {𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴),
      IsAffineRepresentable B S hS 𝒳 →
        HigherDirectImagesMapInto B S hS (sheafFlatBaseChangeModuleRule B S hS E h) f)
    {𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hqc : IsQuasiCompactMorphism B S hS f) (hqs : IsQuasiSeparated B S hS f) :
    HigherDirectImagesMapInto B S hS (sheafFlatBaseChangeModuleRule B S hS E h) f :=
  higherDirectImagesMapInto_of_isAffineRepresentable_target B S hS
    (sheafFlatBaseChangeModuleRule B S hS E h) h𝒴
    (fun c n => sheafFlatBaseChange_fppfModulePullback B S hS E h
      (cechNerveStackProjection B S hS c n)) hAffine f hqc hqs

end AlgebraicGeometry.Stack.AlgebraicStacks

end
