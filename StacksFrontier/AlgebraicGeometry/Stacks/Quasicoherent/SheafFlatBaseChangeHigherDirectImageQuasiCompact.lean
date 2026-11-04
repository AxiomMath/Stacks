module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeHigherDirectImage
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeAffineDirectImage
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeAffineModuleVanishingLargeSections
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeFppfWeakSerreLargeSections
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FppfHigherDirectImageVanishingOfTerminalFibres

/-!
# Higher direct images of the faithful `LQCoh^fbc` along quasi-compact quasi-separated morphisms

**Stacks 0771 part (4)(b)**, fppf reading, for the faithful `LQCoh^fbc` (locally quasi-coherent
modules with the flat base change property of Stacks 0762 read with the pullback of sheaves) at
module universe `u + 1`, the universe in which the higher direct images of modules on the fppf
sites of algebraic stacks are constructed: for a quasi-compact quasi-separated 1-morphism
`f : 𝒳 ⟶ 𝒴` of algebraic stacks, `Rⁱf_*` carries `LQCoh^fbc(𝒪_𝒳)` into `LQCoh^fbc(𝒪_𝒴)` for every
`i`. Nothing is assumed.

The source proves it with the criterion of Stacks 0770; its reduction to the affine case for the
faithful class is `Stack.AlgebraicStacks.sheafFlatBaseChange_higherDirectImage_of_affine`, which
asks for two inputs, both supplied here:

* Stacks 0771 part (2) at the affine charts: the class is a weak Serre subcategory
  (`Stack.isWeakSerreClass_locallyQuasicoherentSheafFlatBaseChangeFppfModulesSucc`);
* the affine case of Stacks 0770: along a 1-morphism between stacks representable by affine
  schemes, `R⁰f_*` preserves the class
  (`Stack.AlgebraicStacks.sheafFlatBaseChangeModuleRule_fppfHigherDirectImage_zero`) and
  `Rⁱf_* = 0` on it for `i > 0`, its module cohomology over affine objects vanishing
  (`Stack.AlgebraicStacks.isZero_fppfHigherDirectImage_of_isAffineRepresentable` with
  `Stack.isZero_rightDerived_evaluation_of_sheafFlatBaseChange_succ`).

## Main results

* `Stack.AlgebraicStacks.affineHigherDirectImagesMapInto_sheafFlatBaseChangeModuleRule`: clause
  (4) of Stacks 0770 for the faithful `LQCoh^fbc` at module universe `u + 1`.
* `Stack.AlgebraicStacks.sheafFlatBaseChange_higherDirectImage`: Stacks 0771 part (4)(b), fppf
  reading, faithful class, module universe `u + 1`.

## References

* [Stacks Project, Tag 0770](https://stacks.math.columbia.edu/tag/0770)
* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] hasSheafify_fppfAssociatedTopology
  wEqualsLocallyBijective_fppfAssociatedTopology

/-- **The affine case (clause (4)) of Stacks 0770 for the faithful `LQCoh^fbc` at module
universe `u + 1`**: along a 1-morphism between stacks representable by affine schemes the
higher direct images carry `LQCoh^fbc` into `LQCoh^fbc`. In degree zero this is
`AlgebraicGeometry.Stack.AlgebraicStacks.sheafFlatBaseChangeModuleRule_fppfHigherDirectImage_zero`;
in positive degrees the higher direct image vanishes, the module cohomology of `LQCoh^fbc` over
affine objects vanishing, and the class contains the zero objects, being a weak Serre class. -/
theorem affineHigherDirectImagesMapInto_sheafFlatBaseChangeModuleRule :
    AffineHigherDirectImagesMapInto.{u, w} B S hS
      (sheafFlatBaseChangeModuleRule.{u, w} B S hS E h) := by
  intro 𝒳 𝒴 f h𝒳 h𝒴 i F hF
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · exact sheafFlatBaseChangeModuleRule_fppfHigherDirectImage_zero B E h S hS f h𝒳 h𝒴 F hF
  · have hz := isZero_fppfHigherDirectImage_of_isAffineRepresentable B S hS f h𝒳 h𝒴 F i
      (fun x hx => isZero_rightDerived_evaluation_of_sheafFlatBaseChange_succ B E h S hS
        𝒳.val.val.p 𝒳.val.isFiberedInGroupoids F hF x hx i hi)
    exact (sheafFlatBaseChangeModuleRule B S hS E h 𝒴).prop_of_isZero hz

/-- **Stacks 0771 part (2) for the faithful `LQCoh^fbc` at module universe `u + 1`**, read as the
rule of Stacks 0770: `LQCoh^fbc(𝒪_𝒳)` is a weak Serre subcategory for every algebraic stack. -/
theorem isWeakSerreClass_sheafFlatBaseChangeModuleRule (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    (sheafFlatBaseChangeModuleRule B S hS E h 𝒳).IsWeakSerreClass :=
  isWeakSerreClass_locallyQuasicoherentSheafFlatBaseChangeFppfModulesSucc B E h S hS 𝒳

/-- **Stacks 0771 part (4)(b), fppf reading, for the faithful `LQCoh^fbc` at module universe
`u + 1`**: for a quasi-compact quasi-separated 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks, every
higher direct image `Rⁱf_*` carries `LQCoh^fbc(𝒪_𝒳)` into `LQCoh^fbc(𝒪_𝒴)`. -/
theorem sheafFlatBaseChange_higherDirectImage {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (hqc : IsQuasiCompactMorphism B S hS f) (hqs : IsQuasiSeparated B S hS f) :
    HigherDirectImagesMapInto B S hS (sheafFlatBaseChangeModuleRule B S hS E h) f := by
  have h₁ : ∀ V : BigFppfOver B S hS, IsAffine ((BigFppfOver.toScheme B S hS).obj V) →
      (sheafFlatBaseChangeModuleRule B S hS E h (schemeStack.{u, w} B S hS V)).IsWeakSerreClass :=
    fun V _ => isWeakSerreClass_sheafFlatBaseChangeModuleRule B E h S hS
      (schemeStack.{u, w} B S hS V)
  have h₂ : AffineHigherDirectImagesMapInto.{u, w} B S hS
      (sheafFlatBaseChangeModuleRule.{u, w} B S hS E h) :=
    affineHigherDirectImagesMapInto_sheafFlatBaseChangeModuleRule.{u, w} B E h S hS
  -- the two hypotheses are supplied before the morphism, so that elaboration does not unfold the
  -- weak Serre class at the charts
  have hred := @sheafFlatBaseChange_higherDirectImage_of_affine.{u, w} B S hS E h h₁
  exact hred h₂ f hqc hqs

end AlgebraicGeometry.Stack.AlgebraicStacks
