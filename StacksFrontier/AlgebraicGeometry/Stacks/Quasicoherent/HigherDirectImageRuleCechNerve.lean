module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.HigherDirectImageFppfWeakSerre
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.SmoothCoveringModuleSpectralSequence
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.CechNerveStackProjection

/-!
# The Čech step of the reduction of Stacks 0770 / 076Z to the affine case

Let `M` be a rule assigning to each algebraic stack a subcategory of its fppf modules
(`AlgebraicGeometry.Stack.AlgebraicStacks.ModuleRule`), let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of
algebraic stacks and let `c : 𝒰 ⟶ 𝒳` be representable by algebraic spaces, surjective and smooth.
If `M_𝒴` is a weak Serre subcategory, the inverse images along the projections of the relative
Čech nerve of `c` carry `M_𝒳` into `M` of the terms, and the higher direct images along the
composites `𝒰ₙ ⟶ 𝒳 ⟶ 𝒴` carry `M` into `M_𝒴`, then so do the higher direct images along `f`.

This is the step the proof of Stacks 076Z (and of its fppf twin Stacks 0770) runs four times:
the relative Čech spectral sequence of modules of Stacks 072G (2)(b),
`AlgebraicGeometry.Stack.exists_fppfModuleCechDirectImageSpectralSequence_of_isSmooth`, has first
page `R^q(f ∘ cₚ)_* cₚ^*F`, which lies in `M_𝒴` by the hypotheses, so its abutment
`R^{p+q}f_*F` does by part (4) of Stacks 0132
(`CategoryTheory.SpectralSequence.AbutsTo.prop_of_prop_page_firstQuadrant`). Nothing is carried:
the spectral sequence is unconditional.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.CechAffineLevel`: the levels of the iteration — level
  `0` is representability by an affine scheme, level `k + 1` is having a smooth surjective
  presentation whose Čech terms are of level `k`.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.higherDirectImagesMapInto_of_cechNerve`: the Čech step.
* `AlgebraicGeometry.Stack.AlgebraicStacks.higherDirectImagesMapInto_of_cechAffineLevel`: the
  iteration, from the affine case to every level, over a fixed target.

The geometric inputs of the source's proof of Stacks 076Z / 0770 are not in this file: that a
quasi-compact quasi-separated algebraic stack over an affine target is of level `3`, and the
reduction of a general target to an affine one (Stacks 075H and clause (3)).

## References

* [Stacks Project, Tag 076Z](https://stacks.math.columbia.edu/tag/076Z)
* [Stacks Project, Tag 0770](https://stacks.math.columbia.edu/tag/0770)
* [Stacks Project, Tag 072G](https://stacks.math.columbia.edu/tag/072G)
* [Stacks Project, Tag 0132](https://stacks.math.columbia.edu/tag/0132)
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

/-- **The Čech step.** Let `M` be a rule with `M_𝒴` a weak Serre subcategory, `f : 𝒳 ⟶ 𝒴` a
1-morphism of algebraic stacks and `c : 𝒰 ⟶ 𝒳` a smooth surjective 1-morphism representable by
algebraic spaces. If the inverse image along each projection `cₙ : 𝒰ₙ ⟶ 𝒳` of the relative Čech
nerve of `c` carries `M_𝒳` into `M_{𝒰ₙ}`, and the higher direct images along each `cₙ ≫ f` carry
`M` into `M_𝒴`, then the higher direct images along `f` carry `M_𝒳` into `M_𝒴`. -/
theorem higherDirectImagesMapInto_of_cechNerve (M : ModuleRule.{u, w} B S hS)
    {𝒰 𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} [(M 𝒴).IsWeakSerreClass]
    (c : 𝒰 ⟶ 𝒳) (hrep : Stack.IsRepresentableByAlgebraicSpaces B S hS c.hom.hom)
    (hsurj : Stack.IsSurjective B S hS c) (hsmooth : AlgebraicStacks.IsSmooth B S hS c)
    (f : 𝒳 ⟶ 𝒴)
    (hpull : ∀ (n : ℕ) (F : fppfModules B S hS 𝒳), M 𝒳 F →
      M (cechNerveStack B S hS c n)
        ((fppfModulePullback B S hS (cechNerveStackProjection B S hS c n)).obj F))
    (hcase : ∀ n : ℕ,
      HigherDirectImagesMapInto B S hS M (cechNerveStackProjection B S hS c n ≫ f)) :
    HigherDirectImagesMapInto B S hS M f := by
  intro i F hF
  obtain ⟨E, hzero, hpage, H, hE, hH⟩ :=
    exists_fppfModuleCechDirectImageSpectralSequence_of_isSmooth B S hS c f hrep hsurj hsmooth F
  refine (M 𝒴).prop_of_iso (hH i).some ?_
  refine @SpectralSequence.AbutsTo.prop_of_prop_page_firstQuadrant _ _ _ _ _ _ hE (M 𝒴)
    ‹(M 𝒴).IsWeakSerreClass› _ le_rfl hzero (fun p q => ?_) (i : ℤ)
  exact (M 𝒴).prop_of_iso (hpage p q).some.symm (hcase p q _ (hpull p F hF))

/-- **The levels of the reduction of Stacks 076Z / 0770 to the affine case.** Level `0` is the
algebraic stacks representable by an affine scheme; an algebraic stack is of level `k + 1` when
it has a smooth surjective presentation, representable by algebraic spaces, every term of whose
relative Čech nerve is of level `k`.

A quasi-compact quasi-separated algebraic stack over an affine target is of level `3`: the terms
of the Čech nerve of a smooth affine presentation are quasi-compact quasi-separated algebraic
spaces, those of an algebraic space are quasi-compact separated, and those of a separated one are
affine. -/
def CechAffineLevel : ℕ → AlgebraicStacks.{u, w} B S hS → Prop
  | 0, 𝒳 => IsAffineRepresentable B S hS 𝒳
  | k + 1, 𝒳 => ∃ (𝒰 : AlgebraicStacks.{u, w} B S hS) (c : 𝒰 ⟶ 𝒳),
      Stack.IsRepresentableByAlgebraicSpaces B S hS c.hom.hom ∧ Stack.IsSurjective B S hS c ∧
        AlgebraicStacks.IsSmooth B S hS c ∧ ∀ n, CechAffineLevel k (cechNerveStack B S hS c n)

/-- **The reduction of Stacks 076Z / 0770 to the affine case, over a fixed target.** Let `M` be
a rule with `M_𝒴` a weak Serre subcategory and whose members are preserved by inverse image
along every projection of a relative Čech nerve. If the higher direct images along every
1-morphism into `𝒴` from an algebraic stack representable by an affine scheme carry `M` into
`M_𝒴`, then so do the higher direct images along every 1-morphism into `𝒴` from an algebraic
stack of any level of `AlgebraicGeometry.Stack.AlgebraicStacks.CechAffineLevel`. -/
theorem higherDirectImagesMapInto_of_cechAffineLevel (M : ModuleRule.{u, w} B S hS)
    {𝒴 : AlgebraicStacks.{u, w} B S hS} [(M 𝒴).IsWeakSerreClass]
    (hpull : ∀ {𝒰 𝒳 : AlgebraicStacks.{u, w} B S hS} (c : 𝒰 ⟶ 𝒳) (n : ℕ)
      (F : fppfModules B S hS 𝒳), M 𝒳 F →
        M (cechNerveStack B S hS c n)
          ((fppfModulePullback B S hS (cechNerveStackProjection B S hS c n)).obj F))
    (hAffine : ∀ {𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴),
      IsAffineRepresentable B S hS 𝒳 → HigherDirectImagesMapInto B S hS M f) :
    ∀ (k : ℕ) {𝒳 : AlgebraicStacks.{u, w} B S hS}, CechAffineLevel B S hS k 𝒳 →
      ∀ f : 𝒳 ⟶ 𝒴, HigherDirectImagesMapInto B S hS M f := by
  intro k
  induction k with
  | zero => exact fun h f => hAffine f h
  | succ k ih =>
    rintro 𝒳 ⟨𝒰, c, hrep, hsurj, hsmooth, hlevel⟩ f
    exact higherDirectImagesMapInto_of_cechNerve B S hS M c hrep hsurj hsmooth f (hpull c)
      fun n => ih (hlevel n) _

end AlgebraicGeometry.Stack.AlgebraicStacks
