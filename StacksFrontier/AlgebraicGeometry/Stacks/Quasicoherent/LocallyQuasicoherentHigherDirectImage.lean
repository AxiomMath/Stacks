module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.HigherDirectImageSmoothLocalRule
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AffineDirectImageCartesian
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentCartesian
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AffineDirectImageVanishing

/-!
# Higher direct images of locally quasi-coherent modules

Let `f : 𝒳 ⟶ 𝒴` be a quasi-compact and quasi-separated 1-morphism of algebraic stacks. Every
higher direct image `Rⁱf_*`, computed in the étale topology at the module universe `u` of the
schemes, carries locally quasi-coherent modules to locally quasi-coherent modules. For `𝒳` and
`𝒴` both representable by affine schemes this also holds for the direct image `f_*` itself.

## Main results

* `StackModuleDirectImage.higherDirectImageZeroIso`: `R⁰f_* ≅ f_*`.
* `isLocallyQuasicoherent_stackModuleDirectImage_of_isAffineRepresentable`: `f_*` preserves local
  quasi-coherence along a 1-morphism of affine-representable stacks.
* `isLocallyQuasicoherent_stackModuleHigherDirectImage_zero_of_isAffineRepresentable`: the same
  for `R⁰f_*`, in the form of the rule of local quasi-coherence.
* `preservesHigherDirectImagesOfAffine_locallyQuasicoherentModuleRule`: along a 1-morphism of
  affine-representable stacks every `Rⁱf_*` preserves local quasi-coherence.
* `isLocallyQuasicoherent_stackModuleHigherDirectImage`: along a quasi-compact and
  quasi-separated 1-morphism every `Rⁱf_*` preserves local quasi-coherence.

All five are in the namespace `AlgebraicGeometry.Stack`.

## References

* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
* [Stacks Project, Tag 076Z](https://stacks.math.columbia.edu/tag/076Z)
* [Stacks Project, Tag 075Z](https://stacks.math.columbia.edu/tag/075Z)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u t

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)

/-- The isomorphism `R⁰f_* ≅ f_*` for a direct image of modules on the `τ`-sites of algebraic
stacks. -/
noncomputable def StackModuleDirectImage.higherDirectImageZeroIso {τ : SiteKind}
    (D : StackModuleDirectImage.{u, t} B S hS τ)
    {𝒳 𝒴 : AlgebraicStacks.{u, t} B S hS} (f : 𝒳 ⟶ 𝒴) :
    D.higherDirectImage f 0 ≅ D.pushforward f := by
  letI := D.enoughInjectives 𝒳
  haveI : Limits.PreservesFiniteLimits (D.pushforward f) :=
    (D.adjunction f).rightAdjoint_preservesLimits.{0, 0}.preservesFiniteLimits
  exact (D.pushforward f).rightDerivedZeroIsoSelf

/-- The direct image along a 1-morphism of affine-representable algebraic stacks preserves local
quasi-coherence, on the étale sites at the module universe `u`. -/
theorem isLocallyQuasicoherent_stackModuleDirectImage_of_isAffineRepresentable
    {𝒳 𝒴 : AlgebraicStacks.{u, t} B S hS} (f : 𝒳 ⟶ 𝒴)
    (h𝒳 : AlgebraicStacks.IsAffineRepresentable B S hS 𝒳)
    (h𝒴 : AlgebraicStacks.IsAffineRepresentable B S hS 𝒴)
    (F : StackModules B S hS .etale 𝒳)
    (hF : IsLocallyQuasicoherent B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids F.val) :
    IsLocallyQuasicoherent B E h S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids
      ((stackModuleDirectImage B S hS f .etale).obj F).val :=
  (isLocallyQuasicoherent_iff_forall_isIso_restrictionBaseChange B E h S hS _ _ _).2
    fun _ _ φ hy hy' hφ ↦ isIso_restrictionBaseChange_stackModuleDirectImage B S hS @Etale
      .etale f h𝒳 h𝒴 F
      ((isLocallyQuasicoherent_iff_forall_isIso_restrictionBaseChange B E h S hS _ _ F).1 hF)
      φ hy hy' hφ

/-- Along a 1-morphism of affine-representable algebraic stacks, `R⁰f_*` of a locally
quasi-coherent module satisfies the rule of local quasi-coherence. -/
theorem isLocallyQuasicoherent_stackModuleHigherDirectImage_zero_of_isAffineRepresentable
    {𝒳 𝒴 : AlgebraicStacks.{u, t} B S hS} (f : 𝒳 ⟶ 𝒴)
    (h𝒳 : AlgebraicStacks.IsAffineRepresentable B S hS 𝒳)
    (h𝒴 : AlgebraicStacks.IsAffineRepresentable B S hS 𝒴)
    (F : StackModules B S hS .etale 𝒳)
    (hF : IsLocallyQuasicoherent B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids F.val) :
    locallyQuasicoherentModuleRule B S hS E h 𝒴
      (((stackModuleDirectImageData.{u, t} B S hS .etale).higherDirectImage f 0).obj F) := by
  have : (locallyQuasicoherentModuleRule B S hS E h 𝒴).IsClosedUnderIsomorphisms :=
    isClosedUnderIsomorphisms_isLocallyQuasicoherent B E h S hS _ _
  exact (locallyQuasicoherentModuleRule B S hS E h 𝒴).prop_of_iso
    ((StackModuleDirectImage.higherDirectImageZeroIso B S hS _ f).app F).symm
    (isLocallyQuasicoherent_stackModuleDirectImage_of_isAffineRepresentable B S hS E h f
      h𝒳 h𝒴 F hF)

/-- Along a 1-morphism of algebraic stacks both representable by affine schemes, every `Rⁱf_*`
(étale topology, module universe `u`) carries locally quasi-coherent modules to locally
quasi-coherent modules. -/
theorem preservesHigherDirectImagesOfAffine_locallyQuasicoherentModuleRule :
    StackModuleRule.PreservesHigherDirectImagesOfAffine
      (stackModuleDirectImageData.{u, t} B S hS .etale)
      (locallyQuasicoherentModuleRule B S hS E h) := by
  intro 𝒳 𝒴 f h𝒳 h𝒴 i F hF
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · exact isLocallyQuasicoherent_stackModuleHigherDirectImage_zero_of_isAffineRepresentable
      B S hS E h f h𝒳 h𝒴 F hF
  · have : (locallyQuasicoherentModuleRule B S hS E h 𝒴).IsClosedUnderIsomorphisms :=
      isClosedUnderIsomorphisms_isLocallyQuasicoherent B E h S hS _ _
    have : (locallyQuasicoherentModuleRule B S hS E h 𝒴).ContainsZero :=
      containsZero_isLocallyQuasicoherent B E h S hS _ _
    exact (locallyQuasicoherentModuleRule B S hS E h 𝒴).prop_of_isZero
      (isZero_stackModuleHigherDirectImage_of_isAffineRepresentable B E h S hS f h𝒳 h𝒴 F hF i hi)

/-- Let `f : 𝒳 ⟶ 𝒴` be a quasi-compact and quasi-separated 1-morphism of algebraic stacks and
`ℱ` a locally quasi-coherent `𝒪_𝒳`-module on `𝒳_étale`. Then every higher direct image `Rⁱf_*ℱ`,
computed in the étale topology, is locally quasi-coherent on `𝒴_étale`.

Modules have sections in the universe `u` of the schemes, the universe of the structure sheaf
`𝒪_𝒳`, and `Rⁱf_*` is the right derived functor of the direct image right adjoint to the inverse
image (`AlgebraicGeometry.Stack.stackModuleHigherDirectImage`). The small étale sites `U_étale` in
the definition of local quasi-coherence (**Stacks 06WJ**) are those of the big étale site `E`
whose underlying category is that of the big fppf site `B` (`E.cutoff = B.cutoff`), which is the
convention of the source: `Sch_étale` is the big étale site on the underlying category `Sch_α`
of `Sch_fppf`. -/
@[stacks 075Z "the whole statement, for every degree i, with the source's hypotheses: f \
  quasi-compact and quasi-separated, ℱ a locally quasi-coherent 𝒪_𝒳-module on 𝒳_étale; modules \
  have sections in the universe of the structure sheaf, and Sch_étale is the big étale site E on \
  the underlying category of Sch_fppf (E.cutoff = B.cutoff), as in the source"]
theorem isLocallyQuasicoherent_stackModuleHigherDirectImage
    {𝒳 𝒴 : AlgebraicStacks.{u, t} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hqc : IsQuasiCompactMorphism B S hS f) (hqs : AlgebraicStacks.IsQuasiSeparated B S hS f)
    (F : StackModules B S hS .etale 𝒳)
    (hF : IsLocallyQuasicoherent B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids F.val)
    (i : ℕ) :
    IsLocallyQuasicoherent B E h S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids
      ((stackModuleHigherDirectImage B S hS f .etale i).obj F).val :=
  StackModuleRule.preservesHigherDirectImages_etale _
    (isWeakSerre_locallyQuasicoherentModuleRule B S hS E h)
    (isStableUnderSmoothPullback_locallyQuasicoherentModuleRule B S hS E h)
    (isSmoothLocal_locallyQuasicoherentModuleRule B S hS E h)
    (preservesHigherDirectImagesOfAffine_locallyQuasicoherentModuleRule B S hS E h) f hqc hqs i F hF

end AlgebraicGeometry.Stack
