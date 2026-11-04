module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FpqcDescent
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Properties
public import StacksFrontier.AlgebraicGeometry.SyntomicBaseChange.Basic

/-!
# Syntomic morphisms are fpqc local on the base

A morphism of schemes is syntomic precisely when its base changes along the members of an fpqc
covering of the target are syntomic.

## Main results

* `AlgebraicGeometry.syntomic_descendsAlong_surjective_inf_flat_inf_quasiCompact`: syntomicity
  descends along surjective flat quasi-compact morphisms.
* `AlgebraicGeometry.syntomic_isLocalAtTarget`: syntomicity is fpqc local on the base.

## Implementation notes

Syntomicity is Zariski local on the target and stable under base change, so by the criterion
`Stacks.Descent.isLocalAtTarget_fpqcPrecoverage` only the descent step is at issue. That step
reduces to the invariance of the *syntomic locus* under base change
(`AlgebraicGeometry.syntomicLocus_eq_preimage`): a syntomic morphism is flat and locally of
finite presentation, both of which are already known to be fpqc local on the base, so once those
two have descended the locus statement applies to `f` itself and identifies the syntomic locus
of the base change `X ×_S S' ⟶ S'` with the preimage of the syntomic locus of `f` along
`X ×_S S' ⟶ X`. The latter morphism is a base change of the surjection `S' ⟶ S`, hence
surjective, so a syntomic base change forces the syntomic locus of `f` to be everything.

Stability under *flat* base change has to be supplied by name from
`Stacks.Descent.isStableUnderFlatBaseChange_of_isStableUnderBaseChange`, whose docstring explains
why instance search cannot apply it on its own.

## References

* [Stacks Project, Tag 02VK](https://stacks.math.columbia.edu/tag/02VK)
-/

@[expose] public section

open CategoryTheory Limits MorphismProperty

namespace AlgebraicGeometry

universe u

/-- If the base change of `f` along a surjective, flat, quasi-compact morphism `g` is syntomic,
then so is `f`. -/
private lemma syntomic_of_pullbackSnd {S S' X : Scheme.{u}} (g : S' ⟶ S)
    [Surjective g] [Flat g] [QuasiCompact g] (f : X ⟶ S)
    (hsnd : Syntomic (pullback.snd f g)) : Syntomic f := by
  let 𝒰 : Precoverage.ZeroHypercover.{0} Scheme.fpqcPrecoverage S :=
    .singleton g g.singleton_mem_fpqcPrecoverage
  have _ : Flat f :=
    MorphismProperty.IsLocalAtTarget.of_zeroHypercover (P := @Flat) 𝒰
      fun i ↦ by cases i; exact AlgebraicGeometry.flat hsnd
  have _ : LocallyOfFinitePresentation f :=
    MorphismProperty.IsLocalAtTarget.of_zeroHypercover (P := @LocallyOfFinitePresentation) 𝒰
      fun i ↦ by cases i; exact AlgebraicGeometry.locallyOfFinitePresentation hsnd
  have hloc := syntomicLocus_eq_preimage (pullback.fst f g) (pullback.snd f g) f g
    (IsPullback.of_hasPullback f g)
  intro x
  obtain ⟨z, rfl⟩ := (pullback.fst f g).surjective x
  exact hloc.le (hsnd z)

/-- Syntomicity of morphisms of schemes descends along surjective flat quasi-compact morphisms:
if the base change of `f` along such a morphism is syntomic, then so is `f`. -/
instance syntomic_descendsAlong_surjective_inf_flat_inf_quasiCompact :
    MorphismProperty.DescendsAlong (@Syntomic : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) where
  of_isPullback {_ _ _ _ _ _ g f} h hg hfst := by
    obtain ⟨⟨hsurj, hflat⟩, hqc⟩ := hg
    have _ : Surjective g := hsurj
    have _ : Flat g := hflat
    have _ : QuasiCompact g := hqc
    have _ : MorphismProperty.RespectsIso (@Syntomic : MorphismProperty Scheme.{u}) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    refine syntomic_of_pullbackSnd g f ?_
    rw [← MorphismProperty.cancel_left_of_respectsIso (P := @Syntomic)
      h.flip.isoPullback.hom, h.flip.isoPullback_hom_snd]
    exact hfst

/-- **Stacks Project, Tag 02VK.** Syntomicity of a morphism of schemes is fpqc local on the
base. -/
@[stacks 02VK]
instance syntomic_isLocalAtTarget :
    MorphismProperty.IsLocalAtTarget (@Syntomic : MorphismProperty Scheme.{u})
      Scheme.fpqcPrecoverage :=
  have := Stacks.Descent.isStableUnderFlatBaseChange_of_isStableUnderBaseChange
    (@Syntomic : MorphismProperty Scheme.{u})
  Stacks.Descent.isLocalAtTarget_fpqcPrecoverage _

end AlgebraicGeometry

end
