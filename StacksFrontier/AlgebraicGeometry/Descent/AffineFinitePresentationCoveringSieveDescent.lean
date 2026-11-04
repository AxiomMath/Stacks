module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomCoveringSieveDescent
public import StacksFrontier.AlgebraicGeometry.Descent.AffineBaseCoveringSieveDescent
public import StacksFrontier.AlgebraicGeometry.Descent.FiniteDescentFromAffine
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff

/-!
# Effective descent along covering sieves for affine morphisms locally of finite presentation

The property `IsAffineHom ⊓ LocallyOfFinitePresentation` of morphisms of schemes satisfies
effective descent along the covering sieves of the big fppf site of a scheme `S`
(`AlgebraicGeometry.Space.IsEffectiveDescentAlongCoveringSieve`), with no hypothesis.

## Main results

* `AlgebraicGeometry.Space.isEffectiveDescentAlongCoveringSieve_affineLocallyOfFinitePresentation`.

## Implementation notes

The argument is that of
`AlgebraicGeometry.Space.isEffectiveDescentAlongCoveringSieve_affineMonoLocallyOfFiniteType`.
The affine-base reduction
`AlgebraicGeometry.Space.isEffectiveDescentAlongCoveringSieve_of_affineBase_of_size_le` needs a
size bound on the sources, which local finite presentation over an affine target provides
(`AlgebraicGeometry.Scheme.size_le_of_locallyOfFiniteType_of_quasiCompact`); over an affine base
a covering sieve is replaced by one surjective flat morphism of finite presentation with affine
source (`AlgebraicGeometry.Space.coveringSieveBody_affineBase_of_affineFlatSource`), along which
affine morphisms descend effectively
(`AlgebraicGeometry.Space.presheaf_pullback_snd_isAffineHom_of_isPullback`), and local finite
presentation is recovered by fppf descent.

## References

* [Stacks Project, Tag 0245](https://stacks.math.columbia.edu/tag/0245)
* [Stacks Project, Tag 02L5](https://stacks.math.columbia.edu/tag/02L5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- The affine morphisms of schemes locally of finite presentation. -/
abbrev affineLocallyOfFinitePresentation : MorphismProperty Scheme.{u} :=
  @_root_.AlgebraicGeometry.IsAffineHom.{u} ⊓ @AlgebraicGeometry.LocallyOfFinitePresentation.{u}

/-- Being an affine morphism of schemes is local on the target in the Zariski topology. -/
theorem isAffineHom_isZariskiLocalAtTarget' :
    IsZariskiLocalAtTarget (@_root_.AlgebraicGeometry.IsAffineHom.{u}) :=
  @HasAffineProperty.instIsZariskiLocalAtTarget _ _ instHasAffinePropertyIsAffineHomIsAffine

/-- Being locally of finite presentation is local on the target in the Zariski topology. -/
theorem locallyOfFinitePresentation_isZariskiLocalAtTarget' :
    IsZariskiLocalAtTarget
      (@AlgebraicGeometry.LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u}) :=
  HasRingHomProperty.instIsZariskiLocalAtTarget
    (P := @AlgebraicGeometry.LocallyOfFinitePresentation.{u}) (Q := RingHom.FinitePresentation)

/-- Being affine and locally of finite presentation is local on the target in the Zariski
topology. -/
theorem affineLocallyOfFinitePresentation_isZariskiLocalAtTarget :
    IsZariskiLocalAtTarget affineLocallyOfFinitePresentation.{u} :=
  @MorphismProperty.IsLocalAtTarget.inf _ _ _ _ _ isAffineHom_isZariskiLocalAtTarget'
    locallyOfFinitePresentation_isZariskiLocalAtTarget'

/-- Being affine and locally of finite presentation descends along surjective flat morphisms
locally of finite presentation. -/
theorem affineLocallyOfFinitePresentation_descendsAlong :
    affineLocallyOfFinitePresentation.{u}.DescendsAlong
      (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) :=
  have _ := isAffineHom_isZariskiLocalAtTarget'.{u}
  have _ := locallyOfFinitePresentation_isZariskiLocalAtTarget'.{u}
  have : MorphismProperty.DescendsAlong (@_root_.AlgebraicGeometry.IsAffineHom.{u})
      (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) := descendsAlong_fppf_of _
  have : MorphismProperty.DescendsAlong
      (@AlgebraicGeometry.LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) := descendsAlong_fppf_of _
  MorphismProperty.DescendsAlong.inf

/-- Being affine and locally of finite presentation is stable under base change. -/
theorem affineLocallyOfFinitePresentation_isStableUnderBaseChange :
    affineLocallyOfFinitePresentation.{u}.IsStableUnderBaseChange :=
  MorphismProperty.IsStableUnderBaseChange.inf

/-- Let `f : X ⟶ Y` be a morphism of sheaves on the big fppf site over `S`, let `a` be affine with
`h : yoneda.obj a ⟶ Y`, and let `p : c ⟶ a` be a surjective flat morphism locally of finite
presentation with `c` affine. If the base change of `f` along `yoneda.map p ≫ h` is representably
affine and locally of finite presentation, then so is the base change of `f` along `h`. -/
theorem coveringSieveBody_affineBase_affineLocallyOfFinitePresentation
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (hY : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y)
    {a c : BigFppfOver B S hS} (h : yoneda.obj a ⟶ Y) (p : c ⟶ a)
    (ha : IsAffine ((BigFppfOver.toScheme B S hS).obj a))
    (hc : IsAffine ((BigFppfOver.toScheme B S hS).obj c))
    (hps : Surjective ((BigFppfOver.toScheme B S hS).map p))
    (hpf : Flat ((BigFppfOver.toScheme B S hS).map p))
    (hpp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map p))
    (hbase : (affineLocallyOfFinitePresentation.{u}.inverseImage
      (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f (yoneda.map p ≫ h))) :
    (affineLocallyOfFinitePresentation.{u}.inverseImage
      (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f h) := by
  have _h1 := affineLocallyOfFinitePresentation_isZariskiLocalAtTarget.{u}
  have _h2 := affineLocallyOfFinitePresentation_descendsAlong.{u}
  have hraff : (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsAffineHom.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f (yoneda.map p ≫ h)) :=
    MorphismProperty.relative_monotone
      (MorphismProperty.monotone_inverseImage (BigFppfOver.toScheme B S hS) inf_le_left) _ hbase
  have haff : (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsAffineHom.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f h) :=
    presheaf_pullback_snd_isAffineHom_of_isPullback hX hY ha hc hps hpf hpp
      (IsPullback.of_hasPullback f (yoneda.map p ≫ h)) hraff
  refine presheaf_of_coveringSieve_of_descendsAlong h haff.rep
    (sieve_generate_singleton_mem_topology_over_of_flat B S hS p hps hpf hpp) ?_
  intro b q hq
  obtain ⟨Z, u, g, hg, hfac⟩ := hq
  cases hg
  have heq : yoneda.map q ≫ h = yoneda.map u ≫ (yoneda.map p ≫ h) := by
    rw [← hfac, Functor.map_comp, Category.assoc]
  have s : IsPullback (pullback.fst f (yoneda.map q ≫ h))
      (pullback.snd f (yoneda.map q ≫ h)) f (yoneda.map u ≫ (yoneda.map p ≫ h)) := by
    rw [← heq]
    exact IsPullback.of_hasPullback f (yoneda.map q ≫ h)
  have _hbc := MorphismProperty.relative_isStableUnderBaseChange
    (affineLocallyOfFinitePresentation.{u}.inverseImage
      (BigFppfOver.toScheme B S hS)) (F := yoneda (C := BigFppfOver B S hS))
  exact MorphismProperty.of_isPullback
    (s.of_right' (IsPullback.of_hasPullback f (yoneda.map p ≫ h))) hbase

/-- **Effective descent along the covering sieves of the big fppf site of `S` holds for the
affine morphisms locally of finite presentation**, with no hypothesis. -/
theorem isEffectiveDescentAlongCoveringSieve_affineLocallyOfFinitePresentation
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    IsEffectiveDescentAlongCoveringSieve B S hS affineLocallyOfFinitePresentation.{u} := by
  have _h1 := affineLocallyOfFinitePresentation_isZariskiLocalAtTarget.{u}
  have _h2 := affineLocallyOfFinitePresentation_descendsAlong.{u}
  refine isEffectiveDescentAlongCoveringSieve_of_affineBase_of_size_le ?_ ?_
  · intro Z W g hg
    have := hg.1
    have := hg.2
    exact (Scheme.size_le_of_locallyOfFiniteType_of_quasiCompact g).trans
      ((Cardinal.cantor _).le.trans (Cardinal.cantor _).le)
  · refine coveringSieveBody_affineBase_of_affineFlatSource ?_
    intro X Y f hX hY a c h p ha hc hps hpf hpp _hpqc hbase
    exact coveringSieveBody_affineBase_affineLocallyOfFinitePresentation
      f hX hY h p ha hc hps hpf hpp hbase

end AlgebraicGeometry.Space

end
