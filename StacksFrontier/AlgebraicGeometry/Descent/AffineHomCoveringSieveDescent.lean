module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineBaseCoveringSieveStepOne
public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomEffectiveDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringSieveDescent

/-!
# Effective descent along the covering sieves for the affine monomorphisms locally of finite type

The predicate `AlgebraicGeometry.Space.IsEffectiveDescentAlongCoveringSieve` of Stacks 0265,
effective descent along the covering sieves of the big fppf site of `S`, holds at the property
of being an affine monomorphism locally of finite type, with no hypothesis.

## Main definitions

* `AlgebraicGeometry.affineMonoLocallyOfFiniteType`: the affine monomorphisms locally of finite
  type.

## Main results

* `AlgebraicGeometry.Space.coveringSieveBody_affineBase_affineMonoLocallyOfFiniteType` is the
  single-morphism body of the predicate at that property, over an affine base.
* `AlgebraicGeometry.Space.isEffectiveDescentAlongCoveringSieve_affineMonoLocallyOfFiniteType`
  is effective descent along the covering sieves of the big fppf site of `S` for the affine
  monomorphisms locally of finite type.

## References

* [Stacks Project, Tag 0265](https://stacks.math.columbia.edu/tag/0265)
* [Stacks Project, Tag 02W3](https://stacks.math.columbia.edu/tag/02W3)
* [Stacks Project, Tag 02W8](https://stacks.math.columbia.edu/tag/02W8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The property of a morphism of schemes of being an affine monomorphism locally of finite
type. -/
abbrev affineMonoLocallyOfFiniteType : MorphismProperty Scheme.{u} :=
  MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType ⊓ @IsAffineHom

/-- Affine monomorphisms which are locally of finite type are Zariski local on the target. -/
theorem affineMonoLocallyOfFiniteType_isZariskiLocalAtTarget :
    IsZariskiLocalAtTarget (affineMonoLocallyOfFiniteType.{u}) :=
  have _h1 := monomorphisms_inf_locallyOfFiniteType_isZariskiLocalAtTarget.{u}
  have _h2 := isZariskiLocalAtTarget_isAffineHom.{u}
  MorphismProperty.IsLocalAtTarget.inf _ _

/-- Affine monomorphisms which are locally of finite type satisfy fppf descent. -/
theorem affineMonoLocallyOfFiniteType_descendsAlong_fppf :
    MorphismProperty.DescendsAlong (affineMonoLocallyOfFiniteType.{u})
      (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) :=
  have _h1 := monomorphisms_inf_locallyOfFiniteType_descendsAlong_fppf.{u}
  have _hzl := isZariskiLocalAtTarget_isAffineHom.{u}
  have _h2 : MorphismProperty.DescendsAlong (@IsAffineHom.{u})
      (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) := descendsAlong_fppf_of _
  MorphismProperty.DescendsAlong.inf

/-- An affine monomorphism locally of finite type is a monomorphism. -/
theorem affineMonoLocallyOfFiniteType_le_monomorphisms :
    affineMonoLocallyOfFiniteType.{u} ≤ MorphismProperty.monomorphisms Scheme.{u} :=
  fun _ _ _ hf ↦ hf.1.1

/-- An affine monomorphism locally of finite type is affine. -/
theorem affineMonoLocallyOfFiniteType_le_isAffineHom :
    affineMonoLocallyOfFiniteType.{u} ≤ (@IsAffineHom.{u}) :=
  fun _ _ _ hf ↦ hf.2

/-- An affine monomorphism locally of finite type is a monomorphism locally of finite type. -/
theorem affineMonoLocallyOfFiniteType_le_monomorphisms_inf_locallyOfFiniteType :
    affineMonoLocallyOfFiniteType.{u} ≤
      (MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType) :=
  fun _ _ _ hf ↦ hf.1

namespace Space

/-- **The single-morphism body of effective descent along the covering sieves at the affine
monomorphisms locally of finite type, over an affine base.** Let `f : X ⟶ Y` be a morphism of
sheaves on the big fppf site of `S`, let `h : yoneda.obj a ⟶ Y` with `a` affine and let
`p : c ⟶ a` be a surjective flat morphism of the site locally of finite presentation with `c`
affine. If the base change of `f` along `yoneda.map p ≫ h` is representable by an affine
monomorphism locally of finite type, then so is its base change along `h`. -/
theorem coveringSieveBody_affineBase_affineMonoLocallyOfFiniteType
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
    (hbase : ((_root_.AlgebraicGeometry.affineMonoLocallyOfFiniteType.{u}).inverseImage
      (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f (yoneda.map p ≫ h))) :
    ((_root_.AlgebraicGeometry.affineMonoLocallyOfFiniteType.{u}).inverseImage
      (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f h) := by
  have _h1 := _root_.AlgebraicGeometry.affineMonoLocallyOfFiniteType_isZariskiLocalAtTarget.{u}
  have _h2 := _root_.AlgebraicGeometry.affineMonoLocallyOfFiniteType_descendsAlong_fppf.{u}
  have hraff : (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsAffineHom.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f (yoneda.map p ≫ h)) :=
    MorphismProperty.relative_monotone
      (MorphismProperty.monotone_inverseImage (BigFppfOver.toScheme B S hS)
        _root_.AlgebraicGeometry.affineMonoLocallyOfFiniteType_le_isAffineHom.{u}) _ hbase
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
    ((_root_.AlgebraicGeometry.affineMonoLocallyOfFiniteType.{u}).inverseImage
      (BigFppfOver.toScheme B S hS)) (F := yoneda (C := BigFppfOver B S hS))
  exact MorphismProperty.of_isPullback
    (s.of_right' (IsPullback.of_hasPullback f (yoneda.map p ≫ h))) hbase

/-- **Effective descent along the covering sieves of the big fppf site of `S` holds for the
affine monomorphisms locally of finite type**: the predicate
`AlgebraicGeometry.Space.IsEffectiveDescentAlongCoveringSieve` holds at
`AlgebraicGeometry.affineMonoLocallyOfFiniteType`, with no hypothesis. -/
theorem isEffectiveDescentAlongCoveringSieve_affineMonoLocallyOfFiniteType
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    IsEffectiveDescentAlongCoveringSieve B S hS
      (_root_.AlgebraicGeometry.affineMonoLocallyOfFiniteType.{u}) := by
  have _h1 := _root_.AlgebraicGeometry.affineMonoLocallyOfFiniteType_isZariskiLocalAtTarget.{u}
  have _h2 := _root_.AlgebraicGeometry.affineMonoLocallyOfFiniteType_descendsAlong_fppf.{u}
  refine isEffectiveDescentAlongCoveringSieve_of_affineBase_of_le_monomorphisms
    _root_.AlgebraicGeometry.affineMonoLocallyOfFiniteType_le_monomorphisms.{u} ?_
  refine coveringSieveBody_affineBase_of_affineFlatSource ?_
  intro X Y f hX hY a c h p ha hc hps hpf hpp _hpqc hbase
  exact coveringSieveBody_affineBase_affineMonoLocallyOfFiniteType
    f hX hY h p ha hc hps hpf hpp hbase

end Space

end AlgebraicGeometry

end
