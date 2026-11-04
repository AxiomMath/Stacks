module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineBaseCoveringSieveDescent
public import StacksFrontier.AlgebraicGeometry.Descent.AffineBaseCoveringSieveStepOne
public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomEffectiveDescent
public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Descent.FiniteDescentFromAffine
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringSieveDescent
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Effective descent along the covering sieves for the finite étale morphisms

`AlgebraicGeometry.Space.IsEffectiveDescentAlongCoveringSieve B S hS P` is effective descent
for `P`-morphisms along the covering sieves of the big fppf site of `S`. This file discharges it
outright at the finite étale morphisms, `IsFinite ⊓ Etale`: a sheaf over an object of the site
whose base change along every arrow of a covering sieve is representable by a finite étale
morphism is itself representable by a finite étale morphism.

This is fppf descent for finite étale morphisms — Stacks 0245 together with Stacks 02LA and
Stacks 02VN — in the shape the big fppf site consumes it.

The two halves of the predicate are paid for separately:

* *representability*, by `AlgebraicGeometry.Space.presheaf_pullback_snd_isAffineHom_of_isPullback`
  — a finite morphism is affine, and affine morphisms descend effectively along a surjective flat
  morphism of finite presentation of affines, the descent datum being an algebra descent datum
  along a faithfully flat ring map;
* the *property*, by the unconditional
  `AlgebraicGeometry.Space.presheaf_of_coveringSieve_of_descendsAlong`, which transports a
  property which is Zariski local on the target and satisfies fppf descent to a base change that
  is already known to be representable.

## Main results

* `AlgebraicGeometry.isFinite_inf_etale_descendsAlong_fppf`: finite étale morphisms satisfy fppf
  descent, Stacks 02LA together with Stacks 02VN.
* `AlgebraicGeometry.isFinite_inf_etale_size_le`: the source of a finite étale morphism into `Z`
  has size at most `2 ^ 2 ^ size Z`, in fact at most `size Z`.
* `AlgebraicGeometry.Space.coveringSieveBody_affineBase_isFinite_inf_etale` is the
  single-morphism body of the predicate at the finite étale morphisms, over an affine base.
* `AlgebraicGeometry.Space.isEffectiveDescentAlongCoveringSieve_isFinite_inf_etale`
  is **effective descent along the covering sieves of the big fppf site of `S` for the finite
  étale morphisms, with no hypothesis.**

## Implementation notes

*Why no hypothesis on the site's cutoff is incurred.* Finite étale morphisms are not
monomorphisms, so the reduction to an affine base used for the affine monomorphisms locally of
finite type is unavailable; instead
`AlgebraicGeometry.Space.isEffectiveDescentAlongCoveringSieve_of_affineBase_of_size_le` asks only
that the property not raise size beyond `2 ^ 2 ^ size (target)`. A finite morphism is locally of
finite type and quasi-compact, so
`AlgebraicGeometry.Scheme.size_le_of_locallyOfFiniteType_of_quasiCompact` bounds the source by
the target, and the cutoff of the site is closed under powersets.

*The covering sieve used for the property half.* It is `Sieve.generate (Presieve.singleton p)`
for the single morphism `p` produced by step 1, which is covering by
`AlgebraicGeometry.sieve_generate_singleton_mem_topology_over_of_flat`. Over an arrow of that
sieve the base change of `f` is a base change of the base change along `p`, so the property is
inherited from the hypothesis by stability under base change of
`CategoryTheory.MorphismProperty.relative`.

## References

* [Stacks Project, Tag 0245](https://stacks.math.columbia.edu/tag/0245)
* [Stacks Project, Tag 02LA](https://stacks.math.columbia.edu/tag/02LA)
* [Stacks Project, Tag 02VN](https://stacks.math.columbia.edu/tag/02VN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Finite étale morphisms are Zariski local on the target: finiteness is an affine-local
property of the target and étaleness is a local property of the structure ring maps. -/
theorem isFinite_inf_etale_isZariskiLocalAtTarget :
    IsZariskiLocalAtTarget
      ((@IsFinite.{u} ⊓ @Etale.{u} : MorphismProperty Scheme.{u})) :=
  have _h1 := Space.isZariskiLocalAtTarget_isFinite.{u}
  have _h2 : IsZariskiLocalAtTarget (@Etale.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _ (Q := RingHom.Etale)
  MorphismProperty.IsLocalAtTarget.inf _ _

/-- Finite étale morphisms satisfy fppf descent: if the base change of a morphism along a
surjective flat morphism locally of finite presentation is finite and étale, then so is the
morphism. This is Stacks 02LA together with Stacks 02VN. -/
theorem isFinite_inf_etale_descendsAlong_fppf :
    MorphismProperty.DescendsAlong
      ((@IsFinite.{u} ⊓ @Etale.{u} : MorphismProperty Scheme.{u}))
      (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) :=
  have _h1 := isFinite_descendsAlong_fppf.{u}
  have _h2 :=
    Space.etale_descendsAlong_surjective_inf_flat_inf_locallyOfFinitePresentation.{u}
  MorphismProperty.DescendsAlong.inf

/-- A finite étale morphism is affine, finiteness alone already giving this. -/
theorem isFinite_inf_etale_le_isAffineHom :
    (@IsFinite.{u} ⊓ @Etale.{u} : MorphismProperty Scheme.{u}) ≤ (@IsAffineHom.{u}) :=
  fun _ _ _ hf ↦ Space.isFinite_le_isAffineHom.{u} _ _ _ hf.1

/-- The source of a finite étale morphism into `Z` has size at most `2 ^ 2 ^ size Z`: a finite
morphism is locally of finite type and quasi-compact, so its source has size at most that of its
target, and a cardinal lies below its double powerset. -/
theorem isFinite_inf_etale_size_le : ∀ {Z W : Scheme.{u}} (g : W ⟶ Z),
    (@IsFinite.{u} ⊓ @Etale.{u} : MorphismProperty Scheme.{u}) g →
    W.size ≤ (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ Z.size := by
  intro Z W g hg
  have _hfin : IsFinite g := hg.1
  refine (Scheme.size_le_of_locallyOfFiniteType_of_quasiCompact g).trans ?_
  exact (Cardinal.cantor _).le.trans
    (Cardinal.power_le_power_left two_ne_zero (Cardinal.cantor _).le)

namespace Space

/-- **The single-morphism body of effective descent along the covering sieves at the finite
étale morphisms, over an affine base.** Let `f : X ⟶ Y` be a morphism of sheaves on the big fppf
site of `S`, let `h : yoneda.obj a ⟶ Y` with `a` affine and let `p : c ⟶ a` be a surjective flat
morphism of the site locally of finite presentation with `c` affine. If the base change of `f`
along `yoneda.map p ≫ h` is representable by a finite étale morphism, then so is its base change
along `h`.

The representability of the base change along `h` is
`AlgebraicGeometry.Space.presheaf_pullback_snd_isAffineHom_of_isPullback`, which needs only that
a finite morphism be affine; the property is then transported from the sieve generated by `p` by
`AlgebraicGeometry.Space.presheaf_of_coveringSieve_of_descendsAlong`. -/
theorem coveringSieveBody_affineBase_isFinite_inf_etale
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
    (hbase : (((@_root_.AlgebraicGeometry.IsFinite.{u} ⊓ @_root_.AlgebraicGeometry.Etale.{u} :
      MorphismProperty Scheme.{u})).inverseImage
      (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f (yoneda.map p ≫ h))) :
    (((@_root_.AlgebraicGeometry.IsFinite.{u} ⊓ @_root_.AlgebraicGeometry.Etale.{u} :
      MorphismProperty Scheme.{u})).inverseImage
      (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f h) := by
  have _h1 := _root_.AlgebraicGeometry.isFinite_inf_etale_isZariskiLocalAtTarget.{u}
  have _h2 := _root_.AlgebraicGeometry.isFinite_inf_etale_descendsAlong_fppf.{u}
  have hraff : (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsAffineHom.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f (yoneda.map p ≫ h)) :=
    MorphismProperty.relative_monotone
      (MorphismProperty.monotone_inverseImage (BigFppfOver.toScheme B S hS)
        _root_.AlgebraicGeometry.isFinite_inf_etale_le_isAffineHom.{u}) _ hbase
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
    ((@_root_.AlgebraicGeometry.IsFinite.{u} ⊓ @_root_.AlgebraicGeometry.Etale.{u} :
      MorphismProperty Scheme.{u}).inverseImage
      (BigFppfOver.toScheme B S hS)) (F := yoneda (C := BigFppfOver B S hS))
  exact MorphismProperty.of_isPullback
    (s.of_right' (IsPullback.of_hasPullback f (yoneda.map p ≫ h))) hbase

/-- **Effective descent along the covering sieves of the big fppf site of `S` holds for the
finite étale morphisms**, with no hypothesis.

Since a finite morphism does not raise size, the affine-base reduction
`AlgebraicGeometry.Space.isEffectiveDescentAlongCoveringSieve_of_affineBase_of_size_le` applies
with no hypothesis on the cutoff of the site. -/
@[sga "7 II 2.3.1" "partial"]
theorem isEffectiveDescentAlongCoveringSieve_isFinite_inf_etale
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    IsEffectiveDescentAlongCoveringSieve B S hS
      ((@_root_.AlgebraicGeometry.IsFinite.{u} ⊓ @_root_.AlgebraicGeometry.Etale.{u}) :
        MorphismProperty Scheme.{u}) := by
  have _h1 := _root_.AlgebraicGeometry.isFinite_inf_etale_isZariskiLocalAtTarget.{u}
  have _h2 := _root_.AlgebraicGeometry.isFinite_inf_etale_descendsAlong_fppf.{u}
  refine isEffectiveDescentAlongCoveringSieve_of_affineBase_of_size_le
    _root_.AlgebraicGeometry.isFinite_inf_etale_size_le.{u} ?_
  refine coveringSieveBody_affineBase_of_affineFlatSource ?_
  intro X Y f hX hY a c h p ha hc hps hpf hpp _hpqc hbase
  exact coveringSieveBody_affineBase_isFinite_inf_etale
    f hX hY h p ha hc hps hpf hpp hbase

end Space

end AlgebraicGeometry

end
