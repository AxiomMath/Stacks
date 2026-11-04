module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnSourceTopologies.AffineCriteria
public import StacksFrontier.AlgebraicGeometry.Descent.MorphismProperty.FaithfullyFlatRing

/-!
# Properties of morphisms local on the source for the fppf topology

Being locally of finite presentation, being locally of finite type, being an open map and being
universally open can each be checked after precomposing with the members of an fppf covering of
the source.

## Main results

* `AlgebraicGeometry.locallyOfFinitePresentation_isLocalAtSource`: being locally of finite
  presentation is fppf local on the source.
* `AlgebraicGeometry.locallyOfFiniteType_isLocalAtSource`: being locally of finite type is fppf
  local on the source.
* `AlgebraicGeometry.isLocalAtSource_fppf_isOpenMap`: being an open morphism is fppf local on the
  source.
* `AlgebraicGeometry.universallyOpen_isLocalAtSource`: being universally open is fppf local on the
  source.

## Implementation notes

An open morphism is `topologically IsOpenMap`, the morphism property of having an open
underlying map of topological spaces; universal openness is Mathlib's
`AlgebraicGeometry.UniversallyOpen`. Source locality is
`CategoryTheory.MorphismProperty.IsLocalAtSource` for Mathlib's
`AlgebraicGeometry.Scheme.fppfPrecoverage`.

## References

* [Stacks Project, Tag 0367](https://stacks.math.columbia.edu/tag/0367)
* [Stacks Project, Tag 02KK](https://stacks.math.columbia.edu/tag/02KK)
* [Stacks Project, Tag 036H](https://stacks.math.columbia.edu/tag/036H)
* [Stacks Project, Tag 036N](https://stacks.math.columbia.edu/tag/036N)
* [Stacks Project, Tag 036O](https://stacks.math.columbia.edu/tag/036O)
* [Stacks Project, Tag 036P](https://stacks.math.columbia.edu/tag/036P)
* [Stacks Project, Tag 036Q](https://stacks.math.columbia.edu/tag/036Q)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Being locally of finite presentation is local on the source for the fppf topology. -/
@[stacks 036N]
instance locallyOfFinitePresentation_isLocalAtSource :
    MorphismProperty.IsLocalAtSource (@LocallyOfFinitePresentation.{u})
      Scheme.fppfPrecoverage := by
  have : MorphismProperty.RespectsLeft (@LocallyOfFinitePresentation.{u})
      (@Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) :=
    ⟨fun g hg f hf ↦ MorphismProperty.comp_mem _ g f hg.2 hf⟩
  have : IsZariskiLocalAtSource (@LocallyOfFinitePresentation.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.FinitePresentation)
  have : IsZariskiLocalAtTarget (@LocallyOfFinitePresentation.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @LocallyOfFinitePresentation.{u})
      (Q := RingHom.FinitePresentation)
  refine isLocalAtSource_fppf_of_affine_descent _ fun g f hg hflat hfp hcomp ↦ ?_
  have : Surjective g := hg
  have : Flat g := hflat
  have : LocallyOfFinitePresentation g := hfp
  have : LocallyOfFinitePresentation (g ≫ f) := hcomp
  rw [HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)]
  refine RingHom.finitePresentation_of_comp_of_faithfullyFlat f.appTop.hom g.appTop.hom ?_ ?_
    (Scheme.Hom.finitePresentation_appTop g)
  · simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] using
      Scheme.Hom.finitePresentation_appTop (g ≫ f)
  · exact (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine g).mp
      ⟨inferInstance, inferInstance⟩

/-- Being locally of finite type is local on the source for the fppf topology. -/
@[stacks 036O]
instance locallyOfFiniteType_isLocalAtSource :
    MorphismProperty.IsLocalAtSource (@LocallyOfFiniteType.{u}) Scheme.fppfPrecoverage := by
  have : MorphismProperty.RespectsLeft (@LocallyOfFiniteType.{u})
      (@Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) :=
    ⟨fun g hg f hf ↦ by
      have : LocallyOfFinitePresentation g := hg.2
      exact MorphismProperty.comp_mem _ g f inferInstance hf⟩
  have : IsZariskiLocalAtSource (@LocallyOfFiniteType.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.FiniteType)
  have : IsZariskiLocalAtTarget (@LocallyOfFiniteType.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @LocallyOfFiniteType.{u})
      (Q := RingHom.FiniteType)
  refine isLocalAtSource_fppf_of_affine_descent _ fun g f hg hflat hfp hcomp ↦ ?_
  have : Surjective g := hg
  have : Flat g := hflat
  have : LocallyOfFinitePresentation g := hfp
  have : LocallyOfFiniteType (g ≫ f) := hcomp
  rw [HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)]
  refine RingHom.finiteType_of_comp_of_faithfullyFlat_of_finitePresentation
    (f := f.appTop.hom) (g := g.appTop.hom) ?_ ?_ (Scheme.Hom.finitePresentation_appTop g)
  · simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] using
      HasRingHomProperty.appTop (P := @LocallyOfFiniteType) (g ≫ f) inferInstance
  · exact (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine g).mp
      ⟨inferInstance, inferInstance⟩

/-- Being an open morphism is local on the source for the fppf topology. -/
@[stacks 036P]
instance isLocalAtSource_fppf_isOpenMap :
    (topologically IsOpenMap : MorphismProperty Scheme.{u}).IsLocalAtSource
      Scheme.fppfPrecoverage := by
  have : MorphismProperty.RespectsLeft (topologically IsOpenMap : MorphismProperty Scheme.{u})
      (@Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) :=
    ⟨fun g hg f hf ↦ by
      have : Flat g := hg.1
      have : LocallyOfFinitePresentation g := hg.2
      have : UniversallyOpen g := UniversallyOpen.of_flat g
      exact MorphismProperty.comp_mem _ g f (Scheme.Hom.isOpenMap g) hf⟩
  exact isLocalAtSource_fppf_of_affine_descent _ fun g f hsurj _ _ hcomp ↦
    IsOpenMap.of_comp g.continuous hsurj.surj hcomp

/-- Being universally open is local on the source for the fppf topology. -/
@[stacks 036Q]
instance universallyOpen_isLocalAtSource :
    MorphismProperty.IsLocalAtSource (@UniversallyOpen.{u}) Scheme.fppfPrecoverage := by
  refine MorphismProperty.IsLocalAtSource.mk_of_iff_of_zeroHypercover fun {X Y} f 𝒰 ↦ ⟨?_, ?_⟩
  · intro hf i
    have hmem : 𝒰.presieve₀ ∈
        Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u})
          _ := 𝒰.mem₀
    have hi := ((Scheme.presieve₀_mem_precoverage_iff 𝒰.toPreZeroHypercover).mp hmem).2 i
    have : Flat (𝒰.f i) := hi.1
    have : LocallyOfFinitePresentation (𝒰.f i) := hi.2
    exact MorphismProperty.comp_mem _ (𝒰.f i) f (UniversallyOpen.of_flat _) hf
  · intro h
    rw [universallyOpen_iff]
    intro X' Y' i₁ i₂ f' hpull
    have hstd : IsOpenMap (pullback.fst i₂ f) := by
      refine MorphismProperty.IsLocalAtSource.of_zeroHypercover
        (P := (topologically IsOpenMap : MorphismProperty Scheme.{u}))
        (𝒰.pullbackCoverOfRight i₂ f) fun j ↦ ?_
      have hcomp : (𝒰.pullbackCoverOfRight i₂ f).f j ≫ pullback.fst i₂ f =
          pullback.fst i₂ (𝒰.f j ≫ f) := by
        change pullback.map i₂ (𝒰.f j ≫ f) i₂ f (𝟙 Y') (𝒰.f j) (𝟙 Y) (by simp) (by simp) ≫
          pullback.fst i₂ f = pullback.fst i₂ (𝒰.f j ≫ f)
        rw [pullback.lift_fst]
        simp
      rw [hcomp]
      exact (h j).universally_isOpenMap (pullback.snd i₂ (𝒰.f j ≫ f)) i₂
        (pullback.fst i₂ (𝒰.f j ≫ f)) (IsPullback.of_hasPullback i₂ (𝒰.f j ≫ f))
    change IsOpenMap f'
    rw [← hpull.isoPullback_hom_fst]
    exact IsOpenMap.comp (g := (pullback.fst i₂ f).base)
      (f := hpull.isoPullback.hom.base) hstd hpull.isoPullback.hom.isOpenMap

end AlgebraicGeometry

end
