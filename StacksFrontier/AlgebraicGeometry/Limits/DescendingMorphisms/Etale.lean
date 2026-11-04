module

public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.EtaleUnramified
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Monomorphism
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Unramified
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Étale morphisms and open immersions descend to a finite stage

Let a scheme be the limit of a cofiltered diagram of quasi-compact and quasi-separated schemes
with affine transition morphisms. A morphism over one stage which is locally of finite
presentation and becomes étale, respectively an open immersion, over the limit is already étale,
respectively an open immersion, after passing to some later stage.

## Main results

* `AlgebraicGeometry.exists_etale_pullback_of_isLimit`: étaleness descends to a finite stage.
* `AlgebraicGeometry.exists_isOpenImmersion_pullback`: an open immersion over the limit descends
  to a finite stage.

## Implementation notes

Schemes over the chosen stage are objects of its over category, and their base changes are
expressed by `CategoryTheory.Over.pullback`. An object of `Over i₀` packages both a later index
and its transition morphism to `i₀`.

Étaleness is smoothness together with formal unramifiedness, so it descends by combining the
descent of smoothness with the descent of unramifiedness and taking a common later stage. An open
immersion is a flat monomorphism which is locally of finite presentation, so it descends by
combining the étale and monomorphism statements.

The source assumes a directed preorder. The results are stated for an arbitrary cofiltered
category, which is the natural categorical generality of the same argument.

## References

* [Stacks Project, Tag 07RP](https://stacks.math.columbia.edu/tag/07RP)
* [Stacks Project, Tag 0EUU](https://stacks.math.columbia.edu/tag/0EUU)
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- A property of morphisms stable under base change, holding for the base change of a morphism
to one stage of a diagram, holds for its base change to every later stage. -/
private lemma prop_overPullback_map_of_comp {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u})
    {i₀ : I} {X₀ Y₀ : Over (D.obj i₀)} (f₀ : X₀ ⟶ Y₀) (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] {a b : I} (v : a ⟶ b) (w : b ⟶ i₀)
    (hp : P ((Over.pullback (D.map w)).map f₀).left) :
    P ((Over.pullback (D.map (v ≫ w))).map f₀).left := by
  have h := overPullback_map_comp P (D.map w) (D.map v) f₀ hp
  rwa [← D.map_comp] at h

/-- **Stacks 07RP.** If a locally finitely presented morphism at one stage of a cofiltered
inverse system becomes étale over the limit, then it is étale at some later stage. -/
@[stacks 07RP, ega "IV 17.7.8" "(ii) étale"]
theorem exists_etale_pullback_of_isLimit
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c) (i₀ : I)
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    (X₀ Y₀ : Over (D.obj i₀)) (f₀ : X₀ ⟶ Y₀)
    [CompactSpace (D.obj i₀)] [QuasiSeparatedSpace (D.obj i₀)]
    [CompactSpace X₀.left] [QuasiSeparatedSpace X₀.left]
    [CompactSpace Y₀.left] [QuasiSeparatedSpace Y₀.left]
    [LocallyOfFinitePresentation f₀.left]
    [Etale ((Over.pullback (c.π.app i₀)).map f₀).left] :
    ∃ i : Over i₀, Etale ((Over.pullback (D.map i.hom)).map f₀).left := by
  have : Smooth ((Over.pullback (c.π.app i₀)).map f₀).left := inferInstance
  have : Unramified ((Over.pullback (c.π.app i₀)).map f₀).left := unramified_of_etale _
  have : LocallyOfFiniteType f₀.left := inferInstance
  obtain ⟨i, gi, hs⟩ :=
    exists_smooth_baseChange_of_smooth_limitBaseChange D c i₀ X₀ Y₀ f₀ hc
  obtain ⟨j, gj, hu⟩ :=
    exists_unramified_baseChange_of_unramified_limitBaseChange D c i₀ X₀ Y₀ f₀ hc
  obtain ⟨k, ki, kj, h⟩ := IsCofiltered.cospan gi gj
  have : MorphismProperty.RespectsIso (@Smooth : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : MorphismProperty.RespectsIso
      (@FormallyUnramified : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hs' := prop_overPullback_map_of_comp D f₀ (@Smooth) ki gi hs
  have hfu : FormallyUnramified ((Over.pullback (D.map gj)).map f₀).left :=
    (unramified_iff_locallyOfFiniteType_and_formallyUnramified _).mp hu |>.2
  have hformal := prop_overPullback_map_of_comp D f₀ (@FormallyUnramified) kj gj hfu
  rw [← h] at hformal
  have het : Etale ((Over.pullback (D.map (ki ≫ gi))).map f₀).left := by
    have : Smooth ((Over.pullback (D.map (ki ≫ gi))).map f₀).left := hs'
    exact (Etale.iff_flat_and_formallyUnramified).2 ⟨inferInstance, hformal, inferInstance⟩
  exact ⟨Over.mk (ki ≫ gi), het⟩

/-- **Stacks 0EUU.** An open immersion obtained by base change to the inverse limit of an
affine-transition inverse system descends to some stage of the system. -/
@[stacks 0EUU]
lemma exists_isOpenImmersion_pullback
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (S : I ⥤ Scheme.{u}) (c : Cone S) (hc : IsLimit c)
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (S.map g)]
    (i₀ : I) [CompactSpace (S.obj i₀)] [QuasiSeparatedSpace (S.obj i₀)]
    (X₀ Y₀ : Over (S.obj i₀))
    [CompactSpace X₀.left] [QuasiSeparatedSpace X₀.left]
    [CompactSpace Y₀.left] [QuasiSeparatedSpace Y₀.left]
    (f₀ : X₀ ⟶ Y₀) [LocallyOfFinitePresentation f₀.left]
    (hf : IsOpenImmersion ((Over.pullback (c.π.app i₀)).map f₀).left) :
    ∃ (i : I) (g : i ⟶ i₀), IsOpenImmersion ((Over.pullback (S.map g)).map f₀).left := by
  have : IsOpenImmersion ((Over.pullback (c.π.app i₀)).map f₀).left := hf
  obtain ⟨ii, hi⟩ := exists_etale_pullback_of_isLimit S c hc i₀ X₀ Y₀ f₀
  obtain ⟨j, gj, hj⟩ := exists_mono_baseChange_of_mono_limitBaseChange S c hc i₀ X₀ Y₀ f₀
  obtain ⟨k, ki, kj, hfac⟩ := IsCofiltered.cospan ii.hom gj
  have : MorphismProperty.RespectsIso (@Flat : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hflat := prop_overPullback_map_of_comp S f₀ (@Flat) ki ii.hom
    (Etale.iff_flat_and_formallyUnramified.mp hi |>.1)
  have hmono : Mono ((Over.pullback (S.map (ki ≫ ii.hom))).map f₀).left := by
    rw [hfac]
    exact prop_overPullback_map_of_comp S f₀ (MorphismProperty.monomorphisms Scheme) kj gj hj
  refine ⟨k, ki ≫ ii.hom, ?_⟩
  have : Flat ((Over.pullback (S.map (ki ≫ ii.hom))).map f₀).left := hflat
  have : Mono ((Over.pullback (S.map (ki ≫ ii.hom))).map f₀).left := hmono
  have : LocallyOfFinitePresentation ((Over.pullback (S.map (ki ≫ ii.hom))).map f₀).left :=
    MorphismProperty.overPullbackMap (P := @LocallyOfFinitePresentation)
      (S.map (ki ≫ ii.hom)) _ inferInstance
  exact IsOpenImmersion.of_flat_of_mono _

end AlgebraicGeometry
