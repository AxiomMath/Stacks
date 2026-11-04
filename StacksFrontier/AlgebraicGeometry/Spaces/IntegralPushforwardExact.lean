module

public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePushforwardExact
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralFiniteTfae
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks 0A4K for an integral morphism of algebraic spaces

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`. Stacks 0A4K says that for `f` integral the direct image on the abelian sheaves of the
small étale sites is exact and its positive-degree higher direct images vanish. Both conclusions
are proved here with integrality as the only hypothesis, so this is the full statement of the
tag; `StacksFrontier.AlgebraicGeometry.Spaces.FinitePushforwardExact` records the finite case,
which the integral case contains.

## Main results

* `AlgebraicGeometry.Space.smallEtalePushforward_preservesEpimorphisms_of_isIntegralHom` is
  **Stacks 04C2, part (1), for an integral morphism of algebraic spaces**: the small étale
  direct image of sheaves of sets transforms surjections into surjections.
* `AlgebraicGeometry.Space.smallEtaleAbelianPushforward_exact_of_isIntegralHom` and
  `AlgebraicGeometry.Space.smallEtaleAbelianPushforward_rightDerivedPlus_isZero_of_isIntegralHom`
  are the two conclusions of **Stacks 0A4K**.

## Implementation notes

The proof is the one of the finite case, with the representability of an integral morphism in
place of that of a finite one. A scheme atlas `a : yoneda.obj T ⟶ Y` of the target is chosen;
`AlgebraicGeometry.Space.isIntegralHom_iff_representable`, which is Stacks 03ZQ for integral
morphisms, makes `f` relatively representable, so its base change along `a` is the represented
morphism `yoneda.map s` for a morphism `s` of the site; integrality of `s` as a morphism of
schemes then makes
`AlgebraicGeometry.Space.representedSmallEtalePushforward_preservesEpimorphisms` apply, and
`AlgebraicGeometry.Space.smallEtalePushforward_preservesEpimorphisms_of_etaleCover` carries the
conclusion back to `f`.

## References

* [Stacks Project, Tag 0A4K](https://stacks.math.columbia.edu/tag/0A4K)
* [Stacks Project, Tag 04C2](https://stacks.math.columbia.edu/tag/04C2)
* [Stacks Project, Tag 03ZQ](https://stacks.math.columbia.edu/tag/03ZQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 04C2, part (1), for an integral morphism of algebraic spaces.** The small étale
direct image of sheaves of sets along an integral morphism of algebraic spaces over `S`
transforms surjections into surjections.

A scheme atlas `a : yoneda.obj T ⟶ Y` of the target is chosen, and the base change of `f` along
it is taken from the representability witness that Stacks 03ZQ attaches to an integral
morphism: that produces an object `P` of the site, a morphism `s : P ⟶ T` and a Cartesian
square exhibiting `yoneda.map s` as the base change. Its underlying morphism of schemes is
integral, so `AlgebraicGeometry.Space.representedSmallEtalePushforward_preservesEpimorphisms`
applies, and
`AlgebraicGeometry.Space.smallEtalePushforward_preservesEpimorphisms_of_etaleCover` carries the
conclusion back to `f`. -/
@[stacks 04C2 "part (1), for an integral morphism of algebraic spaces"]
theorem smallEtalePushforward_preservesEpimorphisms_of_isIntegralHom
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsIntegralHom B S hS f.hom) :
    Functor.PreservesEpimorphisms (smallToposMorphism B S hS f).pushforward := by
  obtain ⟨T, a, hasurj, haetale⟩ := Y.property.exists_atlas
  have hrep : yoneda.relativelyRepresentable f.hom :=
    ((isIntegralHom_iff_representable B S hS f.hom X.property Y.property).mp hf).1
  let s : hrep.pullback a ⟶ T := hrep.snd a
  let Y' : AlgebraicSpaces B S hS := ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩
  let X' : AlgebraicSpaces B S hS :=
    ⟨yoneda.obj (hrep.pullback a), isAlgebraicSpace_yoneda B S hS (hrep.pullback a)⟩
  let g : Y' ⟶ Y := ObjectProperty.homMk a
  let i : X' ⟶ X := ObjectProperty.homMk (hrep.fst a)
  let f' : X' ⟶ Y' := representedSpaceMap B S hS s
  have sq : IsPullback i f' f g :=
    IsPullback.of_map_of_faithful (ObjectProperty.ι _) (hrep.isPullback a)
  have hg : IsEtale B S hS g.hom := isEtale_of_presheaf_etale B S hS haetale
  have hgs : IsSurjective B S hS g.hom :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS Y.1 Y.property T a).mp hasurj
  -- the base change of an integral morphism is integral
  have hint' : IsIntegralHom B S hS f'.hom :=
    (isIntegralHom_iff_holdsOnAffineBaseChange f'.hom).mpr
      (HoldsOnAffineBaseChange.of_isPullback (AlgebraicSpaces.isPullback_hom B S hS sq)
        ((isIntegralHom_iff_holdsOnAffineBaseChange f.hom).mp hf))
  have hsrep : yoneda.relativelyRepresentable (yoneda.map s) :=
    relativelyRepresentable_yoneda_map B S hS s
  have hintP : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsIntegralHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map s) :=
    presheaf_isIntegralHom_of_isIntegralHom (yoneda.map s) hsrep hint'
  have hintS : _root_.AlgebraicGeometry.IsIntegralHom ((BigFppfOver.toScheme B S hS).map s) :=
    hintP.2 (𝟙 _) (𝟙 _) s (IsPullback.id_horiz _)
  exact smallEtalePushforward_preservesEpimorphisms_of_etaleCover B S hS i f' f g sq hg hgs
    (representedSmallEtalePushforward_preservesEpimorphisms B S hS s hsrep hintS)

/-- **Stacks 0A4K, exactness.** For an integral morphism `f : X ⟶ Y` of algebraic spaces over
`S` the direct image on the abelian sheaves of the small étale sites is exact.

The step from surjections of sheaves of sets to exactness on abelian sheaves is Stacks 04DB,
available as `Stacks.Topos.AbelianPushforward.abelianPushforward_exact`, and the surjection
statement is
`AlgebraicGeometry.Space.smallEtalePushforward_preservesEpimorphisms_of_isIntegralHom`. -/
@[stacks 0A4K "exactness of f_* for an integral morphism of algebraic spaces"]
theorem smallEtaleAbelianPushforward_exact_of_isIntegralHom {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : IsIntegralHom B S hS f.hom) :
    exactFunctor (Sheaf (SmallEtale.topology B S hS X.obj) AddCommGrpCat.{u + 1})
      (Sheaf (SmallEtale.topology B S hS Y.obj) AddCommGrpCat.{u + 1})
      (Stacks.Topos.AbelianPushforward.abelianPushforward (SmallEtale.topology B S hS X.obj)
        (smallToposMorphism B S hS f)) :=
  smallEtaleAbelianPushforward_exact B S hS f hf
    fun _ => smallEtalePushforward_preservesEpimorphisms_of_isIntegralHom B S hS f hf

/-- **Stacks 0A4K, vanishing of the positive-degree higher direct images.** For an integral
morphism `f : X ⟶ Y` of algebraic spaces over `S` the right derived functors of the small étale
direct image on abelian sheaves vanish in positive degree.

Given the exactness this is formal, by
`CategoryTheory.Functor.isZero_rightDerivedPlus_of_exact`. -/
@[stacks 0A4K "vanishing of R^p f_* for p > 0 for an integral morphism of algebraic spaces",
  sga "4 VIII 5.6" "more general",
  sga "4 Vbis 4.3.4" "more general",
  sga "4½ Arcata 2.3.6" "more general"]
theorem smallEtaleAbelianPushforward_rightDerivedPlus_isZero_of_isIntegralHom
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsIntegralHom B S hS f.hom)
    (F : Sheaf (SmallEtale.topology B S hS X.obj) AddCommGrpCat.{u + 1})
    (p : ℤ) (hp : 0 < p) :
    IsZero (((Stacks.Topos.AbelianPushforward.abelianPushforward
      (SmallEtale.topology B S hS X.obj)
      (smallToposMorphism B S hS f)).rightDerivedPlus p).obj F) :=
  smallEtaleAbelianPushforward_rightDerivedPlus_isZero B S hS f hf
    (fun _ => smallEtalePushforward_preservesEpimorphisms_of_isIntegralHom B S hS f hf) F p hp

end AlgebraicGeometry.Space

end
