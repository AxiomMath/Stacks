module

public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralUniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteCriteriaRepresentable03ZQ
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardPreservesEpi
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedIntegralPushforwardEpi
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks 0A4K for a finite morphism of algebraic spaces

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`.  Stacks 0A4K says that for `f` *integral* — "integral (for example finite)" — the
direct image on the abelian sheaves of the small étale sites is exact and its positive-degree
higher direct images vanish.  Both conclusions are proved here **for `f` finite**, with the
finiteness as the only hypothesis.

## Main results

* this module's exactness results use `AlgebraicGeometry.Space.IsFinite.isIntegralHom` of
  `StacksFrontier.AlgebraicGeometry.Spaces.IntegralUniversallyClosed` — a finite morphism is
  integral.
* `AlgebraicGeometry.Space.smallEtalePushforward_preservesEpimorphisms_of_isFinite` is
  **Stacks 04C2, part (1), for a finite morphism of algebraic spaces**: the small étale direct
  image of sheaves of sets transforms surjections into surjections.
* `AlgebraicGeometry.Space.smallEtaleAbelianPushforward_exact_of_isFinite` and
  `AlgebraicGeometry.Space.smallEtaleAbelianPushforward_rightDerivedPlus_isZero_of_isFinite` are
  the two conclusions of Stacks 0A4K for a finite morphism.

## Implementation notes

**The finite case and the integral case.**  The reduction
`AlgebraicGeometry.Space.smallEtalePushforward_preservesEpimorphisms_of_etaleCover` replaces `f`
by its base change along a scheme atlas of `Y`, and
`AlgebraicGeometry.Space.representedSmallEtalePushforward_preservesEpimorphisms` settles that
base change once its *source* is representable too.  Representability of the source is supplied
here by `AlgebraicGeometry.Space.relativelyRepresentable_of_isFinite`, which is Stacks 03ZQ,
condition (2) implies condition (1), **for finite morphisms**.  The same reduction runs for an
integral morphism, with `AlgebraicGeometry.Space.isIntegralHom_iff_representable` in place of
that witness, and the integral case of Stacks 0A4K — the full statement of the tag — is
`AlgebraicGeometry.Space.smallEtaleAbelianPushforward_exact_of_isIntegralHom` and
`AlgebraicGeometry.Space.smallEtaleAbelianPushforward_rightDerivedPlus_isZero_of_isIntegralHom`
in `StacksFrontier.AlgebraicGeometry.Spaces.IntegralPushforwardExact`.  The declarations below
keep the finite hypothesis under which they were proved; nothing here narrows "integral"
silently.

**The representable base change is taken from the representability witness, not from a chosen
fibre product.**  `AlgebraicGeometry.Space.relativelyRepresentable_of_isFinite` applied to the
atlas `a : yoneda.obj T ⟶ Y` already produces an object `P` of the site, a morphism `s : P ⟶ T`
and a Cartesian square over `f` and `a`.  Using that square rather than
`CategoryTheory.Limits.pullback f a` makes the base change *literally* the represented morphism
`yoneda.map s`, so no transport along an isomorphism of algebraic spaces is needed and
`AlgebraicGeometry.Space.SmallEtale.congr` does not appear.

**Integrality of the representing morphism of schemes** is read off the represented base changes
of `yoneda.map s` at the identity square `CategoryTheory.IsPullback.id_horiz`, which is the only
place where the second component of `CategoryTheory.MorphismProperty.relative` is used.

## References

* [Stacks Project, Tag 0A4K](https://stacks.math.columbia.edu/tag/0A4K)
* [Stacks Project, Tag 04C2](https://stacks.math.columbia.edu/tag/04C2)
* [Stacks Project, Tag 03ZQ](https://stacks.math.columbia.edu/tag/03ZQ)
* [Stacks Project, Tag 03ZP](https://stacks.math.columbia.edu/tag/03ZP)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 04C2, part (1), for a finite morphism of algebraic spaces.** The small étale
direct image of sheaves of sets along a finite morphism of algebraic spaces over `S` transforms
surjections into surjections.

A scheme atlas `a : yoneda.obj T ⟶ Y` of the target is chosen, and the base change of `f` along
it is taken from the representability witness of
`AlgebraicGeometry.Space.relativelyRepresentable_of_isFinite`: that produces an object `P` of
the site, a morphism `s : P ⟶ T` and a Cartesian square exhibiting `yoneda.map s` as the base
change.  Its underlying morphism of schemes is finite, hence integral, so
`AlgebraicGeometry.Space.representedSmallEtalePushforward_preservesEpimorphisms` applies, and
`AlgebraicGeometry.Space.smallEtalePushforward_preservesEpimorphisms_of_etaleCover` carries the
conclusion back to `f`. -/
theorem smallEtalePushforward_preservesEpimorphisms_of_isFinite
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsFinite B S hS f.hom) :
    Functor.PreservesEpimorphisms (smallToposMorphism B S hS f).pushforward := by
  obtain ⟨T, a, hasurj, haetale⟩ := Y.property.exists_atlas
  have hrep : yoneda.relativelyRepresentable f.hom :=
    relativelyRepresentable_of_isFinite B S hS X.property.isSheaf Y.property.isSheaf hf
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
  -- the base change is finite, so its morphism of schemes is finite, hence integral
  have hfin' : IsFinite B S hS f'.hom :=
    (isFinite_iff_holdsOnAffineBaseChange f'.hom).mpr
      (HoldsOnAffineBaseChange.of_isPullback (AlgebraicSpaces.isPullback_hom B S hS sq)
        ((isFinite_iff_holdsOnAffineBaseChange f.hom).mp hf))
  have hsrep : yoneda.relativelyRepresentable (yoneda.map s) :=
    relativelyRepresentable_yoneda_map B S hS s
  have hfinS : _root_.AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme B S hS).map s) :=
    (presheaf_isFinite_of_isFinite (yoneda.map s) hsrep hfin').2 (𝟙 _) (𝟙 _) s
      (IsPullback.id_horiz _)
  have hintS : _root_.AlgebraicGeometry.IsIntegralHom ((BigFppfOver.toScheme B S hS).map s) :=
    ((_root_.AlgebraicGeometry.IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).mp hfinS).1
  exact smallEtalePushforward_preservesEpimorphisms_of_etaleCover B S hS i f' f g sq hg hgs
    (representedSmallEtalePushforward_preservesEpimorphisms B S hS s hsrep hintS)

/-- **Stacks 0A4K, exactness, for a finite morphism.** For a finite morphism `f : X ⟶ Y` of
algebraic spaces over `S` the direct image on the abelian sheaves of the small étale sites is
exact.

The source states this for an integral morphism, "integral (for example finite)"; that case is
`AlgebraicGeometry.Space.smallEtaleAbelianPushforward_exact_of_isIntegralHom`.  The step from
surjections of sheaves of sets to exactness on abelian sheaves is Stacks 04DB, already
available as `Stacks.Topos.AbelianPushforward.abelianPushforward_exact`, and the surjection
statement is
`AlgebraicGeometry.Space.smallEtalePushforward_preservesEpimorphisms_of_isFinite`. -/
@[stacks 0A4K "exactness of f_*, the finite case"]
theorem smallEtaleAbelianPushforward_exact_of_isFinite {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : IsFinite B S hS f.hom) :
    exactFunctor (Sheaf (SmallEtale.topology B S hS X.obj) AddCommGrpCat.{u + 1})
      (Sheaf (SmallEtale.topology B S hS Y.obj) AddCommGrpCat.{u + 1})
      (Stacks.Topos.AbelianPushforward.abelianPushforward (SmallEtale.topology B S hS X.obj)
        (smallToposMorphism B S hS f)) :=
  smallEtaleAbelianPushforward_exact B S hS f (IsFinite.isIntegralHom B S hS hf)
    fun _ => smallEtalePushforward_preservesEpimorphisms_of_isFinite B S hS f hf

/-- **Stacks 0A4K, vanishing of the positive-degree higher direct images, for a finite
morphism.** For a finite morphism `f : X ⟶ Y` of algebraic spaces over `S` the right derived
functors of the small étale direct image on abelian sheaves vanish in positive degree.

The integral case, which contains this one, is
`AlgebraicGeometry.Space.smallEtaleAbelianPushforward_rightDerivedPlus_isZero_of_isIntegralHom`. -/
@[stacks 0A4K "vanishing of R^p f_* for p > 0, the finite case",
  sga "4 Vbis 4.3.4" "Remarque 4.3.4",
  sga "4½ Arcata 2.3.6" "more general"]
theorem smallEtaleAbelianPushforward_rightDerivedPlus_isZero_of_isFinite
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsFinite B S hS f.hom)
    (F : Sheaf (SmallEtale.topology B S hS X.obj) AddCommGrpCat.{u + 1})
    (p : ℤ) (hp : 0 < p) :
    IsZero (((Stacks.Topos.AbelianPushforward.abelianPushforward
      (SmallEtale.topology B S hS X.obj)
      (smallToposMorphism B S hS f)).rightDerivedPlus p).obj F) :=
  smallEtaleAbelianPushforward_rightDerivedPlus_isZero B S hS f
    (IsFinite.isIntegralHom B S hS hf)
    (fun _ => smallEtalePushforward_preservesEpimorphisms_of_isFinite B S hS f hf) F p hp

end AlgebraicGeometry.Space

end
