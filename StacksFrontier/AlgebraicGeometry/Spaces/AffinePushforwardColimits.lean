module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDirectImageQuasicoherentUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffinePushforwardColimits

/-!
# The direct image along an affine morphism of algebraic spaces commutes with colimits of
quasi-coherent modules

Let `f : X ⟶ Y` be an affine morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B`.  This file proves, for a representable target, that the direct image of Stacks 03LU
preserves the colimit of a diagram of quasi-coherent `𝒪_X`-modules.

Nothing of the sort holds for a general morphism, nor for a general diagram: the direct image is a
right adjoint, so the content is entirely in the affineness of `f` and the quasi-coherence of the
diagram.  It is the space-level analogue of
`Stacks.AlgebraicGeometry.PushforwardColimits.preservesColimit_pushforward_of_isAffineHom`.

## The route

It is the route of `AlgebraicGeometry.Space.schemeTargetAffinePushforwardQuasicoherent`, with
quasi-coherence of the direct image replaced by preservation of a colimit, and it is available
because every comparison it uses is an isomorphism of *functors*:

* the first form of [Stacks, Tag 03WG] makes `f` relatively representable with affine represented
  base changes;
* evaluating that at the **identity** of the representable target collapses `f` into a single
  represented base change `q`, with no atlas and no covering;
* `AlgebraicGeometry.Space.modulePushforwardEtaleBaseChangeIso` — Stacks 03LX for the ordinary
  direct image, for an arbitrary étale base-change square — identifies `f_*` composed with
  restriction along the identity with étale restriction along `i` composed with `q_*`, and
  `AlgebraicGeometry.Space.etaleModulePullbackIdIso` cancels the restriction along the identity;
* étale restriction preserves all colimits, being isomorphic to the pullback of modules of
  Stacks 03LU, which is a left adjoint, and it preserves quasi-coherence by [Stacks, Tag 03LX];
* `AlgebraicGeometry.Space.preservesColimit_modulePushforward_representedSpaceMap` is the
  represented case.

## Main results

* `AlgebraicGeometry.Space.preservesColimit_modulePushforward_of_schemeTarget`: **for an affine
  morphism of algebraic spaces whose target is representable, the direct image of Stacks 03LU
  preserves colimits of quasi-coherent modules.**

## Implementation notes

The index shape is `K : Type u₂` with homs in `Type v₂`, arbitrary: the only colimit-preservation
input that is not universe-polymorphic is that of étale restriction, and it is taken here from
`AlgebraicGeometry.Space.modulePullbackAdjunction` — a left adjoint preserves colimits of every
size — rather than from `AlgebraicGeometry.Space.preservesFiniteColimits_etaleModulePullback`,
whose universes are pinned to `u` by the sheafification it goes through.

The étaleness witness `isEtale_of_isPullback … sq.flip hid` is written out at each occurrence
rather than named, because `AlgebraicGeometry.Space.modulePushforwardEtaleBaseChangeIso` takes it
as a derived argument and the applications have to agree on the nose.

Preservation of a colimit is not a local property, so the passage from a representable target
to an arbitrary algebraic space is not the chartwise glueing that
`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePushforward_of_isAffineHom` performs for
quasi-coherence. For an arbitrary target, the base change of `f` along an étale chart of `Y` has
representable target, so the statement below applies there;
`Stacks.AlgebraicGeometry.PushforwardColimits.isIso_map_colimit_post` turns that into invertibility
of the chart restriction `AlgebraicGeometry.Space.chartModuleRestriction` of the comparison
morphism `colimit (D ⋙ f_*) ⟶ f_*(colimit D)`;
`AlgebraicGeometry.Space.chartModuleRestrictionSliceIso` rewrites that restriction as the slice
restriction followed by the comparison of Stacks 04M0; and
`AlgebraicGeometry.Space.isIso_of_isIso_over_affineCharts` lifts the slice statements back. This
file does not carry out that assembly.

## References

* [Stacks Project, Tag 01SB](https://stacks.math.columbia.edu/tag/01SB)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LX](https://stacks.math.columbia.edu/tag/03LX)
* [Stacks Project, Tag 03WG](https://stacks.math.columbia.edu/tag/03WG)
* [Stacks Project, Tag 08AI](https://stacks.math.columbia.edu/tag/08AI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v₂ u₂ u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {K : Type u₂} [Category.{v₂} K] [HasColimitsOfShape K AddCommGrpCat.{u}]
  [∀ R : CommRingCat.{u}, HasColimitsOfShape K (ModuleCat.{u} R)]
  [∀ W : Scheme.{u}, HasColimitsOfShape K W.Modules]

/-- **The direct image along an affine morphism of algebraic spaces with representable target
preserves colimits of quasi-coherent modules.**

This is `AlgebraicGeometry.Space.schemeTargetAffinePushforwardQuasicoherent` for colimits instead
of quasi-coherence, by the same route: relative representability of `f` evaluated at the identity
of the target, the étale base-change isomorphism of Stacks 03LX, and the represented case
`AlgebraicGeometry.Space.preservesColimit_modulePushforward_representedSpaceMap`. -/
theorem preservesColimit_modulePushforward_of_schemeTarget (V : BigFppfOver B S hS)
    {X : AlgebraicSpaces B S hS} (f : X ⟶ schemeSpace V) (hf : IsAffineHom B S hS f.hom)
    {D : K ⥤ Modules.{u, u} B S hS X.1 X.2} (hD : ∀ k, (D.obj k).IsQuasicoherentOnSite) :
    PreservesColimit D (modulePushforward B S hS f) := by
  -- The first form of Stacks 03WG: `f` is relatively representable, and its represented base
  -- changes are affine morphisms of schemes.
  have hrel : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsAffineHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f.hom :=
    (presheaf_isAffineHom_of_isAffineHom_of_isAlgebraicSpace B S hS X.2
      (isAlgebraicSpace_yoneda B S hS V) hf).2
  -- Evaluate it at the identity of `yoneda.obj V`.
  set g₀ : yoneda.obj V ⟶ (schemeSpace V).1 := 𝟙 (yoneda.obj V)
  set W : BigFppfOver B S hS := hrel.rep.pullback g₀
  set q : W ⟶ V := hrel.rep.snd g₀
  -- Lift the square to the category of algebraic spaces.
  let Wsp : AlgebraicSpaces B S hS := ⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩
  let i : Wsp ⟶ X := ObjectProperty.homMk (hrel.rep.fst g₀)
  have sq : IsPullback i (representedSpaceMap B S hS q) f (𝟙 (schemeSpace V)) :=
    IsPullback.of_map_of_faithful
      (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u => IsAlgebraicSpace B S hS F))
      (hrel.rep.isPullback g₀)
  have hid : IsEtale B S hS (𝟙 (schemeSpace V) : schemeSpace V ⟶ schemeSpace V).hom :=
    isEtale_of_isIso B S hS _
  have : _root_.AlgebraicGeometry.IsAffineHom
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) q.left) :=
    hrel.property_snd g₀
  -- Étale restriction along `i` preserves all colimits, being a left adjoint up to isomorphism,
  -- and it preserves quasi-coherence.
  have : PreservesColimitsOfSize.{v₂, u₂} (modulePullback B S hS i) :=
    Adjunction.leftAdjoint_preservesColimits (modulePullbackAdjunction B S hS i)
  have : PreservesColimit D (etaleModulePullback B S hS i
      (isEtale_of_isPullback B S hS (representedSpaceMap B S hS q) i
        (𝟙 (schemeSpace V)) f sq.flip hid)) :=
    (preservesColimit_iff_of_natIso D (modulePullbackIsoEtaleModulePullback B S hS i
      (isEtale_of_isPullback B S hS (representedSpaceMap B S hS q) i
        (𝟙 (schemeSpace V)) f sq.flip hid))).1 inferInstance
  -- The represented case, and its composite with étale restriction.
  have : PreservesColimit (D ⋙ etaleModulePullback B S hS i
      (isEtale_of_isPullback B S hS (representedSpaceMap B S hS q) i
        (𝟙 (schemeSpace V)) f sq.flip hid))
      (modulePushforward B S hS (representedSpaceMap B S hS q)) :=
    preservesColimit_modulePushforward_representedSpaceMap B S hS q
      (fun k ↦ isQuasicoherentOnSite_etaleModulePullback B S hS i _ (D.obj k) (hD k))
  -- Transport along the étale base-change isomorphism, and cancel the restriction along `𝟙`.
  have hstep : PreservesColimit D (modulePushforward B S hS f ⋙
      etaleModulePullback B S hS (𝟙 (schemeSpace V)) hid) :=
    (preservesColimit_iff_of_natIso D
      (modulePushforwardEtaleBaseChangeIso B S hS i (representedSpaceMap B S hS q) f
        (𝟙 (schemeSpace V)) sq hid)).1 (comp_preservesColimit _ _)
  exact (preservesColimit_iff_of_natIso D
    (Functor.isoWhiskerLeft (modulePushforward B S hS f)
      (etaleModulePullbackIdIso B S hS hid) ≪≫ Functor.rightUnitor _)).1 hstep

end AlgebraicGeometry.Space

end
