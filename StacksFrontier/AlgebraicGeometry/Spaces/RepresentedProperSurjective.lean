module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineProper
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Properness and surjectivity of a morphism of schemes read off its Yoneda image

For a morphism `f : U ⟶ V` of the big fppf site of `S`, the Yoneda image `yoneda.map f` is a
morphism of algebraic spaces. `AlgebraicGeometry.Space.isProper_yoneda_map` and
`AlgebraicGeometry.Space.isSurjective_yoneda_map` say that it is proper, resp. surjective, when the
underlying morphism of schemes is. This file proves the converses: properness and surjectivity of
the Yoneda image are properness and surjectivity of its represented base changes, among which is
the morphism itself.

## Main results

* `AlgebraicGeometry.Space.isProper_toScheme_of_isProper_yoneda`.
* `AlgebraicGeometry.Space.surjective_toScheme_map_of_isSurjective_yoneda_map`.

These are additions to
`StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineProper` and
`StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints`, kept as a separate file.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A scheme morphism property stable under base change holds for `f` once it holds for the
Yoneda image of `f` relative to the represented morphisms. -/
private theorem map_of_relative_yoneda_map (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] {U V : BigFppfOver B S hS} (f : U ⟶ V)
    (h : (P.inverseImage (BigFppfOver.toScheme B S hS)).relative yoneda (yoneda.map f)) :
    P ((BigFppfOver.toScheme B S hS).map f) := by
  have : HasPullbacks (BigFppfOver B S hS) := inferInstance
  have hstab : (P.inverseImage (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange :=
    ⟨fun hsq hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := P)
      (hsq.map (BigFppfOver.toScheme B S hS)) hg⟩
  exact (MorphismProperty.relative_map_iff (F := yoneda)
    (P := P.inverseImage (BigFppfOver.toScheme B S hS))).mp h

/-- **A morphism of the site whose Yoneda image is proper has proper underlying morphism of
schemes**, the converse of `AlgebraicGeometry.Space.isProper_yoneda_map`: properness of the
Yoneda image is properness of its represented base changes
(`AlgebraicGeometry.Space.presheaf_isProper_iff`), among which is the morphism itself. -/
theorem isProper_toScheme_of_isProper_yoneda {U V : BigFppfOver B S hS} (f : U ⟶ V)
    (hf : IsProper B S hS (yoneda.map f)) :
    _root_.AlgebraicGeometry.IsProper ((BigFppfOver.toScheme B S hS).map f) :=
  map_of_relative_yoneda_map B S hS (@_root_.AlgebraicGeometry.IsProper.{u}) f
    ((presheaf_isProper_iff B S hS (yoneda.map f) (isAlgebraicSpace_yoneda B S hS U)
      (isAlgebraicSpace_yoneda B S hS V) (Functor.relativelyRepresentable.map yoneda f)).mp hf)

/-- **A morphism of the site whose Yoneda image is surjective has surjective underlying morphism
of schemes**, the converse of `AlgebraicGeometry.Space.isSurjective_yoneda_map`. -/
theorem surjective_toScheme_map_of_isSurjective_yoneda_map {U V : BigFppfOver B S hS} (h : U ⟶ V)
    (hh : IsSurjective B S hS (yoneda.map h)) :
    _root_.AlgebraicGeometry.Surjective ((BigFppfOver.toScheme B S hS).map h) :=
  map_of_relative_yoneda_map B S hS (@_root_.AlgebraicGeometry.Surjective.{u}) h
    ((surjective_yonedaMap_iff_surjective_pointsMap B S hS h).mpr hh)

end AlgebraicGeometry.Space

end
