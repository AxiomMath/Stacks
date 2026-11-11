module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.RingTheory.RingHom.StandardSmooth
public import StacksCore.Tactic.StacksAttribute

/-!
# Smooth morphisms of schemes and standard smooth morphisms of affine schemes

A morphism of schemes is smooth if it is smooth at every point of its source; it is smooth of
relative dimension `d` when in addition its sheaf of relative differentials is finite locally free
of constant rank `d`. A morphism between affine schemes is standard smooth when its induced map on
global sections is a standard smooth ring homomorphism.

## Main definitions

* `AlgebraicGeometry.Smooth` is the predicate that a morphism of schemes is smooth.
* `AlgebraicGeometry.SmoothOfRelativeDimension` is the property that a scheme morphism is
  locally standard smooth of a specified relative dimension.
* `AlgebraicGeometry.IsStandardSmooth` is the predicate that a morphism of affine schemes is
  standard smooth.

## Main results

* `AlgebraicGeometry.isStandardSmooth_iff_exists_iso_specMap` characterizes standard smoothness by
  an isomorphism of arrows to the spectrum of a standard smooth ring map.
* `AlgebraicGeometry.isStandardSmooth_specMap_iff` identifies standard smoothness of `Spec.map g`
  with standard smoothness of `g`.

## Implementation notes

The existing class `AlgebraicGeometry.Smooth` gives the standard affine-local formulation of
smoothness for scheme morphisms and is adopted as the formalization of that notion.
`AlgebraicGeometry.SmoothOfRelativeDimension` refines it by standard smooth maps of a fixed
dimension; Stacks' own notion (Tag 02G2: smooth with `Ω_{X/S}` finite locally free of rank `d`) is
`AlgebraicGeometry.IsSmoothOfRelativeDimension`, and the two are identified by
`AlgebraicGeometry.smoothOfRelativeDimension_iff_isSmoothOfRelativeDimension`, both in
`StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension`.

Affine schemes are canonically isomorphic to the spectra of their rings of global sections. Thus
standard smoothness is expressed by applying `RingHom.IsStandardSmooth` to the map on global
sections; that ring-theoretic predicate includes the choice of a standard smooth presentation. The
lemma `AlgebraicGeometry.isStandardSmooth_iff_exists_iso_specMap` proves that this formulation is
equivalent to the existence of a standard smooth ring map whose spectrum is isomorphic to the
given arrow.

The affineness assumptions are typeclass arguments, so the predicate applies directly to
morphisms whose source and target are already known to be affine.

## References

* [Stacks Project, Tag 01V5](https://stacks.math.columbia.edu/tag/01V5)
* [Stacks Project, Tag 02G2](https://stacks.math.columbia.edu/tag/02G2)
-/

@[expose] public section

namespace AlgebraicGeometry

open CategoryTheory

universe u

add_to_stacks 01V5 "smooth_morphism" AlgebraicGeometry.Smooth
add_to_sga "1 II 1.1" AlgebraicGeometry.Smooth
add_to_sga "3 XI 1.1" AlgebraicGeometry.Smooth
add_to_sga "3 XI 1.6" AlgebraicGeometry.Smooth
add_to_sga "7 XIV 2.1" "partial" AlgebraicGeometry.Smooth
add_to_ega "IV 17.3.1" AlgebraicGeometry.Smooth

add_to_sga "1 II 1.5" "special case" AlgebraicGeometry.SmoothOfRelativeDimension
add_to_sga "4 XVII 6.3.8" "partial" AlgebraicGeometry.SmoothOfRelativeDimension
add_to_sga "7 XIV 2.1" "partial" AlgebraicGeometry.SmoothOfRelativeDimension
add_to_sga "7 XVIII 5.6.8" AlgebraicGeometry.SmoothOfRelativeDimension

/-- A morphism of affine schemes is standard smooth if the corresponding ring homomorphism on
global sections is standard smooth. -/
@[stacks 01V5 "standard_smooth_affine"]
public abbrev IsStandardSmooth {X S : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsAffine X] [AlgebraicGeometry.IsAffine S] (f : X ⟶ S) : Prop :=
  f.appTop.hom.IsStandardSmooth

/-- Standard smoothness of affine morphisms is invariant under isomorphism in the arrow
category. -/
public lemma isStandardSmooth_iff_of_arrow_iso
    {X S X' S' : Scheme.{u}} [IsAffine X] [IsAffine S] [IsAffine X'] [IsAffine S']
    (f : X ⟶ S) (g : X' ⟶ S') (e : Arrow.mk f ≅ Arrow.mk g) :
    IsStandardSmooth f ↔ IsStandardSmooth g := by
  rw [IsStandardSmooth, IsStandardSmooth, Arrow.iso_w' e,
    Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop]
  let _ : IsIso e.hom.right := inferInstance
  let _ : IsIso e.inv.left := inferInstance
  let _ : IsIso e.hom.right.appTop := by change IsIso (e.hom.right.app ⊤); infer_instance
  let _ : IsIso e.inv.left.appTop := by change IsIso (e.inv.left.app ⊤); infer_instance
  let h := RingHom.isStandardSmooth_respectsIso
  exact (h.cancel_left_isIso e.hom.right.appTop f.appTop).symm.trans
    (h.cancel_right_isIso (e.hom.right.appTop ≫ f.appTop) e.inv.left.appTop).symm

/-- The spectrum of a ring map is standard smooth exactly when the ring map is standard smooth. -/
@[simp]
public lemma isStandardSmooth_specMap_iff {R A : CommRingCat.{u}} (g : R ⟶ A) :
    IsStandardSmooth (Spec.map g) ↔ g.hom.IsStandardSmooth := by
  simpa [IsStandardSmooth] using
    (RingHom.isStandardSmooth_respectsIso.arrow_mk_iso_iff
      (arrowIsoΓSpecOfIsAffine g)).symm

/-- A morphism of affine schemes is standard smooth exactly when it is isomorphic, as an arrow,
to the spectrum of a standard smooth ring map. -/
public lemma isStandardSmooth_iff_exists_iso_specMap {X S : Scheme.{u}}
    [IsAffine X] [IsAffine S] (f : X ⟶ S) :
    IsStandardSmooth f ↔
      ∃ (R A : CommRingCat.{u}) (g : R ⟶ A),
        g.hom.IsStandardSmooth ∧ Nonempty (Arrow.mk f ≅ Arrow.mk (Spec.map g)) := by
  refine ⟨fun hf => ⟨_, _, _, hf, ⟨arrowIsoSpecΓOfIsAffine f⟩⟩, ?_⟩
  rintro ⟨R, A, g, hg, ⟨e⟩⟩
  exact (isStandardSmooth_iff_of_arrow_iso f (Spec.map g) e).2
    ((isStandardSmooth_specMap_iff g).2 hg)

end AlgebraicGeometry
