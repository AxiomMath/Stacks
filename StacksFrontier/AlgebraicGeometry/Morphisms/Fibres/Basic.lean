module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme

/-!
# Reduced closed subschemes and fibres

Basic facts about reduced closed subschemes and scheme-theoretic fibres that are used
throughout the study of the fibres of a morphism of schemes.

## Main results

* `AlgebraicGeometry.isReduced_nilradical_subscheme`: the reduction of a scheme is reduced.
* `AlgebraicGeometry.ker_eq_nilradical_of_support_eq_top`: a closed immersion from a reduced
  scheme whose image is everything is the inclusion of the reduction.
* `AlgebraicGeometry.isReduced_fiber_comp`: restricting a morphism to an open subscheme of its
  source preserves reducedness of the fibres.
* `AlgebraicGeometry.Scheme.Hom.apply_fiberι`: a point of the fibre of `f` over `y` is carried
  by `f` to `y`.

## Implementation notes

A closed subscheme is represented by an ideal sheaf, and `Scheme.nilradical` is the radical of
the zero ideal sheaf, so the reduction of `X` is `X.nilradical.subscheme`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The reduction of a scheme, the closed subscheme cut out by the nilradical ideal sheaf, is
reduced. -/
theorem isReduced_nilradical_subscheme (X : Scheme.{u}) : IsReduced X.nilradical.subscheme := by
  rw [Scheme.nilradical]
  infer_instance

/-- A closed immersion from a reduced scheme whose set-theoretic image is the whole target cuts
out the nilradical ideal sheaf; that is, it presents the target's reduction. -/
theorem ker_eq_nilradical_of_support_eq_top {Z W : Scheme.{u}} (i : Z ⟶ W)
    [IsClosedImmersion i] [IsReduced Z] (h : i.ker.support = ⊤) : i.ker = W.nilradical := by
  have hrad : i.ker.radical = i.ker := by
    apply Scheme.IdealSheafData.ext
    funext U
    rw [Scheme.IdealSheafData.radical_ideal, Scheme.Hom.ker_apply]
    exact (Ideal.radical_eq_iff).2 <| (RingHom.ker_isRadical_iff_reduced_of_surjective
      (i.app_surjective U.1 U.2)).2 inferInstance
  calc
    i.ker = i.ker.radical := hrad.symm
    _ = Scheme.IdealSheafData.vanishingIdeal i.ker.support :=
      (Scheme.IdealSheafData.vanishingIdeal_support).symm
    _ = W.nilradical := by simp [h]

/-- If the fibre of `f` over `y` is reduced, then so is the fibre over `y` of the restriction of
`f` to an open subscheme of its source. -/
theorem isReduced_fiber_comp {U X Y : Scheme.{u}} (i : U ⟶ X) (f : X ⟶ Y)
    [IsOpenImmersion i] (y : Y) [IsReduced (f.fiber y)] :
    IsReduced ((i ≫ f).fiber y) := by
  have hred : IsReduced (pullback i (f.fiberι y)) :=
    isReduced_of_isOpenImmersion (pullback.snd i (f.fiberι y))
  exact ObjectProperty.prop_of_iso IsReduced
    (pullbackRightPullbackFstIso f (Y.fromSpecResidueField y) i) hred

namespace Scheme.Hom

/-- A point of the scheme-theoretic fibre of `f` over `y` is carried by `f` to `y`. -/
theorem apply_fiberι {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) (x : f.fiber y) :
    f (f.fiberι y x) = y := by
  have h : f.fiberι y x ∈ f ⁻¹' {y} := f.range_fiberι y ▸ Set.mem_range_self x
  simpa using h

end Scheme.Hom

end AlgebraicGeometry

end
