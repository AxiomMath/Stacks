module

public import Mathlib.AlgebraicGeometry.Properties
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Criterion
public import StacksFrontier.RingTheory.Flat.FaithfullyFlat.Descent
public import StacksFrontier.RingTheory.Smooth.Reduced

/-!
# Reducedness is local in the smooth topology

A scheme is reduced if and only if the members of a jointly surjective family of smooth
morphisms onto it are reduced.

## Main results

* `AlgebraicGeometry.isReduced_isLocal_smooth` states that reducedness is local for the
  smooth precoverage.

## Implementation notes

The smooth topology is the precoverage of jointly surjective families of
`AlgebraicGeometry.Smooth` morphisms. Ascent is reducedness of a smooth algebra over a
reduced ring, and descent is reducedness along a faithfully flat ring map; both are read
off the global sections of the affine schemes involved.

## References

* [Stacks Project, Tag 034E](https://stacks.math.columbia.edu/tag/034E)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

private instance isReduced_isLocal_zariski :
    ObjectProperty.IsLocal (fun X : Scheme.{u} => IsReduced X) Scheme.zariskiPrecoverage :=
  ObjectProperty.IsLocal.mk_of_zeroHypercover fun X 𝒰 => IsReduced.iff_of_openCover X 𝒰

/-- **Stacks Project, Tag 034E.** Reducedness of schemes is local for the smooth
precoverage. -/
@[stacks 034E]
instance isReduced_isLocal_smooth :
    ObjectProperty.IsLocal (fun X : Scheme.{u} => IsReduced X)
      (Scheme.precoverage @Smooth) := by
  refine isLocal_smoothPrecoverage_of_affine (fun X : Scheme.{u} => IsReduced X) ?_ ?_
  · intro X S hX hS f hsm hred
    let : IsAffine X := hX
    let : IsAffine S := hS
    have hmap : (f.appTop).hom.Smooth := by
      simpa [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE] using
        hsm.smooth_appLE (isAffineOpen_top S) (isAffineOpen_top X) le_rfl
    let : Algebra Γ(S, ⊤) Γ(X, ⊤) := (f.appTop).hom.toAlgebra
    let : Algebra.Smooth Γ(S, ⊤) Γ(X, ⊤) := RingHom.smooth_algebraMap.mp hmap
    let : _root_.IsReduced Γ(S, ⊤) := hred.component_reduced ⊤
    let : _root_.IsReduced Γ(X, ⊤) := Algebra.isReduced_of_smooth Γ(S, ⊤) Γ(X, ⊤)
    exact isReduced_of_isAffine_isReduced X
  · intro X S hX hS f hsm hsurj hred
    let : IsAffine X := hX
    let : IsAffine S := hS
    let : Smooth f := hsm
    have hff : (f.appTop).hom.FaithfullyFlat :=
      (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine f).mp ⟨inferInstance, hsurj⟩
    let : _root_.IsReduced Γ(X, ⊤) := hred.component_reduced ⊤
    let : _root_.IsReduced Γ(S, ⊤) := RingHom.FaithfullyFlat.isReduced hff
    exact isReduced_of_isAffine_isReduced S

end AlgebraicGeometry
