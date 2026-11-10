module

public import Mathlib.CategoryTheory.Iso

/-!
# A functor carries a given isomorphism to an isomorphism

Mathlib has this as an instance, `CategoryTheory.Functor.map_isIso`, which takes the
invertibility of the morphism as an instance argument. That form is unusable wherever the
morphism's category is presented in a spelling instance search will not unfold — notably through
`DerivedCategory` and the derived functors on it, where synthesis fails outright. This module is
the same statement with the invertibility taken as an EXPLICIT HYPOTHESIS, so that a caller who
holds a proof of `IsIso f` can apply it directly.

It exists because four copies of it had accumulated, in
`StacksFrontier/Deformation/RingedSpaceThickening/FlatLiftExistence.lean`,
`StacksFrontier/AlgebraicGeometry/BaseChange/TorIndependence/TensorAndSheafHomBaseChange.lean`,
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalAlgebraSquareMapAmbientComparison.lean` and
`StacksFrontier/AlgebraicGeometry/Perfect/Coherator/KoszulPowerLift.lean`, whose import closures
have no common ancestor in this library; this module is that ancestor.
-/

@[expose] public section

namespace CategoryTheory.Functor

universe v₁ v₂ u₁ u₂

/-- A functor carries an isomorphism to an isomorphism, with the invertibility supplied as an
explicit hypothesis rather than found by instance search. -/
public theorem isIso_map_of_isIso {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    (F : C ⥤ D) {A B : C} (f : A ⟶ B) (hf : IsIso f) : IsIso (F.map f) :=
  have := hf
  inferInstance

end CategoryTheory.Functor

end
