module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Properties
public import StacksCore.Tactic.StacksAttribute

/-!
# Varieties over a field

Let `k` be a field. A *variety* over `k` is a scheme `X` equipped with a structure morphism
`f : X ⟶ Spec k` such that `X` is integral and `f` is separated and of finite type. A variety
is *proper* or *smooth* when its structure morphism is, and *affine* when its underlying scheme
is.

## Main definitions

* `AlgebraicGeometry.IsVariety`: the property of a structure morphism to the spectrum of a field
  that makes its source a variety.
* `AlgebraicGeometry.IsProperVariety`: a variety whose structure morphism is proper.
* `AlgebraicGeometry.IsSmoothVariety`: a variety whose structure morphism is smooth.

## Main results

* `AlgebraicGeometry.isProperVariety_iff` and `AlgebraicGeometry.isSmoothVariety_iff`:
  characterizations of the two classes as a variety together with the corresponding property of
  the structure morphism.
* `AlgebraicGeometry.isProperVariety_iff_isProper` and
  `AlgebraicGeometry.isSmoothVariety_iff_smooth`: the same characterizations when the variety
  hypothesis is already available.

## References

* [Stacks Project, Tag 020D](https://stacks.math.columbia.edu/tag/020D)
* [Stacks Project, Tag 04L1](https://stacks.math.columbia.edu/tag/04L1)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A scheme over a field is a variety when it is integral and its structure morphism is
separated and of finite type. -/
@[stacks 020D, stacks 03RE "the variety clause"]
class IsVariety (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) : Prop
    extends IsIntegral X, IsSeparated f, LocallyOfFiniteType f, QuasiCompact f

add_to_stacks 04L1 "affine_variety_2" AlgebraicGeometry.IsAffine
add_to_ega "I 1.7.1" AlgebraicGeometry.IsAffine

/-- A variety over a field is proper when its structure morphism to the spectrum of the field
is proper. -/
@[stacks 04L1 "proper_variety"]
class IsProperVariety (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) : Prop
    extends IsVariety k f, IsProper f

/-- A proper variety is exactly a variety whose structure morphism is proper. -/
theorem isProperVariety_iff (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) :
    IsProperVariety k f ↔ IsVariety k f ∧ IsProper f :=
  ⟨fun h => ⟨h.toIsVariety, h.toIsProper⟩,
    fun ⟨_, _⟩ => IsProperVariety.mk⟩

/-- For a variety, being a proper variety is equivalent to properness of its
structure morphism. -/
@[simp]
theorem isProperVariety_iff_isProper (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsVariety k f] :
    IsProperVariety k f ↔ IsProper f :=
  (isProperVariety_iff k f).trans (and_iff_right inferInstance)

/-- A variety over a field is smooth when its structure morphism to the spectrum of the field
is smooth. -/
@[stacks 04L1 "smooth_variety"]
class IsSmoothVariety (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) : Prop extends IsVariety k f, Smooth f

/-- A smooth variety is exactly a variety whose structure morphism is smooth. -/
public theorem isSmoothVariety_iff (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) : IsSmoothVariety k f ↔ IsVariety k f ∧ Smooth f :=
  ⟨fun h => ⟨h.toIsVariety, h.toSmooth⟩, fun ⟨hv, hs⟩ => { toIsVariety := hv, toSmooth := hs }⟩

/-- For a variety, being a smooth variety is equivalent to smoothness of its
structure morphism. -/
@[simp]
public theorem isSmoothVariety_iff_smooth (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsVariety k f] : IsSmoothVariety k f ↔ Smooth f :=
  ⟨fun h => h.toSmooth, fun hs => { toIsVariety := inferInstance, toSmooth := hs }⟩

end AlgebraicGeometry

end
