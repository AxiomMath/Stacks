module

public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import StacksFrontier.AlgebraicGeometry.Groupoids.OverField.Morphisms.Restriction
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Defs.Integral

/-!
# Scalar extension of a scheme along a field extension

For a scheme `X` over a field `k` and a field extension `k'/k`, the scalar extension of `X` is
the fibre product of `X → Spec k` with `Spec k' → Spec k`. When `k'/k` is purely inseparable the
projection from the scalar extension to `X` is a universal homeomorphism, so the two schemes have
the same topology after any further base change.

## Main definitions

* `Stacks.EtaleCohomology.scalarExtension` is the scalar extension of a scheme over `k` along an
  extension `k'/k`, and `Stacks.EtaleCohomology.scalarExtensionFst` is its projection to the
  original scheme.

## Main results

* `Stacks.EtaleCohomology.specMap_universalHomeomorphism_of_isPurelyInseparable`: the spectrum
  map of a purely inseparable field extension is a universal homeomorphism.
* `Stacks.EtaleCohomology.scalarExtensionFst_universalHomeomorphism_of_isPurelyInseparable`: so is
  the projection from the scalar extension along a purely inseparable extension.

## Implementation notes

Universal injectivity is checked on the criterion that two points of a field-valued fibre with
the same image coincide: a morphism out of the spectrum of a field is the spectrum map of a ring
homomorphism, and purely inseparable extensions are epimorphisms of fields in the sense that two
homomorphisms agreeing on the base agree. Being a universal homeomorphism then follows from the
integral, universally injective and surjective criterion, surjectivity being automatic since the
target is the spectrum of a field. The statement for the scalar extension is base change of a
universal homeomorphism.

## References

* [Stacks Project, Tag 04DD](https://stacks.math.columbia.edu/tag/04DD)
* [Stacks Project, Tag 04DF](https://stacks.math.columbia.edu/tag/04DF)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-- Extension of scalars of a scheme over `k` along a field extension `k'/k`. -/
abbrev scalarExtension (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) : Scheme.{u} :=
  pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k')))

/-- The projection from a scalar extension to the original scheme. -/
abbrev scalarExtensionFst (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) : scalarExtension k k' f ⟶ X :=
  pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k k')))

/-- The spectrum map of a purely inseparable field extension is a universal homeomorphism: it is
integral, universally injective, and surjective because its target is a point. -/
theorem specMap_universalHomeomorphism_of_isPurelyInseparable
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    [IsPurelyInseparable k K] :
    UniversalHomeomorphism
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
  (universalHomeomorphism_iff_integral_universallyInjective_surjective _).mpr
    ⟨IsIntegralHom.SpecMap_iff.mpr fun x => Algebra.IsIntegral.isIntegral x,
      universallyInjective_specMap_algebraMap k K, ⟨Function.surjective_to_subsingleton _⟩⟩

/-- Along a purely inseparable field extension the projection from the scalar extension of a
scheme is a universal homeomorphism. -/
theorem scalarExtensionFst_universalHomeomorphism_of_isPurelyInseparable
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    [IsPurelyInseparable k K] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) :
    UniversalHomeomorphism (scalarExtensionFst k K f) :=
  ⟨MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).flip
    (specMap_universalHomeomorphism_of_isPurelyInseparable k K).universally_isHomeomorph⟩

end Stacks.EtaleCohomology

end
