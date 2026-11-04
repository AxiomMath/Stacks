module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Defs.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Properties
public import StacksCore.Tactic.StacksAttribute

/-!
# Properties of morphisms of schemes stable under base change

A morphism of presheaves on a big site is called representable when every base change of it
along a representable presheaf is a morphism of schemes, and a property of morphisms of
schemes may be transported to such a morphism of presheaves exactly when the property is
preserved by arbitrary base change. This module collects the properties for which that is
the case: affine, étale, finite, of finite presentation, of finite type, flat, G-unramified,
integral, locally of finite presentation, locally of finite type, locally quasi-finite, a
monomorphism, proper, quasi-compact, quasi-finite, quasi-separated, separated, smooth,
surjective, a universal homeomorphism, universally closed, universally injective,
universally open, universally submersive, and unramified.

## Main results

* `AlgebraicGeometry.Space.finitePresentation_isStableUnderBaseChange`: a morphism of
  schemes of finite presentation stays of finite presentation after arbitrary base change.

## Implementation notes

Every entry of the list other than finite presentation, finite type and quasi-finiteness is
already available as a declaration, either in Mathlib or elsewhere in this library, and is
adopted rather than restated. Those three are conjunctions of other entries of the list, so
each has its stability assembled from the stability of its conjuncts. Finite presentation is
the conjunction of local finite presentation, quasi-compactness and quasi-separatedness
formed in `AlgebraicGeometry.FinitePresentation`, and is assembled here; finite type and
quasi-finiteness are assembled in the companion modules
`StacksFrontier.AlgebraicGeometry.Spaces.Representable.BaseChangeFiniteType` and
`…BaseChangeQuasiFinite`. Being a universal homeomorphism is
`AlgebraicGeometry.UniversalHomeomorphism`, the universal closure of the homeomorphism
property, and the universal closure of any morphism property is stable under base change by
`CategoryTheory.MorphismProperty.universally_isStableUnderBaseChange`.

The two quasi-finiteness entries of the list, the finite-type entry, and the entries each of
which is a single existing result, are stated in the companion modules
`StacksFrontier.AlgebraicGeometry.Spaces.Representable.BaseChangeLocallyQuasiFinite`,
`…BaseChangeQuasiFinite`, `…BaseChangeFiniteType`, `…BaseChangeClauses` and
`…BaseChangeRemainingClauses`.

All the statements are instances of Mathlib's
`CategoryTheory.MorphismProperty.IsStableUnderBaseChange`, so they apply to an arbitrary
pullback square of schemes rather than to a chosen fibre product.

## References

* [Stacks Project, Tag 02WF](https://stacks.math.columbia.edu/tag/02WF)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Space

add_to_stacks 02WF "affine" AlgebraicGeometry.isAffineHom_isStableUnderBaseChange
add_to_sga "1 VIII 2.1" "partial" AlgebraicGeometry.isAffineHom_isStableUnderBaseChange
add_to_sga "1 VIII 5.6" "necessity" AlgebraicGeometry.isAffineHom_isStableUnderBaseChange
add_to_sga "3 I 4.6.4.1" "partial" AlgebraicGeometry.isAffineHom_isStableUnderBaseChange
add_to_sga "3 III 0.1.7" "(a)" AlgebraicGeometry.isAffineHom_isStableUnderBaseChange
add_to_sga "3 III 0.17" "partial" AlgebraicGeometry.isAffineHom_isStableUnderBaseChange
add_to_sga "3 VIB 10.1" "partial" AlgebraicGeometry.isAffineHom_isStableUnderBaseChange
add_to_sga "3 XIX 2.1" "more general" AlgebraicGeometry.isAffineHom_isStableUnderBaseChange
add_to_sga "4 VIII 5.1" "partial" AlgebraicGeometry.isAffineHom_isStableUnderBaseChange
add_to_ega "II 1.5.1" AlgebraicGeometry.isAffineHom_isStableUnderBaseChange
add_to_ega "II 1.5.5" "more general" AlgebraicGeometry.isAffineHom_isStableUnderBaseChange
add_to_ega "II 1.6.2" AlgebraicGeometry.isAffineHom_isStableUnderBaseChange
add_to_ega "IV 14.5.11" "Necessity direction" AlgebraicGeometry.isAffineHom_isStableUnderBaseChange
add_to_ega "IV 2.7.1" "(xiii)" AlgebraicGeometry.isAffineHom_isStableUnderBaseChange

add_to_stacks 02WF "etale" AlgebraicGeometry.Etale.etale_isStableUnderBaseChange

add_to_stacks 02WF "finite" AlgebraicGeometry.IsFinite.instIsStableUnderBaseChangeScheme
add_to_sga "1 VIII 5.7" "preservation (finite)"
  AlgebraicGeometry.IsFinite.instIsStableUnderBaseChangeScheme
add_to_sga "1 VIII 6.6" AlgebraicGeometry.IsFinite.instIsStableUnderBaseChangeScheme
add_to_sga "3 VIB 10.1" "partial" AlgebraicGeometry.IsFinite.instIsStableUnderBaseChangeScheme
add_to_sga "4 VIII 5.4" "more general" AlgebraicGeometry.IsFinite.instIsStableUnderBaseChangeScheme
add_to_ega "I 6.4.12" "more general" AlgebraicGeometry.IsFinite.instIsStableUnderBaseChangeScheme
add_to_ega "I 6.4.6" "more general" AlgebraicGeometry.IsFinite.instIsStableUnderBaseChangeScheme
add_to_ega "II 6.1.5" "(iii), finite branch"
  AlgebraicGeometry.IsFinite.instIsStableUnderBaseChangeScheme
add_to_ega "III 2.6.2.1" "more general" AlgebraicGeometry.IsFinite.instIsStableUnderBaseChangeScheme
add_to_ega "IV 2.7.1" "implication" AlgebraicGeometry.IsFinite.instIsStableUnderBaseChangeScheme
add_to_ega "IV 21.10.16" "f₁ is finite" AlgebraicGeometry.IsFinite.instIsStableUnderBaseChangeScheme

add_to_stacks 02WF "finite_type" AlgebraicGeometry.locallyOfFiniteType_isStableUnderBaseChange

add_to_stacks 02WF "flat" AlgebraicGeometry.Flat.isStableUnderBaseChange

add_to_stacks 02WF "g_unramified" AlgebraicGeometry.gUnramified_isStableUnderBaseChange

add_to_stacks 02WF "integral" AlgebraicGeometry.IsIntegralHom.instIsStableUnderBaseChangeScheme
add_to_sga "1 VIII 5.7" "preservation (integral)"
  AlgebraicGeometry.IsIntegralHom.instIsStableUnderBaseChangeScheme
add_to_ega "II 6.1.5" "(iii), integral branch"
  AlgebraicGeometry.IsIntegralHom.instIsStableUnderBaseChangeScheme
add_to_ega "IV 2.7.1" "implication"
  AlgebraicGeometry.IsIntegralHom.instIsStableUnderBaseChangeScheme

add_to_stacks 02WF "locally_finite_presentation"
  AlgebraicGeometry.locallyOfFinitePresentation_isStableUnderBaseChange

add_to_stacks 02WF "monomorphism"
  CategoryTheory.MorphismProperty.IsStableUnderBaseChange.monomorphisms

add_to_stacks 02WF "proper" AlgebraicGeometry.IsProper.isStableUnderBaseChange

add_to_stacks 02WF "quasi_separated" AlgebraicGeometry.quasiSeparated_isStableUnderBaseChange

add_to_stacks 02WF "separated" AlgebraicGeometry.IsSeparated.isStableUnderBaseChange
add_to_sga "1 IX 2.4" "partial" AlgebraicGeometry.IsSeparated.isStableUnderBaseChange
add_to_sga "1 IX 4.2" "partial" AlgebraicGeometry.IsSeparated.isStableUnderBaseChange
add_to_sga "1 VIII 4.8" "partial" AlgebraicGeometry.IsSeparated.isStableUnderBaseChange
add_to_sga "3 VIB 10.1" "separatedness" AlgebraicGeometry.IsSeparated.isStableUnderBaseChange
add_to_ega "I 10.15.3" "(iii), special case" AlgebraicGeometry.IsSeparated.isStableUnderBaseChange
add_to_ega "I 5.5.1" AlgebraicGeometry.IsSeparated.isStableUnderBaseChange
add_to_ega "I 5.5.3" "more general" AlgebraicGeometry.IsSeparated.isStableUnderBaseChange
add_to_ega "III 6.9.1" "separatedness of f′_i" AlgebraicGeometry.IsSeparated.isStableUnderBaseChange
add_to_ega "III 7.7.2" "separatedness of f'" AlgebraicGeometry.IsSeparated.isStableUnderBaseChange
add_to_ega "IV 2.7.1" "implication" AlgebraicGeometry.IsSeparated.isStableUnderBaseChange

add_to_stacks 02WF "smooth" AlgebraicGeometry.smooth_isStableUnderBaseChange

add_to_stacks 02WF "surjective" AlgebraicGeometry.Surjective.instIsStableUnderBaseChangeScheme
add_to_sga "1 VIII 3.1" "Surjectivity clause"
  AlgebraicGeometry.Surjective.instIsStableUnderBaseChangeScheme
add_to_sga "3 VIB 10.1" "partial, sufficiency"
  AlgebraicGeometry.Surjective.instIsStableUnderBaseChangeScheme
add_to_sga "3 VIIB 2.4.1" "special case"
  AlgebraicGeometry.Surjective.instIsStableUnderBaseChangeScheme
add_to_ega "I 3.5.2" AlgebraicGeometry.Surjective.instIsStableUnderBaseChangeScheme

add_to_stacks 02WF "universal_homeomorphism"
  CategoryTheory.MorphismProperty.universally_isStableUnderBaseChange
add_to_sga "1 IX 4.2" "partial" CategoryTheory.MorphismProperty.universally_isStableUnderBaseChange
add_to_sga "1 VIII 4.7" "more general"
  CategoryTheory.MorphismProperty.universally_isStableUnderBaseChange
add_to_sga "3 IV 1.11" "partial" CategoryTheory.MorphismProperty.universally_isStableUnderBaseChange
add_to_sga "4 VI 1.9.1" "more general"
  CategoryTheory.MorphismProperty.universally_isStableUnderBaseChange
add_to_ega "IV 14.3.4" "(ii), special case"
  CategoryTheory.MorphismProperty.universally_isStableUnderBaseChange
add_to_ega "IV 2.4.3" "more general"
  CategoryTheory.MorphismProperty.universally_isStableUnderBaseChange
add_to_ega "IV 2.6.4" "partial" CategoryTheory.MorphismProperty.universally_isStableUnderBaseChange

add_to_stacks 02WF "universally_closed" AlgebraicGeometry.universallyClosed_isStableUnderBaseChange

add_to_stacks 02WF "universally_injective"
  AlgebraicGeometry.UniversallyInjective.isStableUnderBaseChange

add_to_stacks 02WF "universally_open"
  AlgebraicGeometry.UniversallyOpen.instIsStableUnderBaseChangeScheme
add_to_sga "1 IX 2.4" "partial" AlgebraicGeometry.UniversallyOpen.instIsStableUnderBaseChangeScheme
add_to_sga "1 VIII 4.7" "necessity"
  AlgebraicGeometry.UniversallyOpen.instIsStableUnderBaseChangeScheme
add_to_sga "3 V 6.1" "special case"
  AlgebraicGeometry.UniversallyOpen.instIsStableUnderBaseChangeScheme
add_to_sga "3 VIB 2.1.2" "partial"
  AlgebraicGeometry.UniversallyOpen.instIsStableUnderBaseChangeScheme
add_to_ega "IV 14.3.4" "(ii), global form"
  AlgebraicGeometry.UniversallyOpen.instIsStableUnderBaseChangeScheme
add_to_ega "IV 2.4.3" "(iii), universally open"
  AlgebraicGeometry.UniversallyOpen.instIsStableUnderBaseChangeScheme
add_to_ega "IV 2.6.4" "necessity in (i)"
  AlgebraicGeometry.UniversallyOpen.instIsStableUnderBaseChangeScheme

add_to_stacks 02WF "unramified" AlgebraicGeometry.unramified_isStableUnderBaseChange

/-- Morphisms of schemes of finite presentation remain of finite presentation
after arbitrary base change. -/
@[stacks 02WF "finite_presentation"]
public instance finitePresentation_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange
      (@AlgebraicGeometry.FinitePresentation.{u}) := by
  let _ : MorphismProperty.IsStableUnderBaseChange (@QuasiCompact ⊓ @QuasiSeparated) := .inf
  exact MorphismProperty.IsStableUnderBaseChange.inf

end AlgebraicGeometry.Space

end
