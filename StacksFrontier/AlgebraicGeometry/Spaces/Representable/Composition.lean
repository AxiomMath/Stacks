module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Constructors
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Category.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Defs.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Properties
public import StacksCore.Tactic.StacksAttribute

/-!
# Properties of morphisms of schemes stable under composition

Of the properties of morphisms of schemes that are preserved by arbitrary base change, the
following are also preserved by composition: affine, quasi-affine, a closed immersion, an
open immersion, a locally closed immersion, étale, finite, finite locally free, of finite
presentation, of finite type, quasi-finite, locally quasi-finite, flat, H-projective,
integral, a monomorphism, proper, quasi-compact, separated, quasi-separated, smooth,
surjective, syntomic, G-unramified, a universal homeomorphism, universally closed,
universally injective, universally open, universally submersive, and unramified. For a
property on both lists, the corresponding property of a representable morphism of
presheaves on a big site is again preserved by composition.

## Main results

* `AlgebraicGeometry.Space.universalHomeomorphism_isStableUnderComposition`: a composite of
  universal homeomorphisms of schemes is a universal homeomorphism.
* `AlgebraicGeometry.Space.universallySubmersive_isStableUnderComposition`: a composite of
  universally submersive morphisms of schemes is universally submersive.

## Implementation notes

Every entry of the list other than the two above is already available as a declaration,
either in Mathlib or elsewhere in this library, and is adopted rather than restated. Finite
presentation is the conjunction of local finite presentation, quasi-compactness and
quasi-separatedness formed in `AlgebraicGeometry.FinitePresentation`, so its entry is the
composition statement for each of the three conjuncts. The finite-type entry, likewise a
conjunction, is stated in the companion module
`StacksFrontier.AlgebraicGeometry.Spaces.Representable.CompositionFiniteType`, and the five
entries whose composition result lives elsewhere in this library — quasi-affine,
quasi-finite, syntomic, H-projective and finite locally free — in the companion module
`StacksFrontier.AlgebraicGeometry.Spaces.Representable.CompositionClauses`.

Both remaining entries concern a universal closure. Being a universal homeomorphism is
`AlgebraicGeometry.UniversalHomeomorphism`, carrying the universal closure of the
homeomorphism property as a field, so its composition instance is extracted from that of
the closure. Universal submersiveness is the universal closure of the property that the
underlying continuous map is a quotient map, and the general categorical statement
`CategoryTheory.MorphismProperty.IsStableUnderComposition.universally` applies to it
directly.

## References

* [Stacks Project, Tag 02WG](https://stacks.math.columbia.edu/tag/02WG)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.Space

add_to_stacks 02WG "affine" AlgebraicGeometry.instIsAffineHomCompScheme
add_to_ega "II 1.3.5" AlgebraicGeometry.instIsAffineHomCompScheme
add_to_ega "II 1.3.6" "partial" AlgebraicGeometry.instIsAffineHomCompScheme
add_to_ega "II 1.6.2" AlgebraicGeometry.instIsAffineHomCompScheme

add_to_stacks 02WG "etale" AlgebraicGeometry.Etale.etale_comp

add_to_stacks 02WG "finite_integral" AlgebraicGeometry.IsFinite.instIsStableUnderCompositionScheme
add_to_ega "II 6.1.5" "(ii), finite branch"
  AlgebraicGeometry.IsFinite.instIsStableUnderCompositionScheme
add_to_ega "IV 21.10.15" "Condition a)"
  AlgebraicGeometry.IsFinite.instIsStableUnderCompositionScheme

add_to_stacks 02WG "finite_integral"
  AlgebraicGeometry.IsIntegralHom.instIsStableUnderCompositionScheme
add_to_ega "II 6.1.5" "(ii), integral branch"
  AlgebraicGeometry.IsIntegralHom.instIsStableUnderCompositionScheme

add_to_stacks 02WG "finite_presentation" AlgebraicGeometry.locallyOfFinitePresentation_comp

add_to_stacks 02WG "finite_presentation" AlgebraicGeometry.quasiCompact_comp
add_to_sga "4 VI 1.8" "(i), special case" AlgebraicGeometry.quasiCompact_comp
add_to_sga "4 VI 1.9.1" "(i), special case" AlgebraicGeometry.quasiCompact_comp
add_to_ega "I 6.6.4" AlgebraicGeometry.quasiCompact_comp
add_to_ega "IV 1.1.2" AlgebraicGeometry.quasiCompact_comp

add_to_stacks 02WG "finite_presentation" AlgebraicGeometry.quasiSeparated_comp
add_to_sga "4 VI 1.8" "(i), special case" AlgebraicGeometry.quasiSeparated_comp
add_to_sga "4 VI 1.9.1" "(i), special case" AlgebraicGeometry.quasiSeparated_comp
add_to_ega "IV 1.2.2" AlgebraicGeometry.quasiSeparated_comp

add_to_stacks 02WG "flat" AlgebraicGeometry.Flat.comp

add_to_stacks 02WG "immersions" AlgebraicGeometry.IsClosedImmersion.comp
add_to_ega "I 10.14.5" "(i), ordinary schemes" AlgebraicGeometry.IsClosedImmersion.comp
add_to_ega "I 4.1.6" AlgebraicGeometry.IsClosedImmersion.comp
add_to_ega "I 4.2.5" AlgebraicGeometry.IsClosedImmersion.comp
add_to_ega "I 4.5.5" "(i), special case" AlgebraicGeometry.IsClosedImmersion.comp

add_to_stacks 02WG "immersions" AlgebraicGeometry.IsOpenImmersion.comp
add_to_ega "I 4.2.5" AlgebraicGeometry.IsOpenImmersion.comp
add_to_ega "I 4.5.5" "(i), special case" AlgebraicGeometry.IsOpenImmersion.comp

add_to_stacks 02WG "immersions" AlgebraicGeometry.IsImmersion.comp
add_to_ega "I 4.1.6" AlgebraicGeometry.IsImmersion.comp
add_to_ega "I 4.2.5" AlgebraicGeometry.IsImmersion.comp
add_to_ega "I 4.5.5" "(i), special case" AlgebraicGeometry.IsImmersion.comp

add_to_stacks 02WG "monomorphisms" CategoryTheory.mono_comp

add_to_stacks 02WG "proper" AlgebraicGeometry.IsProper.stableUnderComposition

add_to_stacks 02WG "quasi_compact" AlgebraicGeometry.quasiCompact_isStableUnderComposition
add_to_sga "4 VI 1.8" "(i), special case" AlgebraicGeometry.quasiCompact_isStableUnderComposition
add_to_sga "4 VI 1.9.1" "(i), special case" AlgebraicGeometry.quasiCompact_isStableUnderComposition
add_to_ega "I 6.6.4" AlgebraicGeometry.quasiCompact_isStableUnderComposition
add_to_ega "IV 1.1.2" AlgebraicGeometry.quasiCompact_isStableUnderComposition

add_to_stacks 02WG "quasi_separated"
  AlgebraicGeometry.quasiSeparated_isStableUnderComposition
add_to_sga "4 VI 1.8" "(i), special case" AlgebraicGeometry.quasiSeparated_isStableUnderComposition
add_to_sga "4 VI 1.9.1" "(i), special case"
  AlgebraicGeometry.quasiSeparated_isStableUnderComposition
add_to_ega "IV 1.2.2" AlgebraicGeometry.quasiSeparated_isStableUnderComposition

add_to_stacks 02WG "separated" AlgebraicGeometry.IsSeparated.stableUnderComposition
add_to_ega "I 10.15.3" "(i), ordinary preschemes"
  AlgebraicGeometry.IsSeparated.stableUnderComposition
add_to_ega "I 5.5.1" AlgebraicGeometry.IsSeparated.stableUnderComposition

add_to_stacks 02WG "smooth" AlgebraicGeometry.smooth_comp
add_to_sga "1 II 1.3" "more general" AlgebraicGeometry.smooth_comp
add_to_ega "IV 17.3.3" "smooth branch of (ii)" AlgebraicGeometry.smooth_comp
add_to_ega "IV 6.8.3" "more general" AlgebraicGeometry.smooth_comp

add_to_stacks 02WG "surjective" AlgebraicGeometry.instSurjectiveCompScheme
add_to_ega "I 2.2.7" AlgebraicGeometry.instSurjectiveCompScheme

add_to_stacks 02WG "universally_closed"
  AlgebraicGeometry.universallyClosed_isStableUnderComposition

add_to_stacks 02WG "universally_injective"
  AlgebraicGeometry.universallyInjective_isStableUnderComposition
add_to_ega "I 3.5.6" AlgebraicGeometry.universallyInjective_isStableUnderComposition
add_to_ega "IV 6.15.3.1" "(i), special case"
  AlgebraicGeometry.universallyInjective_isStableUnderComposition

add_to_stacks 02WG "universally_open" AlgebraicGeometry.UniversallyOpen.instCompScheme
add_to_ega "IV 14.3.4" "(i), special case" AlgebraicGeometry.UniversallyOpen.instCompScheme
add_to_ega "IV 2.4.3" "(ii), universally open" AlgebraicGeometry.UniversallyOpen.instCompScheme

add_to_stacks 02WG "unramified" AlgebraicGeometry.unramified_isStableUnderComposition

add_to_stacks 02WG "unramified" AlgebraicGeometry.gUnramified_isStableUnderComposition

/-- Universal homeomorphisms of schemes are stable under composition. -/
@[stacks 02WG "universal_homeomorphism"]
public instance universalHomeomorphism_isStableUnderComposition :
    MorphismProperty.IsStableUnderComposition
      (@AlgebraicGeometry.UniversalHomeomorphism.{u} : MorphismProperty Scheme.{u}) := by
  let _ : MorphismProperty.IsStableUnderComposition
      (topologically @IsHomeomorph : MorphismProperty Scheme.{u}) :=
    topologically_isStableUnderComposition (P := @IsHomeomorph) (fun _ _ hf hg => hg.comp hf)
  exact ⟨fun f g hf hg => ⟨MorphismProperty.comp_mem _ f g hf.1 hg.1⟩⟩

/-- The composite of universally submersive morphisms of schemes is universally
submersive. -/
@[stacks 02WG "universally_submersive"]
public instance universallySubmersive_isStableUnderComposition :
    (topologically @Topology.IsQuotientMap :
      MorphismProperty Scheme.{u}).universally.IsStableUnderComposition :=
  IsStableUnderComposition.universally _
    (hP := topologically_isStableUnderComposition _ (fun _ _ hf hg => hg.comp hf))

end AlgebraicGeometry.Space

end
