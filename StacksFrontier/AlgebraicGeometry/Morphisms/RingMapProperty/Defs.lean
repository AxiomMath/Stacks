module

public import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
public import Mathlib.RingTheory.LocalProperties.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Properties of ring maps, and the morphisms they define

A property `P` of commutative-ring homomorphisms is *local* when it is preserved by
simultaneous principal localization, passes from a map `R_f → A` to the induced composite
`R → A_a`, and may be checked on a finite principal open cover of the target. A local
property determines a property of morphisms of schemes: a morphism is *locally of type `P`*
when every point of its source has an affine open neighbourhood mapping into an affine open
of the target on which the induced map of rings of sections satisfies `P`.

## Main definitions

* `RingHom.StacksPropertyIsLocal` is locality of a property of ring homomorphisms.
* `AlgebraicGeometry.locallyOfType` is the morphism property of being locally of type `P`.

## Main results

* `RingHom.stacksPropertyIsLocal_iff` is the direct characterization by the three
  locality conditions.

## Implementation notes

Mathlib's `RingHom.PropertyIsLocal` is a different notion: it permits composition with a
principal localization of the target, but not the simultaneous passage from `R_f → A` to
`R → A_a` required here. The two are therefore kept apart, the name of this one recording
that it is the Stacks Project's notion. Abstract localizations are used in conditions
(1)(a) and (1)(b), while condition (1)(c) is expressed using Mathlib's canonical principal
localizations.

Stability under base change and under composition are Mathlib's
`RingHom.IsStableUnderBaseChange` and `RingHom.StableUnderComposition`. The former uses an
abstract pushout algebra; `RingHom.IsStableUnderBaseChange.tensorProduct` specializes it to
the tensor-product formulation `P (R → A) → P (R' → R' ⊗[R] A)` that the source states, and
`RingHom.IsStableUnderBaseChange.mk` promotes that formulation back to arbitrary pushout
algebras for a property satisfying `RingHom.RespectsIso`.

The three numbered parts of the source definition are therefore registered on three
declarations: part (1) on `RingHom.StacksPropertyIsLocal` here, and parts (2) and (3) on the
two Mathlib notions by `add_to_stacks` below. Part (1) carries `stacks_fixed` rather than
`stacks` only because the carrier is a `structure`.

`locallyOfType` is stated as a `MorphismProperty` so that properties of scheme morphisms can
specialize it directly. The witness `h` that the source open maps into the target open
determines the induced map `f.appLE V U h` on sections.

## References

* [Stacks Project, Tag 01SR](https://stacks.math.columbia.edu/tag/01SR)
* [Stacks Project, Tag 01SS](https://stacks.math.columbia.edu/tag/01SS)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace RingHom

/-- A property of commutative-ring homomorphisms is local if it is preserved
by simultaneous principal localization, passes from a map `R_f → A` to the
composite `R → A_a`, and can be checked on a finite principal open cover of
the target. -/
@[stacks_fixed 01SR "(1) local, all three conditions (a), (b), (c)"]
structure StacksPropertyIsLocal
    (P : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop) : Prop where
  /-- Condition (1)(a): localizing a map at an element of its source preserves
  the property. -/
  localizationAwayPreserves : RingHom.LocalizationAwayPreserves P
  /-- Condition (1)(b): if `P` holds for `R_f → A`, then it holds for the
  induced composite `R → A_a`. -/
  compPrincipalLocalizations : ∀ {R A Rf Aa : Type u} [CommRing R] [CommRing A]
    [CommRing Rf] [CommRing Aa] (f : R) (a : A) [Algebra R Rf]
    [IsLocalization.Away f Rf] [Algebra A Aa] [IsLocalization.Away a Aa]
    (g : Rf →+* A), P g → P ((algebraMap A Aa).comp (g.comp (algebraMap R Rf)))
  /-- Condition (1)(c): the property descends from a finite principal open
  cover of the target. -/
  ofLocalizationFiniteSpanTarget : RingHom.OfLocalizationFiniteSpanTarget P

/-- A property is local exactly when it satisfies the three defining localization
conditions. -/
@[simp] theorem stacksPropertyIsLocal_iff
    (P : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop) :
    StacksPropertyIsLocal P ↔ RingHom.LocalizationAwayPreserves P ∧
      (∀ {R A Rf Aa : Type u} [CommRing R] [CommRing A] [CommRing Rf] [CommRing Aa]
        (f : R) (a : A) [Algebra R Rf] [IsLocalization.Away f Rf]
        [Algebra A Aa] [IsLocalization.Away a Aa] (g : Rf →+* A),
        P g → P ((algebraMap A Aa).comp (g.comp (algebraMap R Rf)))) ∧
      RingHom.OfLocalizationFiniteSpanTarget P :=
  ⟨fun ⟨a, b, c⟩ => ⟨a, b, c⟩, fun ⟨a, b, c⟩ => ⟨a, b, c⟩⟩

end RingHom

add_to_stacks 01SR "(2) stable under base change, in the pushout formulation"
  RingHom.IsStableUnderBaseChange
add_to_stacks 01SR "(3) stable under composition" RingHom.StableUnderComposition

namespace AlgebraicGeometry

/-- A morphism of schemes is locally of type `P` if every point of its source lies in
an affine open mapping into an affine open of the target on whose rings of sections
the induced homomorphism satisfies `P`. -/
@[stacks 01SS] abbrev locallyOfType (P : ∀ {R S : Type u} [CommRing R] [CommRing S],
    (R →+* S) → Prop) : MorphismProperty Scheme.{u} := fun {X S} f ↦ ∀ x : X, ∃
  (V : S.affineOpens) (U : X.affineOpens) (_ : x ∈ U.1) (h : U.1 ≤ f ⁻¹ᵁ V.1), P (f.appLE V U h).hom

end AlgebraicGeometry
