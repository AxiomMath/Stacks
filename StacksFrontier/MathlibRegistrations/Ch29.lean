module

public import Mathlib.AlgebraicGeometry.Birational.RationalMap
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import StacksCore.Tactic.StacksAttribute
import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import StacksCore.Tactic.StacksAttribute

/-!
# Stacks tags of Chapter 29 (Morphisms of schemes) covered by Mathlib

This file records, with `add_to_stacks`, the Stacks tags of Chapter 29 whose statements Mathlib
already states, on the Mathlib declarations that state them. Where Mathlib covers only part of a
tag, the comment names the part, and the parts it does not cover are left unregistered.

* Tag 03BB: a finite monomorphism is a closed immersion
  (`AlgebraicGeometry.IsClosedImmersion.iff_isFinite_and_mono`, which also gives the converse).

* Tag 01QU (a closed immersion is separated) is not registered: Mathlib does not state it; it
  holds only through a chain of three general instances (closed immersion ⇒ preimmersion ⇒
  monomorphism ⇒ separated).
* Tag 01RK is not registered: Mathlib does not state it.
* Tag 01RW is not registered: Mathlib's `AlgebraicGeometry.Scheme.functionField` is the stalk at
  the generic point, not the ring `R(X)` of rational functions of the definition; Mathlib has no
  ring of rational functions, and the identification of the two is Tag 01RV.
* Tag 01S3: part (1) is Mathlib's `AlgebraicGeometry.UniversallyInjective`, registered here;
  Mathlib does not define radicial morphisms (part (2)), whose condition appears only as one of
  the equivalent conditions of `AlgebraicGeometry.tfae_universallyInjective` (Tag 01S4). Part (2)
  is `AlgebraicGeometry.IsRadicial` in `StacksFrontier.AlgebraicGeometry.Morphisms.Radicial`, which
  also states part (1) in the source's form.

The `example`s at the end of the file declare nothing; they only record, as checked statements,
how the registered declarations combine where a tag is covered by more than one of them.

## Affine morphisms

* Tag 01S6 (definition of an affine morphism) is `AlgebraicGeometry.IsAffineHom`, whose single
  field says the preimage of every affine open is an affine open.
* Tag 01S7 has two parts: separated (`AlgebraicGeometry.IsSeparated.of_isAffineHom`) and
  quasi-compact (the instance `AlgebraicGeometry.instQuasiCompactOfIsAffineHom`).
* Tags 01SC, 01SE and 01SH are each one Mathlib instance.

## Morphisms locally of type `P`

* Tag 01SW is `AlgebraicGeometry.HasRingHomProperty.isStableUnderBaseChange`: Mathlib's
  `HasRingHomProperty P Q` says that `P` is "locally of type `Q`" (`P = affineLocally Q`) for a
  local property `Q` of ring maps, and for every local `Q` the property `affineLocally Q` has it
  (first `example` below).

## Finite type

* Mathlib has `AlgebraicGeometry.LocallyOfFiniteType` but no separate predicate for morphisms of
  finite type; by Tag 01T1 a morphism is of finite type if it is locally of finite type and
  quasi-compact. So each "finite type" clause of Tags 01T3 and 01T4 is covered by two
  registrations, one per component, and each part string names its component.
* Tag 01T5 is registered here for "an immersion is locally of finite type" and for the locally
  of finite type component of "a closed immersion is of finite type". The complete statement,
  with the quasi-compact component (closed immersion ⇒ affine ⇒ quasi-compact), is
  `AlgebraicGeometry.isClosedImmersion_finiteType_and_isImmersion_locallyOfFiniteType` in
  `StacksFrontier.AlgebraicGeometry.Morphisms.ImmersionsAndAffine.Immersions`.

## Not registered here

* Tag 01TK (characterisations of locally quasi-finite morphisms) is registered in
  `StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Defs`, on
  `AlgebraicGeometry.locallyQuasiFinite_conditions_tfae` and
  `AlgebraicGeometry.locallyQuasiFinite_conditions_resLE`, not on a Mathlib declaration. Mathlib's
  `AlgebraicGeometry.LocallyQuasiFinite` is defined through `RingHom.QuasiFinite`, which by its
  docstring omits the finite-type condition of the Stacks definition (Tag 00PL); for instance
  `Spec ℚ ⟶ Spec ℤ` is `LocallyQuasiFinite` in Mathlib but not locally of finite type, so it is
  not locally quasi-finite in the sense of Tag 01TD. The registered statements use the Stacks
  notions `LocallyOfFiniteType f ∧ LocallyQuasiFinite f` and `FiniteType ∧ QuasiFinite`.
## Smooth, proper, integral and finite morphisms

* Tags 01VA, 01VC, 01VE, 01VF: smooth morphisms (`AlgebraicGeometry.Smooth`) are stable under
  composition, include open immersions, are locally of finite presentation, and are flat.
* Tag 01W1: proper morphisms (`AlgebraicGeometry.IsProper`).
* Tags 01WH, 01WI, 01WK, 01WL: integral and finite morphisms (`AlgebraicGeometry.IsIntegralHom`,
  `AlgebraicGeometry.IsFinite`), their locality on the target, and their stability under
  composition and base change.

## References

* [Stacks Project, Chapter 29, Morphisms of Schemes][stacks-morphisms]

[stacks-morphisms]: https://stacks.math.columbia.edu/chapter/morphisms
-/

@[expose] public section

add_to_stacks 03HV AlgebraicGeometry.Flat.generalizingMap

add_to_stacks 03GO "the isomorphism of schemes"
  AlgebraicGeometry.Scheme.Hom.normalizationCoprodIso

add_to_stacks 03GO "compatibility with the morphisms to the base"
  AlgebraicGeometry.Scheme.Hom.normalizationCoprodIso_inv_coprodDesc_fromNormalization

add_to_stacks 03GO "compatibility with the dominant morphism from the first summand"
  AlgebraicGeometry.Scheme.Hom.toNormalization_inl_normalizationCoprodIso_hom

add_to_stacks 03GO "compatibility with the dominant morphism from the second summand"
  AlgebraicGeometry.Scheme.Hom.toNormalization_inr_normalizationCoprodIso_hom

add_to_stacks 03GT AlgebraicGeometry.Scheme.Hom.exists_isIso_morphismRestrict_toNormalization

add_to_stacks 03BB AlgebraicGeometry.IsClosedImmersion.iff_isFinite_and_mono

add_to_stacks 01QV "the forward implication"
  AlgebraicGeometry.IsImmersion.isImmersion_iff_exists_of_quasiCompact
add_to_stacks 01RJ AlgebraicGeometry.IsDominant
add_to_stacks 01RS "(1) a morphism defined on a dense open subscheme"
  AlgebraicGeometry.Scheme.PartialMap
add_to_stacks 01RS "(1) equivalence" AlgebraicGeometry.Scheme.PartialMap.equiv
add_to_stacks 01RS "(2) rational map" AlgebraicGeometry.Scheme.RationalMap
add_to_stacks 01RS "(3) S-rational map" AlgebraicGeometry.Scheme.RationalMap.IsOver
add_to_stacks 01RZ AlgebraicGeometry.Surjective
add_to_stacks 01S0 AlgebraicGeometry.instSurjectiveCompScheme
add_to_stacks 01S1 AlgebraicGeometry.Surjective.instIsStableUnderBaseChangeScheme
add_to_stacks 01S3 "(1) universally injective (Mathlib's definition)"
  AlgebraicGeometry.UniversallyInjective
add_to_stacks 05VE "universally injective => injective" AlgebraicGeometry.Scheme.Hom.injective
add_to_stacks 05VE "injective on points => separated" AlgebraicGeometry.isSeparated_of_injective

add_to_stacks 01S6 AlgebraicGeometry.IsAffineHom

add_to_stacks 0FCZ "being an immersion is Zariski-local on the target"
  AlgebraicGeometry.IsImmersion.instIsZariskiLocalAtTarget
add_to_stacks 0FCZ "the source-point criterion for target-local properties"
  AlgebraicGeometry.IsZariskiLocalAtTarget.of_forall_source_exists_preimage

add_to_stacks 01S7 "separated" AlgebraicGeometry.IsSeparated.of_isAffineHom
add_to_stacks 01S7 "quasi-compact" AlgebraicGeometry.instQuasiCompactOfIsAffineHom

add_to_stacks 01SC AlgebraicGeometry.instIsAffineHomCompScheme

add_to_stacks 01SE AlgebraicGeometry.IsClosedImmersion.instIsAffineHom

add_to_stacks 01SH AlgebraicGeometry.isAffineHom_of_isAffine

-- Stacks 02K8, 02V1 and 02V2: integral morphisms; composites of radicial and of open morphisms.
add_to_stacks 02GN AlgebraicGeometry.Etale.etale_comp
add_to_stacks 02GO AlgebraicGeometry.Etale.etale_isStableUnderBaseChange
add_to_stacks 02J5 AlgebraicGeometry.LocallyOfFiniteType.jacobsonSpace
add_to_stacks 02K7 "being universally closed is local on the target"
  AlgebraicGeometry.universallyClosed_isZariskiLocalAtTarget

add_to_stacks 02K8 "the affine-local property used for (1) ⇔ (2): over an affine target, \
  integral means affine source and integral map on global sections"
  AlgebraicGeometry.IsIntegralHom.hasAffineProperty
add_to_stacks 02K8 "(1) ⇔ (2), for an affine open covering, applied to the affine-local property \
  of integral morphisms" AlgebraicGeometry.HasAffineProperty.iff_of_iSup_eq_top
add_to_stacks 02K8 "(1) ⇔ (3), for an open covering, integrality being local at the target"
  AlgebraicGeometry.IsZariskiLocalAtTarget.iff_of_iSup_eq_top
add_to_stacks 02K8 "the `Moreover` clause: restriction to the preimage of an open subscheme"
  AlgebraicGeometry.IsIntegralHom.instMorphismRestrict
add_to_stacks 02V1 "composition of universally injective morphisms"
  AlgebraicGeometry.universallyInjective_isStableUnderComposition
add_to_stacks 02V1 "radicial (condition (3)) is equivalent to universally injective"
  AlgebraicGeometry.tfae_universallyInjective
add_to_stacks 02V2 "composition of open morphisms"
  AlgebraicGeometry.UniversallyOpen.instIsStableUnderCompositionSchemeTopologicallyIsOpenMap
add_to_stacks 02V2 "composition of universally open morphisms"
  AlgebraicGeometry.UniversallyOpen.instIsStableUnderCompositionScheme

add_to_stacks 01SW AlgebraicGeometry.HasRingHomProperty.isStableUnderBaseChange

add_to_stacks 01T3 "locally of finite type (also the first component of the finite type clause)"
  AlgebraicGeometry.locallyOfFiniteType_comp
add_to_stacks 01T3 "finite type: the quasi-compact component" AlgebraicGeometry.quasiCompact_comp

-- Stacks 01QP, 01QR, 01QS and 01QT: closed immersions and their ideal sheaves.
add_to_stacks 01QP "part (1), `⇐`: the factorization `Z ⟶ Z'` when `I' ≤ I`"
  AlgebraicGeometry.IsClosedImmersion.lift
add_to_stacks 01QP "part (1), `⇐`: the lift factors `i` through `i'`"
  AlgebraicGeometry.IsClosedImmersion.lift_fac
add_to_stacks 01QP "part (1), `⇒`: a factorization through `i'` forces `I' ≤ I`"
  AlgebraicGeometry.Scheme.Hom.le_ker_comp
add_to_stacks 01QP "part (1), the factor `a` is a closed immersion"
  AlgebraicGeometry.IsClosedImmersion.of_comp_isClosedImmersion
add_to_stacks 01QP "part (2), `⇐`: equal ideal sheaves give an isomorphism over `X`"
  AlgebraicGeometry.IsClosedImmersion.isIso_lift
add_to_stacks 01QP "part (2), `⇐`: a map over `X` between equal ideal sheaves is an isomorphism"
  AlgebraicGeometry.IsClosedImmersion.isIso_of_ker_eq
add_to_stacks 01QP "part (2), `⇒`: an isomorphism over `X` preserves the ideal sheaf"
  AlgebraicGeometry.Scheme.Hom.ker_comp_of_isIso
add_to_stacks 01QP "closed subschemes of `X` are anti-equivalent to ideal sheaves"
  AlgebraicGeometry.IsClosedImmersion.overEquivIdealSheafData
add_to_stacks 01QR "closed immersions are stable under base change"
  AlgebraicGeometry.IsClosedImmersion.isStableUnderBaseChange
add_to_stacks 01QS "the composition" AlgebraicGeometry.IsClosedImmersion.comp
add_to_stacks 01QT "first step: a closed immersion is affine"
  AlgebraicGeometry.IsClosedImmersion.instIsAffineHom
add_to_stacks 01QT "second step: an affine morphism is quasi-compact"
  AlgebraicGeometry.instQuasiCompactOfIsAffineHom

add_to_stacks 01T4 "locally of finite type (also the first component of the finite type clause)"
  AlgebraicGeometry.locallyOfFiniteType_isStableUnderBaseChange
add_to_stacks 01T4 "finite type: the quasi-compact component"
  AlgebraicGeometry.quasiCompact_isStableUnderBaseChange

add_to_stacks 01T5 "a closed immersion is of finite type: the locally of finite type component"
  AlgebraicGeometry.instLocallyOfFiniteTypeOfIsClosedImmersion
add_to_stacks 01T5 "an immersion is locally of finite type"
  AlgebraicGeometry.IsImmersion.instLocallyOfFiniteType

namespace Stacks.Ch29MathlibRegistrations

open CategoryTheory AlgebraicGeometry

universe u

/-- Tag 01SW for the property `affineLocally Q` of a local property `Q` of ring maps. -/
example (Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop)
    (hQ : RingHom.PropertyIsLocal Q) (hQb : RingHom.IsStableUnderBaseChange Q) :
    (affineLocally Q).IsStableUnderBaseChange :=
  haveI : HasRingHomProperty (affineLocally Q) Q := ⟨hQ, rfl⟩
  HasRingHomProperty.isStableUnderBaseChange hQb

/-- Tag 01T3, finite type: both components of "of finite type" pass to the composite. -/
example {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [LocallyOfFiniteType f] [QuasiCompact f]
    [LocallyOfFiniteType g] [QuasiCompact g] :
    LocallyOfFiniteType (f ≫ g) ∧ QuasiCompact (f ≫ g) :=
  ⟨locallyOfFiniteType_comp f g, quasiCompact_comp f g⟩

end Stacks.Ch29MathlibRegistrations

/- Smooth morphisms. -/
add_to_stacks 01VA AlgebraicGeometry.smooth_comp
add_to_stacks 01VC AlgebraicGeometry.instSmoothOfIsOpenImmersion
add_to_stacks 01VE AlgebraicGeometry.instLocallyOfFinitePresentationOfSmooth
add_to_stacks 01VF AlgebraicGeometry.instFlatOfSmooth

/- Proper morphisms. Mathlib asks for locally of finite type rather than finite type: the
quasi-compactness this leaves out follows from universal closedness. -/
add_to_stacks 01W1 AlgebraicGeometry.IsProper

/- Integral and finite morphisms. -/
add_to_stacks 01WH "(1) integral morphism" AlgebraicGeometry.IsIntegralHom
add_to_stacks 01WH "(2) finite morphism" AlgebraicGeometry.IsFinite

add_to_stacks 0A1X "the domain of definition" AlgebraicGeometry.Scheme.RationalMap.domain
add_to_stacks 0A1X "a point is in it iff some representative is defined there"
  AlgebraicGeometry.Scheme.RationalMap.mem_domain

run_cmd do
  let decl := Lean.mkIdent <| .str `AlgebraicGeometry.IsFinite <|
    "instHasAffinePropertyAndIsAffineFiniteCarrierObjOppositeOpens" ++
      "CarrierCarrierCommRingCatPresheafOpOpensTopHomAppTop"
  Lean.Elab.Command.elabCommand
    (← `(command| add_to_stacks 01WI "(1) ⟺ (2): being finite is the affine-local property \
      `X` affine with a finite ring map on global sections" $decl:ident))
add_to_stacks 01WI "(1) ⟺ (2), checked on an affine open cover of the target, applied to IsFinite"
  AlgebraicGeometry.HasAffineProperty.iff_of_openCover
add_to_stacks 01WI "(1) ⟺ (3), checked on an open cover of the target, applied to IsFinite"
  AlgebraicGeometry.IsZariskiLocalAtTarget.iff_of_openCover
add_to_stacks 01WI "moreover: the restriction f⁻¹(U) → U of a finite morphism is finite"
  AlgebraicGeometry.IsFinite.instMorphismRestrict

add_to_stacks 01WK "finite morphisms" AlgebraicGeometry.IsFinite.instCompScheme
add_to_stacks 01WK "integral morphisms" AlgebraicGeometry.IsIntegralHom.instCompScheme

add_to_stacks 01WL "finite morphisms" AlgebraicGeometry.IsFinite.instIsStableUnderBaseChangeScheme
add_to_stacks 01WL "integral morphisms"
  AlgebraicGeometry.IsIntegralHom.instIsStableUnderBaseChangeScheme

-- Any immersion is locally quasi-finite.
add_to_stacks 01TN
  "quasi-finite fibres; Mathlib's `LocallyQuasiFinite` leaves out the finite-type condition \
    built into Stacks' definition (01TD)"
  AlgebraicGeometry.instLocallyQuasiFiniteOfIsImmersion
add_to_stacks 01TN "locally of finite type, the other half of Stacks' locally quasi-finite"
  AlgebraicGeometry.IsImmersion.instLocallyOfFiniteType

-- Any open immersion is locally of finite presentation.
add_to_stacks 01TT AlgebraicGeometry.locallyOfFinitePresentation_of_isOpenImmersion

-- Locally of finite presentation implies locally of finite type. Mathlib writes finite
-- presentation / finite type as LOFP + qc + qs / LOFT + qc, so the second sentence (finite
-- presentation implies finite type) is the same instance.
add_to_stacks 01TW AlgebraicGeometry.instLocallyOfFiniteTypeOfLocallyOfFinitePresentation

-- If `S` is quasi-compact and quasi-separated and `X` is of finite presentation over `S`,
-- then `X` is quasi-compact and quasi-separated.
add_to_stacks 01TY "X is quasi-compact" AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace
add_to_stacks 01TY "X is quasi-separated" AlgebraicGeometry.quasiSeparatedSpace_of_quasiSeparated

-- Definition: open and universally open morphisms.
add_to_stacks 01U0
  "(1), open: `IsOpenMap f.base`, which Mathlib writes `topologically @IsOpenMap f`"
  IsOpenMap
add_to_stacks 01U0 "(2), universally open" AlgebraicGeometry.UniversallyOpen

-- The composition of flat morphisms is flat.
add_to_stacks 01U7 AlgebraicGeometry.Flat.comp

-- The base change of a flat morphism is flat.
add_to_stacks 01U9 AlgebraicGeometry.Flat.isStableUnderBaseChange

-- A smooth morphism is universally open.
add_to_stacks 056G
  "flat and locally of finite presentation; smooth morphisms are both (instances)"
  AlgebraicGeometry.UniversallyOpen.of_flat

add_to_stacks 07RK "(1); also the immersion part of (2)" AlgebraicGeometry.IsImmersion.of_comp
add_to_stacks 07RK "(2), quasi-compactness of Z → Y when Y → X is quasi-separated"
  AlgebraicGeometry.QuasiCompact.of_comp
add_to_stacks 07RK "(3)" AlgebraicGeometry.IsClosedImmersion.of_comp
add_to_stacks 0819 "only: f is an open immersion; Mathlib's form assumes flat, locally of finite \
  presentation and mono (a closed immersion is mono). That its image is open and closed is not \
  stated separately" AlgebraicGeometry.IsOpenImmersion.of_flat_of_mono

-- A base change of a universally injective morphism is universally injective.
add_to_stacks 0472 AlgebraicGeometry.UniversallyInjective.isStableUnderBaseChange

-- Points `x ∈ X`, `y ∈ Y` come from a point of `X ×_S Y` iff they lie over the same point of `S`.
add_to_stacks 0495 "the 'if' direction" AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback
add_to_stacks 0495
  "both directions: the points of `X ×_S Y` surject onto the set-theoretic fibre product"
  AlgebraicGeometry.Scheme.pullbackComparison_forget_surjective

end

add_to_stacks 035C "a closed immersion is finite" AlgebraicGeometry.IsFinite.instOfIsClosedImmersion
add_to_stacks 035C "a finite morphism is integral" AlgebraicGeometry.IsFinite.instIsIntegralHom

add_to_stacks 035D "part (1)" AlgebraicGeometry.IsFinite.instHasOfPostcompPropertySchemeIsSeparated
add_to_stacks 035D "part (2)"
  AlgebraicGeometry.IsIntegralHom.instHasOfPostcompPropertySchemeIsSeparated

add_to_stacks 035K "the comparison morphism from the normalization of the base change to the base \
  change of the normalization, for `f` quasi-compact and quasi-separated"
  AlgebraicGeometry.Scheme.Hom.normalizationPullback
add_to_stacks 035K "it is an isomorphism for a smooth base change, in particular for the inclusion \
  of an open `U`" AlgebraicGeometry.Scheme.Hom.instIsIsoNormalizationPullbackOfSmooth
add_to_stacks 035K "open immersions are smooth" AlgebraicGeometry.instSmoothOfIsOpenImmersion
