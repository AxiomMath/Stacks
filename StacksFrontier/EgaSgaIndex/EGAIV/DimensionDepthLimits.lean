module  -- shake: keep-all

import Mathlib.Algebra.Category.AlgCat.FilteredColimits
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Category.CommAlgCat.Monoidal
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.Ring.FinitePresentation
import Mathlib.Algebra.Colimit.DirectLimit
import Mathlib.Algebra.Colimit.Ring
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Geometrically.Basic
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Morphisms.AffineAnd
import Mathlib.AlgebraicGeometry.Morphisms.Constructors
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Spec
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.MorphismProperty.Basic
import Mathlib.CategoryTheory.MorphismProperty.Composition
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Image
import Mathlib.Data.Set.Operations
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.KummerExtension
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.FieldTheory.PurelyInseparable.AdjoinPthRoots
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.FieldTheory.SeparablyGenerated
import Mathlib.Geometry.RingedSpace.Basic
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace.ResidueField
import Mathlib.Geometry.RingedSpace.PresheafedSpace
import Mathlib.GroupTheory.MonoidLocalization.Away
import Mathlib.Order.TypeTags
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.Conductor
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Etale.Descent
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Defs
import Mathlib.RingTheory.Jacobson.Artinian
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.KrullDimension.Module
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
import Mathlib.RingTheory.LocalProperties.ProjectiveDimension
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.LocalRing.Length
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Free
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.MvPowerSeries.Restricted
import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Noetherian.Orzech
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.PowerSeries.Restricted
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RingHom.FinitePresentation
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.RingHom.Smooth
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Smooth.Locus
import Mathlib.RingTheory.Spectrum.Maximal.Defs
import Mathlib.RingTheory.Spectrum.Maximal.Topology
import Mathlib.RingTheory.Spectrum.Prime.ConstructibleSet
import Mathlib.RingTheory.Spectrum.Prime.Defs
import Mathlib.RingTheory.Spectrum.Prime.Jacobson
import Mathlib.RingTheory.Spectrum.Prime.Module
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Support
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Constructible
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Inseparable
import Mathlib.Topology.Irreducible
import Mathlib.Topology.JacobsonSpace
import Mathlib.Topology.KrullDimension
import Mathlib.Topology.LocallyClosed
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Sets.Opens
import StacksCore.RingTheory.Ideal.Operations
import StacksCore.RingTheory.Localization.Ideal
import StacksCore.Tactic.EgaSgaAttribute

/-!
# EGA IV references registered by name, §§4–10

Registrations for EGA IV §§4–10: change of base field, dimension, depth and regularity, flat
morphisms of locally noetherian preschemes, excellent rings, projective limits, constructible
properties, Jacobson preschemes. Part of `StacksFrontier.EgaSgaIndex.EGAIV`, whose module
docstring describes the index.
-/

add_to_ega "IV 4.1.2.1" "more general" topologicalKrullDim_subspace_le
add_to_ega "IV 4.3.1" "special case" IsPurelyInseparable
add_to_ega "IV 4.3.3" "partial" Algebra.IsAlgebraic.isPurelyInseparable_of_isSepClosed
add_to_ega "IV 4.3.3" IsSepClosed
add_to_ega "IV 4.3.3" isSepClosed_iff_isPurelyInseparable_algebraicClosure
add_to_ega "IV 4.3.4" "maximality" le_separableClosure
add_to_ega "IV 4.3.4" "maximality" le_separableClosure'
add_to_ega "IV 4.3.4" le_separableClosure_iff
add_to_ega "IV 4.3.4" separableClosure
add_to_ega "IV 4.3.4" "algebraic subextension" separableClosure.isAlgebraic
add_to_ega "IV 4.3.4" "partial" separableClosure.isSeparable
add_to_ega "IV 4.3.9" IsAlgClosed
add_to_ega "IV 4.3.9" IsDomain
add_to_ega "IV 4.4.1" "special case" Algebra.isReduced_of_isGeometricallyReduced
add_to_ega "IV 4.4.1" "flatness of p" AlgebraicGeometry.Flat.instFstScheme
add_to_ega "IV 4.4.1" "flatness of p" AlgebraicGeometry.Flat.instSndScheme
add_to_ega "IV 4.4.1" "surjectivity of p" AlgebraicGeometry.Surjective.instFstScheme
add_to_ega "IV 4.4.1" "surjectivity of p" AlgebraicGeometry.Surjective.instSndScheme
add_to_ega "IV 4.4.1" "partial" AlgebraicGeometry.UniversallyOpen.snd
add_to_ega "IV 4.4.1" "partial" AlgebraicGeometry.finite_irreducibleComponents_of_isNoetherian
add_to_ega "IV 4.4.1" "partial" AlgebraicGeometry.instQuasiCompactFstScheme
add_to_ega "IV 4.4.1" "more general" Continuous.connectedComponentsMap_surjective
add_to_ega "IV 4.4.1" "if X ⊗_k K is connected" Function.Surjective.connectedSpace
add_to_ega "IV 4.4.1" "partial" Function.Surjective.irreducibleSpace
add_to_ega "IV 4.4.1" "special case" Ideal.exists_isPrime_liesOver_of_faithfullyFlat
add_to_ega "IV 4.4.1" "special case" PrimeSpectrum.comap_surjective_of_faithfullyFlat
add_to_ega "IV 4.4.2" "connectedness clause" Function.Surjective.connectedSpace
add_to_ega "IV 4.4.2" "irreducibility clause" Function.Surjective.irreducibleSpace
add_to_ega "IV 4.4.2" "irreducibility clause" IsIrreducible.image
add_to_ega "IV 4.4.2" "irreducibility clause" IsIrreducible.preimage_of_isPreirreducible_fiber
add_to_ega "IV 4.4.2" "connectedness clause" Quotient.instConnectedSpace
add_to_ega "IV 4.4.2" "irreducibility clause"
  image_mem_irreducibleComponents_of_isPreirreducible_fiber
add_to_ega "IV 4.4.2" "more general" irreducibleComponentsEquivOfIsPreirreducibleFiber
add_to_ega "IV 4.4.2" "connectedness clause" preimage_connectedComponent_connected
add_to_ega "IV 4.4.2" "irreducibility clause"
  preimage_mem_irreducibleComponents_of_isPreirreducible_fiber
add_to_ega "IV 4.5.2" "partial" AlgebraicGeometry.GeometricallyConnected
add_to_ega "IV 4.5.2" "more general" AlgebraicGeometry.GeometricallyIrreducible
add_to_ega "IV 4.5.3" "partial" AlgebraicGeometry.Scheme.Opens.instCoeOut
add_to_ega "IV 4.5.5" AlgebraicGeometry.GeometricallyIrreducible
add_to_ega "IV 4.5.5" AlgebraicGeometry.GeometricallyIrreducible.iff_geometricallyIrreducible_fiber
add_to_ega "IV 4.5.6" AlgebraicGeometry.instGeometricallyConnectedSndScheme
add_to_ega "IV 4.5.6" "(ii), special case"
  AlgebraicGeometry.instGeometricallyIrreducibleFiberToSpecResidueField
add_to_ega "IV 4.5.6" AlgebraicGeometry.instGeometricallyIrreducibleFstScheme
add_to_ega "IV 4.5.6" "(ii), special case"
  AlgebraicGeometry.instGeometricallyIrreducibleMorphismRestrict
add_to_ega "IV 4.5.6" AlgebraicGeometry.instGeometricallyIrreducibleSndScheme
add_to_ega "IV 4.5.6" "more general"
  AlgebraicGeometry.instIsStableUnderBaseChangeSchemeGeometrically
add_to_ega "IV 4.5.6" AlgebraicGeometry.instIsStableUnderBaseChangeSchemeGeometricallyConnected
add_to_ega "IV 4.5.6" AlgebraicGeometry.instIsStableUnderBaseChangeSchemeGeometricallyIrreducible
add_to_ega "IV 4.5.7" "special case" AlgebraicGeometry.GeometricallyConnected.connectedSpace
add_to_ega "IV 4.5.7" "special case" AlgebraicGeometry.GeometricallyIrreducible.irreducibleSpace
add_to_ega "IV 4.5.7" "special case" AlgebraicGeometry.Scheme.Hom.isConnected_preimage
add_to_ega "IV 4.5.7" "special case" AlgebraicGeometry.Scheme.Hom.isIrreducible_preimage
-- The auto-generated instance names are longer than a line, so each identifier is assembled
-- from pieces before being handed to `add_to_ega`.
run_cmd do
  let conn := "instConnectedSpaceCarrierCarrierCommRingCatPullbackScheme" ++
    "OfGeometricallyConnectedOfUniversallyOpen"
  let irr := "instIrreducibleSpaceCarrierCarrierCommRingCatPullbackScheme" ++
    "OfGeometricallyIrreducibleOfUniversallyOpen"
  let mk (s : String) : Lean.Ident := Lean.mkIdent <| .str `AlgebraicGeometry s
  let c := mk conn
  let c1 := mk (conn ++ "_1")
  let i := mk irr
  let i1 := mk (irr ++ "_1")
  Lean.Elab.Command.elabCommand (← `(command| add_to_ega "IV 4.5.7" "connected clause" $c:ident))
  Lean.Elab.Command.elabCommand (← `(command| add_to_ega "IV 4.5.7" "connected clause" $c1:ident))
  Lean.Elab.Command.elabCommand (← `(command| add_to_ega "IV 4.5.7" $i:ident))
  Lean.Elab.Command.elabCommand (← `(command| add_to_ega "IV 4.5.7" $i1:ident))
  Lean.Elab.Command.elabCommand (← `(command| add_to_ega "IV 4.5.8" "more general" $c:ident))
  Lean.Elab.Command.elabCommand (← `(command| add_to_ega "IV 4.5.8" "more general" $c1:ident))
add_to_ega "IV 4.5.9" AlgebraicGeometry.GeometricallyIrreducible
add_to_ega "IV 4.6.1" "(c) ⇒ (d)"
  Algebra.instIsReducedTensorProductOfIsAlgebraicOfIsGeometricallyReduced
add_to_ega "IV 4.6.1" "(c) ⇒ (e)" Algebra.isReduced_of_isGeometricallyReduced
add_to_ega "IV 4.6.2" Algebra.IsGeometricallyReduced
add_to_ega "IV 4.6.2" "more general"
  AlgebraicGeometry.GeometricallyIntegral.eq_geometricallyReduced_inf_geometricallyIrreducible
add_to_ega "IV 4.6.2" "partial"
  AlgebraicGeometry.GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible
add_to_ega "IV 4.6.2" "more general" AlgebraicGeometry.GeometricallyReduced
add_to_ega "IV 4.6.2" "partial"
  AlgebraicGeometry.instGeometricallyIrreducibleOfGeometricallyIntegral
add_to_ega "IV 4.6.2" "partial" AlgebraicGeometry.instGeometricallyReducedOfGeometricallyIntegral
add_to_ega "IV 4.6.5" "(i)" AlgebraicGeometry.instGeometricallyIntegralFstScheme
add_to_ega "IV 4.6.5" "(i)" AlgebraicGeometry.instGeometricallyIntegralSndScheme
add_to_ega "IV 4.6.5" "(i)" AlgebraicGeometry.instGeometricallyReducedFstScheme
add_to_ega "IV 4.6.5" "(i)" AlgebraicGeometry.instGeometricallyReducedSndScheme
add_to_ega "IV 4.6.5" "(i)" AlgebraicGeometry.instIsStableUnderBaseChangeSchemeGeometricallyIntegral
add_to_ega "IV 4.6.5" "(i)" AlgebraicGeometry.instIsStableUnderBaseChangeSchemeGeometricallyReduced
add_to_ega "IV 4.6.7" "special case" exists_isTranscendenceBasis_and_isSeparable_of_perfectField
add_to_ega "IV 4.6.14" "special case"
  AlgebraicGeometry.GeometricallyIntegral.eq_geometricallyReduced_inf_geometricallyIrreducible
add_to_ega "IV 4.6.14" "special case"
  AlgebraicGeometry.GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible
add_to_ega "IV 4.6.17" "special case" Algebra.IsGeometricallyReduced
add_to_ega "IV 4.6.17" "special case" AlgebraicGeometry.GeometricallyReduced
add_to_ega "IV 4.6.20" "special case" AlgebraicGeometry.instGeometricallyIntegralFstScheme
add_to_ega "IV 4.6.20" "special case"
  AlgebraicGeometry.instIsStableUnderBaseChangeSchemeGeometrically
add_to_ega "IV 4.6.20" "special case"
  AlgebraicGeometry.instIsStableUnderBaseChangeSchemeGeometricallyIntegral
add_to_ega "IV 4.6.20" "special case"
  AlgebraicGeometry.instIsStableUnderBaseChangeSchemeGeometricallyReduced
add_to_ega "IV 4.7.1" "more general" IsLocalRing.length_baseChange
add_to_ega "IV 4.7.2" "more general" IsLocalRing.length_baseChange
add_to_ega "IV 4.7.3" "partial"
  AlgebraicGeometry.instIsLocallyNoetherianPullbackSchemeOfLocallyOfFiniteType
add_to_ega "IV 4.7.3" "partial"
  AlgebraicGeometry.instIsLocallyNoetherianPullbackSchemeOfLocallyOfFiniteType_1
add_to_ega "IV 4.8.1" Set
add_to_ega "IV 4.8.1" Set.powerset
add_to_ega "IV 4.8.2" "special case" AlgebraicGeometry.Scheme.IdealSheafData.comapIso_inv_subschemeι
add_to_ega "IV 4.8.2" "more general" Set.preimage
add_to_ega "IV 4.8.2" "partial" Set.preimage_comp
add_to_ega "IV 4.8.3" "special case" Submodule.baseChange_inj
add_to_ega "IV 4.8.3" "special case" Submodule.baseChange_injective
add_to_ega "IV 4.9.3" "partial" instIsPurelyInseparableAdjoinPthRoots
add_to_ega "IV 5.1.1" "more general" PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim
add_to_ega "IV 5.1.2" AlgebraicGeometry.ringKrullDim_stalk_eq_coheight
add_to_ega "IV 5.1.3" "special case" AlgebraicGeometry.ringKrullDim_stalk_eq_coheight
add_to_ega "IV 5.1.6" "partial" Ideal.exists_finset_card_eq_height_of_isNoetherianRing
add_to_ega "IV 5.1.6" "partial" Ideal.exists_spanRank_eq_and_height_eq
add_to_ega "IV 5.1.6" "partial" Ideal.finiteHeight_of_isNoetherianRing
add_to_ega "IV 5.1.6" "more general" Ideal.height_le_iff_exists_minimalPrimes
add_to_ega "IV 5.1.6" "partial"
  Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes_of_isLocalRing
add_to_ega "IV 5.1.6" "partial" instFiniteRingKrullDimOfIsLocalRing
add_to_ega "IV 5.1.6" "finiteness of dimension" ringKrullDim_le_spanFinrank_maximalIdeal
add_to_ega "IV 5.1.8" "special case" AlgebraicGeometry.RingedSpace.zeroLocus
add_to_ega "IV 5.1.8" "special case" AlgebraicGeometry.Scheme.zeroLocus
add_to_ega "IV 5.1.10" "partial" IsLocallyClosed.isOpen_preimage_val_closure
add_to_ega "IV 5.1.10" "more general" isLocallyClosed_tfae
add_to_ega "IV 5.1.11" "quasi-compact schemes" IsClosed.exists_closed_singleton
add_to_ega "IV 5.1.12" "(5.1.12.2) for F = O_X" AlgebraicGeometry.ringKrullDim_stalk_eq_coheight
add_to_ega "IV 5.1.12" Module.supportDim
add_to_ega "IV 5.1.12" "special case" Module.supportDim_eq_ringKrullDim_quotient_annihilator
add_to_ega "IV 5.2.4" "special case" AlgebraicGeometry.RingedSpace.zeroLocus
add_to_ega "IV 5.2.4" "special case" AlgebraicGeometry.Scheme.zeroLocus
add_to_ega "IV 5.2.5" "more general" Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
add_to_ega "IV 5.2.5" "dim Spec(B) = 1" IsDiscreteValuationRing.ringKrullDim_eq_one
add_to_ega "IV 5.2.5" "more general" Polynomial.height_eq_height_add_one
add_to_ega "IV 5.3.1.3" "special case"
  AlgebraicGeometry.LocallyRingedSpace.evaluation_ne_zero_iff_mem_basicOpen
add_to_ega "IV 5.3.1.3" "special case"
  AlgebraicGeometry.LocallyRingedSpace.Γevaluation_eq_zero_iff_notMem_basicOpen
add_to_ega "IV 5.3.1.3" "special case"
  AlgebraicGeometry.LocallyRingedSpace.Γevaluation_ne_zero_iff_mem_basicOpen
add_to_ega "IV 5.3.1.3" "special case" AlgebraicGeometry.RingedSpace.zeroLocus
add_to_ega "IV 5.3.1.3" "special case" AlgebraicGeometry.Scheme.affineBasicOpen
add_to_ega "IV 5.3.1.3" "special case" AlgebraicGeometry.Scheme.basicOpen
add_to_ega "IV 5.3.1.3" "special case"
  AlgebraicGeometry.Scheme.evaluation_eq_zero_iff_notMem_basicOpen
add_to_ega "IV 5.3.1.3" "special case" AlgebraicGeometry.Scheme.evaluation_ne_zero_iff_mem_basicOpen
add_to_ega "IV 5.3.1.3" "special case" AlgebraicGeometry.Scheme.zeroLocus
add_to_ega "IV 5.4.2" "special case" AlgebraicGeometry.IsClosedImmersion.eq_isFinite_inf_mono
add_to_ega "IV 5.4.2" "special case" AlgebraicGeometry.IsClosedImmersion.iff_isFinite_and_mono
add_to_ega "IV 5.4.2" "more general" AlgebraicGeometry.IsFinite.eq_isProper_inf_isAffineHom
add_to_ega "IV 5.4.2" "more general" AlgebraicGeometry.IsFinite.eq_proper_inf_locallyQuasiFinite
add_to_ega "IV 5.4.2" "more general" AlgebraicGeometry.IsFinite.iff_isProper_and_locallyQuasiFinite
add_to_ega "IV 5.4.2" "more general" AlgebraicGeometry.IsIntegralHom.instUniversallyClosed
add_to_ega "IV 5.4.2" "more general" AlgebraicGeometry.IsProper.instOfIsFinite
add_to_ega "IV 5.4.2" "more general" AlgebraicGeometry.instIsProperOfIsFinite
add_to_ega "IV 5.5.1" "special case" ringKrullDim_le_ringKrullDim_quotSMulTop_succ
add_to_ega "IV 5.5.3" "primality of p' = pA[T]" Ideal.isPrime_map_C_iff_isPrime
add_to_ega "IV 5.5.3" "primality of p' = pA[T]" Ideal.isPrime_map_C_of_isPrime
add_to_ega "IV 5.5.3" Ideal.map
add_to_ega "IV 5.5.3" "special case" Polynomial.height_eq_height_add_one
add_to_ega "IV 5.5.4" MvPolynomial.ringKrullDim_of_isNoetherianRing
add_to_ega "IV 5.5.4" "r = 1" Polynomial.ringKrullDim_of_isNoetherianRing
add_to_ega "IV 5.5.4" "partial" ringKrullDim_add_enatCard_le_ringKrullDim_mvPolynomial
add_to_ega "IV 5.5.4" "partial" ringKrullDim_add_natCard_le_ringKrullDim_mvPolynomial
add_to_ega "IV 5.5.4" "partial" ringKrullDim_succ_le_ringKrullDim_polynomial
add_to_ega "IV 5.5.5" AlgebraicGeometry.AffineSpace.over_over
add_to_ega "IV 5.5.5" "affine base" MvPolynomial.ringKrullDim_of_isNoetherianRing
add_to_ega "IV 5.5.5" "affine base, r = 1" Polynomial.ringKrullDim_of_isNoetherianRing
add_to_ega "IV 5.5.5" "affine lower bound" ringKrullDim_add_enatCard_le_ringKrullDim_mvPolynomial
add_to_ega "IV 5.5.5" "affine lower bound" ringKrullDim_add_natCard_le_ringKrullDim_mvPolynomial
add_to_ega "IV 5.5.6" "q maximal in A[T]" Polynomial.height_eq_height_add_one
add_to_ega "IV 5.5.7" Algebra.trdeg
add_to_ega "IV 5.6.11" "partial" IsLocalization.integralClosure
add_to_ega "IV 5.6.11" Localization.AtPrime
add_to_ega "IV 5.6.11" Module.annihilator
add_to_ega "IV 5.6.11" RingHom.eqLocus
add_to_ega "IV 5.6.11" Submodule.annihilator
add_to_ega "IV 5.6.11" Submodule.colon
add_to_ega "IV 5.6.11" conductor
add_to_ega "IV 5.6.11.1" Module.annihilator
add_to_ega "IV 5.6.11.1" Submodule.colon
add_to_ega "IV 5.6.11.1" conductor
add_to_ega "IV 5.7.9" "special case" Algebra.QuasiFinite.finite_primesOver
add_to_ega "IV 5.7.9" "special case" IsDedekindDomain.instFintypeElemIdealPrimesOver
add_to_ega "IV 5.7.9" "special case" IsDedekindDomain.primesOver_finite
add_to_ega "IV 5.7.9" "special case" primesOver_finite
add_to_ega "IV 5.8.4" "special case"
  AlgebraicGeometry.isField_stalk_of_closure_mem_irreducibleComponents
add_to_ega "IV 5.8.4" "partial" Ring.KrullDimLE.isField_of_isReduced
add_to_ega "IV 5.8.6" "(i), special case" instIsRegularRingOfIsDedekindDomain
add_to_ega "IV 5.9.1" "forward direction" StableUnderSpecialization.Union_eq
add_to_ega "IV 5.9.1" "partial" Union_closure_singleton_eq_iff
add_to_ega "IV 5.9.1" "partial" stableUnderSpecialization_iff_Union_eq
add_to_ega "IV 5.9.4" "more general" StableUnderSpecialization.preimage
add_to_ega "IV 5.9.6" AlgebraicGeometry.instCanonicallyOverSpecStalkCommRingCatPresheaf
add_to_ega "IV 5.9.6" AlgebraicGeometry.instOverSpecStalkCommRingCatPresheaf
add_to_ega "IV 5.9.12" "(ii), special case" LocalizedModule.subsingleton_iff_disjoint
add_to_ega "IV 5.9.12" "(ii), special case" LocalizedModule.subsingleton_iff_support_subset
add_to_ega "IV 5.11.7" "C/r is a domain" Ideal.Quotient.isDomain
add_to_ega "IV 5.11.7" "C/r is a domain" Ideal.Quotient.isDomain_iff_prime
add_to_ega "IV 5.11.7" "A/p embeds in C/r" Ideal.algebraMap_quotient_injective
add_to_ega "IV 5.11.7" "partial"
  IsLocalization.instQuotientIdealAlgebraMapSubmonoidMapRingHomAlgebraMap
add_to_ega "IV 5.12.8" "height(p) ≤ 1" Ideal.height_le_height_add_one_of_mem
add_to_ega "IV 5.12.8" "height(p) ≤ 1" Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes
add_to_ega "IV 5.12.8" "more general" Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
add_to_ega "IV 5.12.8" "height(p) ≤ 1" Ideal.height_span_singleton_le_one
add_to_ega "IV 5.12.8" "1 ≤ height(p)" Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors
add_to_ega "IV 5.12.10" "more general" IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
add_to_ega "IV 5.13.3" "(i), special case" Field.DirectLimit.field
add_to_ega "IV 5.13.5" "more general" isReduced_ofLocalizationMaximal
add_to_ega "IV 5.13.6" Ring.DirectLimit
add_to_ega "IV 6.1.3" Module.Finite
add_to_ega "IV 6.1.3" Module.Flat
add_to_ega "IV 6.1.3" Module.support
add_to_ega "IV 6.2.1" "(i), special case" ModuleCat.localizedModule_hasProjectiveDimensionLE
add_to_ega "IV 6.2.1" "(i), localization case"
  ModuleCat.projectiveDimension_le_projectiveDimension_of_isLocalizedModule
add_to_ega "IV 6.6.1" "(i): flatness of h = g∘f" AlgebraicGeometry.Flat.instIsMultiplicativeScheme
add_to_ega "IV 6.6.1" "(i): flatness of h = g∘f"
  AlgebraicGeometry.Flat.instIsStableUnderCompositionScheme
add_to_ega "IV 6.6.1" "(i), special case" RingHom.Flat.stableUnderComposition
add_to_ega "IV 6.7.1" "partial"
  AlgebraicGeometry.instIsLocallyNoetherianPullbackSchemeOfLocallyOfFiniteType
add_to_ega "IV 6.7.1" "special case"
  AlgebraicGeometry.instIsLocallyNoetherianPullbackSchemeOfLocallyOfFiniteType_1
add_to_ega "IV 6.7.5" "special case" WeierstrassCurve.Affine.CoordinateRing.instIsDomain
add_to_ega "IV 6.7.5" "partial" X_pow_sub_C_irreducible_iff_of_prime
add_to_ega "IV 6.7.5" "special case" X_pow_sub_C_irreducible_of_odd
add_to_ega "IV 6.7.5" "partial" X_pow_sub_C_irreducible_of_prime
add_to_ega "IV 6.7.5" "special case" X_pow_sub_C_irreducible_of_prime_pow
add_to_ega "IV 6.7.5" "Affine case" instIsRegularRingOfIsDedekindDomain
add_to_ega "IV 6.7.6" Algebra.IsGeometricallyReduced
add_to_ega "IV 6.8.2" "special case" RingHom.Smooth.isStableUnderBaseChange
add_to_ega "IV 6.8.3" "(i), special case" Algebra.Smooth.comp
add_to_ega "IV 6.8.3" "(iii), special case" Algebra.Smooth.of_smooth_tensorProduct_of_faithfullyFlat
add_to_ega "IV 6.8.3" "more general"
  AlgebraicGeometry.instDescendsAlongSchemeSmoothMinMorphismPropertySurjectiveFlatQuasiCompact
add_to_ega "IV 6.8.3" "more general" AlgebraicGeometry.instIsStableUnderCompositionSchemeSmooth
add_to_ega "IV 6.8.3" "special case" AlgebraicGeometry.smoothOfRelativeDimension_comp
add_to_ega "IV 6.8.3" "(iii), special case" RingHom.Smooth.codescendsAlong_faithfullyFlat
add_to_ega "IV 6.8.3" "(iii), special case" RingHom.Smooth.isStableUnderBaseChange
add_to_ega "IV 6.8.3" "special case" RingHom.Smooth.stableUnderComposition
add_to_ega "IV 6.8.6" "special case" AlgebraicGeometry.Scheme.Hom.smoothLocus_eq_top
add_to_ega "IV 6.8.6" "partial" AlgebraicGeometry.Scheme.Hom.smoothLocus_eq_top_iff
add_to_ega "IV 6.8.7" "special case" Algebra.isOpen_smoothLocus
add_to_ega "IV 6.8.7" "more general" AlgebraicGeometry.Scheme.Hom.isOpen_smoothLocus
add_to_ega "IV 6.8.8" "special case" Algebra.isOpen_smoothLocus
add_to_ega "IV 6.8.8" "partial" AlgebraicGeometry.Scheme.Hom.isOpen_smoothLocus
add_to_ega "IV 6.10.3" IsClopen
add_to_ega "IV 6.10.3" Module.support
add_to_ega "IV 6.11.6.1" "necessity" IsOpen.stableUnderGeneralization
add_to_ega "IV 6.11.9" "special case" exists_integral_inj_algHom_of_fg
add_to_ega "IV 6.13.4" "partial"
  AlgebraicGeometry.isField_stalk_of_closure_mem_irreducibleComponents
add_to_ega "IV 6.14.1.1" "(ii), special case" IsIntegrallyClosed.iInf
add_to_ega "IV 6.14.1.1" "(ii), special case" IsIntegrallyClosed.of_iInf_eq_bot
add_to_ega "IV 6.15.3" AlgebraicGeometry.Scheme.Hom.fiber
add_to_ega "IV 6.15.3" AlgebraicGeometry.Scheme.Hom.fiberOverSpecResidueField
add_to_ega "IV 6.15.3" AlgebraicGeometry.Scheme.Hom.fiberToSpecResidueField
add_to_ega "IV 6.15.3" AlgebraicGeometry.Scheme.fromSpecResidueField
add_to_ega "IV 6.15.5" "special case" Algebra.IsIntegral.comap_surjective
add_to_ega "IV 6.15.5" "more general"
  AlgebraicGeometry.Surjective.of_universallyClosed_of_isDominant
add_to_ega "IV 6.15.8" "forward implication" Algebra.IsAlgebraic.isPurelyInseparable_of_isSepClosed
add_to_ega "IV 6.15.8" IsSepClosed
add_to_ega "IV 6.15.8" isSepClosed_iff_isPurelyInseparable_algebraicClosure
add_to_ega "IV 6.15.9" isSepClosed_iff_isPurelyInseparable_algebraicClosure
add_to_ega "IV 6.15.10" "special case"
  AlgebraicGeometry.GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian
add_to_ega "IV 6.15.10" "special case"
  AlgebraicGeometry.instIsReducedPullbackSchemeOfGeometricallyReducedOfFlatOfIsLocallyNoetherian
add_to_ega "IV 6.15.10" "special case"
  AlgebraicGeometry.instIsReducedPullbackSchemeOfGeometricallyReducedOfFlatOfIsLocallyNoetherian_1
add_to_ega "IV 7.2.4" AdicCompletion
add_to_ega "IV 7.2.4" Ideal.height
add_to_ega "IV 7.2.4" Localization.AtPrime
add_to_ega "IV 7.2.4" Module.Finite
add_to_ega "IV 7.3.1" "Stalk clause" AlgebraicGeometry.stalkwise
add_to_ega "IV 7.3.5" "partial" AlgebraicGeometry.Flat.instFstScheme
add_to_ega "IV 7.3.5" "partial" AlgebraicGeometry.Flat.instIsMultiplicativeScheme
add_to_ega "IV 7.3.5" "partial" AlgebraicGeometry.Flat.instIsStableUnderCompositionScheme
add_to_ega "IV 7.3.5" "partial" AlgebraicGeometry.Flat.instSndScheme
add_to_ega "IV 7.3.5" CategoryTheory.MorphismProperty.IsStableUnderComposition
add_to_ega "IV 7.3.5" CategoryTheory.MorphismProperty.RespectsRight
add_to_ega "IV 7.3.5" "special case" RingHom.Flat.stableUnderComposition
add_to_ega "IV 7.3.8" "partial" AlgebraicGeometry.instGeometricallyReducedFstScheme
add_to_ega "IV 7.3.8" "(vi)"
  AlgebraicGeometry.instIsReducedPullbackSchemeOfGeometricallyReducedOfFlatOfIsLocallyNoetherian
add_to_ega "IV 7.3.8" "(vi)"
  AlgebraicGeometry.instIsReducedPullbackSchemeOfGeometricallyReducedOfFlatOfIsLocallyNoetherian_1
add_to_ega "IV 7.3.8" "partial" AlgebraicGeometry.instIsStableUnderBaseChangeSchemeGeometrically
add_to_ega "IV 7.3.8" "partial"
  AlgebraicGeometry.instIsStableUnderBaseChangeSchemeGeometricallyReduced
add_to_ega "IV 7.3.9" "(vi), special case" Algebra.isReduced_of_isGeometricallyReduced
add_to_ega "IV 7.3.9" "more general" AlgebraicGeometry.instIsReducedFiberOfGeometricallyReduced
add_to_ega "IV 7.3.9" "more general"
  AlgebraicGeometry.instIsReducedPullbackSchemeOfGeometricallyReducedOfFlatOfIsLocallyNoetherian
add_to_ega "IV 7.3.13" "more general" Ideal.Fiber
add_to_ega "IV 7.3.13" "partial" PrimeSpectrum.preimageEquivFiber
add_to_ega "IV 7.3.13" "partial" PrimeSpectrum.preimageHomeomorphFiber
add_to_ega "IV 7.3.19" "partial" AdicCompletion.maximalIdeal_eq_map
add_to_ega "IV 7.3.19" "partial" AdicCompletion.maximalIdeal_eq_map_of_fg
add_to_ega "IV 7.3.19" IsArtinianRing.equivPi
add_to_ega "IV 7.3.19" "special case" IsArtinianRing.isField_of_isDomain
add_to_ega "IV 7.3.19" "special case" IsArtinianRing.isField_of_isReduced_of_isLocalRing
add_to_ega "IV 7.3.19" "more general" IsArtinianRing.quotNilradicalEquivPi
add_to_ega "IV 7.3.19" "more general" IsArtinianRing.quotNilradicalPowEquivPi
add_to_ega "IV 7.3.19" "(iv), special case" IsLocalRing.Ring.KrullDimLE.eq_bot_or_eq_top
add_to_ega "IV 7.4.8" "more general" MvPowerSeries.IsRestricted.subring
add_to_ega "IV 7.4.8" "special case" PowerSeries.IsRestricted.subring
add_to_ega "IV 7.5.3" IsDomain
add_to_ega "IV 7.5.3" IsReduced
add_to_ega "IV 7.5.3" IsRegularLocalRing
add_to_ega "IV 7.5.3" IsRegularRing
add_to_ega "IV 7.8.3" "(viii)" IsDedekindDomain.HeightOneSpectrum.iInf_localization_eq_bot
add_to_ega "IV 7.8.3" "(vi), second clause" IsIntegralClosure.finite
add_to_ega "IV 7.8.3" "(vi), second clause" IsIntegralClosure.isNoetherian
add_to_ega "IV 7.9.1" "more general" AlgebraicGeometry.IsFinite.eq_isProper_inf_isAffineHom
add_to_ega "IV 7.9.1" "more general" AlgebraicGeometry.IsFinite.eq_proper_inf_locallyQuasiFinite
add_to_ega "IV 7.9.1" "more general" AlgebraicGeometry.IsFinite.iff_isProper_and_locallyQuasiFinite
add_to_ega "IV 7.9.1" AlgebraicGeometry.IsProper.instOfIsFinite
add_to_ega "IV 7.9.1" AlgebraicGeometry.instIsProperOfIsFinite
add_to_ega "IV 7.9.1" "DVR classification" IsDiscreteValuationRing.TFAE
add_to_ega "IV 7.9.1" "DVR implies regular"
  IsRegularLocalRing.instOfIsLocalRingOfIsDomainOfIsPrincipalIdealRing
add_to_ega "IV 7.9.1" "more general" instIsRegularRingOfIsDedekindDomain
add_to_ega "IV 7.9.10" "special case"
  PrimeSpectrum.isOpen_of_stableUnderGeneralization_of_isConstructible
add_to_ega "IV 8.1.2" "Affine case" AlgebraicGeometry.functionField_isFractionRing_of_affine
add_to_ega "IV 8.1.2" "partial" AlgebraicGeometry.functionField_isFractionRing_of_isAffineOpen
add_to_ega "IV 8.1.2" "partial" AlgebraicGeometry.instFieldCarrierFunctionField
add_to_ega "IV 8.1.2" "partial" AlgebraicGeometry.isField_stalk_of_closure_mem_irreducibleComponents
add_to_ega "IV 8.2.1" "special case" CommRingCat.FilteredColimits.colimit
add_to_ega "IV 8.2.1" "special case" CommRingCat.FilteredColimits.colimitCommRing
add_to_ega "IV 8.2.1" "special case" CommSemiRingCat.FilteredColimits.colimitCommSemiring
add_to_ega "IV 8.2.1" "partial" DirectLimit.Algebra.hom_ext
add_to_ega "IV 8.2.1" "partial" DirectLimit.Algebra.hom_ext_iff
add_to_ega "IV 8.2.1" "special case" DirectLimit.Algebra.of
add_to_ega "IV 8.2.1" "special case" DirectLimit.instAlgebra
add_to_ega "IV 8.2.1" "special case" RingCat.FilteredColimits.colimitRing
add_to_ega "IV 8.2.1" "partial" instPreservesFilteredColimitsAlgCatForgetAlgHomCarrier
add_to_ega "IV 8.2.3" "special case" AlgebraicGeometry.preservesLimitsOfSize_algSpec
add_to_ega "IV 8.2.7" "special case" AlgebraicGeometry.isPullback_SpecMap_pushout
add_to_ega "IV 8.2.7" "special case" CommAlgCat.binaryCofanIsColimit
add_to_ega "IV 8.2.7" "special case" CommRingCat.Colimits.hasColimits_commRingCat
add_to_ega "IV 8.2.7" "special case" CommRingCat.isPushout_tensorProduct
add_to_ega "IV 8.2.7" "special case" CommRingCat.pushoutCoconeIsColimit
add_to_ega "IV 8.2.7" "special case" instHasColimitsCommAlgCat
add_to_ega "IV 8.2.8" AlgebraicGeometry.PresheafedSpace.Hom.base
add_to_ega "IV 8.2.8" "partial" AlgebraicGeometry.Scheme.Hom.continuous
add_to_ega "IV 8.2.11" "more general" AlgebraicGeometry.exists_preimage_eq
add_to_ega "IV 8.3.6" "Nontrivial direction" AlgebraicGeometry.Scheme.nonempty_of_isLimit
add_to_ega "IV 8.3.9" "more general" AlgebraicGeometry.Scheme.Hom.isConstructible_preimage
add_to_ega "IV 8.3.9" Set
add_to_ega "IV 8.3.9" Topology.IsConstructible
add_to_ega "IV 8.5.2.1" "Setup clause" DirectLimit.Algebra.of
add_to_ega "IV 8.5.2.1" "Setup clause" DirectLimit.instAlgebra
add_to_ega "IV 8.5.4" "special case" AlgebraicGeometry.AffineScheme.Γ_preservesLimits
add_to_ega "IV 8.5.4" "partial" AlgebraicGeometry.exists_appTop_π_eq_of_isAffine_of_isLimit
add_to_ega "IV 8.5.4" "partial" AlgebraicGeometry.exists_appTop_π_eq_of_isLimit
add_to_ega "IV 8.5.4" "partial" AlgebraicGeometry.exists_app_map_eq_map_of_isLimit
-- The auto-generated instance name is longer than a line, so its identifier is assembled
-- from two pieces before being handed to `add_to_ega`.
run_cmd do
  let decl := Lean.mkIdent <| .str `AlgebraicGeometry <|
    "instPreservesLimitSchemeOppositeCommRingCatRightOpΓOfIsAffineHomMap" ++
      "OfCompactSpaceOfQuasiSeparatedSpaceCarrierCarrierObj"
  Lean.Elab.Command.elabCommand
    (← `(command| add_to_ega "IV 8.5.4" "structure sheaf" $decl:ident))
add_to_ega "IV 8.5.4" "structure sheaf" AlgebraicGeometry.nonempty_isColimit_Γ_mapCocone
add_to_ega "IV 8.5.4" "special case" AlgebraicGeometry.preservesColimit_Γ
add_to_ega "IV 8.5.5" "special case" Module.FinitePresentation.exists_free_localizedModule_powers
add_to_ega "IV 8.6.2" "special case" Algebra.FinitePresentation.baseChange
add_to_ega "IV 8.6.2" "special case" AlgebraicGeometry.affineAnd_isStableUnderBaseChange
add_to_ega "IV 8.6.2" "partial" AlgebraicGeometry.instLocallyOfFinitePresentationFstScheme
add_to_ega "IV 8.6.2" "partial" AlgebraicGeometry.instLocallyOfFinitePresentationSndScheme
add_to_ega "IV 8.6.2" "special case" RingHom.finitePresentation_isStableUnderBaseChange
add_to_ega "IV 8.8.2" "more general"
  AlgebraicGeometry.Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType
add_to_ega "IV 8.8.2" "more general"
  AlgebraicGeometry.Scheme.exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType
add_to_ega "IV 8.8.2" "partial" RingHom.EssFiniteType.exists_comp_map_eq_of_isColimit
add_to_ega "IV 8.8.2.3" CommRingCat.isFinitelyPresentable_hom
add_to_ega "IV 8.8.2.3" CommRingCat.isFinitelyPresentable_under
add_to_ega "IV 8.8.2.3" "more general" CommRingCat.preservesColimit_coyoneda_of_finitePresentation
add_to_ega "IV 8.8.2.3" "more general" CommRingCat.preservesFilteredColimits_coyoneda
add_to_ega "IV 8.8.2.3" "more general" RingHom.EssFiniteType.exists_comp_map_eq_of_isColimit
add_to_ega "IV 8.8.2.3" "surjectivity" RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit
add_to_ega "IV 8.8.2.4" "special case" AlgHom.FiniteType.of_finitePresentation
add_to_ega "IV 8.8.2.4" "special case" Algebra.FiniteType.of_finitePresentation
add_to_ega "IV 8.8.2.4" "partial"
  AlgebraicGeometry.instLocallyOfFiniteTypeOfLocallyOfFinitePresentation
add_to_ega "IV 8.8.2.4" "special case" RingHom.FiniteType.of_finitePresentation
add_to_ega "IV 8.8.3" "partial"
  AlgebraicGeometry.Scheme.exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType
add_to_ega "IV 8.9.3" "Noetherian modules" IsNoetherian.bijective_of_surjective_endomorphism
add_to_ega "IV 8.9.3" "special case" IsNoetherian.injective_of_surjective_endomorphism
add_to_ega "IV 8.10.2" AlgebraicGeometry.AffineSpace
add_to_ega "IV 8.10.2" "partial" AlgebraicGeometry.AffineSpace.isPullback_map
add_to_ega "IV 8.10.2" AlgebraicGeometry.AffineSpace.map
add_to_ega "IV 8.10.2" "special case" AlgebraicGeometry.AffineSpace.mapSpecMap
add_to_ega "IV 8.10.2" "special case" AlgebraicGeometry.AffineSpace.map_SpecMap
add_to_ega "IV 8.10.2" AlgebraicGeometry.AffineSpace.over
add_to_ega "IV 8.10.5" "(ix), special case" AlgebraicGeometry.Scheme.exists_isQuasiAffine_of_isLimit
add_to_ega "IV 8.11.1" "more general" AlgebraicGeometry.IsFinite.eq_proper_inf_locallyQuasiFinite
add_to_ega "IV 8.11.1" "more general" AlgebraicGeometry.IsFinite.iff_isProper_and_locallyQuasiFinite
add_to_ega "IV 8.11.1" "more general" AlgebraicGeometry.IsFinite.of_isProper_of_locallyQuasiFinite
add_to_ega "IV 8.11.1" "partial"
  AlgebraicGeometry.exists_isFinite_morphismRestrict_of_finite_preimage_singleton
add_to_ega "IV 8.11.4" "Â is a local ring"
  AdicCompletion.instIsLocalRingMaximalIdealOfIsNoetherianRing
add_to_ega "IV 8.11.4" "Properness" AlgebraicGeometry.IsProper.instIsZariskiLocalAtTarget
add_to_ega "IV 8.11.5" "special case" AlgebraicGeometry.IsClosedImmersion.eq_isFinite_inf_mono
add_to_ega "IV 8.11.5" "more general"
  AlgebraicGeometry.IsClosedImmersion.eq_proper_inf_monomorphisms
add_to_ega "IV 8.11.5" "special case" AlgebraicGeometry.IsClosedImmersion.iff_isFinite_and_mono
add_to_ega "IV 8.11.5" "more general" AlgebraicGeometry.IsClosedImmersion.iff_isProper_and_mono
add_to_ega "IV 8.11.5.1" AlgebraicGeometry.Scheme.Hom.fiber
add_to_ega "IV 8.11.5.1" AlgebraicGeometry.Scheme.Hom.fiberOverSpecResidueField
add_to_ega "IV 8.11.5.1" AlgebraicGeometry.Scheme.Hom.fiberToSpecResidueField
add_to_ega "IV 8.12.1" "more general"
  AlgebraicGeometry.IsImmersion.instIsOpenImmersionToImageOfQuasiCompact
add_to_ega "IV 8.12.2" "more general" AlgebraicGeometry.IsImmersion.of_comp
add_to_ega "IV 8.12.3" "special case" mem_integralClosure_iff_mem_fg
add_to_ega "IV 8.12.11" "special case" IsIntegralClosure
add_to_ega "IV 8.13.1" "injectivity, partial"
  AlgebraicGeometry.Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType
add_to_ega "IV 8.13.1" "more general"
  AlgebraicGeometry.Scheme.exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType
add_to_ega "IV 8.13.1" "more general" AlgebraicGeometry.Scheme.preservesColimit_yoneda
add_to_ega "IV 8.13.5" "partial" AlgebraicGeometry.IsLocallyNoetherian.quasiSeparatedSpace
add_to_ega "IV 8.14.2" "a ⇒ b, a ⇒ c, a ⇒ c′" AlgebraicGeometry.Scheme.preservesColimit_yoneda
add_to_ega "IV 8.14.2" CategoryTheory.yoneda
add_to_ega "IV 8.14.2.2" "sufficiency" CommRingCat.isFinitelyPresentable_under
add_to_ega "IV 8.14.2.2" "partial" CommRingCat.preservesColimit_coyoneda_of_finitePresentation
add_to_ega "IV 8.14.2.2" "sufficiency" CommRingCat.preservesFilteredColimits_coyoneda
add_to_ega "IV 8.14.2.2" "partial" RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit
add_to_ega "IV 9.2.2" "partial" AlgebraicGeometry.Scheme.Hom.isConstructible_preimage
add_to_ega "IV 9.2.3" "special case" AlgebraicGeometry.Scheme.Hom.isLocallyConstructible_image
add_to_ega "IV 9.2.6" WithBot
add_to_ega "IV 9.4.1" AlgebraicGeometry.Scheme.Hom.fiber
add_to_ega "IV 9.4.1" AlgebraicGeometry.Scheme.Hom.fiberHomeo
add_to_ega "IV 9.4.1" AlgebraicGeometry.Scheme.Hom.fiberι
add_to_ega "IV 9.4.1" "image of p equals f⁻¹(s)" AlgebraicGeometry.Scheme.Hom.range_fiberι
add_to_ega "IV 9.4.1" AlgebraicGeometry.instCanonicallyOverFiber
add_to_ega "IV 9.4.9" CategoryTheory.Limits.pullback
add_to_ega "IV 9.5.1" "more general" AlgebraicGeometry.Scheme.Hom.isLocallyConstructible_image
add_to_ega "IV 9.5.7" "B is a Dedekind ring" IsIntegralClosure.isDedekindDomain
add_to_ega "IV 9.5.7" "partial" IsIntegralClosure.isLocalization_of_isSeparable
add_to_ega "IV 9.5.7" "B is a Dedekind ring" integralClosure.isDedekindDomain
add_to_ega "IV 9.5.7" "B is a Dedekind ring" integralClosure.isDedekindDomain_fractionRing
add_to_ega "IV 10.1.1" IsClosed
add_to_ega "IV 10.1.1" IsLocallyClosed
add_to_ega "IV 10.1.1" IsOpen
add_to_ega "IV 10.1.1" TopologicalSpace.Opens
add_to_ega "IV 10.1.1" Topology.IsConstructible
add_to_ega "IV 10.1.1" Topology.IsLocallyConstructible
add_to_ega "IV 10.1.2" "implication a′ ⇒ a" nonempty_inter_closedPoints
add_to_ega "IV 10.2.7" "partial" Topology.IsInducing.isLocallyClosed_iff
add_to_ega "IV 10.3.1" JacobsonSpace
add_to_ega "IV 10.3.1" "Forward direction" JacobsonSpace.closure_inter_closedPoints_eq_closure
add_to_ega "IV 10.3.1" "special case" isClosed_singleton_of_isLocallyClosed_singleton
add_to_ega "IV 10.3.1" jacobsonSpace_iff_locallyClosed
add_to_ega "IV 10.3.1" "Forward direction" nonempty_inter_closedPoints
add_to_ega "IV 10.3.2" "special case" JacobsonSpace.of_isClosedEmbedding
add_to_ega "IV 10.3.2" "special case" TopologicalSpace.IsOpenCover.jacobsonSpace_iff
add_to_ega "IV 10.3.3" TopologicalSpace.IsOpenCover.jacobsonSpace_iff
add_to_ega "IV 10.4.1" JacobsonSpace
add_to_ega "IV 10.4.2" "special case"
  AlgebraicGeometry.instJacobsonSpaceCarrierCarrierCommRingCatSpecOfIsJacobsonRingCarrier
add_to_ega "IV 10.4.2" "special case"
  AlgebraicGeometry.instJacobsonSpaceCarrierCarrierCommRingCatSpecOfOfIsJacobsonRing
add_to_ega "IV 10.4.2" "special case" PrimeSpectrum.instJacobsonSpaceOfIsJacobsonRing
add_to_ega "IV 10.4.3" "partial" IsArtinianRing.isPrime_iff_isMaximal
add_to_ega "IV 10.4.3" IsArtinianRing.jacobson_eq_radical
add_to_ega "IV 10.4.3" "Closed subpreschemes" JacobsonSpace.of_isClosedEmbedding
add_to_ega "IV 10.4.3" instIsJacobsonRingOfIsArtinianRing
add_to_ega "IV 10.4.3" "more general" instIsJacobsonRingOfKrullDimLEOfNatNat
add_to_ega "IV 10.4.3" "partial" isArtinianRing_iff_isNoetherianRing_krullDimLE_zero
add_to_ega "IV 10.4.3" "special case" isJacobsonRing_localization
add_to_ega "IV 10.4.3" "special case" isJacobsonRing_quotient
add_to_ega "IV 10.4.4" Algebra.FiniteType
add_to_ega "IV 10.4.4" IsDomain
add_to_ega "IV 10.4.4" IsFractionRing
add_to_ega "IV 10.4.4" Localization.Away
add_to_ega "IV 10.4.4" PrimeSpectrum
add_to_ega "IV 10.4.5" "a⇒b′" Module.finite_of_isArtinianRing
add_to_ega "IV 10.4.5" "a⇒b′" Module.finite_of_isSemisimpleRing
add_to_ega "IV 10.4.5" "a⇒b′" RingHom.finite_iff_finiteType_of_isJacobsonRing
add_to_ega "IV 10.4.5" "special case" RingHom.finite_of_algHom_finiteType_of_isJacobsonRing
add_to_ega "IV 10.4.5" "special case" finite_of_algHom_finiteType_of_isJacobsonRing
add_to_ega "IV 10.4.5.1" "necessity" isClosed_singleton_of_isLocallyClosed_singleton
add_to_ega "IV 10.4.6" "partial"
  AlgebraicGeometry.instJacobsonSpaceCarrierCarrierCommRingCatFiberOfLocallyOfFiniteType
add_to_ega "IV 10.4.6" "B = A[X], special case" Polynomial.instIsJacobsonRing
add_to_ega "IV 10.4.6" "B = A[X], special case"
  Polynomial.isJacobsonRing_polynomial_of_isJacobsonRing
add_to_ega "IV 10.4.6" "B = A[X]" Polynomial.isMaximal_comap_C_of_isJacobsonRing
add_to_ega "IV 10.4.6" RingHom.FiniteType.isJacobsonRing
add_to_ega "IV 10.4.6" "quotient algebras" isJacobsonRing_of_surjective
add_to_ega "IV 10.4.7" AlgebraicGeometry.Scheme.Hom.closePoints_subset_preimage_closedPoints
add_to_ega "IV 10.4.7" "special case"
  AlgebraicGeometry.instJacobsonSpaceCarrierCarrierCommRingCatFiberOfLocallyOfFiniteType
add_to_ega "IV 10.4.7" "closed immersions" JacobsonSpace.of_isClosedEmbedding
add_to_ega "IV 10.4.7" "special case" RingHom.FiniteType.isJacobsonRing
add_to_ega "IV 10.4.7" "open immersions" Topology.IsOpenEmbedding.preimage_closedPoints
add_to_ega "IV 10.4.7" "special case" isJacobsonRing_localization
add_to_ega "IV 10.4.7" "affine closed immersions" isJacobsonRing_of_surjective
add_to_ega "IV 10.4.9" "special case"
  AlgebraicGeometry.instJacobsonSpaceCarrierCarrierCommRingCatFiberOfLocallyOfFiniteType
add_to_ega "IV 10.4.10" "special case" IsIntegralClosure.finite
add_to_ega "IV 10.4.14" "more general" TrivSqZeroExt.lift
add_to_ega "IV 10.5.1" IsDomain
add_to_ega "IV 10.5.1" "f) ⇒ e) for local B" IsLocalRing.Ring.KrullDimLE.eq_bot_or_eq_top
add_to_ega "IV 10.5.1" IsNoetherianRing
add_to_ega "IV 10.5.1" PrimeSpectrum
add_to_ega "IV 10.6.1" "(i), special case"
  AlgebraicGeometry.instJacobsonSpaceCarrierCarrierCommRingCatFiberOfLocallyOfFiniteType
add_to_ega "IV 10.6.1" "(i), special case" RingHom.FiniteType.isJacobsonRing
add_to_ega "IV 10.7.1" "1° for fibres"
  AlgebraicGeometry.instJacobsonSpaceCarrierCarrierCommRingCatFiberOfLocallyOfFiniteType
add_to_ega "IV 10.7.1" "special case" MvPolynomial.isJacobsonRing_MvPolynomial_fin
add_to_ega "IV 10.7.1" "affine case" Ring.krullDimLE_one_iff
add_to_ega "IV 10.7.1" "integral affine case" Ring.krullDimLE_one_iff_of_isPrime_bot
add_to_ega "IV 10.7.3" "partial" AlgebraicGeometry.isIso_SpecMap_stakMap_localization
add_to_ega "IV 10.7.3" "partial" Ideal.IsMaximal.of_isLocalization_of_disjoint
add_to_ega "IV 10.7.3" "partial" Ideal.map_addIdeal_le_ringJacobson
add_to_ega "IV 10.7.3" "partial" Ideal.map_le_ringJacobson_of_add_mem
add_to_ega "IV 10.7.3" "partial" IsLocalization.primeSpectrumOrderIso
add_to_ega "IV 10.7.3" "partial" Polynomial.height_eq_height_add_one
add_to_ega "IV 10.7.3" Submonoid.addIdeal
add_to_ega "IV 10.9.2" "more general"
  AlgebraicGeometry.Scheme.Hom.closePoints_subset_preimage_closedPoints
add_to_ega "IV 10.9.2" "open immersions" Topology.IsOpenEmbedding.preimage_closedPoints
add_to_ega "IV 10.9.3" "underlying set" MaximalSpectrum
add_to_ega "IV 10.9.3" "partial" MaximalSpectrum.toPrimeSpectrum_range
add_to_ega "IV 10.9.3" "topology clause 1°" MaximalSpectrum.zariskiTopology
add_to_ega "IV 10.9.3" "partial" PrimeSpectrum.isClosed_singleton_iff_isMaximal
add_to_ega "IV 10.10.3" "more general" AlgHom.FiniteType.of_comp_finiteType
add_to_ega "IV 10.10.3" "partial" AlgebraicGeometry.ext_of_apply_closedPoint_eq
add_to_ega "IV 10.10.3" "partial" AlgebraicGeometry.pointEquivClosedPoint
add_to_ega "IV 10.10.3" "partial" AlgebraicGeometry.residueFieldIsoBase
add_to_ega "IV 10.10.3" "more general" RingHom.FiniteType.of_comp_finiteType
add_to_ega "IV 10.10.4" AlgebraicGeometry.IsReduced
add_to_ega "IV 10.10.4" "forward direction" AlgebraicGeometry.isReduced_stalk_of_isReduced
add_to_ega "IV 10.10.4" "special case" instIsReducedLocalization
add_to_ega "IV 10.10.4" "special case" isReduced_localizationPreserves
add_to_ega "IV 10.10.4" "special case" isReduced_ofLocalizationMaximal
add_to_ega "IV 10.10.5" "partial" AlgebraicGeometry.pointEquivClosedPoint
