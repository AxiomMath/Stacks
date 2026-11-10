module  -- shake: keep-all

import Mathlib.Algebra.Algebra.RestrictScalars
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
import Mathlib.Algebra.Category.ModuleCat.Algebra
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Mathlib.Algebra.Category.ModuleCat.Ext.Finite
import Mathlib.Algebra.Category.ModuleCat.Presheaf
import Mathlib.Algebra.Category.ModuleCat.Semi
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.Algebra.Homology.CochainComplexOpposite
import Mathlib.Algebra.Homology.Embedding.TruncGE
import Mathlib.Algebra.Homology.Embedding.TruncGEHomology
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.Homology
import Mathlib.Algebra.Homology.ShortComplex.LeftHomology
import Mathlib.Algebra.Homology.ShortComplex.RightHomology
import Mathlib.Algebra.Lie.TensorProduct
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Module.Hom
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.StructureSheaf
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.CategoryTheory.CommSq
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Preadditive.Opposite
import Mathlib.CategoryTheory.Square
import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace.ResidueField
import Mathlib.GroupTheory.GroupAction.DomAct.Basic
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.LinearAlgebra.DirectSum.TensorProduct
import Mathlib.LinearAlgebra.Dual.BaseChange
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.LinearAlgebra.PiTensorProduct.DirectSum
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Defs
import Mathlib.LinearAlgebra.TensorProduct.DirectLimit
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Conductor
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Ideal.IsPrimary
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.IsAdjoinRoot
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Nilpotent.Defs
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.QuotSMulTop
import Mathlib.RingTheory.ReesAlgebra
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RingHom.Finite
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Support
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.Topology.Irreducible
import StacksCore.RingTheory.Spectrum.Prime.Topology
import StacksCore.Tactic.EgaSgaAttribute

/-!
# EGA III references registered by name

Declarations realizing numbered items of EGA III, from the EGA/SGA concept index, that
are not tagged where they are declared: Mathlib and core declarations without an
`add_to_stacks` pointer in this library, and (with `--draft-only`) those of `StacksCore/`.
-/

add_to_ega "III 1.1.3" Ideal.ofList
add_to_ega "III 1.1.3" Ideal.span
add_to_ega "III 1.1.3" "(f)" QuotSMulTop.equivQuotTensor
add_to_ega "III 1.1.3" "(f)" QuotSMulTop.equivTensorQuot
add_to_ega "III 1.1.3" "(f)" TensorProduct.tensorQuotEquivQuotSMul
add_to_ega "III 1.1.4" "special case" QuotSMulTop
add_to_ega "III 1.1.5" ExteriorAlgebra.map
add_to_ega "III 1.1.5" "more general" Pi.mul_apply
add_to_ega "III 1.1.5" "more general" Pi.mul_def
add_to_ega "III 1.2.1" "more general"
  AlgebraicGeometry.LocallyRingedSpace.evaluation_eq_zero_iff_notMem_basicOpen
add_to_ega "III 1.2.1" "more general"
  AlgebraicGeometry.LocallyRingedSpace.evaluation_ne_zero_iff_mem_basicOpen
add_to_ega "III 1.2.1" "more general"
  AlgebraicGeometry.LocallyRingedSpace.Γevaluation_eq_zero_iff_notMem_basicOpen
add_to_ega "III 1.2.1" "more general"
  AlgebraicGeometry.LocallyRingedSpace.Γevaluation_ne_zero_iff_mem_basicOpen
open AlgebraicGeometry.Scheme.Modules in
add_to_ega "III 1.2.1" "M = Γ(X"
  instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensCarrierAbPresheaf
add_to_ega "III 1.2.1" AlgebraicGeometry.Scheme.basicOpen
add_to_ega "III 1.2.1" "more general"
  AlgebraicGeometry.Scheme.evaluation_eq_zero_iff_notMem_basicOpen
add_to_ega "III 1.2.1" "more general" AlgebraicGeometry.Scheme.evaluation_ne_zero_iff_mem_basicOpen
add_to_ega "III 1.2.1" "A = Γ(X, O_X)" AlgebraicGeometry.Scheme.Γ
open AlgebraicGeometry.IsAffineOpen in
add_to_ega "III 1.2.2" "special case"
  instAwayCarrierObjOppositeOpensCarrierCarrierCommRingCatSpecPresheafOpOpensBasicOpen
add_to_ega "III 1.2.2" "special case" AlgebraicGeometry.IsAffineOpen.isLocalization_basicOpen
add_to_ega "III 1.2.2" "special case" AlgebraicGeometry.IsAffineOpen.isLocalization_of_eq_basicOpen
-- These auto-generated instance names are longer than a line, so each identifier is
-- assembled from two pieces before being handed to `add_to_ega`.
run_cmd Lean.Elab.Command.elabCommand (← `(command| add_to_ega "III 1.2.2" "special case"
  $(Lean.mkIdent <| .str `AlgebraicGeometry.StructureSheaf
    ("instAwayObjOppositeOpensCarrierTopObjFunctorTypeIsSheafGrothendieckTopology" ++
      "StructureSheafInTypeOpBasicOpen"))))
run_cmd Lean.Elab.Command.elabCommand (← `(command| add_to_ega "III 1.2.2" "special case"
  $(Lean.mkIdent <| .str `AlgebraicGeometry.StructureSheaf
    ("instAwayObjOppositeOpensCarrierTopObjFunctorTypeIsSheafGrothendieckTopology" ++
      "StructureSheafInTypeOpBasicOpenToOpenₗ"))))
add_to_ega "III 1.2.2" "special case" AlgebraicGeometry.isLocalization_away_of_isAffine
add_to_ega "III 1.2.2" "special case" AlgebraicGeometry.Γ_restrict_isLocalization
add_to_ega "III 1.2.5" "partial" AlgebraicGeometry.IsAffineOpen.basicOpen
add_to_ega "III 1.2.5" "partial" AlgebraicGeometry.IsAffineOpen.biInf
add_to_ega "III 1.2.5" "partial" AlgebraicGeometry.IsAffineOpen.iInf
add_to_ega "III 1.2.5" "partial" AlgebraicGeometry.IsAffineOpen.inf
add_to_ega "III 1.2.5" "partial" AlgebraicGeometry.IsAffineOpen.instIsAffineToSchemeBasicOpen
add_to_ega "III 1.2.5" "partial" AlgebraicGeometry.IsAffineOpen.ι_basicOpen_preimage
add_to_ega "III 1.4.6" "special case" AlgebraicGeometry.IsAffineOpen.isLocalization_of_eq_basicOpen
run_cmd Lean.Elab.Command.elabCommand (← `(command| add_to_ega "III 1.4.6" "special case"
  $(Lean.mkIdent <| .str `AlgebraicGeometry.StructureSheaf
    ("instAwayObjOppositeOpensCarrierTopObjFunctorTypeIsSheafGrothendieckTopology" ++
      "StructureSheafInTypeOpBasicOpenToOpenₗ"))))
add_to_ega "III 1.4.6" "special case" AlgebraicGeometry.isLocalization_away_of_isAffine
add_to_ega "III 1.4.6" "special case" AlgebraicGeometry.Γ_restrict_isLocalization
add_to_ega "III 1.4.15" CategoryTheory.Limits.pullback
add_to_ega "III 1.4.15.5" AlgebraicGeometry.Flat.SpecMap_iff
add_to_ega "III 1.4.15.5" "partial" AlgebraicGeometry.Scheme.Hom.flat_appTop
run_cmd Lean.Elab.Command.elabCommand (← `(command| add_to_ega "III 2.1.2" "special case"
  $(Lean.mkIdent <| .str `AlgebraicGeometry.StructureSheaf
    ("instAwayObjOppositeOpensCarrierTopObjFunctorTypeIsSheafGrothendieckTopology" ++
      "StructureSheafInTypeOpBasicOpen"))))
run_cmd Lean.Elab.Command.elabCommand (← `(command| add_to_ega "III 2.1.2" "special case"
  $(Lean.mkIdent <| .str `AlgebraicGeometry.StructureSheaf
    ("instAwayObjOppositeOpensCarrierTopObjFunctorTypeIsSheafGrothendieckTopology" ++
      "StructureSheafInTypeOpBasicOpenToOpenₗ"))))
add_to_ega "III 2.1.2" "special case" AlgebraicGeometry.Γ_restrict_isLocalization
add_to_ega "III 2.1.8" "special case" AdjoinRoot.powerBasis'
add_to_ega "III 2.1.8" "special case" AdjoinRoot.powerBasisAux
add_to_ega "III 2.1.8" "special case" AdjoinRoot.powerBasisAux'
add_to_ega "III 2.1.8" "special case" IsAdjoinRootMonic.basis_apply
add_to_ega "III 2.1.11" "special case" Algebra.TensorProduct.quotientTensorEquiv
add_to_ega "III 2.1.11" "special case" Algebra.TensorProduct.tensorQuotientEquiv
add_to_ega "III 2.1.11" "partial" TensorProduct.AlgebraTensorModule.tensorQuotientEquiv
add_to_ega "III 2.1.11" "partial" TensorProduct.quotientTensorEquiv
add_to_ega "III 2.1.11" "partial" TensorProduct.quotientTensorQuotientEquiv
add_to_ega "III 2.1.11" "partial" TensorProduct.tensorQuotientEquiv
add_to_ega "III 2.2.5" "more general"
  AlgebraicGeometry.instQuasiCompactOfIsLocallyNoetherianOfIsOpenImmersion
add_to_ega "III 2.2.5" "more general" AlgebraicGeometry.quasiCompact_of_noetherianSpace_source
add_to_ega "III 2.6.2.1" "special case" RingHom.finite_isStableUnderBaseChange
add_to_ega "III 2.6.2.3" "partial" AlgebraicGeometry.instIsClosedImmersionFstScheme
add_to_ega "III 2.6.2.3" "j'" AlgebraicGeometry.instIsClosedImmersionSndScheme
add_to_ega "III 2.6.2.4" "special case" conductor
add_to_ega "III 2.6.2.5" "Affine, special case" Module.support_quotSMulTop
add_to_ega "III 2.6.2.5" "special case" Module.support_quotient
add_to_ega "III 2.6.2.5" "partial" prod_mem_ideal_map_of_mem_conductor
add_to_ega "III 3.4.5" "partial" AlgebraicGeometry.IsAffineOpen.Spec_basicOpen
add_to_ega "III 3.4.5" "partial" AlgebraicGeometry.IsAffineOpen.basicOpen
add_to_ega "III 3.4.5" "partial" AlgebraicGeometry.IsAffineOpen.instIsAffineToSchemeBasicOpen
add_to_ega "III 3.4.5" "partial" AlgebraicGeometry.basicOpenIsoSpecAway
add_to_ega "III 4.1.2" "partial" AlgebraicGeometry.Scheme.IdealSheafData.support_comap
add_to_ega "III 4.1.7" AdicCompletion
add_to_ega "III 4.1.7" AlgebraicGeometry.Scheme.IdealSheafData.equivOfIsAffine
add_to_ega "III 4.1.7.7" instIsNoetherianRingSubtypePolynomialMemSubalgebraReesAlgebra
add_to_ega "III 4.1.7.7" reesAlgebra
add_to_ega "III 4.2.1" "special case" AlgebraicGeometry.Scheme.Hom.fiberOverSpecResidueField
add_to_ega "III 4.2.1" "special case" AlgebraicGeometry.instCanonicallyOverFiber
add_to_ega "III 4.3.4" AlgebraicGeometry.GeometricallyConnected
add_to_ega "III 4.3.4" "more general" AlgebraicGeometry.IsProper.instFstScheme
add_to_ega "III 4.3.4" AlgebraicGeometry.geometricallyConnected_iff
add_to_ega "III 4.3.11" AlgebraicGeometry.UniversallyOpen
add_to_ega "III 4.3.13" "partial" AlgebraicGeometry.Proj.instIsSeparated
add_to_ega "III 4.3.13" "partial" AlgebraicGeometry.Proj.isSeparated
add_to_ega "III 4.3.13" AlgebraicGeometry.Proj.toSpecZero
add_to_ega "III 4.3.13" ProjectiveSpectrum
add_to_ega "III 4.3.13" ProjectiveSpectrum.top
add_to_ega "III 4.4.1" "more general"
  AlgebraicGeometry.Scheme.Hom.exists_isIso_morphismRestrict_toNormalization
add_to_ega "III 4.4.1" "(x)"
  AlgebraicGeometry.Scheme.Hom.exists_mem_and_isIso_morphismRestrict_toNormalization
add_to_ega "III 4.4.1" "more general" AlgebraicGeometry.Scheme.Hom.isOpen_quasiFiniteAt
add_to_ega "III 4.4.1" "partial"
  AlgebraicGeometry.instIsOpenImmersionCompSchemeιQuasiFiniteLocusToNormalization
add_to_ega "III 4.4.1" "case X′ = X"
  AlgebraicGeometry.instIsOpenImmersionToNormalizationOfLocallyQuasiFiniteOfLocallyOfFiniteType
add_to_ega "III 4.4.2" "more general" AlgebraicGeometry.IsFinite.eq_isProper_inf_isAffineHom
add_to_ega "III 4.4.2" "a) ⇒ b), a) ⇒ c)" AlgebraicGeometry.IsProper.instOfIsFinite
add_to_ega "III 4.4.2" "a)" AlgebraicGeometry.Scheme.Hom.finite_preimage_singleton
add_to_ega "III 4.4.2" "a) ⇒ b), a) ⇒ c)" AlgebraicGeometry.instIsProperOfIsFinite
add_to_ega "III 4.4.3" "more general" AlgebraicGeometry.Scheme.Hom.isOpen_quasiFiniteAt
add_to_ega "III 4.4.3" AlgebraicGeometry.Scheme.Hom.quasiFiniteLocus
add_to_ega "III 4.4.4" "partial" AlgebraicGeometry.IsSchemeTheoreticallyDominant.isReduced
add_to_ega "III 4.4.4" "partial" IsIrreducible.closure
add_to_ega "III 4.4.4" "partial" isIrreducible_iff_closure
add_to_ega "III 4.4.4" "partial" isPreirreducible_iff_closure
add_to_ega "III 4.4.7" Ideal.IsMaximal
add_to_ega "III 4.4.7" "partial" Ideal.IsPrimary
add_to_ega "III 4.4.7" Ideal.comap
add_to_ega "III 4.4.7" Localization.AtPrime
add_to_ega "III 4.4.7" Module.Finite
add_to_ega "III 4.4.10" "more general" AlgebraicGeometry.Scheme.Hom.isOpen_quasiFiniteAt
add_to_ega "III 4.4.10" AlgebraicGeometry.Scheme.Hom.quasiFiniteLocus
add_to_ega "III 4.4.11" "more general" AlgebraicGeometry.IsFinite.eq_proper_inf_locallyQuasiFinite
add_to_ega "III 4.4.11" "more general"
  AlgebraicGeometry.IsFinite.iff_isProper_and_locallyQuasiFinite
add_to_ega "III 4.4.11" "more general" AlgebraicGeometry.IsFinite.of_isProper_of_locallyQuasiFinite
add_to_ega "III 4.4.11" "locally Artinian target" AlgebraicGeometry.IsFinite.of_locallyQuasiFinite
add_to_ega "III 4.4.11" "partial"
  AlgebraicGeometry.exists_isFinite_morphismRestrict_of_finite_preimage_singleton
add_to_ega "III 4.4.12" "partial" AlgebraicGeometry.IsSeparated.instResLE
add_to_ega "III 4.4.12" "partial"
  AlgebraicGeometry.Scheme.Hom.exists_isIso_morphismRestrict_toNormalization
add_to_ega "III 4.4.12" "openness of X′" AlgebraicGeometry.Scheme.Hom.isOpen_quasiFiniteAt
add_to_ega "III 4.4.12" AlgebraicGeometry.Scheme.Hom.quasiFiniteLocus
add_to_ega "III 4.4.12" "partial"
  AlgebraicGeometry.instLocallyQuasiFiniteCompSchemeιQuasiFiniteLocus
add_to_ega "III 4.5.1" "special case" ModuleCat.finite_ext
add_to_ega "III 4.6.2" AlgebraicGeometry.Scheme.Hom.fiber
add_to_ega "III 4.6.2" "partial" AlgebraicGeometry.Scheme.Hom.fiberHomeo
add_to_ega "III 4.6.2" AlgebraicGeometry.Scheme.Hom.fiberToSpecResidueField
add_to_ega "III 4.6.2" AlgebraicGeometry.Scheme.Hom.fiberι
add_to_ega "III 4.6.2" AlgebraicGeometry.Scheme.residueField
add_to_ega "III 4.6.2" "special case" AlgebraicGeometry.Spec.fiberToSpecResidueFieldIso
add_to_ega "III 4.6.2" "special case" Ideal.Fiber
add_to_ega "III 4.6.7" "partial" AlgebraicGeometry.Scheme.Hom.fiber
add_to_ega "III 4.6.7" "(i), special case"
  AlgebraicGeometry.exists_finite_imageι_comp_morphismRestrict_of_finite_image_preimage
add_to_ega "III 4.6.7" "(i), special case"
  AlgebraicGeometry.exists_isFinite_morphismRestrict_of_finite_preimage_singleton
add_to_ega "III 4.6.7.1" "special case" Module.IsLocalRing.linearIndependent_of_flat
add_to_ega "III 4.7.1" "canonical projection g" AlgebraicGeometry.instCanonicallyOverFiber
add_to_ega "III 4.8.5" "ordinary schemes" AlgebraicGeometry.IsFinite.instMorphismRestrict
add_to_ega "III 4.8.9" "ordinary affine case" AlgebraicGeometry.IsClosedImmersion.Spec_iff
add_to_ega "III 4.8.9" "ordinary affine case"
  AlgebraicGeometry.IsClosedImmersion.isAffine_surjective_of_isAffine
add_to_ega "III 4.8.9" "ordinary affine case"
  AlgebraicGeometry.IsClosedImmersion.of_surjective_of_isAffine
add_to_ega "III 4.8.11" "special case" AlgebraicGeometry.IsFinite.eq_proper_inf_locallyQuasiFinite
add_to_ega "III 4.8.11" "special case"
  AlgebraicGeometry.IsFinite.iff_isProper_and_locallyQuasiFinite
add_to_ega "III 4.8.11" "partial" AlgebraicGeometry.IsFinite.of_isProper_of_locallyQuasiFinite
add_to_ega "III 4.8.11" "finite implies proper" AlgebraicGeometry.IsProper.instOfIsFinite
add_to_ega "III 4.8.11" "partial" AlgebraicGeometry.Scheme.Hom.finite_preimage_singleton
add_to_ega "III 4.8.11" "ordinary schemes"
  AlgebraicGeometry.exists_isFinite_morphismRestrict_of_finite_preimage_singleton
add_to_ega "III 4.8.11" "finite implies proper" AlgebraicGeometry.instIsProperOfIsFinite
add_to_ega "III 5.1.1" Ideal.adicTopology
add_to_ega "III 5.1.1" IsAdic
add_to_ega "III 5.1.1" IsAdicComplete
add_to_ega "III 5.3.5" "j" AlgebraicGeometry.IsClosedImmersion.instSubschemeι
add_to_ega "III 5.3.5" "special case" AlgebraicGeometry.Scheme.eq_zeroLocus_of_isClosed_of_isAffine
add_to_ega "III 5.4.6" "more general" Ideal.map_radical_le
add_to_ega "III 5.4.6" "more general" IsNilpotent.map
add_to_ega "III 6.1.1" CategoryTheory.Limits.pullback
add_to_ega "III 6.1.1" "special case" Module.Flat.iff_lTensor_exact'
add_to_ega "III 6.1.1" "partial" Module.Flat.iff_preservesFiniteLimits_tensorRight
add_to_ega "III 6.1.1" "special case" Module.Flat.iff_rTensor_exact
add_to_ega "III 6.1.1" "special case" Module.Flat.iff_rTensor_preserves_shortComplex_exact
add_to_ega "III 6.1.1" "special case" Module.Flat.lTensor_exact
add_to_ega "III 6.1.1" "special case" Module.Flat.lTensor_shortComplex_exact
add_to_ega "III 6.1.1" "special case" Module.Flat.rTensor_exact
add_to_ega "III 6.1.1" "special case" Module.Flat.rTensor_shortComplex_exact
add_to_ega "III 6.1.4" HomologicalComplex.homotopyEquivalences
add_to_ega "III 6.1.4" HomotopyEquiv
add_to_ega "III 6.1.4" "special case" HomotopyEquiv.quasiIso_hom
add_to_ega "III 6.2.1" "f = id_X" HomotopyEquiv.quasiIso_hom
add_to_ega "III 6.2.1" "f = id_X" HomotopyEquiv.toHomologyIso
add_to_ega "III 6.2.7" ChainComplex.cochainComplexEquivalence
add_to_ega "III 6.3.1" HomologicalComplex.tensorObj
add_to_ega "III 6.3.10" "special case" ModuleCat.ExtendRestrictScalarsAdj.counit
add_to_ega "III 6.3.13" "special case" IsLocalization.moduleTensorEquiv
add_to_ega "III 6.4.1" "special case"
  AlgebraicGeometry.Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent
add_to_ega "III 6.4.1" "special case" AlgebraicGeometry.isQuasicoherent_iff_isIso_fromTildeΓ
add_to_ega "III 6.4.1" "partial" AlgebraicGeometry.pullbackSpecIso'
add_to_ega "III 6.5.2" "Affineness clause"
  AlgebraicGeometry.Scheme.Pullback.isAffine_of_isAffine_isAffine_isAffine
add_to_ega "III 6.5.2" "Covering clause" AlgebraicGeometry.Scheme.Pullback.openCoverOfLeftRight
add_to_ega "III 6.5.6" "special case" TensorProduct.directLimitLeft
add_to_ega "III 6.5.10" "special case" AlgebraicGeometry.Flat.iff_flat_stalkMap
add_to_ega "III 6.5.10" "partial" AlgebraicGeometry.Flat.of_stalkMap
add_to_ega "III 6.5.10" "partial" AlgebraicGeometry.Flat.stalkMap
add_to_ega "III 6.5.10" "more general" Module.Flat.dfinsupp
add_to_ega "III 6.5.10" "more general" Module.Flat.dfinsupp_iff
add_to_ega "III 6.5.10" "more general" Module.Flat.directSum
add_to_ega "III 6.5.10" "more general" Module.Flat.directSum_iff
add_to_ega "III 6.6.1" "partial"
  AlgebraicGeometry.instCompactSpaceCarrierCarrierCommRingCatPullbackSchemeOfQuasiCompact_1
add_to_ega "III 6.6.4" "more general" AlgebraicGeometry.IsAffineOpen.biInf
add_to_ega "III 6.6.4" "more general" AlgebraicGeometry.IsAffineOpen.iInf
add_to_ega "III 6.6.4" "binary intersections" AlgebraicGeometry.IsAffineOpen.inf
add_to_ega "III 6.7.1" "partial" AlgebraicGeometry.IsAffineOpen.preimage
add_to_ega "III 6.7.1" "special case" PrimeSpectrum.basicOpen_mul
add_to_ega "III 6.7.2" "partial" IsLocalization.moduleTensorEquiv
add_to_ega "III 6.7.10.1" "more general" CategoryTheory.CommSq
add_to_ega "III 6.7.10.1" "more general" CategoryTheory.Square
add_to_ega "III 6.7.10.1" CategoryTheory.Square.mk
add_to_ega "III 6.7.13" CategoryTheory.Limits.pullbackSymmetry
add_to_ega "III 6.9.1" "partial" AlgebraicGeometry.instQuasiCompactSndScheme
add_to_ega "III 6.9.1" "partial" CategoryTheory.Limits.pullback
add_to_ega "III 6.9.4" "more general"
  AlgebraicGeometry.instCompactSpaceCarrierCarrierCommRingCatPullbackSchemeOfQuasiCompact
add_to_ega "III 6.9.4" "more general"
  AlgebraicGeometry.instCompactSpaceCarrierCarrierCommRingCatPullbackSchemeOfQuasiCompact_1
add_to_ega "III 6.9.4" "more general" AlgebraicGeometry.instQuasiCompactSndScheme
add_to_ega "III 6.9.10" AlgebraicGeometry.Scheme.Hom.fiber
add_to_ega "III 6.10.4" "partial" CategoryTheory.Limits.pullback
add_to_ega "III 6.10.4" "special case" Module.Flat.instTensorProduct
add_to_ega "III 6.10.5" "partial" SheafOfModules.freeFunctorCompPullbackIso
add_to_ega "III 6.10.5" "partial" SheafOfModules.pullbackObjFreeIso
add_to_ega "III 7.1.1" Ab
add_to_ega "III 7.1.1" ModuleCat
add_to_ega "III 7.1.1" "partial" ModuleCat.forget₂AddCommGroupIsEquivalence
add_to_ega "III 7.1.2" CategoryTheory.Functor.Linear
add_to_ega "III 7.1.2" "more general" CategoryTheory.Functor.linear_iff
add_to_ega "III 7.1.2" ModuleCat.hasForgetToAddCommGroup
add_to_ega "III 7.1.2" "more general" PresheafOfModules.instFaithfulFunctorOppositeAbToPresheaf
add_to_ega "III 7.1.2" "more general" SheafOfModules.instFaithfulSheafAddCommGrpCatToSheaf
add_to_ega "III 7.1.3" CategoryTheory.Functor.comp
add_to_ega "III 7.1.3" "partial" CategoryTheory.Functor.whiskeringLeft
add_to_ega "III 7.1.3" Module.restrictScalars
add_to_ega "III 7.1.3" ModuleCat.Algebra.instModuleCarrier
add_to_ega "III 7.1.3" ModuleCat.RestrictScalars.obj'
add_to_ega "III 7.1.3" "additivity of ρ_*" ModuleCat.instAdditiveRestrictScalars
add_to_ega "III 7.1.3" "special case" ModuleCat.moduleOfAlgebraModule
add_to_ega "III 7.1.3" "partial" ModuleCat.preservesColimit_restrictScalars
add_to_ega "III 7.1.3" "left exactness of ρ_*" ModuleCat.preservesLimit_restrictScalars
add_to_ega "III 7.1.3" ModuleCat.restrictScalars
add_to_ega "III 7.1.3" "special case" ModuleCat.restrictScalars_map_exact
add_to_ega "III 7.1.3" RestrictScalars.module
add_to_ega "III 7.1.3" SemimoduleCat.Algebra.instModuleCarrier
add_to_ega "III 7.1.3" "partial" instPreservesFiniteColimitsModuleCatRestrictScalars
add_to_ega "III 7.1.3" "partial" instPreservesFiniteLimitsModuleCatRestrictScalars
add_to_ega "III 7.1.5" "special case" Module.flat_of_isLocalized_maximal
add_to_ega "III 7.1.5" "special case" Module.flat_of_localized_maximal
add_to_ega "III 7.2.1" "special case" TensorProduct.LieModule.lift
add_to_ega "III 7.2.1" "special case" TensorProduct.curry
add_to_ega "III 7.2.1" "special case" TensorProduct.lift
add_to_ega "III 7.2.1" TensorProduct.liftAddHom
add_to_ega "III 7.2.2" "more general" AddMonoidHom.instDomMulActModule
add_to_ega "III 7.2.2" "more general" CategoryTheory.moduleEndLeft
add_to_ega "III 7.2.2" "partial" DomMulAct.instDistribMulActionAddMonoidHom
add_to_ega "III 7.2.2" "partial" DomMulAct.instMulActionAddMonoidHomOfDistribMulAction
add_to_ega "III 7.2.2" "partial" DomMulAct.instSMulAddMonoidHom
add_to_ega "III 7.2.2" "partial" LinearMap.ringLmapEquivSelf
add_to_ega "III 7.2.2" "partial" LinearMap.ringLmapEquivSelf_symm_apply
add_to_ega "III 7.2.2" LinearMap.toSpanSingleton
add_to_ega "III 7.2.3.2" "M_(B)" ModuleCat.ExtendScalars.obj'
add_to_ega "III 7.2.3.2" "M ↦ M_(B) as a functor" ModuleCat.extendScalars
add_to_ega "III 7.2.5" "(c) ⇒ (a)" lTensor.equiv
add_to_ega "III 7.2.5" "(c) ⇒ (a)" lTensor.linearEquiv_of_rightInverse
add_to_ega "III 7.2.5" "(c) ⇒ (a)" rTensor.equiv
add_to_ega "III 7.2.6" CategoryTheory.Functor.Additive
add_to_ega "III 7.2.6" "special case" LinearMap.lTensor_add
add_to_ega "III 7.2.6" "special case" LinearMap.rTensorHom
add_to_ega "III 7.2.6" "special case" PiTensorProduct.ofDirectSumEquiv
add_to_ega "III 7.2.6" TensorProduct
add_to_ega "III 7.2.6" "special case" TensorProduct.AlgebraTensorModule.map_add_right
add_to_ega "III 7.2.6" TensorProduct.AlgebraTensorModule.rTensor
add_to_ega "III 7.2.6" "special case" TensorProduct.directSum
add_to_ega "III 7.2.6" "special case" TensorProduct.directSumLeft
add_to_ega "III 7.2.6" "special case" TensorProduct.directSumRight
add_to_ega "III 7.2.6" "special case" TensorProduct.finsuppRight
add_to_ega "III 7.2.6" "special case" TensorProduct.finsuppScalarRight
add_to_ega "III 7.2.6" "special case" TensorProduct.piLeft
add_to_ega "III 7.2.6" "special case" TensorProduct.piRight
add_to_ega "III 7.2.6" "special case" TensorProduct.prodRight
add_to_ega "III 7.2.6" "special case" lTensor.equiv
add_to_ega "III 7.2.6" "special case" lTensor.linearEquiv_of_rightInverse
add_to_ega "III 7.2.6" "partial" lTensor_exact
add_to_ega "III 7.2.6" "partial" rTensor_exact
add_to_ega "III 7.3.2" "Case T_i = Tor_i^A(-" Module.Flat.isSMulRegular_of_isRegular
add_to_ega "III 7.3.2" "Case T_0 = M ⊗ -" Module.Invertible.lTensor_injective_iff
add_to_ega "III 7.3.2" "Case T_0 =" Module.Invertible.rTensor_injective_iff
add_to_ega "III 7.3.4" "special case" AlgebraicGeometry.Scheme.Hom.isLocallyConstant_finrank
add_to_ega "III 7.3.4" "special case" Module.isLocallyConstant_rankAtStalk
add_to_ega "III 7.3.5" "partial" Module.free_of_flat_of_finrank_eq
add_to_ega "III 7.3.5" "partial" Module.free_of_flat_of_isLocalRing
add_to_ega "III 7.4.1" "partial" Module.Flat.isBaseChange
add_to_ega "III 7.4.1" "partial" TensorProduct.AlgebraTensorModule.cancelBaseChange
add_to_ega "III 7.4.2" "more general" CategoryTheory.Limits.cokernel
add_to_ega "III 7.4.2" "more general" CategoryTheory.ShortComplex.opcyclesIsCokernel
add_to_ega "III 7.4.2" "more general" HomologicalComplex.opcyclesIsCokernel
add_to_ega "III 7.4.3" "partial"
  IsRegularLocalRing.instOfIsLocalRingOfIsDomainOfIsPrincipalIdealRing
add_to_ega "III 7.4.3" "partial" instIsRegularRingOfIsDedekindDomain
add_to_ega "III 7.4.6" "partial" CategoryTheory.Functor.RepresentableBy.uniqueUpToIso
add_to_ega "III 7.4.6" Module.Finite
add_to_ega "III 7.4.7.2" TensorProduct.quotTensorEquivQuotSMul
add_to_ega "III 7.4.7.2" TensorProduct.tensorQuotEquivQuotSMul
add_to_ega "III 7.5.1" AdicCompletion
add_to_ega "III 7.6.3" "Local case" IsDiscreteValuationRing.TFAE
add_to_ega "III 7.6.3" "Fields and DVRs"
  IsRegularLocalRing.instOfIsLocalRingOfIsDomainOfIsPrincipalIdealRing
add_to_ega "III 7.6.3" "partial" instIsRegularRingOfIsDedekindDomain
add_to_ega "III 7.6.4" HomologicalComplex.tensorObj
add_to_ega "III 7.6.9" "special case" Ideal.finrank_fiber_eq_finrank
add_to_ega "III 7.6.9" "(ii), special case" Module.isLocallyConstant_rankAtStalk
add_to_ega "III 7.6.11" CategoryTheory.ShortComplex.cycles
add_to_ega "III 7.6.11" CategoryTheory.ShortComplex.cyclesIsKernel
add_to_ega "III 7.6.11" CategoryTheory.ShortComplex.cyclesIsoKernel
add_to_ega "III 7.6.11" CategoryTheory.ShortComplex.homologyIsCokernel
add_to_ega "III 7.6.11" CategoryTheory.ShortComplex.leftHomologyIsCokernel
add_to_ega "III 7.6.11" CategoryTheory.ShortComplex.opcyclesIsCokernel
add_to_ega "III 7.6.11" HomologicalComplex.cycles
add_to_ega "III 7.6.11" HomologicalComplex.cyclesIsKernel
add_to_ega "III 7.6.11" HomologicalComplex.homologyIsCokernel
add_to_ega "III 7.6.11" HomologicalComplex.iCyclesIso
add_to_ega "III 7.6.11" HomologicalComplex.opcycles
add_to_ega "III 7.6.11" HomologicalComplex.opcyclesIsCokernel
add_to_ega "III 7.6.11" "partial" IsLocalRing.span_eq_top_of_tmul_eq_basis
add_to_ega "III 7.6.11" LinearMap.dualMap
add_to_ega "III 7.6.11" LinearMap.ker
add_to_ega "III 7.6.11" LinearMap.range
add_to_ega "III 7.6.11" Module.Dual
add_to_ega "III 7.6.11" Module.Dual.transpose
add_to_ega "III 7.6.11" "partial" Module.IsReflexive.of_finite_of_free
add_to_ega "III 7.6.11" "partial" Module.finrank_of_isPerfPair
add_to_ega "III 7.6.11" "partial" Module.instIsReflexiveOfFiniteOfProjective
add_to_ega "III 7.7.1" ChainComplex.cochainComplexEquivalence
add_to_ega "III 7.7.2" "special case" AlgebraicGeometry.Flat.instFstScheme
add_to_ega "III 7.7.2" "special case" AlgebraicGeometry.Flat.instSndScheme
add_to_ega "III 7.7.2" "special case"
  AlgebraicGeometry.Scheme.Modules.isQuasicoherent_restrictFunctor
add_to_ega "III 7.7.2" "quasi-compactness of f'" AlgebraicGeometry.instQuasiCompactSndScheme
add_to_ega "III 7.7.2" CategoryTheory.Limits.pullback
add_to_ega "III 7.7.2" "special case" Module.Flat.isBaseChange
add_to_ega "III 7.7.2" "special case" RingHom.Flat.isStableUnderBaseChange
add_to_ega "III 7.7.8" "(ii), special case" SheafOfModules.Presentation.IsFinite
add_to_ega "III 7.7.9" "more general" AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction
add_to_ega "III 7.7.9" "special case" IsBaseChange.dual
add_to_ega "III 7.7.9" "(i), special case" IsBaseChange.toDualBaseChange
add_to_ega "III 7.7.11" "Converse, special case" Module.Flat.of_flat_tensorProduct
add_to_ega "III 7.7.12" "special case" HomologicalComplex.instQuasiIsoAtπTruncGEF
add_to_ega "III 7.7.12" "special case" HomologicalComplex.quasiIsoAt_πTruncGE
add_to_ega "III 7.7.12" HomologicalComplex.truncGE
add_to_ega "III 7.7.12" "partial" HomologicalComplex.truncGE'.X
add_to_ega "III 7.7.12" "L′_i = L_i for i < i₁" HomologicalComplex.truncGE'XIso
add_to_ega "III 7.7.12" "more general" Module.Flat.projective_of_finitePresentation
add_to_ega "III 7.7.12" "special case" Module.free_of_flat_of_finrank_eq
add_to_ega "III 7.7.12" "special case" Module.free_of_flat_of_isLocalRing
add_to_ega "III 7.8.6" Algebra.Etale.iff_exists_algEquiv_prod
add_to_ega "III 7.8.6.1" "special case" PrimeSpectrum.connectedSpace_iff_isIdempotentElem
add_to_ega "III 7.8.6.1" "affine case Z = Spec R"
  PrimeSpectrum.preconnectedSpace_iff_isIdempotentElem
add_to_ega "III 7.9.1" "more general" Ideal.finrank_fiber_eq_rankAtStalk
add_to_ega "III 7.9.1" Module.Finite
add_to_ega "III 7.9.1" Module.Projective
add_to_ega "III 7.9.1" Module.rankAtStalk
add_to_ega "III 7.9.1" "more general" Module.rankAtStalk_eq
add_to_ega "III 7.9.3" "special case" Module.isLocallyConstant_rankAtStalk
add_to_ega "III 7.9.7" "special case" AlgebraicGeometry.Flat.instFstScheme
add_to_ega "III 7.9.7" "special case" AlgebraicGeometry.Flat.instSndScheme
add_to_ega "III 7.9.7" "special case" CommRingCat.instIsStableUnderCobaseChangeFlat
add_to_ega "III 7.9.7" "special case" Module.Flat.isBaseChange
add_to_ega "III 7.9.7" "special case" RingHom.Flat.isStableUnderBaseChange
