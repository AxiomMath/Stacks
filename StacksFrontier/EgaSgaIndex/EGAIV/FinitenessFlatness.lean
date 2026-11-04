module  -- shake: keep-all

import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Category.FGModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.LeftHomology
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.AlgebraicGeometry.IdealSheaf.IrreducibleComponent
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.LocalIso
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.CategoryTheory.Limits.Constructions.Filtered
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryFan
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryProducts
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Preadditive.Opposite
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Geometry.RingedSpace.OpenImmersion
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.LinearAlgebra.TensorProduct.Defs
import Mathlib.RingTheory.Adjoin.FG
import Mathlib.RingTheory.Adjoin.Tower
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Extension.Generators
import Mathlib.RingTheory.Extension.Presentation.Basic
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.Finiteness.Finsupp
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Finiteness.Nakayama
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Descent
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Jacobson.Artinian
import Mathlib.RingTheory.Jacobson.Radical
import Mathlib.RingTheory.Lasker
import Mathlib.RingTheory.LocalRing.Length
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Noetherian.Orzech
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.Regular.IsSMulRegular
import Mathlib.RingTheory.RingHom.EssFiniteType
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.RingHom.Finite
import Mathlib.RingTheory.RingHom.FinitePresentation
import Mathlib.RingTheory.RingHom.FiniteType
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.RingHom.Integral
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import Mathlib.RingTheory.SimpleRing.Field
import Mathlib.RingTheory.Spectrum.Prime.Chevalley
import Mathlib.RingTheory.Spectrum.Prime.ChevalleyComplexity
import Mathlib.RingTheory.Spectrum.Prime.ConstructibleSet
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Support
import Mathlib.RingTheory.TensorProduct.IsBaseChangeHom
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.TotallySplit
import Mathlib.Topology.Constructible
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Irreducible
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.OpenPartialHomeomorph.IsImage
import Mathlib.Topology.QuasiSeparated
import Mathlib.Topology.Spectral.ConstructibleTopology
import StacksCore.RingTheory.Morita.SimpleRing
import StacksCore.RingTheory.Support
import StacksCore.Topology.Compact.Image
import StacksCore.Topology.Noetherian.ConstructiblePreimage
import StacksCore.Topology.Noetherian.Retrocompact
import StacksCore.Tactic.EgaSgaAttribute

/-!
# EGA IV references registered by name, §§1–3

Registrations for EGA IV §§1–3: relative finiteness conditions and constructible sets, base
change and flatness, associated primes and primary decomposition. Part of
`StacksFrontier.EgaSgaIndex.EGAIV`, whose module docstring describes the index.
-/

add_to_ega "IV 1.1.1" AlgebraicGeometry.quasiCompact_iff_isSpectralMap
add_to_ega "IV 1.1.2" "more general" AlgebraicGeometry.QuasiCompact.of_comp
add_to_ega "IV 1.1.2" "special case"
  AlgebraicGeometry.instHasOfPostcompPropertySchemeIsOpenImmersionOfIsStableUnderBaseChange
add_to_ega "IV 1.1.2" "more general"
  AlgebraicGeometry.instHasOfPostcompPropertySchemeQuasiCompactQuasiSeparated
add_to_ega "IV 1.1.2" "more general" AlgebraicGeometry.instIsMultiplicativeSchemeQuasiCompact
add_to_ega "IV 1.1.2" AlgebraicGeometry.instQuasiCompactFstScheme
add_to_ega "IV 1.1.2" "special case" AlgebraicGeometry.instQuasiCompactMorphismRestrict
add_to_ega "IV 1.1.2" "special case"
  AlgebraicGeometry.instQuasiCompactOfIsLocallyNoetherianOfIsOpenImmersion
add_to_ega "IV 1.1.2" AlgebraicGeometry.instQuasiCompactSndScheme
add_to_ega "IV 1.1.2" "more general" AlgebraicGeometry.quasiCompact_of_noetherianSpace_source
add_to_ega "IV 1.1.6" "more general" CategoryTheory.Limits.coprod.desc
add_to_ega "IV 1.2.1" AlgebraicGeometry.QuasiSeparated
add_to_ega "IV 1.2.1" AlgebraicGeometry.quasiSeparatedSpace_iff_quasiCompact_prod_lift
add_to_ega "IV 1.2.1" AlgebraicGeometry.quasiSeparatedSpace_iff_quasiSeparated
add_to_ega "IV 1.2.2" "more general" AlgebraicGeometry.IsSeparated.isSeparated_of_mono
add_to_ega "IV 1.2.2" AlgebraicGeometry.QuasiSeparated.of_comp
add_to_ega "IV 1.2.2"
  AlgebraicGeometry.instHasOfPostcompPropertySchemeQuasiSeparatedTopMorphismProperty
add_to_ega "IV 1.2.2" AlgebraicGeometry.instIsMultiplicativeSchemeQuasiSeparated
add_to_ega "IV 1.2.2" AlgebraicGeometry.instQuasiSeparatedFstScheme
add_to_ega "IV 1.2.2" "(iii), special case" AlgebraicGeometry.instQuasiSeparatedMorphismRestrict
add_to_ega "IV 1.2.2" AlgebraicGeometry.instQuasiSeparatedOfMonoScheme
add_to_ega "IV 1.2.2" "(iii), special case" AlgebraicGeometry.instQuasiSeparatedResLE
add_to_ega "IV 1.2.2" AlgebraicGeometry.instQuasiSeparatedSndScheme
add_to_ega "IV 1.2.2" "(ii), special case" AlgebraicGeometry.quasiSeparatedSpace_of_quasiSeparated
add_to_ega "IV 1.2.3" "more general" AlgebraicGeometry.Scheme.Hom.isQuasiSeparated_preimage
add_to_ega "IV 1.2.3" "(ii), necessity" AlgebraicGeometry.quasiSeparatedSpace_of_quasiSeparated
add_to_ega "IV 1.2.4" AlgebraicGeometry.QuasiCompact.of_comp
add_to_ega "IV 1.2.4" AlgebraicGeometry.instHasOfPostcompPropertySchemeQuasiCompactQuasiSeparated
add_to_ega "IV 1.2.4" "special case" AlgebraicGeometry.quasiCompact_iff_compactSpace
add_to_ega "IV 1.2.6" "necessity" AlgebraicGeometry.Scheme.Hom.isQuasiSeparated_preimage
add_to_ega "IV 1.2.6" "special case"
  AlgebraicGeometry.instHasAffinePropertyQuasiSeparatedQuasiSeparatedSpaceCarrierCarrierCommRingCat
add_to_ega "IV 1.2.6" "partial" AlgebraicGeometry.quasiSeparatedSpace_of_quasiSeparated
add_to_ega "IV 1.2.7" "special case" AlgebraicGeometry.Scheme.quasiSeparatedSpace_of_isOpenCover
add_to_ega "IV 1.2.7" "special case" AlgebraicGeometry.quasiSeparatedSpace_iff_forall_affineOpens
add_to_ega "IV 1.2.7" AlgebraicGeometry.quasiSeparatedSpace_iff_quasiCompact_prod_lift
add_to_ega "IV 1.2.7" AlgebraicGeometry.quasiSeparatedSpace_iff_quasiSeparated
add_to_ega "IV 1.2.7" IsRetrocompact
add_to_ega "IV 1.2.7" IsRetrocompact_iff_isSpectralMap_subtypeVal
add_to_ega "IV 1.2.7" "partial" IsSpectralMap.isRetrocompact_range
add_to_ega "IV 1.2.7" "special case" QuasiSeparatedSpace.of_isTopologicalBasis
add_to_ega "IV 1.2.8" "special case" AlgebraicGeometry.IsLocallyNoetherian.quasiSeparatedSpace
add_to_ega "IV 1.2.8" "special case" NoetherianSpace.to_quasiSeparatedSpace
add_to_ega "IV 1.2.9" "partial" CategoryTheory.Limits.BinaryCofan.IsColimit.hom_ext
add_to_ega "IV 1.2.9" CategoryTheory.Limits.coprod
add_to_ega "IV 1.2.9" CategoryTheory.Limits.coprod.desc
add_to_ega "IV 1.2.9" CategoryTheory.Limits.coprod.desc'
add_to_ega "IV 1.2.9" "partial" CategoryTheory.Limits.coprod.hom_ext
add_to_ega "IV 1.2.9" "partial" CategoryTheory.Limits.coprod.hom_ext_iff
add_to_ega "IV 1.2.9" "left restriction" CategoryTheory.Limits.coprod.inl_desc
add_to_ega "IV 1.2.9" "left restriction" CategoryTheory.Limits.coprod.inl_desc_assoc
add_to_ega "IV 1.2.9" "right restriction" CategoryTheory.Limits.coprod.inr_desc
add_to_ega "IV 1.2.9" "right restriction" CategoryTheory.Limits.coprod.inr_desc_assoc
add_to_ega "IV 1.3.1" AlgHom.FiniteType
add_to_ega "IV 1.3.1" AlgHom.FiniteType.comp
add_to_ega "IV 1.3.1" "special case" AlgHom.FiniteType.comp_surjective
add_to_ega "IV 1.3.1" Algebra.FiniteType
add_to_ega "IV 1.3.1" Algebra.FiniteType.baseChange
add_to_ega "IV 1.3.1" Algebra.FiniteType.iff_exists_generators
add_to_ega "IV 1.3.1" "more general" Algebra.FiniteType.iff_quotient_mvPolynomial
add_to_ega "IV 1.3.1" "more general" Algebra.FiniteType.iff_quotient_mvPolynomial'
add_to_ega "IV 1.3.1" "more general" Algebra.FiniteType.iff_quotient_mvPolynomial''
add_to_ega "IV 1.3.1" "Final algebra is S[X]" Algebra.FiniteType.instPolynomial
add_to_ega "IV 1.3.1" "more general" Algebra.FiniteType.trans
add_to_ega "IV 1.3.1" Algebra.Generators.comp
add_to_ega "IV 1.3.1" "partial" Algebra.Generators.finiteType
add_to_ega "IV 1.3.1" Algebra.Presentation.comp
add_to_ega "IV 1.3.1" "more general" Algebra.fg_trans'
add_to_ega "IV 1.3.1" "partial" MvPolynomial.algebraTensorAlgEquiv
add_to_ega "IV 1.3.1" "partial" MvPolynomial.quotientEquivQuotientMvPolynomial
add_to_ega "IV 1.3.1" "partial" MvPolynomial.rTensorAlgEquiv
add_to_ega "IV 1.3.1" "partial" MvPolynomial.rTensorAlgHom
add_to_ega "IV 1.3.1" "partial" MvPolynomial.scalarRTensorAlgEquiv
add_to_ega "IV 1.3.1" RingHom.FiniteType
add_to_ega "IV 1.3.1" RingHom.FiniteType.comp
add_to_ega "IV 1.3.1" RingHom.finiteType_isStableUnderBaseChange
add_to_ega "IV 1.3.3" "more general"
  AlgebraicGeometry.instIsLocallyNoetherianPullbackSchemeOfLocallyOfFiniteType
add_to_ega "IV 1.3.3" "more general"
  AlgebraicGeometry.instIsLocallyNoetherianPullbackSchemeOfLocallyOfFiniteType_1
add_to_ega "IV 1.3.3" "open subschemes" AlgebraicGeometry.instIsLocallyNoetherianToScheme
add_to_ega "IV 1.3.3" "members of an open cover" AlgebraicGeometry.instIsLocallyNoetherianXScheme
add_to_ega "IV 1.3.3" "special case" AlgebraicGeometry.isLocallyNoetherian_iff_openCover
add_to_ega "IV 1.3.3" "open immersions" AlgebraicGeometry.isLocallyNoetherian_of_isOpenImmersion
add_to_ega "IV 1.3.4" "(i), immersions" AlgebraicGeometry.IsImmersion.instLocallyOfFiniteType
add_to_ega "IV 1.3.4" "more general" AlgebraicGeometry.instIsMultiplicativeSchemeLocallyOfFiniteType
add_to_ega "IV 1.3.4" AlgebraicGeometry.instIsStableUnderCompositionSchemeLocallyOfFiniteType
add_to_ega "IV 1.3.4" AlgebraicGeometry.instLocallyOfFiniteTypeFstScheme
add_to_ega "IV 1.3.4" "(iii), special case"
  AlgebraicGeometry.instLocallyOfFiniteTypeMorphismRestrict
add_to_ega "IV 1.3.4" "(i), closed immersions"
  AlgebraicGeometry.instLocallyOfFiniteTypeOfIsClosedImmersion
add_to_ega "IV 1.3.4" AlgebraicGeometry.instLocallyOfFiniteTypeSndScheme
add_to_ega "IV 1.3.4" "(i), open immersions"
  AlgebraicGeometry.locallyOfFiniteType_of_isOpenImmersion
add_to_ega "IV 1.3.5" AlgebraicGeometry.instIsLocallyNoetherianPullbackSchemeOfLocallyOfFiniteType
add_to_ega "IV 1.3.5" AlgebraicGeometry.instIsLocallyNoetherianPullbackSchemeOfLocallyOfFiniteType_1
add_to_ega "IV 1.3.6" "more general"
  AlgebraicGeometry.instHasRingHomPropertyLocallyOfFiniteTypeFiniteType
add_to_ega "IV 1.3.6" "sufficiency" AlgebraicGeometry.locallyOfFiniteType_specOverSpec
add_to_ega "IV 1.3.8" Algebra.EssFiniteType
add_to_ega "IV 1.3.8" RingHom.EssFiniteType
add_to_ega "IV 1.3.9" Algebra.EssFiniteType.baseChange
add_to_ega "IV 1.3.9" Algebra.EssFiniteType.comp
add_to_ega "IV 1.3.9" "more general" Algebra.EssFiniteType.comp_iff
add_to_ega "IV 1.3.9" "clause (i), special case" Algebra.EssFiniteType.of_surjective
add_to_ega "IV 1.3.9" "more general" RingHom.EssFiniteType.comp_iff
add_to_ega "IV 1.3.10" Ideal.comap
add_to_ega "IV 1.3.10" "partial" IsLocalization.isLocalization_atPrime_localization_atPrime
add_to_ega "IV 1.3.10" IsLocalization.localizationLocalizationAtPrimeIsoLocalization
add_to_ega "IV 1.3.10" Localization.AtPrime
add_to_ega "IV 1.4.1" AlgHom.FinitePresentation
add_to_ega "IV 1.4.1" AlgHom.FinitePresentation.comp
add_to_ega "IV 1.4.1" AlgHom.FinitePresentation.of_finiteType
add_to_ega "IV 1.4.1" "more general" Algebra.EssFiniteType.isNoetherianRing
add_to_ega "IV 1.4.1" Algebra.FinitePresentation
add_to_ega "IV 1.4.1" Algebra.FinitePresentation.baseChange
add_to_ega "IV 1.4.1" Algebra.FinitePresentation.iff
add_to_ega "IV 1.4.1" "special case" Algebra.FinitePresentation.mvPolynomial
add_to_ega "IV 1.4.1" "special case" Algebra.FinitePresentation.mvPolynomial_of_finitePresentation
add_to_ega "IV 1.4.1" Algebra.FinitePresentation.of_finiteType
add_to_ega "IV 1.4.1" "C = B[T]" Algebra.FinitePresentation.polynomial
add_to_ega "IV 1.4.1" Algebra.FinitePresentation.trans
add_to_ega "IV 1.4.1" Algebra.Generators.comp
add_to_ega "IV 1.4.1" Algebra.Presentation.baseChange
add_to_ega "IV 1.4.1" Algebra.Presentation.comp
add_to_ega "IV 1.4.1" "partial" Algebra.Presentation.exists_presentation_fin
add_to_ega "IV 1.4.1" "partial" Algebra.Presentation.finitePresentation_of_isFinite
add_to_ega "IV 1.4.1" "partial" Algebra.Presentation.instFinitePresentationQuotientOfFinite
add_to_ega "IV 1.4.1" "partial" Algebra.Presentation.span_range_relation_eq_ker_baseChange
add_to_ega "IV 1.4.1" "more general" Module.Finite.of_submodule_quotient
add_to_ega "IV 1.4.1" MvPolynomial.isNoetherianRing
add_to_ega "IV 1.4.1" MvPolynomial.isNoetherianRing_fin
add_to_ega "IV 1.4.1" "n = 1" Polynomial.isNoetherianRing
add_to_ega "IV 1.4.1" RingHom.FinitePresentation
add_to_ega "IV 1.4.1" "more general" RingHom.FinitePresentation.of_finiteType
add_to_ega "IV 1.4.1" "more general" isNoetherianRing_of_fg
add_to_ega "IV 1.4.3" "clause (ii), affine case" AlgHom.FinitePresentation.comp
add_to_ega "IV 1.4.3" "(iii), special case" Algebra.FinitePresentation.baseChange
add_to_ega "IV 1.4.3" "more general" AlgebraicGeometry.IsLocalIso.eq_iInf
add_to_ega "IV 1.4.3" "more general" AlgebraicGeometry.IsLocalIso.le_of_isZariskiLocalAtSource
add_to_ega "IV 1.4.3"
  AlgebraicGeometry.instIsStableUnderCompositionSchemeLocallyOfFinitePresentation
add_to_ega "IV 1.4.3" AlgebraicGeometry.instLocallyOfFinitePresentationFstScheme
add_to_ega "IV 1.4.3" "(iii), special case"
  AlgebraicGeometry.instLocallyOfFinitePresentationMorphismRestrict
add_to_ega "IV 1.4.3" "(iii), special case" AlgebraicGeometry.instLocallyOfFinitePresentationResLE
add_to_ega "IV 1.4.3" AlgebraicGeometry.instLocallyOfFinitePresentationSndScheme
add_to_ega "IV 1.4.3" "(ii), affine schemes" RingHom.FinitePresentation.comp
add_to_ega "IV 1.4.3" "(v), affine schemes" RingHom.FinitePresentation.of_comp_finiteType
add_to_ega "IV 1.4.3" "(iii), affine schemes" RingHom.finitePresentation_isStableUnderBaseChange
add_to_ega "IV 1.4.3" "(iii), special case" RingHom.finitePresentation_localizationPreserves
add_to_ega "IV 1.4.3" "(ii), affine schemes" RingHom.finitePresentation_stableUnderComposition
add_to_ega "IV 1.4.4" "necessity" Algebra.FinitePresentation.ker_fG_of_surjective
add_to_ega "IV 1.4.4" "necessity" Algebra.FinitePresentation.ker_fg_of_mvPolynomial
add_to_ega "IV 1.4.4" "sufficiency" Algebra.FinitePresentation.of_surjective
add_to_ega "IV 1.4.4" "special case" Algebra.FinitePresentation.quotient
add_to_ega "IV 1.4.4" "necessity" Algebra.Generators.fg_ker_of_finitePresentation
add_to_ega "IV 1.4.4" "sufficiency" Algebra.Presentation.finitePresentation_of_isFinite
add_to_ega "IV 1.4.4" "sufficiency" Algebra.Presentation.instFinitePresentationQuotientOfFinite
add_to_ega "IV 1.4.6" AlgebraicGeometry.LocallyOfFinitePresentation.SpecMap_iff
add_to_ega "IV 1.4.6" "necessity" AlgebraicGeometry.Scheme.Hom.finitePresentation_appTop
add_to_ega "IV 1.4.7" "sufficiency" Algebra.FinitePresentation.of_finitePresentation
add_to_ega "IV 1.4.7" Module.FinitePresentation.iff_finitePresentation_of_finite
add_to_ega "IV 1.4.7" "necessity" Module.FinitePresentation.of_finite_of_finitePresentation
add_to_ega "IV 1.4.7.1" Module.Finite.exists_free_surjective
add_to_ega "IV 1.5.4" "affine case of (ii)" AlgHom.FiniteType.comp
add_to_ega "IV 1.5.4" "special case" AlgHom.FiniteType.of_comp_finiteType
add_to_ega "IV 1.5.4" "(iii), special case" Algebra.FiniteType.baseChange
add_to_ega "IV 1.5.4" "more general" AlgebraicGeometry.IsClosedImmersion.eq_isFinite_inf_mono
add_to_ega "IV 1.5.4" "more general" AlgebraicGeometry.IsClosedImmersion.iff_isFinite_and_mono
add_to_ega "IV 1.5.4" "more general" AlgebraicGeometry.IsClosedImmersion.iff_isProper_and_mono
add_to_ega "IV 1.5.4" "more general" AlgebraicGeometry.IsFinite.instOfIsClosedImmersion
add_to_ega "IV 1.5.4" "(i)" AlgebraicGeometry.IsImmersion.instLocallyOfFiniteType
add_to_ega "IV 1.5.4" "(v)" AlgebraicGeometry.QuasiCompact.of_comp
add_to_ega "IV 1.5.4" "special case"
  AlgebraicGeometry.instQuasiCompactOfIsLocallyNoetherianOfIsOpenImmersion
add_to_ega "IV 1.5.4" "(i)" AlgebraicGeometry.quasiCompact_of_noetherianSpace_source
add_to_ega "IV 1.5.4" "(ii) for affine schemes" RingHom.FiniteType.comp
add_to_ega "IV 1.5.4" "(ii), special case" RingHom.FiniteType.comp_surjective
add_to_ega "IV 1.5.4" "special case" RingHom.FiniteType.of_comp_finiteType
add_to_ega "IV 1.5.4" "(iii) in the affine case" RingHom.finiteType_isStableUnderBaseChange
add_to_ega "IV 1.5.4" "(ii) for affine schemes" RingHom.finiteType_stableUnderComposition
add_to_ega "IV 1.5.5" "partial"
  AlgebraicGeometry.instIsLocallyNoetherianPullbackSchemeOfLocallyOfFiniteType
add_to_ega "IV 1.5.5" "partial"
  AlgebraicGeometry.instIsLocallyNoetherianPullbackSchemeOfLocallyOfFiniteType_1
add_to_ega "IV 1.5.7" "more general" AlgebraicGeometry.LocallyOfFiniteType.finiteType_appLE
add_to_ega "IV 1.5.7" "more general" AlgebraicGeometry.Scheme.Hom.finiteType_appLE
add_to_ega "IV 1.5.7" "sufficiency" AlgebraicGeometry.locallyOfFiniteType_specOverSpec
add_to_ega "IV 1.6.2" "(ii), affine case" AlgHom.FinitePresentation.comp
add_to_ega "IV 1.6.2" "(iii), special case" Algebra.FinitePresentation.baseChange
add_to_ega "IV 1.6.2" "(ii), affine case" RingHom.FinitePresentation.comp
add_to_ega "IV 1.6.2" "(v), affine case" RingHom.FinitePresentation.of_comp_finiteType
add_to_ega "IV 1.6.2" "(iii), affine case" RingHom.finitePresentation_isStableUnderBaseChange
add_to_ega "IV 1.6.2" "(ii), affine case" RingHom.finitePresentation_stableUnderComposition
add_to_ega "IV 1.6.3" AlgebraicGeometry.LocallyOfFinitePresentation.SpecMap_iff
add_to_ega "IV 1.6.3" "necessity"
  AlgebraicGeometry.LocallyOfFinitePresentation.finitePresentation_appLE
add_to_ega "IV 1.6.3" "necessity" AlgebraicGeometry.Scheme.Hom.finitePresentation_appLE
add_to_ega "IV 1.6.3" "necessity" AlgebraicGeometry.Scheme.Hom.finitePresentation_appTop
add_to_ega "IV 1.8.1" "special case" AlgebraicGeometry.IsAffineOpen.isCompact
add_to_ega "IV 1.8.1" "more general"
  AlgebraicGeometry.QuasiCompactCover.exists_isAffineOpen_of_isCompact
add_to_ega "IV 1.8.1" "more general" AlgebraicGeometry.Scheme.OpenCover.compactSpace
add_to_ega "IV 1.8.1" AlgebraicGeometry.isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens
add_to_ega "IV 1.8.1" "affine ambient scheme"
  AlgebraicGeometry.isCompact_and_isOpen_iff_finite_and_eq_biUnion_basicOpen
add_to_ega "IV 1.8.1" "more general" AlgebraicGeometry.quasiCompact_iff_forall_isAffineOpen
add_to_ega "IV 1.8.1" "partial" IsCompact.isConstructible
add_to_ega "IV 1.8.1" "partial" Topology.IsConstructible.isLocallyConstructible
add_to_ega "IV 1.8.1" "more general"
  Topology.IsLocallyConstructible.iff_isConstructible_of_isOpenCover
add_to_ega "IV 1.8.1" "partial" Topology.IsLocallyConstructible.inter_of_isOpen_isCompact
add_to_ega "IV 1.8.1" "partial" Topology.IsLocallyConstructible.isConstructible
add_to_ega "IV 1.8.1" "partial"
  Topology.IsLocallyConstructible.isConstructible_of_subset_of_isCompact
add_to_ega "IV 1.8.1" "special case" noetherianSpace_isRetrocompact
add_to_ega "IV 1.8.2" AlgebraicGeometry.Scheme.Hom.isConstructible_preimage
add_to_ega "IV 1.8.2" "special case" Topology.IsConstructible.preimage_of_isOpenEmbedding
add_to_ega "IV 1.8.2" "special case" Topology.IsLocallyConstructible.preimage_of_isOpenEmbedding
add_to_ega "IV 1.8.2" "special case" isConstructibleSet_preimage
add_to_ega "IV 1.8.4" "special case" AlgebraicGeometry.Scheme.Hom.isConstructible_image
add_to_ega "IV 1.8.4" "more general" AlgebraicGeometry.Scheme.Hom.isLocallyConstructible_image
add_to_ega "IV 1.8.4" "Affine schemes; Z = X" PrimeSpectrum.isConstructible_range_comap
add_to_ega "IV 1.8.4" "special case" chevalley_mvPolynomial_mvPolynomial
add_to_ega "IV 1.8.4.1" "more general" AlgebraicGeometry.Scheme.Hom.isConstructible_image
add_to_ega "IV 1.8.4.1" "more general" AlgebraicGeometry.Scheme.Hom.isLocallyConstructible_image
add_to_ega "IV 1.8.4.1" "affine source" PrimeSpectrum.isConstructible_range_comap
add_to_ega "IV 1.8.5" "more general" AlgebraicGeometry.Scheme.Hom.isConstructible_image
add_to_ega "IV 1.8.5" "more general" AlgebraicGeometry.Scheme.Hom.isLocallyConstructible_image
add_to_ega "IV 1.8.5" "special case" PrimeSpectrum.isConstructible_range_comap
add_to_ega "IV 1.8.5.1" "special case" IsAlgClosed.lift
add_to_ega "IV 1.8.6" "affine case" Ideal.Fiber
add_to_ega "IV 1.8.7" AlgebraicGeometry.Scheme.Hom.fiber
add_to_ega "IV 1.8.7" "partial" AlgebraicGeometry.Scheme.Hom.fiberHomeo
add_to_ega "IV 1.8.7" "special case" AlgebraicGeometry.Spec.fiberToSpecResidueFieldIso
add_to_ega "IV 1.8.7.1" AlgebraicGeometry.UniversallyInjective.iff_diagonal
add_to_ega "IV 1.8.7.1" "more general" AlgebraicGeometry.isSeparated_of_injective
add_to_ega "IV 1.8.7.1" AlgebraicGeometry.universallyInjective_eq_diagonal
add_to_ega "IV 1.9.1" "Necessity" CommRingCat.FilteredColimits.nontrivial
add_to_ega "IV 1.9.2" "more general" AlgebraicGeometry.Scheme.Spec
add_to_ega "IV 1.9.2" "more general" AlgebraicGeometry.Spec.map
add_to_ega "IV 1.9.2" AlgebraicGeometry.algSpec
add_to_ega "IV 1.9.2" AlgebraicGeometry.specOverSpec
add_to_ega "IV 1.9.3.2" "Algebraic part"
  CategoryTheory.Limits.CoproductsFromFiniteFiltered.liftToFinsetColimitCocone
add_to_ega "IV 1.9.3.2" "partial"
  CategoryTheory.Limits.ProductsFromFiniteCofiltered.liftToFinsetLimitCone
add_to_ega "IV 1.9.5" "(v), special case" AlgebraicGeometry.isRetrocompact_basicOpen
add_to_ega "IV 1.9.5" "(vi), special case" PrimeSpectrum.BasicConstructibleSetData.toSet_map
add_to_ega "IV 1.9.5" "(vi), special case" PrimeSpectrum.ConstructibleSetData.toSet_map
add_to_ega "IV 1.9.5" "(viii), special case" PrimeSpectrum.isConstructible_range_comap
add_to_ega "IV 1.9.6" "more general" AlgebraicGeometry.IsLocallyNoetherian.quasiSeparatedSpace
add_to_ega "IV 1.9.6" AlgebraicGeometry.Scheme.fromSpecResidueField
add_to_ega "IV 1.9.6" "partial" AlgebraicGeometry.Scheme.range_fromSpecResidueField
add_to_ega "IV 1.9.6" "more general" NoetherianSpace.to_quasiSeparatedSpace
add_to_ega "IV 1.9.6" "special case" PrimeSpectrum.instQuasiSeparatedSpace
add_to_ega "IV 1.9.13" WithConstructibleTopology
add_to_ega "IV 1.9.13" constructibleTopology
add_to_ega "IV 1.10.3" "b) ⇒ a), special case" AlgebraicGeometry.isOpenMap_of_generalizingMap
add_to_ega "IV 1.10.4" "b) ⇒ a)" AlgebraicGeometry.isOpenMap_of_generalizingMap
add_to_ega "IV 1.10.4" DenseRange
add_to_ega "IV 1.10.4" IsOpenMap
add_to_ega "IV 1.10.4" irreducibleComponents
add_to_ega "IV 2.1.1" AlgebraicGeometry.Flat.iff_flat_stalkMap
add_to_ega "IV 2.1.1" "partial" AlgebraicGeometry.Flat.of_stalkMap
add_to_ega "IV 2.1.1" "partial" AlgebraicGeometry.Flat.stalkMap
add_to_ega "IV 2.1.2" "Case M = B" AlgebraicGeometry.Flat.SpecMap_iff
add_to_ega "IV 2.1.2" "partial" AlgebraicGeometry.Scheme.Hom.flat_appTop
add_to_ega "IV 2.1.4" AlgebraicGeometry.Flat.instFstScheme
add_to_ega "IV 2.1.4" AlgebraicGeometry.Flat.instSndScheme
add_to_ega "IV 2.1.4" "affine case of" CommRingCat.instIsStableUnderCobaseChangeFlat
add_to_ega "IV 2.1.4" "special case" Module.Flat.isBaseChange
add_to_ega "IV 2.1.4" "affine case of" RingHom.Flat.isStableUnderBaseChange
add_to_ega "IV 2.1.5" "global case h = id" AlgebraicGeometry.Flat.instFstScheme
add_to_ega "IV 2.1.5" "special case" AlgebraicGeometry.Flat.instIsMultiplicativeScheme
add_to_ega "IV 2.1.5" "global case h = id" AlgebraicGeometry.Flat.instSndScheme
add_to_ega "IV 2.1.5" "special case" Module.Flat.instTensorProduct
add_to_ega "IV 2.1.6" "more general" AlgebraicGeometry.Flat.instIsMultiplicativeScheme
add_to_ega "IV 2.1.6" AlgebraicGeometry.Flat.instIsStableUnderCompositionScheme
add_to_ega "IV 2.1.6" "special case" RingHom.Flat.stableUnderComposition
add_to_ega "IV 2.1.9" "Z^{i+1}(L) = Coker(d^i)" HomologicalComplex.opcyclesIsCokernel
add_to_ega "IV 2.1.10" CategoryTheory.ShortComplex.cycles
add_to_ega "IV 2.1.10" HomologicalComplex.cycles
add_to_ega "IV 2.1.10" "special case" LinearMap.kerLTensorEquivOfSurjective
add_to_ega "IV 2.1.12" Module.Flat
add_to_ega "IV 2.2.1" "special case" Ideal.Fiber
add_to_ega "IV 2.2.2" "partial" RingHom.FaithfullyFlat.isStableUnderBaseChange
add_to_ega "IV 2.2.3" "M = B"
  AlgebraicGeometry.Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine
add_to_ega "IV 2.2.3" "M = B" AlgebraicGeometry.flat_and_surjective_SpecMap_iff
add_to_ega "IV 2.2.3" "M = B" Module.FaithfullyFlat.of_comap_surjective
add_to_ega "IV 2.2.3" "M = B" RingHom.FaithfullyFlat.eq_and
add_to_ega "IV 2.2.3" "M = B" RingHom.FaithfullyFlat.iff_flat_and_comap_surjective
add_to_ega "IV 2.2.4" "special case" RingHom.FaithfullyFlat
add_to_ega "IV 2.2.5" "special case"
  AlgebraicGeometry.Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine
add_to_ega "IV 2.2.5" "special case" AlgebraicGeometry.flat_and_surjective_SpecMap_iff
add_to_ega "IV 2.2.5" "special case" RingHom.FaithfullyFlat.eq_and
add_to_ega "IV 2.2.5" "special case" RingHom.FaithfullyFlat.iff_flat_and_comap_surjective
add_to_ega "IV 2.2.6" "special case" RingHom.FaithfullyFlat.eq_and
add_to_ega "IV 2.2.6" "special case" RingHom.FaithfullyFlat.iff_flat_and_comap_surjective
add_to_ega "IV 2.2.7" "partial" IsTensorProduct.map_id_injective_of_flat_left
add_to_ega "IV 2.2.7" "special case" Module.FaithfullyFlat.iff_exact_iff_rTensor_exact
add_to_ega "IV 2.2.7" "partial" Module.FaithfullyFlat.iff_flat_and_lTensor_faithful
add_to_ega "IV 2.2.7" "partial" Module.FaithfullyFlat.iff_flat_and_lTensor_reflects_triviality
add_to_ega "IV 2.2.7" "partial" Module.FaithfullyFlat.iff_flat_and_rTensor_faithful
add_to_ega "IV 2.2.7" "partial" Module.FaithfullyFlat.iff_flat_and_rTensor_reflects_triviality
add_to_ega "IV 2.2.7" "special case" Module.FaithfullyFlat.lTensor_bijective_iff_bijective
add_to_ega "IV 2.2.7" "special case" Module.FaithfullyFlat.lTensor_exact_iff_exact
add_to_ega "IV 2.2.7" "special case" Module.FaithfullyFlat.lTensor_injective_iff_injective
add_to_ega "IV 2.2.7" "partial" Module.FaithfullyFlat.lTensor_nontrivial
add_to_ega "IV 2.2.7" "partial" Module.FaithfullyFlat.lTensor_reflects_exact
add_to_ega "IV 2.2.7" "partial" Module.FaithfullyFlat.lTensor_reflects_triviality
add_to_ega "IV 2.2.7" "special case" Module.FaithfullyFlat.lTensor_surjective_iff_surjective
add_to_ega "IV 2.2.7" "special case" Module.FaithfullyFlat.nontrivial_tensorProduct_iff_left
add_to_ega "IV 2.2.7" "special case" Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right
add_to_ega "IV 2.2.7" "special case" Module.FaithfullyFlat.rTensor_exact_iff_exact
add_to_ega "IV 2.2.7" "partial" Module.FaithfullyFlat.rTensor_nontrivial
add_to_ega "IV 2.2.7" "partial" Module.FaithfullyFlat.rTensor_reflects_exact
add_to_ega "IV 2.2.7" "partial" Module.FaithfullyFlat.rTensor_reflects_triviality
add_to_ega "IV 2.2.7" "special case" Module.FaithfullyFlat.subsingleton_tensorProduct_iff_left
add_to_ega "IV 2.2.7" "special case" Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right
add_to_ega "IV 2.2.7" "special case" Module.FaithfullyFlat.zero_iff_lTensor_zero
add_to_ega "IV 2.2.7" "special case" Module.FaithfullyFlat.zero_iff_rTensor_zero
add_to_ega "IV 2.2.7" "partial" Module.Flat.iff_lTensor_exact'
add_to_ega "IV 2.2.7" "partial" Module.Flat.iff_lTensor_injectiveₛ
add_to_ega "IV 2.2.7" "partial" Module.Flat.iff_lTensor_preserves_injective_linearMapₛ
add_to_ega "IV 2.2.7" "partial" Module.Flat.iff_rTensor_exact
add_to_ega "IV 2.2.7" "partial" Module.Flat.iff_rTensor_injectiveₛ
add_to_ega "IV 2.2.7" "partial" Module.Flat.iff_rTensor_preserves_injective_linearMap
add_to_ega "IV 2.2.7" "partial" Module.Flat.lTensor_exact
add_to_ega "IV 2.2.7" "partial" Module.Flat.lTensor_preserves_injective_linearMap
add_to_ega "IV 2.2.7" "partial" Module.Flat.rTensor_exact
add_to_ega "IV 2.2.7" "partial" Module.Flat.rTensor_preserves_injective_linearMap
add_to_ega "IV 2.2.7" "special case" Module.Invertible.lTensor_surjective_iff
add_to_ega "IV 2.2.7" "partial" ModuleCat.reflectsIsomorphisms_extendScalars_of_faithfullyFlat
add_to_ega "IV 2.2.8" "Affine source and target" Module.FaithfullyFlat.tensorProduct_mk_injective
add_to_ega "IV 2.2.8" "special case" RingHom.FaithfullyFlat.injective
add_to_ega "IV 2.2.9" "partial" AlgebraicGeometry.Flat.iff_flat_stalkMap
add_to_ega "IV 2.2.9" "partial" AlgebraicGeometry.Flat.stalkMap
add_to_ega "IV 2.2.10" "special case" AlgebraicGeometry.Flat.instFstScheme
add_to_ega "IV 2.2.11" "(iii), special case" AlgebraicGeometry.Flat.instIsMultiplicativeScheme
add_to_ega "IV 2.2.11" "(iii), special case"
  AlgebraicGeometry.Flat.instIsStableUnderCompositionScheme
add_to_ega "IV 2.2.11" "(iii), special case" Module.Flat.of_flat_tensorProduct
add_to_ega "IV 2.2.11" "(i), special case" RingHom.FaithfullyFlat.isStableUnderBaseChange
add_to_ega "IV 2.2.13" "(iii)" AlgebraicGeometry.Flat.instIsMultiplicativeScheme
add_to_ega "IV 2.2.13" "(iii)" AlgebraicGeometry.Flat.instIsStableUnderCompositionScheme
add_to_ega "IV 2.2.13" "(i)" AlgebraicGeometry.Flat.instSndScheme
add_to_ega "IV 2.2.13" "(i) for affine schemes" RingHom.FaithfullyFlat.isStableUnderBaseChange
add_to_ega "IV 2.2.13" "(i)" RingHom.Flat.isStableUnderBaseChange
add_to_ega "IV 2.2.13" "(iii)" RingHom.Flat.stableUnderComposition
add_to_ega "IV 2.2.14" "affine source and target"
  Submodule.IsNoetherian.of_isNoetherian_tensorProduct_of_faithfullyFlat
add_to_ega "IV 2.2.15" "special case" Ideal.map_injective_of_faithfullyFlat
add_to_ega "IV 2.2.16" "special case"
  AlgebraicGeometry.instFaithfulOverSchemePullbackOfSurjectiveOfFlatOfLocallyOfFinitePresentation
add_to_ega "IV 2.2.16" "special case"
  AlgebraicGeometry.instFaithfulOverSchemePullbackOfSurjectiveOfFlatOfQuasiCompact
add_to_ega "IV 2.2.17" "partial" Module.FaithfullyFlat.tensorProduct_mk_injective
add_to_ega "IV 2.2.17" "partial" Module.exists_basis_of_span_of_flat
add_to_ega "IV 2.2.17" "partial" Module.free_of_flat_of_isLocalRing
add_to_ega "IV 2.2.17" "partial" Module.nonempty_basis_of_flat_of_finrank_eq
add_to_ega "IV 2.3.2" "special case" AlgebraicGeometry.IsSchemeTheoreticallyDominant.of_isPullback
add_to_ega "IV 2.3.2" "special case" AlgebraicGeometry.IsSchemeTheoreticallyDominant.pullbackFst
add_to_ega "IV 2.3.2" "special case" AlgebraicGeometry.IsSchemeTheoreticallyDominant.pullbackSnd
add_to_ega "IV 2.3.2" "Factorization f = j ∘ g" AlgebraicGeometry.Scheme.Hom.toImageAux_spec
add_to_ega "IV 2.3.2" "more general" AlgebraicGeometry.Scheme.Hom.toImage_imageι_assoc
add_to_ega "IV 2.3.2" "special case" AlgebraicGeometry.specTargetImageFactorization
add_to_ega "IV 2.3.4" "(i), special case" AlgebraicGeometry.Flat.generalizingMap
add_to_ega "IV 2.3.5" "special case" AlgebraicGeometry.Flat.generalizingMap
add_to_ega "IV 2.3.5" "(iii), special case"
  AlgebraicGeometry.GeometricallyIrreducible.irreducibleSpace
add_to_ega "IV 2.3.5" "(ii), special case"
  AlgebraicGeometry.Scheme.Hom.irreducibleComponentsEquiv_apply_coe
add_to_ega "IV 2.3.5" "(iii), special case"
  AlgebraicGeometry.instIrreducibleSpaceCarrierCarrierCommRingCatPullbackSchemeOfGeometricallyIrreducibleOfUniversallyOpen
add_to_ega "IV 2.3.5" "(iii), special case" IsIrreducible.preimage_of_isPreirreducible_fiber
add_to_ega "IV 2.3.5" "(ii), special case" image_mem_irreducibleComponents_of_isPreirreducible_fiber
add_to_ega "IV 2.3.6" "(iii), special case" Algebra.QuasiFinite.iff_finite_comap_preimage_singleton
add_to_ega "IV 2.3.6" "(iii)" AlgebraicGeometry.Scheme.Hom.finite_preimage_singleton
add_to_ega "IV 2.3.6" "special case" AlgebraicGeometry.finite_irreducibleComponents_of_isNoetherian
add_to_ega "IV 2.3.6" "(iii)" AlgebraicGeometry.locallyQuasiFinite_iff_finite_preimage_singleton
add_to_ega "IV 2.3.6" "special case" TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
add_to_ega "IV 2.3.7" "(i)" AlgebraicGeometry.instQuasiCompactFstScheme
add_to_ega "IV 2.3.7" "(i)" AlgebraicGeometry.instQuasiCompactSndScheme
add_to_ega "IV 2.3.12" "special case" AlgebraicGeometry.Flat.isQuotientMap_of_surjective
add_to_ega "IV 2.3.13" "more general" AlgebraicGeometry.IsImmersion.instMapDescScheme
add_to_ega "IV 2.4.2" AlgebraicGeometry.UniversallyOpen
add_to_ega "IV 2.4.3" "(ii), universally open"
  AlgebraicGeometry.UniversallyOpen.instIsMultiplicativeScheme
add_to_ega "IV 2.4.3" "(ii), universally open"
  AlgebraicGeometry.UniversallyOpen.instIsStableUnderCompositionScheme
add_to_ega "IV 2.4.3" "(vii)" AlgebraicGeometry.UniversallyOpen.instIsZariskiLocalAtTarget
add_to_ega "IV 2.4.3" AlgebraicGeometry.UniversallyOpen.instOfIsOpenImmersion
add_to_ega "IV 2.4.3" "(ii), universally closed"
  AlgebraicGeometry.instIsMultiplicativeSchemeUniversallyClosed
add_to_ega "IV 2.4.3" "partial" AlgebraicGeometry.instUniversallyClosedMorphismRestrict
add_to_ega "IV 2.4.3" "(ii)" AlgebraicGeometry.universallyClosedTypeComp
add_to_ega "IV 2.4.3" "(iii)" AlgebraicGeometry.universallyClosed_snd
add_to_ega "IV 2.4.3" "more general"
  CategoryTheory.MorphismProperty.IsStableUnderComposition.universally
add_to_ega "IV 2.4.7" AlgebraicGeometry.AffineSpace
add_to_ega "IV 2.4.7" "special case" AlgebraicGeometry.AffineSpace.SpecIso
add_to_ega "IV 2.4.7" "special case" AlgebraicGeometry.AffineSpace.isoOfIsAffine
add_to_ega "IV 2.4.7" AlgebraicGeometry.AffineSpace.over
add_to_ega "IV 2.4.9" "special case"
  AlgebraicGeometry.instUniversallyOpenOfIsIntegralOfSubsingletonCarrierCarrierCommRingCat
add_to_ega "IV 2.4.11" "dense subsets E" Dense.preimage
add_to_ega "IV 2.4.11" "partial" IsOpenMap.clusterPt_comap
add_to_ega "IV 2.4.11" "more general" IsOpenMap.preimage_closure_eq_closure_preimage
add_to_ega "IV 2.4.11" "partial" IsOpenMap.preimage_closure_subset_closure_preimage
add_to_ega "IV 2.4.11" "open embeddings" OpenPartialHomeomorph.IsImage.closure
add_to_ega "IV 2.4.11" "open embeddings" OpenPartialHomeomorph.preimage_closure
add_to_ega "IV 2.5.1" "special case" AlgebraicGeometry.Flat.instSndScheme
add_to_ega "IV 2.5.1" "special case" Module.Flat.of_flat_tensorProduct
add_to_ega "IV 2.5.1" "special case" RingHom.FaithfullyFlat.isStableUnderBaseChange
add_to_ega "IV 2.5.2" "clause (i), special case"
  Module.Finite.of_finite_tensorProduct_of_faithfullyFlat
add_to_ega "IV 2.5.3" "special case" Ideal.FG.of_FG_map_of_faithfullyFlat
add_to_ega "IV 2.5.3" Module.Finite
add_to_ega "IV 2.5.3" "partial" Module.Finite.of_finite_tensorProduct_of_faithfullyFlat
add_to_ega "IV 2.5.3" Module.FinitePresentation
add_to_ega "IV 2.5.3" "special case" RingHom.Finite.codescendsAlong_faithfullyFlat
add_to_ega "IV 2.5.4.1" "case N' = A'" Module.FaithfullyFlat.lTensor_surjective_iff_surjective
add_to_ega "IV 2.5.4.1" "case P = A" Module.FaithfullyFlat.surjective_of_tensorProduct
add_to_ega "IV 2.5.4.1" "case P = A" RingHom.FaithfullyFlat.codescendsAlong_surjective
add_to_ega "IV 2.5.5" "affine fiber module" Ideal.Fiber
add_to_ega "IV 2.5.5.1" "special case" IsLocalRing.length_baseChange
add_to_ega "IV 2.5.5.3" "special case" IsLocalRing.length_baseChange
add_to_ega "IV 2.5.5.4" "more general" Submodule.FG.eq_bot_of_le_jacobson_smul
add_to_ega "IV 2.5.5.4" "more general"
  Submodule.eq_bot_of_set_smul_eq_of_subset_jacobson_annihilator
add_to_ega "IV 2.5.5.4" "more general"
  Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul
add_to_ega "IV 2.5.6" "partial" CategoryTheory.End.mulActionLeft
add_to_ega "IV 2.5.6" CategoryTheory.moduleEndLeft
add_to_ega "IV 2.5.7" "(i), b′ ⇒ b under (i)" IsNoetherian.bijective_of_surjective_endomorphism
add_to_ega "IV 2.5.7" "(i), b′ ⇒ b under (i)" IsNoetherian.injective_of_surjective_endomorphism
add_to_ega "IV 2.5.7" "(i), b′ ⇒ b under (i)" IsNoetherian.injective_of_surjective_of_injective
add_to_ega "IV 2.5.7" "(i), b′ ⇒ b under (i)" IsNoetherian.injective_of_surjective_of_submodule
add_to_ega "IV 2.5.8" "partial" TensorProduct
add_to_ega "IV 2.5.8.1" "Case A = B = K a field" FGModuleCat.instFiniteHom
add_to_ega "IV 2.5.8.1" "Case A = B = K a field" FGModuleCat.instFiniteHomModuleCatObjIsFG
add_to_ega "IV 2.5.8.1" "(i), special case" isNoetherian_linearMap
add_to_ega "IV 2.5.8.2" "special case" IsBaseChange.linearMapLeftRight
add_to_ega "IV 2.5.8.2" "special case" IsBaseChange.linearMapRightBaseChangeEquiv
add_to_ega "IV 2.5.8.2" "more general" IsBaseChange.linearMapRightBaseChangeHom
add_to_ega "IV 2.5.8.2" LinearMap.tensorProduct
add_to_ega "IV 2.5.8.6" "partial" IsBaseChange.end
add_to_ega "IV 2.5.8.6" "partial" IsBaseChange.linearMapLeftRight
add_to_ega "IV 2.5.8.6" "partial" IsBaseChange.linearMapRight
add_to_ega "IV 2.5.8.6" "partial" IsBaseChange.linearMapRightBaseChangeEquiv
add_to_ega "IV 2.5.8.7" "(i), special case" LinearMap.finiteDimensional'
add_to_ega "IV 2.5.8.7" "more general" Module.FaithfullyFlat.lTensor_bijective_iff_bijective
add_to_ega "IV 2.5.8.7" "partial" Module.FaithfullyFlat.lTensor_injective_iff_injective
add_to_ega "IV 2.5.8.7" "partial" Module.FaithfullyFlat.lTensor_surjective_iff_surjective
add_to_ega "IV 2.5.8.7" ModuleCat.reflectsIsomorphisms_extendScalars_of_faithfullyFlat
add_to_ega "IV 2.5.8.8" "for Artinian B" IsArtinianRing.isSemisimpleRing_iff_jacobson
add_to_ega "IV 2.5.8.8" "N = 0 implies semisimple" IsArtinianRing.isSemisimpleRing_of_isReduced
add_to_ega "IV 2.5.8.8" "more general" IsArtinianRing.of_finite
add_to_ega "IV 2.5.8.8" "special case" IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed
add_to_ega "IV 2.5.8.8" "special case" IsSimpleRing.isField_center
add_to_ega "IV 2.5.8.8" Module.Projective
add_to_ega "IV 2.5.8.8" "special case" Module.finite_iff_isArtinianRing
add_to_ega "IV 2.5.8.8" "partial" RingHom.FaithfullyFlat.isStableUnderBaseChange
add_to_ega "IV 2.5.8.8" Subalgebra.center
add_to_ega "IV 2.5.8.8" "partial, special case"
  Submodule.exists_injOn_mkQ_image_span_eq_of_span_eq_map_mkQ_of_le_jacobson_bot
add_to_ega "IV 2.5.8.8" "partial, special case" Submodule.exists_mem_addIdeal_and_span_image_eq_top
add_to_ega "IV 2.5.8.8" "partial, special case"
  Submodule.span_image_eq_top_of_span_image_toLocalizedQuotient'_eq_top
add_to_ega "IV 2.5.8.8" Subring.center
add_to_ega "IV 2.5.8.9" "the case B = A" FiniteDimensional.nonempty_linearEquiv_iff_finrank_eq
add_to_ega "IV 2.5.8.9" "special case" FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
add_to_ega "IV 2.5.8.9" "partial" IsBaseChange.finrank_eq
add_to_ega "IV 2.5.8.9" "partial" IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule
add_to_ega "IV 2.5.8.9" "partial" IsSemisimpleRing.isSemisimpleModule
add_to_ega "IV 2.5.8.9" "the equalities [W'" Module.finrank_baseChange
add_to_ega "IV 2.5.8.9" "partial" directSum_simple_module_over_simple_algebra
add_to_ega "IV 2.5.8.9" "more general" directSum_simple_module_over_simple_algebra'
add_to_ega "IV 2.5.8.9" "partial" directSum_simple_module_over_simple_ring
add_to_ega "IV 2.5.8.9" "more general" linearEquiv_iff_finrank_eq_over_simple_ring
add_to_ega "IV 2.5.8.9" "special case" linearEquiv_of_isSimpleModule_over_simple_ring
add_to_ega "IV 2.6.1" "clause (i), special case"
  AlgebraicGeometry.Flat.surjective_descendsAlong_surjective_inf_flat_inf_quasicompact
add_to_ega "IV 2.6.1" "(ii), special case" AlgebraicGeometry.injective_isZariskiLocalAtTarget
add_to_ega "IV 2.6.2" "(ii), special case"
  AlgebraicGeometry.descendsAlong_universallyClosed_surjective_inf_flat_inf_quasicompact
add_to_ega "IV 2.6.2" "(i), special case"
  AlgebraicGeometry.descendsAlong_universallyOpen_surjective_inf_flat_inf_quasicompact
add_to_ega "IV 2.6.4" "(i)" AlgebraicGeometry.UniversallyOpen.fst
add_to_ega "IV 2.6.4" "(i)" AlgebraicGeometry.UniversallyOpen.snd
add_to_ega "IV 2.6.4" "(ii)"
  AlgebraicGeometry.descendsAlong_universallyClosed_surjective_inf_flat_inf_quasicompact
add_to_ega "IV 2.6.4" "(i)"
  AlgebraicGeometry.descendsAlong_universallyOpen_surjective_inf_flat_inf_quasicompact
add_to_ega "IV 2.6.4" "(v)" AlgebraicGeometry.instQuasiCompactFstScheme
add_to_ega "IV 2.6.4" "necessity in (v)" AlgebraicGeometry.instQuasiCompactSndScheme
add_to_ega "IV 2.7.1" "special case"
  Algebra.FiniteType.of_finiteType_tensorProduct_of_faithfullyFlat
add_to_ega "IV 2.7.1" "implication" AlgebraicGeometry.IsIntegralHom.instFstScheme
add_to_ega "IV 2.7.1" "implication" AlgebraicGeometry.IsProper.instFstScheme
add_to_ega "IV 2.7.1" "implication" AlgebraicGeometry.IsSeparated.instFstScheme
add_to_ega "IV 2.7.1" "(x)"
  AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.pullback_fst_of_right
add_to_ega "IV 2.7.1" "(x)"
  AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.pullback_snd_of_left
add_to_ega "IV 2.7.1" "(x)"
  AlgebraicGeometry.descendsAlong_isOpenImmersion_surjective_inf_flat_inf_quasicompact'
add_to_ega "IV 2.7.1" "(viii)"
  AlgebraicGeometry.descendsAlong_isomorphisms_surjective_inf_flat_inf_quasicompact
add_to_ega "IV 2.7.1" "(iv)"
  AlgebraicGeometry.instDescendsAlongSchemeLocallyOfFinitePresentationMinMorphismPropertySurjectiveFlatQuasiCompact
add_to_ega "IV 2.7.1" "(iii)"
  AlgebraicGeometry.instDescendsAlongSchemeLocallyOfFiniteTypeMinMorphismPropertySurjectiveFlatQuasiCompact
add_to_ega "IV 2.7.1" "(ii)" AlgebraicGeometry.instQuasiSeparatedFstScheme
add_to_ega "IV 2.7.1" "(ii)" AlgebraicGeometry.instQuasiSeparatedSndScheme
add_to_ega "IV 2.7.1" "special case" RingHom.FinitePresentation.codescendsAlong_faithfullyFlat
add_to_ega "IV 2.7.1" "special case" RingHom.FiniteType.codescendsAlong_faithfullyFlat
add_to_ega "IV 2.7.1" "special case" RingHom.finitePresentation_isStableUnderBaseChange
add_to_ega "IV 2.7.1" "special case" RingHom.finiteType_isStableUnderBaseChange
add_to_ega "IV 2.7.1" "(xv), special case" RingHom.finite_isStableUnderBaseChange
add_to_ega "IV 2.7.1" "(xvii), special case" RingHom.isIntegral_isStableUnderBaseChange
add_to_ega "IV 2.7.1.1" "partial" Algebra.FiniteType.baseChange
add_to_ega "IV 2.7.1.1" "partial" Algebra.FiniteType.of_finiteType_tensorProduct_of_faithfullyFlat
add_to_ega "IV 2.7.1.1" "partial" RingHom.FinitePresentation.codescendsAlong_faithfullyFlat
add_to_ega "IV 2.7.1.1" "partial" RingHom.FiniteType.codescendsAlong_faithfullyFlat
add_to_ega "IV 2.7.3" "more general" Algebra.FormallyEtale.equivPiOfIsSepClosed
add_to_ega "IV 2.7.3" "more general"
  Algebra.IsFiniteSplit.instOfIsSepClosedOfEssFiniteTypeOfFormallyEtale
add_to_ega "IV 2.7.3" "partial" AlgebraicGeometry.Flat.instDescScheme
add_to_ega "IV 2.7.3" "partial" AlgebraicGeometry.instSurjectiveDescI₀SchemeF
add_to_ega "IV 3.1.6" "more general" LocallyFinite
add_to_ega "IV 3.1.7" "(iii), special case" associatedPrimes.prod
add_to_ega "IV 3.1.7" "(i), special case" associatedPrimes.subset_union_of_exact
add_to_ega "IV 3.2.1" "a) ⇒ b)" AlgebraicGeometry.instIsReducedToScheme
add_to_ega "IV 3.2.1" "a) ⇒ b)" AlgebraicGeometry.instIsReducedXScheme
add_to_ega "IV 3.2.1" "a) ⇒ b)" AlgebraicGeometry.isReduced_of_isOpenImmersion
add_to_ega "IV 3.2.5" "special case" Submodule.IsMinimalPrimaryDecomposition
add_to_ega "IV 3.2.9" AlgebraicGeometry.Scheme.fromSpecResidueField
add_to_ega "IV 3.2.9" AlgebraicGeometry.Scheme.instOverSpecResidueField
add_to_ega "IV 3.3.1" "special case" Ideal.Fiber
add_to_ega "IV 3.3.4" "partial"
  AlgebraicGeometry.GeometricallyReduced.isReduced_of_flat_of_finite_irreducibleComponents
add_to_ega "IV 3.3.4" "partial"
  AlgebraicGeometry.GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian
add_to_ega "IV 3.3.5" "special case"
  AlgebraicGeometry.GeometricallyReduced.isReduced_of_flat_of_finite_irreducibleComponents
add_to_ega "IV 3.3.5" "special case"
  AlgebraicGeometry.GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian
add_to_ega "IV 3.3.5" "special case"
  AlgebraicGeometry.instIsReducedPullbackSchemeOfGeometricallyReducedOfFlatOfIsLocallyNoetherian
add_to_ega "IV 3.3.5" "special case"
  AlgebraicGeometry.instIsReducedPullbackSchemeOfGeometricallyReducedOfFlatOfIsLocallyNoetherian_1
add_to_ega "IV 3.3.6" AlgebraicGeometry.Scheme.Pullback.Triplet.SpecTensorTo
add_to_ega "IV 3.3.6" AlgebraicGeometry.Scheme.Pullback.Triplet.tensor
add_to_ega "IV 3.4.1" AlgebraicGeometry.IsReduced
add_to_ega "IV 3.4.1" "partial" AlgebraicGeometry.Scheme.irreducibleComponent
add_to_ega "IV 3.4.1" "partial" AlgebraicGeometry.Scheme.irreducibleComponentIdeal
add_to_ega "IV 3.4.1" "partial" AlgebraicGeometry.Scheme.zeroLocus
add_to_ega "IV 3.4.1" IsDiscreteValuationRing
add_to_ega "IV 3.4.1" IsLocalRing.maximalIdeal
add_to_ega "IV 3.4.1" Module.support
add_to_ega "IV 3.4.1" "Supp(F/tF) = S ∩ Y" Module.support_quotSMulTop
add_to_ega "IV 3.4.1" "Supp(F/tF) = S ∩ Y" Module.support_quotient
add_to_ega "IV 3.4.1.4" "more general"
  QuotSMulTop.map_first_exact_on_four_term_exact_of_isSMulRegular_last
