module  -- shake: keep-all

import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.Algebra.Colimit.Finiteness
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.Group.Submonoid.Saturation
import Mathlib.Algebra.Homology.LocalCohomology
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.LocalizedModule.AtPrime
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.Algebra.Module.RingHom
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Artinian
import Mathlib.AlgebraicGeometry.Birational.RationalMap
import Mathlib.AlgebraicGeometry.Cover.Directed
import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.IdealSheaf.IrreducibleComponent
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.AlgebraicGeometry.Morphisms.LocalClosure
import Mathlib.AlgebraicGeometry.Morphisms.LocalIso
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Over
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Sites.Pretopology
import Mathlib.AlgebraicGeometry.Spec
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.AlgebraicGeometry.StructureSheaf
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Comma.Over.OverClass
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.EpiMono
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Limits.EpiMono
import Mathlib.CategoryTheory.Limits.IsLimit
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Square
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryFan
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Limits.Shapes.Images
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.ChosenPullback
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Equifibered
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono
import Mathlib.CategoryTheory.Monoidal.Mod
import Mathlib.CategoryTheory.MorphismProperty.Composition
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Sites.JointlySurjective
import Mathlib.CategoryTheory.Subobject.FactorThru
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Data.Set.Function
import Mathlib.Data.Set.Lattice.Image
import Mathlib.Data.Set.Prod
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.FieldTheory.SeparableDegree
import Mathlib.Geometry.RingedSpace.Basic
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace.ResidueField
import Mathlib.Geometry.RingedSpace.OpenImmersion
import Mathlib.GroupTheory.MonoidLocalization.Away
import Mathlib.GroupTheory.MonoidLocalization.Maps
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Logic.Function.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.DedekindDomain.Instances
import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Flat.Rank
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.RingTheory.LocalRing.LocalSubring
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Away.AdjoinRoot
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Defs
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Noetherian.Nilpotent
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.RingHom.Finite
import Mathlib.RingTheory.RingHom.FiniteType
import Mathlib.RingTheory.RingHom.Locally
import Mathlib.RingTheory.RingHom.OpenImmersion
import Mathlib.RingTheory.RingHom.QuasiFinite
import Mathlib.RingTheory.Spectrum.Maximal.Topology
import Mathlib.RingTheory.Spectrum.Prime.Basic
import Mathlib.RingTheory.Spectrum.Prime.ConstructibleSet
import Mathlib.RingTheory.Spectrum.Prime.Defs
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Support
import Mathlib.RingTheory.SurjectiveOnStalks
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Continuous
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Irreducible
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.LocallyClosed
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Sober
import StacksCore.RingTheory.Spectrum.Prime.Topology
import StacksCore.Tactic.EgaSgaAttribute

/-!
# EGA I references registered by name: Chapters 4 to 6

The part of `StacksFrontier.EgaSgaIndex.EGAI` covering EGA I, Chapters 4 to 6 (subpreschemes and
immersions; reduced preschemes and the separation condition; finiteness conditions).

Declarations realizing numbered items of EGA I, from the EGA/SGA concept index, that
are not tagged where they are declared: Mathlib and core declarations without an
`add_to_stacks` pointer in this library, and (with `--draft-only`) those of `StacksCore/`.
-/

add_to_ega "I 4.1.1" "affine case"
  AlgebraicGeometry.Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent
add_to_ega "I 4.1.1" "special case" AlgebraicGeometry.essImage_tilde
add_to_ega "I 4.1.1" "special case" AlgebraicGeometry.isQuasicoherent_iff_isIso_fromTildeΓ
add_to_ega "I 4.1.1" "partial" SheafOfModules.IsQuasicoherent.of_coversTop
add_to_ega "I 4.1.1" "partial" SheafOfModules.isQuasicoherent_over
add_to_ega "I 4.1.2" "affine case" Module.support_quotient
add_to_ega "I 4.1.3" "1°" IsLocallyClosed
add_to_ega "I 4.1.3" "partial" IsLocallyClosed.isOpen_coborder
add_to_ega "I 4.1.3" "partial" isLocallyClosed_iff_isOpen_coborder
add_to_ega "I 4.1.3" "partial" isLocallyClosed_tfae
add_to_ega "I 4.1.4" "partial" AlgebraicGeometry.Scheme.ker_morphismRestrict_ideal
add_to_ega "I 4.1.4" "Y ∩ V is closed in V" AlgebraicGeometry.instIsClosedImmersionMorphismRestrict
add_to_ega "I 4.1.6" "more general" AlgebraicGeometry.IsClosedImmersion.comp_iff
add_to_ega "I 4.1.6" "more general" AlgebraicGeometry.IsClosedImmersion.instIsMultiplicativeScheme
add_to_ega "I 4.1.7" "special case" AlgebraicGeometry.IsClosedImmersion.spec_of_quotient_mk
add_to_ega "I 4.1.7" "special case"
  AlgebraicGeometry.Scheme.IdealSheafData.instIsPreimmersionSubschemeι
add_to_ega "I 4.1.7" "partial" AlgebraicGeometry.Scheme.IdealSheafData.subschemeι_app
add_to_ega "I 4.1.7" "partial" AlgebraicGeometry.Scheme.IdealSheafData.subschemeι_app_surjective
add_to_ega "I 4.1.7" "partial" AlgebraicGeometry.Scheme.IdealSheafData.subschemeι_apply
add_to_ega "I 4.1.7" "special case" AlgebraicGeometry.Scheme.homOfLE
add_to_ega "I 4.1.7" "partial" AlgebraicGeometry.Scheme.homOfLE_apply'
add_to_ega "I 4.1.7" "special case" AlgebraicGeometry.Scheme.ofRestrict
add_to_ega "I 4.1.7" "partial" AlgebraicGeometry.Scheme.ofRestrict_toLRSHom_base
add_to_ega "I 4.1.8" "more general" CategoryTheory.Limits.MonoFactorisation.ext
add_to_ega "I 4.1.8" CategoryTheory.MonoOver.Factors
add_to_ega "I 4.1.8" CategoryTheory.MonoOver.factorThru
add_to_ega "I 4.1.8" CategoryTheory.Subobject.Factors
add_to_ega "I 4.1.8" CategoryTheory.Subobject.factorThru
add_to_ega "I 4.1.8" "more general" CategoryTheory.cancel_mono
add_to_ega "I 4.1.10" "partial" AlgebraicGeometry.Scheme.IdealSheafData.inclusion_subschemeι
add_to_ega "I 4.1.10" "partial" AlgebraicGeometry.Scheme.IdealSheafData.inclusion_subschemeι_assoc
add_to_ega "I 4.1.10" "partial" AlgebraicGeometry.Scheme.homOfLE_ι
add_to_ega "I 4.2.1" "partial" AlgebraicGeometry.IsOpenImmersion.isoRestrict
add_to_ega "I 4.2.1" "more general" AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion
add_to_ega "I 4.2.1" "special case" AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι
add_to_ega "I 4.2.1" "more general" AlgebraicGeometry.SheafedSpace.IsOpenImmersion
add_to_ega "I 4.2.1" "special case" AlgebraicGeometry.instIsOpenImmersionHomOfLE
add_to_ega "I 4.2.2" AlgebraicGeometry.IsOpenImmersion.iff_isIso_stalkMap
add_to_ega "I 4.2.2" "a)" AlgebraicGeometry.IsOpenImmersion.instIsIsoCommRingCatStalkMap
add_to_ega "I 4.2.2" "a), sufficiency" AlgebraicGeometry.IsOpenImmersion.of_isIso_stalkMap
add_to_ega "I 4.2.2" AlgebraicGeometry.isOpenImmersion_eq_inf
add_to_ega "I 4.2.3" "more general" AlgebraicGeometry.IsClosedImmersion.hasAffineProperty
add_to_ega "I 4.2.3" "necessity" AlgebraicGeometry.IsClosedImmersion.isAffine_surjective_of_isAffine
add_to_ega "I 4.2.3" "sufficiency" AlgebraicGeometry.IsClosedImmersion.of_surjective_of_isAffine
add_to_ega "I 4.2.3" "more general" AlgebraicGeometry.Scheme.Hom.app_surjective
add_to_ega "I 4.2.4" AlgebraicGeometry.IsClosedImmersion.isZariskiLocalAtTarget
add_to_ega "I 4.2.4" "(a), special case" AlgebraicGeometry.IsImmersion.instIsZariskiLocalAtTarget
add_to_ega "I 4.2.4" "(a)" AlgebraicGeometry.IsImmersion.instMorphismRestrict
add_to_ega "I 4.2.4" "(a)" AlgebraicGeometry.IsImmersion.instResLE
add_to_ega "I 4.2.4" "(b): necessity" AlgebraicGeometry.instIsClosedImmersionMorphismRestrict
add_to_ega "I 4.2.4" "(a)" AlgebraicGeometry.instIsOpenImmersionMorphismRestrict
add_to_ega "I 4.2.5" "more general" AlgebraicGeometry.IsClosedImmersion.comp_iff
add_to_ega "I 4.2.5" "more general" AlgebraicGeometry.IsClosedImmersion.instIsMultiplicativeScheme
add_to_ega "I 4.2.5" "more general" AlgebraicGeometry.IsImmersion.comp_iff
add_to_ega "I 4.2.5" "more general" AlgebraicGeometry.IsImmersion.instIsMultiplicativeScheme
add_to_ega "I 4.2.5" "more general" AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.comp
add_to_ega "I 4.2.5" "more general" AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.comp
add_to_ega "I 4.2.5" "more general" AlgebraicGeometry.SheafedSpace.IsOpenImmersion.comp
add_to_ega "I 4.2.5" "more general" AlgebraicGeometry.isOpenImmersion_isMultiplicative
add_to_ega "I 4.2.5" AlgebraicGeometry.isOpenImmersion_isStableUnderComposition
add_to_ega "I 4.3.1" "special case" AlgebraicGeometry.IsImmersion.instFstScheme
add_to_ega "I 4.3.1" "special case" AlgebraicGeometry.IsImmersion.instSndScheme
add_to_ega "I 4.3.1" "special case" AlgebraicGeometry.IsOpenImmersion.instFstScheme
add_to_ega "I 4.3.1" "special case" AlgebraicGeometry.IsOpenImmersion.instSndScheme
add_to_ega "I 4.3.1" "partial" AlgebraicGeometry.IsOpenImmersion.range_pullback_to_base_of_left
add_to_ega "I 4.3.1" "partial" AlgebraicGeometry.IsOpenImmersion.range_pullback_to_base_of_right
add_to_ega "I 4.3.1" "partial" AlgebraicGeometry.Scheme.Pullback.range_fst_comp
add_to_ega "I 4.3.1" "partial" AlgebraicGeometry.Scheme.Pullback.range_snd_comp
add_to_ega "I 4.3.1" "more general" AlgebraicGeometry.Scheme.pullback_map_isOpenImmersion
add_to_ega "I 4.3.1" "special case" AlgebraicGeometry.instIsClosedImmersionFstScheme
add_to_ega "I 4.3.1" "special case" AlgebraicGeometry.instIsClosedImmersionMorphismRestrict
add_to_ega "I 4.3.1" "special case" AlgebraicGeometry.instIsClosedImmersionSndScheme
add_to_ega "I 4.3.1" "special case" AlgebraicGeometry.isPullback_opens_inf
add_to_ega "I 4.3.2" "more general"
  AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.pullback_fst_of_right
add_to_ega "I 4.3.2" "more general"
  AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.pullback_snd_of_left
add_to_ega "I 4.3.2" "special case" AlgebraicGeometry.instIsClosedImmersionMorphismRestrict
add_to_ega "I 4.3.2" "special case" AlgebraicGeometry.instIsOpenImmersionMorphismRestrict
add_to_ega "I 4.3.2" "special case" RingHom.IsStandardOpenImmersion.isStableUnderBaseChange
add_to_ega "I 4.4.1" "closed case" AlgebraicGeometry.Scheme.IdealSheafData.comapIso_inv_subschemeι
add_to_ega "I 4.4.1" "closed case"
  AlgebraicGeometry.Scheme.IdealSheafData.comapIso_inv_subschemeι_assoc
add_to_ega "I 4.4.1" "closed-immersion clause" AlgebraicGeometry.instIsClosedImmersionFstScheme
add_to_ega "I 4.4.1" "special case" AlgebraicGeometry.instIsClosedImmersionMorphismRestrict
add_to_ega "I 4.4.1" "closed-immersion clause" AlgebraicGeometry.instIsClosedImmersionSndScheme
add_to_ega "I 4.4.2" "special case" AlgebraicGeometry.Scheme.Hom.comp_preimage
add_to_ega "I 4.4.3" "special case" AlgebraicGeometry.isPullback_opens_inf
add_to_ega "I 4.4.3" "special case" AlgebraicGeometry.isPullback_opens_inf_le
add_to_ega "I 4.4.4" "open sub-preschemes" AlgebraicGeometry.Scheme.Hom.preimage_inf
add_to_ega "I 4.4.6" "special case" AlgebraicGeometry.Scheme.IdealSheafData.inclusion_subschemeι
add_to_ega "I 4.4.6" "special case"
  AlgebraicGeometry.Scheme.IdealSheafData.inclusion_subschemeι_assoc
add_to_ega "I 4.5.2" AlgebraicGeometry.IsLocalIso
add_to_ega "I 4.5.2" AlgebraicGeometry.IsLocalIso.eq_sourceLocalClosure_isOpenImmersion
add_to_ega "I 4.5.3" "sufficiency" AlgebraicGeometry.IsOpenImmersion.of_forall_source_exists
add_to_ega "I 4.5.3" "sufficiency" AlgebraicGeometry.IsOpenImmersion.of_openCover_source
add_to_ega "I 4.5.5" "(i), special case" AlgebraicGeometry.IsClosedImmersion.comp_iff
add_to_ega "I 4.5.5" "(i), special case"
  AlgebraicGeometry.IsClosedImmersion.instIsMultiplicativeScheme
add_to_ega "I 4.5.5" "(i), special case" AlgebraicGeometry.IsImmersion.comp_iff
add_to_ega "I 4.5.5" "(i), special case" AlgebraicGeometry.IsImmersion.instIsMultiplicativeScheme
add_to_ega "I 4.5.5" AlgebraicGeometry.IsLocalIso.instIsMultiplicativeScheme
add_to_ega "I 4.5.5" AlgebraicGeometry.IsLocalIso.instIsStableUnderBaseChangeScheme
add_to_ega "I 4.5.5" "(i), special case" AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.comp
add_to_ega "I 4.5.5" "(iii), special case"
  AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.pullback_fst_of_right
add_to_ega "I 4.5.5" "(iii), special case"
  AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.pullback_snd_of_left
add_to_ega "I 4.5.5" "(i), special case" AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.comp
add_to_ega "I 4.5.5" "(i), special case" AlgebraicGeometry.isOpenImmersion_isMultiplicative
add_to_ega "I 4.5.5" "(i), special case" AlgebraicGeometry.isOpenImmersion_isStableUnderComposition
add_to_ega "I 4.5.5" "more general"
  AlgebraicGeometry.sourceLocalClosure.instIsStableUnderBaseChangeScheme
add_to_ega "I 4.5.5" "(iii), special case" RingHom.IsStandardOpenImmersion.isStableUnderBaseChange
add_to_ega "I 4.5.5" "(iii), special case" RingHom.locally_isStableUnderBaseChange
add_to_ega "I 5.1.1" "special case" AlgebraicGeometry.Scheme.nilradical
add_to_ega "I 5.1.2" "partial" AlgebraicGeometry.Scheme.support_nilradical
add_to_ega "I 5.1.3" "partial" AlgebraicGeometry.Scheme.support_nilradical
add_to_ega "I 5.1.4" AlgebraicGeometry.affine_isIntegral_iff
add_to_ega "I 5.1.4" AlgebraicGeometry.affine_isReduced_iff
add_to_ega "I 5.1.4" "partial" AlgebraicGeometry.instIsIntegralSpecOfIsDomainCarrier
add_to_ega "I 5.1.4" "partial" AlgebraicGeometry.instIsReducedSpecOfIsReducedCarrier
add_to_ega "I 5.1.4" "partial" AlgebraicGeometry.isIntegral_of_isAffine_of_isDomain
add_to_ega "I 5.1.4" "partial" AlgebraicGeometry.isReduced_of_isAffine_isReduced
add_to_ega "I 5.1.9" "partial" AlgebraicGeometry.IsClosedImmersion.instSubschemeι
add_to_ega "I 5.1.9" "partial" AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι
add_to_ega "I 5.1.9" "necessity" AlgebraicGeometry.isAffine_of_isAffineHom
add_to_ega "I 5.3.1" CategoryTheory.Limits.ChosenPullback.Diagonal
add_to_ega "I 5.3.1" "partial" CategoryTheory.Limits.ChosenPullback.instNonemptyDiagonal
add_to_ega "I 5.3.1" CategoryTheory.Limits.pullback.diagonal
add_to_ega "I 5.3.1" "5.3.1.1" CategoryTheory.Limits.pullback.diagonal_fst
add_to_ega "I 5.3.6" "more general" CategoryTheory.Limits.pullback_map_diagonal_isPullback
add_to_ega "I 5.3.7" "more general" CategoryTheory.Limits.pullbackDiagonalMapIdIso
add_to_ega "I 5.3.7" "more general" CategoryTheory.Limits.pullback_lift_diagonal_isPullback
add_to_ega "I 5.3.7" "more general" CategoryTheory.Limits.pullback_map_diagonal_isPullback
add_to_ega "I 5.3.8" "necessity" CategoryTheory.Limits.pullback.instIsIsoDiagonalOfMono
add_to_ega "I 5.3.8" "more general" CategoryTheory.Limits.pullback.isIso_diagonal_iff
add_to_ega "I 5.3.8" "more general" CategoryTheory.MorphismProperty.diagonal_isomorphisms
add_to_ega "I 5.3.8" "more general" CategoryTheory.mono_iff_isPullback
add_to_ega "I 5.3.9" AlgebraicGeometry.IsImmersion.instDiagonalScheme
add_to_ega "I 5.3.9" "absolute diagonal" AlgebraicGeometry.IsImmersion.instLiftSchemeId
add_to_ega "I 5.3.9" "more general" AlgebraicGeometry.IsImmersion.instMapDescScheme
add_to_ega "I 5.3.10" "Case X = Y = S" AlgebraicGeometry.IsImmersion.instDiagonalScheme
add_to_ega "I 5.3.10" "Case X = Y = S" AlgebraicGeometry.IsImmersion.instLiftSchemeId
add_to_ega "I 5.3.10" AlgebraicGeometry.IsImmersion.instMapDescScheme
add_to_ega "I 5.3.11" "special case" AlgebraicGeometry.IsImmersion.instDiagonalScheme
add_to_ega "I 5.3.11" "special case" AlgebraicGeometry.IsImmersion.instLiftSchemeId
add_to_ega "I 5.3.11" "more general" AlgebraicGeometry.IsImmersion.instMapDescScheme
add_to_ega "I 5.3.11" CategoryTheory.Limits.pullback.lift
add_to_ega "I 5.3.13" "special case" AlgebraicGeometry.IsImmersion.comp_iff
add_to_ega "I 5.3.13"
  AlgebraicGeometry.IsImmersion.instHasOfPostcompPropertySchemeTopMorphismProperty
add_to_ega "I 5.3.13" AlgebraicGeometry.IsImmersion.of_comp
add_to_ega "I 5.3.14" "more general"
  AlgebraicGeometry.IsImmersion.instHasOfPostcompPropertySchemeTopMorphismProperty
add_to_ega "I 5.3.14" "more general" AlgebraicGeometry.IsImmersion.of_comp
add_to_ega "I 5.3.15" "more general" CategoryTheory.Limits.prod.diag_map
add_to_ega "I 5.4.1" AlgebraicGeometry.IsSeparated
add_to_ega "I 5.4.1" AlgebraicGeometry.Scheme.IsSeparated
add_to_ega "I 5.4.1" AlgebraicGeometry.Scheme.isSeparated_iff_isClosedImmersion_prod_lift
add_to_ega "I 5.4.2" "special case" AlgebraicGeometry.IsSeparated.instIsClosedImmersionLiftSchemeId
add_to_ega "I 5.4.2" AlgebraicGeometry.IsSeparated.instIsClosedImmersionMapDescScheme
add_to_ega "I 5.4.3" AlgebraicGeometry.IsSeparated.instIsClosedImmersionLiftSchemeId
add_to_ega "I 5.4.3" "more general" AlgebraicGeometry.IsSeparated.instIsClosedImmersionMapDescScheme
add_to_ega "I 5.4.4" "special case" AlgebraicGeometry.IsClosedImmersion.comp_iff
add_to_ega "I 5.4.4" AlgebraicGeometry.IsClosedImmersion.of_comp
add_to_ega "I 5.4.4" "special case" AlgebraicGeometry.IsClosedImmersion.of_comp_isClosedImmersion
add_to_ega "I 5.4.4" AlgebraicGeometry.instHasOfPostcompPropertySchemeIsClosedImmersionIsSeparated
add_to_ega "I 5.4.5" "j = id_X" AlgebraicGeometry.IsSeparated.instIsClosedImmersionLiftSchemeId
add_to_ega "I 5.4.6" "more general" AlgebraicGeometry.IsClosedImmersion.of_comp
add_to_ega "I 5.4.6" "more general"
  AlgebraicGeometry.instHasOfPostcompPropertySchemeIsClosedImmersionIsSeparated
add_to_ega "I 5.4.8" AlgebraicGeometry.IsSeparated.isSeparated_eq_diagonal_isClosedImmersion
add_to_ega "I 5.4.8" AlgebraicGeometry.IsSeparated.mk
add_to_ega "I 5.4.8" "special case"
  AlgebraicGeometry.Scheme.isSeparated_iff_isClosedImmersion_prod_lift
add_to_ega "I 5.4.8" AlgebraicGeometry.isSeparated_iff
add_to_ega "I 5.5.1" AlgebraicGeometry.IsSeparated.comp_iff
add_to_ega "I 5.5.1" AlgebraicGeometry.IsSeparated.instCompScheme
add_to_ega "I 5.5.1" AlgebraicGeometry.IsSeparated.instFstScheme
add_to_ega "I 5.5.1" "more general" AlgebraicGeometry.IsSeparated.instIsMultiplicativeScheme
add_to_ega "I 5.5.1" "(iv), special case" AlgebraicGeometry.IsSeparated.instMorphismRestrict
add_to_ega "I 5.5.1" "(iv), special case" AlgebraicGeometry.IsSeparated.instResLE
add_to_ega "I 5.5.1" AlgebraicGeometry.IsSeparated.instSndScheme
add_to_ega "I 5.5.1" AlgebraicGeometry.IsSeparated.isSeparated_of_mono
add_to_ega "I 5.5.1" AlgebraicGeometry.IsSeparated.of_comp
add_to_ega "I 5.5.1" "(v), special case" AlgebraicGeometry.Scheme.instIsSeparatedOfIsSeparated
add_to_ega "I 5.5.1" AlgebraicGeometry.instHasOfPostcompPropertySchemeIsSeparatedTopMorphismProperty
add_to_ega "I 5.5.1" "more general" AlgebraicGeometry.isSeparated_of_injective
add_to_ega "I 5.5.2" "special case" AlgebraicGeometry.IsSeparated.instResLE
add_to_ega "I 5.5.3" AlgebraicGeometry.IsSeparated.instFstScheme
add_to_ega "I 5.5.3" "special case" AlgebraicGeometry.IsSeparated.instMorphismRestrict
add_to_ega "I 5.5.3" AlgebraicGeometry.IsSeparated.instSndScheme
add_to_ega "I 5.5.5" AlgebraicGeometry.IsSeparated.instIsZariskiLocalAtTarget
add_to_ega "I 5.5.5" "Necessity" AlgebraicGeometry.IsSeparated.instMorphismRestrict
add_to_ega "I 5.5.5" "Necessity" AlgebraicGeometry.IsSeparated.instResLE
add_to_ega "I 5.5.6" "necessity" AlgebraicGeometry.IsAffineOpen.inf
add_to_ega "I 5.5.7" "more general" AlgebraicGeometry.IsSeparated.instMap
add_to_ega "I 5.5.7" "more general" AlgebraicGeometry.IsSeparated.of_isAffineHom
add_to_ega "I 5.5.7" "more general" AlgebraicGeometry.Scheme.instIsSeparatedOfIsQuasiAffine
add_to_ega "I 5.5.8" "more general" AlgebraicGeometry.IsSeparated.comp_iff
add_to_ega "I 5.5.8" "more general" AlgebraicGeometry.IsSeparated.hasAffineProperty
add_to_ega "I 5.5.8" "sufficiency" AlgebraicGeometry.IsSeparated.of_comp
add_to_ega "I 5.5.8" "sufficiency" AlgebraicGeometry.Scheme.instIsSeparatedOfIsSeparated
add_to_ega "I 5.5.9" AlgebraicGeometry.IsSeparated.hasAffineProperty
add_to_ega "I 5.5.9" "special case" AlgebraicGeometry.IsSeparated.instMap
add_to_ega "I 5.5.9" "special case" AlgebraicGeometry.IsSeparated.of_isAffineHom
add_to_ega "I 5.5.9" "special case" AlgebraicGeometry.Scheme.instIsSeparatedOfIsSeparated
add_to_ega "I 5.5.10" "more general" AlgebraicGeometry.IsAffineHom.of_comp
add_to_ega "I 5.5.10" "identity morphism" AlgebraicGeometry.IsAffineOpen.biInf
add_to_ega "I 5.5.10" "identity morphism" AlgebraicGeometry.IsAffineOpen.iInf
add_to_ega "I 5.5.10" "identity morphism" AlgebraicGeometry.IsAffineOpen.inf
add_to_ega "I 5.5.10" "more general"
  AlgebraicGeometry.instHasOfPostcompPropertySchemeIsAffineHomIsSeparated
add_to_ega "I 5.5.11" "more general" AlgebraicGeometry.Proj.instIsSeparated
add_to_ega "I 5.5.11" "more general" AlgebraicGeometry.Proj.isSeparated
add_to_ega "I 5.5.12" "(i), special case" AlgebraicGeometry.IsAffineHom.of_comp
add_to_ega "I 5.5.12" "(v), special case" AlgebraicGeometry.IsClosedImmersion.comp_iff
add_to_ega "I 5.5.12" "(i), special case" AlgebraicGeometry.IsClosedImmersion.of_comp
add_to_ega "I 5.5.12" "(v), special case"
  AlgebraicGeometry.IsClosedImmersion.of_comp_isClosedImmersion
add_to_ega "I 5.5.12" "special case" AlgebraicGeometry.IsImmersion.comp_iff
add_to_ega "I 5.5.12" "(ii), special case"
  AlgebraicGeometry.IsImmersion.instHasOfPostcompPropertySchemeTopMorphismProperty
add_to_ega "I 5.5.12" "special case" AlgebraicGeometry.IsImmersion.of_comp
add_to_ega "I 5.5.12" "(i), special case"
  AlgebraicGeometry.IsIntegralHom.instHasOfPostcompPropertySchemeIsSeparated
add_to_ega "I 5.5.12" "(i), special case" AlgebraicGeometry.IsIntegralHom.of_comp
add_to_ega "I 5.5.12" "(i), special case" AlgebraicGeometry.IsProper.of_comp
add_to_ega "I 5.5.12" "(i), special case" AlgebraicGeometry.IsSeparated.comp_iff
add_to_ega "I 5.5.12" "special case" AlgebraicGeometry.IsSeparated.of_comp
add_to_ega "I 5.5.12" "(i), special case" AlgebraicGeometry.QuasiCompact.of_comp
add_to_ega "I 5.5.12" "special case" AlgebraicGeometry.QuasiSeparated.of_comp
add_to_ega "I 5.5.12" "P = universally closed"
  AlgebraicGeometry.UniversallyClosed.of_comp_of_isSeparated
add_to_ega "I 5.5.12" "P = closed immersion"
  AlgebraicGeometry.instHasOfPostcompPropertySchemeIsClosedImmersionIsSeparated
add_to_ega "I 5.5.12" "P = separated"
  AlgebraicGeometry.instHasOfPostcompPropertySchemeIsSeparatedTopMorphismProperty
add_to_ega "I 5.5.12" "P = universally closed"
  AlgebraicGeometry.instHasOfPostcompPropertySchemeUniversallyClosedIsSeparated
add_to_ega "I 5.5.12" CategoryTheory.MorphismProperty.IsStableUnderBaseChangeAgainst
add_to_ega "I 5.5.12" CategoryTheory.MorphismProperty.IsStableUnderComposition
add_to_ega "I 5.5.12" "more general"
  CategoryTheory.MorphismProperty.hasOfPostcompProperty_iff_le_diagonal
add_to_ega "I 6.1.1" AlgebraicGeometry.IsLocallyNoetherian
add_to_ega "I 6.1.1" AlgebraicGeometry.IsNoetherian
add_to_ega "I 6.1.1" "special case"
  AlgebraicGeometry.instIsLocallyNoetherianSpecOfIsNoetherianRingCarrier
add_to_ega "I 6.1.1" "special case" AlgebraicGeometry.instIsNoetherianSpecOfIsNoetherianRingCarrier
add_to_ega "I 6.1.1" "special case" AlgebraicGeometry.instIsNoetherianSpecOfOfIsNoetherianRing
add_to_ega "I 6.1.1" "more general" AlgebraicGeometry.isLocallyNoetherian_iff_of_affine_openCover
add_to_ega "I 6.1.1" "more general" AlgebraicGeometry.isLocallyNoetherian_iff_of_iSup_eq_top
add_to_ega "I 6.1.1" "partial" AlgebraicGeometry.isLocallyNoetherian_of_affine_cover
add_to_ega "I 6.1.1" "more general" AlgebraicGeometry.isNoetherian_iff_of_finite_affine_openCover
add_to_ega "I 6.1.1" "more general" AlgebraicGeometry.isNoetherian_iff_of_finite_iSup_eq_top
add_to_ega "I 6.1.2" AlgebraicGeometry.IsNoetherian.noetherianSpace
add_to_ega "I 6.1.2" "special case"
  AlgebraicGeometry.instNoetherianSpaceCarrierCarrierCommRingCatSpecOfIsNoetherianRingCarrier
add_to_ega "I 6.1.2" "special case" AlgebraicGeometry.isNoetherian_iff_of_finite_iSup_eq_top
add_to_ega "I 6.1.2" "special case" AlgebraicGeometry.noetherianSpace_of_isAffineOpen
add_to_ega "I 6.1.3" "c ⇒ b" AlgebraicGeometry.instIsLocallyNoetherianSpecOfIsNoetherianRingCarrier
add_to_ega "I 6.1.3" "c ⇒ a" AlgebraicGeometry.instIsNoetherianSpecOfIsNoetherianRingCarrier
add_to_ega "I 6.1.3" "c ⇒ a" AlgebraicGeometry.instIsNoetherianSpecOfOfIsNoetherianRing
add_to_ega "I 6.1.3" "b ⇔ c" AlgebraicGeometry.isLocallyNoetherian_Spec
add_to_ega "I 6.1.3" "more general" AlgebraicGeometry.isLocallyNoetherian_iff_of_affine_openCover
add_to_ega "I 6.1.3" "more general" AlgebraicGeometry.isLocallyNoetherian_iff_of_iSup_eq_top
add_to_ega "I 6.1.3" "more general" AlgebraicGeometry.isLocallyNoetherian_of_affine_cover
add_to_ega "I 6.1.3" "a ⇔ c" AlgebraicGeometry.isNoetherian_Spec
add_to_ega "I 6.1.3" "more general" AlgebraicGeometry.isNoetherian_iff_of_finite_affine_openCover
add_to_ega "I 6.1.3" "more general" AlgebraicGeometry.isNoetherian_iff_of_finite_iSup_eq_top
add_to_ega "I 6.1.4" "special case" AlgebraicGeometry.instIsLocallyNoetherianToScheme
add_to_ega "I 6.1.4" "special case" AlgebraicGeometry.instIsLocallyNoetherianXScheme
add_to_ega "I 6.1.4" "special case" AlgebraicGeometry.isLocallyNoetherian_iff_openCover
add_to_ega "I 6.1.4" "special case" AlgebraicGeometry.isLocallyNoetherian_of_isOpenImmersion
add_to_ega "I 6.1.6" "special case" IsArtinianRing.isNilpotent_nilradical
add_to_ega "I 6.1.6" "affine case X = Spec(R)" IsNoetherianRing.isNilpotent_nilradical
add_to_ega "I 6.1.10" "(e)" PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical
add_to_ega "I 6.1.12" "necessity"
  AlgebraicGeometry.instIsDomainCarrierStalkCommRingCatPresheafOfIsIntegral
add_to_ega "I 6.1.12" "necessity" AlgebraicGeometry.irreducibleSpace_of_isIntegral
add_to_ega "I 6.1.12" "necessity" AlgebraicGeometry.isIntegral_iff_irreducibleSpace_and_isReduced
add_to_ega "I 6.2.1" AlgebraicGeometry.IsArtinianScheme
add_to_ega "I 6.2.1" "special case" AlgebraicGeometry.Scheme.isArtinianScheme_Spec
add_to_ega "I 6.2.1" "sufficiency on spectra"
  AlgebraicGeometry.instIsArtinianSchemeSpecOfIsArtinianRingCarrier
add_to_ega "I 6.2.2" AlgebraicGeometry.IsArtinianScheme.finite
add_to_ega "I 6.2.2" "(a) ⇔ (b)"
  AlgebraicGeometry.IsArtinianScheme.iff_isNoetherian_and_discreteTopology
add_to_ega "I 6.2.2" "(a) ⇒ X Noetherian" AlgebraicGeometry.IsArtinianScheme.isNoetherianScheme
add_to_ega "I 6.2.2" "(a)" AlgebraicGeometry.IsLocallyArtinian.discreteTopology
add_to_ega "I 6.2.2" "more general"
  AlgebraicGeometry.IsLocallyArtinian.iff_isLocallyNoetherian_and_discreteTopology
add_to_ega "I 6.2.2" "more general"
  AlgebraicGeometry.IsLocallyArtinian.of_isLocallyNoetherian_of_discreteTopology
add_to_ega "I 6.2.2" "more general"
  AlgebraicGeometry.IsLocallyArtinian.of_topologicalKrullDim_le_zero
add_to_ega "I 6.2.2" "special case" IsArtinianRing.equivPi
add_to_ega "I 6.2.2" "(a), special case" IsArtinianRing.instDiscreteTopologyPrimeSpectrum
add_to_ega "I 6.2.2" "affine finiteness" IsArtinianRing.instFinitePrimeSpectrum
add_to_ega "I 6.2.2" "affine, special case" IsArtinianRing.instLocalization
add_to_ega "I 6.2.2" "affine, special case" IsArtinianRing.localization_artinian
add_to_ega "I 6.2.2" "special case" IsArtinianRing.quotNilradicalEquivPi
add_to_ega "I 6.2.2" "affine decomposition" IsArtinianRing.quotNilradicalPowEquivPi
add_to_ega "I 6.3.1" "(P)" AlgHom.FiniteType
add_to_ega "I 6.3.1" "(P)" Algebra.FiniteType
add_to_ega "I 6.3.1" "(P)" RingHom.FiniteType
add_to_ega "I 6.3.3" "Sufficiency" AlgebraicGeometry.locallyOfFiniteType_specOverSpec
add_to_ega "I 6.3.4" "(ii), affine case" AlgHom.FiniteType.comp
add_to_ega "I 6.3.4" "(v), affine case" AlgHom.FiniteType.of_comp_finiteType
add_to_ega "I 6.3.4" "(iv), affine case" Algebra.FiniteType.baseChange
add_to_ega "I 6.3.4" "more general" AlgebraicGeometry.IsClosedImmersion.eq_isFinite_inf_mono
add_to_ega "I 6.3.4" "more general" AlgebraicGeometry.IsClosedImmersion.eq_proper_inf_monomorphisms
add_to_ega "I 6.3.4" "more general" AlgebraicGeometry.IsClosedImmersion.iff_isFinite_and_mono
add_to_ega "I 6.3.4" "more general" AlgebraicGeometry.IsClosedImmersion.iff_isProper_and_mono
add_to_ega "I 6.3.4" "more general" AlgebraicGeometry.IsFinite.instOfIsClosedImmersion
add_to_ega "I 6.3.4" "(i)" AlgebraicGeometry.IsImmersion.instLocallyOfFiniteType
add_to_ega "I 6.3.4" "(v)" AlgebraicGeometry.QuasiCompact.of_comp
add_to_ega "I 6.3.4" "clause (ii)" AlgebraicGeometry.instIsMultiplicativeSchemeLocallyOfFiniteType
add_to_ega "I 6.3.4" "clause (ii)"
  AlgebraicGeometry.instIsStableUnderCompositionSchemeLocallyOfFiniteType
add_to_ega "I 6.3.4" "clause (i)" AlgebraicGeometry.instLocallyOfFiniteTypeOfIsClosedImmersion
add_to_ega "I 6.3.4" "clause (ii), affine case" RingHom.FiniteType.comp
add_to_ega "I 6.3.4" "special case" RingHom.FiniteType.comp_surjective
add_to_ega "I 6.3.4" "clause (v), affine case" RingHom.FiniteType.of_comp_finiteType
add_to_ega "I 6.3.4" "clause (iv), affine case" RingHom.finiteType_isStableUnderBaseChange
add_to_ega "I 6.3.4" "clause (ii), affine case" RingHom.finiteType_stableUnderComposition
add_to_ega "I 6.3.5" "partial" AlgebraicGeometry.IsImmersion.instLocallyOfFiniteType
add_to_ega "I 6.3.5" "partial"
  AlgebraicGeometry.instQuasiCompactOfIsLocallyNoetherianOfIsOpenImmersion
add_to_ega "I 6.3.5" "partial" AlgebraicGeometry.quasiCompact_of_noetherianSpace_source
add_to_ega "I 6.3.6" "special case" AlgHom.FiniteType.of_comp_finiteType
add_to_ega "I 6.3.6" "affine case" RingHom.FiniteType.of_comp_finiteType
add_to_ega "I 6.3.7" "more general"
  AlgebraicGeometry.instIsLocallyNoetherianPullbackSchemeOfLocallyOfFiniteType
add_to_ega "I 6.3.7" "more general"
  AlgebraicGeometry.instIsLocallyNoetherianPullbackSchemeOfLocallyOfFiniteType_1
add_to_ega "I 6.3.8" "more general"
  AlgebraicGeometry.instIsLocallyNoetherianPullbackSchemeOfLocallyOfFiniteType
add_to_ega "I 6.3.8" "more general"
  AlgebraicGeometry.instIsLocallyNoetherianPullbackSchemeOfLocallyOfFiniteType_1
add_to_ega "I 6.4.2" "special case" AlgebraicGeometry.residueFieldIsoBase
add_to_ega "I 6.4.3" "partial" AlgebraicGeometry.ext_of_apply_closedPoint_eq
add_to_ega "I 6.4.3" "more general" AlgebraicGeometry.pointEquivClosedPoint
add_to_ega "I 6.4.3" "partial" AlgebraicGeometry.pointOfClosedPoint
add_to_ega "I 6.4.3" "partial" AlgebraicGeometry.residueFieldIsoBase
add_to_ega "I 6.4.4" "(a) ⇒ (c′)" AlgebraicGeometry.IsArtinianScheme.finite
add_to_ega "I 6.4.4" "(a) ⇔ (b)"
  AlgebraicGeometry.IsArtinianScheme.iff_isNoetherian_and_discreteTopology
add_to_ega "I 6.4.4" "(a) ⇒ (b)" AlgebraicGeometry.IsLocallyArtinian.discreteTopology
add_to_ega "I 6.4.4" "(a) ⇔ (b)"
  AlgebraicGeometry.IsLocallyArtinian.iff_isLocallyNoetherian_and_discreteTopology
add_to_ega "I 6.4.4" "(b) ⇒ (a)"
  AlgebraicGeometry.IsLocallyArtinian.of_isLocallyNoetherian_of_discreteTopology
add_to_ega "I 6.4.4" "(d) ⇒ (a)" AlgebraicGeometry.IsLocallyArtinian.of_topologicalKrullDim_le_zero
add_to_ega "I 6.4.4" "(b) ⇒ (a), reduced case"
  AlgebraicGeometry.instIsLocallyArtinianOfDiscreteTopologyCarrierCarrierCommRingCatOfIsReduced
add_to_ega "I 6.4.4" "affine case: (a) ⇒ (b)" IsArtinianRing.instDiscreteTopologyPrimeSpectrum
add_to_ega "I 6.4.4" "affine case: (a) ⇒ (c′)" IsArtinianRing.instFinitePrimeSpectrum
add_to_ega "I 6.4.5" AlgebraicGeometry.IsFinite
add_to_ega "I 6.4.5" "partial" AlgebraicGeometry.IsFinite.SpecMap_iff
-- The auto-generated instance name is longer than a line, so its identifier is assembled
-- from two pieces before being handed to `add_to_ega`.
run_cmd do
  let decl := Lean.mkIdent <| .str `AlgebraicGeometry.IsFinite <|
    "instHasAffinePropertyAndIsAffineFiniteCarrierObjOppositeOpensCarrierCarrier" ++
      "CommRingCatPresheafOpOpensTopHomAppTop"
  Lean.Elab.Command.elabCommand (← `(command| add_to_ega "I 6.4.5" "more general" $decl:ident))
add_to_ega "I 6.4.5" "more general" AlgebraicGeometry.Scheme.Hom.finrank
add_to_ega "I 6.4.5" "partial" AlgebraicGeometry.Scheme.Hom.finrank_SpecMap_algebraMap
add_to_ega "I 6.4.5" "partial" AlgebraicGeometry.Scheme.Hom.finrank_SpecMap_eq_finrank
add_to_ega "I 6.4.5" Module.finrank
add_to_ega "I 6.4.5" "(6.4.5.1), special case" Module.finrank_prod
add_to_ega "I 6.4.5" "(6.4.5.2), special case" Module.finrank_tensorProduct
add_to_ega "I 6.4.5" "(6.4.5.1), special case" Module.rankAtStalk_prod
add_to_ega "I 6.4.5" "more general" RingHom.finrank
add_to_ega "I 6.4.5" "(6.4.5.1), special case" rank_prod'
add_to_ega "I 6.4.5" "(6.4.5.2), special case" rank_tensorProduct
add_to_ega "I 6.4.5" "(6.4.5.2), special case" rank_tensorProduct'
add_to_ega "I 6.4.6" "special case" RingHom.finite_isStableUnderBaseChange
add_to_ega "I 6.4.7" "partial" AlgebraicGeometry.pointEquivClosedPoint
add_to_ega "I 6.4.7" Field.finSepDegree
add_to_ega "I 6.4.7" Field.sepDegree
add_to_ega "I 6.4.7" separableClosure
add_to_ega "I 6.4.11" Algebra.EssFiniteType
add_to_ega "I 6.4.11" "partial"
  AlgebraicGeometry.instCompactSpaceCarrierCarrierCommRingCatFiberOfQuasiCompact
add_to_ega "I 6.4.11" "special case" instEssFiniteTypeResidueField_1
add_to_ega "I 6.4.12" "more general" Algebra.QuasiFinite.baseChange
add_to_ega "I 6.4.12" "more general" AlgebraicGeometry.IsFinite.instFstScheme
add_to_ega "I 6.4.12" "more general" AlgebraicGeometry.IsFinite.instSndScheme
add_to_ega "I 6.4.12" "special case" AlgebraicGeometry.Scheme.Hom.finrank_of_isPullback
add_to_ega "I 6.4.12" "special case" AlgebraicGeometry.Scheme.Hom.finrank_pullback_fst
add_to_ega "I 6.4.12" "special case" AlgebraicGeometry.Scheme.Hom.finrank_pullback_snd
add_to_ega "I 6.4.12" "special case" CommAlgCat.FiniteEtale.fiberIsoBaseChangeFiber
add_to_ega "I 6.4.12" "more general" IsBaseChange.finrank_eq
add_to_ega "I 6.4.12" "more general" IsBaseChange.finrank_eq_of_le_nonZeroDivisors
add_to_ega "I 6.4.12" "more general" IsBaseChange.lift_rank_eq
add_to_ega "I 6.4.12" "more general" IsBaseChange.lift_rank_eq_of_le_nonZeroDivisors
add_to_ega "I 6.4.12" "more general" IsBaseChange.rank_eq
add_to_ega "I 6.4.12" "more general" IsBaseChange.rank_eq_of_le_nonZeroDivisors
add_to_ega "I 6.4.12" "more general" Module.finrank_baseChange
add_to_ega "I 6.4.12" "more general" Module.rankAtStalk_baseChange
add_to_ega "I 6.4.12" "more general" Module.rankAtStalk_isBaseChange
add_to_ega "I 6.4.12" "more general" Module.rank_baseChange
add_to_ega "I 6.4.12" "more general" RingHom.QuasiFinite.isStableUnderBaseChange
add_to_ega "I 6.4.12" "more general" RingHom.finite_isStableUnderBaseChange
add_to_ega "I 6.5.5" "(ii)" AlgebraicGeometry.genericPoint_eq_of_isOpenImmersion
add_to_ega "I 6.6.4" "more general" AlgebraicGeometry.QuasiCompact.of_comp
add_to_ega "I 6.6.4" "more general"
  AlgebraicGeometry.instHasOfPostcompPropertySchemeQuasiCompactQuasiSeparated
add_to_ega "I 6.6.4" "more general" AlgebraicGeometry.instIsMultiplicativeSchemeQuasiCompact
add_to_ega "I 6.6.4" AlgebraicGeometry.instQuasiCompactFstScheme
add_to_ega "I 6.6.4" "(iii), special case" AlgebraicGeometry.instQuasiCompactMorphismRestrict
add_to_ega "I 6.6.4" "(i), special case"
  AlgebraicGeometry.instQuasiCompactOfIsLocallyNoetherianOfIsOpenImmersion
add_to_ega "I 6.6.4" AlgebraicGeometry.instQuasiCompactSndScheme
add_to_ega "I 6.6.4" "more general" AlgebraicGeometry.quasiCompact_of_noetherianSpace_source
add_to_ega "I 6.6.6" "(i), for immersions" AlgebraicGeometry.IsImmersion.instLocallyOfFiniteType
add_to_ega "I 6.6.6" AlgebraicGeometry.instIsMultiplicativeSchemeLocallyOfFiniteType
add_to_ega "I 6.6.6" AlgebraicGeometry.instIsStableUnderCompositionSchemeLocallyOfFiniteType
add_to_ega "I 6.6.6" "(iii), special case" AlgebraicGeometry.instLocallyOfFiniteTypeFstScheme
add_to_ega "I 6.6.6" "(iii), special case" AlgebraicGeometry.instLocallyOfFiniteTypeMorphismRestrict
add_to_ega "I 6.6.6" "(i), closed immersions"
  AlgebraicGeometry.instLocallyOfFiniteTypeOfIsClosedImmersion
add_to_ega "I 6.6.6" "(iii), special case" AlgebraicGeometry.instLocallyOfFiniteTypeResLE
add_to_ega "I 6.6.6" "(iii), special case" AlgebraicGeometry.instLocallyOfFiniteTypeSndScheme
add_to_ega "I 6.6.6" "(i), open immersions" AlgebraicGeometry.locallyOfFiniteType_of_isOpenImmersion
add_to_ega "I 6.6.6" "(ii), affine schemes" RingHom.FiniteType.comp
add_to_ega "I 6.6.6" "(v), affine schemes" RingHom.FiniteType.of_comp_finiteType
add_to_ega "I 6.6.6" "(iii), special case" RingHom.finiteType_isStableUnderBaseChange
add_to_ega "I 6.6.6" "(ii), affine schemes" RingHom.finiteType_stableUnderComposition
add_to_ega "I 6.6.7" "more general"
  AlgebraicGeometry.instIsLocallyNoetherianPullbackSchemeOfLocallyOfFiniteType
add_to_ega "I 6.6.7" "more general"
  AlgebraicGeometry.instIsLocallyNoetherianPullbackSchemeOfLocallyOfFiniteType_1
