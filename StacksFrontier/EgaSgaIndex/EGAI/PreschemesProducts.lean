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
# EGA I references registered by name: Chapters 2 and 3

The part of `StacksFrontier.EgaSgaIndex.EGAI` covering EGA I, Chapters 2 and 3 (preschemes and
their morphisms; products of preschemes).

Declarations realizing numbered items of EGA I, from the EGA/SGA concept index, that
are not tagged where they are declared: Mathlib and core declarations without an
`add_to_stacks` pointer in this library, and (with `--draft-only`) those of `StacksCore/`.
-/

add_to_ega "I 2.1.1" AlgebraicGeometry.IsAffineOpen
add_to_ega "I 2.1.1" AlgebraicGeometry.Scheme.affineOpens
add_to_ega "I 2.1.2" AlgebraicGeometry.Scheme
add_to_ega "I 2.1.2" AlgebraicGeometry.Scheme.mk
add_to_ega "I 2.1.3" "quasi-affine schemes" AlgebraicGeometry.Scheme.IsQuasiAffine.isBasis_basicOpen
add_to_ega "I 2.1.3" AlgebraicGeometry.Scheme.isBasis_affineOpens
add_to_ega "I 2.1.4" AlgebraicGeometry.instT0SpaceCarrierCarrierCommRingCat
add_to_ega "I 2.1.5" "partial" AlgebraicGeometry.instQuasiSoberCarrierCarrierCommRingCat
add_to_ega "I 2.1.6" AlgebraicGeometry.Scheme.functionField
add_to_ega "I 2.1.7" "more general" AlgebraicGeometry.Scheme.restrict
add_to_ega "I 2.1.8" AlgebraicGeometry.IsIntegral
add_to_ega "I 2.1.8" "partial" AlgebraicGeometry.irreducibleSpace_of_isIntegral
add_to_ega "I 2.1.8" AlgebraicGeometry.isIntegral_iff_irreducibleSpace_and_isReduced
add_to_ega "I 2.1.8" "partial" AlgebraicGeometry.isIntegral_of_irreducibleSpace_of_isReduced
add_to_ega "I 2.1.8" "integral implies reduced" AlgebraicGeometry.isReduced_of_isIntegral
add_to_ega "I 2.1.8" ConnectedSpace
add_to_ega "I 2.1.8" IrreducibleSpace
add_to_ega "I 2.1.8" IsIrreducible
add_to_ega "I 2.2.1" "more general" AlgebraicGeometry.LocallyRingedSpace.Hom
add_to_ega "I 2.2.1" AlgebraicGeometry.LocallyRingedSpace.Hom.mk
add_to_ega "I 2.2.1" AlgebraicGeometry.LocallyRingedSpace.homMk
add_to_ega "I 2.2.1" AlgebraicGeometry.Scheme.Hom
add_to_ega "I 2.2.1" AlgebraicGeometry.Scheme.Hom.mk
add_to_ega "I 2.2.2" "more general" AlgebraicGeometry.LocallyRingedSpace.comp
add_to_ega "I 2.2.2" "more general" AlgebraicGeometry.LocallyRingedSpace.instCategory
add_to_ega "I 2.2.2" AlgebraicGeometry.Scheme.Hom
add_to_ega "I 2.2.2" "partial" AlgebraicGeometry.Scheme.Hom.stalkMap_comp
add_to_ega "I 2.2.2" AlgebraicGeometry.Scheme.instCategory
add_to_ega "I 2.2.3" "more general" AlgebraicGeometry.IsOpenImmersion.le_monomorphisms
add_to_ega "I 2.2.3" "more general" AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.mono
add_to_ega "I 2.2.3" "more general" AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.mono
add_to_ega "I 2.2.3" "more general" AlgebraicGeometry.Scheme.ofRestrict
add_to_ega "I 2.2.3" "more general" AlgebraicGeometry.SheafedSpace.IsOpenImmersion.instMono
add_to_ega "I 2.2.4" "affine source" AlgebraicGeometry.AffineScheme.ΓIsEquiv
add_to_ega "I 2.2.4" "injectivity" AlgebraicGeometry.ext_of_isAffine
add_to_ega "I 2.2.5" "more general" Module.compHom
add_to_ega "I 2.2.5" "more general" ModuleCat.restrictScalars
add_to_ega "I 2.2.6" AlgebraicGeometry.IsDominant
add_to_ega "I 2.2.6" AlgebraicGeometry.Surjective
add_to_ega "I 2.2.6" "partial" AlgebraicGeometry.dominant_eq_topologically
add_to_ega "I 2.2.6" AlgebraicGeometry.isDominant_iff
add_to_ega "I 2.2.6" AlgebraicGeometry.surjective_eq_topologically
add_to_ega "I 2.2.6" AlgebraicGeometry.surjective_iff
add_to_ega "I 2.2.6" DenseRange
add_to_ega "I 2.2.6" IsOpenMap
add_to_ega "I 2.2.7" "more general" AlgebraicGeometry.IsDominant.comp_iff
add_to_ega "I 2.2.7" "more general" AlgebraicGeometry.Surjective.comp_iff
add_to_ega "I 2.2.7" AlgebraicGeometry.Surjective.of_comp
add_to_ega "I 2.2.7"
  AlgebraicGeometry.UniversallyOpen.instIsStableUnderCompositionSchemeTopologicallyIsOpenMap
add_to_ega "I 2.2.7" AlgebraicGeometry.instHasOfPrecompPropertySchemeSurjective
add_to_ega "I 2.2.7" AlgebraicGeometry.instIsDominantCompScheme
add_to_ega "I 2.2.7" "more general" AlgebraicGeometry.instIsMultiplicativeSchemeIsDominant
add_to_ega "I 2.2.7" "more general" AlgebraicGeometry.instIsMultiplicativeSchemeSurjective
add_to_ega "I 2.2.7" AlgebraicGeometry.isClosedMap_isStableUnderComposition
add_to_ega "I 2.2.7" "more general"
  CategoryTheory.Types.instIsStableUnderCompositionJointlySurjectivePrecoverage
add_to_ega "I 2.2.7" "more general" DenseRange.comp
add_to_ega "I 2.2.7" "more general" Function.Surjective.comp
add_to_ega "I 2.2.7" "more general" Function.Surjective.of_comp
add_to_ega "I 2.2.7" "more general" Function.Surjective.of_comp_iff
add_to_ega "I 2.2.7" "more general" IsClosedMap.comp
add_to_ega "I 2.2.7" "more general" IsClosedMap.of_comp_surjective
add_to_ega "I 2.2.7" "more general" IsOpenMap.comp
add_to_ega "I 2.2.7" "more general" Set.SurjOn.comp
add_to_ega "I 2.2.7" "more general" Set.SurjOn.comp_left
add_to_ega "I 2.2.7" "more general" Set.SurjOn.comp_right
add_to_ega "I 2.2.7" "more general" Set.SurjOn.of_comp
add_to_ega "I 2.2.8" AlgebraicGeometry.IsDominant.isZariskiLocalAtTarget
add_to_ega "I 2.2.8" "more general" AlgebraicGeometry.Scheme.Hom.resLE
add_to_ega "I 2.2.8" AlgebraicGeometry.isClosedMap_isZariskiLocalAtTarget
add_to_ega "I 2.2.8" AlgebraicGeometry.isOpenMap_isZariskiLocalAtTarget
add_to_ega "I 2.2.8" AlgebraicGeometry.morphismRestrict
add_to_ega "I 2.2.8" AlgebraicGeometry.surjective_isZariskiLocalAtTarget
add_to_ega "I 2.2.8" "necessity for closedness" IsClosedMap.restrictPreimage
add_to_ega "I 2.2.8" "necessity for openness" IsOpenMap.mapsToRestrict
add_to_ega "I 2.2.8" "necessity for openness" IsOpenMap.restrictPreimage
add_to_ega "I 2.2.8" "more general" Set.surjective_iff_surjective_of_iUnion_eq_univ
add_to_ega "I 2.2.8" "more general" TopologicalSpace.IsOpenCover.denseRange_iff_restrictPreimage
add_to_ega "I 2.2.8" "more general" TopologicalSpace.IsOpenCover.isClosedMap_iff_restrictPreimage
add_to_ega "I 2.2.8" "more general" TopologicalSpace.IsOpenCover.isOpenMap_iff_restrictPreimage
add_to_ega "I 2.2.10" AlgebraicGeometry.Scheme.Opens.instCoeOut
add_to_ega "I 2.2.10" "partial" AlgebraicGeometry.Scheme.Opens.toScheme_presheaf_obj
add_to_ega "I 2.3.1" "more general" AlgebraicGeometry.Scheme.Cover.instIsIsoFromGlued
add_to_ega "I 2.3.1" AlgebraicGeometry.Scheme.GlueData.glued
add_to_ega "I 2.3.1" AlgebraicGeometry.Scheme.GlueData.gluedScheme
-- The auto-generated instance name is longer than a line, so its identifier is assembled
-- from two pieces before being handed to `add_to_ega`.
run_cmd do
  let decl := Lean.mkIdent <| .str `AlgebraicGeometry.Scheme.GlueData <|
    "instCreatesColimitLocallyRingedSpaceWalkingMultispanProdJ" ++
      "MultispanDiagramForgetToLocallyRingedSpace"
  Lean.Elab.Command.elabCommand (← `(command| add_to_ega "I 2.3.1" $decl:ident))
add_to_ega "I 2.3.1" AlgebraicGeometry.Scheme.GlueData.isoLocallyRingedSpace
add_to_ega "I 2.3.1" "partial" AlgebraicGeometry.Scheme.affineCover
add_to_ega "I 2.3.1" "partial" AlgebraicGeometry.Scheme.affineOpenCover
add_to_ega "I 2.3.1" "partial" AlgebraicGeometry.iSup_affineOpens_eq_top
add_to_ega "I 2.3.2" "partial" AlgebraicGeometry.IsAffineOpen.Spec_basicOpen
-- The auto-generated instance name is longer than a line, so its identifier is assembled
-- from two pieces before being handed to `add_to_ega`.
run_cmd do
  let decl := Lean.mkIdent <| .str `AlgebraicGeometry.IsAffineOpen <|
    "instAwayCarrierObjOppositeOpensCarrierCarrierCommRingCat" ++
      "SpecPresheafOpOpensBasicOpen"
  Lean.Elab.Command.elabCommand (← `(command| add_to_ega "I 2.3.2" "partial" $decl:ident))
add_to_ega "I 2.3.2" "partial" AlgebraicGeometry.IsAffineOpen.instIsAffineToSchemeBasicOpen
-- The auto-generated instance name is longer than a line, so its identifier is assembled
-- from two pieces before being handed to `add_to_ega`.
run_cmd do
  let decl := Lean.mkIdent <| .str `AlgebraicGeometry.StructureSheaf <|
    "instAwayObjOppositeOpensCarrierTopObjFunctorTypeIsSheaf" ++
      "GrothendieckTopologyStructureSheafInTypeOpBasicOpen"
  Lean.Elab.Command.elabCommand (← `(command| add_to_ega "I 2.3.2" "partial" $decl:ident))
add_to_ega "I 2.3.2" "more general" AlgebraicGeometry.basicOpenIsoSpecAway
add_to_ega "I 2.4.1" "more general" AlgebraicGeometry.Scheme.preimage_eq_top_of_closedPoint_mem
add_to_ega "I 2.4.1" "more general" IsLocalRing.closedPoint_mem_iff
add_to_ega "I 2.4.1" "more general" IsLocalRing.closed_point_mem_iff
add_to_ega "I 2.4.1" "partial" IsLocalRing.isClosed_singleton_closedPoint
add_to_ega "I 2.4.1" "more general" IsLocalRing.specializes_closedPoint
add_to_ega "I 2.4.1" "more general" isLocalRing_iff_existsUnique_isClosed_singleton
add_to_ega "I 2.4.2" AlgebraicGeometry.IsAffineOpen.fromSpecStalk
add_to_ega "I 2.4.2" AlgebraicGeometry.Scheme.Opens.fromSpecStalkOfMem
add_to_ega "I 2.4.2" "image of ψ equals S_y" AlgebraicGeometry.Scheme.range_fromSpecStalk
add_to_ega "I 2.4.2" "special case" AlgebraicGeometry.Scheme.stalkClosedPointTo_fromSpecStalk
add_to_ega "I 2.4.2" AlgebraicGeometry.instCanonicallyOverSpecStalkCommRingCatPresheaf
add_to_ega "I 2.4.2" "partial" AlgebraicGeometry.instIsPreimmersionFromSpecStalk
add_to_ega "I 2.4.2" AlgebraicGeometry.instOverSpecStalkCommRingCatPresheaf
add_to_ega "I 2.4.2" "special case" AlgebraicGeometry.isIso_SpecMap_stakMap_localization
add_to_ega "I 2.4.4" "partial" AlgebraicGeometry.Scheme.Spec_stalkClosedPointTo_fromSpecStalk
add_to_ega "I 2.4.4" "partial" AlgebraicGeometry.Scheme.Spec_stalkClosedPointTo_fromSpecStalk_assoc
add_to_ega "I 2.4.4" "partial" AlgebraicGeometry.Scheme.isLocalHom_stalkClosedPointTo
add_to_ega "I 2.4.4" "partial" AlgebraicGeometry.Scheme.isLocalHom_stalkClosedPointTo'
add_to_ega "I 2.4.4" AlgebraicGeometry.SpecToEquivOfLocalRing
add_to_ega "I 2.4.5" AlgebraicGeometry.Scheme.descResidueField
add_to_ega "I 2.4.5" AlgebraicGeometry.Scheme.instUniqueCarrierCarrierCommRingCatSpecOf
add_to_ega "I 2.4.5" "special case"
  AlgebraicGeometry.Scheme.instUniqueCarrierCarrierCommRingCatSpecResidueField
add_to_ega "I 2.4.5" "factorization for stalks" AlgebraicGeometry.Scheme.residue_descResidueField
add_to_ega "I 2.4.5" IsLocalRing.ResidueField
add_to_ega "I 2.4.5" IsLocalRing.ResidueField.lift
add_to_ega "I 2.4.5" "partial" IsLocalRing.ResidueField.lift_comp_residue
add_to_ega "I 2.4.5" "kernel clause" IsLocalRing.comap_closedPoint
add_to_ega "I 2.4.5" "kernel clause" IsLocalRing.isLocalHom_iff_comap_closedPoint
add_to_ega "I 2.4.5" "special case" IsLocalRing.ker_eq_maximalIdeal
add_to_ega "I 2.4.5" IsLocalRing.residue
add_to_ega "I 2.4.5" PrimeSpectrum.instUnique
add_to_ega "I 2.4.5" "at most one point" PrimeSpectrum.subsingleton_iff_isField_of_isReduced
add_to_ega "I 2.4.5" "more general" PrimeSpectrum.unique_of_ringKrullDimLE_zero
add_to_ega "I 2.4.5" "at most one point" Ring.KrullDimLE.subsingleton_primeSpectrum
add_to_ega "I 2.4.5" "partial" map_nonunit
add_to_ega "I 2.4.6" AlgebraicGeometry.Scheme.descResidueField
add_to_ega "I 2.4.6" "partial"
  AlgebraicGeometry.Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField
add_to_ega "I 2.4.6" AlgebraicGeometry.Scheme.fromSpecResidueField
add_to_ega "I 2.4.7" "zero ideal, special case" AlgebraicGeometry.Scheme.Opens.fromSpecStalkOfMem
add_to_ega "I 2.4.8" "more general" AlgebraicGeometry.Scheme.preimage_eq_top_of_closedPoint_mem
add_to_ega "I 2.4.8" "partial" CommRing.Pic.instSubsingletonOfIsLocalRing
add_to_ega "I 2.4.8" "more general" IsLocalRing.closedPoint_mem_iff
add_to_ega "I 2.4.8" "more general" IsLocalRing.closed_point_mem_iff
add_to_ega "I 2.4.8" "partial" instSubsingletonPicOfIsDomainOfIsGCDMonoid
add_to_ega "I 2.5.1" AlgebraicGeometry.Scheme.CanonicallyOver
add_to_ega "I 2.5.1" AlgebraicGeometry.Scheme.Over
add_to_ega "I 2.5.1" CategoryTheory.Over.hom
add_to_ega "I 2.5.1" CategoryTheory.OverClass
add_to_ega "I 2.5.2" AlgebraicGeometry.Scheme.Hom.IsOver
add_to_ega "I 2.5.2" AlgebraicGeometry.Scheme.Hom.isOver_iff
add_to_ega "I 2.5.2" "more general" CategoryTheory.Over.Hom
add_to_ega "I 2.5.3" "partial" AlgebraicGeometry.Scheme.Cover.glueMorphisms
add_to_ega "I 2.5.3" "uniqueness" AlgebraicGeometry.Scheme.Cover.hom_ext
add_to_ega "I 2.5.3" "partial" AlgebraicGeometry.Scheme.Cover.ι_glueMorphisms
add_to_ega "I 2.5.3" "partial" AlgebraicGeometry.Scheme.Cover.ι_glueMorphisms_assoc
add_to_ega "I 2.5.3" "partial" AlgebraicGeometry.Scheme.OpenCover.glueMorphismsOfLocallyDirected
add_to_ega "I 2.5.3" "partial" AlgebraicGeometry.Scheme.OpenCover.glueMorphismsOverOfLocallyDirected
add_to_ega "I 2.5.3" "partial" AlgebraicGeometry.Scheme.OpenCover.map_glueMorphismsOfLocallyDirected
add_to_ega "I 2.5.3" "partial"
  AlgebraicGeometry.Scheme.OpenCover.map_glueMorphismsOverOfLocallyDirected_left
add_to_ega "I 2.5.3" "partial"
  AlgebraicGeometry.Scheme.OpenCover.map_glueMorphismsOverOfLocallyDirected_left_assoc
add_to_ega "I 2.5.3" AlgebraicGeometry.Scheme.Opens.ι_comp_over
add_to_ega "I 2.5.4" "more general" AlgebraicGeometry.Scheme.Hom.resLE
add_to_ega "I 2.5.4" "more general" AlgebraicGeometry.morphismRestrict
add_to_ega "I 2.5.5" AlgebraicGeometry.Scheme.Hom.IsOver
add_to_ega "I 2.5.5" "more general" AlgebraicGeometry.Scheme.Hom.isOver_iff
add_to_ega "I 2.5.5" "more general" CategoryTheory.Over.Hom
add_to_ega "I 3.2.1" "more general" CategoryTheory.Limits.IsLimit
add_to_ega "I 3.2.1" "more general" CategoryTheory.Limits.prod.fst
add_to_ega "I 3.2.1" "more general" CategoryTheory.Limits.prod.snd
add_to_ega "I 3.2.1" "more general" CategoryTheory.Limits.pullback.fst
add_to_ega "I 3.2.1" "more general" CategoryTheory.Limits.pullback.snd
add_to_ega "I 3.2.2" Algebra.TensorProduct.includeLeft
add_to_ega "I 3.2.2" Algebra.TensorProduct.includeRight
add_to_ega "I 3.2.2" "partial"
  AlgebraicGeometry.Scheme.Pullback.isAffine_of_isAffine_isAffine_isAffine
add_to_ega "I 3.2.2" "more general" AlgebraicGeometry.instIsAffinePullbackSchemeOfIsAffineHom
add_to_ega "I 3.2.2" "more general" AlgebraicGeometry.instIsAffinePullbackSchemeOfIsAffineHom_1
add_to_ega "I 3.2.2" "partial" AlgebraicGeometry.prodComparison_algSpec_left
add_to_ega "I 3.2.2" AlgebraicGeometry.pullbackSpecIso
add_to_ega "I 3.2.2" AlgebraicGeometry.pullbackSpecIso'
add_to_ega "I 3.2.2" "partial" AlgebraicGeometry.pullbackSpecIso_hom_base
add_to_ega "I 3.2.2" "partial" AlgebraicGeometry.pullbackSpecIso_hom_base_assoc
add_to_ega "I 3.2.2" "partial" AlgebraicGeometry.pullbackSpecIso_hom_fst
add_to_ega "I 3.2.2" "partial" AlgebraicGeometry.pullbackSpecIso_hom_fst'
add_to_ega "I 3.2.2" "partial" AlgebraicGeometry.pullbackSpecIso_hom_fst'_assoc
add_to_ega "I 3.2.2" "partial" AlgebraicGeometry.pullbackSpecIso_hom_snd
add_to_ega "I 3.2.2" "partial" AlgebraicGeometry.pullbackSpecIso_hom_snd_assoc
add_to_ega "I 3.2.2" "partial" AlgebraicGeometry.pullbackSpecIso_inv_fst_assoc
add_to_ega "I 3.2.2" "partial" AlgebraicGeometry.pullbackSpecIso_inv_snd_assoc
add_to_ega "I 3.2.3" Algebra.TensorProduct.lift
add_to_ega "I 3.2.3" "τ(b⊗c)=ρ(b)σ(c)" Algebra.TensorProduct.lift_tmul
add_to_ega "I 3.2.5" "Forward clause" AlgebraicGeometry.Scheme.Hom.isPullback_resLE
add_to_ega "I 3.2.6" "special case" AlgebraicGeometry.Scheme.Pullback.affine_affine_hasPullback
add_to_ega "I 3.2.6" "X, Y and S affine" AlgebraicGeometry.Scheme.Pullback.affine_hasPullback
add_to_ega "I 3.2.6" "S affine" AlgebraicGeometry.Scheme.Pullback.base_affine_hasPullback
add_to_ega "I 3.2.6" AlgebraicGeometry.Scheme.Pullback.instHasPullback
add_to_ega "I 3.2.6" AlgebraicGeometry.Scheme.Pullback.instHasPullbacks
add_to_ega "I 3.2.6" AlgebraicGeometry.instCartesianMonoidalCategoryOverScheme
add_to_ega "I 3.2.6" "special case" AlgebraicGeometry.instCartesianMonoidalCategoryScheme
add_to_ega "I 3.2.6" "more general" AlgebraicGeometry.instHasFiniteLimitsScheme
add_to_ega "I 3.2.6.1" "more general" AlgebraicGeometry.Scheme.Hom.isPullback_resLE
add_to_ega "I 3.2.6.1" "special case" AlgebraicGeometry.isPullback_morphismRestrict
add_to_ega "I 3.2.6.1" "special case" AlgebraicGeometry.isPullback_opens_inf
add_to_ega "I 3.2.6.2" "special case" AlgebraicGeometry.Scheme.isPullback_of_openCover
add_to_ega "I 3.2.6.3" "special case" AlgebraicGeometry.Scheme.Pullback.hasPullback_of_cover
add_to_ega "I 3.2.7" AlgebraicGeometry.Scheme.Hom.isPullback_resLE
add_to_ega "I 3.2.7" "special case" AlgebraicGeometry.isPullback_opens_inf
add_to_ega "I 3.2.7" "special case" AlgebraicGeometry.isPullback_opens_inf_le
add_to_ega "I 3.2.7" "special case" AlgebraicGeometry.morphismRestrictOpensRange
add_to_ega "I 3.3.1" CategoryTheory.HomIsOver
add_to_ega "I 3.3.1" CategoryTheory.Over.Hom
add_to_ega "I 3.3.1" CategoryTheory.OverClass
add_to_ega "I 3.3.1" CategoryTheory.instCategoryOver
add_to_ega "I 3.3.2" AlgebraicGeometry.instCartesianMonoidalCategoryOverScheme
add_to_ega "I 3.3.2" "special case" AlgebraicGeometry.instCartesianMonoidalCategoryScheme
add_to_ega "I 3.3.2" "more general" CategoryTheory.Limits.prod.functor
add_to_ega "I 3.3.2" "partial" CategoryTheory.Limits.prod.map
add_to_ega "I 3.3.2" "partial" CategoryTheory.Limits.prod.map_comp_id
add_to_ega "I 3.3.2" "partial" CategoryTheory.Limits.prod.map_id_comp
add_to_ega "I 3.3.2" "identities" CategoryTheory.Limits.prod.map_id_id
add_to_ega "I 3.3.2" "partial" CategoryTheory.Limits.pullback.map
add_to_ega "I 3.3.2" "partial" CategoryTheory.Over.star
add_to_ega "I 3.3.3" "more general" CategoryTheory.Limits.prod.leftUnitor
add_to_ega "I 3.3.3" "more general" CategoryTheory.Limits.prod.rightUnitor
add_to_ega "I 3.3.5" "special case" AlgebraicGeometry.Scheme.Pullback.affine_affine_hasPullback
add_to_ega "I 3.3.5" "special case" AlgebraicGeometry.Scheme.Pullback.affine_hasPullback
add_to_ega "I 3.3.5" "special case" AlgebraicGeometry.Scheme.Pullback.base_affine_hasPullback
add_to_ega "I 3.3.5" "existence for n = 2" AlgebraicGeometry.Scheme.Pullback.instHasPullback
add_to_ega "I 3.3.5" "existence for n = 2" AlgebraicGeometry.Scheme.Pullback.instHasPullbacks
add_to_ega "I 3.3.5" AlgebraicGeometry.instCartesianMonoidalCategoryOverScheme
add_to_ega "I 3.3.5" "special case" AlgebraicGeometry.instCartesianMonoidalCategoryScheme
add_to_ega "I 3.3.5" "more general" AlgebraicGeometry.instHasFiniteLimitsScheme
add_to_ega "I 3.3.5" "special case" CategoryTheory.Limits.BinaryFan.associator
add_to_ega "I 3.3.5" CategoryTheory.Limits.HasFiniteProducts
add_to_ega "I 3.3.5" "more general"
  CategoryTheory.Limits.hasFiniteLimits_of_hasTerminal_and_pullbacks
add_to_ega "I 3.3.5" CategoryTheory.Limits.prod.associator
add_to_ega "I 3.3.5" "special case" CategoryTheory.Limits.prod.braiding
add_to_ega "I 3.3.5" CategoryTheory.Limits.pullback
add_to_ega "I 3.3.5" "special case" CategoryTheory.Limits.pullbackSymmetry
add_to_ega "I 3.3.6" AlgebraicGeometry.Scheme.canonicallyOverPullback
add_to_ega "I 3.3.6" "partial" AlgebraicGeometry.Scheme.canonicallyOverPullback_over
add_to_ega "I 3.3.6" "more general" CategoryTheory.Limits.pullback
add_to_ega "I 3.3.6" "partial" CategoryTheory.Limits.pullback.condition
add_to_ega "I 3.3.6" "more general" CategoryTheory.Limits.pullback.snd
add_to_ega "I 3.3.7" "more general" CategoryTheory.Limits.pullback.map
add_to_ega "I 3.3.8" "partial" CategoryTheory.Limits.pullback.hom_ext
add_to_ega "I 3.3.8" "existence" CategoryTheory.Limits.pullback.lift
add_to_ega "I 3.3.12" "more general" CategoryTheory.Limits.Pi.map_mono
add_to_ega "I 3.3.12" "more general"
  CategoryTheory.Limits.PullbackCone.mono_fst_of_is_pullback_of_mono
add_to_ega "I 3.3.12" "more general"
  CategoryTheory.Limits.PullbackCone.mono_snd_of_is_pullback_of_mono
add_to_ega "I 3.3.12" "more general" CategoryTheory.Limits.prod.map_mono
add_to_ega "I 3.3.12" "more general" CategoryTheory.Limits.pullback.snd_of_mono
add_to_ega "I 3.3.13" "special case" AlgebraicGeometry.AffineSpace.isoOfIsAffine
add_to_ega "I 3.3.13" "Affineness of X ×_S S′"
  AlgebraicGeometry.Scheme.Pullback.isAffine_of_isAffine_isAffine_isAffine
add_to_ega "I 3.3.13" AlgebraicGeometry.Scheme.Spec
add_to_ega "I 3.3.13" "partial" AlgebraicGeometry.Spec.homEquiv
add_to_ega "I 3.3.13" AlgebraicGeometry.Spec.map
add_to_ega "I 3.3.13" "Affineness of X ×_S S′"
  AlgebraicGeometry.instIsAffinePullbackSchemeOfIsAffineHom_1
add_to_ega "I 3.3.13" AlgebraicGeometry.pullbackSpecIso
add_to_ega "I 3.3.13" AlgebraicGeometry.pullbackSpecIso'
add_to_ega "I 3.3.13" AlgebraicGeometry.specOverSpec
add_to_ega "I 3.3.13" CategoryTheory.Limits.pullback
add_to_ega "I 3.3.14" AlgebraicGeometry.Scheme.Hom.IsOver
add_to_ega "I 3.3.14" "more general" AlgebraicGeometry.Scheme.Hom.isOver_iff
add_to_ega "I 3.3.14" CategoryTheory.Limits.pullback.lift
add_to_ega "I 3.3.14" CategoryTheory.SplitEpi
add_to_ega "I 3.3.15" AlgebraicGeometry.AffineSpace
add_to_ega "I 3.3.15" "partial" AlgebraicGeometry.AffineSpace.SpecIso
add_to_ega "I 3.3.15" "partial" AlgebraicGeometry.AffineSpace.SpecIso_inv_over
add_to_ega "I 3.3.15" "partial" AlgebraicGeometry.AffineSpace.homOfVector_appTop_coord
add_to_ega "I 3.3.15" "partial" AlgebraicGeometry.AffineSpace.homOverEquiv_apply
add_to_ega "I 3.3.15" "partial" AlgebraicGeometry.AffineSpace.homOverEquiv_symm_apply_coe
add_to_ega "I 3.3.15" "partial" AlgebraicGeometry.AffineSpace.hom_ext
add_to_ega "I 3.3.15" "partial" AlgebraicGeometry.AffineSpace.isoOfIsAffine
add_to_ega "I 3.3.15" AlgebraicGeometry.AffineSpace.over
add_to_ega "I 3.3.15" AlgebraicGeometry.AffineSpace.toSpecMvPoly
add_to_ega "I 3.3.15" "partial" AlgebraicGeometry.AffineSpace.toSpecMvPolyIntEquiv
add_to_ega "I 3.3.15" "partial" AlgebraicGeometry.AffineSpace.toSpecMvPolyIntEquiv_comp
add_to_ega "I 3.3.15" "partial" AlgebraicGeometry.AffineSpace.toSpecMvPolyIntEquiv_symm_apply
add_to_ega "I 3.3.15" "affine schemes" AlgebraicGeometry.specOverSpec
add_to_ega "I 3.3.15" AlgebraicGeometry.specULiftZIsTerminal
add_to_ega "I 3.3.15" AlgebraicGeometry.specZIsTerminal
add_to_ega "I 3.3.15" "partial" Polynomial.aeval
add_to_ega "I 3.4.1" "more general" CategoryTheory.yoneda
add_to_ega "I 3.4.2" Function.Pullback
add_to_ega "I 3.4.3" "more general" CategoryTheory.Limits.PushoutCocone.isColimitYonedaEquiv
add_to_ega "I 3.4.3" "more general" CategoryTheory.Square.isPushout_iff_op_map_yoneda_isPullback
add_to_ega "I 3.4.3" CategoryTheory.yoneda
add_to_ega "I 3.4.5" "partial, special case" AlgebraicGeometry.Scheme.SpecToEquivOfField_apply_fst
add_to_ega "I 3.4.5" AlgebraicGeometry.SpecToEquivOfLocalRing
add_to_ega "I 3.4.5" "partial" AlgebraicGeometry.ext_of_apply_closedPoint_eq
add_to_ega "I 3.4.7" "partial" AlgebraicGeometry.Scheme.Pullback.Triplet.exists_preimage
add_to_ega "I 3.4.7" "partial" AlgebraicGeometry.Scheme.Pullback.Triplet.ofPoint
add_to_ega "I 3.4.7" "partial" AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback
add_to_ega "I 3.4.7" "partial" AlgebraicGeometry.Scheme.exists_preimage_of_isPullback
add_to_ega "I 3.4.8" "special case" AlgebraicGeometry.Scheme.Pullback.range_fst
add_to_ega "I 3.4.8" "more general" AlgebraicGeometry.Scheme.image_preimage_eq_of_isPullback
add_to_ega "I 3.5.1" "more general" CategoryTheory.MorphismProperty.IsStableUnderBaseChangeAgainst
add_to_ega "I 3.5.1" "more general" CategoryTheory.MorphismProperty.IsStableUnderProductsOfShape
add_to_ega "I 3.5.1" "special case" CommAlgCat.FiniteEtale.baseChange_map_hom
add_to_ega "I 3.5.2" "more general"
  AlgebraicGeometry.Scheme.instIsStableUnderBaseChangeJointlySurjectivePrecoverage
add_to_ega "I 3.5.2" AlgebraicGeometry.Surjective.instFstScheme
add_to_ega "I 3.5.2" AlgebraicGeometry.Surjective.instSndScheme
add_to_ega "I 3.5.4" AlgebraicGeometry.UniversallyInjective
add_to_ega "I 3.5.4" AlgebraicGeometry.tfae_universallyInjective
add_to_ega "I 3.5.8" AlgebraicGeometry.tfae_universallyInjective
add_to_ega "I 3.5.8" "special case" IsPurelyInseparable.injective_comp_algebraMap
add_to_ega "I 3.5.8" "special case" IsPurelyInseparable.of_injective_comp_algebraMap
add_to_ega "I 3.5.8" "special case" instSubsingletonAlgHomOfIsPurelyInseparable
add_to_ega "I 3.5.10" "special case" AlgebraicGeometry.Scheme.Hom.fiberHomeo
add_to_ega "I 3.6.1" "special case" AlgebraicGeometry.Scheme.Hom.fiberHomeo
add_to_ega "I 3.6.1" "partial" AlgebraicGeometry.Scheme.Hom.fiberHomeo_apply
add_to_ega "I 3.6.1" "partial" AlgebraicGeometry.Scheme.Hom.fiberι_fiberHomeo_symm
add_to_ega "I 3.6.1" "partial" PrimeSpectrum.coe_preimageHomeomorphFiber_symm_apply_coe_asIdeal
add_to_ega "I 3.6.1" "special case" PrimeSpectrum.preimageHomeomorphFiber
add_to_ega "I 3.6.2" AlgebraicGeometry.Scheme.Hom.fiber
add_to_ega "I 3.6.2" AlgebraicGeometry.Scheme.Hom.fiberHomeo
add_to_ega "I 3.6.2" AlgebraicGeometry.Scheme.Hom.fiberOverSpecResidueField
add_to_ega "I 3.6.2" AlgebraicGeometry.Scheme.Hom.fiberToSpecResidueField
add_to_ega "I 3.6.2" AlgebraicGeometry.Scheme.Hom.fiberι
add_to_ega "I 3.6.3" "more general" AlgebraicGeometry.Scheme.Hom.isPullback_resLE
add_to_ega "I 3.7.2" "more general" AlgebraicGeometry.Scheme.Hom.fiberOverSpecResidueField
add_to_ega "I 3.7.2" "partial" AlgebraicGeometry.genericPoint_eq_bot_of_affine
add_to_ega "I 3.7.2" "P=Spec(A)" AlgebraicGeometry.instIsNoetherianSpecOfIsNoetherianRingCarrier
add_to_ega "I 3.7.2" "P=Spec(A)" AlgebraicGeometry.instIsNoetherianSpecOfOfIsNoetherianRing
add_to_ega "I 3.7.2" "P=Spec(A)" AlgebraicGeometry.isNoetherian_Spec
add_to_ega "I 3.7.2" "partial" IsLocalRing.isClosed_singleton_closedPoint
add_to_ega "I 3.7.3" "more general" AlgebraicGeometry.IsProper.eq_valuativeCriterion
