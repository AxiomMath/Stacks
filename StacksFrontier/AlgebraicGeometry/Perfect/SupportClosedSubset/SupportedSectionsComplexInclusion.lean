module

public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.DerivedFunctorAtKInjectives
public import StacksFrontier.Topology.Sheaves.Cohomology.ExtensionByZero.RestrictionOfKInjectives
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.SupportedSectionsSheafTriangle

/-!
# The subcomplex of sections supported on a closed subset of an injective complex

Let `Z` be a closed subset of a ringed space `X`, let `U = X ∖ Z` and let `ℐ^•` be a complex of
injective `𝒪_X`-modules.  Applying the sheaf of sections supported on `Z` degreewise gives a
subcomplex `ℋ_Z(ℐ^•) ⊆ ℐ^•`, and the quotient is the complex `j_*(ℐ^•|_U)`, by the short exact
sequence `0 ⟶ ℋ_Z(ℐ) ⟶ ℐ ⟶ j_*(ℐ|_U) ⟶ 0` of Stacks 0G72 at an injective module.

If moreover `ℐ^•` is K-injective and its restriction to `U` is acyclic, the quotient complex is
acyclic: `ℐ^•|_U` is again K-injective, so being acyclic it is null-homotopic, and `j_*` of a
null-homotopic complex is null-homotopic.  Hence the inclusion `ℋ_Z(ℐ^•) ⟶ ℐ^•` is a
quasi-isomorphism.

## Main definitions

* `supportedSectionsComplexι`: the inclusion `ℋ_Z(ℐ^•) ⟶ ℐ^•` of the subcomplex of sections
  supported on `Z`, and `restrictPushComplexUnit`, the restriction `ℐ^• ⟶ j_*(ℐ^•|_U)`.
* `supportedSectionsRestrictPushComplexShortComplex`: the short complex they form.

## Main results

* `supportedSectionsRestrictPushComplexShortExact`: that short complex is short exact when every
  term of `ℐ^•` is injective.
* `isIso_Q_map_supportedSectionsComplexι`: the inclusion is a quasi-isomorphism when `ℐ^•` is in
  addition K-injective with acyclic restriction to `U`.

## Implementation notes

Short exactness is checked degreewise, where it is
`Stacks.Cohomology.SupportedComplexes.supportedSectionsRestrictPushShortExact`, and assembled by
`HomologicalComplex.shortExact_of_degreewise_shortExact`.  The passage from short exactness to
the distinguished triangle in the derived category is `DerivedCategory.triangleOfSES`, and a
distinguished triangle whose third vertex vanishes has an invertible first map.

The acyclicity of `j_*(ℐ^•|_U)` is
`Stacks.Perfect.KInjectiveValues.isZero_Q_obj_mapHomologicalComplex` applied to the additive
functor `j_*`; the hypothesis that `ℐ^•|_U` is K-injective is Stacks 08BS.

## References

* [Stacks Project, Tag 0G72](https://stacks.math.columbia.edu/tag/0G72)
* [Stacks Project, Tag 0G7M](https://stacks.math.columbia.edu/tag/0G7M)
* [Stacks Project, Tag 08BS](https://stacks.math.columbia.edu/tag/08BS)
* [Stacks Project, Tag 01E1](https://stacks.math.columbia.edu/tag/01E1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open CategoryTheory.Pretriangulated
open ExtensionByZeroModules
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.RestrictionCover
open Stacks.Cohomology.SectionsWithSupport (openComplement)
open Stacks.Cohomology.SupportedComplexes
open Stacks.SheafOfModules.SupportedSections

universe u

namespace Stacks.Perfect.SupportedSectionsComplex

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSpace.{u, u}) (Z : Set X.carrier) (hZ : IsClosed Z)
  (I : CochainComplex (_root_.SheafOfModules.{u} (structureSheafRing X)) ℤ)

/-- The subcomplex of sections supported on `Z` of a complex of `𝒪_X`-modules, included into
the complex itself. -/
public def supportedSectionsComplexι :
    ((supportedSectionsFunctor X Z).mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ I where
  f n := (supportedSectionsSubsheafInclusion X Z).app (I.X n)
  comm' i j _ := (supportedSectionsSubsheafInclusion X Z).naturality (I.d i j)

/-- The restriction of a complex of `𝒪_X`-modules to the complement of `Z`, pushed forward
to `X`. -/
public def restrictPushComplexUnit :
    I ⟶ ((restrictPush (structureSheafRing X) (openComplement Z hZ)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I where
  f n := (jStarAdjunction (openComplement Z hZ) (structureSheafRing X)).unit.app (I.X n)
  comm' i j _ := ((jStarAdjunction (openComplement Z hZ) (structureSheafRing X)).unit.naturality
    (I.d i j)).symm

/-- The short complex `ℋ_Z(ℐ^•) ⟶ ℐ^• ⟶ j_*(ℐ^•|_U)` of complexes of `𝒪_X`-modules. -/
public def supportedSectionsRestrictPushComplexShortComplex :
    ShortComplex (CochainComplex (_root_.SheafOfModules.{u} (structureSheafRing X)) ℤ) :=
  ShortComplex.mk (supportedSectionsComplexι X Z I) (restrictPushComplexUnit X Z hZ I)
    (HomologicalComplex.hom_ext _ _ fun n =>
      NatTrans.congr_app (supportedSectionsSubsheafInclusion_comp_unit X Z hZ) (I.X n))

/-- **The sections supported on `Z` of a complex of injectives form a subcomplex with quotient
the pushforward of the restriction to the complement.**  Degreewise this is the short exact
sequence of Stacks 0G72 at an injective module. -/
public theorem supportedSectionsRestrictPushComplexShortExact [∀ n, Injective (I.X n)] :
    (supportedSectionsRestrictPushComplexShortComplex X Z hZ I).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n =>
    supportedSectionsRestrictPushShortExact X Z hZ (I.X n)

/-- **The pushforward of the restriction of a K-injective complex to the complement of `Z` is
acyclic once that restriction is.**  The restriction is again K-injective by Stacks 08BS, so
being acyclic it is null-homotopic, and the additive functor `j_*` preserves null-homotopies. -/
public theorem isZero_Q_obj_restrictPushComplex (hI : I.IsKInjective)
    (hU : (((jStar (openComplement Z hZ) (structureSheafRing X)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I).Acyclic) :
    IsZero (DerivedCategory.Q.obj
      (((restrictPush (structureSheafRing X) (openComplement Z hZ)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I)) := by
  let _ := hI
  let _ : (jPush (openComplement Z hZ) (structureSheafRing X)).IsRightAdjoint :=
    (jStarAdjunction (openComplement Z hZ) (structureSheafRing X)).isRightAdjoint
  let _ : (jPush (openComplement Z hZ) (structureSheafRing X)).Additive :=
    Functor.additive_of_preserves_binary_products _
  have hKI : CochainComplex.IsKInjective
      (((jStar (openComplement Z hZ) (structureSheafRing X)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I) := inferInstance
  exact (Stacks.Perfect.KInjectiveValues.isZero_Q_obj_mapHomologicalComplex
    (jPush (openComplement Z hZ) (structureSheafRing X)) _ hKI hU).of_iso (DerivedCategory.Q.mapIso
    ((Functor.mapHomologicalComplexCompIso
      (Iso.refl (restrictPush (structureSheafRing X) (openComplement Z hZ)))
      (ComplexShape.up ℤ)).app I))

/-- **The inclusion of the sections supported on `Z` into a K-injective complex of injectives
whose restriction to `X ∖ Z` is acyclic is a quasi-isomorphism.**  The quotient complex is
acyclic, so in the distinguished triangle attached to the short exact sequence the third vertex
vanishes and the first map is invertible. -/
public theorem isIso_Q_map_supportedSectionsComplexι [∀ n, Injective (I.X n)]
    (hI : I.IsKInjective)
    (hU : (((jStar (openComplement Z hZ) (structureSheafRing X)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I).Acyclic) :
    IsIso (DerivedCategory.Q.map (supportedSectionsComplexι X Z I)) := by
  have hS := supportedSectionsRestrictPushComplexShortExact X Z hZ I
  have hzero : IsZero (DerivedCategory.triangleOfSES hS).obj₃ :=
    isZero_Q_obj_restrictPushComplex X Z hZ I hI hU
  exact (Triangle.isZero₃_iff_isIso₁ _ (DerivedCategory.triangleOfSES_distinguished hS)).1 hzero

end Stacks.Perfect.SupportedSectionsComplex

end
