module

public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedSpaceDifferentials
public import StacksFrontier.Topology.Sheaves.Modules.Differentials.Functoriality

/-!
# Comparing the two descriptions of the sheaf of relative differentials

For a morphism of ringed spaces `h : X ⟶ S` the sheaf `Ω_{X/S}` admits two descriptions:
as the object corepresenting relative derivations, which is
`AlgebraicGeometry.SheafOfModules.moduleOfDifferentials (inverseImageStructureMap h)`, and as
the sheafification of the presheaf of sectionwise Kähler differentials, which is
`Stacks.Sheaves.RingedSpaceDifferentials.moduleOfDifferentials h`. Each carries its own
universal relative derivation, and each has its own canonical comparison map for a commutative
square and its own canonical map to the differentials over an intermediate space.

This file identifies the two, maps and all. The identification is the specialisation of
`AlgebraicGeometry.SheafOfModules.moduleOfDifferentialsIsoSectionwise` to the structural map of
a morphism of ringed spaces; everything else follows from it, because both canonical maps are
characterised by their action on the universal derivation and the identification carries one
universal derivation to the other.

The point of doing so is that the exact triangle of a composable pair is available only for the
sheafified description, while the morphisms of schemes are built on the corepresentable one.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.relativeDifferentialsIsoSectionwise`: the identification.

## Main results

* `AlgebraicGeometry.SheafOfModules.relativeDifferentialsIsoSectionwise_hom_app_d` and
  `…_inv_app_d`: the identification carries one universal derivation to the other.
* `AlgebraicGeometry.SheafOfModules.differentialMap_eq_sectionwise`: the canonical comparison
  maps of the two descriptions agree under the identification.

## Implementation notes

The two descriptions of `Ω_{X/S}` are not merely isomorphic objects of the same category: the
second is definitionally the sheafification which the first is compared to, so the comparison
is obtained without any transport of structure, and the compatibility of the two universal
derivations is the existing compatibility statement.

Agreement of the comparison maps is proved by uniqueness: the conjugate of one of them by the
identification satisfies the defining compatibility of the other, which is checked by pushing
the identification through the hom-set bijection of `f^* ⊣ f_*` in both variables.

## References

* [Stacks Project, Tag 08RU](https://stacks.math.columbia.edu/tag/08RU)
* [Stacks Project, Tag 0H79](https://stacks.math.columbia.edu/tag/0H79)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
-- the structure map `h⁻¹𝒪_S ⟶ 𝒪_X` of a morphism of ringed spaces; the rest of
-- `Stacks.Sheaves.RingedSpaceDifferentials` is named in full below, to keep its
-- `moduleOfDifferentials` and `universalDerivation` apart from the corepresentable ones
open Stacks.Sheaves.RingedSpaceDifferentials (inverseImageStructureMap)

universe u

namespace AlgebraicGeometry.SheafOfModules

variable {X' X Y S' S : AlgebraicGeometry.RingedSpace.{u, u}}

/-- The sheaf corepresenting relative derivations of `h : X ⟶ S` is the sheafification of the
presheaf of sectionwise Kähler differentials of the structural map of `h`. -/
noncomputable def relativeDifferentialsIsoSectionwise (h : X ⟶ S) :
    moduleOfDifferentials (inverseImageStructureMap h) ≅
      Stacks.Sheaves.RingedSpaceDifferentials.moduleOfDifferentials h :=
  moduleOfDifferentialsIsoSectionwise _

/-- The identification carries the universal derivation of the corepresenting sheaf to the
universal derivation of the sheafified sectionwise differentials. -/
theorem universalDerivation_postcomp_relativeDifferentialsIsoSectionwise (h : X ⟶ S) :
    (universalDerivation (inverseImageStructureMap h)).postcomp
        (relativeDifferentialsIsoSectionwise h).hom.val =
      Stacks.Sheaves.RingedSpaceDifferentials.universalDerivation h :=
  moduleOfDifferentialsIsoSectionwise_compatible _

/-- On a local section, the identification sends the universal differential to the universal
differential. -/
theorem relativeDifferentialsIsoSectionwise_hom_app_d (h : X ⟶ S) (U : Opens X.carrier)
    (a : X.presheaf.obj (.op U)) :
    (((relativeDifferentialsIsoSectionwise h).hom.val.app (.op U)).hom
        ((universalDerivation (inverseImageStructureMap h)).d a)) =
      (Stacks.Sheaves.RingedSpaceDifferentials.universalDerivation h).d a :=
  PresheafOfModulesOfCommRing.Derivation.congr_d
    (universalDerivation_postcomp_relativeDifferentialsIsoSectionwise h) a

/-- On a local section, the inverse of the identification sends the universal differential to
the universal differential. -/
theorem relativeDifferentialsIsoSectionwise_inv_app_d (h : X ⟶ S) (U : Opens X.carrier)
    (a : X.presheaf.obj (.op U)) :
    (((relativeDifferentialsIsoSectionwise h).inv.val.app (.op U)).hom
        ((Stacks.Sheaves.RingedSpaceDifferentials.universalDerivation h).d a)) =
      (universalDerivation (inverseImageStructureMap h)).d a := by
  rw [← relativeDifferentialsIsoSectionwise_hom_app_d h U a]
  exact congrArg (fun m : moduleOfDifferentials (inverseImageStructureMap h) ⟶
      moduleOfDifferentials (inverseImageStructureMap h) =>
        (m.val.app (.op U)).hom ((universalDerivation (inverseImageStructureMap h)).d a))
    (relativeDifferentialsIsoSectionwise h).hom_inv_id

/-- Transposing the conjugate of the sheafified comparison map across `f^* ⊣ f_*` splits into
the identification on the source, the transpose of the sheafified comparison map, and the
pushforward of the identification on the target. -/
private theorem homEquiv_conjugate (f : X' ⟶ X) (h : X ⟶ S) (h' : X' ⟶ S')
    (g : S' ⟶ S) (hcomm : f ≫ h = h' ≫ g) :
    RingedSpaceModuleAdjunction.homEquiv f
        (moduleOfDifferentials (inverseImageStructureMap h'))
        (moduleOfDifferentials (inverseImageStructureMap h))
        ((RingedSpaceModuleAdjunction.modulePullback f).map
            (relativeDifferentialsIsoSectionwise h).hom ≫
          Stacks.Sheaves.RingedSpaceDifferentials.differentialMap f h h' g hcomm ≫
          (relativeDifferentialsIsoSectionwise h').inv) =
      (relativeDifferentialsIsoSectionwise h).hom ≫
        RingedSpaceModuleAdjunction.homEquiv f
            (Stacks.Sheaves.RingedSpaceDifferentials.moduleOfDifferentials h')
            (Stacks.Sheaves.RingedSpaceDifferentials.moduleOfDifferentials h)
            (Stacks.Sheaves.RingedSpaceDifferentials.differentialMap f h h' g hcomm) ≫
        (RingedSpaceModuleAdjunction.modulePushforward f).map
          (relativeDifferentialsIsoSectionwise h').inv := by
  have hright := Adjunction.homEquiv_naturality_right
    (RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction f)
    (Stacks.Sheaves.RingedSpaceDifferentials.differentialMap f h h' g hcomm)
    (relativeDifferentialsIsoSectionwise h').inv
  have hleft := Adjunction.homEquiv_naturality_left
    (RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction f)
    (relativeDifferentialsIsoSectionwise h).hom
    (Stacks.Sheaves.RingedSpaceDifferentials.differentialMap f h h' g hcomm ≫
      (relativeDifferentialsIsoSectionwise h').inv)
  exact hleft.trans
    (congrArg (fun m => (relativeDifferentialsIsoSectionwise h).hom ≫ m) hright)

/-- **The canonical comparison maps of the two descriptions agree.** For a commutative square
of ringed spaces, the comparison map of the corepresentable description is the conjugate, by the
identification, of the comparison map of the sheafified description. -/
theorem differentialMap_eq_sectionwise (f : X' ⟶ X) (h : X ⟶ S) (h' : X' ⟶ S')
    (g : S' ⟶ S) (hcomm : f ≫ h = h' ≫ g) :
    differentialMap f h h' g hcomm =
      (RingedSpaceModuleAdjunction.modulePullback f).map
          (relativeDifferentialsIsoSectionwise h).hom ≫
        Stacks.Sheaves.RingedSpaceDifferentials.differentialMap f h h' g hcomm ≫
        (relativeDifferentialsIsoSectionwise h').inv := by
  refine ((Classical.choose_spec (existsUnique_differentialMap f h h' g hcomm)).2 _ ?_).symm
  intro U a
  rw [homEquiv_conjugate f h h' g hcomm]
  exact
    show ((relativeDifferentialsIsoSectionwise h').inv.val.app
            (.op ((Opens.map f.hom.base).obj U))).hom
          (((RingedSpaceModuleAdjunction.homEquiv f
                (Stacks.Sheaves.RingedSpaceDifferentials.moduleOfDifferentials h')
                (Stacks.Sheaves.RingedSpaceDifferentials.moduleOfDifferentials h)
                (Stacks.Sheaves.RingedSpaceDifferentials.differentialMap
                  f h h' g hcomm)).val.app (.op U)).hom
            (((relativeDifferentialsIsoSectionwise h).hom.val.app (.op U)).hom
              ((universalDerivation (inverseImageStructureMap h)).d a))) =
          (universalDerivation (inverseImageStructureMap h')).d
            ((f.hom.c.app (.op U)).hom a) by
      rw [relativeDifferentialsIsoSectionwise_hom_app_d h U a,
        Stacks.Sheaves.RingedSpaceDifferentials.differentialMap_isDifferentialMap
          f h h' g hcomm U a,
        relativeDifferentialsIsoSectionwise_inv_app_d h' ((Opens.map f.hom.base).obj U)]

end AlgebraicGeometry.SheafOfModules

end
