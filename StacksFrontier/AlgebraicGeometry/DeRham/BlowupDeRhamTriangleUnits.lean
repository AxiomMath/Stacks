module

public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupDeRhamTriangle
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedUnitComposite
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.DerivedPushforwardComparison

/-!
# Units of derived direct images: composites, equal morphisms and closed embeddings

For a morphism of ringed spaces `g`, write `u_g(K) : g_*K ⟶ Rg_*K` for the unit of the derived
direct image read on a cochain complex `K` of modules. This file records three properties of these
units, for an arbitrary model of each derived category:

* along a composite `g ≫ h`, the composite `u_h(g_*K) ≫ Rh_*(u_g K)` is `u_{g ≫ h}(K)` followed by
  the comparison `R(g ≫ h)_* ≅ Rg_* ∘ Rh_*` of [Stacks, Tag 0D5T], once `h_*g_*K` and
  `(g ≫ h)_*K` are identified;
* the units along two equal morphisms agree, through the identifications the equality induces;
* along a morphism whose underlying map is a closed embedding the unit is invertible on every
  complex, since the direct image is then exact ([Stacks, Tag 08KS]).

## Main results

* `Stacks.DeRham.BlowupTriangle.unit_comp_map_unit`: the unit along a composite.
* `Stacks.DeRham.BlowupTriangle.unit_comp_eqToHom`: the unit along equal morphisms.
* `Stacks.DeRham.BlowupTriangle.isIso_unit_of_isClosedEmbedding`: the unit along a closed
  embedding is invertible.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

universe u

attribute [-instance] CategoryTheory.catToReflQuiver

namespace Stacks.DeRham.BlowupTriangle

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

section Composite

variable {A B C : RingedSpace.{u, u}} [HasDerivedCategory (ModuleSheaves A)]
  [HasDerivedCategory (ModuleSheaves B)] [HasDerivedCategory (ModuleSheaves C)]
  (g : A ⟶ B) (h : B ⟶ C)

/-- The comparison of [Stacks, Tag 0D5T] restricts along the unit of `R(g ≫ h)_*` to the composite
of the units of `Rg_*` and `Rh_*`. -/
lemma unit_app_comp_compIso_hom_app (K : HomotopyCategory (ModuleSheaves A) (ComplexShape.up ℤ)) :
    (derivedPushforwardUnit (g ≫ h)).app K ≫ (compIso g h).hom.app (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
          (RingedSpaceModuleAdjunction.modulePushforwardComp g h) (ComplexShape.up ℤ)).inv.app K) ≫
        (derivedPushforwardUnit h).app
          (((RingedSpaceModuleAdjunction.modulePushforward g).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj K) ≫
        (derivedPushforward h).map ((derivedPushforwardUnit g).app K) := by
  have hfac := Functor.rightDerived_fac_app (derivedPushforward (g ≫ h))
    (derivedPushforwardUnit (g ≫ h)) (HomotopyCategory.quasiIso _ _)
    (derivedPushforward g ⋙ derivedPushforward h)
    (Stacks.Cohomology.DerivedPushforwardComposition.derivedPushforwardCompUnit g h
      (derivedPushforward g) (derivedPushforward h) (derivedPushforwardUnit g)
      (derivedPushforwardUnit h)) K
  rw [Stacks.Cohomology.DerivedPushforwardComposition.derivedPushforwardCompUnit_app] at hfac
  exact hfac

/-- **The unit along a composite**: `u_h(g_*K) ≫ Rh_*(u_g K)` is `u_{g ≫ h}(K)` followed by the
comparison of [Stacks, Tag 0D5T], through the identification `h_*g_*K ≅ (g ≫ h)_*K`. -/
theorem unit_comp_map_unit (K : CochainComplex (ModuleSheaves A) ℤ) :
    unit h (((RingedSpaceModuleAdjunction.modulePushforward g).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K) ≫ (derivedPushforward h).map (unit g K) =
      DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso
          (RingedSpaceModuleAdjunction.modulePushforwardComp g h) (ComplexShape.up ℤ)).hom.app K) ≫
        unit (g ≫ h) K ≫ (compIso g h).hom.app (DerivedCategory.Q.obj K) :=
  StacksDraft.DerivedUnitSquare.unitQ_comp_map_unitQ _ _ _ _ _
    (unit_app_comp_compIso_hom_app g h) K

end Composite

section Transport

variable {A B : RingedSpace.{u, u}} [HasDerivedCategory (ModuleSheaves A)]
  [HasDerivedCategory (ModuleSheaves B)]

/-- **The units along equal morphisms agree**, through the identifications of the direct images
and of the derived direct images that the equality induces. -/
lemma unit_comp_eqToHom {g g' : A ⟶ B} (w : g = g') (K : CochainComplex (ModuleSheaves A) ℤ) :
    unit g K ≫
        eqToHom (congrArg (fun k => (derivedPushforward k).obj (DerivedCategory.Q.obj K)) w) =
      DerivedCategory.Q.map (eqToHom (congrArg (fun k =>
          ((RingedSpaceModuleAdjunction.modulePushforward k).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) w)) ≫ unit g' K := by
  subst w
  simp

/-- **Along a closed embedding the unit is invertible**: the direct image is then exact
([Stacks, Tag 08KS]), so it computes its derived functor on every complex. -/
lemma isIso_unit_of_isClosedEmbedding (g : A ⟶ B) (hg : Topology.IsClosedEmbedding g.hom.base)
    (K : CochainComplex (ModuleSheaves A) ℤ) : IsIso (unit g K) :=
  have := Stacks.ClosedImmersion.preservesFiniteColimits_modulePushforward g hg
  StacksDraft.DerivedUnitSquare.isIso_unitQ_of_preservesFiniteColimits _ _
    (fun I hI => isIso_derivedPushforwardUnit_app_of_isKInjective g I hI)
    (exists_quasiIso_isKInjective A) K

end Transport

end Stacks.DeRham.BlowupTriangle

end
