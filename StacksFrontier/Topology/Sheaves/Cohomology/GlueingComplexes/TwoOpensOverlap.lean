module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.Geometry.RingedSpace.OpenImmersion
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Sheaves.Cohomology.CechAndResolutions.KInjectiveRestriction
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Triangulated
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.AdjunctionAlongAComposite
public import StacksFrontier.Topology.Sheaves.Cohomology.GlueingComplexes.TwoOpens
import all StacksFrontier.Topology.Sheaves.Cohomology.GlueingComplexes.TwoOpens
public import StacksFrontier.Topology.Sheaves.Cohomology.RelativeMayerVietoris.OpenImmersionPullback
public import StacksFrontier.Topology.Sheaves.Cohomology.RelativeMayerVietoris.UnboundedDerivedPushforward

/-!
# Compatibility on the overlap of two opens

Let `jU : U ⟶ X` and `jV : V ⟶ X` be open immersions of ringed spaces, and `iU : W ⟶ U`,
`iV : W ⟶ V` maps with `iU ≫ jU = iV ≫ jV`. For a complex `F` on `X` with maps
`u : F ⟶ Rj_U,* A` and `v : F ⟶ Rj_V,* B`, and an isomorphism `c` between the restrictions of
`A` and `B` to `W`, the compatibility of `u` and `v` on `W` expressed through `overlapIso` implies
the same condition expressed through the canonical comparison isomorphisms
`derivedPullbackCompIsoCanonical` of the iterated restrictions.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open RingedSpaceModuleAdjunction

namespace Stacks.Cohomology.GlueingComplexes

universe u

attribute [local instance] HasDerivedCategory.standard

/-- The compatibility condition on the intersection, read through the two comparison isomorphisms
of the iterated restrictions. -/
lemma overlap_mid_of_eq {X U V W : RingedSpace.{u, u}} (jU : U ⟶ X) (jV : V ⟶ X)
    (iU : W ⟶ U) (iV : W ⟶ V) [SheafedSpace.IsOpenImmersion jU]
    [SheafedSpace.IsOpenImmersion jV] (h : iU ≫ jU = iV ≫ jV) {A : DerivedModules U}
    {B : DerivedModules V} (c : (derivedRestrict iU).obj A ≅ (derivedRestrict iV).obj B)
    (F : DerivedModules X) (u : F ⟶ (derivedPush jU).obj A) (v : F ⟶ (derivedPush jV).obj B)
    (hoverlap : ((derivedRestrict iU).map ((derivedRestrict jU).map u ≫
          (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction
            jU).counit.app A) ≫ c.hom =
      (overlapIso jU jV iU iV h).hom.app F ≫
        (derivedRestrict iV).map ((derivedRestrict jV).map v ≫
          (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction
            jV).counit.app B))) :
    ((restrictEqIso h).inv.app F ≫
        (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical iU jU).inv.app F ≫
          ((derivedRestrict iU).map ((derivedRestrict jU).map u) ≫
            (derivedRestrict iU).map
              ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction
                jU).counit.app A)) ≫ c.hom =
      (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical iV jV).inv.app F ≫
        ((derivedRestrict iV).map ((derivedRestrict jV).map v) ≫
          (derivedRestrict iV).map
            ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction
              jV).counit.app B))) := by
  have hpre : (overlapIso jU jV iU iV h).inv.app F ≫
      ((derivedRestrict iU).map ((derivedRestrict jU).map u ≫
          (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction
            jU).counit.app A) ≫ c.hom) =
      (derivedRestrict iV).map ((derivedRestrict jV).map v ≫
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction
          jV).counit.app B) := by
    rw [hoverlap, Iso.inv_hom_id_app_assoc]
  rw [congrArg (fun α => α.app F) (overlapIso_inv jU jV iU iV h)] at hpre
  simp only [NatTrans.comp_app] at hpre
  have hh := congrArg (fun q =>
    (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical iV jV).inv.app F ≫ q)
    hpre
  simp only [Functor.map_comp] at hh
  simpa only [Category.assoc,
    (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical iV
      jV).inv_hom_id_app_assoc] using hh

section Conservativity

open TopologicalSpace Stacks.Cohomology.RelativeMayerVietoris

end Conservativity

end Stacks.Cohomology.GlueingComplexes

end
