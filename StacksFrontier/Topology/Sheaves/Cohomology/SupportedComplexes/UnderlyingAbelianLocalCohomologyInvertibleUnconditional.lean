module
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ObjectSections.DerivedSectionsVanishing
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjectiveLocalization
public import StacksFrontier.Topology.Sheaves.Modules.Support
public import StacksFrontier.Topology.Sheaves.Modules.SupportedSectionsSheaf
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.UnderlyingAbelianLocalCohomologyInvertible
import all StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.UnderlyingAbelianLocalCohomologyInvertible

public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import StacksFrontier.AlgebraicGeometry.Cohomology.GlobalSectionsDerived
public import StacksFrontier.AlgebraicGeometry.Cohomology.InjectiveFlasqueModules
public import StacksFrontier.Topology.Sheaves.ClosedImmersion.FlasqueSupportedSections
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.UnderlyingAbelianLocalCohomologyComparison
import StacksCore.Tactic.StacksAttribute

/-!
# Quasi-isomorphisms of complexes of sheaves detected on presheaves

For a Grothendieck topology `J` on a category `C`, a morphism of cochain complexes of sheaves of
abelian groups on `J` is a quasi-isomorphism whenever the induced morphism of the underlying
complexes of presheaves is one.

## Main results

* `Stacks.Cohomology.SupportedComplexes.sheafQuasiIso_of_presheafQuasiIso_general`: a morphism of
  complexes of sheaves which is a quasi-isomorphism of complexes of presheaves is a
  quasi-isomorphism.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace
open AlgebraicGeometry.SheafOfModules (supportedSectionsSheafι supportedSectionsPresheafι)
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.OpenSubspace
open Stacks.Cohomology.Localization (derivedUnit_isIsoOnKInjective
  enoughKInjectives natTrans_isIso_of_kInjectives)
open Stacks.Cohomology.UnderlyingAbelianSheaf
open Stacks.SheafOfModules.SupportedSections

universe u w v₁ u₁

namespace Stacks.Cohomology.SupportedComplexes

attribute [local instance] HasDerivedCategory.standard

/-- A morphism of complexes of sheaves is a quasi-isomorphism as soon as it is one on the
underlying complexes of presheaves. -/
lemma sheafQuasiIso_of_presheafQuasiIso_general
    {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
    {K L : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℤ} (f : K ⟶ L)
    [HasSheafify J AddCommGrpCat.{w}]
    (hf : QuasiIso (((sheafToPresheaf J AddCommGrpCat.{w}).mapHomologicalComplex
      (ComplexShape.up ℤ)).map f)) : QuasiIso f := by
  let F := sheafToPresheaf J AddCommGrpCat.{w}
  let G := presheafToSheaf J AddCommGrpCat.{w}
  let c := ComplexShape.up ℤ
  let _ : G.Additive := Functor.additive_of_preserves_binary_products G
  let e : F.mapHomologicalComplex c ⋙ G.mapHomologicalComplex c ≅
      𝟭 (CochainComplex (Sheaf J AddCommGrpCat.{w}) ℤ) :=
    Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) c ≪≫
      NatIso.mapHomologicalComplex (sheafificationNatIso J AddCommGrpCat.{w}).symm c ≪≫
      Functor.mapHomologicalComplexIdIso _ c
  let sf := (G.mapHomologicalComplex c).map ((F.mapHomologicalComplex c).map f)
  have hsf : QuasiIso sf :=
    HomologicalComplex.quasiIso_map_of_preservesHomology
      ((F.mapHomologicalComplex c).map f) G
  let he : Arrow.mk sf ≅ Arrow.mk f :=
    Arrow.isoMk (e.app K) (e.app L) (by simpa [sf] using (e.hom.naturality f).symm)
  exact quasiIso_of_arrow_mk_iso sf f he

variable {X : TopCat.{u}}

end Stacks.Cohomology.SupportedComplexes

end
