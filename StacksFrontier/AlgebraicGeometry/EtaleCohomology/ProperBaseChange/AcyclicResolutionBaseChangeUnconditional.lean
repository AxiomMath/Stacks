module
public import StacksFrontier.Algebra.Homology.HomotopyCategory.InducedCommShift
public import StacksFrontier.CategoryTheory.Triangulated.ConnectingMorphismNatTrans
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ResolutionBaseChange
public import StacksFrontier.Algebra.Homology.HomotopyCategory.Adjunction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianPairRestriction
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.AcyclicResolutionBaseChange
import all
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.AcyclicResolutionBaseChange

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeMap
public import StacksFrontier.AlgebraicGeometry.DerivedAcyclic.BoundedBelowComparison
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorSingleRightDerived
public import StacksFrontier.Algebra.Homology.DerivedCategory.InverseLimitHelpers
public import StacksFrontier.AlgebraicGeometry.RightAcyclicProduct.Basic

/-!
# AcyclicResolutionBaseChangeUnconditional

Stronger forms of declarations of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.AcyclicResolutionBaseChange`,
stated as separate declarations beside the ones there: over more general coefficient universes, or
with inputs that are carried there as hypotheses discharged, together with the new results built on
them.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.DerivedFunctor

section RightAcyclic

variable {A : Type*} [Category* A] [Abelian A] [EnoughInjectives A] [HasDerivedCategory A]
  {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory B]

end RightAcyclic

/-- Applying a natural transformation degreewise, the component at an object of the homotopy
category is invertible as soon as every component at a term of the complex is invertible. -/
public theorem isIso_natTrans_mapHomotopyCategory_app {ι : Type*} {V W : Type*}
    [Category* V] [Category* W] [Preadditive V] [Preadditive W] {F G : V ⥤ W} [F.Additive]
    [G.Additive] (α : F ⟶ G) {c : ComplexShape ι} (Z : HomotopyCategory V c)
    (hZ : ∀ n, IsIso (α.app (Z.as.X n))) :
    IsIso ((NatTrans.mapHomotopyCategory α c).app Z) := by
  have : ∀ n, IsIso (((NatTrans.mapHomologicalComplex α c).app Z.as).f n) := hZ
  have : IsIso ((NatTrans.mapHomologicalComplex α c).app Z.as) :=
    HomologicalComplex.Hom.isIso_of_components _
  exact Functor.map_isIso (HomotopyCategory.quotient W c)
    ((NatTrans.mapHomologicalComplex α c).app Z.as)

end Stacks.DerivedFunctor

namespace Stacks.EtaleCohomology

variable {X X' Y Y' : Scheme.{u}}

variable (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y') (h : g' ≫ f = f' ≫ g)

/-- `Stacks.DerivedFunctor.isIso_natTrans_mapHomotopyCategory_app` for a transformation of the
shape of the base change comparison, stated for a variable transformation so that the kernel
only ever instantiates it and never unfolds the base change comparison itself. -/
private theorem isIso_comp_mapHomotopyCategory_app_of_baseChangeShape
    (α : etaleAbelianDirectImage.{u, v} f ⋙ etaleAbelianInverseImage.{u, v} g ⟶
      etaleAbelianInverseImage.{u, v} g' ⋙ etaleAbelianDirectImage.{u, v} f')
    (Z : HomotopyCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
      (ComplexShape.up ℤ))
    (hZ : ∀ n : ℤ, IsIso (α.app (Z.as.X n))) :
    IsIso (((Functor.mapHomotopyCategoryCompIso
      (Iso.refl (etaleAbelianDirectImage.{u, v} f ⋙ etaleAbelianInverseImage.{u, v} g))
      (ComplexShape.up ℤ)).hom ≫
    NatTrans.mapHomotopyCategory α (ComplexShape.up ℤ) ≫
    (Functor.mapHomotopyCategoryCompIso
      (Iso.refl (etaleAbelianInverseImage.{u, v} g' ⋙ etaleAbelianDirectImage.{u, v} f'))
      (ComplexShape.up ℤ)).inv).app Z) := by
  have := Stacks.DerivedFunctor.isIso_natTrans_mapHomotopyCategory_app α Z hZ
  rw [NatTrans.comp_app, NatTrans.comp_app]
  infer_instance

/-- The degreewise base change comparison is invertible in the homotopy category at a complex
all of whose terms the underived comparison is invertible at. -/
public theorem isIso_etaleAbelianHomotopyBaseChange_app_unconditional
    (Z : HomotopyCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
      (ComplexShape.up ℤ))
    (hZ : ∀ n : ℤ, IsIso ((etaleAbelianBaseChange.{u, v} f g g' f' h).app (Z.as.X n))) :
    IsIso ((etaleAbelianHomotopyBaseChange.{u, v} f g g' f' h).app Z) := by
  rw [_root_.Stacks.EtaleCohomology.etaleAbelianHomotopyBaseChange_eq]
  exact isIso_comp_mapHomotopyCategory_app_of_baseChangeShape f g g' f' _ Z hZ

end Stacks.EtaleCohomology

end
