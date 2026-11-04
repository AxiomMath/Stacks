module
public import StacksFrontier.AlgebraicGeometry.Cohomology.UniformVanishing.SheafComparison
import all StacksFrontier.AlgebraicGeometry.Cohomology.UniformVanishing.SheafComparison

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris
public import Mathlib.Topology.Sheaves.MayerVietoris
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.CohomologyPresheafLocallyZero
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparisonDef
public import StacksFrontier.Topology.Sheaves.Cohomology.Locality.CohomologyVanishesLocally

/-!
# SheafComparisonUnconditional

Stronger forms of declarations of
`StacksFrontier.AlgebraicGeometry.Cohomology.UniformVanishing.SheafComparison`, stated as separate
declarations beside the ones there: over more general coefficient universes, or with inputs that
are carried there as hypotheses discharged, together with the new results built on them.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}
  [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

/-- **The comparison `hgroupIsoSheafCohomology` is natural in the module.** A morphism `φ` of
module sheaves acts on the derived-functor side through `Hfunctor` and on the `Ext` side through
the functoriality of the cohomology presheaf in its sheaf, applied to the underlying morphism of
abelian sheaves; the comparison intertwines the two.

Both factors of the comparison are components of natural isomorphisms of functors on
`Mod(𝒪_X)`, so this is their naturality. -/
theorem hgroupIsoSheafCohomology_hom_naturality {F G : X.Modules} (φ : F ⟶ G) (U : X.Opens)
    (n : ℕ) :
    (Hfunctor X.ringCatSheaf U (n + 1)).map φ ≫ (hgroupIsoSheafCohomology G U n).hom =
      (hgroupIsoSheafCohomology F U n).hom ≫
        ((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) (n + 1)).map
          ((SheafOfModules.toSheaf X.ringCatSheaf).map φ)).app (op U) := by
  have key : ∀ {A B C : X.Modules ⥤ AddCommGrpCat.{u}} (α : A ≅ B) (β : B ≅ C),
      A.map φ ≫ (α.app G ≪≫ β.app G).hom = (α.app F ≪≫ β.app F).hom ≫ C.map φ := by
    intro A B C α β
    simp only [Iso.trans_hom, Iso.app_hom, Category.assoc, NatTrans.naturality,
      NatTrans.naturality_assoc]
  exact key _ _

end AlgebraicGeometry

namespace Stacks.Cohomology.UniformVanishing

variable {T : Type u} [TopologicalSpace T]
  [HasSheafify (Opens.grothendieckTopology T) AddCommGrpCat.{u}]

section Bot

variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u})]

section MayerVietoris

end MayerVietoris

end Bot

end Stacks.Cohomology.UniformVanishing
