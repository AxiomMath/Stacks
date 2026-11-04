module

public import StacksFrontier.Topology.Sheaves.Cohomology.FilteredColimits.AbelianHigherDirectImage
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.AbelianLocalCohomologyExcision
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.CompositeRightDerivedFunctors
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose

/-!
# Cohomology of an abelian sheaf over an open subset

Let `U` be an open subset of a topological space `X`. For an abelian sheaf `F` on `X`, the
cohomology of `F` over `U` is the cohomology of the restriction `F|_U` on the space `U`,
`H^p(U, F) ≅ H^p(U, F|_U)`, naturally in `F` ([Stacks, Tag 01E1]): sections over `U` are the
global sections of the restriction, and restriction to an open subset is exact and preserves
injective sheaves.

## Main definitions

* `Stacks.Cohomology.AbelianSheaf.sectionsOverIsoRestrictTop`: `Γ(U, F) ≅ Γ(U, F|_U)`.
* `Stacks.Cohomology.AbelianSheaf.cohomologyOverIsoRestrictTop`: `H^p(U, -) ≅ H^p(U, (-)|_U)`.

## Main results

* `Stacks.Cohomology.AbelianSheaf.cohomologyOver_map_eq_zero_of_restrict`: a morphism of abelian
  sheaves induces zero on `H^p(U, -)` as soon as its restriction to `U` induces zero on
  `H^p(U, -)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.SupportedComplexes (abelianRestrictOpen)

universe u

namespace Stacks.Cohomology.AbelianSheaf

variable {X : TopCat.{u}} (U : Opens X)

/-- **Sections over an open subset are the global sections of the restriction**: `F(U)` and
`F|_U(U) = F(j(U))` are the same group, `j(U)` being `U`. -/
def sectionsOverIsoRestrictTop :
    sectionsOver.{u, u} U ≅
      abelianRestrictOpen U ⋙ sectionsOver.{u, u} (X := (Opens.toTopCat X).obj U) ⊤ :=
  NatIso.ofComponents
    (fun F => F.obj.mapIso (eqToIso (congrArg op (Opens.isOpenEmbedding_obj_top U).symm)))
    (fun φ => (φ.hom.naturality _).symm)

/-- **[Stacks, Tag 01E1] for abelian sheaves**: cohomology over an open subset `U` is the
cohomology of the restriction to `U`, naturally in the abelian sheaf. -/
def cohomologyOverIsoRestrictTop (p : ℕ) :
    cohomologyOver.{u, u} U p ≅
      abelianRestrictOpen U ⋙ cohomologyOver.{u, u} (X := (Opens.toTopCat X).obj U) ⊤ p := by
  let Γ : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
    sectionsOver.{u, u} U
  haveI : Γ.Additive := { map_add := fun {_ _ _ _} => rfl }
  let Γ' : Sheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj U)) AddCommGrpCat.{u} ⥤
      AddCommGrpCat.{u} := sectionsOver.{u, u} (X := (Opens.toTopCat X).obj U) ⊤
  haveI : Γ'.Additive := { map_add := fun {_ _ _ _} => rfl }
  haveI : EnoughInjectives (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) := by
    change EnoughInjectives (X.Sheaf AddCommGrpCat.{u}); infer_instance
  haveI : EnoughInjectives
      (Sheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj U)) AddCommGrpCat.{u}) := by
    change EnoughInjectives (((Opens.toTopCat X).obj U).Sheaf AddCommGrpCat.{u}); infer_instance
  exact Functor.rightDerivedIsoOfNatIso (F := Γ) (G := abelianRestrictOpen U ⋙ Γ')
      (sectionsOverIsoRestrictTop U) p ≪≫
    Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso (abelianRestrictOpen U) Γ' p

/-- **A morphism of abelian sheaves vanishing on the cohomology of the restriction to an open
subset vanishes on cohomology over that subset.** -/
theorem cohomologyOver_map_eq_zero_of_restrict {F G : X.Sheaf AddCommGrpCat.{u}} (φ : F ⟶ G)
    (p : ℕ)
    (h : (cohomologyOver.{u, u} (X := (Opens.toTopCat X).obj U) ⊤ p).map
      ((abelianRestrictOpen U).map φ) = 0) :
    (cohomologyOver.{u, u} U p).map φ = 0 := by
  have hnat := (cohomologyOverIsoRestrictTop U p).hom.naturality φ
  exact (Iso.cancel_iso_hom_right _ _ ((cohomologyOverIsoRestrictTop U p).app G)).1
    (hnat.trans ((congrArg (_ ≫ ·) h).trans (comp_zero.trans zero_comp.symm)))

end Stacks.Cohomology.AbelianSheaf
