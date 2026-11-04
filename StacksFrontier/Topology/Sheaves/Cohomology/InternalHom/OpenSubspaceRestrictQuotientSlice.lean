module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CokernelLocalClosureRecognition
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.QuotientRingSheafOpenSubspaceIdeal
public import StacksFrontier.CategoryTheory.Sites.Modules.OverFunctorExact
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedIsoOpenSubspace
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.OpenSubspaceRestrictQuotient

/-!
# Restricting a quotient of the structure sheaf to an open subspace

For a ringed space `X`, an open `U`, and a quotient of the structure sheaf of `X` by the image of
a morphism `Φ`, the restriction of the quotient to `U` is identified with the quotient of the
structure sheaf of `U` by a morphism `φ` with the same section ideals. This file shows that this
identification is compatible with the quotient maps.

## Main results

* `openSubspaceRestrict_π_comp_quotientIsoOfSlice`: the restriction of the quotient map by `Φ`,
  followed by `openSubspaceRestrictQuotientIsoOfSlice`, is the quotient map by `φ`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite TopologicalSpace
open AlgebraicGeometry RingedSpaceModuleAdjunction

universe u

namespace Stacks.SheafOfModules

open Stacks.Sites

variable {X : RingedSpace.{u, u}} (U : Opens X.carrier)
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology ↥U) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology ↥U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify ((Opens.grothendieckTopology X.carrier).over U) AddCommGrpCat.{u}]
  [((Opens.grothendieckTopology X.carrier).over U).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The identification of the restriction of a quotient of the structure sheaf with a quotient
formed over the open carries the restricted quotient map to the quotient map. -/
theorem openSubspaceRestrict_π_comp_quotientIsoOfSlice (U : Opens X.carrier)
    {F : _root_.SheafOfModules.{u} (structureSheafRing X)}
    (Φ : F ⟶ _root_.SheafOfModules.unit (structureSheafRing X))
    {F' : _root_.SheafOfModules.{u} (openSubspaceRing U)}
    (φ : F' ⟶ _root_.SheafOfModules.unit (openSubspaceRing U))
    (h : ∀ V : (Opens ↥U)ᵒᵖ,
      sectionIdeal (idealOfHom (O := openSubspaceSheaf U) φ) V =
        sectionIdeal (idealOfHom (O := X.sheaf.over U)
            ((_root_.SheafOfModules.overFunctor.{u} (structureSheafRing X) U).map Φ))
          (op ((openSubspaceSiteFunctor U).obj V.unop))) :
    (openSubspaceEquiv U).functor.map
        ((_root_.SheafOfModules.overFunctor.{u} (structureSheafRing X) U).map (cokernel.π Φ)) ≫
      (openSubspaceRestrictQuotientIsoOfSlice U Φ φ h).hom = cokernel.π φ := by
  have h1 := PreservesCokernel.π_iso_hom
    (_root_.SheafOfModules.overFunctor.{u} (structureSheafRing X) U) Φ
  have h2 := PreservesCokernel.π_iso_hom (openSubspaceEquiv U).functor
    ((_root_.SheafOfModules.overFunctor.{u} (structureSheafRing X) U).map Φ)
  have h3 := Stacks.Sites.cokernelπ_comp_cokernelIsoOfSectionIdealEq_hom
    (openSubspaceRestrictHom U Φ) φ (fun V =>
      (sectionIdeal_idealOfHom_openSubspaceRestrictHom U Φ V).trans (h V).symm)
  have key : ∀ {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D] (F : C ⥤ D)
      {A B B' : C} {E G : D} (a : A ⟶ B) (b : B ⟶ B') (x : A ⟶ B') (c : F.obj B' ⟶ E)
      (y : F.obj A ⟶ E) (dd : E ⟶ G) (z : F.obj A ⟶ G),
      a ≫ b = x → F.map x ≫ c = y → y ≫ dd = z → F.map a ≫ (F.map b ≫ c) ≫ dd = z := by
    intro C D _ _ F A B B' E G a b x c y dd z e1 e2 e3
    rw [← e3, ← e2, ← e1, F.map_comp]
    simp only [Category.assoc]
  exact key (openSubspaceEquiv U).functor _ _ _ _ _ _ _ h1 h2 h3

end Stacks.SheafOfModules

end
