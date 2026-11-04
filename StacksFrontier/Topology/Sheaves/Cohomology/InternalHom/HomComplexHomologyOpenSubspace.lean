module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.HomComplexHomologySliceRestriction
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedIsoOpenSubspace
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.HomComplexAlgebraOpenSubspace

/-!
# Cohomology sheaves of an internal Hom complex, read on an open subspace

For complexes `L`, `M` of `O_X`-modules on a ringed space and an open `U ⊆ X`, the restriction
to `U` of the cohomology sheaf `Hⁿ(𝓗om^•(L, M))`, read on the ringed space `X|_U`, is the
cohomology sheaf `Hⁿ(𝓗om^•(L|_U, M|_U))` formed there, naturally in `L` and `M`.

## Main definitions

* `Stacks.SheafOfModules.sheafHomHomologyOpenSubspaceIso`: the comparison.

## Main results

* `Stacks.SheafOfModules.sheafHomHomologyOpenSubspaceIso_natural`: it is natural in both
  variables.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry

universe u

namespace Stacks.SheafOfModules

variable {X : RingedSpace.{u, u}} (U : Opens X.carrier)
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify ((Opens.grothendieckTopology X.carrier).over U) AddCommGrpCat.{u}]
  [((Opens.grothendieckTopology X.carrier).over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology ↥U) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology ↥U).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The transport of complexes off the slice site onto the open subspace commutes with
cohomology. -/
def openSubspacePushHomologyIso (n : ℤ) :
    openSubspacePushComplex U ⋙
        HomologicalComplex.homologyFunctor
          (_root_.SheafOfModules.{u} (structureSheafRing (openSubspace U))) (ComplexShape.up ℤ) n ≅
      HomologicalComplex.homologyFunctor
          (_root_.SheafOfModules.{u} ((structureSheafRing X).over U)) (ComplexShape.up ℤ) n ⋙
        (openSubspaceEquiv U).functor :=
  Functor.isoWhiskerRight (eqToIso (openSubspacePushComplex_eq U)) _ ≪≫
    Stacks.Homology.exactHomologyIso (openSubspaceEquiv U).functor n

/-- The cohomology sheaves of an internal Hom complex, restricted to an open and read on the
open subspace, are those of the internal Hom complex of the restrictions. -/
def sheafHomHomologyOpenSubspaceIso
    (L M : CochainComplex (_root_.SheafOfModules.{u} (structureSheafRing X)) ℤ) (n : ℤ) :
    (openSubspaceEquiv U).functor.obj
        ((_root_.SheafOfModules.overFunctor.{u} (structureSheafRing X) U).obj
          ((RingedSite.sheafHomComplex (ringedSite X.sheaf) L M).obj.homology n)) ≅
      (RingedSite.sheafHomComplex (ringedSite (openSubspace U).sheaf)
        (openSubspaceRestrictComplex U L) (openSubspaceRestrictComplex U M)).obj.homology n :=
  (openSubspaceEquiv U).functor.mapIso
      (RingedSite.sheafHomHomologyOverIso (ringedSite X.sheaf) U L M n) ≪≫
    ((openSubspacePushHomologyIso U n).app _).symm ≪≫
    (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) n).mapIso
      (sheafHomComplexOpenSubspaceIso U _ _)

/-- The comparison, written out as a composite. -/
theorem sheafHomHomologyOpenSubspaceIso_hom
    (L M : CochainComplex (_root_.SheafOfModules.{u} (structureSheafRing X)) ℤ) (n : ℤ) :
    (sheafHomHomologyOpenSubspaceIso U L M n).hom =
      (openSubspaceEquiv U).functor.map
          (RingedSite.sheafHomHomologyOverIso (ringedSite X.sheaf) U L M n).hom ≫
        (openSubspacePushHomologyIso U n).inv.app _ ≫
        HomologicalComplex.homologyMap (sheafHomComplexOpenSubspaceIso U _ _).hom n :=
  rfl

/-- Pasting three commuting squares, the first one under a functor. -/
theorem paste_three_squares_functor {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A A' B B' : C} {E E' G G' : D}
    (x : A ⟶ A') (a : A ⟶ B) (a' : A' ⟶ B') (y : B ⟶ B')
    (e : F.obj B ⟶ E) (e' : F.obj B' ⟶ E') (z : E ⟶ E')
    (c : E ⟶ G) (c' : E' ⟶ G') (w : G ⟶ G')
    (h1 : x ≫ a' = a ≫ y) (h2 : F.map y ≫ e' = e ≫ z) (h3 : z ≫ c' = c ≫ w) :
    F.map x ≫ F.map a' ≫ e' ≫ c' = (F.map a ≫ e ≫ c) ≫ w := by
  rw [← F.map_comp_assoc, h1, F.map_comp_assoc, reassoc_of% h2, h3]
  simp only [Category.assoc]

/-- The comparison `sheafHomHomologyOpenSubspaceIso` is natural in both variables. -/
theorem sheafHomHomologyOpenSubspaceIso_natural
    {L L' M M' : CochainComplex (_root_.SheafOfModules.{u} (structureSheafRing X)) ℤ}
    (f : L' ⟶ L) (g : M ⟶ M') (n : ℤ) :
    (openSubspaceEquiv U).functor.map
        ((_root_.SheafOfModules.overFunctor.{u} (structureSheafRing X) U).map
          (HomologicalComplex.homologyMap (RingedSite.homMap (ringedSite X.sheaf) f g) n)) ≫
        (sheafHomHomologyOpenSubspaceIso U L' M' n).hom =
      (sheafHomHomologyOpenSubspaceIso U L M n).hom ≫
        HomologicalComplex.homologyMap
          (RingedSite.homMap (ringedSite (openSubspace U).sheaf)
            (openSubspaceRestrictComplexMap U f) (openSubspaceRestrictComplexMap U g)) n := by
  have h₁ := RingedSite.sheafHomHomologyOverIso_natural (ringedSite X.sheaf) U f g n
  let T := (_root_.SheafOfModules.overFunctor.{u} (structureSheafRing X) U).mapHomologicalComplex
    (ComplexShape.up ℤ)
  have h₂ := (openSubspacePushHomologyIso U n).inv.naturality
    (RingedSite.homMap ((ringedSite X.sheaf).over U) (T.map f) (T.map g))
  have h₃ := congrArg (fun ψ => HomologicalComplex.homologyMap ψ n)
    (sheafHomComplexOpenSubspaceIso_natural U (T.map f) (T.map g))
  simp only [HomologicalComplex.homologyMap_comp] at h₃
  rw [sheafHomHomologyOpenSubspaceIso_hom, sheafHomHomologyOpenSubspaceIso_hom]
  exact paste_three_squares_functor (openSubspaceEquiv U).functor _ _ _ _ _ _ _ _ _ _ h₁ h₂ h₃

end Stacks.SheafOfModules
