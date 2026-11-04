module

public import Mathlib.CategoryTheory.Abelian.LeftDerived
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose

/-!
# Transporting a left derived functor along isomorphisms and equivalences

Let `F : C ⥤ D` be an additive functor out of an abelian category with projective resolutions.
This file records the three ways in which `F.leftDerived n` may be transported.

* Along an isomorphism of the functor: a natural isomorphism `F ≅ G` of additive functors
  induces `F.leftDerived n ≅ G.leftDerived n`.
* Along the target: if `E : D ⥤ D'` is additive and preserves homology — for instance if it is
  exact, and in particular if it is an equivalence — then `(F ⋙ E).leftDerived n` is
  `F.leftDerived n ⋙ E`.
* Along the source: if `G : C ⥤ C'` is additive, preserves homology and sends projective
  objects to projective objects — again, for instance an equivalence — then
  `(G ⋙ F).leftDerived n` is `G ⋙ F.leftDerived n`.

Taken together these transport `CategoryTheory.Functor.leftDerived` along an equivalence of the
source and of the target of an additive functor, which is what is needed to compare the derived
functors of two functors that are the same up to such equivalences.

## Main definitions

* `CategoryTheory.Functor.leftDerivedIsoOfNatIso`: a natural isomorphism of additive functors
  induces one of their left derived functors.
* `CategoryTheory.Functor.leftDerivedCompIso`: `(F ⋙ E).leftDerived n ≅ F.leftDerived n ⋙ E`
  for `E` additive and preserving homology.
* `CategoryTheory.Functor.projectiveResolutionsCompIso`: a functor which is additive, preserves
  homology and preserves projective objects carries the chosen projective resolution of an
  object to the chosen projective resolution of its image, up to canonical homotopy equivalence
  and naturally in the object.
* `CategoryTheory.Functor.compLeftDerivedIso`: `(G ⋙ F).leftDerived n ≅ G ⋙ F.leftDerived n`
  for such a `G`.
* `CategoryTheory.Equivalence.leftDerivedCompIso` and
  `CategoryTheory.Equivalence.compLeftDerivedIso`: the two transport isomorphisms for an
  equivalence of abelian categories.

## Implementation notes

The target transport is the exact mirror of
`CategoryTheory.Functor.rightDerivedCompIso`: the homology comparisons
`CategoryTheory.Functor.mapHomologicalComplexHomologyIso` and
`CategoryTheory.Functor.mapHomotopyCategoryHomologyIso` it is assembled from are stated for an
arbitrary complex shape and are reused verbatim.

The source transport has no right derived analogue in this library. It rests on
`CategoryTheory.Functor.mapProjectiveResolution`, which is the statement that a functor
preserving homology and projective objects carries a projective resolution to a projective
resolution; the chosen resolution of `G.obj X` is then compared to the image of the chosen
resolution of `X` by `CategoryTheory.ProjectiveResolution.iso`, and the naturality square is
`CategoryTheory.ProjectiveResolution.iso_inv_naturality` applied to the image of the lift of
`f` to the chosen resolutions.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

namespace Functor

variable {C : Type*} [Category* C] [Abelian C] [HasProjectiveResolutions C]
  {D : Type*} [Category* D] [Abelian D] {D' : Type*} [Category* D'] [Abelian D']

/-- A natural isomorphism of additive functors induces one of their left derived functors. -/
def leftDerivedIsoOfNatIso {F G : C ⥤ D} [F.Additive] [G.Additive] (e : F ≅ G) (n : ℕ) :
    F.leftDerived n ≅ G.leftDerived n where
  hom := NatTrans.leftDerived e.hom n
  inv := NatTrans.leftDerived e.inv n
  hom_inv_id := by rw [← NatTrans.leftDerived_comp, e.hom_inv_id, NatTrans.leftDerived_id]
  inv_hom_id := by rw [← NatTrans.leftDerived_comp, e.inv_hom_id, NatTrans.leftDerived_id]

/-- **An exact functor may be pulled out of a left derived functor.** If `E` is additive and
preserves homology then `(F ⋙ E).leftDerived n ≅ F.leftDerived n ⋙ E`, naturally in the object
of `C`.

Both left derived functors are the chosen projective resolution followed by a functor on
homotopy categories and then homology; the comparison is
`CategoryTheory.Functor.mapHomotopyCategoryCompIso` followed by
`CategoryTheory.Functor.mapHomotopyCategoryHomologyIso`. -/
def leftDerivedCompIso (F : C ⥤ D) [F.Additive] (E : D ⥤ D') [E.Additive]
    [E.PreservesHomology] (n : ℕ) :
    (F ⋙ E).leftDerived n ≅ F.leftDerived n ⋙ E :=
  Functor.isoWhiskerLeft (projectiveResolutions C)
    (Functor.isoWhiskerRight (F.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ E)) _).symm
        (HomotopyCategory.homologyFunctor D' _ n) ≪≫
      Functor.isoWhiskerLeft (F.mapHomotopyCategory _) (mapHomotopyCategoryHomologyIso E _ n))

section Source

variable {C' : Type*} [Category* C'] [Abelian C'] [HasProjectiveResolutions C']
  (G : C ⥤ C') [G.Additive] [G.PreservesProjectiveObjects] [G.PreservesHomology]

omit [HasProjectiveResolutions C'] in
/-- The image under `G` of the lift of `f : X ⟶ Y` to the chosen projective resolutions is a
lift of `G.map f` to their images. -/
lemma mapProjectiveResolution_lift_comm {X Y : C} (f : X ⟶ Y) :
    ((G.mapHomologicalComplex (ComplexShape.down ℕ)).map
        (ProjectiveResolution.lift f (projectiveResolution X) (projectiveResolution Y))).f 0 ≫
      (G.mapProjectiveResolution (projectiveResolution Y)).π.f 0 =
      (G.mapProjectiveResolution (projectiveResolution X)).π.f 0 ≫ G.map f := by
  have key : (G.mapHomologicalComplex (ComplexShape.down ℕ)).map
        (ProjectiveResolution.lift f (projectiveResolution X) (projectiveResolution Y)) ≫
      ((G.mapHomologicalComplex (ComplexShape.down ℕ)).map (projectiveResolution Y).π ≫
        (HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.down ℕ) 0).hom.app Y) =
      ((G.mapHomologicalComplex (ComplexShape.down ℕ)).map (projectiveResolution X).π ≫
          (HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.down ℕ) 0).hom.app X) ≫
        (ChainComplex.single₀ C').map (G.map f) := by
    rw [← Category.assoc, ← Functor.map_comp, ProjectiveResolution.lift_commutes,
      Functor.map_comp, Category.assoc, Category.assoc]
    congr 1
    exact (HomologicalComplex.singleMapHomologicalComplex G
      (ComplexShape.down ℕ) 0).hom.naturality f
  have h0 := HomologicalComplex.congr_hom key 0
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    ChainComplex.single₀_map_f_zero] at h0
  exact h0

/-- **A functor preserving projectives and homology carries a chosen projective resolution to a
projective resolution.** The image under `G` of the chosen projective resolution of `X` is
isomorphic in the homotopy category to the chosen projective resolution of `G.obj X`.

Two projective resolutions of one object are homotopy equivalent, and the image of a projective
resolution under `G` is a projective resolution of the image
(`CategoryTheory.Functor.mapProjectiveResolution`), so this is
`CategoryTheory.ProjectiveResolution.iso` for that resolution. -/
def mapProjectiveResolutionIso (X : C) :
    (projectiveResolutions C').obj (G.obj X) ≅
      (G.mapHomologicalComplex (ComplexShape.down ℕ) ⋙
        HomotopyCategory.quotient C' (ComplexShape.down ℕ)).obj (projectiveResolution X).complex :=
  (G.mapProjectiveResolution (projectiveResolution X)).iso

/-- The comparison of `CategoryTheory.Functor.mapProjectiveResolutionIso` with the functoriality
of the chosen projective resolutions: the image of the lift of `f` to the chosen resolutions is
the map induced by `G.map f`. -/
lemma mapProjectiveResolutionIso_inv_naturality {X Y : C} (f : X ⟶ Y) :
    (mapProjectiveResolutionIso G X).inv ≫ (projectiveResolutions C').map (G.map f) =
      (G.mapHomologicalComplex (ComplexShape.down ℕ) ⋙
          HomotopyCategory.quotient C' (ComplexShape.down ℕ)).map
        (ProjectiveResolution.lift f (projectiveResolution X) (projectiveResolution Y)) ≫
      (mapProjectiveResolutionIso G Y).inv :=
  ProjectiveResolution.iso_inv_naturality (G.map f)
    (G.mapProjectiveResolution (projectiveResolution X))
    (G.mapProjectiveResolution (projectiveResolution Y)) _
    (mapProjectiveResolution_lift_comm G f)

/-- **A functor preserving projectives and homology carries the chosen projective resolutions to
the chosen projective resolutions, naturally.** For such a `G`, the functor
`G.leftDerivedToHomotopyCategory` — the chosen projective resolution followed by `G` — is the
chosen projective resolution of the image. -/
def leftDerivedToHomotopyCategoryIso :
    G.leftDerivedToHomotopyCategory ≅ G ⋙ projectiveResolutions C' :=
  NatIso.ofComponents
    (fun X => (projectiveResolution X).isoLeftDerivedToHomotopyCategoryObj G ≪≫
      (mapProjectiveResolutionIso G X).symm)
    (fun {X Y} f => by
      simp only [Iso.trans_hom, Iso.symm_hom, Functor.comp_map, Category.assoc]
      rw [← Category.assoc,
        ProjectiveResolution.isoLeftDerivedToHomotopyCategoryObj_hom_naturality f
          (projectiveResolution X) (projectiveResolution Y)
          (ProjectiveResolution.lift f (projectiveResolution X) (projectiveResolution Y))
          (ProjectiveResolution.lift_commutes_zero f _ _) G,
        Category.assoc, mapProjectiveResolutionIso_inv_naturality])

/-- The comparison of `CategoryTheory.Functor.leftDerivedToHomotopyCategoryIso` after
postcomposition with an additive functor `F`: the left derived functor of `G ⋙ F` is computed
from the chosen projective resolutions of the source of `G`, and that of `F` from those of its
target. -/
def compLeftDerivedToHomotopyCategoryIso (F : C' ⥤ D) [F.Additive] :
    (G ⋙ F).leftDerivedToHomotopyCategory ≅ G ⋙ F.leftDerivedToHomotopyCategory :=
  Functor.isoWhiskerLeft (projectiveResolutions C)
      (G.mapHomotopyCategoryCompIso (Iso.refl (G ⋙ F)) (ComplexShape.down ℕ)).symm ≪≫
    Functor.isoWhiskerRight (leftDerivedToHomotopyCategoryIso G) (F.mapHomotopyCategory _)

/-- **A functor preserving projectives and homology may be pulled out of a left derived functor
on the left.** If `G : C ⥤ C'` is additive, preserves homology and preserves projective objects
— for instance if it is an equivalence — then `(G ⋙ F).leftDerived n ≅ G ⋙ F.leftDerived n`
for every additive `F : C' ⥤ D`, naturally in the object of `C`. -/
def compLeftDerivedIso (F : C' ⥤ D) [F.Additive] (n : ℕ) :
    (G ⋙ F).leftDerived n ≅ G ⋙ F.leftDerived n :=
  Functor.isoWhiskerRight (compLeftDerivedToHomotopyCategoryIso G F)
    (HomotopyCategory.homologyFunctor D _ n)

end Source

end Functor

namespace Equivalence

variable {C : Type*} [Category* C] [Abelian C] [HasProjectiveResolutions C]
  {D : Type*} [Category* D] [Abelian D] {D' : Type*} [Category* D'] [Abelian D']

/-- **Having enough projectives is invariant under equivalence.** The image under an equivalence
of a projective presentation of `e.inverse.obj X` is a projective presentation of `X`: an
equivalence preserves projective objects and epimorphisms. -/
lemma enoughProjectives {D₁ : Type*} [Category* D₁] {D₂ : Type*} [Category* D₂] (e : D₁ ≌ D₂)
    [EnoughProjectives D₁] : EnoughProjectives D₂ where
  presentation X :=
    ⟨{ p := e.functor.obj (Projective.over (e.inverse.obj X))
       f := e.functor.map (Projective.π (e.inverse.obj X)) ≫ e.counit.app X }⟩

/-- **The left derived functors of an additive functor are transported along an equivalence of
the target.** An equivalence of abelian categories is exact, so it may be pulled out of a left
derived functor. -/
def leftDerivedCompIso (F : C ⥤ D) [F.Additive] (e : D ≌ D') [e.functor.Additive] (n : ℕ) :
    (F ⋙ e.functor).leftDerived n ≅ F.leftDerived n ⋙ e.functor :=
  F.leftDerivedCompIso e.functor n

/-- **The left derived functors of an additive functor are transported along an equivalence of
the source.** An equivalence of abelian categories is exact and preserves projective objects, so
it may be pulled out of a left derived functor on the left. -/
def compLeftDerivedIso {C' : Type*} [Category* C'] [Abelian C'] [HasProjectiveResolutions C']
    (e : C ≌ C') [e.functor.Additive] (F : C' ⥤ D) [F.Additive] (n : ℕ) :
    (e.functor ⋙ F).leftDerived n ≅ e.functor ⋙ F.leftDerived n :=
  e.functor.compLeftDerivedIso F n

end Equivalence

end CategoryTheory

end
