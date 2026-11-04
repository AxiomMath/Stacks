module

public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose

/-!
# Transporting a right derived functor along an equivalence of its source

Let `F : C' ⥤ D` be an additive functor out of an abelian category with injective resolutions.
`CategoryTheory.Functor.rightDerivedCompIso` of
`StacksFrontier/CategoryTheory/Abelian/RightDerivedPostcompose.lean` pulls an exact functor out of
`F.rightDerived n` on the **right**. This file does the same on the **left**: if
`G : C ⥤ C'` is additive, preserves homology and sends injective objects to injective objects —
for instance if it is an equivalence — then

`(G ⋙ F).rightDerived n ≅ G ⋙ F.rightDerived n`.

The module docstring of `StacksFrontier/CategoryTheory/Abelian/LeftDerivedTransport.lean` records
that its own source transport, `CategoryTheory.Functor.compLeftDerivedIso`, "has no right derived
analogue in this library". It has one now: everything below is the mirror of the `Source` section
of that file, with projective resolutions replaced by injective ones and
`CategoryTheory.Functor.mapProjectiveResolution` by `mapInjectiveResolution`, which Mathlib does
not have; it is the library's `CategoryTheory.Functor.mapInjectiveResolution` of
`StacksFrontier/CategoryTheory/Abelian/RightDerivedPostcompose.lean`.

## Main definitions

* `CategoryTheory.Functor.mapInjectiveResolutionIso`: such a functor carries the chosen injective
  resolution of an object to the chosen injective resolution of its image, up to canonical
  homotopy equivalence.
* `CategoryTheory.Functor.rightDerivedToHomotopyCategoryIso`: the same statement read as an
  isomorphism of functors `G.rightDerivedToHomotopyCategory ≅ G ⋙ injectiveResolutions C'`.
* `CategoryTheory.Functor.compRightDerivedIso`:
  `(G ⋙ F).rightDerived n ≅ G ⋙ F.rightDerived n`.
* `CategoryTheory.Equivalence.compRightDerivedIso`: the same for an equivalence of the source,
  whose three hypotheses on `G` are then automatic.

## Implementation notes

`CategoryTheory.InjectiveResolution.desc` descends a morphism `f : X ⟶ Y` to a map of
resolutions `I_X.cocomplex ⟶ I_Y.cocomplex` with its two arguments in the opposite order to the
projective `lift`; apart from that bookkeeping every proof is the dual of its left derived
counterpart. The augmentation of a mapped resolution is `G` applied to the augmentation, after
the comparison `HomologicalComplex.singleMapHomologicalComplex` of the two ways of forming the
complex concentrated in degree zero, and `mapInjectiveResolution_desc_comm` is the naturality of
that comparison.

The image of an injective resolution is the library's
`CategoryTheory.Functor.mapInjectiveResolution` (`RightDerivedPostcompose.lean`), which takes
`G.PreservesHomology` and so discharges the quasi-isomorphism of the mapped augmentation by
instance search; it is used here rather than redefined.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

namespace Functor

variable {C : Type*} [Category* C] [Abelian C] [HasInjectiveResolutions C]
  {D : Type*} [Category* D] [Abelian D]
  {C' : Type*} [Category* C'] [Abelian C'] [HasInjectiveResolutions C']
  (G : C ⥤ C') [G.Additive] [G.PreservesInjectiveObjects] [G.PreservesHomology]

omit [HasInjectiveResolutions C'] in
/-- The image under `G` of the descent of `f : X ⟶ Y` to the chosen injective resolutions is a
descent of `G.map f` to their images. -/
lemma mapInjectiveResolution_desc_comm {X Y : C} (f : X ⟶ Y) :
    (G.mapInjectiveResolution (injectiveResolution X)).ι.f 0 ≫
        ((G.mapHomologicalComplex (ComplexShape.up ℕ)).map
          (InjectiveResolution.desc f (injectiveResolution Y) (injectiveResolution X))).f 0 =
      G.map f ≫ (G.mapInjectiveResolution (injectiveResolution Y)).ι.f 0 := by
  have key : ((HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℕ) 0).inv.app X ≫
        (G.mapHomologicalComplex _).map (injectiveResolution X).ι) ≫
      (G.mapHomologicalComplex (ComplexShape.up ℕ)).map
        (InjectiveResolution.desc f (injectiveResolution Y) (injectiveResolution X)) =
      (CochainComplex.single₀ C').map (G.map f) ≫
        ((HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℕ) 0).inv.app Y ≫
          (G.mapHomologicalComplex _).map (injectiveResolution Y).ι) := by
    rw [Category.assoc, ← Functor.map_comp, InjectiveResolution.desc_commutes,
      Functor.map_comp, ← Category.assoc, ← Category.assoc]
    congr 1
    exact ((HomologicalComplex.singleMapHomologicalComplex G
      (ComplexShape.up ℕ) 0).inv.naturality f).symm
  have h0 := HomologicalComplex.congr_hom key 0
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    CochainComplex.single₀_map_f_zero] at h0
  exact h0

/-- **A functor preserving injectives and homology carries a chosen injective resolution to an
injective resolution.** The image under `G` of the chosen injective resolution of `X` is
isomorphic in the homotopy category to the chosen injective resolution of `G.obj X`.

Two injective resolutions of one object are homotopy equivalent, and the image of an injective
resolution under `G` is an injective resolution of the image (`mapInjectiveResolution`), so this
is `CategoryTheory.InjectiveResolution.iso` for that resolution. -/
def mapInjectiveResolutionIso (X : C) :
    (injectiveResolutions C').obj (G.obj X) ≅
      (G.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
        HomotopyCategory.quotient C' (ComplexShape.up ℕ)).obj
          (injectiveResolution X).cocomplex :=
  (G.mapInjectiveResolution (injectiveResolution X)).iso

/-- The comparison `CategoryTheory.Functor.mapInjectiveResolutionIso` against the functoriality
of the chosen injective resolutions: the image of the descent of `f` to the chosen resolutions is
the map induced by `G.map f`. -/
lemma mapInjectiveResolutionIso_inv_naturality {X Y : C} (f : X ⟶ Y) :
    (mapInjectiveResolutionIso G X).inv ≫ (injectiveResolutions C').map (G.map f) =
      (G.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
          HomotopyCategory.quotient C' (ComplexShape.up ℕ)).map
        (InjectiveResolution.desc f (injectiveResolution Y) (injectiveResolution X)) ≫
      (mapInjectiveResolutionIso G Y).inv :=
  InjectiveResolution.iso_inv_naturality (G.map f)
    (G.mapInjectiveResolution (injectiveResolution X))
    (G.mapInjectiveResolution (injectiveResolution Y)) _
    (mapInjectiveResolution_desc_comm G f)

/-- **A functor preserving injectives and homology carries the chosen injective resolutions to
the chosen injective resolutions, naturally.** For such a `G`, the functor
`G.rightDerivedToHomotopyCategory` — the chosen injective resolution followed by `G` — is the
chosen injective resolution of the image. -/
def rightDerivedToHomotopyCategoryIso :
    G.rightDerivedToHomotopyCategory ≅ G ⋙ injectiveResolutions C' :=
  NatIso.ofComponents
    (fun X => (injectiveResolution X).isoRightDerivedToHomotopyCategoryObj G ≪≫
      (mapInjectiveResolutionIso G X).symm)
    (fun {X Y} f => by
      simp only [Iso.trans_hom, Iso.symm_hom, Functor.comp_map, Category.assoc]
      rw [← Category.assoc,
        InjectiveResolution.isoRightDerivedToHomotopyCategoryObj_hom_naturality f
          (injectiveResolution X) (injectiveResolution Y)
          (InjectiveResolution.desc f (injectiveResolution Y) (injectiveResolution X))
          (InjectiveResolution.desc_commutes_zero f _ _) G,
        Category.assoc, mapInjectiveResolutionIso_inv_naturality])

/-- The comparison `CategoryTheory.Functor.rightDerivedToHomotopyCategoryIso` after
postcomposition with an additive functor `F`: the right derived functor of `G ⋙ F` is computed
from the chosen injective resolutions of the source of `G`, and that of `F` from those of its
target. -/
def compRightDerivedToHomotopyCategoryIso (F : C' ⥤ D) [F.Additive] :
    (G ⋙ F).rightDerivedToHomotopyCategory ≅ G ⋙ F.rightDerivedToHomotopyCategory :=
  Functor.isoWhiskerLeft (injectiveResolutions C)
      (G.mapHomotopyCategoryCompIso (Iso.refl (G ⋙ F)) (ComplexShape.up ℕ)).symm ≪≫
    Functor.isoWhiskerRight (rightDerivedToHomotopyCategoryIso G) (F.mapHomotopyCategory _)

/-- **A functor preserving injectives and homology may be pulled out of a right derived functor
on the left.** If `G : C ⥤ C'` is additive, preserves homology and preserves injective objects —
for instance if it is an equivalence — then `(G ⋙ F).rightDerived n ≅ G ⋙ F.rightDerived n` for
every additive `F : C' ⥤ D`, naturally in the object of `C`. -/
def compRightDerivedIso (F : C' ⥤ D) [F.Additive] (n : ℕ) :
    (G ⋙ F).rightDerived n ≅ G ⋙ F.rightDerived n :=
  Functor.isoWhiskerRight (compRightDerivedToHomotopyCategoryIso G F)
    (HomotopyCategory.homologyFunctor D _ n)

end Functor

namespace Equivalence

variable {C : Type*} [Category* C] [Abelian C] [HasInjectiveResolutions C]
  {D : Type*} [Category* D] [Abelian D]

/-- **The right derived functors of an additive functor are transported along an equivalence of
the source.** An equivalence of abelian categories is exact and preserves injective objects, so
it may be pulled out of a right derived functor on the left. -/
def compRightDerivedIso {C' : Type*} [Category* C'] [Abelian C'] [HasInjectiveResolutions C']
    (e : C ≌ C') [e.functor.Additive] (F : C' ⥤ D) [F.Additive] (n : ℕ) :
    (e.functor ⋙ F).rightDerived n ≅ e.functor ⋙ F.rightDerived n :=
  e.functor.compRightDerivedIso F n

end Equivalence

end CategoryTheory

end
