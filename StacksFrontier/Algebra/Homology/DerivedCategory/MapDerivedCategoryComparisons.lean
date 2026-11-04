module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import Mathlib.CategoryTheory.Triangulated.Subcategory

@[expose] public noncomputable section

/-!
# Comparisons for functors on derived categories and invertibility loci

An exact functor between abelian categories with derived categories acts on them degreewise,
through `CategoryTheory.Functor.mapDerivedCategory`, which is the lift of the induced functor on
cochain complexes through the localization. This file collects the comparisons of that action
with isomorphisms and composition of functors, together with the general facts about the locus
of objects at which a natural transformation is invertible: that locus is closed under
isomorphisms and retracts, and it is a triangulated subcategory when the transformation is a
shift-compatible transformation of triangulated functors. A companion statement records that a
natural transformation lifted through a localization commutes with the shift as soon as the
transformation it lifts does.

Nothing here is specific to a site, a presheaf of rings or a topology: every statement is about
an arbitrary exact functor, an arbitrary natural transformation, or an arbitrary localization.

## Main definitions

* `Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso`: the isomorphism of the
  degreewise actions on derived categories attached to an isomorphism of exact functors.
* `Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso`: the degreewise action of a
  composite of exact functors is the composite of the degreewise actions.

## Main results

* `Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso_hom_app_Q` and
  `Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso_inv_app_Q`: the two values at
  the image of a cochain complex of the isomorphism attached to an isomorphism of exact functors.
* `Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso_inv_app_Q` and
  `Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso_hom_app_Q`: the two values of the
  composition isomorphism at the image of a cochain complex.
* `mapDerivedCategoryFactorsh_hom_app_comp_quotientCompQhIso_hom`: the `Qh`-level factorization of
  an exact functor at the class of a cochain complex, crossed over to the `Q`-level factorization
  at that complex.
* `Stacks.DerivedCategoryComparisons.localization_liftNatTrans_commShift`: a natural
  transformation lifted through a localization commutes with the shift.
* `Stacks.DerivedCategoryComparisons.isIso_app_of_retract`: the invertibility locus of a natural
  transformation is stable under retracts.
* `Stacks.DerivedCategoryComparisons.isIso_app_isClosedUnderIsomorphisms`: that locus is closed
  under isomorphisms.
* `Stacks.DerivedCategoryComparisons.isIso_app_isTriangulated`: that locus is a triangulated
  subcategory, for a shift-compatible transformation of triangulated functors.
* `Stacks.DerivedCategoryComparisons.isIso_app_colimit_of_preserves`: a transformation between
  functors preserving a colimit is invertible at that colimit as soon as it is invertible at
  every object of the diagram.
* `Stacks.DerivedCategoryComparisons.isIso_app_isClosedUnderColimitsOfShape`: that locus is
  closed under the colimits of a shape which both functors preserve.
-/

open CategoryTheory CategoryTheory.Limits
open ZeroObject

universe w₃ w₂ w₁

namespace Stacks.DerivedCategoryComparisons

section Descent

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

variable {C₁ : Type*} [Category C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type*} [Category C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  {C₃ : Type*} [Category C₃] [Abelian C₃] [HasDerivedCategory.{w₃} C₃]

/-- Isomorphic exact functors induce isomorphic functors on derived categories: both descents
are lifts through the localization of the corresponding functors on cochain complexes. -/
def mapDerivedCategoryIsoOfNatIso (F G : C₁ ⥤ C₂)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G) :
    F.mapDerivedCategory ≅ G.mapDerivedCategory :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ))
    (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    F.mapDerivedCategory G.mapDerivedCategory
    (Functor.isoWhiskerRight (NatIso.mapHomologicalComplex e (ComplexShape.up ℤ))
      DerivedCategory.Q)

/-- **The composite of the two descents is a lift of the composite on cochain complexes.** The
comparison chains the two canonical factorizations `Functor.mapDerivedCategoryFactors`. -/
def mapDerivedCategoryCompLiftingIso (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    DerivedCategory.Q ⋙ F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅
      (F ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight F.mapDerivedCategoryFactors G.mapDerivedCategory ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ G.mapDerivedCategoryFactors ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (ComplexShape.up ℤ))
      DerivedCategory.Q

/-- The composite of the two descents lifts the composite on cochain complexes, through
`Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompLiftingIso`. -/
instance liftingMapDerivedCategoryComp (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    Localization.Lifting (DerivedCategory.Q)
      (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ))
      ((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
      (F.mapDerivedCategory ⋙ G.mapDerivedCategory) :=
  ⟨mapDerivedCategoryCompLiftingIso F G⟩

/-- **The lifting comparison of a composite is compatible with the shift.** It is a composite of
associators and of whiskerings of `CategoryTheory.Functor.mapDerivedCategoryFactors`, and each of
those is shift-compatible. -/
instance commShift_mapDerivedCategoryCompLiftingIso_hom (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    NatTrans.CommShift (mapDerivedCategoryCompLiftingIso F G).hom ℤ := by
  have : NatTrans.CommShift
      (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G))
        (ComplexShape.up ℤ)).hom ℤ := by
    refine NatTrans.CommShift.of_core fun n => ⟨?_⟩
    ext K i
    simp [Functor.commShiftIso_comp_hom_app]
  unfold mapDerivedCategoryCompLiftingIso
  dsimp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom]
  infer_instance

omit [HasDerivedCategory C₁] [HasDerivedCategory C₂] [HasDerivedCategory C₃] in
/-- The isomorphism identifying the degreewise action of `F ⋙ G` on cochain complexes with the
composite of the degreewise actions of `F` and `G` has identity components. -/
lemma mapHomologicalComplexCompIso_refl_hom_app (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃)
    [F.Additive] [G.Additive] (P : CochainComplex C₁ ℤ) :
    (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G))
      (ComplexShape.up ℤ)).hom.app P = 𝟙 _ := by
  ext i
  simp

omit [HasDerivedCategory C₁] [HasDerivedCategory C₂] [HasDerivedCategory C₃] in
/-- The inverse of the isomorphism identifying the degreewise action of `F ⋙ G` on cochain
complexes with the composite of the degreewise actions of `F` and `G` has identity components. -/
@[simp]
lemma mapHomologicalComplexCompIso_refl_inv_app (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃)
    [F.Additive] [G.Additive] (P : CochainComplex C₁ ℤ) :
    (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G))
      (ComplexShape.up ℤ)).inv.app P = 𝟙 _ := by
  ext i
  simp

/-- The descent to derived categories of a composite of exact functors is the composite of the
descents. The composite of the two descents is itself a lift through the localization of the
composite on cochain complexes, obtained by chaining the two canonical factorizations. -/
def mapDerivedCategoryCompIso (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    (F ⋙ G).mapDerivedCategory ≅ F.mapDerivedCategory ⋙ G.mapDerivedCategory :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ))
    ((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    ((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (F ⋙ G).mapDerivedCategory (F.mapDerivedCategory ⋙ G.mapDerivedCategory)
    (Iso.refl _)

/-- **The isomorphism `mapDerivedCategoryIsoOfNatIso` evaluated at the image of a cochain
complex.**  It is the canonical factorization for `F`, then `DerivedCategory.Q` of the degreewise
isomorphism, then the canonical factorization for `G` read backwards. -/
lemma mapDerivedCategoryIsoOfNatIso_hom_app_Q (F G : C₁ ⥤ C₂)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G)
    (P : CochainComplex C₁ ℤ) :
    (mapDerivedCategoryIsoOfNatIso F G e).hom.app (DerivedCategory.Q.obj P) =
      F.mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).hom.app P) ≫
          G.mapDerivedCategoryFactors.inv.app P := by
  simp [mapDerivedCategoryIsoOfNatIso]
  all_goals rfl

/-- The composition isomorphism `mapDerivedCategoryCompIso` evaluated at the image of a cochain
complex: it is the canonical factorization of each of the three descents involved. -/
lemma mapDerivedCategoryCompIso_inv_app_Q (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (P : CochainComplex C₁ ℤ) :
    (mapDerivedCategoryCompIso F G).inv.app (DerivedCategory.Q.obj P) =
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
        G.mapDerivedCategoryFactors.hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
        (F ⋙ G).mapDerivedCategoryFactors.inv.app P := by
  simp [mapDerivedCategoryCompIso, Localization.Lifting.iso,
    mapDerivedCategoryCompLiftingIso, mapHomologicalComplexCompIso_refl_hom_app]

/-- **The `Qh`-level factorization of an exact functor, crossed over to `Q`.** At the class of a
cochain complex `K` the `Qh`-level identification `F.mapDerivedCategoryFactorsh`, followed by the
identification of `Qh` on the class of `F K` with `Q` there, is the `Q`-level identification
`F.mapDerivedCategoryFactors` at `K`, precomposed with the same comparison on the source side. -/
@[reassoc]
lemma mapDerivedCategoryFactorsh_hom_app_comp_quotientCompQhIso_hom (F : C₁ ⥤ C₂)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : CochainComplex C₁ ℤ) :
    F.mapDerivedCategoryFactorsh.hom.app
          ((HomotopyCategory.quotient C₁ (ComplexShape.up ℤ)).obj K) ≫
        (DerivedCategory.quotientCompQhIso C₂).hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) =
      F.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso C₁).hom.app K) ≫
        F.mapDerivedCategoryFactors.hom.app K := by
  have hd : DerivedCategory.Qh.map
          ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app K) ≫
        (DerivedCategory.quotientCompQhIso C₂).hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) =
      (DerivedCategory.quotientCompQhIso C₂).hom.app
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
    (congrArg (fun t => t ≫ (DerivedCategory.quotientCompQhIso C₂).hom.app
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
      (DerivedCategory.Qh.map_id _)).trans (Category.id_comp _)
  have hcde : (DerivedCategory.quotientCompQhIso C₂).inv.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map
            ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app K) ≫
          (DerivedCategory.quotientCompQhIso C₂).hom.app
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) =
      𝟙 _ :=
    (congrArg (fun t => (DerivedCategory.quotientCompQhIso C₂).inv.app
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫ t) hd).trans
      (Iso.inv_hom_id_app _ _)
  refine (congrArg (fun t => t ≫ (DerivedCategory.quotientCompQhIso C₂).hom.app
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
    (F.mapDerivedCategoryFactorsh_hom_app K)).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine congrArg (fun t => F.mapDerivedCategory.map
      ((DerivedCategory.quotientCompQhIso C₁).hom.app K) ≫ t) ?_
  refine (Category.assoc _ _ _).trans ?_
  exact (congrArg (fun t => F.mapDerivedCategoryFactors.hom.app K ≫ t)
    ((Category.assoc _ _ _).trans hcde)).trans (Category.comp_id _)

/-- The composition isomorphism `mapDerivedCategoryCompIso` in the other direction, evaluated at
the image of a cochain complex: the inverse of `mapDerivedCategoryCompIso_inv_app_Q`. -/
lemma mapDerivedCategoryCompIso_hom_app_Q (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (P : CochainComplex C₁ ℤ) :
    (mapDerivedCategoryCompIso F G).hom.app (DerivedCategory.Q.obj P) =
      (F ⋙ G).mapDerivedCategoryFactors.hom.app P ≫
        G.mapDerivedCategoryFactors.inv.app
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
          G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app P) := by
  rw [← cancel_mono ((mapDerivedCategoryCompIso F G).inv.app (DerivedCategory.Q.obj P)),
    Iso.hom_inv_id_app, mapDerivedCategoryCompIso_inv_app_Q]
  simp

/-- `mapDerivedCategoryIsoOfNatIso` in the other direction, evaluated at the image of a cochain
complex. -/
lemma mapDerivedCategoryIsoOfNatIso_inv_app_Q (F G : C₁ ⥤ C₂)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G)
    (P : CochainComplex C₁ ℤ) :
    (mapDerivedCategoryIsoOfNatIso F G e).inv.app (DerivedCategory.Q.obj P) =
      G.mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).inv.app P) ≫
          F.mapDerivedCategoryFactors.inv.app P := by
  simp [mapDerivedCategoryIsoOfNatIso, Localization.Lifting.iso]

end Descent

/-! ### Lifting a shift-compatible natural transformation through a localization -/

/-- The shift comparison of a lifted functor, at an object of the form `L.obj X`, in terms of the
shift comparison of the functor it lifts. -/
private lemma commShiftIso_lifting_hom_app
    {A B E : Type*} [Category A] [Category B] [Category E]
    [HasShift A ℤ] [HasShift B ℤ] [HasShift E ℤ]
    (L : A ⥤ B) (W : MorphismProperty A) [L.IsLocalization W]
    (F : A ⥤ E) (F' : B ⥤ E) [Localization.Lifting L W F F']
    [L.CommShift ℤ] [F.CommShift ℤ] [F'.CommShift ℤ]
    [NatTrans.CommShift (Localization.Lifting.iso L W F F').hom ℤ] (n : ℤ) (X : A) :
    (F'.commShiftIso n).hom.app (L.obj X) =
      F'.map ((L.commShiftIso n).inv.app X) ≫
        (Localization.Lifting.iso L W F F').hom.app (X⟦n⟧) ≫
        (F.commShiftIso n).hom.app X ≫
        (shiftFunctor E n).map ((Localization.Lifting.iso L W F F').inv.app X) := by
  have hF := NatTrans.shift_app_comm (Localization.Lifting.iso L W F F').hom n X
  simp only [Functor.commShiftIso_comp_hom_app] at hF
  apply (cancel_mono ((shiftFunctor E n).map
    ((Localization.Lifting.iso L W F F').hom.app X))).1
  calc
    (F'.commShiftIso n).hom.app (L.obj X) ≫
        (shiftFunctor E n).map ((Localization.Lifting.iso L W F F').hom.app X) =
      F'.map ((L.commShiftIso n).inv.app X) ≫
        (F'.map ((L.commShiftIso n).hom.app X) ≫
          (F'.commShiftIso n).hom.app (L.obj X) ≫
          (shiftFunctor E n).map ((Localization.Lifting.iso L W F F').hom.app X)) := by simp
    _ = F'.map ((L.commShiftIso n).inv.app X) ≫
        ((Localization.Lifting.iso L W F F').hom.app (X⟦n⟧) ≫
          (F.commShiftIso n).hom.app X) := by
      simpa [Category.assoc] using congrArg
        (fun f => F'.map ((L.commShiftIso n).inv.app X) ≫ f) hF
    _ = (F'.map ((L.commShiftIso n).inv.app X) ≫
        (Localization.Lifting.iso L W F F').hom.app (X⟦n⟧) ≫
        (F.commShiftIso n).hom.app X ≫
        (shiftFunctor E n).map ((Localization.Lifting.iso L W F F').inv.app X)) ≫
        (shiftFunctor E n).map ((Localization.Lifting.iso L W F F').hom.app X) := by
          simp [Category.assoc]

/-- A natural transformation lifted through a localization commutes with the shift as soon as
the transformation it lifts does and the two lifting isomorphisms do. Both sides are compared
on the image of the localization functor, where the lifting isomorphisms identify them with the
corresponding data for the unlifted transformation. -/
lemma localization_liftNatTrans_commShift
    {A B E : Type*} [Category A] [Category B] [Category E]
    [HasShift A ℤ] [HasShift B ℤ] [HasShift E ℤ]
    (L : A ⥤ B) (W : MorphismProperty A) [L.IsLocalization W]
    (F G : A ⥤ E) (F' G' : B ⥤ E)
    [Localization.Lifting L W F F'] [Localization.Lifting L W G G']
    (τ : F ⟶ G) [L.CommShift ℤ] [F.CommShift ℤ] [G.CommShift ℤ]
    [F'.CommShift ℤ] [G'.CommShift ℤ] [NatTrans.CommShift τ ℤ]
    [NatTrans.CommShift (Localization.Lifting.iso L W F F').hom ℤ]
    [NatTrans.CommShift (Localization.Lifting.iso L W G G').hom ℤ] :
    NatTrans.CommShift (Localization.liftNatTrans L W F G F' G' τ) ℤ := by
  apply NatTrans.CommShift.of_core
  intro n
  constructor
  apply Localization.natTrans_ext L W
  intro X
  let β := Localization.liftNatTrans L W F G F' G' τ
  show (F'.commShiftIso n).hom.app (L.obj X) ≫
      ((β.app (L.obj X))⟦n⟧') =
    β.app ((L.obj X)⟦n⟧) ≫ (G'.commShiftIso n).hom.app (L.obj X)
  rw [commShiftIso_lifting_hom_app L W F F', commShiftIso_lifting_hom_app L W G G']
  have hβ' : β.app ((L.obj X)⟦n⟧) ≫
      G'.map ((L.commShiftIso n).inv.app X) =
    F'.map ((L.commShiftIso n).inv.app X) ≫ β.app (L.obj (X⟦n⟧)) := by
    simp [Functor.comp_obj]
  rw [reassoc_of% hβ']
  simp [β, Localization.liftNatTrans_app, Functor.map_comp, Category.assoc]
  simp only [← Category.assoc]
  simpa [Category.assoc, Functor.commShiftIso_comp_hom_app] using congrArg
    (fun g => F'.map ((L.commShiftIso n).inv.app X) ≫
      (Localization.Lifting.iso L W F F').hom.app (X⟦n⟧) ≫ g ≫
      (shiftFunctor E n).map ((Localization.Lifting.iso L W G G').inv.app X))
    (NatTrans.shift_app_comm τ n X)

/-! ### The invertibility locus of a natural transformation -/

/-- The invertibility locus of a natural transformation is stable under retracts: a retract
diagram at `X` inside `Y` conjugates an inverse of `η.app Y` into an inverse of `η.app X`. -/
lemma isIso_app_of_retract {A B : Type*} [Category A] [Category B]
    {F G : A ⥤ B} (η : F ⟶ G) {X Y : A} (rt : Retract X Y)
    (hY : IsIso (η.app Y)) : IsIso (η.app X) := by
  refine ⟨⟨G.map rt.i ≫ inv (η.app Y) ≫ F.map rt.r, ?_, ?_⟩⟩
  · rw [← η.naturality_assoc, IsIso.hom_inv_id_assoc, ← F.map_comp, rt.retract, F.map_id]
  · rw [Category.assoc, Category.assoc, η.naturality rt.r, IsIso.inv_hom_id_assoc,
      ← G.map_comp, rt.retract, G.map_id]

/-- The invertibility locus of a natural transformation, as a property of objects stable under
retracts. -/
lemma isIso_app_isStableUnderRetracts {A B : Type*} [Category A] [Category B]
    {F G : A ⥤ B} (η : F ⟶ G) :
    ObjectProperty.IsStableUnderRetracts (fun X => IsIso (η.app X)) where
  of_retract rt hY := isIso_app_of_retract η rt hY

/-- The invertibility locus of a natural transformation is closed under isomorphisms. -/
lemma isIso_app_isClosedUnderIsomorphisms
    {A E : Type*} [Category A] [Category E]
    {F G : A ⥤ E} (η : F ⟶ G) :
    ObjectProperty.IsClosedUnderIsomorphisms (fun X => IsIso (η.app X)) where
  of_iso e hX := (NatTrans.isIso_app_iff_of_iso η e).1 hX

/-- The invertibility locus of a shift-compatible natural transformation between triangulated
functors is a triangulated subcategory: it contains the zero object, it is stable under shifts,
and it has the two-out-of-three property on distinguished triangles. -/
lemma isIso_app_isTriangulated
    {A E : Type*} [Category A] [Category E]
    [HasZeroObject A] [HasZeroObject E] [Preadditive A] [Preadditive E]
    [HasShift A ℤ] [HasShift E ℤ]
    [∀ n : ℤ, (shiftFunctor A n).Additive] [∀ n : ℤ, (shiftFunctor E n).Additive]
    [Pretriangulated A] [Pretriangulated E]
    (F G : A ⥤ E) [F.CommShift ℤ] [G.CommShift ℤ]
    [F.IsTriangulated] [G.IsTriangulated]
    (η : F ⟶ G) [NatTrans.CommShift η ℤ] :
    ObjectProperty.IsTriangulated (fun X => IsIso (η.app X)) := by
  refine {
    exists_zero := ?_
    isStableUnderShiftBy := fun n => ⟨?_⟩
    ext₂' := ?_ }
  · exact ⟨0, isZero_zero A, isIso_of_source_target_iso_zero _
      (F.map_isZero (isZero_zero A)).isoZero (G.map_isZero (isZero_zero A)).isoZero⟩
  · intro X (hX : IsIso (η.app X))
    have : IsIso (η.app (X⟦n⟧) ≫ (G.commShiftIso n).hom.app X) := by
      rw [← NatTrans.shift_app_comm η n X]
      infer_instance
    exact IsIso.of_isIso_comp_right _ ((G.commShiftIso n).hom.app X)
  · intro T hT h₁ h₃
    let φ : F.mapTriangle.obj T ⟶ G.mapTriangle.obj T :=
      Pretriangulated.Triangle.homMk _ _ (η.app T.obj₁) (η.app T.obj₂) (η.app T.obj₃)
        (η.naturality T.mor₁) (η.naturality T.mor₂) (by
          dsimp [Functor.mapTriangle]
          rw [Category.assoc, NatTrans.shift_app_comm η (1 : ℤ) T.obj₁,
            η.naturality_assoc])
    exact ⟨T.obj₂, Pretriangulated.isIso₂_of_isIso₁₃ φ (F.map_distinguished T hT)
      (G.map_distinguished T hT) h₁ h₃, ⟨Iso.refl _⟩⟩

/-- A natural transformation between two functors is invertible at the apex of a cocone which
both carry to a colimit cocone, as soon as it is invertible at every object of the diagram: the
two images of the cocone then present the same colimit, up to the isomorphism of diagrams that
the transformation is. -/
lemma isIso_app_of_isColimit
    {J A E : Type*} [Category J] [Category A] [Category E]
    (F G : A ⥤ E) (η : F ⟶ G) {K : J ⥤ A} {c : Cocone K}
    (hF : IsColimit (F.mapCocone c)) (hG : IsColimit (G.mapCocone c))
    (h : ∀ j, IsIso (η.app (K.obj j))) : IsIso (η.app c.pt) := by
  have hα : IsIso (Functor.whiskerLeft K η) :=
    (NatTrans.isIso_iff_isIso_app _).2 h
  have heq : η.app c.pt =
      (IsColimit.coconePointsIsoOfNatIso hF hG (asIso (Functor.whiskerLeft K η))).hom := by
    refine hF.hom_ext fun j => ?_
    rw [IsColimit.comp_coconePointsIsoOfNatIso_hom]
    exact η.naturality (c.ι.app j)
  rw [heq]
  infer_instance

/-- A natural transformation between functors preserving a given colimit is invertible at the
colimit as soon as it is invertible at every object of the diagram. -/
lemma isIso_app_colimit_of_preserves
    {J A E : Type*} [Category J] [Category A] [Category E]
    (F G : A ⥤ E) (η : F ⟶ G) (K : J ⥤ A) [HasColimit K]
    [PreservesColimit K F] [PreservesColimit K G]
    (h : ∀ j, IsIso (η.app (K.obj j))) : IsIso (η.app (colimit K)) :=
  isIso_app_of_isColimit F G η (isColimitOfPreserves F (colimit.isColimit K))
    (isColimitOfPreserves G (colimit.isColimit K)) h

/-- The invertibility locus of a natural transformation between functors which preserve the
colimits of shape `J` is closed under those colimits. -/
lemma isIso_app_isClosedUnderColimitsOfShape
    {J A E : Type*} [Category J] [Category A] [Category E]
    (F G : A ⥤ E) (η : F ⟶ G)
    [PreservesColimitsOfShape J F] [PreservesColimitsOfShape J G] :
    ObjectProperty.IsClosedUnderColimitsOfShape (fun X => IsIso (η.app X)) J := by
  have : ObjectProperty.IsClosedUnderIsomorphisms (fun X => IsIso (η.app X)) :=
    isIso_app_isClosedUnderIsomorphisms η
  refine ObjectProperty.IsClosedUnderColimitsOfShape.mk' ?_
  rintro _ ⟨K, hK⟩
  exact isIso_app_colimit_of_preserves F G η K hK

/-! ### The composition comparison is compatible with the shift -/

section CompCommShift

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

variable {C₁ : Type*} [Category C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type*} [Category C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  {C₃ : Type*} [Category C₃] [Abelian C₃] [HasDerivedCategory.{w₃} C₃]

/-- **The comparison `(F ⋙ G)_* ≅ F_* ⋙ G_*` of degreewise actions on derived categories is
compatible with the shift.** It is a transformation lifted through the localization of a
transformation that is, between two lifts whose lifting comparisons are
(`CategoryTheory.Functor.mapDerivedCategoryFactors` on one side and
`Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompLiftingIso` on the other), so
`Stacks.DerivedCategoryComparisons.localization_liftNatTrans_commShift` applies. -/
instance commShift_mapDerivedCategoryCompIso_hom (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    NatTrans.CommShift (mapDerivedCategoryCompIso F G).hom ℤ :=
  letI : NatTrans.CommShift (Localization.Lifting.iso DerivedCategory.Q
      (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ))
      ((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
      (F ⋙ G).mapDerivedCategory).hom ℤ :=
    inferInstanceAs (NatTrans.CommShift (F ⋙ G).mapDerivedCategoryFactors.hom ℤ)
  letI : NatTrans.CommShift (Localization.Lifting.iso DerivedCategory.Q
      (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ))
      ((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
      (F.mapDerivedCategory ⋙ G.mapDerivedCategory)).hom ℤ :=
    inferInstanceAs (NatTrans.CommShift (mapDerivedCategoryCompLiftingIso F G).hom ℤ)
  localization_liftNatTrans_commShift DerivedCategory.Q
    (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ))
    ((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    ((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (F ⋙ G).mapDerivedCategory (F.mapDerivedCategory ⋙ G.mapDerivedCategory)
    (𝟙 _)

end CompCommShift

end Stacks.DerivedCategoryComparisons
