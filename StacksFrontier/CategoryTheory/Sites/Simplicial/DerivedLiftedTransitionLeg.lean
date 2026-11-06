module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactCompositionQhComparison
public import StacksFrontier.Algebra.Homology.HomotopyCategoryTransition
public import StacksFrontier.CategoryTheory.Localization.LiftedTransition
public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianDerivedPostnikov
public import StacksFrontier.CategoryTheory.Sites.Simplicial.DerivedCompIsoNaturality

/-!
# The canonical leg of a direct-sum formula, carried through the derived category

Let `Fl : A ⥤ T` be exact with exact right adjoint `Rn : T ⥤ A`, let `Rm : T ⥤ B` and
`P : A ⥤ B` be exact, and let `τ : Rn ⋙ P ⟶ Rm` be a transition. The *canonical leg* attached to
this data is the transformation `P ⟶ Fl ⋙ Rm` given by the unit of `Fl ⊣ Rn` carried along `P`,
followed by `τ`; it is the shape of the summand inclusion that Stacks 0D72 (6) asserts for the
componentwise direct-sum formula, both for abelian coefficients and for modules.

This file carries that leg through the unbounded derived categories. Two things have to be
reconciled to do so.

*The two localizations.* `CategoryTheory.derivedNatTrans` and `CategoryTheory.derivedCompIso`
are lifts along the localization `DerivedCategory.Q` of the category of complexes, so they are
computed on the image of `Q`. A derived functor produced as a *total* left derived functor — and
with it `CategoryTheory.liftedTransition`, the shape in which the derived transitions of
Stacks 0D9P are built — is a lift along the localization `DerivedCategory.Qh` of the homotopy
category, so it is computed on the image of `Qh`. The crossing is
`DerivedCategory.quotientCompQhIso`, and the single fact needed about it is
`Stacks.DerivedFunctor.mapDerivedCategoryFactorsh_hom_app_comp_quotientCompQhIso`.

*The two names for the compositor.* `CategoryTheory.derivedCompIso F G (F ⋙ G) (Iso.refl _)` and
`Stacks.DerivedFunctor.mapDerivedCategoryCompIso F G` are the same comparison turned opposite
ways; `…derivedCompIso_refl_inv_eq` identifies them, which is what makes the `Qh`-level formula
`Stacks.DerivedFunctor.mapDerivedCategoryCompIso_hom_app_Qh` available to a consumer written with
`derivedCompIso`.

## Main results

* `CategoryTheory.derivedNatTrans_app_Qh`: the derived functor of a transformation of exact
  functors, read on the image of `Qh` rather than of `Q`.
* `CategoryTheory.derivedCompIso_refl_inv_eq`: the two spellings of the compositor of derived
  functors agree.
* `CategoryTheory.liftedTransition_eq_derivedNatTrans`: **a lifted transition whose comparison is
  invertible is the derived functor of the underlying transformation of complexes**, read through
  the compositor. This is what makes a derived transition built as a total left derived functor
  computable by the `Q`-level machinery.
* `CategoryTheory.derivedNatTrans_leg_comp_derivedCompIso`: **the derived functor of the canonical
  leg is the unit of the derived adjunction followed by the derived transition.** This is the
  content of the derived summand inclusion, in the generality in which it holds.

## Implementation notes

Everything is proved in term mode, by chains of `Eq.trans` and `congrArg` with explicit motives.
Two readings of one object — `(G.mapHomotopyCategory c ⋙ Qh).obj (quotient.obj K)` and
`(quotient ⋙ Qh).obj (G.mapHomologicalComplex c |>.obj K)` — are definitionally equal but not
type-correct simultaneously at the `implicit` transparency level at which a rewrite is checked, so
`rw` reports a pattern it prints as present and `cancel_mono` fails to form the composite it is
given. Both sides of each comparison are therefore composed with the *invertible right factor in
the spelling the bridge lemma already states*, and the cancellation is the last step.

A `local implicit_reducible` on `CategoryTheory.Functor.mapHomotopyCategory` and on
`HomotopyCategory.quotient` is what lets the statements of the bridge lemma be instantiated here
at all: without it the unifier tries to unfold `HomologicalComplexUpToQuasiIso.Qh`, whose body is
not exposed, and reports an application type mismatch between two readings of one object.

## References

* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
* [Stacks Project, Tag 0D9P](https://stacks.math.columbia.edu/tag/0D9P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ v₃ u₁ u₂ u₃ w

namespace CategoryTheory

section Qh

variable {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
  [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]
  (F G : A ⥤ B) [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- **The derived functor of a transformation of exact functors, on the image of the localization
of the homotopy category.** `CategoryTheory.derivedNatTrans` is a lift along the localization of
the category of complexes, so `…derivedNatTrans_app_Q` computes it on the image of `Q`; this is
the same formula on the image of `Qh`, which is where a transition built as a total left derived
functor can be met. -/
theorem derivedNatTrans_app_Qh (α : F ⟶ G) (Y : HomotopyCategory A (ComplexShape.up ℤ)) :
    (derivedNatTrans F G α).app (DerivedCategory.Qh.obj Y) =
      F.mapDerivedCategoryFactorsh.hom.app Y ≫
        DerivedCategory.Qh.map
            ((NatTrans.mapHomotopyCategory α (ComplexShape.up ℤ)).app Y) ≫
          G.mapDerivedCategoryFactorsh.inv.app Y := by
  obtain ⟨Z, rfl⟩ := HomotopyCategory.quotient_obj_surjective Y
  have : IsIso ((DerivedCategory.quotientCompQhIso A).hom.app Z) :=
    (Iso.app (DerivedCategory.quotientCompQhIso A) Z).isIso_hom
  have hF := Stacks.DerivedFunctor.mapDerivedCategoryFactorsh_hom_app_comp_quotientCompQhIso F Z
  have hG := Stacks.DerivedFunctor.mapDerivedCategoryFactorsh_hom_app_comp_quotientCompQhIso G Z
  have hnat := (derivedNatTrans F G α).naturality
    ((DerivedCategory.quotientCompQhIso A).hom.app Z)
  have hQ := derivedNatTrans_app_Q F G α Z
  have hiB := DerivedCategory.quotientCompQhIso_hom_naturality
    ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app Z)
  have : IsIso (G.mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Z)) :=
    (Iso.app G.mapDerivedCategoryFactorsh _).isIso_hom
  have : IsIso ((DerivedCategory.quotientCompQhIso B).hom.app
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj Z)) :=
    (Iso.app (DerivedCategory.quotientCompQhIso B) _).isIso_hom
  -- the left side, composed with the invertible right factor
  have hleft : (derivedNatTrans F G α).app
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Z)) ≫
        G.mapDerivedCategoryFactorsh.hom.app
            ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Z) ≫
          (DerivedCategory.quotientCompQhIso B).hom.app
            ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj Z) =
      F.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso A).hom.app Z) ≫
        F.mapDerivedCategoryFactors.hom.app Z ≫
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app Z) := by
    refine Eq.trans (congrArg (fun t => (derivedNatTrans F G α).app
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Z)) ≫ t)
      hG) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans
      (congrArg (fun t => t ≫ G.mapDerivedCategoryFactors.hom.app Z) hnat.symm) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    exact congrArg (fun t => F.mapDerivedCategory.map
      ((DerivedCategory.quotientCompQhIso A).hom.app Z) ≫ t) hQ
  -- the right side, composed with the same factor
  have hright : (F.mapDerivedCategoryFactorsh.hom.app
            ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Z) ≫
          DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory α (ComplexShape.up ℤ)).app
              ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Z)) ≫
            G.mapDerivedCategoryFactorsh.inv.app
              ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Z)) ≫
        G.mapDerivedCategoryFactorsh.hom.app
            ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Z) ≫
          (DerivedCategory.quotientCompQhIso B).hom.app
            ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj Z) =
      F.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso A).hom.app Z) ≫
        F.mapDerivedCategoryFactors.hom.app Z ≫
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app Z) := by
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
    refine Eq.trans (congrArg (fun t => F.mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Z) ≫ t) hiB) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (congrArg (fun t => t ≫ DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app Z)) hF) ?_
    exact Category.assoc _ _ _
  exact (cancel_mono (G.mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Z) ≫
    (DerivedCategory.quotientCompQhIso B).hom.app
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj Z))).1 (hleft.trans hright.symm)

/-- **The two spellings of the compositor of derived functors agree.**
`CategoryTheory.derivedCompIso` at the identity comparison and
`Stacks.DerivedFunctor.mapDerivedCategoryCompIso` are the same isomorphism turned opposite ways:
both are lifts along `Q` of the same comparison of restrictions, and
`CategoryTheory.Localization.natTrans_ext` identifies them. -/
theorem derivedCompIso_refl_inv_eq {C : Type u₃} [Category.{v₃} C] [Abelian C]
    [HasDerivedCategory C] (F' : A ⥤ B) (G' : B ⥤ C) [F'.Additive] [G'.Additive]
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
    [PreservesFiniteLimits G'] [PreservesFiniteColimits G'] :
    (derivedCompIso F' G' (F' ⋙ G') (Iso.refl _)).inv =
      (Stacks.DerivedFunctor.mapDerivedCategoryCompIso F' G').hom := by
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) fun X => ?_
  rw [derivedCompIso_refl_inv_app_Q,
    Stacks.DerivedFunctor.mapDerivedCategoryCompIso_hom_app_Q]

end Qh

section Bridge

variable {T : Type u₁} {A : Type u₂} {B : Type u₃}
  [Category.{v₁} T] [Category.{v₂} A] [Category.{v₃} B]
  [Abelian T] [Abelian A] [Abelian B]
  [HasDerivedCategory T] [HasDerivedCategory A] [HasDerivedCategory B]
  (Rn : T ⥤ A) (P : A ⥤ B) (Rm : T ⥤ B)
  [Rn.Additive] [PreservesFiniteLimits Rn] [PreservesFiniteColimits Rn]
  [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  [Rm.Additive] [PreservesFiniteLimits Rm] [PreservesFiniteColimits Rm]
  (τ : Rn ⋙ P ⟶ Rm)
  {LP : DerivedCategory A ⥤ DerivedCategory B}
  (cmp : DerivedCategory.Qh ⋙ LP ⟶
    P.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
  (iso : LP ≅ P.mapDerivedCategory)

/-- **A lifted transition with invertible comparison is the derived functor of the underlying
transformation.** Let `Rn`, `Rm` and `P` be exact, let `τ : Rn ⋙ P ⟶ Rm`, and let `LP` be a
functor of derived categories presented as a total left derived functor of `P` by a comparison
`cmp`, together with an identification `iso : LP ≅ P.mapDerivedCategory` carrying `cmp` to the
canonical factorization of the degreewise functor. Then the transition lifted from `τ` along the
localization of the homotopy category is, after `iso`, the compositor of derived functors followed
by the derived functor of `τ`.

This is what makes the derived transitions of Stacks 0D9P — which are `…liftedTransition`s, and so
`Classical.choice` over a lifting problem — computable by the machinery that computes
`CategoryTheory.derivedNatTrans` on the image of `DerivedCategory.Q`. -/
theorem liftedTransition_eq_derivedNatTrans
    (hiso : Functor.whiskerLeft DerivedCategory.Qh iso.hom ≫
      P.mapDerivedCategoryFactorsh.hom = cmp) :
    liftedTransition Rn.mapDerivedCategoryFactorsh cmp Rm.mapDerivedCategoryFactorsh
        (mapHomotopyCategoryTransition (ComplexShape.up ℤ) Rn P Rm τ)
        (HomotopyCategory.quasiIso T (ComplexShape.up ℤ)) =
      Functor.whiskerLeft Rn.mapDerivedCategory iso.hom ≫
        (derivedCompIso Rn P (Rn ⋙ P) (Iso.refl _)).inv ≫
          derivedNatTrans (Rn ⋙ P) Rm τ := by
  refine Localization.natTrans_ext DerivedCategory.Qh
    (HomotopyCategory.quasiIso T (ComplexShape.up ℤ)) fun Y => ?_
  have hcmp : cmp.app ((Rn.mapHomotopyCategory (ComplexShape.up ℤ)).obj Y) =
      iso.hom.app
          (DerivedCategory.Qh.obj ((Rn.mapHomotopyCategory (ComplexShape.up ℤ)).obj Y)) ≫
        P.mapDerivedCategoryFactorsh.hom.app
          ((Rn.mapHomotopyCategory (ComplexShape.up ℤ)).obj Y) :=
    (congr_app hiso.symm ((Rn.mapHomotopyCategory (ComplexShape.up ℤ)).obj Y)).trans
      (NatTrans.comp_app _ _ _)
  have hτ : (mapHomotopyCategoryTransition (ComplexShape.up ℤ) Rn P Rm τ).app Y =
      (NatTrans.mapHomotopyCategory τ (ComplexShape.up ℤ)).app Y := by
    rw [mapHomotopyCategoryTransition, NatTrans.comp_app, mapHomotopyCategoryCompIso_hom_app,
      Iso.refl_hom, NatTrans.mapHomologicalComplex_id, NatTrans.id_app,
      CategoryTheory.Functor.map_id]
    exact Category.id_comp _
  rw [liftedTransition_app_q, hcmp, hτ, NatTrans.comp_app, NatTrans.comp_app,
    Functor.whiskerLeft_app, derivedCompIso_refl_inv_eq,
    Stacks.DerivedFunctor.mapDerivedCategoryCompIso_hom_app_Qh, derivedNatTrans_app_Qh]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun t => t ≫ P.mapDerivedCategoryFactorsh.hom.app
      ((Rn.mapHomotopyCategory (ComplexShape.up ℤ)).obj Y) ≫
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory τ (ComplexShape.up ℤ)).app Y) ≫
      Rm.mapDerivedCategoryFactorsh.inv.app Y)
    (iso.hom.naturality (Rn.mapDerivedCategoryFactorsh.hom.app Y))) ?_
  exact Category.assoc _ _ _

end Bridge

section Leg

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

variable (T : Type u₁) (A : Type u₂) (B : Type u₃)
  [Category.{v₁} T] [Category.{v₂} A] [Category.{v₃} B]
  [Abelian T] [Abelian A] [Abelian B]
  [HasDerivedCategory.{w} T] [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
  (Fl : A ⥤ T) (Rn : T ⥤ A) (Rm : T ⥤ B) (P : A ⥤ B)
  [Fl.Additive] [PreservesFiniteLimits Fl] [PreservesFiniteColimits Fl]
  [Rn.Additive] [PreservesFiniteLimits Rn] [PreservesFiniteColimits Rn]
  [Rm.Additive] [PreservesFiniteLimits Rm] [PreservesFiniteColimits Rm]
  [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  (adj : Fl ⊣ Rn) (τ : Rn ⋙ P ⟶ Rm)

/-- **The derived functor of the canonical leg is the unit followed by the transition.** The
canonical leg attached to an adjunction `Fl ⊣ Rn` of exact functors and a transition
`τ : Rn ⋙ P ⟶ Rm` is `Functor.whiskerRight adj.unit P ≫ Functor.whiskerLeft Fl τ`. Its derived
functor, read through the compositor of `Fl` and `Rm`, is the unit of the derived adjunction
`CategoryTheory.Adjunction.mapDerivedCategory` carried along `P`, followed by the compositor of
`Rn` and `P` and the derived functor of `τ`.

This is the content of the summand-inclusion statement of Stacks 0D72 (6) on derived categories,
isolated from every simplicial-site spelling: both sides are transformations of functors of
derived categories, so they are compared after `CategoryTheory.Localization.natTrans_ext` on the
image of a complex, where the unit of the derived adjunction is given by
`…mapDerivedCategoryAdjunction_unit_app_Q` and both compositors by their `Q`-level formulas. The
comparison `Fl.mapDerivedCategoryFactors.hom` is invertible and is cancelled last; the remaining
content is one naturality square of `P.mapDerivedCategoryFactors.hom`. -/
theorem derivedNatTrans_leg_comp_derivedCompIso (X : DerivedCategory A) :
    (derivedNatTrans P (Fl ⋙ Rm)
            (Functor.whiskerRight adj.unit P ≫ Functor.whiskerLeft Fl τ)).app X ≫
        (derivedCompIso Fl Rm (Fl ⋙ Rm) (Iso.refl _)).hom.app X =
      P.mapDerivedCategory.map ((Adjunction.mapDerivedCategory adj).unit.app X) ≫
        ((derivedCompIso Rn P (Rn ⋙ P) (Iso.refl _)).inv ≫
            derivedNatTrans (Rn ⋙ P) Rm τ).app (Fl.mapDerivedCategory.obj X) := by
  have key : derivedNatTrans P (Fl ⋙ Rm)
          (Functor.whiskerRight adj.unit P ≫ Functor.whiskerLeft Fl τ) ≫
        (derivedCompIso Fl Rm (Fl ⋙ Rm) (Iso.refl _)).hom =
      Functor.whiskerRight (Adjunction.mapDerivedCategory adj).unit P.mapDerivedCategory ≫
        Functor.whiskerLeft Fl.mapDerivedCategory
          ((derivedCompIso Rn P (Rn ⋙ P) (Iso.refl _)).inv ≫
            derivedNatTrans (Rn ⋙ P) Rm τ) := by
    refine Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) fun Z => ?_
    have : IsIso (Fl.mapDerivedCategoryFactors.hom.app Z) :=
      (Iso.app Fl.mapDerivedCategoryFactors Z).isIso_hom
    have hleg : (NatTrans.mapHomologicalComplex
          (Functor.whiskerRight adj.unit P ≫ Functor.whiskerLeft Fl τ)
          (ComplexShape.up ℤ)).app Z =
        (P.mapHomologicalComplex (ComplexShape.up ℤ)).map
            ((NatTrans.mapHomologicalComplex adj.unit (ComplexShape.up ℤ)).app Z) ≫
          (NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app
            ((Fl.mapHomologicalComplex (ComplexShape.up ℤ)).obj Z) :=
      HomologicalComplex.hom_ext _ _ fun _ => rfl
    have hcancelRm : Rm.mapDerivedCategory.map (Fl.mapDerivedCategoryFactors.inv.app Z) ≫
        Rm.mapDerivedCategory.map (Fl.mapDerivedCategoryFactors.hom.app Z) = 𝟙 _ := by
      simp [← Functor.map_comp]
    have hcancelRnP : P.mapDerivedCategory.map
            (Rn.mapDerivedCategory.map (Fl.mapDerivedCategoryFactors.inv.app Z)) ≫
          P.mapDerivedCategory.map
            (Rn.mapDerivedCategory.map (Fl.mapDerivedCategoryFactors.hom.app Z)) = 𝟙 _ := by
      simp [← Functor.map_comp]
    have hcancelRnF : P.mapDerivedCategory.map (Rn.mapDerivedCategoryFactors.inv.app
            ((Fl.mapHomologicalComplex (ComplexShape.up ℤ)).obj Z)) ≫
          P.mapDerivedCategory.map (Rn.mapDerivedCategoryFactors.hom.app
            ((Fl.mapHomologicalComplex (ComplexShape.up ℤ)).obj Z)) = 𝟙 _ := by
      simp [← Functor.map_comp]
    have hdt := ((derivedCompIso Rn P (Rn ⋙ P) (Iso.refl _)).inv ≫
      derivedNatTrans (Rn ⋙ P) Rm τ).naturality (Fl.mapDerivedCategoryFactors.hom.app Z)
    simp only [NatTrans.comp_app, Functor.comp_map, Category.assoc] at hdt
    have hPnat := P.mapDerivedCategoryFactors.hom.naturality
      ((NatTrans.mapHomologicalComplex adj.unit (ComplexShape.up ℤ)).app Z)
    simp only [Functor.comp_map] at hPnat
    refine (cancel_mono (Rm.mapDerivedCategory.map
      (Fl.mapDerivedCategoryFactors.hom.app Z))).1 ?_
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Category.assoc]
    rw [derivedNatTrans_app P (Fl ⋙ Rm) _ Z, derivedCompIso_refl_hom_app_Q,
      mapDerivedCategoryAdjunction_unit_app_Q, hleg]
    simp only [Category.assoc, Functor.map_comp, Iso.inv_hom_id_app_assoc]
    refine Eq.trans ?_ (congrArg (fun t => P.mapDerivedCategory.map (DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex adj.unit (ComplexShape.up ℤ)).app Z)) ≫
        P.mapDerivedCategory.map (Rn.mapDerivedCategoryFactors.inv.app
          ((Fl.mapHomologicalComplex (ComplexShape.up ℤ)).obj Z)) ≫
          P.mapDerivedCategory.map (Rn.mapDerivedCategory.map
            (Fl.mapDerivedCategoryFactors.inv.app Z)) ≫ t) hdt)
    dsimp only [Functor.comp_obj]
    rw [derivedCompIso_refl_inv_app_Q, derivedNatTrans_app]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc, reassoc_of% hcancelRnP,
      reassoc_of% hcancelRnF, hcancelRm]
    dsimp only [Functor.comp_obj]
    simp only [Category.comp_id]
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (congrArg (fun t => t ≫ DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app
          ((Fl.mapHomologicalComplex (ComplexShape.up ℤ)).obj Z)) ≫
      Rm.mapDerivedCategoryFactors.inv.app
        ((Fl.mapHomologicalComplex (ComplexShape.up ℤ)).obj Z)) hPnat.symm) ?_
    exact Category.assoc _ _ _
  have h := congr_app key X
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at h
  exact h

end Leg

end CategoryTheory

end
