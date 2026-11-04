module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackModulesCompAssoc
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.CompositionOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.BaseChangeCompositionOnRingedTopoi

/-!
# Associativity lemmas for the composition comparison of derived pullbacks

Let `f : (Sh(C), 𝒪_C) ⟶ (Sh(D), 𝒪_D)`, `g : (Sh(D), 𝒪_D) ⟶ (Sh(E), 𝒪_E)` and
`h : (Sh(E), 𝒪_E) ⟶ (Sh(F), 𝒪_F)` be morphisms of ringed topoi in the sense of Stacks 01D3,
part (2). The composition formula of Stacks 0D6D compares `Lg^* ⋙ Lf^*` with `L(g ∘ f)^*`. This
file proves the cocycle identity for the underived compositor of Stacks 03D6 on the unbounded
homotopy categories, with both bracketings `h ∘ (g ∘ f)` and `(h ∘ g) ∘ f` identified with a
third morphism `t`, together with the componentwise form of the universal-property argument for
left derived functors and the characterization of the Stacks 0D6D comparison transported along an
identification of `g ∘ f` with a third morphism.

## Main definitions

* `derivedPullbackComparison'`: the canonical comparison of Stacks 06YY with its target written
  as a composite `f^* ⋙ Qh`.

## Main results

* `pullbackMapHomotopyCompIso_assoc_of_eq`: the cocycle identity for the underived compositor of
  Stacks 03D6 on the unbounded homotopy categories.
* `leftDerived_comparison_assoc_app`: the cocycle identity for comparisons of left derived
  functors, read at an object, with the two transports carried by separate transformations.
* `derivedPullbackCompComparison_app_comp_derivedPullbackComparison_app_of_eq`: the
  characterization of the Stacks 0D6D comparison transported along an identification of the
  composite with a third morphism.

## References

* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.DerivedBaseChangeComposition
  (mapHomotopyCategoryCompIso_assoc leftDerived_comparison_assoc)

namespace Stacks.Cohomology.DerivedPullbackCompositionOfToposHom

universe v u w v' u' w' v'' u'' w'' v₃ u₃ w₃

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance]
  Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy

noncomputable section

/-! ### Comparisons of abstract left derived functors -/

/-- `Stacks.Cohomology.DerivedBaseChangeComposition.leftDerived_comparison_assoc` read at an
object, with the two transports that identify the codomains of the two routes supplied as
separate transformations `τ` and `σ` out of separate functors `L₀₃'` and `L₀₃''`. -/
theorem leftDerived_comparison_assoc_app
    {C₀ C₁ C₂ C₃ D₀ D₁ D₂ D₃ : Type*}
    [Category* C₀] [Category* C₁] [Category* C₂] [Category* C₃]
    [Category* D₀] [Category* D₁] [Category* D₂] [Category* D₃]
    {Q₀ : C₀ ⥤ D₀} {Q₁ : C₁ ⥤ D₁} {Q₂ : C₂ ⥤ D₂} {Q₃ : C₃ ⥤ D₃}
    {F₀₁ : C₀ ⥤ C₁} {F₁₂ : C₁ ⥤ C₂} {F₂₃ : C₂ ⥤ C₃}
    {F₀₂ : C₀ ⥤ C₂} {F₁₃ : C₁ ⥤ C₃} {F₀₃ : C₀ ⥤ C₃}
    {L₀₁ : D₀ ⥤ D₁} {L₁₂ : D₁ ⥤ D₂} {L₂₃ : D₂ ⥤ D₃}
    {L₀₂ : D₀ ⥤ D₂} {L₁₃ : D₁ ⥤ D₃} {L₀₃ L₀₃' L₀₃'' : D₀ ⥤ D₃}
    (α₀₁ : Q₀ ⋙ L₀₁ ⟶ F₀₁ ⋙ Q₁) (α₁₂ : Q₁ ⋙ L₁₂ ⟶ F₁₂ ⋙ Q₂)
    (α₂₃ : Q₂ ⋙ L₂₃ ⟶ F₂₃ ⋙ Q₃) (α₀₂ : Q₀ ⋙ L₀₂ ⟶ F₀₂ ⋙ Q₂)
    (α₁₃ : Q₁ ⋙ L₁₃ ⟶ F₁₃ ⋙ Q₃) (α₀₃ : Q₀ ⋙ L₀₃ ⟶ F₀₃ ⋙ Q₃)
    (W : MorphismProperty C₀) [Q₀.IsLocalization W] [L₀₃.IsLeftDerivedFunctor α₀₃ W]
    (c₀₁₂ : F₀₁ ⋙ F₁₂ ⟶ F₀₂) (c₁₂₃ : F₁₂ ⋙ F₂₃ ⟶ F₁₃)
    (c₀₁₃ : F₀₁ ⋙ F₁₃ ⟶ F₀₃) (c₀₂₃ : F₀₂ ⋙ F₂₃ ⟶ F₀₃)
    (d₀₁₂ : L₀₁ ⋙ L₁₂ ⟶ L₀₂) (d₁₂₃ : L₁₂ ⋙ L₂₃ ⟶ L₁₃)
    (d₀₁₃ : L₀₁ ⋙ L₁₃ ⟶ L₀₃') (τ : L₀₃' ⟶ L₀₃)
    (d₀₂₃ : L₀₂ ⋙ L₂₃ ⟶ L₀₃'') (σ : L₀₃'' ⟶ L₀₃)
    (fac₀₁₂ : ∀ P, d₀₁₂.app (Q₀.obj P) ≫ α₀₂.app P =
      L₁₂.map (α₀₁.app P) ≫ α₁₂.app (F₀₁.obj P) ≫ Q₂.map (c₀₁₂.app P))
    (fac₁₂₃ : ∀ P, d₁₂₃.app (Q₁.obj P) ≫ α₁₃.app P =
      L₂₃.map (α₁₂.app P) ≫ α₂₃.app (F₁₂.obj P) ≫ Q₃.map (c₁₂₃.app P))
    (fac₀₁₃ : ∀ P, d₀₁₃.app (Q₀.obj P) ≫ τ.app (Q₀.obj P) ≫ α₀₃.app P =
      L₁₃.map (α₀₁.app P) ≫ α₁₃.app (F₀₁.obj P) ≫ Q₃.map (c₀₁₃.app P))
    (fac₀₂₃ : ∀ P, d₀₂₃.app (Q₀.obj P) ≫ σ.app (Q₀.obj P) ≫ α₀₃.app P =
      L₂₃.map (α₀₂.app P) ≫ α₂₃.app (F₀₂.obj P) ≫ Q₃.map (c₀₂₃.app P))
    (hc : Functor.whiskerLeft F₀₁ c₁₂₃ ≫ c₀₁₃ =
      (Functor.associator _ _ _).inv ≫ Functor.whiskerRight c₀₁₂ F₂₃ ≫ c₀₂₃)
    (M : D₀) :
    d₁₂₃.app (L₀₁.obj M) ≫ d₀₁₃.app M ≫ τ.app M =
      L₂₃.map (d₀₁₂.app M) ≫ d₀₂₃.app M ≫ σ.app M := by
  have hn := leftDerived_comparison_assoc α₀₁ α₁₂ α₂₃ α₀₂ α₁₃ α₀₃ W
    c₀₁₂ c₁₂₃ c₀₁₃ c₀₂₃ d₀₁₂ d₁₂₃ (d₀₁₃ ≫ τ) (d₀₂₃ ≫ σ) fac₀₁₂ fac₁₂₃
    (fun P => by simpa only [NatTrans.comp_app, Category.assoc] using fac₀₁₃ P)
    (fun P => by simpa only [NatTrans.comp_app, Category.assoc] using fac₀₂₃ P)
    hc
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Category.id_comp, Category.assoc] using
    NatTrans.congr_app hn M

section Fac

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  {Z : RingedTopos.{v'', u'', w''}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [Z.J.HasSheafCompose (forget RingCat.{w''})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w''})]
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [HasSheafify Z.J AddCommGrpCat.{w''}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{w''}]
  [HasSheafify X.J (Type w)] [HasSheafify Y.J (Type w')] [HasSheafify Z.J (Type w'')]

/-- The canonical comparison of Stacks 06YY with its target written out as the composite
`f^* ⋙ Qh` instead of through the abbreviation
`Stacks.Cohomology.DerivedPullbackOfToposHom.pullbackOnHomotopy`. -/
noncomputable abbrev derivedPullbackComparison' (t : RingedToposHom X Z) :
    DerivedCategory.Qh ⋙ derivedPullback t ⟶
      t.toModulesHom.pullbackModules.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh :=
  derivedPullbackComparison t

/-- `derivedPullbackCompComparison_app_comp_derivedPullbackComparison_app` with the underived
compositor written out as `CategoryTheory.Functor.mapHomotopyCategoryCompIso` of the Stacks 03D6
comparison. -/
theorem derivedPullbackCompComparison_app_comp_derivedPullbackComparison_app'
    (f : RingedToposHom X Y) (g : RingedToposHom Y Z)
    (K : HomotopyCategory (SheafOfModules.{w''}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Z.J)) Z.O)) (ComplexShape.up ℤ)) :
    (derivedPullbackCompComparison f g).app (DerivedCategory.Qh.obj K) ≫
        (derivedPullbackComparison' (g.comp f)).app K =
      (derivedPullback f).map ((derivedPullbackComparison' g).app K) ≫
        (derivedPullbackComparison' f).app ((DerivedPushforward.pullbackMapHomotopy g).obj K) ≫
        DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
          (RingedToposHom.pullbackModulesCompIso f g).symm (ComplexShape.up ℤ)).hom.app K) := by
  have h0 := derivedPullbackCompComparison_app_comp_derivedPullbackComparison_app f g K
  simp only [pullbackMapHomotopyCompIso] at h0
  exact h0

/-- The characterization of the Stacks 0D6D comparison, transported along an identification of
the composite `g ∘ f` with a third morphism `t`. -/
theorem derivedPullbackCompComparison_app_comp_derivedPullbackComparison_app_of_eq
    (f : RingedToposHom X Y) (g : RingedToposHom Y Z) (t : RingedToposHom X Z)
    (e : g.comp f = t)
    (K : HomotopyCategory (SheafOfModules.{w''}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Z.J)) Z.O)) (ComplexShape.up ℤ)) :
    (derivedPullbackCompComparison f g).app (DerivedCategory.Qh.obj K) ≫
        (eqToHom (congrArg (fun m : RingedToposHom X Z => derivedPullback m) e)).app
          (DerivedCategory.Qh.obj K) ≫
        (derivedPullbackComparison' t).app K =
      (derivedPullback f).map ((derivedPullbackComparison' g).app K) ≫
        (derivedPullbackComparison' f).app ((DerivedPushforward.pullbackMapHomotopy g).obj K) ≫
        DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
          ((RingedToposHom.pullbackModulesCompIso f g).symm ≪≫
            eqToIso (congrArg
              (fun m : RingedToposHom X Z => m.toModulesHom.pullbackModules) e))
          (ComplexShape.up ℤ)).hom.app K) := by
  subst t
  simpa only [eqToIso_refl, Iso.trans_refl, eqToHom_refl, NatTrans.id_app, Category.id_comp,
    Category.comp_id] using
    derivedPullbackCompComparison_app_comp_derivedPullbackComparison_app' f g K

end Fac

section Cocycle

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  {Z : RingedTopos.{v'', u'', w''}} {W : RingedTopos.{v₃, u₃, w₃}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [Z.J.HasSheafCompose (forget RingCat.{w''})] [W.J.HasSheafCompose (forget RingCat.{w₃})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]
  [W.J.HasSheafCompose (forget₂ CommRingCat.{w₃} RingCat.{w₃})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w''})]
  [W.J.HasSheafCompose (forget AddCommGrpCat.{w₃})]
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [HasSheafify Z.J AddCommGrpCat.{w''}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{w''}]
  [HasSheafify W.J AddCommGrpCat.{w₃}] [W.J.WEqualsLocallyBijective AddCommGrpCat.{w₃}]
  [HasSheafify X.J (Type w)] [HasSheafify Y.J (Type w')] [HasSheafify Z.J (Type w'')]
  [HasSheafify W.J (Type w₃)]
  (f : RingedToposHom X Y) (g : RingedToposHom Y Z) (h : RingedToposHom Z W)

omit [HasSheafify W.J AddCommGrpCat.{w₃}] [W.J.WEqualsLocallyBijective AddCommGrpCat.{w₃}]
  [HasSheafify X.J (Type w)] [HasSheafify Y.J (Type w')] [HasSheafify Z.J (Type w'')]
  [HasSheafify W.J (Type w₃)] in
/-- **The cocycle identity for the underived compositor of Stacks 03D6, on the unbounded homotopy
categories**, with both bracketings `h ∘ (g ∘ f)` and `(h ∘ g) ∘ f` identified with a morphism
`t`. -/
theorem pullbackMapHomotopyCompIso_assoc_of_eq (t : RingedToposHom X W)
    (e : h.comp (g.comp f) = t) (e' : (h.comp g).comp f = t) :
    Functor.whiskerLeft (DerivedPushforward.pullbackMapHomotopy h)
          (Functor.mapHomotopyCategoryCompIso
            (RingedToposHom.pullbackModulesCompIso f g).symm (ComplexShape.up ℤ)).hom ≫
        (Functor.mapHomotopyCategoryCompIso
          ((RingedToposHom.pullbackModulesCompIso (g.comp f) h).symm ≪≫
            eqToIso (congrArg
              (fun m : RingedToposHom X W => m.toModulesHom.pullbackModules) e))
          (ComplexShape.up ℤ)).hom =
      (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso
              (RingedToposHom.pullbackModulesCompIso g h).symm (ComplexShape.up ℤ)).hom
            (DerivedPushforward.pullbackMapHomotopy f) ≫
          (Functor.mapHomotopyCategoryCompIso
            ((RingedToposHom.pullbackModulesCompIso f (h.comp g)).symm ≪≫
              eqToIso (congrArg
                (fun m : RingedToposHom X W => m.toModulesHom.pullbackModules) e'))
            (ComplexShape.up ℤ)).hom :=
  mapHomotopyCategoryCompIso_assoc
    (RingedToposHom.pullbackModulesCompIso g h).symm
    (RingedToposHom.pullbackModulesCompIso f g).symm
    ((RingedToposHom.pullbackModulesCompIso (g.comp f) h).symm ≪≫
      eqToIso (congrArg (fun m : RingedToposHom X W => m.toModulesHom.pullbackModules) e))
    ((RingedToposHom.pullbackModulesCompIso f (h.comp g)).symm ≪≫
      eqToIso (congrArg (fun m : RingedToposHom X W => m.toModulesHom.pullbackModules) e'))
    (RingedToposHom.pullbackModulesCompIso_assoc_of_eq f g h t e e') (ComplexShape.up ℤ)

end Cocycle

end

end Stacks.Cohomology.DerivedPullbackCompositionOfToposHom

end
