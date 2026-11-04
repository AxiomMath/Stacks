module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposTwoIsoPullbackCoherence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.CompositionOfToposHomAssoc
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.BaseChangeOfToposHomTwoIso

/-!
# Coherence of derived pullbacks along morphisms of ringed topoi

For morphisms of ringed topoi, the derived pullback `Lf^*` comes with the composition
isomorphisms `Lf^* ∘ Lg^* ≅ L(g ∘ f)^*` and with the isomorphisms `Lf^* ≅ Lg^*` induced by
2-isomorphisms `f ≅ g`. This file proves that these isomorphisms are coherent.

## Main results

* `derivedPullbackCompComparison_assoc_of_eq`: the cocycle identity: the two ways of comparing
  `Lf^* ∘ Lg^* ∘ Lh^*` with the derived pullback along a threefold composite agree.
* `derivedPullbackCompComparison_assoc_associator`: the same with the associator 2-isomorphism in
  place of a transport.
* `derivedPullbackIsoOfTwoIso_trans`, `derivedPullbackIsoOfTwoIso_symm`: the isomorphism induced
  by a 2-isomorphism respects vertical composition and inverses.
* `derivedPullbackCompComparison_whiskerRight` and `derivedPullbackCompComparison_whiskerLeft`:
  the composition isomorphism is natural with respect to a 2-isomorphism in either factor.

## References

* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 04IC](https://stacks.math.columbia.edu/tag/04IC)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 0E47](https://stacks.math.columbia.edu/tag/0E47)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackOfToposHom

universe v u w v' u' w' v'' u'' w'' v₃ u₃ w₃

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance]
  Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy

noncomputable section

/-! ### Additive functors on homotopy categories -/

namespace Stacks.Homology

variable {A₀ A₁ A₂ : Type*} [Category* A₀] [Category* A₁] [Category* A₂]
  [Preadditive A₀] [Preadditive A₁] [Preadditive A₂]

/-- Two composites of morphisms of complexes have equal images in the homotopy category as soon
as they agree componentwise. -/
private theorem quotient_map_comp_eq_of_f_eq {K L₁ L₂ N : HomologicalComplex A₂ (ComplexShape.up ℤ)}
    (a : K ⟶ L₁) (b : L₁ ⟶ N) (c : K ⟶ L₂) (d : L₂ ⟶ N) (h : ∀ i, a.f i ≫ b.f i = c.f i ≫ d.f i) :
    (HomotopyCategory.quotient A₂ (ComplexShape.up ℤ)).map a ≫
      (HomotopyCategory.quotient A₂ (ComplexShape.up ℤ)).map b =
    (HomotopyCategory.quotient A₂ (ComplexShape.up ℤ)).map c ≫
      (HomotopyCategory.quotient A₂ (ComplexShape.up ℤ)).map d := by
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  ext i
  exact h i

/-- On homotopy categories, an identity `whiskerLeft F κ₁ ≫ eb = ea ≫ κ₂` of transformations of
additive functors holds componentwise. -/
theorem mapHomotopyCategory_whiskerLeft_app {F₀₁ : A₀ ⥤ A₁} {F₁₂ F₁₂' : A₁ ⥤ A₂}
    {F₀₂ F₀₂' : A₀ ⥤ A₂} [F₀₁.Additive] [F₁₂.Additive] [F₁₂'.Additive] [F₀₂.Additive]
    [F₀₂'.Additive] (ea : F₀₁ ⋙ F₁₂ ≅ F₀₂) (eb : F₀₁ ⋙ F₁₂' ≅ F₀₂') (κ₁ : F₁₂ ⟶ F₁₂')
    (κ₂ : F₀₂ ⟶ F₀₂') (hc : Functor.whiskerLeft F₀₁ κ₁ ≫ eb.hom = ea.hom ≫ κ₂)
    (P : HomotopyCategory A₀ (ComplexShape.up ℤ)) :
    (NatTrans.mapHomotopyCategory κ₁ (ComplexShape.up ℤ)).app
        ((F₀₁.mapHomotopyCategory (ComplexShape.up ℤ)).obj P) ≫
      (Functor.mapHomotopyCategoryCompIso eb (ComplexShape.up ℤ)).hom.app P =
    (Functor.mapHomotopyCategoryCompIso ea (ComplexShape.up ℤ)).hom.app P ≫
      (NatTrans.mapHomotopyCategory κ₂ (ComplexShape.up ℤ)).app P := by
  rcases P with ⟨K⟩
  exact quotient_map_comp_eq_of_f_eq _ _ _ _ fun i => by
    simp only [Functor.mapHomologicalComplex_obj_X, NatTrans.mapHomologicalComplex_app_f,
      Functor.mapHomologicalComplexCompIso_hom_app_f]
    exact NatTrans.congr_app hc (K.X i)

/-- On homotopy categories, an identity `whiskerRight κ₁ F ≫ eb = ea ≫ κ₂` of transformations of
additive functors holds componentwise. -/
theorem mapHomotopyCategory_whiskerRight_app {F₀₁ F₀₁' : A₀ ⥤ A₁} {F₁₂ : A₁ ⥤ A₂}
    {F₀₂ F₀₂' : A₀ ⥤ A₂} [F₀₁.Additive] [F₀₁'.Additive] [F₁₂.Additive] [F₀₂.Additive]
    [F₀₂'.Additive] (ea : F₀₁ ⋙ F₁₂ ≅ F₀₂) (eb : F₀₁' ⋙ F₁₂ ≅ F₀₂') (κ₁ : F₀₁ ⟶ F₀₁')
    (κ₂ : F₀₂ ⟶ F₀₂') (hc : Functor.whiskerRight κ₁ F₁₂ ≫ eb.hom = ea.hom ≫ κ₂)
    (P : HomotopyCategory A₀ (ComplexShape.up ℤ)) :
    (F₁₂.mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomotopyCategory κ₁ (ComplexShape.up ℤ)).app P) ≫
      (Functor.mapHomotopyCategoryCompIso eb (ComplexShape.up ℤ)).hom.app P =
    (Functor.mapHomotopyCategoryCompIso ea (ComplexShape.up ℤ)).hom.app P ≫
      (NatTrans.mapHomotopyCategory κ₂ (ComplexShape.up ℤ)).app P := by
  rcases P with ⟨K⟩
  exact quotient_map_comp_eq_of_f_eq _ _ _ _ fun i => by
    simp only [Functor.mapHomologicalComplex_obj_X, NatTrans.mapHomologicalComplex_app_f,
      Functor.mapHomologicalComplexCompIso_hom_app_f]
    exact NatTrans.congr_app hc (K.X i)

end Stacks.Homology


/-! ### The universal-property arguments, over the module categories -/

namespace Stacks.Cohomology.DerivedBaseChangeOfToposHom

section Spec2

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [HasSheafify X.J (Type w)] [HasSheafify Y.J (Type w')]

omit [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})] [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasSheafify X.J (Type w)] [HasSheafify Y.J (Type w')] in
/-- The transformations `σ₁`, `σ₂`, `σ₃` of derived functors induced, through the comparisons
`α₁`, `α₂`, `α₃` with the underived functors, by transformations `κ₁`, `κ₂`, `κ₃` of the underived
functors with `κ₁ ≫ κ₂ = κ₃` satisfy `σ₁ ≫ σ₂ = σ₃`. -/
theorem leftDerived_comp_of_natTrans
    {F₁ F₂ F₃ : SheafOfModules.{w'} (SheafOfModules.Tensor.ringSheaf Y.O) ⥤
      SheafOfModules.{w} (SheafOfModules.Tensor.ringSheaf X.O)}
    [F₁.Additive] [F₂.Additive] [F₃.Additive]
    {L₁ L₂ L₃ : DerivedCategory (SheafOfModules.{w'} (SheafOfModules.Tensor.ringSheaf Y.O)) ⥤
      DerivedCategory (SheafOfModules.{w} (SheafOfModules.Tensor.ringSheaf X.O))}
    (α₁ : DerivedCategory.Qh ⋙ L₁ ⟶ F₁.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (α₂ : DerivedCategory.Qh ⋙ L₂ ⟶ F₂.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (α₃ : DerivedCategory.Qh ⋙ L₃ ⟶ F₃.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    [L₃.IsLeftDerivedFunctor α₃ (quasiIsoTarget (Y := Y))]
    (κ₁ : F₁ ⟶ F₂) (κ₂ : F₂ ⟶ F₃) (κ₃ : F₁ ⟶ F₃) (σ₁ : L₁ ⟶ L₂) (σ₂ : L₂ ⟶ L₃) (σ₃ : L₁ ⟶ L₃)
    (fac₁ : ∀ P, σ₁.app (DerivedCategory.Qh.obj P) ≫ α₂.app P =
      α₁.app P ≫
          DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory κ₁ (ComplexShape.up ℤ)).app P))
    (fac₂ : ∀ P, σ₂.app (DerivedCategory.Qh.obj P) ≫ α₃.app P =
      α₂.app P ≫
          DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory κ₂ (ComplexShape.up ℤ)).app P))
    (fac₃ : ∀ P, σ₃.app (DerivedCategory.Qh.obj P) ≫ α₃.app P =
      α₁.app P ≫
          DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory κ₃ (ComplexShape.up ℤ)).app P))
    (hκ : κ₁ ≫ κ₂ = κ₃) :
    σ₁ ≫ σ₂ = σ₃ := by
  apply L₃.leftDerived_ext α₃ (quasiIsoTarget (Y := Y))
  ext P
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Category.assoc]
  rw [fac₂ P, reassoc_of% (fac₁ P), fac₃ P, ← Functor.map_comp, ← NatTrans.comp_app,
    ← NatTrans.mapHomotopyCategory_comp, hκ]

end Spec2

section Spec3

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

omit [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [Z.J.HasSheafCompose (forget RingCat.{w''})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})] [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w''})] [HasSheafify X.J (Type w)]
  [HasSheafify Y.J (Type w')] [HasSheafify Z.J (Type w'')] in
/-- Given transformations `κ₁`, `κ₂` of underived functors, with `κ₁` acting on the second
factor, compatible with the two composition isomorphisms `ea`, `eb`, the induced transformations
`σ₁`, `σ₂` of derived functors are compatible with the derived composition comparisons `da`,
`db`. -/
theorem leftDerived_whiskerLeft_of_iso
    {F₀₁ : SheafOfModules.{w''} (SheafOfModules.Tensor.ringSheaf Z.O) ⥤
      SheafOfModules.{w'} (SheafOfModules.Tensor.ringSheaf Y.O)}
    {F₁₂ F₁₂' : SheafOfModules.{w'} (SheafOfModules.Tensor.ringSheaf Y.O) ⥤
      SheafOfModules.{w} (SheafOfModules.Tensor.ringSheaf X.O)}
    {F₀₂ F₀₂' : SheafOfModules.{w''} (SheafOfModules.Tensor.ringSheaf Z.O) ⥤
      SheafOfModules.{w} (SheafOfModules.Tensor.ringSheaf X.O)}
    [F₀₁.Additive] [F₁₂.Additive] [F₁₂'.Additive] [F₀₂.Additive] [F₀₂'.Additive]
    {L₀₁ : DerivedCategory (SheafOfModules.{w''} (SheafOfModules.Tensor.ringSheaf Z.O)) ⥤
      DerivedCategory (SheafOfModules.{w'} (SheafOfModules.Tensor.ringSheaf Y.O))}
    {L₁₂ L₁₂' : DerivedCategory (SheafOfModules.{w'} (SheafOfModules.Tensor.ringSheaf Y.O)) ⥤
      DerivedCategory (SheafOfModules.{w} (SheafOfModules.Tensor.ringSheaf X.O))}
    {L₀₂ L₀₂' : DerivedCategory (SheafOfModules.{w''} (SheafOfModules.Tensor.ringSheaf Z.O)) ⥤
      DerivedCategory (SheafOfModules.{w} (SheafOfModules.Tensor.ringSheaf X.O))}
    (α₀₁ : DerivedCategory.Qh ⋙ L₀₁ ⟶ F₀₁.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh)
    (α₁₂ : DerivedCategory.Qh ⋙ L₁₂ ⟶ F₁₂.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh)
    (α₁₂' : DerivedCategory.Qh ⋙ L₁₂' ⟶ F₁₂'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh)
    (α₀₂ : DerivedCategory.Qh ⋙ L₀₂ ⟶ F₀₂.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh)
    (α₀₂' : DerivedCategory.Qh ⋙ L₀₂' ⟶ F₀₂'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh)
    [L₀₂'.IsLeftDerivedFunctor α₀₂' (quasiIsoTarget (Y := Z))]
    (ea : F₀₁ ⋙ F₁₂ ≅ F₀₂) (eb : F₀₁ ⋙ F₁₂' ≅ F₀₂') (κ₁ : F₁₂ ⟶ F₁₂') (κ₂ : F₀₂ ⟶ F₀₂')
    (da : L₀₁ ⋙ L₁₂ ⟶ L₀₂) (db : L₀₁ ⋙ L₁₂' ⟶ L₀₂') (σ₁ : L₁₂ ⟶ L₁₂') (σ₂ : L₀₂ ⟶ L₀₂')
    (faca : ∀ P, da.app (DerivedCategory.Qh.obj P) ≫ α₀₂.app P =
      L₁₂.map (α₀₁.app P) ≫ α₁₂.app ((F₀₁.mapHomotopyCategory (ComplexShape.up ℤ)).obj P) ≫
        DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso ea
            (ComplexShape.up ℤ)).hom.app P))
    (facb : ∀ P, db.app (DerivedCategory.Qh.obj P) ≫ α₀₂'.app P =
      L₁₂'.map (α₀₁.app P) ≫ α₁₂'.app ((F₀₁.mapHomotopyCategory (ComplexShape.up ℤ)).obj P) ≫
        DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso eb
            (ComplexShape.up ℤ)).hom.app P))
    (fac₁ : ∀ P, σ₁.app (DerivedCategory.Qh.obj P) ≫ α₁₂'.app P =
      α₁₂.app P ≫
          DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory κ₁ (ComplexShape.up ℤ)).app P))
    (fac₂ : ∀ P, σ₂.app (DerivedCategory.Qh.obj P) ≫ α₀₂'.app P =
      α₀₂.app P ≫
          DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory κ₂ (ComplexShape.up ℤ)).app P))
    (hc : Functor.whiskerLeft F₀₁ κ₁ ≫ eb.hom = ea.hom ≫ κ₂) (M :
      DerivedCategory (SheafOfModules.{w''} (SheafOfModules.Tensor.ringSheaf Z.O))) :
    da.app M ≫ σ₂.app M = σ₁.app (L₀₁.obj M) ≫ db.app M := by
  have key : da ≫ σ₂ = Functor.whiskerLeft L₀₁ σ₁ ≫ db := by
    apply L₀₂'.leftDerived_ext α₀₂' (quasiIsoTarget (Y := Z))
    ext P
    have hn := σ₁.naturality (α₀₁.app P)
    dsimp only [Functor.comp_obj] at hn
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Category.assoc]
    rw [fac₂ P, reassoc_of% (faca P), facb P, ← reassoc_of% hn, reassoc_of% (fac₁ _),
      ← Functor.map_comp, ← Functor.map_comp,
      Stacks.Homology.mapHomotopyCategory_whiskerLeft_app ea eb κ₁ κ₂ hc P]
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app] using NatTrans.congr_app key M

omit [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [Z.J.HasSheafCompose (forget RingCat.{w''})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})] [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w''})] [HasSheafify X.J (Type w)]
  [HasSheafify Y.J (Type w')] [HasSheafify Z.J (Type w'')] in
/-- Given transformations `κ₁`, `κ₂` of underived functors, with `κ₁` acting on the first
factor, compatible with the two composition isomorphisms `ea`, `eb`, the induced transformations
`σ₁`, `σ₂` of derived functors are compatible with the derived composition comparisons `da`,
`db`. -/
theorem leftDerived_whiskerRight_of_iso
    {F₀₁ F₀₁' : SheafOfModules.{w''} (SheafOfModules.Tensor.ringSheaf Z.O) ⥤
      SheafOfModules.{w'} (SheafOfModules.Tensor.ringSheaf Y.O)}
    {F₁₂ : SheafOfModules.{w'} (SheafOfModules.Tensor.ringSheaf Y.O) ⥤
      SheafOfModules.{w} (SheafOfModules.Tensor.ringSheaf X.O)}
    {F₀₂ F₀₂' : SheafOfModules.{w''} (SheafOfModules.Tensor.ringSheaf Z.O) ⥤
      SheafOfModules.{w} (SheafOfModules.Tensor.ringSheaf X.O)}
    [F₀₁.Additive] [F₀₁'.Additive] [F₁₂.Additive] [F₀₂.Additive] [F₀₂'.Additive]
    {L₀₁ L₀₁' : DerivedCategory (SheafOfModules.{w''} (SheafOfModules.Tensor.ringSheaf Z.O)) ⥤
      DerivedCategory (SheafOfModules.{w'} (SheafOfModules.Tensor.ringSheaf Y.O))}
    {L₁₂ : DerivedCategory (SheafOfModules.{w'} (SheafOfModules.Tensor.ringSheaf Y.O)) ⥤
      DerivedCategory (SheafOfModules.{w} (SheafOfModules.Tensor.ringSheaf X.O))}
    {L₀₂ L₀₂' : DerivedCategory (SheafOfModules.{w''} (SheafOfModules.Tensor.ringSheaf Z.O)) ⥤
      DerivedCategory (SheafOfModules.{w} (SheafOfModules.Tensor.ringSheaf X.O))}
    (α₀₁ : DerivedCategory.Qh ⋙ L₀₁ ⟶ F₀₁.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh)
    (α₀₁' : DerivedCategory.Qh ⋙ L₀₁' ⟶ F₀₁'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh)
    (α₁₂ : DerivedCategory.Qh ⋙ L₁₂ ⟶ F₁₂.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh)
    (α₀₂ : DerivedCategory.Qh ⋙ L₀₂ ⟶ F₀₂.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh)
    (α₀₂' : DerivedCategory.Qh ⋙ L₀₂' ⟶ F₀₂'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh)
    [L₀₂'.IsLeftDerivedFunctor α₀₂' (quasiIsoTarget (Y := Z))]
    (ea : F₀₁ ⋙ F₁₂ ≅ F₀₂) (eb : F₀₁' ⋙ F₁₂ ≅ F₀₂') (κ₁ : F₀₁ ⟶ F₀₁') (κ₂ : F₀₂ ⟶ F₀₂')
    (da : L₀₁ ⋙ L₁₂ ⟶ L₀₂) (db : L₀₁' ⋙ L₁₂ ⟶ L₀₂') (σ₁ : L₀₁ ⟶ L₀₁') (σ₂ : L₀₂ ⟶ L₀₂')
    (faca : ∀ P, da.app (DerivedCategory.Qh.obj P) ≫ α₀₂.app P =
      L₁₂.map (α₀₁.app P) ≫ α₁₂.app ((F₀₁.mapHomotopyCategory (ComplexShape.up ℤ)).obj P) ≫
        DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso ea
            (ComplexShape.up ℤ)).hom.app P))
    (facb : ∀ P, db.app (DerivedCategory.Qh.obj P) ≫ α₀₂'.app P =
      L₁₂.map (α₀₁'.app P) ≫ α₁₂.app ((F₀₁'.mapHomotopyCategory (ComplexShape.up ℤ)).obj P) ≫
        DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso eb
            (ComplexShape.up ℤ)).hom.app P))
    (fac₁ : ∀ P, σ₁.app (DerivedCategory.Qh.obj P) ≫ α₀₁'.app P =
      α₀₁.app P ≫
          DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory κ₁ (ComplexShape.up ℤ)).app P))
    (fac₂ : ∀ P, σ₂.app (DerivedCategory.Qh.obj P) ≫ α₀₂'.app P =
      α₀₂.app P ≫
          DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory κ₂ (ComplexShape.up ℤ)).app P))
    (hc : Functor.whiskerRight κ₁ F₁₂ ≫ eb.hom = ea.hom ≫ κ₂) (M :
      DerivedCategory (SheafOfModules.{w''} (SheafOfModules.Tensor.ringSheaf Z.O))) :
    da.app M ≫ σ₂.app M = L₁₂.map (σ₁.app M) ≫ db.app M := by
  have key : da ≫ σ₂ = Functor.whiskerRight σ₁ L₁₂ ≫ db := by
    apply L₀₂'.leftDerived_ext α₀₂' (quasiIsoTarget (Y := Z))
    ext P
    have hn := α₁₂.naturality ((NatTrans.mapHomotopyCategory κ₁ (ComplexShape.up ℤ)).app P)
    dsimp only [Functor.comp_obj, Functor.comp_map] at hn
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Category.assoc]
    rw [fac₂ P, reassoc_of% (faca P), facb P, ← L₁₂.map_comp_assoc, fac₁ P, L₁₂.map_comp_assoc,
      reassoc_of% hn, ← Functor.map_comp, ← Functor.map_comp,
      Stacks.Homology.mapHomotopyCategory_whiskerRight_app ea eb κ₁ κ₂ hc P]
  simpa only [NatTrans.comp_app, Functor.whiskerRight_app] using NatTrans.congr_app key M

end Spec3

end Stacks.Cohomology.DerivedBaseChangeOfToposHom



namespace AlgebraicGeometry.RingedToposHom.TwoIso

variable {A : RingedTopos.{v, u, w}} {B : RingedTopos.{v', u', w'}}
  {C : RingedTopos.{v'', u'', w''}} {D : RingedTopos.{v₃, u₃, w₃}}
  [A.J.HasSheafCompose (forget RingCat.{w})] [B.J.HasSheafCompose (forget RingCat.{w'})]
  [C.J.HasSheafCompose (forget RingCat.{w''})] [D.J.HasSheafCompose (forget RingCat.{w₃})]
  [A.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [C.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]
  [D.J.HasSheafCompose (forget₂ CommRingCat.{w₃} RingCat.{w₃})]

/-- The underlying isomorphism of direct images of the 2-isomorphism of an equality is the
transport along the induced equality of direct images. -/
theorem ofEq_e {f g : RingedToposHom A B} (p : f = g) :
    (ofEq p).e =
      eqToIso (congrArg (fun m : RingedToposHom A B => m.toToposHom.pushforward) p) := by
  subst p
  rfl

/-- **The associator 2-isomorphism is the 2-isomorphism of the equality `comp_assoc`.** -/
theorem associator_eq_ofEq (f : RingedToposHom A B) (g : RingedToposHom B C)
    (h : RingedToposHom C D) : associator f g h = ofEq (comp_assoc f g h) := by
  refine TwoIso.ext (Iso.ext (NatTrans.ext (funext fun X => ?_)))
  rw [ofEq_e]
  rfl

end AlgebraicGeometry.RingedToposHom.TwoIso

namespace Stacks.Cohomology.DerivedBaseChangeOfToposHom

open Stacks.Cohomology.DerivedPullbackCompositionOfToposHom

section TwoIso

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [HasSheafify X.J (Type w)] [HasSheafify Y.J (Type w')]

/-- The derived pullback isomorphism of a 2-isomorphism is characterized by its composite with the
comparison of Stacks 06YY: on a complex it is the underived pullback isomorphism. -/
theorem derivedPullbackIsoOfTwoIso_hom_fac {m₁ m₂ : RingedToposHom X Y}
    (s : RingedToposHom.TwoIso m₁ m₂)
    (P : HomotopyCategory (SheafOfModules.{w'}
      (SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ)) :
    (derivedPullbackIsoOfTwoIso s).hom.app (DerivedCategory.Qh.obj P) ≫
        (derivedPullbackComparison' m₂).app P =
      (derivedPullbackComparison' m₁).app P ≫
        DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory s.pullbackModulesIso.hom (ComplexShape.up ℤ)).app P) :=
  Functor.leftDerivedNatTrans_app _ _ _ _ (quasiIsoTarget (Y := Y)) _ P

/-- **The derived pullback isomorphism of a vertical composite of 2-isomorphisms is the composite
of the two derived pullback isomorphisms.** -/
theorem derivedPullbackIsoOfTwoIso_trans {m₁ m₂ m₃ : RingedToposHom X Y}
    (s : RingedToposHom.TwoIso m₁ m₂) (s' : RingedToposHom.TwoIso m₂ m₃) :
    derivedPullbackIsoOfTwoIso (s.trans s') =
      derivedPullbackIsoOfTwoIso s ≪≫ derivedPullbackIsoOfTwoIso s' :=
  Iso.ext (leftDerived_comp_of_natTrans (derivedPullbackComparison' m₁)
    (derivedPullbackComparison' m₂) (derivedPullbackComparison' m₃)
    s.pullbackModulesIso.hom s'.pullbackModulesIso.hom (s.trans s').pullbackModulesIso.hom
    (derivedPullbackIsoOfTwoIso s).hom (derivedPullbackIsoOfTwoIso s').hom
    (derivedPullbackIsoOfTwoIso (s.trans s')).hom
    (derivedPullbackIsoOfTwoIso_hom_fac s) (derivedPullbackIsoOfTwoIso_hom_fac s')
    (derivedPullbackIsoOfTwoIso_hom_fac (s.trans s'))
    (by rw [RingedToposHom.TwoIso.pullbackModulesIso_trans, Iso.trans_hom])).symm

/-- The derived pullback isomorphism of the inverse of a 2-isomorphism is the inverse of its
derived pullback isomorphism. -/
theorem derivedPullbackIsoOfTwoIso_symm {m₁ m₂ : RingedToposHom X Y}
    (s : RingedToposHom.TwoIso m₁ m₂) :
    derivedPullbackIsoOfTwoIso s.symm = (derivedPullbackIsoOfTwoIso s).symm := by
  have h := derivedPullbackIsoOfTwoIso_trans s s.symm
  rw [RingedToposHom.TwoIso.trans_symm_self, derivedPullbackIsoOfTwoIso_refl] at h
  exact Iso.ext (Iso.inv_ext' (congrArg Iso.hom h).symm)

end TwoIso

section Whisker

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

/-- **The composition isomorphism of Stacks 0D6D is natural in a 2-isomorphism of its first
factor.**  For `s : f₁ ≅ f₂` and `g`, comparing `Lf₁^* Lg^*` with `L(g ∘ f₁)^*` and then passing
to `L(g ∘ f₂)^*` along `g ∘ s` agrees with first passing from `Lf₁^*` to `Lf₂^*` along `s`. -/
theorem derivedPullbackCompComparison_whiskerRight {f₁ f₂ : RingedToposHom X Y}
    (s : RingedToposHom.TwoIso f₁ f₂) (g : RingedToposHom Y Z)
    (M : DerivedCategory (SheafOfModules.{w''}
      (SheafOfModules.Tensor.ringSheaf Z.O))) :
    (derivedPullbackCompComparison f₁ g).app M ≫
        (derivedPullbackIsoOfTwoIso (s.whiskerRight g)).hom.app M =
      (derivedPullbackIsoOfTwoIso s).hom.app ((derivedPullback g).obj M) ≫
        (derivedPullbackCompComparison f₂ g).app M :=
  leftDerived_whiskerLeft_of_iso (derivedPullbackComparison' g) (derivedPullbackComparison' f₁)
    (derivedPullbackComparison' f₂) (derivedPullbackComparison' (g.comp f₁))
    (derivedPullbackComparison' (g.comp f₂))
    (RingedToposHom.pullbackModulesCompIso f₁ g).symm
    (RingedToposHom.pullbackModulesCompIso f₂ g).symm
    s.pullbackModulesIso.hom (s.whiskerRight g).pullbackModulesIso.hom
    (derivedPullbackCompComparison f₁ g) (derivedPullbackCompComparison f₂ g)
    (derivedPullbackIsoOfTwoIso s).hom (derivedPullbackIsoOfTwoIso (s.whiskerRight g)).hom
    (derivedPullbackCompComparison_app_comp_derivedPullbackComparison_app' f₁ g)
    (derivedPullbackCompComparison_app_comp_derivedPullbackComparison_app' f₂ g)
    (derivedPullbackIsoOfTwoIso_hom_fac s) (derivedPullbackIsoOfTwoIso_hom_fac (s.whiskerRight g))
    (RingedToposHom.TwoIso.pullbackModulesCompIso_inv_whiskerRight s g).symm M

/-- **The composition isomorphism of Stacks 0D6D is natural in a 2-isomorphism of its second
factor.**  For `f` and `s : g₁ ≅ g₂`, comparing `Lf^* Lg₁^*` with `L(g₁ ∘ f)^*` and then passing
to `L(g₂ ∘ f)^*` along `s ∘ f` agrees with first passing from `Lg₁^*` to `Lg₂^*` along `s`. -/
theorem derivedPullbackCompComparison_whiskerLeft (f : RingedToposHom X Y)
    {g₁ g₂ : RingedToposHom Y Z} (s : RingedToposHom.TwoIso g₁ g₂)
    (M : DerivedCategory (SheafOfModules.{w''}
      (SheafOfModules.Tensor.ringSheaf Z.O))) :
    (derivedPullbackCompComparison f g₁).app M ≫
        (derivedPullbackIsoOfTwoIso (s.whiskerLeft f)).hom.app M =
      (derivedPullback f).map ((derivedPullbackIsoOfTwoIso s).hom.app M) ≫
        (derivedPullbackCompComparison f g₂).app M :=
  leftDerived_whiskerRight_of_iso (derivedPullbackComparison' g₁) (derivedPullbackComparison' g₂)
    (derivedPullbackComparison' f) (derivedPullbackComparison' (g₁.comp f))
    (derivedPullbackComparison' (g₂.comp f))
    (RingedToposHom.pullbackModulesCompIso f g₁).symm
    (RingedToposHom.pullbackModulesCompIso f g₂).symm
    s.pullbackModulesIso.hom (s.whiskerLeft f).pullbackModulesIso.hom
    (derivedPullbackCompComparison f g₁) (derivedPullbackCompComparison f g₂)
    (derivedPullbackIsoOfTwoIso s).hom (derivedPullbackIsoOfTwoIso (s.whiskerLeft f)).hom
    (derivedPullbackCompComparison_app_comp_derivedPullbackComparison_app' f g₁)
    (derivedPullbackCompComparison_app_comp_derivedPullbackComparison_app' f g₂)
    (derivedPullbackIsoOfTwoIso_hom_fac s) (derivedPullbackIsoOfTwoIso_hom_fac (s.whiskerLeft f))
    (RingedToposHom.TwoIso.pullbackModulesCompIso_inv_whiskerLeft f s).symm M

end Whisker

end Stacks.Cohomology.DerivedBaseChangeOfToposHom


/-! ### The cocycle identity of Stacks 0D6D -/

namespace Stacks.Cohomology.DerivedPullbackCompositionOfToposHom

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

omit [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [Z.J.HasSheafCompose (forget RingCat.{w''})] [W.J.HasSheafCompose (forget RingCat.{w₃})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]
  [W.J.HasSheafCompose (forget₂ CommRingCat.{w₃} RingCat.{w₃})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})] [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w''})]
  [W.J.HasSheafCompose (forget AddCommGrpCat.{w₃})] [HasSheafify X.J (Type w)]
  [HasSheafify Y.J (Type w')] [HasSheafify Z.J (Type w'')] [HasSheafify W.J (Type w₃)] in
/-- If four comparisons of derived functors are compatible, through the comparisons `α` with
the underived functors, with four composition isomorphisms of the underived functors satisfying
the cocycle identity, then they satisfy it themselves, up to the transports `τ` and `σ` between
the codomains of the two routes. -/
theorem leftDerived_assoc_of_iso {F₀₁ : SheafOfModules.{w₃} (SheafOfModules.Tensor.ringSheaf W.O) ⥤
      SheafOfModules.{w''} (SheafOfModules.Tensor.ringSheaf Z.O)}
    {F₁₂ : SheafOfModules.{w''} (SheafOfModules.Tensor.ringSheaf Z.O) ⥤
      SheafOfModules.{w'} (SheafOfModules.Tensor.ringSheaf Y.O)}
    {F₂₃ : SheafOfModules.{w'} (SheafOfModules.Tensor.ringSheaf Y.O) ⥤
      SheafOfModules.{w} (SheafOfModules.Tensor.ringSheaf X.O)}
    {F₀₂ : SheafOfModules.{w₃} (SheafOfModules.Tensor.ringSheaf W.O) ⥤
      SheafOfModules.{w'} (SheafOfModules.Tensor.ringSheaf Y.O)}
    {F₁₃ : SheafOfModules.{w''} (SheafOfModules.Tensor.ringSheaf Z.O) ⥤
      SheafOfModules.{w} (SheafOfModules.Tensor.ringSheaf X.O)}
    {F₀₃ : SheafOfModules.{w₃} (SheafOfModules.Tensor.ringSheaf W.O) ⥤
      SheafOfModules.{w} (SheafOfModules.Tensor.ringSheaf X.O)}
    [F₀₁.Additive] [F₁₂.Additive] [F₂₃.Additive] [F₀₂.Additive] [F₁₃.Additive] [F₀₃.Additive]
    {L₀₁ : DerivedCategory (SheafOfModules.{w₃} (SheafOfModules.Tensor.ringSheaf W.O)) ⥤
      DerivedCategory (SheafOfModules.{w''} (SheafOfModules.Tensor.ringSheaf Z.O))}
    {L₁₂ : DerivedCategory (SheafOfModules.{w''} (SheafOfModules.Tensor.ringSheaf Z.O)) ⥤
      DerivedCategory (SheafOfModules.{w'} (SheafOfModules.Tensor.ringSheaf Y.O))}
    {L₂₃ : DerivedCategory (SheafOfModules.{w'} (SheafOfModules.Tensor.ringSheaf Y.O)) ⥤
      DerivedCategory (SheafOfModules.{w} (SheafOfModules.Tensor.ringSheaf X.O))}
    {L₀₂ : DerivedCategory (SheafOfModules.{w₃} (SheafOfModules.Tensor.ringSheaf W.O)) ⥤
      DerivedCategory (SheafOfModules.{w'} (SheafOfModules.Tensor.ringSheaf Y.O))}
    {L₁₃ : DerivedCategory (SheafOfModules.{w''} (SheafOfModules.Tensor.ringSheaf Z.O)) ⥤
      DerivedCategory (SheafOfModules.{w} (SheafOfModules.Tensor.ringSheaf X.O))}
    {L₀₃ L₀₃' L₀₃'' : DerivedCategory (SheafOfModules.{w₃} (SheafOfModules.Tensor.ringSheaf W.O)) ⥤
      DerivedCategory (SheafOfModules.{w} (SheafOfModules.Tensor.ringSheaf X.O))}
    (α₀₁ : DerivedCategory.Qh ⋙ L₀₁ ⟶ F₀₁.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh)
    (α₁₂ : DerivedCategory.Qh ⋙ L₁₂ ⟶ F₁₂.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh)
    (α₂₃ : DerivedCategory.Qh ⋙ L₂₃ ⟶ F₂₃.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh)
    (α₀₂ : DerivedCategory.Qh ⋙ L₀₂ ⟶ F₀₂.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh)
    (α₁₃ : DerivedCategory.Qh ⋙ L₁₃ ⟶ F₁₃.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh)
    (α₀₃ : DerivedCategory.Qh ⋙ L₀₃ ⟶ F₀₃.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh)
    [L₀₃.IsLeftDerivedFunctor α₀₃ (quasiIsoTarget (Y := W))]
    (e₀₁₂ : F₀₁ ⋙ F₁₂ ≅ F₀₂) (e₁₂₃ : F₁₂ ⋙ F₂₃ ≅ F₁₃) (e₀₁₃ : F₀₁ ⋙ F₁₃ ≅ F₀₃)
    (e₀₂₃ : F₀₂ ⋙ F₂₃ ≅ F₀₃)
    (d₀₁₂ : L₀₁ ⋙ L₁₂ ⟶ L₀₂) (d₁₂₃ : L₁₂ ⋙ L₂₃ ⟶ L₁₃)
    (d₀₁₃ : L₀₁ ⋙ L₁₃ ⟶ L₀₃') (τ : L₀₃' ⟶ L₀₃) (d₀₂₃ : L₀₂ ⋙ L₂₃ ⟶ L₀₃'') (σ : L₀₃'' ⟶ L₀₃)
    (fac₀₁₂ : ∀ P, d₀₁₂.app (DerivedCategory.Qh.obj P) ≫ α₀₂.app P =
      L₁₂.map (α₀₁.app P) ≫ α₁₂.app ((F₀₁.mapHomotopyCategory (ComplexShape.up ℤ)).obj P) ≫
        DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso e₀₁₂
            (ComplexShape.up ℤ)).hom.app P))
    (fac₁₂₃ : ∀ P, d₁₂₃.app (DerivedCategory.Qh.obj P) ≫ α₁₃.app P =
      L₂₃.map (α₁₂.app P) ≫ α₂₃.app ((F₁₂.mapHomotopyCategory (ComplexShape.up ℤ)).obj P) ≫
        DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso e₁₂₃
            (ComplexShape.up ℤ)).hom.app P))
    (fac₀₁₃ : ∀ P, d₀₁₃.app (DerivedCategory.Qh.obj P) ≫ τ.app (DerivedCategory.Qh.obj P) ≫
      α₀₃.app P =
      L₁₃.map (α₀₁.app P) ≫ α₁₃.app ((F₀₁.mapHomotopyCategory (ComplexShape.up ℤ)).obj P) ≫
        DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso e₀₁₃
            (ComplexShape.up ℤ)).hom.app P))
    (fac₀₂₃ : ∀ P, d₀₂₃.app (DerivedCategory.Qh.obj P) ≫ σ.app (DerivedCategory.Qh.obj P) ≫
      α₀₃.app P =
      L₂₃.map (α₀₂.app P) ≫ α₂₃.app ((F₀₂.mapHomotopyCategory (ComplexShape.up ℤ)).obj P) ≫
        DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso e₀₂₃
            (ComplexShape.up ℤ)).hom.app P))
    (hc : Functor.whiskerLeft F₀₁ e₁₂₃.hom ≫ e₀₁₃.hom =
      (Functor.associator _ _ _).inv ≫ Functor.whiskerRight e₀₁₂.hom F₂₃ ≫ e₀₂₃.hom)
    (M : DerivedCategory (SheafOfModules.{w₃} (SheafOfModules.Tensor.ringSheaf W.O))) :
    d₁₂₃.app (L₀₁.obj M) ≫ d₀₁₃.app M ≫ τ.app M =
      L₂₃.map (d₀₁₂.app M) ≫ d₀₂₃.app M ≫ σ.app M :=
  leftDerived_comparison_assoc_app α₀₁ α₁₂ α₂₃ α₀₂ α₁₃ α₀₃ (quasiIsoTarget (Y := W))
    (Functor.mapHomotopyCategoryCompIso e₀₁₂ (ComplexShape.up ℤ)).hom
    (Functor.mapHomotopyCategoryCompIso e₁₂₃ (ComplexShape.up ℤ)).hom
    (Functor.mapHomotopyCategoryCompIso e₀₁₃ (ComplexShape.up ℤ)).hom
    (Functor.mapHomotopyCategoryCompIso e₀₂₃ (ComplexShape.up ℤ)).hom
    d₀₁₂ d₁₂₃ d₀₁₃ τ d₀₂₃ σ fac₀₁₂ fac₁₂₃ fac₀₁₃ fac₀₂₃
    (Stacks.Cohomology.DerivedBaseChangeComposition.mapHomotopyCategoryCompIso_assoc
      e₀₁₂ e₁₂₃ e₀₁₃ e₀₂₃ hc (ComplexShape.up ℤ)) M

variable (f : RingedToposHom X Y) (g : RingedToposHom Y Z) (h : RingedToposHom Z W)

/-- **The cocycle identity of Stacks 0D6D**, for morphisms of ringed topoi. The two ways of
comparing `Lf^* Lg^* Lh^*` with the derived pullback along the threefold composite agree, each
bracketing of the composite being compared with a third morphism `t`. -/
theorem derivedPullbackCompComparison_assoc_of_eq (t : RingedToposHom X W)
    (e : h.comp (g.comp f) = t) (e' : (h.comp g).comp f = t) (M :
      DerivedCategory (SheafOfModules.{w₃} (SheafOfModules.Tensor.ringSheaf W.O))) :
    (derivedPullbackCompComparison f g).app ((derivedPullback h).obj M) ≫
        (derivedPullbackCompComparison (g.comp f) h).app M ≫
        (eqToHom (congrArg (fun m : RingedToposHom X W => derivedPullback m) e)).app M =
      (derivedPullback f).map ((derivedPullbackCompComparison g h).app M) ≫
        (derivedPullbackCompComparison f (h.comp g)).app M ≫
        (eqToHom (congrArg (fun m : RingedToposHom X W => derivedPullback m) e')).app M :=
  leftDerived_assoc_of_iso
    (derivedPullbackComparison' h) (derivedPullbackComparison' g)
    (derivedPullbackComparison' f) (derivedPullbackComparison' (h.comp g))
    (derivedPullbackComparison' (g.comp f)) (derivedPullbackComparison' t)
    (RingedToposHom.pullbackModulesCompIso g h).symm
    (RingedToposHom.pullbackModulesCompIso f g).symm
    ((RingedToposHom.pullbackModulesCompIso (g.comp f) h).symm ≪≫
      eqToIso (congrArg (fun m : RingedToposHom X W => m.toModulesHom.pullbackModules) e))
    ((RingedToposHom.pullbackModulesCompIso f (h.comp g)).symm ≪≫
      eqToIso (congrArg (fun m : RingedToposHom X W => m.toModulesHom.pullbackModules) e'))
    (derivedPullbackCompComparison g h) (derivedPullbackCompComparison f g)
    (derivedPullbackCompComparison (g.comp f) h)
    (eqToHom (congrArg (fun m : RingedToposHom X W => derivedPullback m) e))
    (derivedPullbackCompComparison f (h.comp g))
    (eqToHom (congrArg (fun m : RingedToposHom X W => derivedPullback m) e'))
    (derivedPullbackCompComparison_app_comp_derivedPullbackComparison_app' g h)
    (derivedPullbackCompComparison_app_comp_derivedPullbackComparison_app' f g)
    (derivedPullbackCompComparison_app_comp_derivedPullbackComparison_app_of_eq (g.comp f) h t e)
    (derivedPullbackCompComparison_app_comp_derivedPullbackComparison_app_of_eq f (h.comp g) t e')
    (RingedToposHom.pullbackModulesCompIso_assoc_of_eq f g h t e e') M

/-- The transport of `Stacks.Cohomology.DerivedBaseChangeOfToposHom.derivedPullbackCongr` is the
transport along the induced equality of derived pullbacks. -/
theorem derivedPullbackCongr_hom_app {m₁ m₂ : RingedToposHom X W} (p : m₁ = m₂)
    (M : DerivedCategory (SheafOfModules.{w₃} (SheafOfModules.Tensor.ringSheaf W.O))) :
    (Stacks.Cohomology.DerivedBaseChangeOfToposHom.derivedPullbackCongr p).hom.app M =
      (eqToHom (congrArg (fun m : RingedToposHom X W => derivedPullback m) p)).app M := by
  subst p
  rfl

/-- **The cocycle identity of Stacks 0D6D with the associator 2-isomorphism.**  Comparing
`Lf^* Lg^* Lh^*` with `L(h ∘ (g ∘ f))^*` and passing to `L((h ∘ g) ∘ f)^*` along the derived
pullback isomorphism of the associator 2-isomorphism agrees with the comparison through
`L(h ∘ g)^*`. -/
theorem derivedPullbackCompComparison_assoc_associator
    (M : DerivedCategory (SheafOfModules.{w₃} (SheafOfModules.Tensor.ringSheaf W.O))) :
    (derivedPullbackCompComparison f g).app ((derivedPullback h).obj M) ≫
        (derivedPullbackCompComparison (g.comp f) h).app M ≫
        (Stacks.Cohomology.DerivedBaseChangeOfToposHom.derivedPullbackIsoOfTwoIso
          (RingedToposHom.TwoIso.associator f g h)).hom.app M =
      (derivedPullback f).map ((derivedPullbackCompComparison g h).app M) ≫
        (derivedPullbackCompComparison f (h.comp g)).app M := by
  rw [RingedToposHom.TwoIso.associator_eq_ofEq,
    Stacks.Cohomology.DerivedBaseChangeOfToposHom.derivedPullbackIsoOfTwoIso_ofEq,
    derivedPullbackCongr_hom_app]
  simpa only [eqToHom_refl, NatTrans.id_app, Category.comp_id] using
    derivedPullbackCompComparison_assoc_of_eq f g h _ (RingedToposHom.comp_assoc f g h) rfl M

end Cocycle

end Stacks.Cohomology.DerivedPullbackCompositionOfToposHom

end
