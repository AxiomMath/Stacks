module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackTensorComp
public import StacksFrontier.Algebra.Homology.DerivedCategory.LeftDerivedIsoMapDerivedCategoryOfIsoComp
public import StacksFrontier.Algebra.Homology.HomotopyCategory.ExactFunctorHomology
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.DerivedModuleSystemOfObject
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.DerivedPullbackComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSmallEtaleStrictBridge
public import StacksFrontier.CategoryTheory.Adjunction.ConjugateCompTransfer
public import StacksFrontier.CategoryTheory.Adjunction.ConjugateNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.DerivedPullbackSquarePaste
public import StacksFrontier.CategoryTheory.Sites.Simplicial.RestrictTransitionCoherence

/-!
# The composition comparisons of the transition morphisms, through 2-isomorphisms

For a simplicial-site situation the transition morphisms of ringed topoi compose only up to the
2-isomorphism `f_ψ ∘ f_φ ≅ f_{ψ ≫ φ}` of Stacks 09WE
(`CategoryTheory.SimplicialSiteSituation.transitionRingedToposHomCompTwoIso`). This file
identifies the compositors of pullbacks and of derived pullbacks along transitions with the ones
of Stacks 03D8 and 0D6D for a genuine composite of morphisms of ringed topoi, read through that
2-isomorphism. These identifications are what lets the derived squares of the strict components
of a simplicial algebraic space be pasted by
`Stacks.Cohomology.DerivedBaseChangeOfToposHom.derivedPullbackSquare_paste_hom_app`, which gives
the cocycle condition for those squares.

## Main results

* `AlgebraicGeometry.RingedToposHom.TwoIso.pullbackModulesCompIso_four_symm_eq`: the compositor
  of pullbacks attached to a 2-isomorphism `ψ ∘ φ ≅ χ` is the one of Stacks 03D8 followed by the
  pullback isomorphism of the 2-isomorphism.
* `CategoryTheory.SimplicialSiteSituation.transitionPullbackModulesCompIso_symm_eq`: the case of
  the transition morphisms.
* `CategoryTheory.SimplicialSiteSituation.derivedTransitionCompComparison_app_eq`: the comparison
  `Lf_ψ^* ⋙ Lf_φ^* ⟶ Lf_{ψ ≫ φ}^*` of Stacks 0D6D is the one for `f_ψ ∘ f_φ` followed by the
  derived pullback isomorphism of the 2-isomorphism.

* `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.strictComponentTransitionTwoIso_comp`: the
  squares `f_φ ∘ realize_n ≅ realize_m ∘ X(φ)_{étale}` of the strict components of a simplicial
  algebraic space satisfy the cocycle condition: the square of `ψ ≫ φ` is the horizontal pasting
  of the squares of `ψ` and `φ`.
* `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.strictComponentDerivedTransitionIso_comp`: the
  same cocycle condition for the derived squares
  `Lf_φ^* ⋙ L realize_n^* ≅ L realize_m^* ⋙ L X(φ)^*`.

## References

* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 03D8](https://stacks.math.columbia.edu/tag/03D8)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.DerivedPullbackCompositionOfToposHom
open Stacks.Cohomology.DerivedPushforward (targetQuasiIso pullbackMapHomotopy)

universe u

-- no global `HasDerivedCategory` instance on these categories of sheaves of modules
attribute [local instance] HasDerivedCategory.standard

attribute [local instance]
  Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy

namespace AlgebraicGeometry.RingedToposHom.TwoIso

universe v' u' w

variable {X Y Z : RingedTopos.{v', u', w}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [Y.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [Z.J.HasSheafCompose (forget RingCat.{w})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify Z.J AddCommGrpCat.{w}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

omit [HasWeakSheafify Z.J AddCommGrpCat.{w}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- **The compositor of pullbacks attached to a 2-isomorphism `ρ : ψ ∘ φ ≅ χ`** (the four-field
`Stacks.Sheaves.RingedToposModules.pullbackModulesCompIso` with comparison of direct images
`ρ`) is the compositor `ψ^* ⋙ φ^* ≅ (ψ ∘ φ)^*` of Stacks 03D8 followed by the pullback
isomorphism of `ρ`. -/
theorem pullbackModulesCompIso_four_symm_eq (φ : RingedToposHom X Y) (ψ : RingedToposHom Y Z)
    {χ : RingedToposHom X Z} (ρ : TwoIso (ψ.comp φ) χ)
    (hρ : Stacks.Sheaves.RingedToposModules.fSharpSetComp φ.toModulesHom ψ.toModulesHom ≫
      ρ.e.hom.app (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) =
        Stacks.Sheaves.RingedToposModules.fSharpSet χ.toModulesHom) :
    (Stacks.Sheaves.RingedToposModules.pullbackModulesCompIso φ.toModulesHom ψ.toModulesHom
        χ.toModulesHom ρ.e hρ).symm =
      (RingedToposHom.pullbackModulesCompIso φ ψ).symm ≪≫ ρ.pullbackModulesIso := by
  refine Iso.ext ?_
  rw [Iso.symm_hom, Iso.trans_hom, Iso.symm_hom]
  have hAG := congrArg Iso.inv (RingedToposHom.pullbackModulesCompIso_eq φ ψ)
  refine Eq.trans ?_ (congrArg (· ≫ _) hAG).symm
  -- the four-field adjunctions of Stacks 03D7
  let Aφ := Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules φ.toModulesHom
  let Aψ := Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules ψ.toModulesHom
  let Aχ := Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules χ.toModulesHom
  let Ac := Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules (ψ.comp φ).toModulesHom
  -- the conjugate of the inverse of a comparison of left adjoints
  have hinv : ∀ {A B : Type _} [Category A] [Category B] {L L' : A ⥤ B} {R R' : B ⥤ A}
      (adj : L ⊣ R) (e : R ≅ R') (adj' : L' ⊣ R'),
      conjugateEquiv adj adj' (Adjunction.leftAdjointUniq (adj.ofNatIsoRight e) adj').inv =
        e.hom := fun adj e adj' =>
    congrArg Iso.inv (Iso.ext
      (Stacks.CategoryTheory.conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom
        adj e adj') : conjugateIsoEquiv adj' adj
        (Adjunction.leftAdjointUniq (adj.ofNatIsoRight e) adj') = e.symm)
  have hL := hinv Aχ (Stacks.Sheaves.RingedToposModules.pushforwardModulesCompIso
    φ.toModulesHom ψ.toModulesHom χ.toModulesHom ρ.e hρ).symm (Aψ.comp Aφ)
  have hR2 := hinv Ac (Stacks.Sheaves.RingedToposModules.pushforwardModulesCompIso
    φ.toModulesHom ψ.toModulesHom (ψ.comp φ).toModulesHom
    (RingedToposHom.toModulesHomPushforwardIso φ ψ)
    (RingedToposHom.fSharpSetComp_toModulesHomPushforwardIso φ ψ)).symm (Aψ.comp Aφ)
  have hR1 : conjugateEquiv Aχ Ac ρ.pullbackModulesIso.hom =
      χ.toModulesPushforwardIso.hom ≫ ρ.pushforwardModulesIso.inv ≫
        (ψ.comp φ).toModulesPushforwardIso.inv := by
    have h : χ.toModulesPushforwardIso.inv ≫ conjugateEquiv Aχ Ac ρ.pullbackModulesIso.hom ≫
        (ψ.comp φ).toModulesPushforwardIso.hom = ρ.pushforwardModulesIso.inv :=
      (Stacks.CategoryTheory.conjugateEquiv_ofNatIsoRight Aχ Ac _ _ _).symm.trans
        (RingedToposHom.TwoIso.conjugateEquiv_pullbackModulesIso_hom ρ)
    rw [← h]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
  apply (conjugateEquiv Aχ (Aψ.comp Aφ)).injective
  rw [← conjugateEquiv_comp Aχ Ac (Aψ.comp Aφ)]
  show _ = conjugateEquiv Aχ Ac _ ≫ conjugateEquiv Ac (Aψ.comp Aφ)
    (Adjunction.leftAdjointUniq _ _).inv
  rw [hR1, hR2]
  refine (hL.trans ?_)
  refine NatTrans.ext (funext fun M => ?_)
  apply Stacks.Sheaves.RingedToposModules.hom_ext_moduleSheafFunctor
  simp only [Iso.symm_hom, NatTrans.comp_app, Functor.map_comp,
    RingedToposHom.moduleSheafFunctor_map_toModulesPushforwardIso_hom_app,
    RingedToposHom.moduleSheafFunctor_map_toModulesPushforwardIso_inv_app]
  rfl

end AlgebraicGeometry.RingedToposHom.TwoIso

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})

/-- **The compositor of pullbacks along transition morphisms is the one of Stacks 03D8 read
through the 2-isomorphism `f_ψ ∘ f_φ ≅ f_{ψ ≫ φ}`**: the simplicial compositor
`f_ψ^* ⋙ f_φ^* ≅ f_{ψ ≫ φ}^*` is the compositor `f_ψ^* ⋙ f_φ^* ≅ (f_ψ ∘ f_φ)^*` of a genuine
composite followed by the pullback isomorphism of
`CategoryTheory.SimplicialSiteSituation.transitionRingedToposHomCompTwoIso`. -/
theorem transitionPullbackModulesCompIso_symm_eq {l m n : SimplexCategory} (ψ : l ⟶ m)
    (φ : m ⟶ n) :
    (S.transitionPullbackModulesCompIso O ψ φ).symm =
      (RingedToposHom.pullbackModulesCompIso (S.transitionRingedToposHom O φ)
          (S.transitionRingedToposHom O ψ)).symm ≪≫
        (S.transitionRingedToposHomCompTwoIso O ψ φ).pullbackModulesIso :=
  RingedToposHom.TwoIso.pullbackModulesCompIso_four_symm_eq _ _
    (S.transitionRingedToposHomCompTwoIso O ψ φ) (S.transitionFSharpSetComp O ψ φ)

/-- **The comparison of Stacks 0D6D for transition morphisms is the one for morphisms of ringed
topoi read through the 2-isomorphism `f_ψ ∘ f_φ ≅ f_{ψ ≫ φ}`**: the canonical comparison
`Lf_ψ^* ⋙ Lf_φ^* ⟶ Lf_{ψ ≫ φ}^*` is, at every object, the comparison
`Lf_ψ^* ⋙ Lf_φ^* ⟶ L(f_ψ ∘ f_φ)^*` followed by the derived pullback isomorphism of
`CategoryTheory.SimplicialSiteSituation.transitionRingedToposHomCompTwoIso`. -/
theorem derivedTransitionCompComparison_app_eq {l m n : SimplexCategory} (ψ : l ⟶ m)
    (φ : m ⟶ n) (K : DerivedCategory (S.componentRingedTopos O l).Modules) :
    (S.derivedTransitionCompComparison O ψ φ).app K =
      (derivedPullbackCompComparison (S.transitionRingedToposHom O φ)
          (S.transitionRingedToposHom O ψ)).app K ≫
        (Stacks.Cohomology.DerivedBaseChangeOfToposHom.derivedPullbackIsoOfTwoIso
          (S.transitionRingedToposHomCompTwoIso O ψ φ)).hom.app K := by
  let γ : derivedPullback (X := S.componentRingedTopos O m) (Y := S.componentRingedTopos O l)
        (S.transitionRingedToposHom O ψ) ⋙
      derivedPullback (X := S.componentRingedTopos O n) (Y := S.componentRingedTopos O m)
        (S.transitionRingedToposHom O φ) ⟶
        derivedPullback (X := S.componentRingedTopos O n) (Y := S.componentRingedTopos O l)
          (S.transitionRingedToposHom O (ψ ≫ φ)) :=
    { app := fun K => (S.derivedTransitionCompComparison O ψ φ).app K
      naturality := fun _ _ f => (S.derivedTransitionCompComparison O ψ φ).naturality f }
  have key : γ = derivedPullbackCompComparison (S.transitionRingedToposHom O φ)
          (S.transitionRingedToposHom O ψ) ≫
        (Stacks.Cohomology.DerivedBaseChangeOfToposHom.derivedPullbackIsoOfTwoIso
          (S.transitionRingedToposHomCompTwoIso O ψ φ)).hom := by
    refine Functor.leftDerived_ext (derivedPullback (X := S.componentRingedTopos O n)
        (Y := S.componentRingedTopos O l) (S.transitionRingedToposHom O (ψ ≫ φ)))
      (derivedPullbackComparison (X := S.componentRingedTopos O n)
        (Y := S.componentRingedTopos O l) (S.transitionRingedToposHom O (ψ ≫ φ)))
      (quasiIsoTarget (Y := S.componentRingedTopos O l))
      _ _ _ (NatTrans.ext (funext fun P => ?_))
    rw [NatTrans.comp_app, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerLeft_app,
      NatTrans.comp_app, Category.assoc]
    have hfac : (S.derivedTransitionCompComparison O ψ φ).app (DerivedCategory.Qh.obj P) ≫
        (S.derivedTransitionComparison O (ψ ≫ φ)).app P =
        (S.derivedTransitionCompCounit O ψ φ).app P := by
      simpa only [NatTrans.comp_app, Functor.whiskerLeft_app] using
        NatTrans.congr_app (S.derivedTransitionComp_fac O ψ φ) P
    refine hfac.trans ?_
    have h₂ := Stacks.Cohomology.DerivedBaseChangeOfToposHom.derivedPullbackIsoOfTwoIso_hom_fac
      (S.transitionRingedToposHomCompTwoIso O ψ φ) P
    have h₃ := derivedPullbackCompComparison_app_comp_derivedPullbackComparison_app
      (S.transitionRingedToposHom O φ) (S.transitionRingedToposHom O ψ) P
    have h₄ : (pullbackMapHomotopyCompIso (S.transitionRingedToposHom O φ)
          (S.transitionRingedToposHom O ψ) ≪≫ Stacks.Homology.mapHomotopyCategoryIso
            (S.transitionRingedToposHomCompTwoIso O ψ φ).pullbackModulesIso (ComplexShape.up ℤ)) =
        Functor.mapHomotopyCategoryCompIso (S.transitionPullbackModulesCompIso O ψ φ).symm
          (ComplexShape.up ℤ) := by
      rw [S.transitionPullbackModulesCompIso_symm_eq O ψ φ]
      exact Stacks.Homology.mapHomotopyCategoryCompIso_trans_mapHomotopyCategoryIso _ _ _
    refine Eq.symm ((congrArg (_ ≫ ·) h₂).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ _) h₃).trans ?_)))
    rw [Category.assoc, Category.assoc, ← Functor.map_comp,
      S.derivedTransitionCompCounit_app O ψ φ P]
    exact congrArg (fun t => (derivedPullback (X := S.componentRingedTopos O n)
        (Y := S.componentRingedTopos O m) (S.transitionRingedToposHom O φ)).map
          ((derivedPullbackComparison (S.transitionRingedToposHom O ψ)).app P) ≫
        (derivedPullbackComparison (S.transitionRingedToposHom O φ)).app
          ((pullbackMapHomotopy (S.transitionRingedToposHom O ψ)).obj P) ≫
        DerivedCategory.Qh.map t) (congrArg (fun e => e.hom.app P) h₄)
  exact NatTrans.congr_app key K

end CategoryTheory.SimplicialSiteSituation


namespace AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (X : SimplicialObject (AlgebraicSpaces B S hS))

attribute [local implicit_reducible] AlgebraicGeometry.RingedToposHom.comp MorphismOfTopoi.comp

/-- A morphism out of `F.obj X` is itself precomposed with `𝟙` and `F.map (𝟙 X)`. -/
theorem eq_id_comp_map_id_comp {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D) {X : C}
    {Z : D} (a : F.obj X ⟶ Z) : a = 𝟙 _ ≫ F.map (𝟙 X) ≫ a := by
  simp

/-- For a simplicial object `Y` in any category, `Y(φ) ∘ Y(ψ) = Y(ψ ≫ φ)`, in the order of
composition of morphisms of the category. -/
theorem _root_.CategoryTheory.SimplicialObject.map_op_comp_map_op {C : Type*} [Category* C]
    (Y : SimplicialObject C) {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    Y.map φ.op ≫ Y.map ψ.op = Y.map (ψ ≫ φ).op := by
  rw [op_comp, Y.map_comp]

/-- Transport along an equality `t = t'` of the base change of `W`, followed by the first
projection for `t'`, is the first projection for `t`. -/
theorem spacesBaseChange_eqToHom_hom_left_fst {Y Z : AlgebraicSpaces B S hS} {t t' : Y ⟶ Z}
    (h : t = t') (W : SpacesEtale B S hS Z) :
    (eqToHom (congrArg (fun t => (spacesBaseChange B S hS t).functor.obj W) h)).hom.left ≫
        pullback.fst W.1.hom t' = pullback.fst W.1.hom t := by
  subst h
  exact Category.id_comp _

/-- The inverse of the composition isomorphism of base changes of Stacks 03G2, followed by the
two first projections, is the first projection of the base change along the composite. -/
theorem spacesBaseChange_comp_inv_app_hom_left_fst_fst {Y Y' Z : AlgebraicSpaces B S hS}
    (f : Y ⟶ Y') (g : Y' ⟶ Z) (W : SpacesEtale B S hS Z) :
    ((spacesBaseChange_comp B S hS f g).inv.app W).hom.left ≫
        pullback.fst (pullback.snd W.1.hom g) f ≫ pullback.fst W.1.hom g =
      pullback.fst W.1.hom (f ≫ g) := by
  have hp : ((spacesBaseChange_comp B S hS f g).hom.app W).hom.left ≫
      pullback.fst W.1.hom (f ≫ g) = pullback.fst (pullback.snd W.1.hom g) f ≫
        pullback.fst W.1.hom g := spacesBaseChange_comp_projection B S hS f g W
  have e : ((spacesBaseChange_comp B S hS f g).inv.app W).hom.left ≫
      ((spacesBaseChange_comp B S hS f g).hom.app W).hom.left = 𝟙 _ :=
    congrArg (fun k => k.hom.left) ((spacesBaseChange_comp B S hS f g).inv_hom_id_app W)
  exact (congrArg (((spacesBaseChange_comp B S hS f g).inv.app W).hom.left ≫ ·) hp.symm).trans
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ pullback.fst W.1.hom (f ≫ g)) e).trans
      (Category.id_comp _)))

/-- A chase of five commutative triangles and squares, with every morphism a variable. -/
theorem comp_four_chase {C : Type*} [Category* C] {A A' A'' D E P R R' Q : C}
    (k₅ : A ⟶ A') (k₄ : A' ⟶ A'') (k₃ : A'' ⟶ D) (k₂ : D ⟶ E) (p : E ⟶ R) (q : D ⟶ R')
    (r : R' ⟶ R) (q' : A'' ⟶ Q) (s : Q ⟶ R') (w : Q ⟶ P) (v : P ⟶ R) (w' : A' ⟶ P)
    (w'' : A ⟶ P) (h₂ : k₂ ≫ p = q ≫ r) (h₃ : k₃ ≫ q = q' ≫ s) (h₃' : s ≫ r = w ≫ v)
    (h₄ : k₄ ≫ q' ≫ w = w') (h₅ : k₅ ≫ w' = w'') :
    (k₅ ≫ k₄ ≫ k₃ ≫ k₂) ≫ p = w'' ≫ v := by
  rw [Category.assoc, Category.assoc, Category.assoc, h₂, reassoc_of% h₃, h₃', ← h₅,
    ← h₄]
  simp only [Category.assoc]

/-- **The comparisons of iterated base changes of the strict objects compose**: the comparison
`V ×_{X_k} X_l ×_{X_l} X_n ≅ V ×_{X_k} X_n` for `ψ ≫ φ` is the one for `ψ` base changed along
`X(φ)`, followed by the one for `φ`, after the composition isomorphism of base changes of
Stacks 03G2. -/
theorem StrictObj.transitionRealizeIso_comp_inv {l m n : SimplexCategory} (ψ : l ⟶ m)
    (φ : m ⟶ n) (x : StrictObj X l) :
    eqToHom (congrArg (fun t => (spacesBaseChange B S hS t).functor.obj x.realize)
        (SimplicialObject.map_op_comp_map_op X ψ φ).symm) ≫
      (spacesBaseChange_comp B S hS (X.map φ.op) (X.map ψ.op)).inv.app x.realize ≫
        (spacesBaseChange B S hS (X.map φ.op)).functor.map
            (StrictObj.transitionRealizeIso ψ x).inv ≫
          (StrictObj.transitionRealizeIso φ (x.transition ψ)).inv =
      (StrictObj.transitionRealizeIso (ψ ≫ φ) x).inv := by
  refine ObjectProperty.hom_ext _ (Over.OverMorphism.ext (pullback.hom_ext ?_ ?_))
  · have h₂ : (StrictObj.transitionRealizeIso φ (x.transition ψ)).inv.hom.left ≫
        pullback.fst x.obj.1.hom (X.map ((x.simplex ≫ ψ) ≫ φ).op) =
          pullback.fst _ _ ≫ pullback.fst _ _ := StrictObj.transitionRealizeInv_fst φ _
    have h₃ := spacesBaseChange_map_fst (X.map φ.op) (StrictObj.transitionRealizeIso ψ x).inv
    have h₃' : (StrictObj.transitionRealizeIso ψ x).inv.hom.left ≫
        pullback.fst x.obj.1.hom (X.map (x.simplex ≫ ψ).op) =
          pullback.fst _ _ ≫ pullback.fst _ _ := StrictObj.transitionRealizeInv_fst ψ x
    have hL : (StrictObj.transitionRealizeIso (ψ ≫ φ) x).inv.hom.left ≫
        pullback.fst x.obj.1.hom (X.map (x.simplex ≫ ψ ≫ φ).op) =
          pullback.fst _ _ ≫ pullback.fst _ _ := StrictObj.transitionRealizeInv_fst (ψ ≫ φ) x
    exact (comp_four_chase _ _ _ _ _ _ _ _ _ _ _ _ _ h₂ h₃ h₃'
      (spacesBaseChange_comp_inv_app_hom_left_fst_fst (X.map φ.op) (X.map ψ.op) x.realize)
      (spacesBaseChange_eqToHom_hom_left_fst (SimplicialObject.map_op_comp_map_op X ψ φ).symm
        x.realize)).trans
        hL.symm
  · exact (Over.w _).trans (Over.w (StrictObj.transitionRealizeIso (ψ ≫ φ) x).inv.hom).symm

/-- The components of `strictComponentTransitionTwoIso` are restriction maps along the inverse
comparisons of iterated base changes. -/
theorem strictComponentTransitionTwoIso_e_hom_app_hom_app {m n : SimplexCategory} (φ : m ⟶ n)
    (G : Sheaf (SpacesEtale.topology B S hS (X.obj (op n))) (Type (u + 1)))
    (V : ((strictSituation X).component m)ᵒᵖ) :
    ((strictComponentTransitionTwoIso X φ).e.hom.app G).hom.app V =
      G.obj.map (StrictObj.transitionRealizeIso φ V.unop).inv.op :=
  rfl

/-- A contravariant functor applied to a component of the transport along an equality of
functors is the transport along the induced equality of values. -/
theorem map_op_eqToHom_app {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (F : Cᵒᵖ ⥤ E) {A A' : D ⥤ C} (h : A = A') (x : D) :
    F.map ((eqToHom h).app x).op =
      eqToHom (congrArg (fun y => F.obj (op y)) (Functor.congr_obj h x).symm) := by
  subst h
  simp

/-- The components of the compositor `f_ψ ∘ f_φ ≅ f_{ψ ≫ φ}` of the strict components are
identities, the transition functors composing on the nose. -/
theorem strictTransitionRingedToposHomCompTwoIso_e_inv_app_hom_app {l m n : SimplexCategory}
    (ψ : l ⟶ m) (φ : m ⟶ n)
    (M : ((strictSituation X).componentRingedTopos (strictStructureSheaf X) n).Topos)
    (V : ((strictSituation X).componentRingedTopos (strictStructureSheaf X) l).Cᵒᵖ) :
    (((strictSituation X).transitionRingedToposHomCompTwoIso (strictStructureSheaf X)
        ψ φ).e.inv.app M).hom.app V = 𝟙 _ := by
  have h : (((strictSituation X).transitionRingedToposHomCompTwoIso (strictStructureSheaf X)
      ψ φ).e.hom.app M).hom.app V = 𝟙 _ := by
    refine (SimplicialSiteSituation.pushforwardCompSymm_inl_hom_app_hom_app
      (strictSimplicialSite X) ψ φ M V).trans ?_
    rw [eqToIso.inv]
    exact (map_op_eqToHom_app M.obj _ _).trans (eqToHom_refl _ _)
  have h' := congrArg (fun k => k.hom.app V)
    ((((strictSituation X).transitionRingedToposHomCompTwoIso (strictStructureSheaf X)
      ψ φ).e.inv_hom_id_app M))
  exact ((Category.comp_id _).symm.trans ((congrArg (_ ≫ ·) h.symm).trans h'))

/-- The square of `φ`, on direct images and then along the transition of `ψ`, is restriction
along the inverse comparison of iterated base changes at the transported object. -/
theorem strictTransitionPushforward_map_strictComponentTransitionTwoIso_e_hom_app_hom_app
    {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
    (G : (spacesEtaleRingedTopos B S hS (X.obj (op n))).Topos)
    (V : ((strictSituation X).componentRingedTopos (strictStructureSheaf X) l).Cᵒᵖ) :
    (((strictSituation X).transitionRingedToposHom (strictStructureSheaf X)
        ψ).toToposHom.pushforward.map ((strictComponentTransitionTwoIso X φ).e.hom.app G)).hom.app
        V =
      G.obj.map (StrictObj.transitionRealizeIso φ (V.unop.transition ψ)).inv.op :=
  rfl

/-- The square of `ψ` at the direct image along `X(φ)_{étale}` is restriction along the base
change along `X(φ)` of the inverse comparison of iterated base changes. -/
theorem strictComponentTransitionTwoIso_e_hom_app_pushforward_hom_app
    {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
    (G : (spacesEtaleRingedTopos B S hS (X.obj (op n))).Topos)
    (V : ((strictSituation X).componentRingedTopos (strictStructureSheaf X) l).Cᵒᵖ) :
    ((strictComponentTransitionTwoIso X ψ).e.hom.app
        ((spacesEtaleRingedToposHom (X.map φ.op)).toToposHom.pushforward.obj G)).hom.app V =
      G.obj.map ((spacesBaseChange B S hS (X.map φ.op)).functor.map
        (StrictObj.transitionRealizeIso ψ V.unop).inv).op :=
  rfl

/-- The transport of `(t)_{étale}` to `(t')_{étale}` along an equality `t = t'`, on direct
images and then restricted to a strict component, is restriction along the transport of base
changes. -/
theorem strictComponentRingedToposHom_pushforward_map_ofEq_hom_app {l n : SimplexCategory}
    {t t' : X.obj (op n) ⟶ X.obj (op l)} (h : t = t')
    (G : (spacesEtaleRingedTopos B S hS (X.obj (op n))).Topos)
    (V : ((strictSituation X).componentRingedTopos (strictStructureSheaf X) l).Cᵒᵖ) :
    ((strictComponentRingedToposHom X l).toToposHom.pushforward.map
        ((RingedToposHom.TwoIso.ofEq.{u + 1, u + 1, u + 1, u + 1, u + 1, u + 1}
          (congrArg spacesEtaleRingedToposHom h)).e.hom.app G)).hom.app V =
      G.obj.map (eqToHom (congrArg (fun t => (spacesBaseChange B S hS t).functor.obj
        ((componentRealize X l).obj V.unop)) h.symm)).op := by
  subst h
  simp only [RingedToposHom.TwoIso.ofEq_rfl, RingedToposHom.TwoIso.refl, Iso.refl_hom,
    NatTrans.id_app, CategoryTheory.Functor.map_id, ObjectProperty.FullSubcategory.id_hom,
    eqToHom_refl, op_id]
  rfl

/-- The compositor `X(ψ)_{étale} ∘ X(φ)_{étale} ≅ (X(φ) ≫ X(ψ))_{étale}`, on direct images and
then restricted to a strict component, is restriction along the composition isomorphism of base
changes of Stacks 03G2. -/
theorem strictComponentRingedToposHom_pushforward_map_spacesEtaleCompTwoIso_inv_app
    {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
    (G : (spacesEtaleRingedTopos B S hS (X.obj (op n))).Topos)
    (V : ((strictSituation X).componentRingedTopos (strictStructureSheaf X) l).Cᵒᵖ) :
    ((strictComponentRingedToposHom X l).toToposHom.pushforward.map
        ((spacesEtaleRingedToposHomCompTwoIsoSpacesEtaleRingedToposHomComp (X.map φ.op)
          (X.map ψ.op)).e.inv.app G)).hom.app V =
      G.obj.map ((spacesBaseChange_comp B S hS (X.map φ.op) (X.map ψ.op)).inv.app
        ((componentRealize X l).obj V.unop)).op :=
  rfl

/-- **The 2-isomorphisms of the strict components satisfy the cocycle condition**: the square of
`ψ ≫ φ` is the horizontal pasting of the squares of `ψ` and `φ`, conjugated by the
2-isomorphisms `f_ψ ∘ f_φ ≅ f_{ψ ≫ φ}` of the transitions and
`X(ψ)_{étale} ∘ X(φ)_{étale} ≅ X(ψ ≫ φ)_{étale}` of the spaces-étale ringed topoi. -/
theorem strictComponentTransitionTwoIso_comp {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    strictComponentTransitionTwoIso X (ψ ≫ φ) =
      (((strictSituation X).transitionRingedToposHomCompTwoIso (strictStructureSheaf X)
          ψ φ).symm.whiskerLeft (strictComponentRingedToposHom X n)).trans
        ((RingedToposHom.TwoIso.pasteHorizontal (strictComponentTransitionTwoIso X ψ)
          (strictComponentTransitionTwoIso X φ)).trans
        (((spacesEtaleRingedToposHomCompTwoIsoSpacesEtaleRingedToposHomComp (X.map φ.op)
            (X.map ψ.op)).symm.trans
          (RingedToposHom.TwoIso.ofEq.{u + 1, u + 1, u + 1, u + 1, u + 1, u + 1}
            (congrArg spacesEtaleRingedToposHom
              (SimplicialObject.map_op_comp_map_op X ψ φ)))).whiskerRight
          (strictComponentRingedToposHom X l))) := by
  apply RingedToposHom.TwoIso.ext
  refine Iso.ext (NatTrans.ext (funext fun G => ?_))
  refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun V => ?_))
  dsimp only [RingedToposHom.TwoIso.trans, RingedToposHom.TwoIso.symm,
    RingedToposHom.TwoIso.whiskerLeft, RingedToposHom.TwoIso.whiskerRight,
    RingedToposHom.TwoIso.pasteHorizontal, RingedToposHom.TwoIso.associator, Iso.trans_hom,
    Iso.symm_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, ObjectProperty.FullSubcategory.comp_hom,
    Functor.associator_hom_app, Functor.associator_inv_app]
  have h1 := strictComponentTransitionTwoIso_e_hom_app_hom_app X (ψ ≫ φ) G V
  have h2 := strictTransitionRingedToposHomCompTwoIso_e_inv_app_hom_app X ψ φ
    ((strictComponentRingedToposHom X n).toToposHom.pushforward.obj G) V
  have h3 := strictTransitionPushforward_map_strictComponentTransitionTwoIso_e_hom_app_hom_app
    X ψ φ G V
  have h4 := strictComponentTransitionTwoIso_e_hom_app_pushforward_hom_app X ψ φ G V
  have h6 := strictComponentRingedToposHom_pushforward_map_spacesEtaleCompTwoIso_inv_app X ψ φ G V
  have h7 := strictComponentRingedToposHom_pushforward_map_ofEq_hom_app X
    (SimplicialObject.map_op_comp_map_op X ψ φ) G V
  have hg := congrArg (fun k => G.obj.map (Quiver.Hom.op k))
    (StrictObj.transitionRealizeIso_comp_inv X ψ φ V.unop)
  simp only [h1, h2, h3, h4, Functor.map_comp, ObjectProperty.FullSubcategory.comp_hom,
    NatTrans.comp_app, h6, h7, ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app]
  refine hg.symm.trans ?_
  simp only [op_comp, Functor.map_comp]
  rfl

/-- **The cocycle condition for the derived squares of the strict components.** For simplex
maps `ψ : [l] ⟶ [m]` and `φ : [m] ⟶ [n]`, the derived square of `ψ ≫ φ`,
`Lf_{ψ ≫ φ}^* ⋙ L realize_n^* ≅ L realize_l^* ⋙ L X(ψ ≫ φ)^*`, precomposed with the composition
comparison `Lf_ψ^* ⋙ Lf_φ^* ⟶ Lf_{ψ ≫ φ}^*` of Stacks 0D6D, is the derived square of `φ` at
`Lf_ψ^*`, followed by `L X(φ)^*` of the derived square of `ψ` and by the composition isomorphism
`L X(ψ)^* ⋙ L X(φ)^* ≅ L (X(φ) ≫ X(ψ))^* = L X(ψ ≫ φ)^*` of
`spacesEtaleDerivedPullbackCompIsoSpacesEtaleRingedToposHomComp`. -/
theorem strictComponentDerivedTransitionIso_comp {l m n : SimplexCategory} (ψ : l ⟶ m)
    (φ : m ⟶ n)
    (K : DerivedCategory
      ((strictSituation X).componentRingedTopos (strictStructureSheaf X) l).Modules) :
    (derivedPullback (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
        (Y := (strictSituation X).componentRingedTopos (strictStructureSheaf X) n)
        (strictComponentRingedToposHom X n)).map
        (((strictSituation X).derivedTransitionCompComparison (strictStructureSheaf X) ψ φ).app K) ≫
      (strictComponentDerivedTransitionIso X (ψ ≫ φ)).hom.app K =
    (strictComponentDerivedTransitionIso X φ).hom.app
        (((strictSituation X).derivedTransitionPullback (strictStructureSheaf X) ψ).obj K) ≫
      (derivedPullback (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
          (Y := spacesEtaleRingedTopos B S hS (X.obj (op m)))
          (spacesEtaleRingedToposHom (X.map φ.op))).map
        ((strictComponentDerivedTransitionIso X ψ).hom.app K) ≫
      (spacesEtaleDerivedPullbackCompIsoSpacesEtaleRingedToposHomComp (X.map φ.op)
          (X.map ψ.op)).hom.app
        ((derivedPullback (X := spacesEtaleRingedTopos B S hS (X.obj (op l)))
          (Y := (strictSituation X).componentRingedTopos (strictStructureSheaf X) l)
          (strictComponentRingedToposHom X l)).obj K) ≫
      (Stacks.Cohomology.DerivedBaseChangeOfToposHom.derivedPullbackCongr
          (congrArg spacesEtaleRingedToposHom (SimplicialObject.map_op_comp_map_op X ψ φ))).hom.app
        ((derivedPullback (X := spacesEtaleRingedTopos B S hS (X.obj (op l)))
          (Y := (strictSituation X).componentRingedTopos (strictStructureSheaf X) l)
          (strictComponentRingedToposHom X l)).obj K) :=
  Stacks.Cohomology.DerivedBaseChangeOfToposHom.derivedPullbackSquare_paste_hom_app
    (strictComponentRingedToposHom X n) (strictComponentRingedToposHom X m)
    (strictComponentRingedToposHom X l)
    ((strictSituation X).transitionRingedToposHom (strictStructureSheaf X) φ)
    ((strictSituation X).transitionRingedToposHom (strictStructureSheaf X) ψ)
    ((strictSituation X).transitionRingedToposHom (strictStructureSheaf X) (ψ ≫ φ))
    (spacesEtaleRingedToposHom (X.map φ.op)) (spacesEtaleRingedToposHom (X.map ψ.op))
    (spacesEtaleRingedToposHom (X.map (ψ ≫ φ).op))
    ((strictSituation X).derivedTransitionPullbackIsoDerivedPullbackSimplicialSmallEtaleStrictBridge
      (strictStructureSheaf X) φ)
    ((strictSituation X).derivedTransitionPullbackIsoDerivedPullbackSimplicialSmallEtaleStrictBridge
      (strictStructureSheaf X) ψ)
    ((strictSituation X).derivedTransitionPullbackIsoDerivedPullbackSimplicialSmallEtaleStrictBridge
      (strictStructureSheaf X) (ψ ≫ φ))
    ((strictSituation X).derivedTransitionCompComparison (strictStructureSheaf X) ψ φ)
    (strictComponentTransitionTwoIso X φ) (strictComponentTransitionTwoIso X ψ)
    (strictComponentTransitionTwoIso X (ψ ≫ φ))
    ((strictSituation X).transitionRingedToposHomCompTwoIso (strictStructureSheaf X) ψ φ)
    (spacesEtaleRingedToposHomCompTwoIsoSpacesEtaleRingedToposHomComp (X.map φ.op) (X.map ψ.op))
    (congrArg spacesEtaleRingedToposHom (SimplicialObject.map_op_comp_map_op X ψ φ))
    (fun K' => by
      simp only [SimplicialSiteSituation.derivedTransitionPullbackIsoDerivedPullbackSimplicialSmallEtaleStrictBridge,
        Iso.refl_hom, NatTrans.id_app]
      refine (Category.comp_id _).trans (((strictSituation X).derivedTransitionCompComparison_app_eq
        (strictStructureSheaf X) ψ φ K').trans ?_)
      exact eq_id_comp_map_id_comp (derivedPullback
        (X := (strictSituation X).componentRingedTopos (strictStructureSheaf X) n)
        (Y := (strictSituation X).componentRingedTopos (strictStructureSheaf X) m)
        ((strictSituation X).transitionRingedToposHom (strictStructureSheaf X) φ)) _)
    (strictComponentTransitionTwoIso_comp X ψ φ) K

end AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

end
