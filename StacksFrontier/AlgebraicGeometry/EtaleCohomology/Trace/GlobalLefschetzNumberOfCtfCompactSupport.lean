module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GlobalSectionsEndomorphismComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleRestrictScalarsDerived

/-!
# The global Lefschetz number as the compactly supported one of the trivial compactification

Let `Y` be a scheme over a finite field `k` and `C` a bounded below complex of sheaves of
`Λ`-modules on `Y_étale`.  There are two constructions of the action `π_Y^*` on
`RΓ(Y_k̄, C|_{Y_k̄})`:

* `Stacks.EtaleCohomology.frobeniusGlobalSectionsEndo`, on `D⁺(Y_étale)`, underlying the global
  Lefschetz number of [Stacks, Tag 03TX];
* `Stacks.EtaleCohomology.frobeniusRestrictionCohomologyEndo`, on complexes, computing
  `RΓ(Y_k̄, -)` as `RΓ(Spec k̄, Rf_*(-))`, underlying the canonical compactly supported Lefschetz
  number.

This file shows that they are the same endomorphism up to the canonical identifications, so that
the two traces agree.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

section Frobenius

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

variable (Λ : Type r) [Ring Λ] {k : Type u} [Field k] [Fintype k] (Y : Over (Spec (.of k)))
  (kbar : Type u) [Field kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ q)

/-- The bounded below form of `mapHomotopyCategoryFactors` is the identity: the forward half. -/
private theorem mapHomotopyCategoryPlusFactors_hom_app {A B : Type*} [Category* A] [Category* B]
    [Preadditive A] [Preadditive B] (F : A ⥤ B) [F.Additive] (K : CochainComplex.Plus A) :
    (Stacks.AlgebraicGeometry.Tag01XLDerivedIso.mapHomotopyCategoryPlusFactors F).hom.app K =
      𝟙 _ := by
  apply (HomotopyCategory.Plus.ι _).map_injective
  exact ((HomotopyCategory.Plus.ι _).map_preimage _).trans rfl

/-- Cancellation of two inverse pairs in a composite. -/
private lemma cancel_two_inverses {𝒞 : Type*} [Category* 𝒞] {X Y Z W : 𝒞} (a : X ⟶ Y)
    (b : Y ⟶ Z) (c : Z ⟶ Y) (d : Y ⟶ X) (e : X ⟶ W) (hbc : b ≫ c = 𝟙 Y) (had : a ≫ d = 𝟙 X) :
    a ≫ b ≫ c ≫ d ≫ e = e := by
  rw [reassoc_of% hbc, reassoc_of% had]

/-- Reassociating a composite and substituting `f1 ≫ f2 ≫ f3 = r` and `q' ≫ qt ≫ q2 = t`. -/
private lemma assemble_frobenius {𝒞 : Type*} [Category* 𝒞] {A B C C' D D' E G H I : 𝒞}
    (x : A ⟶ B) (y : B ⟶ C) (t : C ⟶ D) (uu : D ⟶ E) (f1 : E ⟶ G) (f2 : G ⟶ H) (f3 : H ⟶ I)
    (r : E ⟶ I) (q' : C ⟶ C') (qt : C' ⟶ D') (q2 : D' ⟶ D)
    (h1 : f1 ≫ f2 ≫ f3 = r) (h2 : q' ≫ qt ≫ q2 = t) :
    (x ≫ (y ≫ (t ≫ uu) ≫ f1) ≫ f2) ≫ f3 = (x ≫ y ≫ q') ≫ qt ≫ q2 ≫ uu ≫ r := by
  simp only [Category.assoc]
  rw [h1, ← h2]
  simp only [Category.assoc]

/-- **The canonical morphism of `D⁺` agrees with the one on complexes.**  On the class of a bounded
below complex `C`, the canonical morphism `C|_{Y_k̄} ⟶ Rπ̄_*(C|_{Y_k̄})` of
`Stacks.EtaleCohomology.frobeniusBaseChangeDerivedMap` is
`Stacks.EtaleCohomology.frobeniusRestrictionDerivedMap`, under the identification of the derived
restriction of `Q(C)` with the class of the degreewise restriction of `C`. -/
theorem frobeniusBaseChangeDerivedMap_app_Q
    (C : CochainComplex.Plus (EtaleModules.{u, r} Λ Y.left)) :
    (frobeniusBaseChangeDerivedMap.{u, r} Λ Y kbar p q hcard).app (DerivedCategory.Plus.Q.obj C) ≫
        (etaleModuleDerivedDirectImage.{u, r} Λ (geometricFrobeniusBaseChange Y kbar p q hcard)).map
          ((Functor.mapDerivedCategoryPlusQIso
            (etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar))).hom.app C) =
      (Functor.mapDerivedCategoryPlusQIso
          (etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar))).hom.app C ≫
        frobeniusRestrictionDerivedMap.{u, r} Λ Y kbar p q hcard C := by
  let i := etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)
  let P := etaleModuleDirectImage.{u, r} Λ (geometricFrobeniusBaseChange Y kbar p q hcard)
  let X₀ := (HomotopyCategory.Plus.quotient _).obj C
  let qC := (DerivedCategory.Plus.quotientCompQhIso (EtaleModules.{u, r} Λ Y.left)).app C
  let q' := (DerivedCategory.Plus.quotientCompQhIso _).app (i.mapCochainComplexPlus.obj C)
  let q₂ := (DerivedCategory.Plus.quotientCompQhIso _).app
    (P.mapCochainComplexPlus.obj (i.mapCochainComplexPlus.obj C))
  have hι : (Functor.mapDerivedCategoryPlusQIso i).hom.app C =
      i.mapDerivedCategoryPlus.map qC.inv ≫ i.mapDerivedCategoryPlusFactorsh.hom.app X₀ ≫
        q'.hom := by
    simp only [Functor.mapDerivedCategoryPlusQIso, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Iso.symm_hom, Functor.associator_hom_app,
      Functor.associator_inv_app, Category.id_comp, mapHomotopyCategoryPlusFactors_hom_app]
    exact whisker_eq _ (whisker_eq _ ((eq_whisker (DerivedCategory.Plus.Qh.map_id _) _).trans
      (Category.id_comp _)))
  let tw : i.mapCochainComplexPlus.obj C ⟶
      P.mapCochainComplexPlus.obj (i.mapCochainComplexPlus.obj C) :=
    ObjectProperty.homMk (X := i.mapCochainComplexPlus.obj C)
      (Y := P.mapCochainComplexPlus.obj (i.mapCochainComplexPlus.obj C))
      ((NatTrans.mapHomologicalComplex (frobeniusBaseChangeTwist.{u, r} Λ Y kbar p q hcard)
        (ComplexShape.up ℤ)).app C.obj)
  let F := fieldBaseChangeDerivedRestriction.{u, r} Λ Y kbar
  let RP := etaleModuleDerivedDirectImage.{u, r} Λ (geometricFrobeniusBaseChange Y kbar p q hcard)
  let m := frobeniusBaseChangeDerivedMap.{u, r} Λ Y kbar p q hcard
  have hnat : F.map qC.hom ≫ m.app (DerivedCategory.Plus.Q.obj C) =
      m.app (DerivedCategory.Plus.Qh.obj X₀) ≫ RP.map (F.map qC.hom) := m.naturality qC.hom
  have hmQ : m.app (DerivedCategory.Plus.Q.obj C) =
      F.map qC.inv ≫ m.app (DerivedCategory.Plus.Qh.obj X₀) ≫ RP.map (F.map qC.hom) := by
    rw [← hnat, ← Category.assoc, ← F.map_comp, Iso.inv_hom_id, F.map_id, Category.id_comp]
  have hτ : (Functor.mapHomotopyCategoryPlusNatTrans
        (frobeniusBaseChangeTwist.{u, r} Λ Y kbar p q hcard)).app X₀ ≫
      (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (i ⋙ P))).inv.app X₀ =
      (HomotopyCategory.Plus.quotient _).map tw := by
    ext
    rfl
  have hH : (frobeniusBaseChangeHomotopyMap.{u, r} Λ Y kbar p q hcard).app X₀ =
      DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.quotient _).map tw) ≫
        P.rightDerivedFunctorPlusUnith.app (i.mapHomotopyCategoryPlus.obj X₀) := by
    rw [← hτ]
    simp only [frobeniusBaseChangeHomotopyMap, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id]
    rfl
  have hq : q'.hom ≫ DerivedCategory.Plus.Q.map tw ≫ q₂.inv =
      DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.quotient _).map tw) := by
    have := (DerivedCategory.Plus.quotientCompQhIso _).hom.naturality tw
    dsimp only [Functor.comp_map] at this
    rw [← Category.assoc, Iso.comp_inv_eq]
    exact this.symm
  have hm := frobeniusBaseChangeDerivedMap_app_Qh.{u, r} Λ Y kbar p q hcard X₀
  have hD : frobeniusRestrictionDerivedMap.{u, r} Λ Y kbar p q hcard C =
      DerivedCategory.Plus.Q.map tw ≫ q₂.inv ≫
        P.rightDerivedFunctorPlusUnith.app
          ((HomotopyCategory.Plus.quotient _).obj (i.mapCochainComplexPlus.obj C)) ≫
        RP.map q'.hom := rfl
  rw [hmQ, hm, hι, hD, hH]
  have hc : RP.map (i.mapDerivedCategoryPlusFactorsh.inv.app X₀) ≫ RP.map (F.map qC.hom) ≫
      RP.map (i.mapDerivedCategoryPlus.map qC.inv ≫ i.mapDerivedCategoryPlusFactorsh.hom.app X₀ ≫
        q'.hom) = RP.map q'.hom := by
    rw [← RP.map_comp, ← RP.map_comp]
    exact congrArg RP.map (cancel_two_inverses _ _ _ _ _ (F.mapIso qC).hom_inv_id
      (i.mapDerivedCategoryPlusFactorsh.inv_hom_id_app X₀))
  exact assemble_frobenius _ _ _ _ _ _ _ _ _ _ _ hc hq

/-- Pasting the image under `G` of a commutative square with two commutative squares in `𝒟`. -/
private lemma square_of_models {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟] (G : 𝒞 ⥤ 𝒟)
    {A B A' B' : 𝒞} {Z : 𝒟} (m : A ⟶ B) (rpι : B ⟶ B') (ι : A ⟶ A') (m' : A' ⟶ B')
    (hF : m ≫ rpι = ι ≫ m') (ga : G.obj B ⟶ G.obj A) (gb : G.obj B' ⟶ G.obj A')
    (hn : G.map rpι ≫ gb = ga ≫ G.map ι) (gs : G.obj A' ⟶ Z) (endo : Z ⟶ Z)
    (hE : gs ≫ endo = (G.map m' ≫ gb) ≫ gs) :
    (G.map m ≫ ga) ≫ G.map ι ≫ gs = (G.map ι ≫ gs) ≫ endo :=
  calc (G.map m ≫ ga) ≫ G.map ι ≫ gs = G.map m ≫ (ga ≫ G.map ι) ≫ gs := by
        simp only [Category.assoc]
    _ = G.map m ≫ (G.map rpι ≫ gb) ≫ gs := by rw [hn]
    _ = G.map (m ≫ rpι) ≫ gb ≫ gs := by simp only [G.map_comp, Category.assoc]
    _ = G.map (ι ≫ m') ≫ gb ≫ gs := by rw [hF]
    _ = G.map ι ≫ ((G.map m' ≫ gb) ≫ gs) := by simp only [G.map_comp, Category.assoc]
    _ = (G.map ι ≫ gs) ≫ endo := by rw [← hE, Category.assoc]

/-- The comparison `RΓ(Y_k̄, Q(C)|_{Y_k̄}) ≅ RΓ(Spec k̄, Rf_*(C|_{Y_k̄}))` of the two models of the
cohomology of `C` on `Y_k̄`: the identification of the derived restriction of `Q(C)` with the class
of the degreewise restriction, followed by `RΓ(Y_k̄, -) ≅ RΓ(Spec k̄, Rf_*(-))`. -/
def frobeniusCohomologyModelsIso (C : CochainComplex.Plus (EtaleModules.{u, r} Λ Y.left)) :
    (etaleModuleDerivedGlobalSections.{u, r} Λ (fieldBaseChange Y kbar)).obj
        ((fieldBaseChangeDerivedRestriction.{u, r} Λ Y kbar).obj (DerivedCategory.Plus.Q.obj C)) ≅
      (etaleModuleDerivedGlobalSections.{u, r} Λ (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, r} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, r} Λ Y kbar C)) :=
  (etaleModuleDerivedGlobalSections.{u, r} Λ (fieldBaseChange Y kbar)).mapIso
      ((Functor.mapDerivedCategoryPlusQIso
        (etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar))).app C) ≪≫
    (etaleModuleDerivedGlobalSectionsCompIso.{u, r} Λ
      (pullback.snd Y.hom (specAlgebraMap k kbar))).app
        (fieldBaseChangeRestriction.{u, r} Λ Y kbar C)

/-- **The two models of `π_Y^*` agree.**  The comparison
`Stacks.EtaleCohomology.frobeniusCohomologyModelsIso` intertwines the action
`Stacks.EtaleCohomology.frobeniusGlobalSectionsEndo` of [Stacks, Tag 03TX] on
`RΓ(Y_k̄, Q(C)|_{Y_k̄})` with `Stacks.EtaleCohomology.frobeniusRestrictionCohomologyEndo` on
`RΓ(Spec k̄, Rf_*(C|_{Y_k̄}))`. -/
theorem frobeniusGlobalSectionsEndo_comp_frobeniusCohomologyModelsIso_hom
    (C : CochainComplex.Plus (EtaleModules.{u, r} Λ Y.left)) :
    frobeniusGlobalSectionsEndo.{u, r} Λ Y kbar p q hcard (DerivedCategory.Plus.Q.obj C) ≫
        (frobeniusCohomologyModelsIso.{u, r} Λ Y kbar C).hom =
      (frobeniusCohomologyModelsIso.{u, r} Λ Y kbar C).hom ≫
        frobeniusRestrictionCohomologyEndo.{u, r} Λ Y kbar p q hcard C := by
  let s := pullback.snd Y.hom (specAlgebraMap k kbar)
  let π := geometricFrobeniusBaseChange Y kbar p q hcard
  let hπ := geometricFrobeniusBaseChange_comp_toBase Y kbar p q hcard
  let ι := (Functor.mapDerivedCategoryPlusQIso
    (etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar))).app C
  let RΓ := etaleModuleDerivedGlobalSections.{u, r} Λ (fieldBaseChange Y kbar)
  let gπ := etaleModuleDerivedGlobalSectionsCompIso.{u, r} Λ π
  let gs := etaleModuleDerivedGlobalSectionsCompIso.{u, r} Λ s
  have hE := etaleModuleDerivedGlobalSectionsCompIso_comm_endomorphism Λ π s hπ
    (frobeniusRestrictionDerivedMap.{u, r} Λ Y kbar p q hcard C)
  have hF := frobeniusBaseChangeDerivedMap_app_Q Λ Y kbar p q hcard C
  have hn : RΓ.map ((etaleModuleDerivedDirectImage.{u, r} Λ π).map ι.hom) ≫
      gπ.inv.app (fieldBaseChangeRestriction.{u, r} Λ Y kbar C) =
      gπ.inv.app ((fieldBaseChangeDerivedRestriction.{u, r} Λ Y kbar).obj
        (DerivedCategory.Plus.Q.obj C)) ≫ RΓ.map ι.hom :=
    gπ.inv.naturality ι.hom
  exact square_of_models RΓ _ _ _ _ hF _ _ hn _ _ hE

/-- **The two models of `Tr(π_Y^* | RΓ(Y_k̄, C|_{Y_k̄}))` agree.** -/
theorem perfectDerivedTrace_frobeniusGlobalSectionsEndo_eq [Finite Λ]
    (C : CochainComplex.Plus (EtaleModules.{u, r} Λ Y.left))
    (h₁ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      ((etaleModuleDerivedGlobalSections.{u, r} Λ (fieldBaseChange Y kbar)).obj
        ((fieldBaseChangeDerivedRestriction.{u, r} Λ Y kbar).obj (DerivedCategory.Plus.Q.obj C)))))
    (h₂ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      ((etaleModuleDerivedGlobalSections.{u, r} Λ (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, r} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, r} Λ Y kbar C))))) :
    CategoryTheory.FilteredDerived.perfectDerivedTrace Λ ⟨_, h₁⟩ (DerivedCategory.Plus.ι.map
        (frobeniusGlobalSectionsEndo.{u, r} Λ Y kbar p q hcard (DerivedCategory.Plus.Q.obj C))) =
      CategoryTheory.FilteredDerived.perfectDerivedTrace Λ ⟨_, h₂⟩ (DerivedCategory.Plus.ι.map
        (frobeniusRestrictionCohomologyEndo.{u, r} Λ Y kbar p q hcard C)) := by
  refine CategoryTheory.FilteredDerived.perfectDerivedTrace_congr Λ _ _
    (DerivedCategory.Plus.ι.mapIso (frobeniusCohomologyModelsIso.{u, r} Λ Y kbar C)) _ _ ?_
  rw [Functor.mapIso_hom, ← Functor.map_comp, ← Functor.map_comp,
    frobeniusGlobalSectionsEndo_comp_frobeniusCohomologyModelsIso_hom]

end Frobenius

end Stacks.EtaleCohomology

end
