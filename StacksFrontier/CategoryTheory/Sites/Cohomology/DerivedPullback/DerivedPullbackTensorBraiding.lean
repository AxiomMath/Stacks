module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalSheafTensorBraidingAnyUniverse
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackBraiding
public import StacksFrontier.Algebra.Homology.MapHomologicalComplexKoszulBraiding
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorAssociativity
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.FlatKFlatModelsGeneral
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.FlatTensorComplexGeneral
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Braiding

/-!
# Stacks 07A4 is compatible with the symmetry of `⊗^L`

Let `f : (Sh(C), O) ⟶ (Sh(D), O')` be a morphism of ringed topoi. The comparison
`Lf^*(A ⊗^L B) ≅ Lf^*A ⊗^L Lf^*B` of Stacks 07A4 commutes with the commutativity constraints of
the two derived tensor products (Tag 0FPT). The proof is the computation on K-flat complexes
with flat terms: there both constraints are the Koszul symmetry of total tensor complexes, and
the comparison of total tensor complexes commutes with it summand by summand, because the
comparison of Tag 03EL commutes with the symmetry of the tensor product sheaf.

## Main results

* `Stacks.Cohomology.DerivedPullbackOfToposHom.pullbackTensorComplexμ_braiding`.

## References

* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom (pullbackComplex)
open Stacks.Sheaves.DerivedPullback (isFlat_tensorComplex_X_general)

namespace Stacks.Cohomology.DerivedPullbackOfToposHom

universe u c c'

attribute [local instance 2000] CategoryTheory.Abelian.hasBinaryBiproducts

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] hasLeftDerivedFunctor_pullbackOnHomotopy

attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  CochainComplex.symmetricCategory

variable {X : RingedTopos.{u, c, u}} {Y : RingedTopos.{u, c', u}}
  [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)]
  (f : RingedToposHom X Y)

section Complexes

/-- An equation `x ≫ e₂.hom = e₁.hom ≫ y` is equivalent to `e₁.inv ≫ x = y ≫ e₂.inv`. -/
private lemma comp_hom_eq_hom_comp_iff {𝒞 : Type*} [Category 𝒞] {A B A' B' : 𝒞} (e₁ : A ≅ B)
    (e₂ : A' ≅ B') {x : A ⟶ A'} {y : B ⟶ B'} :
    x ≫ e₂.hom = e₁.hom ≫ y ↔ e₁.inv ≫ x = y ≫ e₂.inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]

omit [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)] in
/-- **The tensorator of Tag 03EL commutes with the symmetries** of the monoidal structures of
`Mod(O')` and `Mod(O)` re-seated on `⊗`. -/
theorem pullbackTensorμ_braiding
    (a b : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    pullbackTensorμ f a b ≫ (pullbackModulesTensor f).map (β_ a b).hom =
      (β_ ((pullbackModulesTensor f).obj a) ((pullbackModulesTensor f).obj b)).hom ≫
        pullbackTensorμ f b a := by
  have h : f.toModulesHom.pullbackModules.map
        (((Stacks.SheafOfModules.Tensor.sheafTensorBraiding Y.O).hom.app a).app b) ≫
        (Stacks.SheafOfModules.pullbackTensorIso f.toModulesHom).hom.app (b, a) =
      (Stacks.SheafOfModules.pullbackTensorIso f.toModulesHom).hom.app (a, b) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensorBraiding X.O).hom.app
          (f.toModulesHom.pullbackModules.obj a)).app (f.toModulesHom.pullbackModules.obj b) := by
    refine Eq.trans (congrArg (fun z ↦ f.toModulesHom.pullbackModules.map z ≫
        (Stacks.SheafOfModules.pullbackTensorIso f.toModulesHom).hom.app (b, a))
      (congrArg Iso.hom (Stacks.SheafOfModules.braiding_eq_tensorSheafBraiding Y.O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property a b)).symm) ?_
    refine Eq.trans (Stacks.SheafOfModules.RingedToposPullback.braiding f.toModulesHom a b) ?_
    exact congrArg
      (fun z ↦ (Stacks.SheafOfModules.pullbackTensorIso f.toModulesHom).hom.app (a, b) ≫ z)
      (congrArg Iso.hom (Stacks.SheafOfModules.braiding_eq_tensorSheafBraiding X.O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property (f.toModulesHom.pullbackModules.obj a)
        (f.toModulesHom.pullbackModules.obj b)))
  rw [SheafOfModules.AnyUniverse.braiding_eq_sheafTensorBraiding,
    SheafOfModules.AnyUniverse.braiding_eq_sheafTensorBraiding]
  exact (comp_hom_eq_hom_comp_iff
    ((Stacks.SheafOfModules.pullbackTensorIso f.toModulesHom).app (a, b))
    ((Stacks.SheafOfModules.pullbackTensorIso f.toModulesHom).app (b, a))).1 h

omit [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)] in
/-- **The comparison of total tensor complexes commutes with the Koszul braidings**: the
tensorator `f^*K ⊗ f^*L ≅ f^*(K ⊗ L)` of Stacks 07A4 carries the Koszul symmetry of the total
tensor products of complexes to each other. -/
theorem pullbackTensorComplexμ_braiding
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    (pullbackTensorComplexμ f K L).hom ≫
        ((pullbackModulesTensor f).mapHomologicalComplex _).map (β_ K L).hom =
      (β_ (((pullbackModulesTensor f).mapHomologicalComplex _).obj K)
          (((pullbackModulesTensor f).mapHomologicalComplex _).obj L)).hom ≫
        (pullbackTensorComplexμ f L K).hom :=
  Functor.mapHomologicalComplex_koszulBraiding_of_ι (pullbackModulesTensor f)
    (pullbackTensorμ f) (pullbackTensorμ_braiding f)
    (fun K L ↦ (pullbackTensorComplexμ f K L).hom)
    (fun K L p q n h ↦ ι_pullbackTensorComplexμ_hom f K L p q n h) K L

omit [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)] in
/-- **The comparison of total tensor complexes of Stacks 07A4 commutes with the Koszul
braidings**, in the spelling of `pullbackTensorTotalComplexIso`. -/
theorem pullbackTensorTotalComplexIso_braiding
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    (pullbackComplex f).map (β_ K L).hom ≫ (pullbackTensorTotalComplexIso f L K).hom =
      (pullbackTensorTotalComplexIso f K L).hom ≫
        (β_ ((pullbackComplex f).obj K) ((pullbackComplex f).obj L)).hom :=
  (comp_hom_eq_hom_comp_iff (pullbackTensorTotalComplexIso f K L)
    (pullbackTensorTotalComplexIso f L K)).2 (pullbackTensorComplexμ_braiding f K L)

end Complexes

section Models

variable (TX : Stacks.SheafOfModules.DerivedTensorProduct.{c, u, u} X.toRingedSite)
  (TY : Stacks.SheafOfModules.DerivedTensorProduct.{c', u, u} Y.toRingedSite)

/-- Reassembly of the braiding square of Stacks 07A4 on models, in an arbitrary category so that
every object is a variable. -/
private lemma braid_assemble {𝒟 : Type*} [Category 𝒟]
    {X₀ X₁ X₂ X₃ Y₁ Z₀ Z₁ W₀ W₁ V : 𝒟} (b : X₀ ⟶ X₁) (m₁ : X₁ ⟶ X₂) (ψ₁ : X₂ ⟶ X₃)
    (hψ : Mono ψ₁)
    (m₀ : X₀ ⟶ Y₁) (bX : Y₁ ⟶ X₂) (cN : X₁ ⟶ Z₁) (cP : X₀ ⟶ Z₀) (qβ : Z₀ ⟶ Z₁)
    (flN : Z₁ ⟶ W₁) (flP : Z₀ ⟶ W₀) (fβ : W₀ ⟶ W₁) (tN : W₁ ⟶ X₃) (tP : W₀ ⟶ V)
    (β' : V ⟶ X₃) (ψ₀ : Y₁ ⟶ V)
    (hY : b ≫ cN = cP ≫ qβ) (hfl : qβ ≫ flN = flP ≫ fβ) (htot : fβ ≫ tN = tP ≫ β')
    (hmN : m₁ ≫ ψ₁ = (cN ≫ flN) ≫ tN) (hmP : m₀ ≫ ψ₀ = (cP ≫ flP) ≫ tP)
    (hX : bX ≫ ψ₁ = ψ₀ ≫ β') :
    b ≫ m₁ = m₀ ≫ bX := by
  have := hψ
  rw [← cancel_mono ψ₁, Category.assoc, Category.assoc, hX, hmN, ← Category.assoc m₀, hmP]
  simp only [Category.assoc]
  rw [reassoc_of% hY, reassoc_of% hfl, htot]

/-- The target side of the braiding square on models: the braiding of `⊗^L_O`, moved past the
two computations of `Lf^*` and the K-flat comparison. -/
private lemma braid_target {𝒟 : Type*} [Category 𝒟] {A₀ A₁ A₂ B₀ B₁ B₂ C₂ D₂ : 𝒟}
    (bX : A₀ ⟶ B₀) (k₁ : B₀ ⟶ B₁) (k₂ : B₁ ⟶ B₂) (k₁' : A₀ ⟶ A₁) (k₂' : A₁ ⟶ A₂)
    (bQ : A₂ ⟶ B₂) (c : B₂ ⟶ D₂) (c' : A₂ ⟶ C₂) (qβ : C₂ ⟶ D₂)
    (hnat : k₁' ≫ k₂' ≫ bQ = bX ≫ k₁ ≫ k₂) (hc : bQ ≫ c = c' ≫ qβ) :
    bX ≫ (k₁ ≫ k₂) ≫ c = ((k₁' ≫ k₂') ≫ c') ≫ qβ := by
  simp only [Category.assoc]
  rw [← reassoc_of% hnat, hc]

/-- **The isomorphism of Stacks 07A4 is compatible with the commutativity constraints** of the
derived tensor products, on K-flat complexes with flat terms. -/
theorem derivedPullbackTensorIso_braiding_model
    (P N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hP : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) P)
    (hN : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) N)
    (hflatP : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (P.X i))
    (hflatN : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (N.X i)) :
    (derivedPullback f).map (TY.braiding (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj N)).hom ≫
        (derivedPullbackTensorIso f TX TY).hom.app
          (DerivedCategory.Q.obj N, DerivedCategory.Q.obj P) =
      (derivedPullbackTensorIso f TX TY).hom.app
          (DerivedCategory.Q.obj P, DerivedCategory.Q.obj N) ≫
        (TX.braiding ((derivedPullback f).obj (DerivedCategory.Q.obj P))
          ((derivedPullback f).obj (DerivedCategory.Q.obj N))).hom := by
  have hY : (derivedPullback f).map
        (TY.braiding (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj N)).hom ≫
        (derivedPullback f).map (TY.comparison N P hN hP).hom =
      (derivedPullback f).map (TY.comparison P N hP hN).hom ≫
        (derivedPullback f).map (DerivedCategory.Q.map (β_ P N).hom) :=
    (Functor.map_comp _ _ _).symm.trans
      ((congrArg (derivedPullback f).map (TY.comparison_braiding P N hP hN)).trans
        (Functor.map_comp _ _ _))
  have hfl := flatPullbackIso_naturality f (β_ P N).hom
    (Stacks.SheafOfModules.kFlat_tensorComplex Y.O hP hN)
    (Stacks.SheafOfModules.kFlat_tensorComplex Y.O hN hP)
    (isFlat_tensorComplex_X_general Y.O P N hflatP hflatN)
    (isFlat_tensorComplex_X_general Y.O N P hflatN hflatP)
  have htot : DerivedCategory.Q.map ((pullbackComplex f).map (β_ P N).hom) ≫
        DerivedCategory.Q.map (pullbackTensorTotalComplexIso f N P).hom =
      DerivedCategory.Q.map (pullbackTensorTotalComplexIso f P N).hom ≫
        DerivedCategory.Q.map (β_ ((pullbackComplex f).obj P) ((pullbackComplex f).obj N)).hom := by
    rw [← Functor.map_comp, ← Functor.map_comp, pullbackTensorTotalComplexIso_braiding]
  have hnat := TX.braiding_hom_naturality (flatPullbackIso f P hP hflatP).hom
    (flatPullbackIso f N hN hflatN).hom
  have hc := TX.comparison_braiding ((pullbackComplex f).obj P) ((pullbackComplex f).obj N)
    (kFlat_pullbackComplex' f P hP hflatP) (kFlat_pullbackComplex' f N hN hflatN)
  have hX := braid_target _ _ _ _ _ _ _ _ _ hnat hc
  exact braid_assemble _ _ _ (inferInstanceAs (Mono ((((TX.tensor.mapIso
      (flatPullbackIso f N hN hflatN)).app ((derivedPullback f).obj (DerivedCategory.Q.obj P)) ≪≫
      (TX.tensor.obj (DerivedCategory.Q.obj ((pullbackComplex f).obj N))).mapIso
        (flatPullbackIso f P hP hflatP)) ≪≫
      TX.comparison ((pullbackComplex f).obj N) ((pullbackComplex f).obj P)
        (kFlat_pullbackComplex' f N hN hflatN) (kFlat_pullbackComplex' f P hP hflatP)).hom)))
    _ _ _ _ _ _ _ _ _ _ _ _ hY hfl htot
    (derivedPullbackTensorIso_hom_app_model_comp f TX TY N P hN hP hflatN hflatP)
    (derivedPullbackTensorIso_hom_app_model_comp f TX TY P N hP hN hflatP hflatN) hX

/-- **A braiding square for a bifunctorial isomorphism transfers along isomorphisms** of its two
arguments, both braidings being natural. -/
private lemma braid_of_iso {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] (TC : 𝒞 ⥤ 𝒞 ⥤ 𝒞)
    (TD : 𝒟 ⥤ 𝒟 ⥤ 𝒟) {F : 𝒞 ⥤ 𝒟}
    (μ : Functor.uncurry.obj TC ⋙ F ≅ F.prod F ⋙ Functor.uncurry.obj TD)
    (βC : ∀ A B : 𝒞, (TC.obj A).obj B ≅ (TC.obj B).obj A)
    (βD : ∀ A B : 𝒟, (TD.obj A).obj B ≅ (TD.obj B).obj A)
    (hβC : ∀ {A A' B B' : 𝒞} (a : A ⟶ A') (b : B ⟶ B'),
      (TC.map a).app B ≫ (TC.obj A').map b ≫ (βC A' B').hom =
        (βC A B).hom ≫ (TC.map b).app A ≫ (TC.obj B').map a)
    (hβD : ∀ {A A' B B' : 𝒟} (a : A ⟶ A') (b : B ⟶ B'),
      (TD.map a).app B ≫ (TD.obj A').map b ≫ (βD A' B').hom =
        (βD A B).hom ≫ (TD.map b).app A ≫ (TD.obj B').map a)
    {A A' B B' : 𝒞} (eA : A ≅ A') (eB : B ≅ B')
    (h : F.map (βC A' B').hom ≫ μ.hom.app (B', A') =
      μ.hom.app (A', B') ≫ (βD (F.obj A') (F.obj B')).hom) :
    F.map (βC A B).hom ≫ μ.hom.app (B, A) = μ.hom.app (A, B) ≫ (βD (F.obj A) (F.obj B)).hom := by
  have hμ : ∀ {A A' B B' : 𝒞} (a : A ⟶ A') (b : B ⟶ B'),
      F.map ((TC.map a).app B ≫ (TC.obj A').map b) ≫ μ.hom.app (A', B') =
        μ.hom.app (A, B) ≫ (TD.map (F.map a)).app (F.obj B) ≫ (TD.obj (F.obj A')).map (F.map b) :=
    fun {A A' B B'} a b ↦ by
      have hn := μ.hom.naturality ((a, b) : ((A, B) : _ × _) ⟶ (A', B'))
      simp only [Functor.comp_map, Functor.uncurry_obj_map, Functor.prod_map] at hn
      exact hn
  have hiso : IsIso ((TD.map (F.map eB.hom)).app (F.obj A) ≫
      (TD.obj (F.obj B')).map (F.map eA.hom)) := inferInstance
  rw [← cancel_mono ((TD.map (F.map eB.hom)).app (F.obj A) ≫
      (TD.obj (F.obj B')).map (F.map eA.hom))]
  calc (F.map (βC A B).hom ≫ μ.hom.app (B, A)) ≫ (TD.map (F.map eB.hom)).app (F.obj A) ≫
        (TD.obj (F.obj B')).map (F.map eA.hom)
      = F.map (βC A B).hom ≫ F.map ((TC.map eB.hom).app A ≫ (TC.obj B').map eA.hom) ≫
          μ.hom.app (B', A') := by rw [Category.assoc, hμ]
    _ = F.map ((TC.map eA.hom).app B ≫ (TC.obj A').map eB.hom) ≫ F.map (βC A' B').hom ≫
          μ.hom.app (B', A') := by
        rw [← F.map_comp_assoc, ← F.map_comp_assoc, Category.assoc, ← hβC]
    _ = F.map ((TC.map eA.hom).app B ≫ (TC.obj A').map eB.hom) ≫ μ.hom.app (A', B') ≫
          (βD (F.obj A') (F.obj B')).hom := by rw [h]
    _ = μ.hom.app (A, B) ≫ ((TD.map (F.map eA.hom)).app (F.obj B) ≫
          (TD.obj (F.obj A')).map (F.map eB.hom)) ≫ (βD (F.obj A') (F.obj B')).hom := by
        rw [← Category.assoc, hμ, Category.assoc]
    _ = (μ.hom.app (A, B) ≫ (βD (F.obj A) (F.obj B)).hom) ≫
          (TD.map (F.map eB.hom)).app (F.obj A) ≫ (TD.obj (F.obj B')).map (F.map eA.hom) := by
        rw [Category.assoc, Category.assoc, hβD]

/-- **The isomorphism of Stacks 07A4 is compatible with the commutativity constraints of `⊗^L`**:
for `A, B ∈ D(O')` the two isomorphisms `Lf^*(A ⊗^L B) ≅ Lf^*B ⊗^L Lf^*A` built from 07A4 and
the commutativity constraints (Tag 0FPT) agree. -/
theorem derivedPullbackTensorIso_braiding
    (A B : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :
    (derivedPullback f).map (TY.braiding A B).hom ≫
        (derivedPullbackTensorIso f TX TY).hom.app (B, A) =
      (derivedPullbackTensorIso f TX TY).hom.app (A, B) ≫
        (TX.braiding ((derivedPullback f).obj A) ((derivedPullback f).obj B)).hom := by
  have := Stacks.Sheaves.DerivedPullback.flatKFlatModelsQGeneral_isLocalization Y
  have := Localization.essSurj (Stacks.Sheaves.DerivedPullback.flatKFlatModelsQGeneral Y)
    (Stacks.Sheaves.DerivedPullback.flatKFlatModelsWGeneral Y)
  let PA := (Stacks.Sheaves.DerivedPullback.flatKFlatModelsQGeneral Y).objPreimage A
  let PB := (Stacks.Sheaves.DerivedPullback.flatKFlatModelsQGeneral Y).objPreimage B
  let eA : DerivedCategory.Q.obj PA.obj.as ≅ A :=
    (DerivedCategory.quotientCompQhIso _).symm.app PA.obj.as ≪≫
      (Stacks.Sheaves.DerivedPullback.flatKFlatModelsQGeneral Y).objObjPreimageIso A
  let eB : DerivedCategory.Q.obj PB.obj.as ≅ B :=
    (DerivedCategory.quotientCompQhIso _).symm.app PB.obj.as ≪≫
      (Stacks.Sheaves.DerivedPullback.flatKFlatModelsQGeneral Y).objObjPreimageIso B
  exact braid_of_iso TY.tensor TX.tensor (derivedPullbackTensorIso f TX TY) TY.braiding
    TX.braiding (fun a b ↦ TY.braiding_hom_naturality a b)
    (fun a b ↦ TX.braiding_hom_naturality a b) eA.symm eB.symm
    (derivedPullbackTensorIso_braiding_model f TX TY PA.obj.as PB.obj.as PA.property.1
      PB.property.1 PA.property.2 PB.property.2)

end Models

end Stacks.Cohomology.DerivedPullbackOfToposHom

end
