module

public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricStalkDerivedTensor
public import StacksFrontier.CategoryTheory.Adjunction.PullbackInternalHomPushforward
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorAssociativity
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.FlatKFlatModelsGeneral
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.FlatTensorComplexGeneral
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackTensorTotalAssociativity
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.AssociativityGeneral
public import StacksFrontier.Homology.MapHomologicalComplexMonoidal

/-!
# Derived pullback is compatible with the associators of `⊗^L`

Let `f : (Sh(C), O) ⟶ (Sh(D), O')` be a morphism of ringed topoi and let `⊗^L` be derived tensor
products on `D(O)` and `D(O')`. For `A, B, E ∈ D(O')` the two isomorphisms

`Lf^*((A ⊗^L B) ⊗^L E) ≅ Lf^*A ⊗^L (Lf^*B ⊗^L Lf^*E)`

obtained from Stacks 07A4 and the associators of `⊗^L` agree. The associators are those of the
monoidal structure of Tag 0FPT re-seated on the two derived tensor products.

## Main results

* `Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackTensorIso_associativity`: the
  isomorphism `Lf^*(A ⊗^L B) ≅ Lf^*A ⊗^L Lf^*B` of Stacks 07A4 is compatible with the associators
  of `⊗^L`.
* `Stacks.Cohomology.DerivedPullbackOfToposHom.pullbackTensorTotalComplexIso_associativity`: the
  comparison of total tensor complexes is associative, in the spelling of
  `Stacks.SheafOfModules.Tensor.tensorComplex`.

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

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] hasLeftDerivedFunctor_pullbackOnHomotopy

attribute [local instance 2000] CategoryTheory.Abelian.hasBinaryBiproducts

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


section Models

variable (TX : Stacks.SheafOfModules.DerivedTensorProduct.{c, u, u} X.toRingedSite)
  (TY : Stacks.SheafOfModules.DerivedTensorProduct.{c', u, u} Y.toRingedSite)

/-! ## Associativity of Stacks 07A4 on K-flat complexes with flat terms -/

/-- Mapping an equation of threefold composites by a functor. -/
private lemma map_eq_of_eq₃ {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] (H : 𝒞 ⥤ 𝒟)
    {A B E Z B' E' : 𝒞} {x : A ⟶ B} {y : B ⟶ E} {z : E ⟶ Z} {p : A ⟶ B'} {q : B' ⟶ E'}
    {r : E' ⟶ Z} (h : x ≫ y ≫ z = p ≫ q ≫ r) :
    H.map x ≫ H.map y ≫ H.map z = H.map p ≫ H.map q ≫ H.map r := by
  simp only [← H.map_comp, h]

/-- Mapping an equation of threefold composites by a bifunctor in its first variable. -/
private lemma map_app_eq_of_eq₃ {𝒞 𝒟 ℰ : Type*} [Category 𝒞] [Category 𝒟] [Category ℰ]
    (H : 𝒞 ⥤ 𝒟 ⥤ ℰ) (W : 𝒟)
    {A B E Z B' E' : 𝒞} {x : A ⟶ B} {y : B ⟶ E} {z : E ⟶ Z} {p : A ⟶ B'} {q : B' ⟶ E'}
    {r : E' ⟶ Z} (h : x ≫ y ≫ z = p ≫ q ≫ r) :
    (H.map x).app W ≫ (H.map y).app W ≫ (H.map z).app W =
      (H.map p).app W ≫ (H.map q).app W ≫ (H.map r).app W := by
  simp only [← NatTrans.comp_app, ← H.map_comp, h]

/-- Reassembly of the left-hand side of the associativity of Stacks 07A4 on models. -/
private lemma assoc_left_assemble {𝒟 : Type*} [Category 𝒟]
    {X₀ X₁ X₂ X₃ X₄ X₅ X₆ X₇ Y₁ Y₂ Y₃ Z₁ Z₂' W₁ V₁ V₂ R₁ R₂ R₃ : 𝒟}
    (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂) (t : X₂ ⟶ X₃) (w : X₃ ⟶ X₄) (m : X₄ ⟶ X₅) (n : X₅ ⟶ X₆)
    (e : X₆ ⟶ X₇) (w' : X₂ ⟶ Y₁) (t' : Y₁ ⟶ X₄) (u₁ : Y₁ ⟶ Y₂) (u₂ : Y₂ ⟶ Y₃)
    (u₃ : Y₃ ⟶ X₆) (k : X₂ ⟶ Z₂') (w'' : Z₂' ⟶ Y₂) (v₁ : X₁ ⟶ Z₁) (b' : Z₁ ⟶ Z₂')
    (d₁ : Y₃ ⟶ W₁) (q₁ : W₁ ⟶ X₇) (c₁ : Z₁ ⟶ V₁) (ι₁ : V₁ ⟶ V₂) (q₂ : V₂ ⟶ W₁)
    (r₁ : X₀ ⟶ R₁) (r₂ : R₁ ⟶ R₂) (r₃ : R₂ ⟶ V₁) (ι₂ : R₂ ⟶ R₃) (q₃ : R₃ ⟶ V₂)
    (s1 : t ≫ w = w' ≫ t') (s2 : t' ≫ m ≫ n = u₁ ≫ u₂ ≫ u₃) (s3 : w' ≫ u₁ = k ≫ w'')
    (s4 : b ≫ k = v₁ ≫ b') (s5 : u₃ ≫ e = d₁ ≫ q₁) (s6 : b' ≫ (w'' ≫ u₂) ≫ d₁ = c₁ ≫ ι₁ ≫ q₂)
    (s7 : a ≫ v₁ ≫ c₁ = r₁ ≫ r₂ ≫ r₃) (s8 : r₃ ≫ ι₁ = ι₂ ≫ q₃) :
    (a ≫ b ≫ t) ≫ ((w ≫ m) ≫ n ≫ e) = r₁ ≫ r₂ ≫ ι₂ ≫ q₃ ≫ q₂ ≫ q₁ := by
  simp only [Category.assoc] at s6 ⊢
  rw [reassoc_of% s1, reassoc_of% s2, reassoc_of% s3, s5, reassoc_of% s4, reassoc_of% s6,
    ← reassoc_of% s8]
  simp only [← Category.assoc] at s7 ⊢
  rw [s7]

/-- Reassembly of the right-hand side of the associativity of Stacks 07A4 on models. -/
private lemma assoc_right_assemble {𝒟 : Type*} [Category 𝒟]
    {X₀ X₁ X₂ X₃ X₄ X₅ X₆ X₇ Y₁ Y₂ Y₃ Y₄ Z₁ Z₂ Z₃ Z₄ W₁ R₁ R₂ R₃ : 𝒟}
    (Φ : X₀ ⟶ X₁) (φ' : X₁ ⟶ X₂) (αX : X₂ ⟶ X₃) (w : X₃ ⟶ X₄) (m : X₄ ⟶ X₅) (n : X₅ ⟶ X₆)
    (e : X₆ ⟶ X₇) (y₁ : X₂ ⟶ Y₁) (y₂ : Y₁ ⟶ Y₂) (αX' : Y₂ ⟶ X₅) (x₁ : Y₂ ⟶ Y₃)
    (x₂ : Y₃ ⟶ Y₄) (x₃ : Y₄ ⟶ X₇) (x₁' : Y₁ ⟶ Z₁) (y₂' : Z₁ ⟶ Y₃) (z₁ : X₁ ⟶ Z₂)
    (z₂ : Z₂ ⟶ Z₃) (z₃ : Z₃ ⟶ Z₁) (y₃ : Z₃ ⟶ Z₄) (z₃' : Z₄ ⟶ Y₃) (d₂ : Z₄ ⟶ W₁)
    (q₄ : W₁ ⟶ Y₄) (r₁ : X₀ ⟶ R₁) (b'' : R₁ ⟶ Z₂) (r₂ : R₁ ⟶ R₂) (ι₂ : R₂ ⟶ R₃)
    (q₅ : R₃ ⟶ W₁)
    (h1 : αX ≫ w ≫ m = y₁ ≫ y₂ ≫ αX') (h2 : αX' ≫ n ≫ e = x₁ ≫ x₂ ≫ x₃)
    (h3 : y₂ ≫ x₁ = x₁' ≫ y₂') (h4 : φ' ≫ y₁ ≫ x₁' = z₁ ≫ z₂ ≫ z₃)
    (h5 : z₃ ≫ y₂' = y₃ ≫ z₃') (h6 : z₃' ≫ x₂ = d₂ ≫ q₄) (h7 : Φ ≫ z₁ = r₁ ≫ b'')
    (h8 : b'' ≫ (z₂ ≫ y₃) ≫ d₂ = r₂ ≫ ι₂ ≫ q₅) :
    (Φ ≫ φ' ≫ αX) ≫ ((w ≫ m) ≫ n ≫ e) = r₁ ≫ r₂ ≫ ι₂ ≫ q₅ ≫ q₄ ≫ x₃ := by
  simp only [Category.assoc] at h8 ⊢
  rw [reassoc_of% h1, h2, reassoc_of% h3, reassoc_of% h4, reassoc_of% h5, reassoc_of% h6,
    reassoc_of% h7, reassoc_of% h8]

/-- The isomorphism of Stacks 07A4 is natural in its first variable. -/
theorem derivedPullbackTensorIso_hom_naturality_fst
    {A A' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))}
    (x : A ⟶ A')
    (B : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :
    (derivedPullback f).map ((TY.tensor.map x).app B) ≫
        (derivedPullbackTensorIso f TX TY).hom.app (A', B) =
      (derivedPullbackTensorIso f TX TY).hom.app (A, B) ≫
        (TX.tensor.map ((derivedPullback f).map x)).app ((derivedPullback f).obj B) := by
  have h := (derivedPullbackTensorIso f TX TY).hom.naturality
    ((x, 𝟙 B) : ((A, B) : _ × _) ⟶ (A', B))
  simp only [Functor.comp_map, Functor.uncurry_obj_map, Functor.prod_map, Functor.prod_obj,
    CategoryTheory.Functor.map_id, Category.comp_id] at h
  exact h

/-- The isomorphism of Stacks 07A4 is natural in its second variable. -/
theorem derivedPullbackTensorIso_hom_naturality_snd
    (A : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    {B B' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))}
    (x : B ⟶ B') :
    (derivedPullback f).map ((TY.tensor.obj A).map x) ≫
        (derivedPullbackTensorIso f TX TY).hom.app (A, B') =
      (derivedPullbackTensorIso f TX TY).hom.app (A, B) ≫
        (TX.tensor.obj ((derivedPullback f).obj A)).map ((derivedPullback f).map x) := by
  have h := (derivedPullbackTensorIso f TX TY).hom.naturality
    ((𝟙 A, x) : ((A, B) : _ × _) ⟶ (A, B'))
  simp only [Functor.comp_map, Functor.uncurry_obj_map, Functor.prod_map, Functor.prod_obj,
    CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp] at h
  exact h

/-- Rearranging the inverse of an equation between composites of three isomorphisms. -/
private lemma hom_comp_inv_comp_inv {𝒞 : Type*} [Category 𝒞] {A B C D E G : 𝒞} (a : A ≅ B)
    (b : B ≅ C) (c : C ≅ D) (d : A ≅ E) (e : E ≅ G) (g : G ≅ D)
    (h : a.hom ≫ b.hom ≫ c.hom = d.hom ≫ e.hom ≫ g.hom) :
    c.hom ≫ g.inv ≫ e.inv = b.inv ≫ a.inv ≫ d.hom := by
  calc c.hom ≫ g.inv ≫ e.inv = b.inv ≫ a.inv ≫ (a.hom ≫ b.hom ≫ c.hom) ≫ g.inv ≫ e.inv := by
        simp
    _ = b.inv ≫ a.inv ≫ d.hom := by rw [h]; simp


omit [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)] in
/-- The comparison of total tensor complexes is associative, in the direction of
`pullbackTensorTotalComplexIso`. -/
theorem pullbackTensorComplexμ_inv_associativity
    (P N M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    ((pullbackModulesTensor f).mapHomologicalComplex _).map (α_ P N M).hom ≫
      (pullbackTensorComplexμ f P (N ⊗ M)).inv ≫
      ((((pullbackModulesTensor f).mapHomologicalComplex _).obj P) ◁
      (pullbackTensorComplexμ f N M).inv) =
      (pullbackTensorComplexμ f (P ⊗ N) M).inv ≫
        ((pullbackTensorComplexμ f P N).inv ▷
        (((pullbackModulesTensor f).mapHomologicalComplex _).obj M)) ≫
        (α_ (((pullbackModulesTensor f).mapHomologicalComplex _).obj P)
        (((pullbackModulesTensor f).mapHomologicalComplex _).obj N)
        (((pullbackModulesTensor f).mapHomologicalComplex _).obj M)).hom :=
  hom_comp_inv_comp_inv (whiskerRightIso (pullbackTensorComplexμ f P N)
    (((pullbackModulesTensor f).mapHomologicalComplex _).obj M))
    (pullbackTensorComplexμ f (P ⊗ N) M)
    (((pullbackModulesTensor f).mapHomologicalComplex _).mapIso (α_ P N M))
    (α_ (((pullbackModulesTensor f).mapHomologicalComplex _).obj P)
      (((pullbackModulesTensor f).mapHomologicalComplex _).obj N)
      (((pullbackModulesTensor f).mapHomologicalComplex _).obj M))
      (whiskerLeftIso (((pullbackModulesTensor f).mapHomologicalComplex _).obj P)
      (pullbackTensorComplexμ f N M)) (pullbackTensorComplexμ f P (N ⊗ M))
    (pullbackTensorComplexμ_associativity f P N M)

/-- `derivedPullbackTensorIso_hom_app_model_comp` with the total tensor complex spelled by
`Stacks.SheafOfModules.Tensor.tensorComplex`. -/
theorem derivedPullbackTensorIso_hom_app_model_comp₂
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) K)
    (hL : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) L)
    (hflatK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (K.X i))
    (hflatL : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (L.X i)) :
    ((derivedPullbackTensorIso f TX TY).hom.app
      ((DerivedCategory.Q.obj K), (DerivedCategory.Q.obj L))) ≫
      ((TX.tensor.map (flatPullbackIso f K hK hflatK).hom).app
        ((derivedPullback f).obj (DerivedCategory.Q.obj L)) ≫
        (TX.tensor.obj (DerivedCategory.Q.obj ((pullbackComplex f).obj K))).map
          (flatPullbackIso f L hL hflatL).hom) ≫
        (TX.comparison ((pullbackComplex f).obj K) ((pullbackComplex f).obj L)
          (kFlat_pullbackComplex' f K hK hflatK)
          (kFlat_pullbackComplex' f L hL hflatL)).hom =
      ((derivedPullback f).map (TY.comparison K L hK hL).hom) ≫
        (flatPullbackIso f ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj
          K |>.obj L) (Stacks.SheafOfModules.kFlat_tensorComplex Y.toRingedSite.O hK hL)
          (isFlat_tensorComplex_X_general Y.O K L hflatK hflatL)).hom ≫
          (DerivedCategory.Q.map (Iso.hom
            (X := ((pullbackComplex f).obj
            ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj K |>.obj L)))
            (Y := ((Stacks.SheafOfModules.Tensor.tensorComplex X.toRingedSite.O).obj
            ((pullbackComplex f).obj K) |>.obj ((pullbackComplex f).obj L)))
            (pullbackTensorTotalComplexIso f K L))) :=
  (derivedPullbackTensorIso_hom_app_model_comp f TX TY K L hK hL hflatK hflatL).trans
    (Category.assoc _ _ _)

private theorem assoc_model_s1
    (P N M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hP : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) P)
    (hflatP : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (P.X i)) :
    ((TX.tensor.obj ((derivedPullback f).obj (DerivedCategory.Q.obj P))).map
      ((derivedPullbackTensorIso f TX TY).hom.app
      ((DerivedCategory.Q.obj N), (DerivedCategory.Q.obj M)))) ≫
      ((TX.tensor.map (flatPullbackIso f P hP hflatP).hom).app
      ((TX.tensor.obj ((derivedPullback f).obj (DerivedCategory.Q.obj N))).obj
      ((derivedPullback f).obj (DerivedCategory.Q.obj M)))) =
      ((TX.tensor.map (flatPullbackIso f P hP hflatP).hom).app
      ((derivedPullback f).obj
      ((TY.tensor.obj (DerivedCategory.Q.obj N)).obj (DerivedCategory.Q.obj M)))) ≫
      ((TX.tensor.obj (DerivedCategory.Q.obj ((pullbackComplex f).obj P))).map
      ((derivedPullbackTensorIso f TX TY).hom.app
      ((DerivedCategory.Q.obj N), (DerivedCategory.Q.obj M)))) :=
  ((TX.tensor.map (flatPullbackIso f P hP hflatP).hom).naturality
    ((derivedPullbackTensorIso f TX TY).hom.app
    ((DerivedCategory.Q.obj N), (DerivedCategory.Q.obj M))))

private theorem assoc_model_s2
    (P N M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hN : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) N)
    (hM : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) M)
    (hflatN : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (N.X i))
    (hflatM : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (M.X i)) :
    ((TX.tensor.obj (DerivedCategory.Q.obj ((pullbackComplex f).obj P))).map
      ((derivedPullbackTensorIso f TX TY).hom.app
      ((DerivedCategory.Q.obj N), (DerivedCategory.Q.obj M)))) ≫
      ((TX.tensor.obj (DerivedCategory.Q.obj ((pullbackComplex f).obj P))).map
      ((TX.tensor.map (flatPullbackIso f N hN hflatN).hom).app
      ((derivedPullback f).obj (DerivedCategory.Q.obj M)) ≫
      (TX.tensor.obj (DerivedCategory.Q.obj ((pullbackComplex f).obj N))).map
      (flatPullbackIso f M hM hflatM).hom)) ≫
      ((TX.tensor.obj (DerivedCategory.Q.obj ((pullbackComplex f).obj P))).map
      (TX.comparison ((pullbackComplex f).obj N) ((pullbackComplex f).obj M)
      (kFlat_pullbackComplex' f N hN hflatN) (kFlat_pullbackComplex' f M hM hflatM)).hom) =
      ((TX.tensor.obj (DerivedCategory.Q.obj ((pullbackComplex f).obj P))).map
      ((derivedPullback f).map (TY.comparison N M hN hM).hom)) ≫
      ((TX.tensor.obj (DerivedCategory.Q.obj ((pullbackComplex f).obj P))).map
      (flatPullbackIso f ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj N |>.obj
      M) (Stacks.SheafOfModules.kFlat_tensorComplex Y.toRingedSite.O hN hM)
      (isFlat_tensorComplex_X_general Y.O N M hflatN hflatM)).hom) ≫
      ((TX.tensor.obj (DerivedCategory.Q.obj ((pullbackComplex f).obj P))).map
      (DerivedCategory.Q.map (Iso.hom
      (X := ((pullbackComplex f).obj
      ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj N |>.obj M)))
      (Y := ((Stacks.SheafOfModules.Tensor.tensorComplex X.toRingedSite.O).obj
      ((pullbackComplex f).obj N) |>.obj ((pullbackComplex f).obj M)))
      (pullbackTensorTotalComplexIso f N M)))) :=
  (map_eq_of_eq₃ (TX.tensor.obj (DerivedCategory.Q.obj ((pullbackComplex f).obj P)))
    (derivedPullbackTensorIso_hom_app_model_comp₂ f TX TY N M hN hM hflatN hflatM))

private theorem assoc_model_s3
    (P N M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hP : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) P)
    (hN : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) N)
    (hM : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) M)
    (hflatP : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (P.X i)) :
    ((TX.tensor.map (flatPullbackIso f P hP hflatP).hom).app
      ((derivedPullback f).obj
      ((TY.tensor.obj (DerivedCategory.Q.obj N)).obj (DerivedCategory.Q.obj M)))) ≫
      ((TX.tensor.obj (DerivedCategory.Q.obj ((pullbackComplex f).obj P))).map
      ((derivedPullback f).map (TY.comparison N M hN hM).hom)) =
      ((TX.tensor.obj ((derivedPullback f).obj (DerivedCategory.Q.obj P))).map
      ((derivedPullback f).map (TY.comparison N M hN hM).hom)) ≫
      ((TX.tensor.map (flatPullbackIso f P hP hflatP).hom).app
      ((derivedPullback f).obj
      (DerivedCategory.Q.obj ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj
      N |>.obj M)))) :=
  ((TX.tensor.map (flatPullbackIso f P hP hflatP).hom).naturality
    ((derivedPullback f).map (TY.comparison N M hN hM).hom)).symm

private theorem assoc_model_s4
    (P N M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hN : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) N)
    (hM : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) M) :
    ((derivedPullbackTensorIso f TX TY).hom.app
      ((DerivedCategory.Q.obj P),
      ((TY.tensor.obj (DerivedCategory.Q.obj N)).obj (DerivedCategory.Q.obj M)))) ≫
      ((TX.tensor.obj ((derivedPullback f).obj (DerivedCategory.Q.obj P))).map
      ((derivedPullback f).map (TY.comparison N M hN hM).hom)) =
      ((derivedPullback f).map
      ((TY.tensor.obj (DerivedCategory.Q.obj P)).map (TY.comparison N M hN hM).hom)) ≫
      ((derivedPullbackTensorIso f TX TY).hom.app
      ((DerivedCategory.Q.obj P),
      (DerivedCategory.Q.obj ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj
      N |>.obj M)))) :=
  (derivedPullbackTensorIso_hom_naturality_snd f TX TY (DerivedCategory.Q.obj P)
    (TY.comparison N M hN hM).hom).symm

private theorem assoc_model_s5
    (P N M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hP : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) P)
    (hN : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) N)
    (hM : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) M)
    (hflatP : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (P.X i))
    (hflatN : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (N.X i))
    (hflatM : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (M.X i)) :
    ((TX.tensor.obj (DerivedCategory.Q.obj ((pullbackComplex f).obj P))).map
      (DerivedCategory.Q.map (Iso.hom
      (X := ((pullbackComplex f).obj
      ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj N |>.obj M)))
      (Y := ((Stacks.SheafOfModules.Tensor.tensorComplex X.toRingedSite.O).obj
      ((pullbackComplex f).obj N) |>.obj ((pullbackComplex f).obj M)))
      (pullbackTensorTotalComplexIso f N M)))) ≫
      (TX.comparison ((pullbackComplex f).obj P)
      ((Stacks.SheafOfModules.Tensor.tensorComplex X.toRingedSite.O).obj
      ((pullbackComplex f).obj N) |>.obj ((pullbackComplex f).obj M))
      (kFlat_pullbackComplex' f P hP hflatP)
      (Stacks.SheafOfModules.kFlat_tensorComplex X.toRingedSite.O
      (kFlat_pullbackComplex' f N hN hflatN) (kFlat_pullbackComplex' f M hM hflatM))).hom =
      (TX.comparison ((pullbackComplex f).obj P)
      ((pullbackComplex f).obj
      ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj N |>.obj M))
      (kFlat_pullbackComplex' f P hP hflatP)
      (kFlat_pullbackComplex' f
      ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj N |>.obj M)
      (Stacks.SheafOfModules.kFlat_tensorComplex Y.toRingedSite.O hN hM)
      (isFlat_tensorComplex_X_general Y.O N M hflatN hflatM))).hom ≫
      (DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap (𝟙 ((pullbackComplex f).obj P))
      (Iso.hom (X := ((pullbackComplex f).obj
      ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj N |>.obj M)))
      (Y := ((Stacks.SheafOfModules.Tensor.tensorComplex X.toRingedSite.O).obj
      ((pullbackComplex f).obj N) |>.obj ((pullbackComplex f).obj M)))
      (pullbackTensorTotalComplexIso f N M))
      (Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSite.O) (ComplexShape.up ℤ))) :=
  (TX.comparison_naturality_right ((pullbackComplex f).obj P)
    (Iso.hom (X := ((pullbackComplex f).obj
    ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj N |>.obj M)))
    (Y := ((Stacks.SheafOfModules.Tensor.tensorComplex X.toRingedSite.O).obj
    ((pullbackComplex f).obj N) |>.obj ((pullbackComplex f).obj M)))
    (pullbackTensorTotalComplexIso f N M)) (kFlat_pullbackComplex' f P hP hflatP)
    (kFlat_pullbackComplex' f
    ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj N |>.obj M)
    (Stacks.SheafOfModules.kFlat_tensorComplex Y.toRingedSite.O hN hM)
    (isFlat_tensorComplex_X_general Y.O N M hflatN hflatM))
    (Stacks.SheafOfModules.kFlat_tensorComplex X.toRingedSite.O
    (kFlat_pullbackComplex' f N hN hflatN) (kFlat_pullbackComplex' f M hM hflatM)))

private theorem assoc_model_s6
    (P N M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hP : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) P)
    (hN : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) N)
    (hM : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) M)
    (hflatP : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (P.X i))
    (hflatN : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (N.X i))
    (hflatM : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (M.X i)) :
    ((derivedPullbackTensorIso f TX TY).hom.app
      ((DerivedCategory.Q.obj P),
      (DerivedCategory.Q.obj ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj
      N |>.obj M)))) ≫ (((TX.tensor.map (flatPullbackIso f P hP hflatP).hom).app
      ((derivedPullback f).obj
      (DerivedCategory.Q.obj ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj
      N |>.obj M)))) ≫ ((TX.tensor.obj (DerivedCategory.Q.obj ((pullbackComplex f).obj P))).map
      (flatPullbackIso f ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj N |>.obj
      M) (Stacks.SheafOfModules.kFlat_tensorComplex Y.toRingedSite.O hN hM)
      (isFlat_tensorComplex_X_general Y.O N M hflatN hflatM)).hom)) ≫
      (TX.comparison ((pullbackComplex f).obj P)
      ((pullbackComplex f).obj
      ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj N |>.obj M))
      (kFlat_pullbackComplex' f P hP hflatP)
      (kFlat_pullbackComplex' f
      ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj N |>.obj M)
      (Stacks.SheafOfModules.kFlat_tensorComplex Y.toRingedSite.O hN hM)
      (isFlat_tensorComplex_X_general Y.O N M hflatN hflatM))).hom =
      ((derivedPullback f).map
      (TY.comparison P ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj N |>.obj
      M) hP (Stacks.SheafOfModules.kFlat_tensorComplex Y.toRingedSite.O hN hM)).hom) ≫
      (flatPullbackIso f ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj P |>.obj
      ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj N |>.obj M))
      (Stacks.SheafOfModules.kFlat_tensorComplex Y.toRingedSite.O hP
      (Stacks.SheafOfModules.kFlat_tensorComplex Y.toRingedSite.O hN hM))
      (isFlat_tensorComplex_X_general Y.O P
      ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj N |>.obj M) hflatP
      (isFlat_tensorComplex_X_general Y.O N M hflatN hflatM))).hom ≫
      (DerivedCategory.Q.map (Iso.hom
      (X := ((pullbackComplex f).obj
      ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj P |>.obj
      ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj N |>.obj M))))
      (Y := ((Stacks.SheafOfModules.Tensor.tensorComplex X.toRingedSite.O).obj
      ((pullbackComplex f).obj P) |>.obj
      ((pullbackComplex f).obj
      ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj N |>.obj M))))
      (pullbackTensorTotalComplexIso f P
      ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj N |>.obj M)))) :=
  (derivedPullbackTensorIso_hom_app_model_comp₂ f TX TY P
    ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj N |>.obj M) hP
    (Stacks.SheafOfModules.kFlat_tensorComplex Y.toRingedSite.O hN hM) hflatP
    (isFlat_tensorComplex_X_general Y.O N M hflatN hflatM))

private theorem assoc_model_s7
    (P N M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hP : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) P)
    (hN : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) N)
    (hM : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) M) :
    ((derivedPullback f).map
      (TY.associatorGeneral (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj N)
      (DerivedCategory.Q.obj M)).hom) ≫
      ((derivedPullback f).map
      ((TY.tensor.obj (DerivedCategory.Q.obj P)).map (TY.comparison N M hN hM).hom)) ≫
      ((derivedPullback f).map
      (TY.comparison P ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj N |>.obj
      M) hP (Stacks.SheafOfModules.kFlat_tensorComplex Y.toRingedSite.O hN hM)).hom) =
      ((derivedPullback f).map
      ((TY.tensor.map (TY.comparison P N hP hN).hom).app (DerivedCategory.Q.obj M))) ≫
      ((derivedPullback f).map
      (TY.comparison ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj P |>.obj N)
      M (Stacks.SheafOfModules.kFlat_tensorComplex Y.toRingedSite.O hP hN) hM).hom) ≫
      ((derivedPullback f).map
      (DerivedCategory.Q.map (Stacks.SheafOfModules.DerivedTensorProduct.tensorComplexAssociator
      (Y := Y.toRingedSite) P N M).hom)) :=
  (map_eq_of_eq₃ (derivedPullback f) (TY.comparison_tensorComplexAssociator hP hN hM).symm)

private theorem assoc_model_s8
    (P N M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hP : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) P)
    (hN : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) N)
    (hM : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) M)
    (hflatP : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (P.X i))
    (hflatN : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (N.X i))
    (hflatM : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (M.X i)) :
    ((derivedPullback f).map
      (DerivedCategory.Q.map (Stacks.SheafOfModules.DerivedTensorProduct.tensorComplexAssociator
      (Y := Y.toRingedSite) P N M).hom)) ≫
      (flatPullbackIso f ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj P |>.obj
      ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj N |>.obj M))
      (Stacks.SheafOfModules.kFlat_tensorComplex Y.toRingedSite.O hP
      (Stacks.SheafOfModules.kFlat_tensorComplex Y.toRingedSite.O hN hM))
      (isFlat_tensorComplex_X_general Y.O P
      ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj N |>.obj M) hflatP
      (isFlat_tensorComplex_X_general Y.O N M hflatN hflatM))).hom =
      (flatPullbackIso f ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj
      ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj P |>.obj N) |>.obj M)
      (Stacks.SheafOfModules.kFlat_tensorComplex Y.toRingedSite.O
      (Stacks.SheafOfModules.kFlat_tensorComplex Y.toRingedSite.O hP hN) hM)
      (isFlat_tensorComplex_X_general Y.O
      ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj P |>.obj N) M
      (isFlat_tensorComplex_X_general Y.O P N hflatP hflatN) hflatM)).hom ≫
      (DerivedCategory.Q.map ((pullbackComplex f).map
      (Stacks.SheafOfModules.DerivedTensorProduct.tensorComplexAssociator (Y := Y.toRingedSite)
      P N M).hom)) :=
  (flatPullbackIso_naturality f
    (Stacks.SheafOfModules.DerivedTensorProduct.tensorComplexAssociator (Y := Y.toRingedSite)
    P N M).hom (Stacks.SheafOfModules.kFlat_tensorComplex Y.toRingedSite.O
    (Stacks.SheafOfModules.kFlat_tensorComplex Y.toRingedSite.O hP hN) hM)
    (Stacks.SheafOfModules.kFlat_tensorComplex Y.toRingedSite.O hP
    (Stacks.SheafOfModules.kFlat_tensorComplex Y.toRingedSite.O hN hM))
    (isFlat_tensorComplex_X_general Y.O
    ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj P |>.obj N) M
    (isFlat_tensorComplex_X_general Y.O P N hflatP hflatN) hflatM)
    (isFlat_tensorComplex_X_general Y.O P
    ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj N |>.obj M) hflatP
    (isFlat_tensorComplex_X_general Y.O N M hflatN hflatM)))

private theorem assoc_model_h1
    (P N M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hP : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) P)
    (hN : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) N)
    (hM : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) M)
    (hflatP : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (P.X i))
    (hflatN : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (N.X i))
    (hflatM : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (M.X i)) :
    (TX.associatorGeneral ((derivedPullback f).obj (DerivedCategory.Q.obj P))
      ((derivedPullback f).obj (DerivedCategory.Q.obj N))
      ((derivedPullback f).obj (DerivedCategory.Q.obj M))).hom ≫
      ((TX.tensor.map (flatPullbackIso f P hP hflatP).hom).app
      ((TX.tensor.obj ((derivedPullback f).obj (DerivedCategory.Q.obj N))).obj
      ((derivedPullback f).obj (DerivedCategory.Q.obj M)))) ≫
      ((TX.tensor.obj (DerivedCategory.Q.obj ((pullbackComplex f).obj P))).map
      ((TX.tensor.map (flatPullbackIso f N hN hflatN).hom).app
      ((derivedPullback f).obj (DerivedCategory.Q.obj M)) ≫
      (TX.tensor.obj (DerivedCategory.Q.obj ((pullbackComplex f).obj N))).map
      (flatPullbackIso f M hM hflatM).hom)) =
      ((TX.tensor.map ((TX.tensor.map (flatPullbackIso f P hP hflatP).hom).app
      ((derivedPullback f).obj (DerivedCategory.Q.obj N)) ≫
      (TX.tensor.obj (DerivedCategory.Q.obj ((pullbackComplex f).obj P))).map
      (flatPullbackIso f N hN hflatN).hom)).app
      ((derivedPullback f).obj (DerivedCategory.Q.obj M))) ≫
      ((TX.tensor.obj ((TX.tensor.obj (DerivedCategory.Q.obj ((pullbackComplex f).obj P))).obj
      (DerivedCategory.Q.obj ((pullbackComplex f).obj N)))).map
      (flatPullbackIso f M hM hflatM).hom) ≫
      (TX.associatorGeneral (DerivedCategory.Q.obj ((pullbackComplex f).obj P))
      (DerivedCategory.Q.obj ((pullbackComplex f).obj N))
      (DerivedCategory.Q.obj ((pullbackComplex f).obj M))).hom :=
  (TX.associatorGeneral_naturality (flatPullbackIso f P hP hflatP).hom
    (flatPullbackIso f N hN hflatN).hom (flatPullbackIso f M hM hflatM).hom).symm.trans
    (Category.assoc _ _ _)

private theorem assoc_model_h2
    (P N M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hP : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) P)
    (hN : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) N)
    (hM : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) M)
    (hflatP : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (P.X i))
    (hflatN : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (N.X i))
    (hflatM : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (M.X i)) :
    (TX.associatorGeneral (DerivedCategory.Q.obj ((pullbackComplex f).obj P))
      (DerivedCategory.Q.obj ((pullbackComplex f).obj N))
      (DerivedCategory.Q.obj ((pullbackComplex f).obj M))).hom ≫
      ((TX.tensor.obj (DerivedCategory.Q.obj ((pullbackComplex f).obj P))).map
      (TX.comparison ((pullbackComplex f).obj N) ((pullbackComplex f).obj M)
      (kFlat_pullbackComplex' f N hN hflatN) (kFlat_pullbackComplex' f M hM hflatM)).hom) ≫
      (TX.comparison ((pullbackComplex f).obj P)
      ((Stacks.SheafOfModules.Tensor.tensorComplex X.toRingedSite.O).obj
      ((pullbackComplex f).obj N) |>.obj ((pullbackComplex f).obj M))
      (kFlat_pullbackComplex' f P hP hflatP)
      (Stacks.SheafOfModules.kFlat_tensorComplex X.toRingedSite.O
      (kFlat_pullbackComplex' f N hN hflatN) (kFlat_pullbackComplex' f M hM hflatM))).hom =
      ((TX.tensor.map (TX.comparison ((pullbackComplex f).obj P) ((pullbackComplex f).obj N)
      (kFlat_pullbackComplex' f P hP hflatP) (kFlat_pullbackComplex' f N hN hflatN)).hom).app
      (DerivedCategory.Q.obj ((pullbackComplex f).obj M))) ≫
      (TX.comparison ((Stacks.SheafOfModules.Tensor.tensorComplex X.toRingedSite.O).obj
      ((pullbackComplex f).obj P) |>.obj ((pullbackComplex f).obj N)) ((pullbackComplex f).obj M)
      (Stacks.SheafOfModules.kFlat_tensorComplex X.toRingedSite.O
      (kFlat_pullbackComplex' f P hP hflatP) (kFlat_pullbackComplex' f N hN hflatN))
      (kFlat_pullbackComplex' f M hM hflatM)).hom ≫
      (DerivedCategory.Q.map (Stacks.SheafOfModules.DerivedTensorProduct.tensorComplexAssociator
      (Y := X.toRingedSite) ((pullbackComplex f).obj P) ((pullbackComplex f).obj N)
      ((pullbackComplex f).obj M)).hom) :=
  (TX.comparison_tensorComplexAssociator (kFlat_pullbackComplex' f P hP hflatP)
    (kFlat_pullbackComplex' f N hN hflatN) (kFlat_pullbackComplex' f M hM hflatM)).symm

private theorem assoc_model_h3
    (P N M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hP : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) P)
    (hN : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) N)
    (hM : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) M)
    (hflatP : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (P.X i))
    (hflatN : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (N.X i))
    (hflatM : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (M.X i)) :
    ((TX.tensor.obj ((TX.tensor.obj (DerivedCategory.Q.obj ((pullbackComplex f).obj P))).obj
      (DerivedCategory.Q.obj ((pullbackComplex f).obj N)))).map
      (flatPullbackIso f M hM hflatM).hom) ≫
      ((TX.tensor.map (TX.comparison ((pullbackComplex f).obj P) ((pullbackComplex f).obj N)
      (kFlat_pullbackComplex' f P hP hflatP) (kFlat_pullbackComplex' f N hN hflatN)).hom).app
      (DerivedCategory.Q.obj ((pullbackComplex f).obj M))) =
      ((TX.tensor.map (TX.comparison ((pullbackComplex f).obj P) ((pullbackComplex f).obj N)
      (kFlat_pullbackComplex' f P hP hflatP) (kFlat_pullbackComplex' f N hN hflatN)).hom).app
      ((derivedPullback f).obj (DerivedCategory.Q.obj M))) ≫
      ((TX.tensor.obj (DerivedCategory.Q.obj
      ((Stacks.SheafOfModules.Tensor.tensorComplex X.toRingedSite.O).obj
      ((pullbackComplex f).obj P) |>.obj ((pullbackComplex f).obj N)))).map
      (flatPullbackIso f M hM hflatM).hom) :=
  ((TX.tensor.map (TX.comparison ((pullbackComplex f).obj P) ((pullbackComplex f).obj N)
    (kFlat_pullbackComplex' f P hP hflatP) (kFlat_pullbackComplex' f N hN hflatN)).hom).naturality
    (flatPullbackIso f M hM hflatM).hom)

private theorem assoc_model_h4
    (P N M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hP : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) P)
    (hN : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) N)
    (hflatP : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (P.X i))
    (hflatN : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (N.X i)) :
    ((TX.tensor.map ((derivedPullbackTensorIso f TX TY).hom.app
      ((DerivedCategory.Q.obj P), (DerivedCategory.Q.obj N)))).app
      ((derivedPullback f).obj (DerivedCategory.Q.obj M))) ≫
      ((TX.tensor.map ((TX.tensor.map (flatPullbackIso f P hP hflatP).hom).app
      ((derivedPullback f).obj (DerivedCategory.Q.obj N)) ≫
      (TX.tensor.obj (DerivedCategory.Q.obj ((pullbackComplex f).obj P))).map
      (flatPullbackIso f N hN hflatN).hom)).app
      ((derivedPullback f).obj (DerivedCategory.Q.obj M))) ≫
      ((TX.tensor.map (TX.comparison ((pullbackComplex f).obj P) ((pullbackComplex f).obj N)
      (kFlat_pullbackComplex' f P hP hflatP) (kFlat_pullbackComplex' f N hN hflatN)).hom).app
      ((derivedPullback f).obj (DerivedCategory.Q.obj M))) =
      ((TX.tensor.map ((derivedPullback f).map (TY.comparison P N hP hN).hom)).app
      ((derivedPullback f).obj (DerivedCategory.Q.obj M))) ≫
      ((TX.tensor.map (flatPullbackIso f
      ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj P |>.obj N)
      (Stacks.SheafOfModules.kFlat_tensorComplex Y.toRingedSite.O hP hN)
      (isFlat_tensorComplex_X_general Y.O P N hflatP hflatN)).hom).app
      ((derivedPullback f).obj (DerivedCategory.Q.obj M))) ≫
      ((TX.tensor.map (DerivedCategory.Q.map
      (Iso.hom (X := ((pullbackComplex f).obj
      ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj P |>.obj N)))
      (Y := ((Stacks.SheafOfModules.Tensor.tensorComplex X.toRingedSite.O).obj
      ((pullbackComplex f).obj P) |>.obj ((pullbackComplex f).obj N)))
      (pullbackTensorTotalComplexIso f P N)))).app
      ((derivedPullback f).obj (DerivedCategory.Q.obj M))) :=
  (map_app_eq_of_eq₃ TX.tensor ((derivedPullback f).obj (DerivedCategory.Q.obj M))
    (derivedPullbackTensorIso_hom_app_model_comp₂ f TX TY P N hP hN hflatP hflatN))

private theorem assoc_model_h5
    (P N M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hM : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) M)
    (hflatM : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (M.X i)) :
    ((TX.tensor.map (DerivedCategory.Q.map
      (Iso.hom (X := ((pullbackComplex f).obj
      ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj P |>.obj N)))
      (Y := ((Stacks.SheafOfModules.Tensor.tensorComplex X.toRingedSite.O).obj
      ((pullbackComplex f).obj P) |>.obj ((pullbackComplex f).obj N)))
      (pullbackTensorTotalComplexIso f P N)))).app
      ((derivedPullback f).obj (DerivedCategory.Q.obj M))) ≫
      ((TX.tensor.obj (DerivedCategory.Q.obj
      ((Stacks.SheafOfModules.Tensor.tensorComplex X.toRingedSite.O).obj
      ((pullbackComplex f).obj P) |>.obj ((pullbackComplex f).obj N)))).map
      (flatPullbackIso f M hM hflatM).hom) =
      ((TX.tensor.obj (DerivedCategory.Q.obj
      ((pullbackComplex f).obj
      ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj P |>.obj N)))).map
      (flatPullbackIso f M hM hflatM).hom) ≫
      ((TX.tensor.map (DerivedCategory.Q.map
      (Iso.hom (X := ((pullbackComplex f).obj
      ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj P |>.obj N)))
      (Y := ((Stacks.SheafOfModules.Tensor.tensorComplex X.toRingedSite.O).obj
      ((pullbackComplex f).obj P) |>.obj ((pullbackComplex f).obj N)))
      (pullbackTensorTotalComplexIso f P N)))).app
      (DerivedCategory.Q.obj ((pullbackComplex f).obj M))) :=
  ((TX.tensor.map (DerivedCategory.Q.map
    (Iso.hom (X := ((pullbackComplex f).obj
    ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj P |>.obj N)))
    (Y := ((Stacks.SheafOfModules.Tensor.tensorComplex X.toRingedSite.O).obj
    ((pullbackComplex f).obj P) |>.obj ((pullbackComplex f).obj N)))
    (pullbackTensorTotalComplexIso f P N)))).naturality (flatPullbackIso f M hM hflatM).hom).symm

private theorem assoc_model_h6
    (P N M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hP : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) P)
    (hN : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) N)
    (hM : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) M)
    (hflatP : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (P.X i))
    (hflatN : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (N.X i))
    (hflatM : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (M.X i)) :
    ((TX.tensor.map (DerivedCategory.Q.map
      (Iso.hom (X := ((pullbackComplex f).obj
      ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj P |>.obj N)))
      (Y := ((Stacks.SheafOfModules.Tensor.tensorComplex X.toRingedSite.O).obj
      ((pullbackComplex f).obj P) |>.obj ((pullbackComplex f).obj N)))
      (pullbackTensorTotalComplexIso f P N)))).app
      (DerivedCategory.Q.obj ((pullbackComplex f).obj M))) ≫
      (TX.comparison ((Stacks.SheafOfModules.Tensor.tensorComplex X.toRingedSite.O).obj
      ((pullbackComplex f).obj P) |>.obj ((pullbackComplex f).obj N)) ((pullbackComplex f).obj M)
      (Stacks.SheafOfModules.kFlat_tensorComplex X.toRingedSite.O
      (kFlat_pullbackComplex' f P hP hflatP) (kFlat_pullbackComplex' f N hN hflatN))
      (kFlat_pullbackComplex' f M hM hflatM)).hom =
      (TX.comparison ((pullbackComplex f).obj
      ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj P |>.obj N))
      ((pullbackComplex f).obj M)
      (kFlat_pullbackComplex' f
      ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj P |>.obj N)
      (Stacks.SheafOfModules.kFlat_tensorComplex Y.toRingedSite.O hP hN)
      (isFlat_tensorComplex_X_general Y.O P N hflatP hflatN))
      (kFlat_pullbackComplex' f M hM hflatM)).hom ≫
      (DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap
      (Iso.hom (X := ((pullbackComplex f).obj
      ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj P |>.obj N)))
      (Y := ((Stacks.SheafOfModules.Tensor.tensorComplex X.toRingedSite.O).obj
      ((pullbackComplex f).obj P) |>.obj ((pullbackComplex f).obj N)))
      (pullbackTensorTotalComplexIso f P N)) (𝟙 ((pullbackComplex f).obj M))
      (Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSite.O) (ComplexShape.up ℤ))) :=
  (TX.comparison_naturality_left
    (Iso.hom (X := ((pullbackComplex f).obj
    ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj P |>.obj N)))
    (Y := ((Stacks.SheafOfModules.Tensor.tensorComplex X.toRingedSite.O).obj
    ((pullbackComplex f).obj P) |>.obj ((pullbackComplex f).obj N)))
    (pullbackTensorTotalComplexIso f P N))
    (kFlat_pullbackComplex' f
    ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj P |>.obj N)
    (Stacks.SheafOfModules.kFlat_tensorComplex Y.toRingedSite.O hP hN)
    (isFlat_tensorComplex_X_general Y.O P N hflatP hflatN))
    (Stacks.SheafOfModules.kFlat_tensorComplex X.toRingedSite.O
    (kFlat_pullbackComplex' f P hP hflatP) (kFlat_pullbackComplex' f N hN hflatN))
    (kFlat_pullbackComplex' f M hM hflatM))

private theorem assoc_model_h7
    (P N M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hP : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) P)
    (hN : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) N) :
    ((derivedPullbackTensorIso f TX TY).hom.app
      (((TY.tensor.obj (DerivedCategory.Q.obj P)).obj (DerivedCategory.Q.obj N)),
      (DerivedCategory.Q.obj M))) ≫
      ((TX.tensor.map ((derivedPullback f).map (TY.comparison P N hP hN).hom)).app
      ((derivedPullback f).obj (DerivedCategory.Q.obj M))) =
      ((derivedPullback f).map
      ((TY.tensor.map (TY.comparison P N hP hN).hom).app (DerivedCategory.Q.obj M))) ≫
      ((derivedPullbackTensorIso f TX TY).hom.app
      ((DerivedCategory.Q.obj ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj
      P |>.obj N)), (DerivedCategory.Q.obj M))) :=
  (derivedPullbackTensorIso_hom_naturality_fst f TX TY (TY.comparison P N hP hN).hom
    (DerivedCategory.Q.obj M)).symm

private theorem assoc_model_h8
    (P N M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hP : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) P)
    (hN : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) N)
    (hM : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) M)
    (hflatP : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (P.X i))
    (hflatN : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (N.X i))
    (hflatM : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (M.X i)) :
    ((derivedPullbackTensorIso f TX TY).hom.app
      ((DerivedCategory.Q.obj ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj
      P |>.obj N)), (DerivedCategory.Q.obj M))) ≫
      (((TX.tensor.map (flatPullbackIso f
      ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj P |>.obj N)
      (Stacks.SheafOfModules.kFlat_tensorComplex Y.toRingedSite.O hP hN)
      (isFlat_tensorComplex_X_general Y.O P N hflatP hflatN)).hom).app
      ((derivedPullback f).obj (DerivedCategory.Q.obj M))) ≫
      ((TX.tensor.obj (DerivedCategory.Q.obj
      ((pullbackComplex f).obj
      ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj P |>.obj N)))).map
      (flatPullbackIso f M hM hflatM).hom)) ≫
      (TX.comparison ((pullbackComplex f).obj
      ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj P |>.obj N))
      ((pullbackComplex f).obj M)
      (kFlat_pullbackComplex' f
      ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj P |>.obj N)
      (Stacks.SheafOfModules.kFlat_tensorComplex Y.toRingedSite.O hP hN)
      (isFlat_tensorComplex_X_general Y.O P N hflatP hflatN))
      (kFlat_pullbackComplex' f M hM hflatM)).hom =
      ((derivedPullback f).map
      (TY.comparison ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj P |>.obj N)
      M (Stacks.SheafOfModules.kFlat_tensorComplex Y.toRingedSite.O hP hN) hM).hom) ≫
      (flatPullbackIso f ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj
      ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj P |>.obj N) |>.obj M)
      (Stacks.SheafOfModules.kFlat_tensorComplex Y.toRingedSite.O
      (Stacks.SheafOfModules.kFlat_tensorComplex Y.toRingedSite.O hP hN) hM)
      (isFlat_tensorComplex_X_general Y.O
      ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj P |>.obj N) M
      (isFlat_tensorComplex_X_general Y.O P N hflatP hflatN) hflatM)).hom ≫
      (DerivedCategory.Q.map (Iso.hom
      (X := ((pullbackComplex f).obj
      ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj
      ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj P |>.obj N) |>.obj M)))
      (Y := ((Stacks.SheafOfModules.Tensor.tensorComplex X.toRingedSite.O).obj
      ((pullbackComplex f).obj
      ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj P |>.obj N)) |>.obj
      ((pullbackComplex f).obj M)))
      (pullbackTensorTotalComplexIso f
      ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj P |>.obj N) M))) :=
  (derivedPullbackTensorIso_hom_app_model_comp₂ f TX TY
    ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj P |>.obj N) M
    (Stacks.SheafOfModules.kFlat_tensorComplex Y.toRingedSite.O hP hN) hM
    (isFlat_tensorComplex_X_general Y.O P N hflatP hflatN) hflatM)

/-- The left-hand side of the associativity of Stacks 07A4 on models, read through the
computations of `Lf^*` and `⊗^L`. -/
theorem derivedPullbackTensorIso_assoc_left_model
    (P N M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hP : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) P)
    (hN : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) N)
    (hM : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) M)
    (hflatP : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (P.X i))
    (hflatN : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (N.X i))
    (hflatM : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (M.X i)) :
    (((derivedPullback f).map
      (TY.associatorGeneral (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj N)
      (DerivedCategory.Q.obj M)).hom) ≫
      ((derivedPullbackTensorIso f TX TY).hom.app
      ((DerivedCategory.Q.obj P),
      ((TY.tensor.obj (DerivedCategory.Q.obj N)).obj (DerivedCategory.Q.obj M)))) ≫
      ((TX.tensor.obj ((derivedPullback f).obj (DerivedCategory.Q.obj P))).map
      ((derivedPullbackTensorIso f TX TY).hom.app
      ((DerivedCategory.Q.obj N), (DerivedCategory.Q.obj M))))) ≫
      ((((TX.tensor.map (flatPullbackIso f P hP hflatP).hom).app
      ((TX.tensor.obj ((derivedPullback f).obj (DerivedCategory.Q.obj N))).obj
      ((derivedPullback f).obj (DerivedCategory.Q.obj M)))) ≫
      ((TX.tensor.obj (DerivedCategory.Q.obj ((pullbackComplex f).obj P))).map
      ((TX.tensor.map (flatPullbackIso f N hN hflatN).hom).app
      ((derivedPullback f).obj (DerivedCategory.Q.obj M)) ≫
      (TX.tensor.obj (DerivedCategory.Q.obj ((pullbackComplex f).obj N))).map
      (flatPullbackIso f M hM hflatM).hom))) ≫
      ((TX.tensor.obj (DerivedCategory.Q.obj ((pullbackComplex f).obj P))).map
      (TX.comparison ((pullbackComplex f).obj N) ((pullbackComplex f).obj M)
      (kFlat_pullbackComplex' f N hN hflatN) (kFlat_pullbackComplex' f M hM hflatM)).hom) ≫
      (TX.comparison ((pullbackComplex f).obj P)
      ((Stacks.SheafOfModules.Tensor.tensorComplex X.toRingedSite.O).obj
      ((pullbackComplex f).obj N) |>.obj ((pullbackComplex f).obj M))
      (kFlat_pullbackComplex' f P hP hflatP)
      (Stacks.SheafOfModules.kFlat_tensorComplex X.toRingedSite.O
      (kFlat_pullbackComplex' f N hN hflatN) (kFlat_pullbackComplex' f M hM hflatM))).hom) =
      ((derivedPullback f).map
        ((TY.tensor.map (TY.comparison P N hP hN).hom).app (DerivedCategory.Q.obj M))) ≫
        ((derivedPullback f).map
        (TY.comparison ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj P |>.obj
        N) M (Stacks.SheafOfModules.kFlat_tensorComplex Y.toRingedSite.O hP hN) hM).hom) ≫
        (flatPullbackIso f ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj
        ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj P |>.obj N) |>.obj M)
        (Stacks.SheafOfModules.kFlat_tensorComplex Y.toRingedSite.O
        (Stacks.SheafOfModules.kFlat_tensorComplex Y.toRingedSite.O hP hN) hM)
        (isFlat_tensorComplex_X_general Y.O
        ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj P |>.obj N) M
        (isFlat_tensorComplex_X_general Y.O P N hflatP hflatN) hflatM)).hom ≫
        (DerivedCategory.Q.map ((pullbackComplex f).map
        (Stacks.SheafOfModules.DerivedTensorProduct.tensorComplexAssociator (Y := Y.toRingedSite)
        P N M).hom)) ≫ (DerivedCategory.Q.map
        (Iso.hom (X := ((pullbackComplex f).obj
        ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj P |>.obj
        ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj N |>.obj M))))
        (Y := ((Stacks.SheafOfModules.Tensor.tensorComplex X.toRingedSite.O).obj
        ((pullbackComplex f).obj P) |>.obj
        ((pullbackComplex f).obj
        ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj N |>.obj M))))
        (pullbackTensorTotalComplexIso f P
        ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj N |>.obj M)))) ≫
        (DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap (𝟙 ((pullbackComplex f).obj P))
        (Iso.hom (X := ((pullbackComplex f).obj
        ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj N |>.obj M)))
        (Y := ((Stacks.SheafOfModules.Tensor.tensorComplex X.toRingedSite.O).obj
        ((pullbackComplex f).obj N) |>.obj ((pullbackComplex f).obj M)))
        (pullbackTensorTotalComplexIso f N M))
        (Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSite.O) (ComplexShape.up ℤ))) :=
  assoc_left_assemble _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (assoc_model_s1 f TX TY P N M hP hflatP)
      (assoc_model_s2 f TX TY P N M hN hM hflatN hflatM)
      (assoc_model_s3 f TX TY P N M hP hN hM hflatP)
      (assoc_model_s4 f TX TY P N M hN hM)
      (assoc_model_s5 f TX P N M hP hN hM hflatP hflatN hflatM)
      (assoc_model_s6 f TX TY P N M hP hN hM hflatP hflatN hflatM)
      (assoc_model_s7 f TY P N M hP hN hM)
      (assoc_model_s8 f P N M hP hN hM hflatP hflatN hflatM)

/-- The right-hand side of the associativity of Stacks 07A4 on models, read through the
computations of `Lf^*` and `⊗^L`. -/
theorem derivedPullbackTensorIso_assoc_right_model
    (P N M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hP : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) P)
    (hN : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) N)
    (hM : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) M)
    (hflatP : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (P.X i))
    (hflatN : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (N.X i))
    (hflatM : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (M.X i)) :
    (((derivedPullbackTensorIso f TX TY).hom.app
      (((TY.tensor.obj (DerivedCategory.Q.obj P)).obj (DerivedCategory.Q.obj N)),
      (DerivedCategory.Q.obj M))) ≫
      ((TX.tensor.map ((derivedPullbackTensorIso f TX TY).hom.app
      ((DerivedCategory.Q.obj P), (DerivedCategory.Q.obj N)))).app
      ((derivedPullback f).obj (DerivedCategory.Q.obj M))) ≫
      (TX.associatorGeneral ((derivedPullback f).obj (DerivedCategory.Q.obj P))
      ((derivedPullback f).obj (DerivedCategory.Q.obj N))
      ((derivedPullback f).obj (DerivedCategory.Q.obj M))).hom) ≫
      ((((TX.tensor.map (flatPullbackIso f P hP hflatP).hom).app
      ((TX.tensor.obj ((derivedPullback f).obj (DerivedCategory.Q.obj N))).obj
      ((derivedPullback f).obj (DerivedCategory.Q.obj M)))) ≫
      ((TX.tensor.obj (DerivedCategory.Q.obj ((pullbackComplex f).obj P))).map
      ((TX.tensor.map (flatPullbackIso f N hN hflatN).hom).app
      ((derivedPullback f).obj (DerivedCategory.Q.obj M)) ≫
      (TX.tensor.obj (DerivedCategory.Q.obj ((pullbackComplex f).obj N))).map
      (flatPullbackIso f M hM hflatM).hom))) ≫
      ((TX.tensor.obj (DerivedCategory.Q.obj ((pullbackComplex f).obj P))).map
      (TX.comparison ((pullbackComplex f).obj N) ((pullbackComplex f).obj M)
      (kFlat_pullbackComplex' f N hN hflatN) (kFlat_pullbackComplex' f M hM hflatM)).hom) ≫
      (TX.comparison ((pullbackComplex f).obj P)
      ((Stacks.SheafOfModules.Tensor.tensorComplex X.toRingedSite.O).obj
      ((pullbackComplex f).obj N) |>.obj ((pullbackComplex f).obj M))
      (kFlat_pullbackComplex' f P hP hflatP)
      (Stacks.SheafOfModules.kFlat_tensorComplex X.toRingedSite.O
      (kFlat_pullbackComplex' f N hN hflatN) (kFlat_pullbackComplex' f M hM hflatM))).hom) =
      ((derivedPullback f).map
        ((TY.tensor.map (TY.comparison P N hP hN).hom).app (DerivedCategory.Q.obj M))) ≫
        ((derivedPullback f).map
        (TY.comparison ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj P |>.obj
        N) M (Stacks.SheafOfModules.kFlat_tensorComplex Y.toRingedSite.O hP hN) hM).hom) ≫
        (flatPullbackIso f ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj
        ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj P |>.obj N) |>.obj M)
        (Stacks.SheafOfModules.kFlat_tensorComplex Y.toRingedSite.O
        (Stacks.SheafOfModules.kFlat_tensorComplex Y.toRingedSite.O hP hN) hM)
        (isFlat_tensorComplex_X_general Y.O
        ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj P |>.obj N) M
        (isFlat_tensorComplex_X_general Y.O P N hflatP hflatN) hflatM)).hom ≫
        (DerivedCategory.Q.map (Iso.hom
        (X := ((pullbackComplex f).obj
        ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj
        ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj P |>.obj N) |>.obj M)))
        (Y := ((Stacks.SheafOfModules.Tensor.tensorComplex X.toRingedSite.O).obj
        ((pullbackComplex f).obj
        ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj P |>.obj N)) |>.obj
        ((pullbackComplex f).obj M)))
        (pullbackTensorTotalComplexIso f
        ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj P |>.obj N) M))) ≫
        (DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap
        (Iso.hom (X := ((pullbackComplex f).obj
        ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj P |>.obj N)))
        (Y := ((Stacks.SheafOfModules.Tensor.tensorComplex X.toRingedSite.O).obj
        ((pullbackComplex f).obj P) |>.obj ((pullbackComplex f).obj N)))
        (pullbackTensorTotalComplexIso f P N)) (𝟙 ((pullbackComplex f).obj M))
        (Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSite.O) (ComplexShape.up ℤ))) ≫
        (DerivedCategory.Q.map (Stacks.SheafOfModules.DerivedTensorProduct.tensorComplexAssociator
        (Y := X.toRingedSite) ((pullbackComplex f).obj P) ((pullbackComplex f).obj N)
        ((pullbackComplex f).obj M)).hom) :=
  assoc_right_assemble _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (assoc_model_h1 f TX P N M hP hN hM hflatP hflatN hflatM)
      (assoc_model_h2 f TX P N M hP hN hM hflatP hflatN hflatM)
      (assoc_model_h3 f TX P N M hP hN hM hflatP hflatN hflatM)
      (assoc_model_h4 f TX TY P N M hP hN hflatP hflatN)
      (assoc_model_h5 f TX P N M hM hflatM)
      (assoc_model_h6 f TX P N M hP hN hM hflatP hflatN hflatM)
      (assoc_model_h7 f TX TY P N M hP hN)
      (assoc_model_h8 f TX TY P N M hP hN hM hflatP hflatN hflatM)

omit [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)] in
attribute [local irreducible] Stacks.SheafOfModules.Tensor.sheafTensor in
private theorem assoc_complex_c1
    (P N M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    HEq (((pullbackModulesTensor f).mapHomologicalComplex _).map (α_ P N M).hom)
      ((pullbackComplex f).map
      (Stacks.SheafOfModules.DerivedTensorProduct.tensorComplexAssociator (Y := Y.toRingedSite)
      P N M).hom) :=
  HEq.rfl

omit [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)] in
attribute [local irreducible] Stacks.SheafOfModules.Tensor.sheafTensor in
private theorem assoc_complex_c2
    (P N M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    HEq (pullbackTensorComplexμ f P (N ⊗ M)).inv
      (Iso.hom (X := ((pullbackComplex f).obj
      ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj P |>.obj
      ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj N |>.obj M))))
      (Y := ((Stacks.SheafOfModules.Tensor.tensorComplex X.toRingedSite.O).obj
      ((pullbackComplex f).obj P) |>.obj
      ((pullbackComplex f).obj
      ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj N |>.obj M))))
      (pullbackTensorTotalComplexIso f P
      ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj N |>.obj M))) :=
  HEq.rfl

omit [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)] in
attribute [local irreducible] Stacks.SheafOfModules.Tensor.sheafTensor in
private theorem assoc_complex_c3
    (P N M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    HEq ((((pullbackModulesTensor f).mapHomologicalComplex _).obj P) ◁
      (pullbackTensorComplexμ f N M).inv)
      (HomologicalComplex.mapBifunctorMap (𝟙 ((pullbackComplex f).obj P))
      (Iso.hom (X := ((pullbackComplex f).obj
      ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj N |>.obj M)))
      (Y := ((Stacks.SheafOfModules.Tensor.tensorComplex X.toRingedSite.O).obj
      ((pullbackComplex f).obj N) |>.obj ((pullbackComplex f).obj M)))
      (pullbackTensorTotalComplexIso f N M))
      (Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSite.O) (ComplexShape.up ℤ)) :=
  HEq.rfl

omit [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)] in
attribute [local irreducible] Stacks.SheafOfModules.Tensor.sheafTensor in
private theorem assoc_complex_c4
    (P N M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    HEq (pullbackTensorComplexμ f (P ⊗ N) M).inv
      (Iso.hom (X := ((pullbackComplex f).obj
      ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj
      ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj P |>.obj N) |>.obj M)))
      (Y := ((Stacks.SheafOfModules.Tensor.tensorComplex X.toRingedSite.O).obj
      ((pullbackComplex f).obj
      ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj P |>.obj N)) |>.obj
      ((pullbackComplex f).obj M)))
      (pullbackTensorTotalComplexIso f
      ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj P |>.obj N) M)) :=
  HEq.rfl

omit [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)] in
attribute [local irreducible] Stacks.SheafOfModules.Tensor.sheafTensor in
private theorem assoc_complex_c5
    (P N M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    HEq ((pullbackTensorComplexμ f P N).inv ▷
      (((pullbackModulesTensor f).mapHomologicalComplex _).obj M))
      (HomologicalComplex.mapBifunctorMap
      (Iso.hom (X := ((pullbackComplex f).obj
      ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj P |>.obj N)))
      (Y := ((Stacks.SheafOfModules.Tensor.tensorComplex X.toRingedSite.O).obj
      ((pullbackComplex f).obj P) |>.obj ((pullbackComplex f).obj N)))
      (pullbackTensorTotalComplexIso f P N)) (𝟙 ((pullbackComplex f).obj M))
      (Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSite.O) (ComplexShape.up ℤ)) :=
  HEq.rfl

omit [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)] in
attribute [local irreducible] Stacks.SheafOfModules.Tensor.sheafTensor in
private theorem assoc_complex_c6
    (P N M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    HEq (α_ (((pullbackModulesTensor f).mapHomologicalComplex _).obj P)
      (((pullbackModulesTensor f).mapHomologicalComplex _).obj N)
      (((pullbackModulesTensor f).mapHomologicalComplex _).obj M)).hom
      (Stacks.SheafOfModules.DerivedTensorProduct.tensorComplexAssociator (Y := X.toRingedSite)
      ((pullbackComplex f).obj P) ((pullbackComplex f).obj N) ((pullbackComplex f).obj M)).hom :=
  HEq.rfl

omit [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)] in
attribute [local irreducible] Stacks.SheafOfModules.Tensor.sheafTensor in
private theorem assoc_complex_o1
    (P N M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    (((pullbackModulesTensor f).mapHomologicalComplex _).obj ((P ⊗ N) ⊗ M)) =
      ((pullbackComplex f).obj
      ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj
      ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj P |>.obj N) |>.obj M)) :=
  rfl

omit [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)] in
attribute [local irreducible] Stacks.SheafOfModules.Tensor.sheafTensor in
private theorem assoc_complex_o2
    (P N M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    (((pullbackModulesTensor f).mapHomologicalComplex _).obj (P ⊗ (N ⊗ M))) =
      ((pullbackComplex f).obj
      ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj P |>.obj
      ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj N |>.obj M))) :=
  rfl

omit [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)] in
attribute [local irreducible] Stacks.SheafOfModules.Tensor.sheafTensor in
private theorem assoc_complex_o3
    (P N M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    ((((pullbackModulesTensor f).mapHomologicalComplex _).obj P) ⊗
      (((pullbackModulesTensor f).mapHomologicalComplex _).obj (N ⊗ M))) =
      ((Stacks.SheafOfModules.Tensor.tensorComplex X.toRingedSite.O).obj
      ((pullbackComplex f).obj P) |>.obj
      ((pullbackComplex f).obj
      ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj N |>.obj M))) :=
  rfl

omit [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)] in
attribute [local irreducible] Stacks.SheafOfModules.Tensor.sheafTensor in
private theorem assoc_complex_o4
    (P N M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    ((((pullbackModulesTensor f).mapHomologicalComplex _).obj P) ⊗
      ((((pullbackModulesTensor f).mapHomologicalComplex _).obj N) ⊗
      (((pullbackModulesTensor f).mapHomologicalComplex _).obj M))) =
      (HomologicalComplex.mapBifunctor ((pullbackComplex f).obj P)
      ((Stacks.SheafOfModules.Tensor.tensorComplex X.toRingedSite.O).obj
      ((pullbackComplex f).obj N) |>.obj ((pullbackComplex f).obj M))
      (Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSite.O) (ComplexShape.up ℤ)) :=
  rfl

omit [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)] in
attribute [local irreducible] Stacks.SheafOfModules.Tensor.sheafTensor in
private theorem assoc_complex_o6
    (P N M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    ((((pullbackModulesTensor f).mapHomologicalComplex _).obj (P ⊗ N)) ⊗
      (((pullbackModulesTensor f).mapHomologicalComplex _).obj M)) =
      ((Stacks.SheafOfModules.Tensor.tensorComplex X.toRingedSite.O).obj
      ((pullbackComplex f).obj
      ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj P |>.obj N)) |>.obj
      ((pullbackComplex f).obj M)) :=
  rfl

omit [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)] in
attribute [local irreducible] Stacks.SheafOfModules.Tensor.sheafTensor in
private theorem assoc_complex_o7
    (P N M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    (((((pullbackModulesTensor f).mapHomologicalComplex _).obj P) ⊗
      (((pullbackModulesTensor f).mapHomologicalComplex _).obj N)) ⊗
      (((pullbackModulesTensor f).mapHomologicalComplex _).obj M)) =
      (HomologicalComplex.mapBifunctor
      ((Stacks.SheafOfModules.Tensor.tensorComplex X.toRingedSite.O).obj
      ((pullbackComplex f).obj P) |>.obj ((pullbackComplex f).obj N)) ((pullbackComplex f).obj M)
      (Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSite.O) (ComplexShape.up ℤ)) :=
  rfl

omit [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)] in
attribute [local irreducible] Stacks.SheafOfModules.Tensor.sheafTensor in
private theorem assoc_complex_o8
    (P N M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    ((((pullbackModulesTensor f).mapHomologicalComplex _).obj P) ⊗
      ((((pullbackModulesTensor f).mapHomologicalComplex _).obj N) ⊗
      (((pullbackModulesTensor f).mapHomologicalComplex _).obj M))) =
      ((Stacks.SheafOfModules.Tensor.tensorComplex X.toRingedSite.O).obj
      ((pullbackComplex f).obj P) |>.obj
      ((Stacks.SheafOfModules.Tensor.tensorComplex X.toRingedSite.O).obj
      ((pullbackComplex f).obj N) |>.obj ((pullbackComplex f).obj M))) :=
  rfl

omit [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)] in
attribute [local irreducible] Stacks.SheafOfModules.Tensor.sheafTensor in
private theorem assoc_complex_left
    (P N M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    HEq (((pullbackModulesTensor f).mapHomologicalComplex _).map (α_ P N M).hom ≫
      (pullbackTensorComplexμ f P (N ⊗ M)).inv ≫
      ((((pullbackModulesTensor f).mapHomologicalComplex _).obj P) ◁
      (pullbackTensorComplexμ f N M).inv))
      ((pullbackComplex f).map
      (Stacks.SheafOfModules.DerivedTensorProduct.tensorComplexAssociator (Y := Y.toRingedSite)
      P N M).hom ≫ (Iso.hom (X :=
      ((pullbackComplex f).obj
      ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj P |>.obj
      ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj N |>.obj M))))
      (Y := ((Stacks.SheafOfModules.Tensor.tensorComplex X.toRingedSite.O).obj
      ((pullbackComplex f).obj P) |>.obj
      ((pullbackComplex f).obj
      ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj N |>.obj M))))
      (pullbackTensorTotalComplexIso f P
      ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj N |>.obj M))) ≫
      (HomologicalComplex.mapBifunctorMap (𝟙 ((pullbackComplex f).obj P))
      (Iso.hom (X := ((pullbackComplex f).obj
      ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj N |>.obj M)))
      (Y := ((Stacks.SheafOfModules.Tensor.tensorComplex X.toRingedSite.O).obj
      ((pullbackComplex f).obj N) |>.obj ((pullbackComplex f).obj M)))
      (pullbackTensorTotalComplexIso f N M))
      (Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSite.O) (ComplexShape.up ℤ))) :=
  Stacks.SheafOfModules.comp₃_heq (assoc_complex_o1 f P N M) (assoc_complex_o2 f P N M)
    (assoc_complex_o3 f P N M) (assoc_complex_o4 f P N M) (assoc_complex_c1 f P N M)
    (assoc_complex_c2 f P N M) (assoc_complex_c3 f P N M)

omit [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)] in
attribute [local irreducible] Stacks.SheafOfModules.Tensor.sheafTensor in
private theorem assoc_complex_right
    (P N M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    HEq ((pullbackTensorComplexμ f (P ⊗ N) M).inv ≫
      ((pullbackTensorComplexμ f P N).inv ▷
      (((pullbackModulesTensor f).mapHomologicalComplex _).obj M)) ≫
      (α_ (((pullbackModulesTensor f).mapHomologicalComplex _).obj P)
      (((pullbackModulesTensor f).mapHomologicalComplex _).obj N)
      (((pullbackModulesTensor f).mapHomologicalComplex _).obj M)).hom)
      ((Iso.hom (X := ((pullbackComplex f).obj
      ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj
      ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj P |>.obj N) |>.obj M)))
      (Y := ((Stacks.SheafOfModules.Tensor.tensorComplex X.toRingedSite.O).obj
      ((pullbackComplex f).obj
      ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj P |>.obj N)) |>.obj
      ((pullbackComplex f).obj M)))
      (pullbackTensorTotalComplexIso f
      ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj P |>.obj N) M)) ≫
      (HomologicalComplex.mapBifunctorMap
      (Iso.hom (X := ((pullbackComplex f).obj
      ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj P |>.obj N)))
      (Y := ((Stacks.SheafOfModules.Tensor.tensorComplex X.toRingedSite.O).obj
      ((pullbackComplex f).obj P) |>.obj ((pullbackComplex f).obj N)))
      (pullbackTensorTotalComplexIso f P N)) (𝟙 ((pullbackComplex f).obj M))
      (Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSite.O) (ComplexShape.up ℤ)) ≫
      (Stacks.SheafOfModules.DerivedTensorProduct.tensorComplexAssociator (Y := X.toRingedSite)
      ((pullbackComplex f).obj P) ((pullbackComplex f).obj N) ((pullbackComplex f).obj M)).hom) :=
  Stacks.SheafOfModules.comp₃_heq (assoc_complex_o1 f P N M) (assoc_complex_o6 f P N M)
    (assoc_complex_o7 f P N M) (assoc_complex_o8 f P N M) (assoc_complex_c4 f P N M)
    (assoc_complex_c5 f P N M) (assoc_complex_c6 f P N M)

omit [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)] in
attribute [local irreducible] Stacks.SheafOfModules.Tensor.sheafTensor in
/-- The comparison of total tensor complexes of Stacks 07A4 is associative, in the spelling of
`Stacks.SheafOfModules.Tensor.tensorComplex` and of `pullbackTensorTotalComplexIso`. -/
theorem pullbackTensorTotalComplexIso_associativity
    (P N M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    (pullbackComplex f).map (Stacks.SheafOfModules.DerivedTensorProduct.tensorComplexAssociator
      (Y := Y.toRingedSite) P N M).hom ≫
      (Iso.hom (X := ((pullbackComplex f).obj
      ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj P |>.obj
      ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj N |>.obj M))))
      (Y := ((Stacks.SheafOfModules.Tensor.tensorComplex X.toRingedSite.O).obj
      ((pullbackComplex f).obj P) |>.obj
      ((pullbackComplex f).obj
      ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj N |>.obj M))))
      (pullbackTensorTotalComplexIso f P
      ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj N |>.obj M))) ≫
      (HomologicalComplex.mapBifunctorMap (𝟙 ((pullbackComplex f).obj P))
      (Iso.hom (X := ((pullbackComplex f).obj
      ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj N |>.obj M)))
      (Y := ((Stacks.SheafOfModules.Tensor.tensorComplex X.toRingedSite.O).obj
      ((pullbackComplex f).obj N) |>.obj ((pullbackComplex f).obj M)))
      (pullbackTensorTotalComplexIso f N M))
      (Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSite.O) (ComplexShape.up ℤ)) =
      (Iso.hom (X := ((pullbackComplex f).obj
        ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj
        ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj P |>.obj N) |>.obj M)))
        (Y := ((Stacks.SheafOfModules.Tensor.tensorComplex X.toRingedSite.O).obj
        ((pullbackComplex f).obj
        ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj P |>.obj N)) |>.obj
        ((pullbackComplex f).obj M)))
        (pullbackTensorTotalComplexIso f
        ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj P |>.obj N) M)) ≫
        (HomologicalComplex.mapBifunctorMap
        (Iso.hom (X := ((pullbackComplex f).obj
        ((Stacks.SheafOfModules.Tensor.tensorComplex Y.toRingedSite.O).obj P |>.obj N)))
        (Y := ((Stacks.SheafOfModules.Tensor.tensorComplex X.toRingedSite.O).obj
        ((pullbackComplex f).obj P) |>.obj ((pullbackComplex f).obj N)))
        (pullbackTensorTotalComplexIso f P N)) (𝟙 ((pullbackComplex f).obj M))
        (Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSite.O) (ComplexShape.up ℤ)) ≫
        (Stacks.SheafOfModules.DerivedTensorProduct.tensorComplexAssociator (Y := X.toRingedSite)
        ((pullbackComplex f).obj P) ((pullbackComplex f).obj N) ((pullbackComplex f).obj M)).hom :=
  eq_of_heq ((assoc_complex_left f P N M).symm.trans
    ((heq_of_eq (pullbackTensorComplexμ_inv_associativity f P N M)).trans
      (assoc_complex_right f P N M)))

/-- Cancelling an isomorphism after reading two morphisms on a common factorisation. -/
private lemma eq_of_comp_eq_of_eq {𝒟 : Type*} [Category 𝒟] {A B E R₁ R₂ R₃ V W V' W' : 𝒟}
    {x y : A ⟶ B} {Ω : B ⟶ E} [Mono Ω] {r₁ : A ⟶ R₁} {r₂ : R₁ ⟶ R₂} {ι : R₂ ⟶ R₃}
    {p₁ : R₃ ⟶ V} {p₂ : V ⟶ W} {p₃ : W ⟶ E} {p₁' : R₃ ⟶ V'} {p₂' : V' ⟶ W'} {p₃' : W' ⟶ E}
    (hx : x ≫ Ω = r₁ ≫ r₂ ≫ ι ≫ p₁ ≫ p₂ ≫ p₃) (hy : y ≫ Ω = r₁ ≫ r₂ ≫ ι ≫ p₁' ≫ p₂' ≫ p₃')
    (h : p₁ ≫ p₂ ≫ p₃ = p₁' ≫ p₂' ≫ p₃') : x = y := by
  rw [← cancel_mono Ω, hx, hy, h]

/-- The isomorphism of Stacks 07A4 is compatible with the associators of the derived tensor
products, on K-flat complexes with flat terms. -/
theorem derivedPullbackTensorIso_associativity_model
    (P N M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hP : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) P)
    (hN : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) N)
    (hM : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) M)
    (hflatP : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (P.X i))
    (hflatN : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (N.X i))
    (hflatM : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (M.X i)) :
    (((derivedPullback f).map
      (TY.associatorGeneral (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj N)
      (DerivedCategory.Q.obj M)).hom) ≫
      ((derivedPullbackTensorIso f TX TY).hom.app
      ((DerivedCategory.Q.obj P),
      ((TY.tensor.obj (DerivedCategory.Q.obj N)).obj (DerivedCategory.Q.obj M)))) ≫
      ((TX.tensor.obj ((derivedPullback f).obj (DerivedCategory.Q.obj P))).map
      ((derivedPullbackTensorIso f TX TY).hom.app
      ((DerivedCategory.Q.obj N), (DerivedCategory.Q.obj M))))) =
      (((derivedPullbackTensorIso f TX TY).hom.app
      (((TY.tensor.obj (DerivedCategory.Q.obj P)).obj (DerivedCategory.Q.obj N)),
      (DerivedCategory.Q.obj M))) ≫
      ((TX.tensor.map ((derivedPullbackTensorIso f TX TY).hom.app
      ((DerivedCategory.Q.obj P), (DerivedCategory.Q.obj N)))).app
      ((derivedPullback f).obj (DerivedCategory.Q.obj M))) ≫
      (TX.associatorGeneral ((derivedPullback f).obj (DerivedCategory.Q.obj P))
      ((derivedPullback f).obj (DerivedCategory.Q.obj N))
      ((derivedPullback f).obj (DerivedCategory.Q.obj M))).hom) :=
  eq_of_comp_eq_of_eq (derivedPullbackTensorIso_assoc_left_model f TX TY P N M hP hN hM hflatP
    hflatN hflatM)
    (derivedPullbackTensorIso_assoc_right_model f TX TY P N M hP hN hM hflatP hflatN hflatM)
    (map_eq_of_eq₃ DerivedCategory.Q (pullbackTensorTotalComplexIso_associativity f P N M))

/-- The isomorphism of Stacks 07A4 is compatible with the associators of `⊗^L`: for
`A, B, E ∈ D(O')`, the two isomorphisms
`Lf^*((A ⊗^L B) ⊗^L E) ≅ Lf^*A ⊗^L (Lf^*B ⊗^L Lf^*E)` built from 07A4 and the associators agree.
The associators are those of the monoidal structure of Tag 0FPT re-seated on the two derived
tensor products (`Stacks.SheafOfModules.DerivedTensorProduct.associatorGeneral`). -/
theorem derivedPullbackTensorIso_associativity
    (A B E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :
    (derivedPullback f).map (TY.associatorGeneral A B E).hom ≫
        (derivedPullbackTensorIso f TX TY).hom.app (A, (TY.tensor.obj B).obj E) ≫
        (TX.tensor.obj ((derivedPullback f).obj A)).map
          ((derivedPullbackTensorIso f TX TY).hom.app (B, E)) =
      (derivedPullbackTensorIso f TX TY).hom.app ((TY.tensor.obj A).obj B, E) ≫
        (TX.tensor.map ((derivedPullbackTensorIso f TX TY).hom.app (A, B))).app
          ((derivedPullback f).obj E) ≫
        (TX.associatorGeneral ((derivedPullback f).obj A) ((derivedPullback f).obj B)
          ((derivedPullback f).obj E)).hom := by
  have := Stacks.Sheaves.DerivedPullback.flatKFlatModelsQGeneral_isLocalization Y
  have := Localization.essSurj (Stacks.Sheaves.DerivedPullback.flatKFlatModelsQGeneral Y)
    (Stacks.Sheaves.DerivedPullback.flatKFlatModelsWGeneral Y)
  let P := (Stacks.Sheaves.DerivedPullback.flatKFlatModelsQGeneral Y).objPreimage
  let e := fun Z ↦ (DerivedCategory.quotientCompQhIso _).symm.app (P Z).obj.as ≪≫
    (Stacks.Sheaves.DerivedPullback.flatKFlatModelsQGeneral Y).objObjPreimageIso Z
  exact CategoryTheory.PullbackInternalHom.assoc_of_iso TY.tensor TX.tensor
    (derivedPullbackTensorIso f TX TY) TY.associatorGeneral TX.associatorGeneral
    (fun a b e ↦ TY.associatorGeneral_naturality a b e)
      (fun a b e ↦ TX.associatorGeneral_naturality a b e)
    (e A).symm (e B).symm (e E).symm
    (derivedPullbackTensorIso_associativity_model f TX TY (P A).obj.as (P B).obj.as (P E).obj.as
      (P A).property.1 (P B).property.1 (P E).property.1 (P A).property.2 (P B).property.2
      (P E).property.2)

end Models

end Stacks.Cohomology.DerivedPullbackOfToposHom

end
