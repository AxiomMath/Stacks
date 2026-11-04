module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorComposition
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorSquare
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ModelComparison

/-!
# Stacks 07A4 at the two canonical derived tensor products

A ringed site `X` carries two canonical derived tensor products of Stacks 06YU: that of
`Stacks.DerivedTensor.RingedSite` over its structure sheaf and that of `Stacks.SheafOfModules`
over the site, identified by
`Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctorIsoSheafOfModules`. For a morphism
`f` of ringed topoi there are accordingly two isomorphisms of Stacks 07A4: the one of
`Stacks.Sheaves.DerivedPullback.OfToposHom`, stated at the first tensor product, and the one of
`Stacks.Cohomology.DerivedPullbackOfToposHom`, which takes any derived tensor product on each
side and is applied here at the second. This file shows that the identification of the two
tensor products carries one to the other.

## Main results

* `RingedSite.derivedTensorProductFunctorIsoSheafOfModules_hom_app_app_comparison`:
  on a pair of K-flat complexes the identification of the two tensor products is the K-flat
  comparison of the first followed by the inverse of that of the second.
* `Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso_sheafOfModulesTensor`:
  the two isomorphisms of Stacks 07A4 agree across the identification.

## References

* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Prod

universe u

namespace Stacks.DerivedTensor.RingedSite

variable (X : AlgebraicGeometry.RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory (Modules X.O)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (Modules X.O) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]

/-- The arrow algebra of `derivedTensorProductFunctorIsoSheafOfModules_hom_app_app_comparison`:
two isomorphisms out of a common object `M`, each described through a common map `cR` and a
comparison, compose to the comparison of the first followed by the inverse of the second. -/
private lemma kappa_chase {C : Type*} [Category C] {M T₁ T₂ Z : C} (i₂ : M ≅ T₂) (i₁ : M ⟶ T₁)
    (cR : M ⟶ Z) (c₂ : T₂ ≅ Z) (c₁ : T₁ ≅ Z) (h₁ : i₁ = cR ≫ c₁.inv)
    (h₂ : i₂.hom = cR ≫ c₂.inv) : (i₂.inv ≫ i₁) ≫ c₁.hom = c₂.hom := by
  subst h₁
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.inv_comp_eq, h₂,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- **The identification of the two canonical derived tensor products on K-flat complexes**: it
is the K-flat comparison of `Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct`
followed by the inverse of that of `Stacks.SheafOfModules.canonicalDerivedTensorProduct`. -/
theorem derivedTensorProductFunctorIsoSheafOfModules_hom_app_app_comparison
    (K L : CochainComplex (Modules X.O) ℤ)
    (hK : Stacks.SheafOfModules.KFlat.KFlat X.O K) (hL : Stacks.SheafOfModules.KFlat.KFlat X.O L) :
    ((derivedTensorProductFunctorIsoSheafOfModules X).hom.app (DerivedCategory.Q.obj K)).app
          (DerivedCategory.Q.obj L) ≫
        ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparison K L hK hL).hom =
      ((canonicalDerivedTensorProduct X.O).comparison K L hK hL).hom := by
  have h₁ := Stacks.SheafOfModules.DerivedMonoidal.derivedBifunctorTensorIso_hom_app_app X.O
    (Stacks.SheafOfModules.DerivedTensorProduct.toRingedSiteDerivedTensorProduct
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct X)) K L hK hL
  have h₂ := Stacks.SheafOfModules.DerivedMonoidal.derivedBifunctorTensorIso_hom_app_app X.O
    (canonicalDerivedTensorProduct X.O) K L hK hL
  have h₀ : ((derivedTensorProductFunctorIsoSheafOfModules X).hom.app
        (DerivedCategory.Q.obj K)).app (DerivedCategory.Q.obj L) =
      ((Stacks.SheafOfModules.DerivedMonoidal.derivedBifunctorTensorIso X.O
          (canonicalDerivedTensorProduct X.O)).inv.app
          (DerivedCategory.Q.obj K)).app (DerivedCategory.Q.obj L) ≫
        ((Stacks.SheafOfModules.DerivedMonoidal.derivedBifunctorTensorIso X.O
          (Stacks.SheafOfModules.DerivedTensorProduct.toRingedSiteDerivedTensorProduct
            (Stacks.SheafOfModules.canonicalDerivedTensorProduct X))).hom.app
          (DerivedCategory.Q.obj K)).app (DerivedCategory.Q.obj L) := rfl
  rw [h₀]
  exact kappa_chase (((Stacks.SheafOfModules.DerivedMonoidal.derivedBifunctorTensorIso X.O
    (canonicalDerivedTensorProduct X.O)).app _).app _) _ _
    ((canonicalDerivedTensorProduct X.O).comparison K L hK hL) _ h₁ h₂

/-- The inverse of the identification of the two canonical derived tensor products on K-flat
complexes. -/
theorem derivedTensorProductFunctorIsoSheafOfModules_inv_app_app_comparison
    (K L : CochainComplex (Modules X.O) ℤ)
    (hK : Stacks.SheafOfModules.KFlat.KFlat X.O K) (hL : Stacks.SheafOfModules.KFlat.KFlat X.O L) :
    ((derivedTensorProductFunctorIsoSheafOfModules X).inv.app (DerivedCategory.Q.obj K)).app
          (DerivedCategory.Q.obj L) ≫
        ((canonicalDerivedTensorProduct X.O).comparison K L hK hL).hom =
      ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparison K L hK hL).hom :=
  (Iso.inv_comp_eq (((derivedTensorProductFunctorIsoSheafOfModules X).app _).app _)).2
    (derivedTensorProductFunctorIsoSheafOfModules_hom_app_app_comparison X K L hK hL).symm

end Stacks.DerivedTensor.RingedSite

namespace Stacks.Sheaves.DerivedPullback.OfToposHom

open AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackOfToposHom (derivedPullback)

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance]
  Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy

variable {X Y : AlgebraicGeometry.RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)]
  (f : AlgebraicGeometry.RingedToposHom X Y)

/-- The arrow algebra of `derivedPullbackTensorIso_sheafOfModulesTensor_app_model`: both sides
are compared after the monomorphism `m`, on the left through the description `hα` of the general
comparison followed by the naturality `hκ` of the identification and its value `hc` on K-flat
complexes, on the right through the description `hβ` of the other comparison and the value `hc'`
of the identification upstairs. -/
private lemma model_chase {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A₀ A₁ A₃ : C} {B₀ B₁ B₂ B₃ B₄ : D}
    (kY : A₀ ⟶ A₁) (c₂Y : A₁ ⟶ A₃) (c₁Y : A₀ ⟶ A₃) (gen : F.obj A₀ ⟶ B₀) (kX : B₀ ⟶ B₁)
    (ot : F.obj A₁ ⟶ B₁) (p₁ : B₀ ⟶ B₂) (p₂ : B₁ ⟶ B₃) (kX' : B₂ ⟶ B₃) (c₁X : B₂ ⟶ B₄)
    (c₂X : B₃ ⟶ B₄) (r : F.obj A₃ ⟶ B₄) (m : B₁ ⟶ B₄) [Mono m]
    (hm : m = p₂ ≫ c₂X) (hκY : kY ≫ c₂Y = c₁Y) (hκ : kX ≫ p₂ = p₁ ≫ kX')
    (hc : kX' ≫ c₂X = c₁X) (hα : gen ≫ p₁ ≫ c₁X = F.map c₁Y ≫ r)
    (hβ : ot ≫ p₂ ≫ c₂X = F.map c₂Y ≫ r) :
    gen ≫ kX = F.map kY ≫ ot := by
  refine (cancel_mono m).1 ?_
  rw [hm, Category.assoc, reassoc_of% hκ, hc, hα, Category.assoc, hβ, ← Functor.map_comp_assoc,
    hκY]

/-- The computation of Stacks 06YY on a K-flat complex with flat terms is the same isomorphism in
the two developments. -/
private theorem flatPullbackIso_eq_general
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) K)
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i)) :
    flatPullbackIso f K hK hflat =
      Stacks.Cohomology.DerivedPullbackOfToposHom.flatPullbackIso f K hK hflat :=
  rfl

omit [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)] in
/-- The comparison of total tensor complexes of Stacks 03EL is the same isomorphism in the two
developments. -/
private theorem pullbackTensorTotalIso_eq_general
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    pullbackTensorTotalIso f.toModulesHom K L =
      Stacks.Cohomology.DerivedPullbackOfToposHom.pullbackTensorTotalComplexIso f K L :=
  rfl

/-- Cancelling an isomorphism and its inverse after a three-fold composite. -/
private lemma comp_inv_hom_cancel {C : Type*} [Category C] {W V₁ V₂ Z P Q : C} (y₁ : W ⟶ V₁)
    (y₂ : V₁ ⟶ V₂) (y₃ : V₂ ⟶ Z) (c : Q ≅ Z) (a : P ≅ Q) :
    (y₁ ≫ y₂ ≫ y₃ ≫ c.inv ≫ a.inv) ≫ a.hom ≫ c.hom = y₁ ≫ y₂ ≫ y₃ := by
  simp

/-- The naturality of the identification of the two tensor products downstairs, along the
computations of Stacks 06YY on two K-flat complexes with flat terms. -/
private theorem app_model_naturality
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) K)
    (hL : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) L)
    (hflatK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i))
    (hflatL : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (L.X i)) :
    ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctorIsoSheafOfModules
          X.toRingedSite).inv.app ((derivedPullback f).obj (DerivedCategory.Q.obj K))).app
          ((derivedPullback f).obj (DerivedCategory.Q.obj L)) ≫
        (Functor.uncurry.obj
          (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O)).map
          ((flatPullbackIso f K hK hflatK).hom ×ₘ (flatPullbackIso f L hL hflatL).hom) =
      (Functor.uncurry.obj
          (Stacks.SheafOfModules.canonicalDerivedTensorProduct X.toRingedSite).tensor).map
          ((flatPullbackIso f K hK hflatK).hom ×ₘ (flatPullbackIso f L hL hflatL).hom) ≫
        ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctorIsoSheafOfModules
          X.toRingedSite).inv.app
            (DerivedCategory.Q.obj
              ((Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom.pullbackComplex
                f).obj K))).app
          (DerivedCategory.Q.obj
            ((Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom.pullbackComplex f).obj L)) :=
  ((Functor.uncurry.map
    (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctorIsoSheafOfModules
      X.toRingedSite).inv).naturality
      ((flatPullbackIso f K hK hflatK).hom ×ₘ (flatPullbackIso f L hL hflatL).hom)).symm

/-- The comparison of `Stacks.Sheaves.DerivedPullback.OfToposHom` on a pair of K-flat complexes
with flat terms, followed by the computations of Stacks 06YY and the K-flat comparison. -/
private theorem app_model_ofToposHom
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) K)
    (hL : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) L)
    (hflatK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i))
    (hflatL : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (L.X i)) :
    (derivedPullbackTensorIso f).hom.app
          (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) ≫
        (Functor.uncurry.obj
          (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O)).map
          ((flatPullbackIso f K hK hflatK).hom ×ₘ (flatPullbackIso f L hL hflatL).hom) ≫
        ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).comparison
          _ _ ((Stacks.SheafOfModules.KFlat.kFlat_iff_kFlatBifunctor X.O _).2
          (kFlatBifunctor_pullbackComplex f K hK hflatK))
          ((Stacks.SheafOfModules.KFlat.kFlat_iff_kFlatBifunctor X.O _).2
          (kFlatBifunctor_pullbackComplex f L hL hflatL))).hom =
      (derivedPullback f).map
          ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct Y.O).comparison
            K L ((Stacks.SheafOfModules.KFlat.kFlat_iff_kFlatBifunctor Y.O K).2 hK)
            ((Stacks.SheafOfModules.KFlat.kFlat_iff_kFlatBifunctor Y.O L).2 hL)).hom ≫
        (flatPullbackIso f (HomologicalComplex.mapBifunctor K L
            (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) (ComplexShape.up ℤ))
          (Stacks.Cohomology.DerivedPullbackOfToposHom.kFlat_mapBifunctor hK hL)
          (Stacks.Cohomology.DerivedPullbackOfToposHom.isFlat_mapBifunctor_X K L hflatK
            hflatL)).hom ≫
        DerivedCategory.Q.map (pullbackTensorTotalIso f.toModulesHom K L).hom := by
  rw [derivedPullbackTensorIso_hom_app_model_eq f K L hK hL hflatK hflatL]
  exact comp_inv_hom_cancel _ _ _ _ ((Functor.uncurry.obj
    (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O)).mapIso
      ((flatPullbackIso f K hK hflatK).prod (flatPullbackIso f L hL hflatL)))

/-- The comparison of `Stacks.Cohomology.DerivedPullbackOfToposHom` on a pair of K-flat complexes
with flat terms, followed by the computations of Stacks 06YY and the K-flat comparison, written
with the computations of `Stacks.Sheaves.DerivedPullback.OfToposHom`. -/
private theorem app_model_general
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) K)
    (hL : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) L)
    (hflatK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i))
    (hflatL : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (L.X i)) :
    (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackTensorIso f
          (Stacks.SheafOfModules.canonicalDerivedTensorProduct X.toRingedSite)
          (Stacks.SheafOfModules.canonicalDerivedTensorProduct Y.toRingedSite)).hom.app
          (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) ≫
        (Functor.uncurry.obj
          (Stacks.SheafOfModules.canonicalDerivedTensorProduct X.toRingedSite).tensor).map
          ((flatPullbackIso f K hK hflatK).hom ×ₘ (flatPullbackIso f L hL hflatL).hom) ≫
        ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X.toRingedSite).comparison
          ((Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom.pullbackComplex f).obj K)
          ((Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom.pullbackComplex f).obj L)
          (Stacks.Cohomology.DerivedPullbackOfToposHom.kFlat_pullbackComplex' f K hK hflatK)
          (Stacks.Cohomology.DerivedPullbackOfToposHom.kFlat_pullbackComplex' f L hL hflatL)).hom =
      (derivedPullback f).map
          ((Stacks.SheafOfModules.canonicalDerivedTensorProduct Y.toRingedSite).comparison
            K L hK hL).hom ≫
        (flatPullbackIso f (HomologicalComplex.mapBifunctor K L
            (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) (ComplexShape.up ℤ))
          (Stacks.Cohomology.DerivedPullbackOfToposHom.kFlat_mapBifunctor hK hL)
          (Stacks.Cohomology.DerivedPullbackOfToposHom.isFlat_mapBifunctor_X K L hflatK
            hflatL)).hom ≫
        DerivedCategory.Q.map (pullbackTensorTotalIso f.toModulesHom K L).hom := by
  have hα :=
    Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackTensorIso_hom_app_comp_comparison
      f (Stacks.SheafOfModules.canonicalDerivedTensorProduct X.toRingedSite)
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct Y.toRingedSite) K L hK hL hflatK hflatL
  rwa [← flatPullbackIso_eq_general f K, ← flatPullbackIso_eq_general f L,
    ← flatPullbackIso_eq_general f, ← pullbackTensorTotalIso_eq_general] at hα

omit [Y.J.HasSheafCompose (forget RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})] [HasSheafify Y.J (Type u)] in
/-- The identification of the two tensor products upstairs on K-flat complexes, in the spelling
of the two comparisons of Stacks 07A4. -/
private theorem app_model_kappa_target
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) K)
    (hL : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) L) :
    ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctorIsoSheafOfModules
          Y.toRingedSite).inv.app (DerivedCategory.Q.obj K)).app (DerivedCategory.Q.obj L) ≫
        ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct Y.O).comparison
          K L ((Stacks.SheafOfModules.KFlat.kFlat_iff_kFlatBifunctor Y.O K).2 hK)
          ((Stacks.SheafOfModules.KFlat.kFlat_iff_kFlatBifunctor Y.O L).2 hL)).hom =
      ((Stacks.SheafOfModules.canonicalDerivedTensorProduct Y.toRingedSite).comparison
        K L hK hL).hom :=
  DerivedTensor.RingedSite.derivedTensorProductFunctorIsoSheafOfModules_inv_app_app_comparison
    Y.toRingedSite K L _ _

/-- **The two isomorphisms of Stacks 07A4 agree on a pair of K-flat complexes with flat
terms**, across the identification of the two canonical derived tensor products. -/
theorem derivedPullbackTensorIso_sheafOfModulesTensor_app_model
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) K)
    (hL : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) L)
    (hflatK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i))
    (hflatL : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (L.X i)) :
    (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackTensorIso f
          (Stacks.SheafOfModules.canonicalDerivedTensorProduct X.toRingedSite)
          (Stacks.SheafOfModules.canonicalDerivedTensorProduct Y.toRingedSite)).hom.app
          (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) ≫
        ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctorIsoSheafOfModules
          X.toRingedSite).inv.app ((derivedPullback f).obj (DerivedCategory.Q.obj K))).app
          ((derivedPullback f).obj (DerivedCategory.Q.obj L)) =
      (derivedPullback f).map
          (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctorIsoSheafOfModules
            Y.toRingedSite).inv.app (DerivedCategory.Q.obj K)).app (DerivedCategory.Q.obj L)) ≫
        (derivedPullbackTensorIso f).hom.app
          (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) :=
  model_chase (derivedPullback f) _ _ _ _ _ _ _ _ _ _ _ _
    (m := ((Functor.uncurry.obj
        (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O)).mapIso
        ((flatPullbackIso f K hK hflatK).prod (flatPullbackIso f L hL hflatL)) ≪≫
      (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).comparison
        _ _ ((Stacks.SheafOfModules.KFlat.kFlat_iff_kFlatBifunctor X.O _).2
          (kFlatBifunctor_pullbackComplex f K hK hflatK))
        ((Stacks.SheafOfModules.KFlat.kFlat_iff_kFlatBifunctor X.O _).2
          (kFlatBifunctor_pullbackComplex f L hL hflatL))).hom) rfl
    (app_model_kappa_target K L hK hL)
    (app_model_naturality f K L hK hL hflatK hflatL)
    (DerivedTensor.RingedSite.derivedTensorProductFunctorIsoSheafOfModules_inv_app_app_comparison
      X.toRingedSite _ _ _ _)
    (app_model_general f K L hK hL hflatK hflatL) (app_model_ofToposHom f K L hK hL hflatK hflatL)

/-- **The two isomorphisms of Stacks 07A4 agree** across the identification
`Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctorIsoSheafOfModules` of the two
canonical derived tensor products: the comparison of `Stacks.Cohomology.DerivedPullbackOfToposHom`
at the derived tensor products of `Stacks.SheafOfModules`, read through the identification
downstairs, is the comparison of `Stacks.Sheaves.DerivedPullback.OfToposHom` after `Lf^*` of the
identification upstairs. -/
theorem derivedPullbackTensorIso_sheafOfModulesTensor :
    (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackTensorIso f
          (Stacks.SheafOfModules.canonicalDerivedTensorProduct X.toRingedSite)
          (Stacks.SheafOfModules.canonicalDerivedTensorProduct Y.toRingedSite)).hom ≫
        Functor.whiskerLeft ((derivedPullback f).prod (derivedPullback f))
          (Functor.uncurry.map
            (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctorIsoSheafOfModules
              X.toRingedSite).inv) =
      Functor.whiskerRight
          (Functor.uncurry.map
            (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctorIsoSheafOfModules
              Y.toRingedSite).inv) (derivedPullback f) ≫
        (derivedPullbackTensorIso f).hom := by
  have := Stacks.Sheaves.DerivedPullback.flatKFlatModelPairsQGeneral_isLocalization Y
  refine Localization.natTrans_ext (Stacks.Sheaves.DerivedPullback.flatKFlatModelPairsQGeneral Y)
    (Stacks.Sheaves.DerivedPullback.flatKFlatModelPairsWGeneral Y) (fun P ↦ ?_)
  exact Stacks.Cohomology.DerivedPullbackOfToposHom.app_eq_of_iso' _ _
    (Stacks.Sheaves.DerivedPullback.flatKFlatModelPairsIsoGeneral Y P)
    (derivedPullbackTensorIso_sheafOfModulesTensor_app_model f P.1.obj.as P.2.obj.as
      P.1.property.1 P.2.property.1 P.1.property.2 P.2.property.2)

/-- **The two isomorphisms of Stacks 07A4 agree**, pointwise. -/
theorem derivedPullbackTensorIso_sheafOfModulesTensor_app
    (A B : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :
    (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackTensorIso f
          (Stacks.SheafOfModules.canonicalDerivedTensorProduct X.toRingedSite)
          (Stacks.SheafOfModules.canonicalDerivedTensorProduct Y.toRingedSite)).hom.app (A, B) ≫
        ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctorIsoSheafOfModules
          X.toRingedSite).inv.app ((derivedPullback f).obj A)).app ((derivedPullback f).obj B) =
      (derivedPullback f).map
          (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctorIsoSheafOfModules
            Y.toRingedSite).inv.app A).app B) ≫
        (derivedPullbackTensorIso f).hom.app (A, B) :=
  NatTrans.congr_app (derivedPullbackTensorIso_sheafOfModulesTensor f) (A, B)

end Stacks.Sheaves.DerivedPullback.OfToposHom

end
