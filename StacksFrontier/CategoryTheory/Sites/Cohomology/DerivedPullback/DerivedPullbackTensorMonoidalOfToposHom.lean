module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackMonoidalOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorIsoSheafOfModulesTensor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Associativity
public import StacksFrontier.CategoryTheory.Monoidal.ReseatFunctor

/-!
# Derived pullback along a morphism of ringed topoi is monoidal for the derived tensor product

Let `f : (Sh(C), 𝒪) ⟶ (Sh(C'), 𝒪')` be a morphism of ringed topoi. The monoidal structure of
[Stacks, Tag 0FPT] on `D(𝒪)` can be re-seated onto either of the two canonical derived tensor
products of [Stacks, Tag 06YU]: that of `Stacks.DerivedTensor.RingedSite`
(`Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal`), for which `Lf^*` is monoidal
by `Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackCanonicalCoreMonoidal`, and that of
`Stacks.SheafOfModules` (`Stacks.SheafOfModules.DerivedMonoidal.reseatedDerivedMonoidal`), the
one the internal Hom of [Stacks, Tag 08J8] and the duals of [Stacks, Tag 0FPU] are stated at.
This file carries the monoidal structure of `Lf^*` to the second re-seating and identifies its
tensorator with the inverse of the comparison of [Stacks, Tag 07A4] of
`Stacks.Cohomology.DerivedPullbackOfToposHom`, at the derived tensor products of
`Stacks.SheafOfModules`.

## Main definitions

* `Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorMonoidal`: `Lf^*` as a monoidal
  functor for the derived tensor products of `Stacks.SheafOfModules`.

## Main results

* `Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorMonoidal_μ`: its tensorator is
  the inverse of the comparison of [Stacks, Tag 07A4].

## References

* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackOfToposHom (derivedPullback)

universe u

namespace Stacks.Sheaves.DerivedPullback.OfToposHom

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

/-- `Lf^*` as a monoidal functor for the monoidal structures of [Stacks, Tag 0FPT] themselves:
`derivedPullbackCanonicalCoreMonoidal` read through the identity functors between them and their
re-seatings onto the derived tensor products of `Stacks.DerivedTensor.RingedSite`. -/
@[instance_reducible]
def derivedPullbackDerivedMonoidal :
    @Functor.Monoidal _ _ (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal Y.O) _ _
      (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal X.O) (derivedPullback f) :=
  @Functor.Monoidal.instComp _ _ (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal Y.O) _ _
    (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal Y.O) _ _
    (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal X.O) (𝟭 _) (derivedPullback f ⋙ 𝟭 _)
    (@reseatMonoidalInverse _ _ (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal Y.O) _ _
      (Stacks.SheafOfModules.DerivedMonoidal.monoidalTensorCanonicalIso Y.O)
      (Stacks.SheafOfModules.DerivedMonoidal.canonicalUnitIso Y.O))
    (@Functor.Monoidal.instComp _ _
      (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal Y.O) _ _
      (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal X.O) _ _
      (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal X.O) (derivedPullback f) (𝟭 _)
      (@Functor.CoreMonoidal.toMonoidal _ _
        (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal Y.O) _ _
        (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal X.O) _
        (derivedPullbackCanonicalCoreMonoidal f))
      (@reseatMonoidal _ _ (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal X.O) _ _
        (Stacks.SheafOfModules.DerivedMonoidal.monoidalTensorCanonicalIso X.O)
        (Stacks.SheafOfModules.DerivedMonoidal.canonicalUnitIso X.O)))

/-- **`Lf^*` is monoidal for the derived tensor products of `Stacks.SheafOfModules`**, the
re-seating `Stacks.SheafOfModules.DerivedMonoidal.reseatedDerivedMonoidal` of the monoidal
structure of [Stacks, Tag 0FPT] onto the canonical derived tensor product of the site. -/
@[instance_reducible]
def derivedPullbackTensorMonoidal :
    @Functor.Monoidal _ _
      (Stacks.SheafOfModules.DerivedMonoidal.reseatedDerivedMonoidal Y.O
        (Stacks.SheafOfModules.DerivedTensorProduct.toRingedSiteDerivedTensorProduct
          (Stacks.SheafOfModules.canonicalDerivedTensorProduct Y.toRingedSite))) _ _
      (Stacks.SheafOfModules.DerivedMonoidal.reseatedDerivedMonoidal X.O
        (Stacks.SheafOfModules.DerivedTensorProduct.toRingedSiteDerivedTensorProduct
          (Stacks.SheafOfModules.canonicalDerivedTensorProduct X.toRingedSite)))
      (derivedPullback f) :=
  @Functor.monoidalReseat _ _ (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal Y.O) _ _ _ _
    (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal X.O) _ _ (derivedPullback f)
    (derivedPullbackDerivedMonoidal f)
    (Stacks.SheafOfModules.DerivedMonoidal.derivedTensorMonoidalIso Y.O
      (Stacks.SheafOfModules.DerivedTensorProduct.toRingedSiteDerivedTensorProduct
        (Stacks.SheafOfModules.canonicalDerivedTensorProduct Y.toRingedSite)))
    (Stacks.SheafOfModules.DerivedMonoidal.canonicalUnitIso Y.O)
    (Stacks.SheafOfModules.DerivedMonoidal.derivedTensorMonoidalIso X.O
      (Stacks.SheafOfModules.DerivedTensorProduct.toRingedSiteDerivedTensorProduct
        (Stacks.SheafOfModules.canonicalDerivedTensorProduct X.toRingedSite)))
    (Stacks.SheafOfModules.DerivedMonoidal.canonicalUnitIso X.O)

/-- The comparison of the two re-seatings of the monoidal structure of [Stacks, Tag 0FPT] is the
identification of the two canonical derived tensor products. -/
theorem reseatIso_inv_comp_reseatIso_hom (Z : AlgebraicGeometry.RingedTopos.{u, u, u})
    [Z.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [HasSheafify Z.J AddCommGrpCat.{u}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (A B : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))) :
    (@reseatIso _ _ (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal Z.O) _
        (Stacks.SheafOfModules.DerivedMonoidal.monoidalTensorCanonicalIso Z.O) A B).inv ≫
      (@reseatIso _ _ (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal Z.O) _
        (Stacks.SheafOfModules.DerivedMonoidal.derivedTensorMonoidalIso Z.O
          (Stacks.SheafOfModules.DerivedTensorProduct.toRingedSiteDerivedTensorProduct
            (Stacks.SheafOfModules.canonicalDerivedTensorProduct Z.toRingedSite))) A B).hom =
      ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctorIsoSheafOfModules
        Z.toRingedSite).hom.app A).app B := by
  change (((Stacks.SheafOfModules.DerivedMonoidal.derivedTensorBifunctorIso Z.O ≪≫
      Stacks.SheafOfModules.DerivedMonoidal.canonicalTensorIso Z.O).app A).app B).inv ≫
      (((Stacks.SheafOfModules.DerivedMonoidal.derivedTensorBifunctorIso Z.O ≪≫
        Stacks.SheafOfModules.DerivedMonoidal.derivedBifunctorTensorIso Z.O
          (Stacks.SheafOfModules.DerivedTensorProduct.toRingedSiteDerivedTensorProduct
          (Stacks.SheafOfModules.canonicalDerivedTensorProduct Z.toRingedSite))).app A).app B).hom =
    (((Stacks.SheafOfModules.DerivedMonoidal.canonicalTensorIso Z.O).symm ≪≫
      Stacks.SheafOfModules.DerivedMonoidal.derivedBifunctorTensorIso Z.O
        (Stacks.SheafOfModules.DerivedTensorProduct.toRingedSiteDerivedTensorProduct
          (Stacks.SheafOfModules.canonicalDerivedTensorProduct Z.toRingedSite))).hom.app A).app B
  simp only [Iso.app_inv, Iso.app_hom, Iso.trans_inv, Iso.trans_hom, NatTrans.comp_app,
    Iso.symm_hom, Category.assoc, Iso.inv_hom_id_app_app_assoc]

/-- The tensorator of the identity functor, monoidal from a structure to its re-seating, is the
inverse of `reseatIso`. -/
private theorem reseatMonoidalInverse_μ {C : Type*} [Category C] [MC : MonoidalCategory C]
    {T : C ⥤ C ⥤ C} {U : C} (e : curriedTensor C ≅ T) (ε : 𝟙_ C ≅ U) (A B : C) :
    @Functor.LaxMonoidal.μ _ _ MC _ _ (reseat e ε) (𝟭 C)
      (reseatMonoidalInverse e ε).toLaxMonoidal A B = (reseatIso e A B).inv := by
  change 𝟙 _ ≫ ((reseatIso e A B).inv ≫ (𝟙 A ⊗ₘ 𝟙 B)) = _
  rw [Category.id_comp, id_tensorHom_id, Category.comp_id]

/-- The tensorator of `derivedPullbackDerivedMonoidal`. -/
theorem derivedPullbackDerivedMonoidal_μ
    (A B : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :
    @Functor.LaxMonoidal.μ _ _ (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal Y.O) _ _
        (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal X.O) (derivedPullback f)
        (derivedPullbackDerivedMonoidal f).toLaxMonoidal A B =
      (@reseatIso _ _ (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal X.O) _
          (Stacks.SheafOfModules.DerivedMonoidal.monoidalTensorCanonicalIso X.O)
          ((derivedPullback f).obj A) ((derivedPullback f).obj B)).hom ≫
        (derivedPullbackTensorIso f).inv.app (A, B) ≫
        (derivedPullback f).map
          (@reseatIso _ _ (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal Y.O) _
            (Stacks.SheafOfModules.DerivedMonoidal.monoidalTensorCanonicalIso Y.O) A B).inv := by
  change ((@reseatIso _ _ (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal X.O) _
      (Stacks.SheafOfModules.DerivedMonoidal.monoidalTensorCanonicalIso X.O)
      ((derivedPullback f).obj A) ((derivedPullback f).obj B)).hom ≫
      (derivedPullbackTensorIso f).inv.app (A, B)) ≫ (derivedPullback f).map
    (@Functor.LaxMonoidal.μ _ _
      (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal Y.O) _ _
      (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal Y.O) (𝟭 _)
      (@reseatMonoidalInverse _ _ (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal Y.O) _ _
        (Stacks.SheafOfModules.DerivedMonoidal.monoidalTensorCanonicalIso Y.O)
        (Stacks.SheafOfModules.DerivedMonoidal.canonicalUnitIso Y.O)).toLaxMonoidal A B) = _
  rw [@reseatMonoidalInverse_μ _ _ (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal Y.O),
    Category.assoc]

/-- The identification of the two canonical derived tensor products, inverted, as the comparison of
the two re-seatings. -/
theorem reseatIso_inv_comp_reseatIso_hom' (Z : AlgebraicGeometry.RingedTopos.{u, u, u})
    [Z.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [HasSheafify Z.J AddCommGrpCat.{u}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (A B : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))) :
    (@reseatIso _ _ (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal Z.O) _
        (Stacks.SheafOfModules.DerivedMonoidal.derivedTensorMonoidalIso Z.O
          (Stacks.SheafOfModules.DerivedTensorProduct.toRingedSiteDerivedTensorProduct
            (Stacks.SheafOfModules.canonicalDerivedTensorProduct Z.toRingedSite))) A B).inv ≫
      (@reseatIso _ _ (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal Z.O) _
        (Stacks.SheafOfModules.DerivedMonoidal.monoidalTensorCanonicalIso Z.O) A B).hom =
      ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctorIsoSheafOfModules
        Z.toRingedSite).inv.app A).app B := by
  change (((Stacks.SheafOfModules.DerivedMonoidal.derivedTensorBifunctorIso Z.O ≪≫
      Stacks.SheafOfModules.DerivedMonoidal.derivedBifunctorTensorIso Z.O
        (Stacks.SheafOfModules.DerivedTensorProduct.toRingedSiteDerivedTensorProduct
          (Stacks.SheafOfModules.canonicalDerivedTensorProduct Z.toRingedSite))).app A).app B).inv ≫
      (((Stacks.SheafOfModules.DerivedMonoidal.derivedTensorBifunctorIso Z.O ≪≫
        Stacks.SheafOfModules.DerivedMonoidal.canonicalTensorIso Z.O).app A).app B).hom =
    (((Stacks.SheafOfModules.DerivedMonoidal.canonicalTensorIso Z.O).symm ≪≫
      Stacks.SheafOfModules.DerivedMonoidal.derivedBifunctorTensorIso Z.O
        (Stacks.SheafOfModules.DerivedTensorProduct.toRingedSiteDerivedTensorProduct
          (Stacks.SheafOfModules.canonicalDerivedTensorProduct Z.toRingedSite))).inv.app A).app B
  simp only [Iso.app_inv, Iso.app_hom, Iso.trans_inv, Iso.trans_hom, NatTrans.comp_app,
    Iso.symm_inv, Category.assoc, Iso.inv_hom_id_app_app_assoc]

/-- An inverse read off from a commuting square whose other sides are isomorphisms. -/
private theorem comp_inv_comp_map_hom_eq_inv {C D : Type*} [Category C] [Category D] (G : C ⥤ D)
    {T S : C} {Q Q' : D} (gen : G.obj T ≅ Q) (x : Q ⟶ Q') (OT : G.obj S ≅ Q') (y : S ≅ T)
    (h : gen.hom ≫ x = G.map y.inv ≫ OT.hom) : x ≫ OT.inv ≫ G.map y.hom = gen.inv := by
  rw [← cancel_epi gen.hom, Iso.hom_inv_id, reassoc_of% h, Iso.hom_inv_id_assoc, ← G.map_comp,
    Iso.inv_hom_id, G.map_id]

/-- **The tensorator of `derivedPullbackTensorMonoidal` is the inverse of the comparison of
[Stacks, Tag 07A4]**, at the derived tensor products of `Stacks.SheafOfModules`. -/
theorem derivedPullbackTensorMonoidal_μ
    (A B : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :
    @Functor.LaxMonoidal.μ _ _
        (Stacks.SheafOfModules.DerivedMonoidal.reseatedDerivedMonoidal Y.O
          (Stacks.SheafOfModules.DerivedTensorProduct.toRingedSiteDerivedTensorProduct
            (Stacks.SheafOfModules.canonicalDerivedTensorProduct Y.toRingedSite))) _ _
        (Stacks.SheafOfModules.DerivedMonoidal.reseatedDerivedMonoidal X.O
          (Stacks.SheafOfModules.DerivedTensorProduct.toRingedSiteDerivedTensorProduct
            (Stacks.SheafOfModules.canonicalDerivedTensorProduct X.toRingedSite)))
        (derivedPullback f) (derivedPullbackTensorMonoidal f).toLaxMonoidal A B =
      (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackTensorIso f
          (Stacks.SheafOfModules.canonicalDerivedTensorProduct X.toRingedSite)
          (Stacks.SheafOfModules.canonicalDerivedTensorProduct Y.toRingedSite)).inv.app (A, B) := by
  change (@Functor.LaxMonoidal.μ _ _
      (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal X.O) _ _
      (Stacks.SheafOfModules.DerivedMonoidal.reseatedDerivedMonoidal X.O
          (Stacks.SheafOfModules.DerivedTensorProduct.toRingedSiteDerivedTensorProduct
            (Stacks.SheafOfModules.canonicalDerivedTensorProduct X.toRingedSite))) (𝟭 _)
      (@reseatMonoidalInverse _ _ (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal X.O) _ _
        (Stacks.SheafOfModules.DerivedMonoidal.derivedTensorMonoidalIso X.O
          (Stacks.SheafOfModules.DerivedTensorProduct.toRingedSiteDerivedTensorProduct
            (Stacks.SheafOfModules.canonicalDerivedTensorProduct X.toRingedSite)))
        (Stacks.SheafOfModules.DerivedMonoidal.canonicalUnitIso X.O)).toLaxMonoidal
        ((derivedPullback f).obj A) ((derivedPullback f).obj B) ≫
      @Functor.LaxMonoidal.μ _ _ (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal Y.O) _ _
        (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal X.O) (derivedPullback f)
        (derivedPullbackDerivedMonoidal f).toLaxMonoidal A B) ≫
      (derivedPullback f).map
        (@reseatIso _ _ (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal Y.O) _
          (Stacks.SheafOfModules.DerivedMonoidal.derivedTensorMonoidalIso Y.O
            (Stacks.SheafOfModules.DerivedTensorProduct.toRingedSiteDerivedTensorProduct
              (Stacks.SheafOfModules.canonicalDerivedTensorProduct Y.toRingedSite))) A B).hom = _
  rw [@reseatMonoidalInverse_μ _ _ (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal X.O),
    derivedPullbackDerivedMonoidal_μ]
  have hX := reseatIso_inv_comp_reseatIso_hom' X ((derivedPullback f).obj A)
    ((derivedPullback f).obj B)
  have hY := reseatIso_inv_comp_reseatIso_hom Y A B
  have hB2 := derivedPullbackTensorIso_sheafOfModulesTensor_app f A B
  simp only [Category.assoc]
  rw [reassoc_of% hX, ← Functor.map_comp, hY]
  exact comp_inv_comp_map_hom_eq_inv (derivedPullback f)
    ((Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackTensorIso f
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct X.toRingedSite)
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct Y.toRingedSite)).app (A, B)) _
    ((derivedPullbackTensorIso f).app (A, B))
    (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctorIsoSheafOfModules
      Y.toRingedSite).app A).app B) hB2

end Stacks.Sheaves.DerivedPullback.OfToposHom

end
