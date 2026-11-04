module

public import StacksFrontier.CategoryTheory.Monoidal.CoreMonoidalOfAssociativeTensorator
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackTensorAssociatorOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackStructureSheaf

/-!
# The derived pullback along a morphism of ringed topoi is a monoidal functor

Let `f : (Sh(C), 𝒪) ⟶ (Sh(C'), 𝒪')` be a morphism of ringed topoi in the sense of
[Stacks, Tag 01D3], part (2): a morphism of the underlying topoi together with the structure
map, with no functor between the underlying sites. The comparison of [Stacks, Tag 07A4],

`Lf^*(P ⊗^L_{𝒪'} Q) ≅ Lf^*P ⊗^L_𝒪 Lf^*Q`

(`Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso`), is the tensorator of a
monoidal structure on `Lf^*` for the monoidal derived categories of [Stacks, Tag 0FPT] on both
sides, re-seated so that their tensor product is the derived tensor bifunctor of
[Stacks, Tag 06YU] on the nose
(`Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal`).

The associativity law of the comparison is
`Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso_associator`. The unit
comparison is not the derived pullback of the structure sheaf read as a unit isomorphism: it is
the unique isomorphism `𝒪[0] ≅ Lf^*(𝒪'[0])` making the unitality laws hold, which exists by
Saavedra's unit argument, `CategoryTheory.Functor.CoreMonoidal.ofAssociativeTensorator`, given
that `Lf^*(𝒪'[0]) ≅ 𝒪[0]`
(`Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackUnitIsoGeneral`).

## Main definitions

* `Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackCanonicalCoreMonoidal`: the monoidal
  structure on `Lf^*`.

## Main results

* `Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackCanonicalCoreMonoidal_μIso`: its
  tensorator is the inverse of the comparison of [Stacks, Tag 07A4].

## References

* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.DerivedTensor.RingedSite
open Stacks.SheafOfModules.DerivedMonoidal (canonicalAssociatorHom canonicalDerivedMonoidal)
open scoped CategoryTheory.Prod

attribute [-instance] Stacks.DerivedTensor.ResolutionByExtensionsByZero.instAbelian

namespace Stacks.Sheaves.DerivedPullback.OfToposHom

universe u

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance]
  Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy

/-- The uncurried bifunctor on a morphism which is the identity in the second factor. -/
private lemma uncurry_map_id_snd {A B : Type*} [Category A] [Category B] (T : A ⥤ A ⥤ B)
    {Z Z' : A} (v : Z ⟶ Z') (W : A) :
    (Functor.uncurry.obj T).map (v ×ₘ 𝟙 W) = (T.map v).app W := by
  show (T.map v).app W ≫ (T.obj Z').map (𝟙 W) = _
  rw [CategoryTheory.Functor.map_id, Category.comp_id]

/-- The uncurried bifunctor on a morphism which is the identity in the first factor. -/
private lemma uncurry_map_id_fst {A B : Type*} [Category A] [Category B] (T : A ⥤ A ⥤ B)
    (Z : A) {W W' : A} (v : W ⟶ W') :
    (Functor.uncurry.obj T).map (𝟙 Z ×ₘ v) = (T.obj Z).map v := by
  show (T.map (𝟙 Z)).app W ≫ (T.obj Z).map v = _
  rw [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)]
  (f : AlgebraicGeometry.RingedToposHom X Y)

/-- The associativity law of [Stacks, Tag 07A4], in the oplax shape with whiskerings written as
the derived tensor bifunctor on a morphism. -/
theorem derivedPullbackTensorIso_associator_whiskered (P Q S : DerivedModules Y.O) :
    (derivedPullbackTensorIso f).hom.app
          (((derivedTensorProductFunctor Y.O).obj P).obj Q, S) ≫
        ((derivedTensorProductFunctor X.O).map
            ((derivedPullbackTensorIso f).hom.app (P, Q))).app ((derivedPullback f).obj S) ≫
          canonicalAssociatorHom X.O ((derivedPullback f).obj P) ((derivedPullback f).obj Q)
            ((derivedPullback f).obj S) =
      (derivedPullback f).map (canonicalAssociatorHom Y.O P Q S) ≫
        (derivedPullbackTensorIso f).hom.app
            (P, ((derivedTensorProductFunctor Y.O).obj Q).obj S) ≫
          ((derivedTensorProductFunctor X.O).obj ((derivedPullback f).obj P)).map
            ((derivedPullbackTensorIso f).hom.app (Q, S)) := by
  have h := derivedPullbackTensorIso_associator f P Q S
  unfold DerivedPullbackTensorIsoAssociator at h
  rw [uncurry_map_id_snd, uncurry_map_id_fst] at h
  exact h

/-- **The derived pullback along a morphism of ringed topoi is a monoidal functor** for the
monoidal derived categories of [Stacks, Tag 0FPT] re-seated onto the derived tensor bifunctor:
the tensorator is the inverse of the comparison of [Stacks, Tag 07A4], associative by
`derivedPullbackTensorIso_associator`, and the unit comparison is the one Saavedra's argument
attaches to it, `CategoryTheory.Functor.CoreMonoidal.ofAssociativeTensorator`. -/
def derivedPullbackCanonicalCoreMonoidal :
    @Functor.CoreMonoidal _ _ (canonicalDerivedMonoidal Y.O) _ _ (canonicalDerivedMonoidal X.O)
      (derivedPullback f) :=
  letI := canonicalDerivedMonoidal Y.O
  letI := canonicalDerivedMonoidal X.O
  Functor.CoreMonoidal.ofAssociativeTensorator
    (fun A B => ((derivedPullbackTensorIso f).app (A, B)).symm)
    (fun {A B} g A' => by
      have h := (derivedPullbackTensorIso f).inv.naturality (g ×ₘ 𝟙 A')
      simp only [Functor.comp_map, Functor.prod_map, CategoryTheory.Functor.map_id] at h
      rw [uncurry_map_id_snd, uncurry_map_id_snd] at h
      exact h)
    (fun {A B} A' g => by
      have h := (derivedPullbackTensorIso f).inv.naturality (𝟙 A' ×ₘ g)
      simp only [Functor.comp_map, Functor.prod_map, CategoryTheory.Functor.map_id] at h
      rw [uncurry_map_id_fst, uncurry_map_id_fst] at h
      exact h)
    (@Functor.CoreMonoidal.associativity_of_oplax _ _ _ _ (canonicalDerivedMonoidal Y.O)
      (canonicalDerivedMonoidal X.O) (derivedPullback f)
      (fun A B => ((derivedPullbackTensorIso f).app (A, B)).symm)
      (fun P Q S => derivedPullbackTensorIso_associator_whiskered f P Q S))
    (derivedPullbackUnitIsoGeneral f).symm

/-- The tensorator of `derivedPullbackCanonicalCoreMonoidal` is the inverse of the comparison of
[Stacks, Tag 07A4]. -/
theorem derivedPullbackCanonicalCoreMonoidal_μIso (A B : DerivedModules Y.O) :
    letI := canonicalDerivedMonoidal Y.O
    letI := canonicalDerivedMonoidal X.O
    (derivedPullbackCanonicalCoreMonoidal f).μIso A B =
      ((derivedPullbackTensorIso f).app (A, B)).symm := rfl

end Stacks.Sheaves.DerivedPullback.OfToposHom

end
