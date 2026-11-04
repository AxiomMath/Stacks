module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorTotalSquare
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.FlatKFlatModelsGeneral
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.FlatTensorComplexGeneral
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.KFlatPullbackOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackTensorTotalNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.PullbackInvertsQuasiIsoOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Interface
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.TensorProduct

/-! # Derived pullback and the derived tensor product along a morphism of ringed topoi

Let `f : (Sh(C), O) ⟶ (Sh(D), O')` be a morphism of ringed topoi. **Stacks 07A4** asserts a
canonical bifunctorial isomorphism `Lf^*(K ⊗^L_{O'} L) ≅ Lf^*K ⊗^L_O Lf^*L` for `K, L ∈ D(O')`.

This file proves it for a morphism of ringed topoi in the sense of Stacks 01D3,
`AlgebraicGeometry.RingedToposHom`, whose sites have their morphisms, the sections of their
structure sheaves and their modules in one universe `u` while their objects live in universes of
their own. That is the configuration of the small étale site of an algebraic space. The proof is
the source's: at a pair of K-flat complexes with flat terms the isomorphism is the composite

1. `K ⊗^L L ≅ Tot(K ⊗ L)`, the K-flat comparison of Stacks 06YU;
2. `Lf^*Tot(K ⊗ L) ≅ f^*Tot(K ⊗ L)`, by Stacks 06YY, since `Tot(K ⊗ L)` is K-flat with flat
   terms by Stacks 079R and 0G6Q;
3. `f^*Tot(K ⊗ L) ≅ Tot(f^*K ⊗ f^*L)`, degreewise by Stacks 03EL;
4. `Tot(f^*K ⊗ f^*L) ≅ f^*K ⊗^L f^*L`, since `f^*K`, `f^*L` are K-flat by Stacks 0G7E;
5. `f^*K ≅ Lf^*K` and `f^*L ≅ Lf^*L`, by Stacks 06YY again,

and the passage to arbitrary objects is the descent along the localization of pairs of models,
`Stacks.Sheaves.DerivedPullback.flatKFlatModelPairsQGeneral_isLocalization`.

The derived tensor products on the two sides are arbitrary inhabitants of
`Stacks.SheafOfModules.DerivedTensorProduct`; the canonical ones of Stacks 06YU are particular
choices.

## Main definitions

* `Stacks.Cohomology.DerivedPullbackOfToposHom.flatPullbackIso`: `Lf^*(QK) ≅ Q(f^*K)` for a
  K-flat complex `K` with flat terms.
* `Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackTensorModelIso`: the five-step
  composite at a pair of K-flat complexes with flat terms.
* `Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackTensorIso`: **Stacks 07A4**.

## Main results

* `Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackTensorIso_hom_app_model`: on a pair
  of K-flat complexes with flat terms, the isomorphism of Stacks 07A4 is the five-step composite.

## References

* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 0G7E](https://stacks.math.columbia.edu/tag/0G7E)
* [Stacks Project, Tag 079R](https://stacks.math.columbia.edu/tag/079R)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction (IsKFlat hasResolutions_isKFlat)
open Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom (pullbackComplex
  isFlat_pullbackComplex_X kFlat_pullbackComplex)
open Stacks.Sheaves.DerivedPullback (flatKFlatModelsQGeneral flatKFlatModelPairsQGeneral
  flatKFlatModelPairsWGeneral flatKFlatModelPairsIsoGeneral
  flatKFlatModelPairsQGeneral_isLocalization flatKFlatModelPairsIsoGeneral_naturality
  isoOverCommonTarget_naturality transportedIso_naturality transportedIso_hom_comp
  pullbackTensorTotalIso pullbackTensorTotalIso_hom_naturality isFlat_tensorComplex_X_general
  trans_naturality)

namespace Stacks.Cohomology.DerivedPullbackOfToposHom

universe u c c'

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] hasLeftDerivedFunctor_pullbackOnHomotopy

attribute [local instance 2000] CategoryTheory.Abelian.hasBinaryBiproducts

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

/-! ## The derived pullback of a K-flat complex with flat terms -/

/-- **A K-flat complex with flat terms computes the derived pullback**, Stacks 06YY:
`Lf^*(QK) ≅ Q(f^*K)`. -/
def flatPullbackIso
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) K)
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (K.X i)) :
    (derivedPullback f).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj ((pullbackComplex f).obj K) :=
  (derivedPullback f).mapIso ((DerivedCategory.quotientCompQhIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).app K).symm ≪≫
    (@asIso _ _ _ _ ((derivedPullbackComparison f).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))
      (isIso_derivedPullbackComparison_app f (IsKFlat (Y := Y)) (hasResolutions_isKFlat (Y := Y))
        (pullbackInvertsQuasiIso_isKFlat f) _ ⟨hK, hflat⟩) ≪≫
      (DerivedCategory.quotientCompQhIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).app
          ((pullbackComplex f).obj K))

/-- The identification `Lf^*(QK) ≅ Q(f^*K)` is natural in the K-flat complex `K`. -/
lemma flatPullbackIso_naturality
    {K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ}
    (a : K ⟶ L)
    (hK : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) K)
    (hL : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) L)
    (hflatK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (K.X i))
    (hflatL : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (L.X i)) :
    (derivedPullback f).map (DerivedCategory.Q.map a) ≫ (flatPullbackIso f L hL hflatL).hom =
      (flatPullbackIso f K hK hflatK).hom ≫
        DerivedCategory.Q.map ((pullbackComplex f).map a) := by
  have hY := DerivedCategory.quotientCompQhIso_inv_naturality
    (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) a
  have hX := DerivedCategory.quotientCompQhIso_hom_naturality
    (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    ((pullbackComplex f).map a)
  have hC : (derivedPullback f).map (DerivedCategory.Qh.map
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map a)) ≫
        (derivedPullbackComparison f).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj L) =
      (derivedPullbackComparison f).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
          ((pullbackComplex f).map a)) :=
    (derivedPullbackComparison f).naturality
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map a)
  have hD : (derivedPullback f).map (DerivedCategory.Q.map a) ≫
        (derivedPullback f).map ((DerivedCategory.quotientCompQhIso
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).inv.app L) =
      (derivedPullback f).map ((DerivedCategory.quotientCompQhIso
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).inv.app K) ≫
        (derivedPullback f).map (DerivedCategory.Qh.map
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map a)) := by
    rw [← Functor.map_comp, ← Functor.map_comp, hY]
  exact trans_naturality hD (trans_naturality hC hX)

/-- **Stacks 0G7E**, at the bifunctor-relative K-flatness: the degreewise pullback of a K-flat
complex with flat terms is K-flat. -/
theorem kFlat_pullbackComplex'
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) K)
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (K.X i)) :
    CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      ((pullbackComplex f).obj K) :=
  kFlat_pullbackComplex f K hK hflat

/-- **The comparison `f^*Tot(K ⊗_{O'} L) ≅ Tot(f^*K ⊗_O f^*L)`** of Stacks 03EL, with the
degreewise pullback written as `pullbackComplex f` and the modules over
`Stacks.SheafOfModules.Tensor.ringSheaf`. -/
def pullbackTensorTotalComplexIso
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    (pullbackComplex f).obj (HomologicalComplex.mapBifunctor K L
        (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) (ComplexShape.up ℤ)) ≅
      HomologicalComplex.mapBifunctor ((pullbackComplex f).obj K) ((pullbackComplex f).obj L)
        (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ) :=
  pullbackTensorTotalIso f.toModulesHom K L

/-- The comparison of total tensor complexes of Stacks 03EL is natural in the pair of
complexes. -/
lemma pullbackTensorTotalComplexIso_hom_naturality
    {K K' L L' : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ}
    (a : K ⟶ K') (b : L ⟶ L') :
    (pullbackComplex f).map (HomologicalComplex.mapBifunctorMap a b
          (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) (ComplexShape.up ℤ)) ≫
        (pullbackTensorTotalComplexIso f K' L').hom =
      (pullbackTensorTotalComplexIso f K L).hom ≫
        HomologicalComplex.mapBifunctorMap ((pullbackComplex f).map a)
          ((pullbackComplex f).map b)
          (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ) :=
  pullbackTensorTotalIso_hom_naturality f.toModulesHom a b

/-! ## The comparison at a pair of K-flat complexes with flat terms -/

section Models

variable (TX : Stacks.SheafOfModules.DerivedTensorProduct.{c, u, u} X.toRingedSite)
  (TY : Stacks.SheafOfModules.DerivedTensorProduct.{c', u, u} Y.toRingedSite)

/-- **Steps 1 and 2 of the chain**: for K-flat `K` and `L` with flat terms, `Lf^*(K ⊗^L L)` is
the image in `D(O)` of the degreewise pullback of the total tensor complex. -/
def derivedPullbackTensorModelLeft
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) K)
    (hL : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) L)
    (hflatK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (K.X i))
    (hflatL : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (L.X i)) :
    (derivedPullback f).obj
        ((TY.tensor.obj
          (DerivedCategory.Q.obj K)).obj (DerivedCategory.Q.obj L)) ≅
      DerivedCategory.Q.obj ((pullbackComplex f).obj (HomologicalComplex.mapBifunctor K L
        (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) (ComplexShape.up ℤ))) :=
  (derivedPullback f).mapIso
      (TY.comparison
        K L hK hL) ≪≫
    flatPullbackIso f
      (HomologicalComplex.mapBifunctor K L
        (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) (ComplexShape.up ℤ))
      (Stacks.SheafOfModules.kFlat_tensorComplex Y.O hK hL)
      (isFlat_tensorComplex_X_general Y.O K L hflatK hflatL)

/-- **Steps 3, 4 and 5 of the chain**: for K-flat `K` and `L` with flat terms,
`Lf^*K ⊗^L Lf^*L` is the image in `D(O)` of the degreewise pullback of the total tensor
complex. -/
def derivedPullbackTensorModelRight
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) K)
    (hL : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) L)
    (hflatK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (K.X i))
    (hflatL : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (L.X i)) :
    (TX.tensor.obj
          ((derivedPullback f).obj (DerivedCategory.Q.obj K))).obj
        ((derivedPullback f).obj (DerivedCategory.Q.obj L)) ≅
      DerivedCategory.Q.obj ((pullbackComplex f).obj (HomologicalComplex.mapBifunctor K L
        (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) (ComplexShape.up ℤ))) :=
  (Functor.uncurry.obj
        TX.tensor).mapIso
      ((flatPullbackIso f K hK hflatK).prod (flatPullbackIso f L hL hflatL)) ≪≫
    TX.comparison
        ((pullbackComplex f).obj K) ((pullbackComplex f).obj L)
        (kFlat_pullbackComplex' f K hK hflatK)
        (kFlat_pullbackComplex' f L hL hflatL) ≪≫
      (DerivedCategory.Q.mapIso (pullbackTensorTotalComplexIso f K L)).symm

/-- **The isomorphism of Stacks 07A4 at a pair of K-flat complexes with flat terms**: the two
halves of the five-step chain, which land in the same object of `D(O)`. -/
def derivedPullbackTensorModelIso
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) K)
    (hL : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) L)
    (hflatK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (K.X i))
    (hflatL : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (L.X i)) :
    (Functor.uncurry.obj TY.tensor ⋙
          derivedPullback f).obj (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) ≅
      ((derivedPullback f).prod (derivedPullback f) ⋙
          Functor.uncurry.obj
            TX.tensor).obj
        (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) :=
  derivedPullbackTensorModelLeft f TY K L hK hL hflatK hflatL ≪≫
    (derivedPullbackTensorModelRight f TX K L hK hL hflatK hflatL).symm

section Naturality

variable {K K' L L' : CochainComplex
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ}
  (a : K ⟶ K') (b : L ⟶ L')
  (hK : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) K)
  (hK' : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) K')
  (hL : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) L)
  (hL' : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) L')
  (hflatK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (K.X i))
  (hflatK' : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (K'.X i))
  (hflatL : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (L.X i))
  (hflatL' : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (L'.X i))

/-- The first half of the chain is natural in the pair of complexes: the K-flat comparison of
Stacks 06YU is, and so is the computation of `Lf^*` on a K-flat complex with flat terms. -/
private lemma derivedPullbackTensorModelLeft_naturality :
    (Functor.uncurry.obj TY.tensor ⋙
          derivedPullback f).map
        ((DerivedCategory.Q.map a, DerivedCategory.Q.map b) :
          ((DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) : _ × _) ⟶
            (DerivedCategory.Q.obj K', DerivedCategory.Q.obj L')) ≫
        (derivedPullbackTensorModelLeft f TY K' L' hK' hL' hflatK' hflatL').hom =
      (derivedPullbackTensorModelLeft f TY K L hK hL hflatK hflatL).hom ≫
        DerivedCategory.Q.map ((pullbackComplex f).map
          (HomologicalComplex.mapBifunctorMap a b
            (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) (ComplexShape.up ℤ))) := by
  dsimp only [derivedPullbackTensorModelLeft]
  have s1 : (Functor.uncurry.obj
          TY.tensor ⋙
          derivedPullback f).map
        ((DerivedCategory.Q.map a, DerivedCategory.Q.map b) :
          ((DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) : _ × _) ⟶
            (DerivedCategory.Q.obj K', DerivedCategory.Q.obj L')) ≫
        (derivedPullback f).map
          (TY.comparison
            K' L' hK' hL').hom =
      (derivedPullback f).map
          (TY.comparison
            K L hK hL).hom ≫
        (derivedPullback f).map (DerivedCategory.Q.map
          (HomologicalComplex.mapBifunctorMap a b
            (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) (ComplexShape.up ℤ))) := by
    rw [Functor.comp_map, Functor.uncurry_obj_map, ← Functor.map_comp, ← Functor.map_comp,
      Category.assoc]
    exact congrArg (derivedPullback f).map
      (TY.comparison_naturality
        a b hK hK' hL hL')
  exact trans_naturality s1 (flatPullbackIso_naturality f
    (HomologicalComplex.mapBifunctorMap a b
      (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) (ComplexShape.up ℤ))
    (Stacks.SheafOfModules.kFlat_tensorComplex Y.O hK hL)
    (Stacks.SheafOfModules.kFlat_tensorComplex Y.O hK' hL')
    (isFlat_tensorComplex_X_general Y.O K L hflatK hflatL)
    (isFlat_tensorComplex_X_general Y.O K' L' hflatK' hflatL'))

/-- The second half of the chain is natural in the pair of complexes: the computation of `Lf^*`
in each tensor factor is, the K-flat comparison of Stacks 06YU is, and the comparison of total
tensor complexes of Stacks 03EL is. -/
private lemma derivedPullbackTensorModelRight_naturality :
    ((derivedPullback f).prod (derivedPullback f) ⋙
          Functor.uncurry.obj
            TX.tensor).map
        ((DerivedCategory.Q.map a, DerivedCategory.Q.map b) :
          ((DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) : _ × _) ⟶
            (DerivedCategory.Q.obj K', DerivedCategory.Q.obj L')) ≫
        (derivedPullbackTensorModelRight f TX K' L' hK' hL' hflatK' hflatL').hom =
      (derivedPullbackTensorModelRight f TX K L hK hL hflatK hflatL).hom ≫
        DerivedCategory.Q.map ((pullbackComplex f).map
          (HomologicalComplex.mapBifunctorMap a b
            (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) (ComplexShape.up ℤ))) := by
  dsimp only [derivedPullbackTensorModelRight]
  have he : ((derivedPullback f).prod (derivedPullback f)).map
        ((DerivedCategory.Q.map a, DerivedCategory.Q.map b) :
          ((DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) : _ × _) ⟶
            (DerivedCategory.Q.obj K', DerivedCategory.Q.obj L')) ≫
        ((flatPullbackIso f K' hK' hflatK').prod
          (flatPullbackIso f L' hL' hflatL')).hom =
      ((flatPullbackIso f K hK hflatK).prod
          (flatPullbackIso f L hL hflatL)).hom ≫
        ((DerivedCategory.Q.map ((pullbackComplex f).map a),
            DerivedCategory.Q.map ((pullbackComplex f).map b)) :
          ((DerivedCategory.Q.obj ((pullbackComplex f).obj K),
              DerivedCategory.Q.obj ((pullbackComplex f).obj L)) : _ × _) ⟶
            (DerivedCategory.Q.obj ((pullbackComplex f).obj K'),
              DerivedCategory.Q.obj ((pullbackComplex f).obj L'))) :=
    Prod.ext (flatPullbackIso_naturality f a hK hK' hflatK hflatK')
      (flatPullbackIso_naturality f b hL hL' hflatL hflatL')
  have h2 : (Functor.uncurry.obj
            TX.tensor).map
          ((DerivedCategory.Q.map ((pullbackComplex f).map a),
              DerivedCategory.Q.map ((pullbackComplex f).map b)) :
            ((DerivedCategory.Q.obj ((pullbackComplex f).obj K),
                DerivedCategory.Q.obj ((pullbackComplex f).obj L)) : _ × _) ⟶
              (DerivedCategory.Q.obj ((pullbackComplex f).obj K'),
                DerivedCategory.Q.obj ((pullbackComplex f).obj L'))) ≫
        (TX.comparison
          ((pullbackComplex f).obj K') ((pullbackComplex f).obj L')
          (kFlat_pullbackComplex' f K' hK' hflatK')
          (kFlat_pullbackComplex' f L' hL' hflatL')).hom =
      (TX.comparison
          ((pullbackComplex f).obj K) ((pullbackComplex f).obj L)
          (kFlat_pullbackComplex' f K hK hflatK)
          (kFlat_pullbackComplex' f L hL hflatL)).hom ≫
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap
          ((pullbackComplex f).map a) ((pullbackComplex f).map b)
          (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ)) := by
    simpa only [Functor.uncurry_obj_map, Category.assoc] using
      TX.comparison_naturality
        ((pullbackComplex f).map a) ((pullbackComplex f).map b)
        (kFlat_pullbackComplex' f K hK hflatK)
        (kFlat_pullbackComplex' f K' hK' hflatK')
        (kFlat_pullbackComplex' f L hL hflatL)
        (kFlat_pullbackComplex' f L' hL' hflatL')
  exact trans_naturality ((Functor.uncurry.obj TX.tensor).map_commSq ⟨he⟩).w
    (trans_naturality h2 (CommSq.vert_inv (DerivedCategory.Q.map_commSq
      ⟨pullbackTensorTotalComplexIso_hom_naturality f a b⟩)).w)

/-- **The value of the comparison at a pair of K-flat complexes with flat terms is natural in
both complexes.** This is what makes the descent to arbitrary objects of `D(O')` possible. -/
lemma derivedPullbackTensorModelIso_naturality :
    (Functor.uncurry.obj TY.tensor ⋙
          derivedPullback f).map
        ((DerivedCategory.Q.map a, DerivedCategory.Q.map b) :
          ((DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) : _ × _) ⟶
            (DerivedCategory.Q.obj K', DerivedCategory.Q.obj L')) ≫
        (derivedPullbackTensorModelIso f TX TY K' L' hK' hL' hflatK' hflatL').hom =
      (derivedPullbackTensorModelIso f TX TY K L hK hL hflatK hflatL).hom ≫
        ((derivedPullback f).prod (derivedPullback f) ⋙
            Functor.uncurry.obj
              TX.tensor).map
          ((DerivedCategory.Q.map a, DerivedCategory.Q.map b) :
            ((DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) : _ × _) ⟶
              (DerivedCategory.Q.obj K', DerivedCategory.Q.obj L')) := by
  dsimp only [derivedPullbackTensorModelIso]
  exact isoOverCommonTarget_naturality
    (derivedPullbackTensorModelLeft_naturality f TY a b hK hK' hL hL'
      hflatK hflatK' hflatL hflatL')
    (derivedPullbackTensorModelRight_naturality f TX a b hK hK' hL hL'
      hflatK hflatK' hflatL hflatL')

end Naturality

/-! ## The descent to arbitrary objects of the derived category -/

section Descent

/-- The comparison at a pair of K-flat complexes with flat terms, as an isomorphism of the two
functors on the category of pairs of models. -/
def flatKFlatModelPairsTensorIso :
    flatKFlatModelPairsQGeneral Y ⋙
        (Functor.uncurry.obj
            TY.tensor ⋙
          derivedPullback f) ≅
      flatKFlatModelPairsQGeneral Y ⋙
        ((derivedPullback f).prod (derivedPullback f) ⋙
          Functor.uncurry.obj
            TX.tensor) :=
  NatIso.ofComponents
    (fun P =>
      (Functor.uncurry.obj TY.tensor ⋙
          derivedPullback f).mapIso (flatKFlatModelPairsIsoGeneral Y P) ≪≫
        derivedPullbackTensorModelIso f TX TY P.1.obj.as P.2.obj.as
            P.1.property.1 P.2.property.1 P.1.property.2 P.2.property.2 ≪≫
          (((derivedPullback f).prod (derivedPullback f) ⋙
            Functor.uncurry.obj
              TX.tensor).mapIso
            (flatKFlatModelPairsIsoGeneral Y P)).symm)
    (fun {P R} g => transportedIso_naturality
      (Functor.uncurry.obj TY.tensor ⋙
        derivedPullback f)
      ((derivedPullback f).prod (derivedPullback f) ⋙
        Functor.uncurry.obj TX.tensor)
      (flatKFlatModelPairsIsoGeneral Y P) (flatKFlatModelPairsIsoGeneral Y R)
      (derivedPullbackTensorModelIso f TX TY P.1.obj.as P.2.obj.as
        P.1.property.1 P.2.property.1 P.1.property.2 P.2.property.2)
      (derivedPullbackTensorModelIso f TX TY R.1.obj.as R.2.obj.as
        R.1.property.1 R.2.property.1 R.1.property.2 R.2.property.2)
      ((flatKFlatModelPairsQGeneral Y).map g)
      ((DerivedCategory.Q.map g.1.hom.out, DerivedCategory.Q.map g.2.hom.out) :
        ((DerivedCategory.Q.obj P.1.obj.as, DerivedCategory.Q.obj P.2.obj.as) : _ × _) ⟶
          (DerivedCategory.Q.obj R.1.obj.as, DerivedCategory.Q.obj R.2.obj.as))
      (flatKFlatModelPairsIsoGeneral_naturality Y g)
      (derivedPullbackTensorModelIso_naturality f TX TY g.1.hom.out g.2.hom.out
        P.1.property.1 R.1.property.1 P.2.property.1 R.2.property.1
        P.1.property.2 R.1.property.2 P.2.property.2 R.2.property.2))

/-- **Stacks 07A4.** The canonical bifunctorial isomorphism

`Lf^*(K ⊗^L_{O'} L) ≅ Lf^*K ⊗^L_O Lf^*L`

for a morphism of ringed topoi `f : (Sh(C), O) ⟶ (Sh(D), O')`, stated between the two uncurried
bifunctors on `D(O') × D(O')`, so that naturality in both variables is part of its type.

Its value on a pair of K-flat complexes with flat terms is the five-step composite of the source
(`derivedPullbackTensorModelIso`), and the passage to arbitrary objects of `D(O')` is the
descent of that value along the localization of pairs of models. -/
def derivedPullbackTensorIso :
    Functor.uncurry.obj TY.tensor ⋙
        derivedPullback f ≅
      (derivedPullback f).prod (derivedPullback f) ⋙
        Functor.uncurry.obj
          TX.tensor := by
  letI : (flatKFlatModelPairsQGeneral Y).IsLocalization (flatKFlatModelPairsWGeneral Y) :=
    flatKFlatModelPairsQGeneral_isLocalization Y
  letI : Localization.Lifting (flatKFlatModelPairsQGeneral Y) (flatKFlatModelPairsWGeneral Y)
      (flatKFlatModelPairsQGeneral Y ⋙
        (Functor.uncurry.obj
            TY.tensor ⋙
          derivedPullback f))
      (Functor.uncurry.obj TY.tensor ⋙
        derivedPullback f) := ⟨Iso.refl _⟩
  letI : Localization.Lifting (flatKFlatModelPairsQGeneral Y) (flatKFlatModelPairsWGeneral Y)
      (flatKFlatModelPairsQGeneral Y ⋙
        ((derivedPullback f).prod (derivedPullback f) ⋙
          Functor.uncurry.obj
            TX.tensor))
      ((derivedPullback f).prod (derivedPullback f) ⋙
        Functor.uncurry.obj
          TX.tensor) := ⟨Iso.refl _⟩
  exact Localization.liftNatIso (flatKFlatModelPairsQGeneral Y) (flatKFlatModelPairsWGeneral Y)
    _ _ _ _ (flatKFlatModelPairsTensorIso f TX TY)

end Descent


section Characterization

/-- The isomorphism of Stacks 07A4 evaluated on the image of a pair of K-flat complexes with flat
terms is the transported value out of which it was descended. -/
lemma derivedPullbackTensorIso_hom_app_modelPair
    (PP : (IsKFlat (Y := Y)).FullSubcategory × (IsKFlat (Y := Y)).FullSubcategory) :
    (derivedPullbackTensorIso f TX TY).hom.app ((flatKFlatModelPairsQGeneral Y).obj PP) =
      (flatKFlatModelPairsTensorIso f TX TY).hom.app PP := by
  have := flatKFlatModelPairsQGeneral_isLocalization Y
  have hdef : derivedPullbackTensorIso f TX TY =
      Localization.liftNatIso (flatKFlatModelPairsQGeneral Y) (flatKFlatModelPairsWGeneral Y)
        _ _ _ _ (h₁ := ⟨Iso.refl _⟩) (h₂ := ⟨Iso.refl _⟩) (flatKFlatModelPairsTensorIso f TX TY) :=
    rfl
  rw [hdef, Localization.liftNatIso_hom, Localization.liftNatTrans_app]
  simp

/-- **The isomorphism of Stacks 07A4 at a pair of K-flat complexes with flat terms is the
five-step composite of the source**: the K-flat comparisons of Stacks 06YU, the computation of
`Lf^*` of Stacks 06YY and the comparison of total tensor complexes of Stacks 03EL. -/
lemma derivedPullbackTensorIso_hom_app_model
    (P N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hP : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) P)
    (hN : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) N)
    (hflatP : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (P.X i))
    (hflatN : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (N.X i)) :
    (derivedPullbackTensorIso f TX TY).hom.app
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj N) =
      (derivedPullbackTensorModelIso f TX TY P N hP hN hflatP hflatN).hom := by
  have hnat := (derivedPullbackTensorIso f TX TY).hom.naturality
    (flatKFlatModelPairsIsoGeneral Y
      ((⟨(HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P, ⟨hP, hflatP⟩⟩,
        ⟨(HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj N, ⟨hN, hflatN⟩⟩) :
        (IsKFlat (Y := Y)).FullSubcategory × (IsKFlat (Y := Y)).FullSubcategory)).hom
  rw [derivedPullbackTensorIso_hom_app_modelPair f TX TY] at hnat
  refine (cancel_epi ((Functor.uncurry.obj TY.tensor ⋙ derivedPullback f).map
    (flatKFlatModelPairsIsoGeneral Y
      ((⟨(HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P, ⟨hP, hflatP⟩⟩,
        ⟨(HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj N, ⟨hN, hflatN⟩⟩) :
        (IsKFlat (Y := Y)).FullSubcategory ×
          (IsKFlat (Y := Y)).FullSubcategory)).hom)).1 (hnat.trans ?_)
  exact transportedIso_hom_comp
    ((Functor.uncurry.obj TY.tensor ⋙ derivedPullback f).mapIso (flatKFlatModelPairsIsoGeneral Y
        ((⟨(HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P, ⟨hP, hflatP⟩⟩,
          ⟨(HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj N, ⟨hN, hflatN⟩⟩) :
          (IsKFlat (Y := Y)).FullSubcategory × (IsKFlat (Y := Y)).FullSubcategory)))
    (((derivedPullback f).prod (derivedPullback f) ⋙ Functor.uncurry.obj TX.tensor).mapIso
      (flatKFlatModelPairsIsoGeneral Y
        ((⟨(HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P, ⟨hP, hflatP⟩⟩,
          ⟨(HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj N, ⟨hN, hflatN⟩⟩) :
          (IsKFlat (Y := Y)).FullSubcategory × (IsKFlat (Y := Y)).FullSubcategory)))
    (derivedPullbackTensorModelIso f TX TY P N hP hN hflatP hflatN)

end Characterization


end Models

end Stacks.Cohomology.DerivedPullbackOfToposHom

end
