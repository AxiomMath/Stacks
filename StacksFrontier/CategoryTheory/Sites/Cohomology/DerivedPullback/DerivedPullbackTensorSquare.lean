module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackSquare
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorBraidingOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorComparisonOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ProjectionFormula
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorTotalSquare

/-!
# The comparison of Stacks 07A4 on flat K-flat models, along a composite and around a square

Let `h : (Sh(𝒞), 𝒪_𝒞) ⟶ (Sh(𝒟), 𝒪_𝒟)` be a morphism of ringed topoi. On a pair of K-flat complexes
`P`, `N` of `𝒪_𝒟`-modules with flat terms, the comparison `Lh^*(P ⊗^𝐋 N) ≅ Lh^*P ⊗^𝐋 Lh^*N` of
[Stacks, Tag 07A4] is the five-step composite it is descended from: the K-flat comparison
downstairs, the computation of `Lh^*` on the total complex by degreewise pullback, the degreewise
comparison of [Stacks, Tag 03EL] on total tensor complexes, the inverse K-flat comparison upstairs
and the inverse computations of `Lh^*` on the two factors. For two composable morphisms `a`, `b`
this file also writes out `L(a)^*` of the comparison along `b` followed by the comparison along `a`
on such a pair, and, for a square of morphisms of ringed topoi commuting up to a 2-isomorphism
`s : g ∘ f' ≅ f ∘ g'`, the isomorphism `Σ : L(f')^* ∘ Lg^* ≅ L(g')^* ∘ Lf^*` of
`AlgebraicGeometry.RingedToposHom.TwoIso.derivedPullbackSquareIso` on such a complex. These are the
inputs of the compatibility of the four comparisons around the square,
`AlgebraicGeometry.RingedToposHom.TwoIso.tensorComparisonCompatible`.

## Main definitions

* `Stacks.Sheaves.DerivedPullback.OfToposHom.flatPullbackCompIso`: the computation of
  `L(a)^* L(b)^*` on a K-flat complex with flat terms by the two degreewise pullbacks.

## Main results

* `Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso_hom_app_model_eq`: the
  comparison of [Stacks, Tag 07A4] at a pair of K-flat complexes with flat terms, which
  `Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso_hom_app_model` identifies
  with the model isomorphism it is descended from, written out factor by factor.
* `derivedPullback_map_derivedPullbackTensorIso_comp_model`, in the namespace
  `Stacks.Sheaves.DerivedPullback.OfToposHom`: the comparisons along `b` and then `a` at such a
  pair.
* `AlgebraicGeometry.RingedToposHom.TwoIso.derivedPullbackSquareIso_hom_app_flatPullbackIso`:
  `Σ` on a K-flat complex with flat terms.

## References

* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 0E48](https://stacks.math.columbia.edu/tag/0E48)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction (IsKFlat)
open scoped CategoryTheory.Prod

/-- The algebra of `derivedPullback_map_derivedPullbackTensorIso_comp_model`, over variables. -/
theorem _root_.CategoryTheory.tensor_comp_model_aux {𝒜 𝒞 : Type*} [Category 𝒜] [Category 𝒞]
    (La : 𝒜 ⥤ 𝒞) {S₀ A₁ A₂ A₃ A₄ A₅ : 𝒜} {O₂ V₁ W₁ W₂ V₂ W₀ : 𝒞}
    (x₁ : S₀ ⟶ A₁) (x₂ : A₁ ⟶ A₂) (x₃ : A₂ ⟶ A₃) (x₄ : A₃ ⟶ A₄) (x₄' : A₄ ⟶ A₃) (x₅ : A₄ ⟶ A₅)
    (t : La.obj A₅ ⟶ O₂) (t' : La.obj A₄ ⟶ V₁) (k : V₁ ⟶ O₂) (c₂ : La.obj A₃ ⟶ W₁)
    (c₃ : W₁ ⟶ W₂) (c₄ : W₂ ⟶ V₂) (c₅ : V₂ ⟶ V₁) (n₁ : La.obj A₂ ⟶ W₀) (n₂ : W₀ ⟶ W₁)
    (ψ : V₂ ⟶ O₂)
    (hnat : La.map x₅ ≫ t = t' ≫ k) (hmodel : t' = La.map x₄' ≫ c₂ ≫ c₃ ≫ c₄ ≫ c₅)
    (hcancel : x₄ ≫ x₄' = 𝟙 A₃) (hflat : La.map x₃ ≫ c₂ = n₁ ≫ n₂) (hψ : c₅ ≫ k = ψ) :
    La.map (x₁ ≫ x₂ ≫ x₃ ≫ x₄ ≫ x₅) ≫ t =
      La.map x₁ ≫ La.map x₂ ≫ n₁ ≫ n₂ ≫ c₃ ≫ c₄ ≫ ψ := by
  subst hmodel hψ
  simp only [Functor.map_comp, Category.assoc] at hnat ⊢
  rw [hnat, ← La.map_comp_assoc x₄ x₄', hcancel, La.map_id, Category.id_comp,
    reassoc_of% hflat]

/-- Reassociation of a composite of five morphisms, in the shape the model description of the
comparison of Stacks 07A4 is built in. -/
theorem _root_.CategoryTheory.assoc_model_aux {𝒞 : Type*} [Category 𝒞] {A₀ A₁ A₂ A₃ A₄ A₅ : 𝒞}
    (a : A₀ ⟶ A₁) (b : A₁ ⟶ A₂) (c : A₂ ⟶ A₃) (d : A₃ ⟶ A₄) (e : A₄ ⟶ A₅) :
    (a ≫ b) ≫ ((c ≫ d) ≫ e) = a ≫ b ≫ c ≫ d ≫ e := by
  simp only [Category.assoc]

namespace Stacks.Sheaves.DerivedPullback.OfToposHom

universe u

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

open Stacks.DerivedTensor.RingedSite in
open Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom
  (pullbackComplex isFlat_pullbackComplex_X) in
/-- **The comparison of Stacks 07A4 at a pair of K-flat complexes with flat terms, written out
factor by factor**: `L(f)^*` of the K-flat comparison, the computation of `L(f)^*` on the total
complex, the degreewise comparison of Stacks 03EL, the inverse K-flat comparison upstairs and the
inverse computations of `L(f)^*` on the two factors. -/
theorem derivedPullbackTensorIso_hom_app_model_eq
    (P N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hP : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) P)
    (hN : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) N)
    (hflatP : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (P.X i))
    (hflatN : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (N.X i)) :
    (derivedPullbackTensorIso f).hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj N) =
      (derivedPullback f).map ((canonicalDerivedTensorProduct Y.O).comparison P N
            ((Stacks.SheafOfModules.KFlat.kFlat_iff_kFlatBifunctor Y.O P).2 hP)
            ((Stacks.SheafOfModules.KFlat.kFlat_iff_kFlatBifunctor Y.O N).2 hN)).hom ≫
        (flatPullbackIso f
          (HomologicalComplex.mapBifunctor P N
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ))
          (Stacks.SheafOfModules.kFlat_tensorComplex Y.O hP hN)
          (isFlat_tensorComplex_X Y.O P N hflatP hflatN)).hom ≫
        DerivedCategory.Q.map (pullbackTensorTotalIso f.toModulesHom P N).hom ≫
        ((canonicalDerivedTensorProduct X.O).comparison
          ((pullbackComplex f).obj P) ((pullbackComplex f).obj N)
          ((Stacks.SheafOfModules.KFlat.kFlat_iff_kFlatBifunctor X.O _).2
            (kFlatBifunctor_pullbackComplex f P hP hflatP))
          ((Stacks.SheafOfModules.KFlat.kFlat_iff_kFlatBifunctor X.O _).2
            (kFlatBifunctor_pullbackComplex f N hN hflatN))).inv ≫
        (Functor.uncurry.obj (derivedTensorProductFunctor X.O)).map
          ((flatPullbackIso f P hP hflatP).inv ×ₘ (flatPullbackIso f N hN hflatN).inv) := by
  rw [derivedPullbackTensorIso_hom_app_model f P N hP hN hflatP hflatN]
  exact CategoryTheory.assoc_model_aux _ _ _ _ _

section Composite

open Stacks.DerivedTensor.RingedSite
open Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom
  (pullbackComplex isFlat_pullbackComplex_X)

variable {X' Y' Y : AlgebraicGeometry.RingedTopos.{u, u, u}}
  [X'.J.HasSheafCompose (forget RingCat.{u})]
  [Y'.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X'.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y'.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X'.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y'.J.HasSheafCompose (forget AddCommGrpCat.{u})] [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X'.J AddCommGrpCat.{u}] [X'.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y'.J AddCommGrpCat.{u}] [Y'.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X'.J (Type u)] [HasSheafify Y'.J (Type u)] [HasSheafify Y.J (Type u)]
  (a : AlgebraicGeometry.RingedToposHom X' Y') (b : AlgebraicGeometry.RingedToposHom Y' Y)

/-- The computation of `L(a)^* L(b)^*` on a K-flat complex with flat terms by the degreewise
pullbacks along `b` and then `a`. -/
def flatPullbackCompIso
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) K)
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i)) :
    (derivedPullback a).obj ((derivedPullback b).obj (DerivedCategory.Q.obj K)) ≅
      DerivedCategory.Q.obj ((pullbackComplex a).obj ((pullbackComplex b).obj K)) :=
  (derivedPullback a).mapIso (flatPullbackIso b K hK hflat) ≪≫
    flatPullbackIso a ((pullbackComplex b).obj K) (kFlatBifunctor_pullbackComplex b K hK hflat)
      (isFlat_pullbackComplex_X b K hflat)

variable
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X'.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X'.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y'.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y'.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X'.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y'.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y'.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)]

/-- **The comparisons of Stacks 07A4 along `b` and then `a`, at a pair of K-flat complexes with
flat terms.** `L(a)^*` of the comparison along `b`, followed by the comparison along `a`, is the
K-flat comparison, the computation of `L(a)^* L(b)^*` on the total complex by degreewise
pullbacks, the two degreewise comparisons of Stacks 03EL, the inverse K-flat comparison and the
inverse computations of `L(a)^* L(b)^*` on the two factors. -/
theorem derivedPullback_map_derivedPullbackTensorIso_comp_model
    (P N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hP : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) P)
    (hN : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) N)
    (hflatP : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (P.X i))
    (hflatN : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (N.X i)) :
    (derivedPullback a).map
        ((derivedPullbackTensorIso b).hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj N)) ≫
      (derivedPullbackTensorIso a).hom.app
        ((derivedPullback b).obj (DerivedCategory.Q.obj P),
          (derivedPullback b).obj (DerivedCategory.Q.obj N)) =
    (derivedPullback a).map ((derivedPullback b).map
        ((canonicalDerivedTensorProduct Y.O).comparison P N
          ((Stacks.SheafOfModules.KFlat.kFlat_iff_kFlatBifunctor Y.O P).2 hP)
          ((Stacks.SheafOfModules.KFlat.kFlat_iff_kFlatBifunctor Y.O N).2 hN)).hom) ≫
      (derivedPullback a).map (flatPullbackIso b
          (HomologicalComplex.mapBifunctor P N
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ))
          (Stacks.SheafOfModules.kFlat_tensorComplex Y.O hP hN)
          (isFlat_tensorComplex_X Y.O P N hflatP hflatN)).hom ≫
      (flatPullbackIso a ((pullbackComplex b).obj (HomologicalComplex.mapBifunctor P N
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)))
          (kFlatBifunctor_pullbackComplex b _ (Stacks.SheafOfModules.kFlat_tensorComplex Y.O hP hN)
            (isFlat_tensorComplex_X Y.O P N hflatP hflatN))
          (isFlat_pullbackComplex_X b _ (isFlat_tensorComplex_X Y.O P N hflatP hflatN))).hom ≫
      DerivedCategory.Q.map
          ((pullbackComplex a).map (pullbackTensorTotalIso b.toModulesHom P N).hom) ≫
      DerivedCategory.Q.map (pullbackTensorTotalIso a.toModulesHom
          ((pullbackComplex b).obj P) ((pullbackComplex b).obj N)).hom ≫
      ((canonicalDerivedTensorProduct X'.O).comparison
          ((pullbackComplex a).obj ((pullbackComplex b).obj P))
          ((pullbackComplex a).obj ((pullbackComplex b).obj N))
          ((Stacks.SheafOfModules.KFlat.kFlat_iff_kFlatBifunctor X'.O _).2
            (kFlatBifunctor_pullbackComplex a _ (kFlatBifunctor_pullbackComplex b P hP hflatP)
              (isFlat_pullbackComplex_X b P hflatP)))
          ((Stacks.SheafOfModules.KFlat.kFlat_iff_kFlatBifunctor X'.O _).2
            (kFlatBifunctor_pullbackComplex a _ (kFlatBifunctor_pullbackComplex b N hN hflatN)
              (isFlat_pullbackComplex_X b N hflatN)))).inv ≫
      (Functor.uncurry.obj (derivedTensorProductFunctor X'.O)).map
        ((flatPullbackCompIso a b P hP hflatP).inv ×ₘ
          (flatPullbackCompIso a b N hN hflatN).inv) := by
  have hbP := kFlatBifunctor_pullbackComplex b P hP hflatP
  have hbN := kFlatBifunctor_pullbackComplex b N hN hflatN
  have hbfP := isFlat_pullbackComplex_X b P hflatP
  have hbfN := isFlat_pullbackComplex_X b N hflatN
  have hTot := Stacks.SheafOfModules.kFlat_tensorComplex Y.O hP hN
  have hfTot := isFlat_tensorComplex_X Y.O P N hflatP hflatN
  have hTot' := Stacks.SheafOfModules.kFlat_tensorComplex Y'.O hbP hbN
  have hfTot' := isFlat_tensorComplex_X Y'.O _ _ hbfP hbfN
  have hnat := (derivedPullbackTensorIso a).hom.naturality
    ((flatPullbackIso b P hP hflatP).inv ×ₘ (flatPullbackIso b N hN hflatN).inv)
  have hmodel := derivedPullbackTensorIso_hom_app_model_eq a ((pullbackComplex b).obj P)
    ((pullbackComplex b).obj N) hbP hbN hbfP hbfN
  have hflat := flatPullbackIso_naturality a (pullbackTensorTotalIso b.toModulesHom P N).hom
    (kFlatBifunctor_pullbackComplex b _ hTot hfTot) hTot'
    (isFlat_pullbackComplex_X b _ hfTot) hfTot'
  have hψ : (Functor.uncurry.obj (derivedTensorProductFunctor X'.O)).map
        ((flatPullbackIso a ((pullbackComplex b).obj P) hbP hbfP).inv ×ₘ
          (flatPullbackIso a ((pullbackComplex b).obj N) hbN hbfN).inv) ≫
      (Functor.uncurry.obj (derivedTensorProductFunctor X'.O)).map
        ((derivedPullback a).map (flatPullbackIso b P hP hflatP).inv ×ₘ
          (derivedPullback a).map (flatPullbackIso b N hN hflatN).inv) =
      (Functor.uncurry.obj (derivedTensorProductFunctor X'.O)).map
        ((flatPullbackCompIso a b P hP hflatP).inv ×ₘ
          (flatPullbackCompIso a b N hN hflatN).inv) := by
    rw [← Functor.map_comp]
    rfl
  rw [derivedPullbackTensorIso_hom_app_model_eq b P N hP hN hflatP hflatN]
  exact CategoryTheory.tensor_comp_model_aux (derivedPullback a) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    hnat hmodel (Iso.inv_hom_id _) hflat hψ

end Composite

end Stacks.Sheaves.DerivedPullback.OfToposHom

namespace AlgebraicGeometry.RingedToposHom.TwoIso

open Stacks.Sheaves.DerivedPullback.OfToposHom
open Stacks.Sheaves.DerivedPullback (pullbackComplexFunctor)

universe u

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] hasLeftDerivedFunctor_pullbackOnHomotopy

variable {X' X Y' Y : RingedTopos.{u, u, u}}
  [X'.J.HasSheafCompose (forget RingCat.{u})] [X.J.HasSheafCompose (forget RingCat.{u})]
  [Y'.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X'.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y'.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X'.J.HasSheafCompose (forget AddCommGrpCat.{u})] [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y'.J.HasSheafCompose (forget AddCommGrpCat.{u})] [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X'.J AddCommGrpCat.{u}] [X'.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y'.J AddCommGrpCat.{u}] [Y'.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X'.J (Type u)] [HasSheafify X.J (Type u)]
  [HasSheafify Y'.J (Type u)] [HasSheafify Y.J (Type u)]
  {f : RingedToposHom X Y} {g : RingedToposHom Y' Y} {f' : RingedToposHom X' Y'}
  {g' : RingedToposHom X' X} (s : TwoIso (g.comp f') (f.comp g'))

/-- The algebra behind `derivedPullbackSquareIso_hom_app_flatPullbackIso`, over variables. -/
theorem _root_.CategoryTheory.square_flat_aux {𝒜 ℬ 𝒞 𝒟 : Type*} [Category 𝒜] [Category ℬ]
    [Category 𝒞] [Category 𝒟] (Lg : 𝒜 ⥤ ℬ) (Lf' : ℬ ⥤ 𝒟) (Lf : 𝒜 ⥤ 𝒞) (Lg' : 𝒞 ⥤ 𝒟)
    (S : Lg ⋙ Lf' ⟶ Lf ⋙ Lg') {QP H : 𝒜} (a : QP ⟶ H)
    {Hf Qf : 𝒞} (cf : Lf.obj H ⟶ Hf) (qf : Hf ≅ Qf)
    {Hg Qg : ℬ} (cg : Lg.obj H ⟶ Hg) (qg : Hg ≅ Qg)
    {Hg'f Qg'f Hf'g Qf'g : 𝒟} (cg' : Lg'.obj Hf ⟶ Hg'f) (qg'f : Hg'f ≅ Qg'f)
    (cf' : Lf'.obj Hg ⟶ Hf'g) (qf'g : Hf'g ≅ Qf'g) (m : Hf'g ⟶ Hg'f) (mQ : Qf'g ⟶ Qg'f)
    (fpf : Lf.obj QP ⟶ Qf) (fpg'f : Lg'.obj Qf ⟶ Qg'f) (fpg : Lg.obj QP ⟶ Qg)
    (fpf'g : Lf'.obj Qg ⟶ Qf'g)
    (hfpf : fpf = Lf.map a ≫ cf ≫ qf.hom) (hfpg'f : fpg'f = Lg'.map qf.inv ≫ cg' ≫ qg'f.hom)
    (hfpg : fpg = Lg.map a ≫ cg ≫ qg.hom) (hfpf'g : fpf'g = Lf'.map qg.inv ≫ cf' ≫ qf'g.hom)
    (hS : S.app H ≫ Lg'.map cf ≫ cg' = Lf'.map cg ≫ cf' ≫ m)
    (hq : m ≫ qg'f.hom = qf'g.hom ≫ mQ) :
    S.app QP ≫ Lg'.map fpf ≫ fpg'f = Lf'.map fpg ≫ fpf'g ≫ mQ := by
  have hnat := S.naturality a
  simp only [Functor.comp_map] at hnat
  subst hfpf hfpg'f hfpg hfpf'g
  simp only [Functor.map_comp, Category.assoc, ← Functor.map_comp_assoc Lg' qf.hom,
    Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp,
    ← Functor.map_comp_assoc Lf' qg.hom]
  rw [← reassoc_of% hnat, reassoc_of% hS, hq]

/-- The algebra of `tensorComparison_square_model`, over variables. -/
theorem _root_.CategoryTheory.tensor_square_model_aux {𝒞 : Type*} [Category 𝒞]
    {S₀ O₁ T₁ T U₁ U₂ U₃ U₄ U₅ V R₀ R₁ R₂ R₃ R₄ R₅ V' Z₁ : 𝒞}
    (l₁ : S₀ ⟶ O₁) (l₂ : O₁ ⟶ T₁) (σt : T₁ ⟶ T) (σ₀ : S₀ ⟶ R₀) (r₁ : R₀ ⟶ Z₁) (r₂ : Z₁ ⟶ T)
    (A₁ : S₀ ⟶ U₁) (A₂ : U₁ ⟶ U₂) (A₃ : U₂ ⟶ U₃) (A₄ : U₃ ⟶ U₄) (A₅ : U₄ ⟶ U₅) (A₆ : U₅ ⟶ V)
    (ψ₁ : V ⟶ T₁) (B₁ : R₀ ⟶ R₁) (B₂ : R₁ ⟶ R₂) (B₃ : R₂ ⟶ R₃) (B₄ : R₃ ⟶ R₄) (B₅ : R₄ ⟶ R₅)
    (B₆ : R₅ ⟶ V') (ψ₂ : V' ⟶ T) (σT : U₁ ⟶ R₁) (qmT : U₃ ⟶ R₃) (qTm : U₅ ⟶ R₅) (qmm : V ⟶ V')
    (hL : l₁ ≫ l₂ = A₁ ≫ A₂ ≫ A₃ ≫ A₄ ≫ A₅ ≫ A₆ ≫ ψ₁)
    (hR : r₁ ≫ r₂ = B₁ ≫ B₂ ≫ B₃ ≫ B₄ ≫ B₅ ≫ B₆ ≫ ψ₂)
    (hσnat : A₁ ≫ σT = σ₀ ≫ B₁) (hσmodel : σT ≫ B₂ ≫ B₃ = A₂ ≫ A₃ ≫ qmT)
    (hcx : qmT ≫ B₄ ≫ B₅ = A₄ ≫ A₅ ≫ qTm) (hcmp : A₆ ≫ qmm = qTm ≫ B₆)
    (hψ : ψ₁ ≫ σt = qmm ≫ ψ₂) :
    l₁ ≫ l₂ ≫ σt = σ₀ ≫ r₁ ≫ r₂ := by
  rw [← Category.assoc, hL, hR]
  simp only [Category.assoc]
  rw [hψ, reassoc_of% hcmp, ← reassoc_of% hcx, ← reassoc_of% hσmodel, reassoc_of% hσnat]

/-- **`Σ` on a K-flat complex with flat terms**: `Σ` followed by the computations of
`L(g')^* Lf^*` by degreewise pullbacks is the computations of `L(f')^* Lg^*` by degreewise
pullbacks followed by `m`. -/
theorem derivedPullbackSquareIso_hom_app_flatPullbackIso
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hP : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) P)
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (P.X i)) :
    (derivedPullbackSquareIso s).hom.app (DerivedCategory.Q.obj P) ≫
        (derivedPullback g').map (flatPullbackIso f P hP hflat).hom ≫
        (flatPullbackIso g' ((Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom.pullbackComplex
            f).obj P) (kFlatBifunctor_pullbackComplex f P hP hflat)
          (Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom.isFlat_pullbackComplex_X f P
            hflat)).hom =
      (derivedPullback f').map (flatPullbackIso g P hP hflat).hom ≫
        (flatPullbackIso f' ((Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom.pullbackComplex
            g).obj P) (kFlatBifunctor_pullbackComplex g P hP hflat)
          (Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom.isFlat_pullbackComplex_X g P
            hflat)).hom ≫
        DerivedCategory.Q.map (squarePullbackComplexIso s P).hom := by
  have hS := derivedPullbackSquareIso_hom_app_comp s
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)
  have hq := DerivedCategory.quotientCompQhIso_hom_naturality
    (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O))
    (squarePullbackComplexIso s P).hom
  exact CategoryTheory.square_flat_aux (derivedPullback g) (derivedPullback f')
    (derivedPullback f) (derivedPullback g') (derivedPullbackSquareIso s).hom
    ((DerivedCategory.quotientCompQhIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).inv.app P)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl hS hq

/-- `Σ` on a K-flat complex with flat terms, in terms of the computations of the two iterated
derived pullbacks by degreewise pullbacks. -/
theorem flatPullbackCompIso_inv_comp_derivedPullbackSquareIso_hom_app
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hP : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) P)
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (P.X i)) :
    (flatPullbackCompIso f' g P hP hflat).inv ≫
        (derivedPullbackSquareIso s).hom.app (DerivedCategory.Q.obj P) =
      DerivedCategory.Q.map (squarePullbackComplexIso s P).hom ≫
        (flatPullbackCompIso g' f P hP hflat).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  exact (derivedPullbackSquareIso_hom_app_flatPullbackIso s P hP hflat).trans
    (Category.assoc _ _ _).symm

end AlgebraicGeometry.RingedToposHom.TwoIso

end
