module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorSquare

/-!
# The comparisons of Stacks 07A4 are compatible around a 2-commutative square of ringed topoi

Let
```
              g'
  (Sh(𝒞'), 𝒪_{𝒞'}) ⟶ (Sh(𝒞), 𝒪_𝒞)
        | f'                | f
        v                   v
  (Sh(𝒟'), 𝒪_{𝒟'}) ⟶ (Sh(𝒟), 𝒪_𝒟)
              g
```
be a square of morphisms of ringed topoi commuting up to a 2-isomorphism `s : g ∘ f' ≅ f ∘ g'`,
and let `Σ : L(f')^* ∘ Lg^* ≅ L(g')^* ∘ Lf^*` be the isomorphism of the two derived pullbacks
around it. For `M`, `N` in `D(𝒪_𝒟)` the two composites

`L(f')^*Lg^*(M ⊗^𝐋 N) ⟶ L(f')^*(Lg^*M ⊗^𝐋 Lg^*N) ⟶ L(f')^*Lg^*M ⊗^𝐋 L(f')^*Lg^*N
  ⟶ L(g')^*Lf^*M ⊗^𝐋 L(g')^*Lf^*N`

and

`L(f')^*Lg^*(M ⊗^𝐋 N) ⟶ L(g')^*Lf^*(M ⊗^𝐋 N) ⟶ L(g')^*(Lf^*M ⊗^𝐋 Lf^*N)
  ⟶ L(g')^*Lf^*M ⊗^𝐋 L(g')^*Lf^*N`

built from the comparisons of [Stacks, Tag 07A4] for the four morphisms of the square and from
`Σ` agree. This is the compatibility of the four comparisons around the square which the
compatibility of the projection formula map with base change ([Stacks, Tag 0E48]) consumes, in
the form `Stacks.AffineProjectionFormula.TensorComparisonCompatible`.

On a pair of K-flat complexes with flat terms every arrow is computed by degreewise pullbacks,
and the two composites become the two composites of the comparisons of [Stacks, Tag 03EL] on total
tensor complexes around the square, which agree by
`AlgebraicGeometry.RingedToposHom.TwoIso.pullbackTensorTotalIso_squarePullbackIso`. Both
composites are components of natural transformations, and every pair of objects is isomorphic to
a pair of such complexes, so the equation holds everywhere.

## Main results

* `Stacks.AffineProjectionFormula.tensorComparisonCompatible_of_iso`: the compatibility is
  invariant under isomorphism of the pair of objects.
* `AlgebraicGeometry.RingedToposHom.TwoIso.tensorComparison_square_model`: the compatibility at
  a pair of K-flat complexes with flat terms.
* `AlgebraicGeometry.RingedToposHom.TwoIso.tensorComparisonCompatible`: **the comparisons of
  [Stacks, Tag 07A4] are compatible around a 2-commutative square of ringed topoi**, at every
  pair of objects.

## References

* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 0E48](https://stacks.math.columbia.edu/tag/0E48)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPullbackOfToposHom
open scoped CategoryTheory.Prod

namespace Stacks.AffineProjectionFormula

variable {S : Type*} {T : Type*} {S' : Type*} {T' : Type*}
  [Category S] [Category T] [Category S'] [Category T']
  {Lf : S ⥤ T} {Lf' : S' ⥤ T'} {Lg : S ⥤ S'} {Lg' : T ⥤ T'} {Lc : S ⥤ T'}
  (eg : Lg ⋙ Lf' ≅ Lc) (ef : Lf ⋙ Lg' ≅ Lc)
  (A : S × S ⥤ S) (A' : S' × S' ⥤ S') (B : T × T ⥤ T) (B' : T' × T' ⥤ T')
  (αf : A ⋙ Lf ⟶ Lf.prod Lf ⋙ B) (αf' : A' ⋙ Lf' ⟶ Lf'.prod Lf' ⋙ B')
  (αg : A ⋙ Lg ⟶ Lg.prod Lg ⋙ A') (αg' : B ⋙ Lg' ⟶ Lg'.prod Lg' ⋙ B')

/-- The compatibility of the four tensor comparisons around a square is invariant under
isomorphism of the pair of objects: both of its sides are components of natural
transformations. -/
theorem tensorComparisonCompatible_of_iso {M N M' N' : S} (e : ((M, N) : S × S) ≅ (M', N'))
    (h : TensorComparisonCompatible eg ef A A' B B' αf αf' αg αg' M N) :
    TensorComparisonCompatible eg ef A A' B B' αf αf' αg αg' M' N' := by
  let σ := (squareCompositeIso eg ef).hom
  let α : A ⋙ Lg ⋙ Lf' ⟶ (Lf ⋙ Lg').prod (Lf ⋙ Lg') ⋙ B' :=
    Functor.whiskerRight αg Lf' ≫ Functor.whiskerLeft (Lg.prod Lg) αf' ≫
      Functor.whiskerRight (NatTrans.prod σ σ) B'
  let β : A ⋙ Lg ⋙ Lf' ⟶ (Lf ⋙ Lg').prod (Lf ⋙ Lg') ⋙ B' :=
    Functor.whiskerLeft A σ ≫ Functor.whiskerRight αf Lg' ≫ Functor.whiskerLeft (Lf.prod Lf) αg'
  have hX : α.app (M, N) = β.app (M, N) := h
  change α.app (M', N') = β.app (M', N')
  rw [← cancel_epi ((A ⋙ Lg ⋙ Lf').map e.hom), α.naturality, β.naturality, hX]

/-- When the two composites around the square are identified with the second one by the
identity, the compatibility of the four tensor comparisons is the equation with the
identification `eg` itself in place of `squareCompositeIso`. -/
theorem tensorComparisonCompatible_refl_iff (eg : Lg ⋙ Lf' ≅ Lf ⋙ Lg') (M N : S) :
    TensorComparisonCompatible eg (Iso.refl (Lf ⋙ Lg')) A A' B B' αf αf' αg αg' M N ↔
      Lf'.map (αg.app (M, N)) ≫ αf'.app (Lg.obj M, Lg.obj N) ≫
          B'.map (eg.hom.app M ×ₘ eg.hom.app N) =
        eg.hom.app (A.obj (M, N)) ≫ Lg'.map (αf.app (M, N)) ≫ αg'.app (Lf.obj M, Lf.obj N) := by
  simp only [TensorComparisonCompatible, squareCompositeIso_hom_app, Iso.refl_inv,
    NatTrans.id_app, Category.comp_id]

end Stacks.AffineProjectionFormula

namespace AlgebraicGeometry.RingedToposHom.TwoIso

open Stacks.Sheaves.DerivedPullback.OfToposHom Stacks.DerivedTensor.RingedSite
open Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom
  (pullbackComplex isFlat_pullbackComplex_X)

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


/-- Moving the two isomorphisms of a commutative square to the other side. -/
theorem _root_.CategoryTheory.inv_comp_eq_comp_inv_of_hom {𝒞 : Type*} [Category 𝒞] {A B C D : 𝒞}
    (α : A ≅ B) (β : C ≅ D) (x : A ⟶ C) (q : B ⟶ D) (h : x ≫ β.hom = α.hom ≫ q) :
    α.inv ≫ x = q ≫ β.inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv, h]

omit [HasSheafify X'.J (Type u)] [HasSheafify X.J (Type u)] [HasSheafify Y'.J (Type u)]
  [HasSheafify Y.J (Type u)] in
/-- The compatibility of Stacks 03EL on total tensor complexes around the square, read in the
derived category. -/
theorem Q_map_squarePullbackComplexIso_pullbackTensorTotalIso
    (P N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    DerivedCategory.Q.map (squarePullbackComplexIso s (HomologicalComplex.mapBifunctor P N
          (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) (ComplexShape.up ℤ))).hom ≫
        DerivedCategory.Q.map ((pullbackComplex g').map
          (Stacks.Sheaves.DerivedPullback.pullbackTensorTotalIso f.toModulesHom P N).hom) ≫
        DerivedCategory.Q.map (Stacks.Sheaves.DerivedPullback.pullbackTensorTotalIso g'.toModulesHom
          ((pullbackComplex f).obj P) ((pullbackComplex f).obj N)).hom =
      DerivedCategory.Q.map ((pullbackComplex f').map
          (Stacks.Sheaves.DerivedPullback.pullbackTensorTotalIso g.toModulesHom P N).hom) ≫
        DerivedCategory.Q.map (Stacks.Sheaves.DerivedPullback.pullbackTensorTotalIso f'.toModulesHom
          ((pullbackComplex g).obj P) ((pullbackComplex g).obj N)).hom ≫
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap
          ((squarePullbackComplexIso s P).hom) ((squarePullbackComplexIso s N).hom)
          (Stacks.SheafOfModules.Tensor.sheafTensor X'.O) (ComplexShape.up ℤ)) := by
  simp only [← Functor.map_comp]
  exact congrArg DerivedCategory.Q.map (pullbackTensorTotalIso_squarePullbackIso s P N).symm

/-- The K-flat comparison of the target is natural along `m`. -/
theorem comparison_inv_comp_squarePullbackComplexIso
    (P N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hP : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) P)
    (hN : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) N)
    (hflatP : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (P.X i))
    (hflatN : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (N.X i)) :
    ((canonicalDerivedTensorProduct X'.O).comparison _ _
        ((Stacks.SheafOfModules.KFlat.kFlat_iff_kFlatBifunctor X'.O _).2
          (kFlatBifunctor_pullbackComplex f' _ (kFlatBifunctor_pullbackComplex g P hP hflatP)
            (isFlat_pullbackComplex_X g P hflatP)))
        ((Stacks.SheafOfModules.KFlat.kFlat_iff_kFlatBifunctor X'.O _).2
          (kFlatBifunctor_pullbackComplex f' _ (kFlatBifunctor_pullbackComplex g N hN hflatN)
            (isFlat_pullbackComplex_X g N hflatN)))).inv ≫
        (Functor.uncurry.obj (derivedTensorProductFunctor X'.O)).map
          (DerivedCategory.Q.map (squarePullbackComplexIso s P).hom ×ₘ
            DerivedCategory.Q.map (squarePullbackComplexIso s N).hom) =
      DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap
          ((squarePullbackComplexIso s P).hom) ((squarePullbackComplexIso s N).hom)
          (Stacks.SheafOfModules.Tensor.sheafTensor X'.O) (ComplexShape.up ℤ)) ≫
        ((canonicalDerivedTensorProduct X'.O).comparison _ _
        ((Stacks.SheafOfModules.KFlat.kFlat_iff_kFlatBifunctor X'.O _).2
          (kFlatBifunctor_pullbackComplex g' _ (kFlatBifunctor_pullbackComplex f P hP hflatP)
            (isFlat_pullbackComplex_X f P hflatP)))
        ((Stacks.SheafOfModules.KFlat.kFlat_iff_kFlatBifunctor X'.O _).2
          (kFlatBifunctor_pullbackComplex g' _ (kFlatBifunctor_pullbackComplex f N hN hflatN)
            (isFlat_pullbackComplex_X f N hflatN)))).inv := by
  exact CategoryTheory.inv_comp_eq_comp_inv_of_hom _ _ _ _ ((Category.assoc _ _ _).trans
    ((canonicalDerivedTensorProduct X'.O).comparison_naturality
      (squarePullbackComplexIso s P).hom (squarePullbackComplexIso s N).hom _ _ _ _))

/-- `Σ` in each factor, read through the computations of the iterated derived pullbacks. -/
theorem tensor_flatPullbackCompIso_inv_comp_derivedPullbackSquareIso
    (P N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hP : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) P)
    (hN : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) N)
    (hflatP : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (P.X i))
    (hflatN : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (N.X i)) :
    (Functor.uncurry.obj (derivedTensorProductFunctor X'.O)).map
        ((flatPullbackCompIso f' g P hP hflatP).inv ×ₘ (flatPullbackCompIso f' g N hN hflatN).inv) ≫
      (Functor.uncurry.obj (derivedTensorProductFunctor X'.O)).map
        ((derivedPullbackSquareIso s).hom.app (DerivedCategory.Q.obj P) ×ₘ
          (derivedPullbackSquareIso s).hom.app (DerivedCategory.Q.obj N)) =
      (Functor.uncurry.obj (derivedTensorProductFunctor X'.O)).map
        (DerivedCategory.Q.map (squarePullbackComplexIso s P).hom ×ₘ
          DerivedCategory.Q.map (squarePullbackComplexIso s N).hom) ≫
      (Functor.uncurry.obj (derivedTensorProductFunctor X'.O)).map
        ((flatPullbackCompIso g' f P hP hflatP).inv ×ₘ
          (flatPullbackCompIso g' f N hN hflatN).inv) := by
  rw [← Functor.map_comp, ← Functor.map_comp, prod_comp, prod_comp,
    flatPullbackCompIso_inv_comp_derivedPullbackSquareIso_hom_app s P hP hflatP,
    flatPullbackCompIso_inv_comp_derivedPullbackSquareIso_hom_app s N hN hflatN]


/-- **The comparisons of Stacks 07A4 around a 2-commutative square, at a pair of K-flat complexes
with flat terms.** -/
theorem tensorComparison_square_model
    (P N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hP : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) P)
    (hN : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) N)
    (hflatP : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (P.X i))
    (hflatN : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (N.X i)) :
    (derivedPullback f').map ((derivedPullbackTensorIso g).hom.app
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj N)) ≫
      (derivedPullbackTensorIso f').hom.app
        ((derivedPullback g).obj (DerivedCategory.Q.obj P),
          (derivedPullback g).obj (DerivedCategory.Q.obj N)) ≫
      (Functor.uncurry.obj (derivedTensorProductFunctor X'.O)).map
        ((derivedPullbackSquareIso s).hom.app (DerivedCategory.Q.obj P) ×ₘ
          (derivedPullbackSquareIso s).hom.app (DerivedCategory.Q.obj N)) =
    (derivedPullbackSquareIso s).hom.app
        ((Functor.uncurry.obj (derivedTensorProductFunctor Y.O)).obj
          (DerivedCategory.Q.obj P, DerivedCategory.Q.obj N)) ≫
      (derivedPullback g').map ((derivedPullbackTensorIso f).hom.app
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj N)) ≫
      (derivedPullbackTensorIso g').hom.app
        ((derivedPullback f).obj (DerivedCategory.Q.obj P),
          (derivedPullback f).obj (DerivedCategory.Q.obj N)) :=
  CategoryTheory.tensor_square_model_aux _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (derivedPullback_map_derivedPullbackTensorIso_comp_model f' g P N hP hN hflatP hflatN)
    (derivedPullback_map_derivedPullbackTensorIso_comp_model g' f P N hP hN hflatP hflatN)
    ((derivedPullbackSquareIso s).hom.naturality
      ((canonicalDerivedTensorProduct Y.O).comparison P N
        ((Stacks.SheafOfModules.KFlat.kFlat_iff_kFlatBifunctor Y.O P).2 hP)
        ((Stacks.SheafOfModules.KFlat.kFlat_iff_kFlatBifunctor Y.O N).2 hN)).hom)
    (derivedPullbackSquareIso_hom_app_flatPullbackIso s _
      (Stacks.SheafOfModules.kFlat_tensorComplex Y.O hP hN)
      (Stacks.Sheaves.DerivedPullback.isFlat_tensorComplex_X Y.O P N hflatP hflatN))
    (Q_map_squarePullbackComplexIso_pullbackTensorTotalIso s P N)
    (comparison_inv_comp_squarePullbackComplexIso s P N hP hN hflatP hflatN)
    (tensor_flatPullbackCompIso_inv_comp_derivedPullbackSquareIso s P N hP hN hflatP hflatN)


/-- **The comparisons of Stacks 07A4 are compatible around a 2-commutative square of ringed
topoi.** For a square `s : g ∘ f' ≅ f ∘ g'` and any `M`, `N` in `D(𝒪_𝒟)`, the comparison along
`g` followed by the comparison along `f'` and by `Σ` in each factor is `Σ` followed by the
comparison along `f` and by the comparison along `g'`, where
`Σ : L(f')^* ∘ Lg^* ≅ L(g')^* ∘ Lf^*` is `derivedPullbackSquareIso`. In the vocabulary of
[Stacks, Tag 0E48] this is the compatibility of the four comparisons around the square. -/
theorem tensorComparisonCompatible
    (M N : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :
    Stacks.AffineProjectionFormula.TensorComparisonCompatible (derivedPullbackSquareIso s)
      (Iso.refl _) (Functor.uncurry.obj (derivedTensorProductFunctor Y.O))
      (Functor.uncurry.obj (derivedTensorProductFunctor Y'.O))
      (Functor.uncurry.obj (derivedTensorProductFunctor X.O))
      (Functor.uncurry.obj (derivedTensorProductFunctor X'.O))
      (derivedPullbackTensorIso f).hom (derivedPullbackTensorIso f').hom
      (derivedPullbackTensorIso g).hom (derivedPullbackTensorIso g').hom M N := by
  have := Stacks.Sheaves.DerivedPullback.flatKFlatModelPairsQ_isLocalization Y
  have : (Stacks.Sheaves.DerivedPullback.flatKFlatModelPairsQ Y).EssSurj :=
    Localization.essSurj (Stacks.Sheaves.DerivedPullback.flatKFlatModelPairsQ Y)
      (Stacks.Sheaves.DerivedPullback.flatKFlatModelPairsW Y)
  refine Stacks.AffineProjectionFormula.tensorComparisonCompatible_of_iso _ _ _ _ _ _ _ _ _ _
    ((Stacks.Sheaves.DerivedPullback.flatKFlatModelPairsIso Y
        ((Stacks.Sheaves.DerivedPullback.flatKFlatModelPairsQ Y).objPreimage (M, N))).symm ≪≫
      (Stacks.Sheaves.DerivedPullback.flatKFlatModelPairsQ Y).objObjPreimageIso (M, N)) ?_
  rw [Stacks.AffineProjectionFormula.tensorComparisonCompatible_refl_iff]
  exact tensorComparison_square_model s _ _
    ((Stacks.Sheaves.DerivedPullback.flatKFlatModelPairsQ Y).objPreimage (M, N)).1.property.1
    ((Stacks.Sheaves.DerivedPullback.flatKFlatModelPairsQ Y).objPreimage (M, N)).2.property.1
    ((Stacks.Sheaves.DerivedPullback.flatKFlatModelPairsQ Y).objPreimage (M, N)).1.property.2
    ((Stacks.Sheaves.DerivedPullback.flatKFlatModelPairsQ Y).objPreimage (M, N)).2.property.2

end AlgebraicGeometry.RingedToposHom.TwoIso

end
