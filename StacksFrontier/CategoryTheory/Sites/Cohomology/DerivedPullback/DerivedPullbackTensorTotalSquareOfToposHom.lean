module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorIsoCompositionOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorTotalSquare
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RelativeCupProductBraidingOfToposHom

/-! # Derived pullback against the comparison with the total tensor complex, for a morphism of
ringed topoi

Let `f : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi in the sense of Stacks 01D3,
part (2): a morphism of the underlying topoi together with the structure map, with no functor
between the underlying sites.  For cochain complexes `K`, `M` of `O_D`-modules, **Stacks 0FPH**
asserts that the two paths from `Lf^*(K ⊗^L_{O_D} M)` to `Tot(f^*K ⊗_{O_C} f^*M)`,

* `Lf^*(K ⊗^L M) ⟶ Lf^*Tot(K ⊗ M) ⟶ f^*Tot(K ⊗ M) ⟶ Tot(f^*K ⊗ f^*M)` and
* `Lf^*(K ⊗^L M) ⟶ Lf^*K ⊗^L Lf^*M ⟶ f^*K ⊗^L f^*M ⟶ Tot(f^*K ⊗ f^*M)`,

agree.

## Main results

* `Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullback_toTensor_square`: **Stacks 0FPH**
  for an arbitrary morphism of ringed topoi, with no hypothesis and no class argument.
* `Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullback_toTensor_square_of_instances`: the
  same square with the class arguments of the derived tensor product kept as binders.

## Implementation notes

The proof is the source's.  At a pair of K-flat complexes with flat terms both paths are halves of
the five-step chain defining the comparison of Stacks 07A4, which is
`Stacks.Sheaves.DerivedPullback.OfToposHom.toTensor_square_of_kFlat`.  For arbitrary `K` and `M`
one chooses K-flat resolutions `P ⟶ K`, `N ⟶ M` with flat terms (Stacks 06YS); every arrow of
the square is natural, and the derived pullback of the induced map
`P ⊗^L N ⟶ K ⊗^L M` is invertible, so the square at `(K, M)` follows from the square at
`(P, N)`.

## References

* [Stacks Project, Tag 0FPH](https://stacks.math.columbia.edu/tag/0FPH)
* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom (pullbackComplex)

namespace Stacks.Sheaves.DerivedPullback.OfToposHom

universe u

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance]
  Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy

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

/-- **Stacks 0FPH, at the variable block of the derived tensor product.**  This is
`derivedPullback_toTensor_square` with the `Prop`-valued class arguments under which the total
tensor complexes and the derived tensor products are formed kept as binders. -/
theorem derivedPullback_toTensor_square_of_instances
    (K M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    (derivedPullback f).map
          ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct Y.O).toTensor K M) ≫
        pullbackComparisonQ f
            (((Stacks.SheafOfModules.Tensor.tensorComplex Y.O).obj K).obj M) ≫
        DerivedCategory.Q.map (pullbackTensorComplexIso f K M).hom =
      (derivedPullbackTensorIso f).hom.app (DerivedCategory.Q.obj K, DerivedCategory.Q.obj M) ≫
        bifunctorMap (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).tensor
            (pullbackComparisonQ f K) (pullbackComparisonQ f M) ≫
        (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).toTensor
          ((pullbackComplex f).obj K) ((pullbackComplex f).obj M) := by
  obtain ⟨P, p, hP, hflatP, hp, -⟩ :=
    Stacks.SheafOfModules.KFlatResolution.exists_kFlatResolution Y.O K
  obtain ⟨N, q, hN, hflatN, hq, -⟩ :=
    Stacks.SheafOfModules.KFlatResolution.exists_kFlatResolution Y.O M
  have hp' : QuasiIso p := hp
  have hq' : QuasiIso q := hq
  have hiso : IsIso ((derivedPullback f).map
      (bifunctorMap (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct Y.O).tensor
        (DerivedCategory.Q.map p) (DerivedCategory.Q.map q))) := by
    have hpair : bifunctorMap
          (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct Y.O).tensor
          (DerivedCategory.Q.map p) (DerivedCategory.Q.map q) =
        ((Functor.uncurry.obj
            (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct Y.O).tensor).mapIso
          ((asIso (DerivedCategory.Q.map p)).prod
            (asIso (DerivedCategory.Q.map q)))).hom := rfl
    rw [hpair]
    infer_instance
  refine paths_eq_of_epi
    ((derivedPullback f).map
      (bifunctorMap (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct Y.O).tensor
        (DerivedCategory.Q.map p) (DerivedCategory.Q.map q)))
    _ _ _ _ _ _ _ _ _ _ _ _
    ((derivedPullback f).map (DerivedCategory.Q.map (tensorComplexMap Y p q)))
    (DerivedCategory.Q.map ((pullbackComplex f).map (tensorComplexMap Y p q)))
    (bifunctorMap (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).tensor
      ((derivedPullback f).map (DerivedCategory.Q.map p))
      ((derivedPullback f).map (DerivedCategory.Q.map q)))
    (bifunctorMap (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).tensor
      (DerivedCategory.Q.map ((pullbackComplex f).map p))
      (DerivedCategory.Q.map ((pullbackComplex f).map q)))
    (DerivedCategory.Q.map
      (tensorComplexMap X ((pullbackComplex f).map p) ((pullbackComplex f).map q)))
    ?_ ?_ ?_ ?_ ?_ ?_
    (toTensor_square_of_kFlat f P N hP hN hflatP hflatN)
  · rw [← Functor.map_comp, ← Functor.map_comp]
    refine congrArg (derivedPullback f).map ?_
    dsimp only [bifunctorMap]
    rw [Category.assoc]
    exact (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct Y.O).toTensor_naturality
      p q
  · exact pullbackComparisonQ_naturality f (tensorComplexMap Y p q)
  · rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg DerivedCategory.Q.map
      (pullbackTensorTotalIso_hom_naturality f.toModulesHom p q)
  · exact (derivedPullbackTensorIso f).hom.naturality
      ((DerivedCategory.Q.map p, DerivedCategory.Q.map q) :
        ((DerivedCategory.Q.obj P, DerivedCategory.Q.obj N) : _ × _) ⟶
          (DerivedCategory.Q.obj K, DerivedCategory.Q.obj M))
  · rw [bifunctorMap_comp, bifunctorMap_comp, pullbackComparisonQ_naturality f p,
      pullbackComparisonQ_naturality f q]
  · dsimp only [bifunctorMap]
    rw [Category.assoc]
    exact (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).toTensor_naturality
      ((pullbackComplex f).map p) ((pullbackComplex f).map q)

section Unconditional

attribute [local instance high]
  Stacks.Cohomology.RelativeCupProductOfToposHom.hasMapBifunctor_sheafTensor_ringedTopos

/-- **Stacks 0FPH, for a morphism of ringed topoi.**  For a morphism of ringed topoi
`f : (Sh(C), O_C) ⟶ (Sh(D), O_D)` — a morphism of the underlying topoi together with the
structure map — and cochain complexes `K`, `M` of `O_D`-modules, the square formed by the
canonical maps from the derived tensor product to the ordinary total tensor complex, the
comparison `Lf^*(K ⊗^L_{O_D} M) ≅ Lf^*K ⊗^L_{O_C} Lf^*M` of Stacks 07A4 followed by the
comparison `Lf^* ⟶ f^*` in each tensor factor, and that same comparison at `Tot(K ⊗ M)`
followed by the identification `f^*Tot(K ⊗_{O_D} M) ≅ Tot(f^*K ⊗_{O_C} f^*M)` of Stacks 03EL,
commutes.

The statement has no hypothesis and no class argument of its own: instance search supplies
every class argument of `derivedPullback_toTensor_square_of_instances`. -/
@[stacks 0FPH "for an arbitrary morphism of ringed topoi in the two-field sense of Tag 01D3, \
  part (2) (a morphism of the underlying topoi with its structure map, no functor between the \
  underlying sites and no morphism-of-sites hypothesis), at RingedTopos.{u, u, u}, for all \
  complexes K, M; the statement carries no hypothesis or class argument"]
theorem derivedPullback_toTensor_square {X Y : RingedTopos.{u, u, u}}
    (f : AlgebraicGeometry.RingedToposHom X Y)
    (K M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    (derivedPullback f).map
          ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct Y.O).toTensor K M) ≫
        pullbackComparisonQ f
            (((Stacks.SheafOfModules.Tensor.tensorComplex Y.O).obj K).obj M) ≫
        DerivedCategory.Q.map (pullbackTensorComplexIso f K M).hom =
      (derivedPullbackTensorIso f).hom.app (DerivedCategory.Q.obj K, DerivedCategory.Q.obj M) ≫
        bifunctorMap (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).tensor
            (pullbackComparisonQ f K) (pullbackComparisonQ f M) ≫
        (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).toTensor
          ((pullbackComplex f).obj K) ((pullbackComplex f).obj M) :=
  derivedPullback_toTensor_square_of_instances f K M

end Unconditional

end Stacks.Sheaves.DerivedPullback.OfToposHom

end
