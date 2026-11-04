module

public import StacksFrontier.CategoryTheory.BifunctorComparisonConstraints
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorTotalSquare
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.KoszulBraidingFlipIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedTensorBraidingNatTrans

/-!
# The braidedness of the comparison of Tag 07A4 at a pair of K-flat complexes with flat terms

Let `f : (Sh(C), 𝒪) ⟶ (Sh(D), 𝒪')` be a morphism of ringed topoi presented by a morphism of
sites.  This file shows that the comparison of [Stacks, Tag 07A4],

`Lf^*(M ⊗^𝐋_{𝒪'} N) ≅ Lf^*M ⊗^𝐋_𝒪 Lf^*N`,

carries the commutativity constraint of the symmetric monoidal derived category of
[Stacks, Tag 0FPT] on `D(𝒪')` to the one on `D(𝒪)` **at a pair of K-flat complexes with flat
terms**, given the braidedness of the comparison of total tensor complexes of
[Stacks, Tag 03EL].

## Main definitions

* `Stacks.Sheaves.DerivedPullback.pullbackTensorModelQ` — the model of `Lf^*(QP ⊗^𝐋 QN)` on the
  target.

## Main results

* `Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso_braiding_app_of_kFlat` — the
  braidedness at a pair of K-flat complexes with flat terms, from the braidedness of the
  comparison of total tensor complexes of [Stacks, Tag 03EL].
* `Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso_hom_app_comp_canonicalComparisonHom`
  — the square of [Stacks, Tag 0FPH] at a pair of K-flat complexes with flat terms, written with
  the comparison of [Stacks, Tag 06YU].
* `Stacks.Sheaves.DerivedPullback.pullbackTensorModelQ_braiding` — the model of
  `Lf^*(QP ⊗^𝐋 QN)` carries the Koszul symmetry of complexes to the Koszul symmetry.

## References

* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 0FPH](https://stacks.math.columbia.edu/tag/0FPH)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 0G7E](https://stacks.math.columbia.edu/tag/0G7E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.Sheaves.DerivedPullback.KFlatPullback
open Stacks.SheafOfModules.DerivedMonoidal (canonicalBraidingHom canonicalBraidingHom_naturality
  canonicalComparison canonicalComparisonHom canonicalComparison_braiding complexBraidingHom
  complexBraidingHom_eq)
open scoped CategoryTheory.Prod

namespace Stacks.Sheaves.DerivedPullback

universe u

attribute [local instance] HasDerivedCategory.standard

/-! ## The comparison of Tag 06YU -/

section Comparison

variable (Z : RingedTopos.{u, u, u})
  [HasSheafify Z.J AddCommGrpCat.{u}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O) (ComplexShape.up ℤ)]

/-- On K-flat complexes, the canonical map to the ordinary total tensor complex is the comparison
`Stacks.SheafOfModules.DerivedMonoidal.canonicalComparisonHom` of [Stacks, Tag 06YU]. -/
theorem toTensor_eq_canonicalComparisonHom
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O) K)
    (hL : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O) L) :
    (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct Z.O).toTensor K L =
      canonicalComparisonHom Z.O K L hK hL :=
  (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct Z.O).toTensor_eq_comparison
    K L hK hL

/-- The comparison of Tag 06YU is an isomorphism on K-flat complexes. -/
theorem isIso_canonicalComparisonHom
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O) K)
    (hL : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O) L) :
    IsIso (canonicalComparisonHom Z.O K L hK hL) :=
  Iso.isIso_hom (canonicalComparison Z.O K L hK hL)

/-- The commutativity constraint of the derived category at complexes is induced by the flip
isomorphism of total tensor complexes. -/
private theorem complexBraidingHom_eq_map_tensorComplexFlipIso
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ) :
    complexBraidingHom Z.O K L =
      DerivedCategory.Q.map (Stacks.SheafOfModules.Tensor.tensorComplexFlipIso Z.O K L).hom := by
  rw [complexBraidingHom_eq]
  exact congrArg DerivedCategory.Q.map
    (Stacks.SheafOfModules.Tensor.koszulBraiding_eq_tensorComplexFlipIso Z.O K L)

end Comparison

/-! ## The braidedness at a pair of K-flat complexes with flat terms -/

section Square

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
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
  (f : RingedToposSiteHom X Y)
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ))]

/-- **The model of `Lf^*(QP ⊗^𝐋 QN)` on the target**: the comparison of Tag 06YY at the total
tensor complex, followed by the comparison of total tensor complexes of [Stacks, Tag 03EL]. -/
def pullbackTensorModelQ (hmos : f.u.IsMorphismOfSites Y.J X.J)
    (P N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    (derivedPullback f).obj
        (DerivedCategory.Q.obj
          (((Stacks.SheafOfModules.Tensor.tensorComplex Y.O).obj P).obj N)) ⟶
      DerivedCategory.Q.obj
        (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj
          ((pullbackComplex f).obj P)).obj ((pullbackComplex f).obj N)) :=
  pullbackComparisonQ f (((Stacks.SheafOfModules.Tensor.tensorComplex Y.O).obj P).obj N) ≫
    DerivedCategory.Q.map (pullbackTensorComplexIso f hmos P N).hom

/-- **The model identification of the comparison of Tag 07A4**: the square of
[Stacks, Tag 0FPH] at a pair of K-flat complexes with flat terms, with both canonical maps to the
ordinary total tensor complex written as the comparison of [Stacks, Tag 06YU]. -/
theorem derivedPullbackTensorIso_hom_app_comp_canonicalComparisonHom
    (hmos : f.u.IsMorphismOfSites Y.J X.J)
    (P N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hP : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) P)
    (hN : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) N)
    (hflatP : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (P.X i))
    (hflatN : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (N.X i)) :
    (derivedPullbackTensorIso f hmos).hom.app
          (DerivedCategory.Q.obj P, DerivedCategory.Q.obj N) ≫
        (Functor.uncurry.obj
              (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O)).map
            (pullbackComparisonQ f P ×ₘ pullbackComparisonQ f N) ≫
          canonicalComparisonHom X.O ((pullbackComplex f).obj P) ((pullbackComplex f).obj N)
            (kFlat_pullbackComplex' f hmos P hP hflatP)
            (kFlat_pullbackComplex' f hmos N hN hflatN) =
      (derivedPullback f).map (canonicalComparisonHom Y.O P N hP hN) ≫
        pullbackTensorModelQ f hmos P N := by
  rw [← toTensor_eq_canonicalComparisonHom X ((pullbackComplex f).obj P)
      ((pullbackComplex f).obj N) (kFlat_pullbackComplex' f hmos P hP hflatP)
      (kFlat_pullbackComplex' f hmos N hN hflatN),
    ← toTensor_eq_canonicalComparisonHom Y P N hP hN]
  exact (toTensor_square_of_kFlat f hmos P N hP hN hflatP hflatN).symm

/-- **The model of `Lf^*(QP ⊗^𝐋 QN)` carries the Koszul symmetry of complexes to the Koszul
symmetry of complexes**, given the braidedness `hcx` of the comparison of total tensor
complexes of [Stacks, Tag 03EL]. -/
theorem pullbackTensorModelQ_braiding (hmos : f.u.IsMorphismOfSites Y.J X.J)
    (hcx : ∀ A B : CochainComplex
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ,
      (pullbackComplex f).map (Stacks.SheafOfModules.Tensor.tensorComplexFlipIso Y.O A B).hom ≫
          (pullbackToposTensorTotalIso f hmos B A).hom =
        (pullbackToposTensorTotalIso f hmos A B).hom ≫
          (Stacks.SheafOfModules.Tensor.tensorComplexFlipIso X.O
            ((pullbackComplex f).obj A) ((pullbackComplex f).obj B)).hom)
    (P N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    pullbackTensorModelQ f hmos P N ≫
        complexBraidingHom X.O ((pullbackComplex f).obj P) ((pullbackComplex f).obj N) =
      (derivedPullback f).map (complexBraidingHom Y.O P N) ≫
        pullbackTensorModelQ f hmos N P := by
  have hQ : DerivedCategory.Q.map (pullbackTensorComplexIso f hmos P N).hom ≫
        DerivedCategory.Q.map
          (Stacks.SheafOfModules.Tensor.tensorComplexFlipIso X.O ((pullbackComplex f).obj P)
            ((pullbackComplex f).obj N)).hom =
      DerivedCategory.Q.map ((pullbackComplex f).map
          (Stacks.SheafOfModules.Tensor.tensorComplexFlipIso Y.O P N).hom) ≫
        DerivedCategory.Q.map (pullbackTensorComplexIso f hmos N P).hom :=
    (DerivedCategory.Q.map_comp _ _).symm.trans
      ((congrArg DerivedCategory.Q.map (hcx P N).symm).trans
        (DerivedCategory.Q.map_comp _ _))
  have hnat := pullbackComparisonQ_naturality f
    (Stacks.SheafOfModules.Tensor.tensorComplexFlipIso Y.O P N).hom
  rw [complexBraidingHom_eq_map_tensorComplexFlipIso,
    complexBraidingHom_eq_map_tensorComplexFlipIso]
  dsimp only [pullbackTensorModelQ]
  exact (comp_naturality hnat hQ.symm).symm

/-- **The comparison of [Stacks, Tag 07A4] carries the commutativity constraint of
[Stacks, Tag 0FPT] on `D(𝒪')` to the one on `D(𝒪)`, at a pair of K-flat complexes with flat
terms**, given the braidedness `hcx` of the comparison of total tensor complexes of
[Stacks, Tag 03EL]. -/
theorem derivedPullbackTensorIso_braiding_app_of_kFlat (hmos : f.u.IsMorphismOfSites Y.J X.J)
    (P N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hP : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) P)
    (hN : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) N)
    (hflatP : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (P.X i))
    (hflatN : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (N.X i))
    (hcx : ∀ A B : CochainComplex
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ,
      (pullbackComplex f).map (Stacks.SheafOfModules.Tensor.tensorComplexFlipIso Y.O A B).hom ≫
          (pullbackToposTensorTotalIso f hmos B A).hom =
        (pullbackToposTensorTotalIso f hmos A B).hom ≫
          (Stacks.SheafOfModules.Tensor.tensorComplexFlipIso X.O
            ((pullbackComplex f).obj A) ((pullbackComplex f).obj B)).hom) :
    (derivedPullback f).map
          (Stacks.SheafOfModules.DerivedMonoidal.canonicalBraidingHom Y.O
            (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj N)) ≫
        (derivedPullbackTensorIso f hmos).hom.app
          (DerivedCategory.Q.obj N, DerivedCategory.Q.obj P) =
      (derivedPullbackTensorIso f hmos).hom.app
          (DerivedCategory.Q.obj P, DerivedCategory.Q.obj N) ≫
        Stacks.SheafOfModules.DerivedMonoidal.canonicalBraidingHom X.O
          ((derivedPullback f).obj (DerivedCategory.Q.obj P))
          ((derivedPullback f).obj (DerivedCategory.Q.obj N)) := by
  have hfP := kFlat_pullbackComplex' f hmos P hP hflatP
  have hfN := kFlat_pullbackComplex' f hmos N hN hflatN
  have hiQ : ∀ (M : CochainComplex
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
      (hM : CochainComplex.KFlatBifunctor.KFlat
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) M)
      (hflatM : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (M.X i)),
      IsIso (pullbackComparisonQ f M) := fun M hM hflatM =>
    flatPullbackIso_hom_eq_pullbackComparisonQ f hmos M hM hflatM ▸ inferInstance
  have hpair : IsIso (pullbackComparisonQ f N ×ₘ pullbackComparisonQ f P) :=
    (isIso_prod_iff _ _).2 ⟨hiQ N hN hflatN, hiQ P hP hflatP⟩
  have hc := isIso_canonicalComparisonHom X ((pullbackComplex f).obj N)
    ((pullbackComplex f).obj P) hfN hfP
  have hiso : IsIso ((Functor.uncurry.obj
        (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O)).map
      (pullbackComparisonQ f N ×ₘ pullbackComparisonQ f P) ≫
    canonicalComparisonHom X.O ((pullbackComplex f).obj N)
      ((pullbackComplex f).obj P) hfN hfP) :=
    IsIso.comp_isIso' (@Functor.map_isIso _ _ _ _ _ _ _ _ hpair) hc
  exact bifunctor_comparison_braiding_of_models
    (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.O))
    (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O))
    (derivedPullbackTensorIso f hmos).hom
    (canonicalBraidingHom Y.O (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj N))
    (canonicalBraidingHom X.O (DerivedCategory.Q.obj ((pullbackComplex f).obj P))
      (DerivedCategory.Q.obj ((pullbackComplex f).obj N)))
    (canonicalBraidingHom X.O ((derivedPullback f).obj (DerivedCategory.Q.obj P))
      ((derivedPullback f).obj (DerivedCategory.Q.obj N)))
    (@IsIso.mono_of_iso _ _ _ _ _ hiso)
    (canonicalComparison_braiding Y.O P N hP hN)
    (canonicalComparison_braiding X.O ((pullbackComplex f).obj P)
      ((pullbackComplex f).obj N) hfP hfN)
    (canonicalBraidingHom_naturality X.O (pullbackComparisonQ f P) (pullbackComparisonQ f N))
    (derivedPullbackTensorIso_hom_app_comp_canonicalComparisonHom f hmos P N hP hN hflatP hflatN)
    (derivedPullbackTensorIso_hom_app_comp_canonicalComparisonHom f hmos N P hN hP hflatN hflatP)
    (pullbackTensorModelQ_braiding f hmos hcx P N)

end Square

end Stacks.Sheaves.DerivedPullback

end
