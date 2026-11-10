module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorBraidingUnconditional
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorComparisonOfToposHom

/-! # The comparison of Tag 07A4 is braided, for a morphism of ringed topoi

Let `f : (Sh(C), 𝒪) ⟶ (Sh(D), 𝒪')` be a morphism of ringed topoi in the sense of
[Stacks, Tag 01D3], part (2): a morphism of the underlying *topoi* together with the structure
map, with no functor between the underlying sites asked for
(`AlgebraicGeometry.RingedToposHom`). This file proves that the comparison

`Lf^*(M ⊗^L_{𝒪'} N) ≅ Lf^*M ⊗^L_𝒪 Lf^*N`

of [Stacks, Tag 07A4] (`Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso`)
carries the commutativity constraint `ψ` of [Stacks, Tag 0FPT] on `D(𝒪')` to the one on `D(𝒪)`,
for all `M, N` in `D(𝒪')`. In other words `Lf^*` is a *braided* functor for the derived tensor
product, and not merely a functor carrying a comparison. This is the input
[Stacks, Tag 0FPM] needs.

## Main results

* `Stacks.Sheaves.DerivedPullback.OfToposHom.pullbackTensorTotalIso_braiding`: the comparison
  `f^*Tot(K ⊗ L) ≅ Tot(f^*K ⊗ f^*L)` of total tensor complexes of [Stacks, Tag 03EL] is braided
  for the Koszul symmetry of [Stacks, Tag 06YM].
* `Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso_hom_app_model`: the value
  of the comparison of Tag 07A4 at a pair of K-flat complexes with flat terms is the five-step
  composite it was descended from.
* `Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso_braiding_app_of_kFlat`:
  the braidedness at a pair of K-flat complexes with flat terms.
* `Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso_braiding`: the
  braidedness at arbitrary `M, N` in `D(𝒪')`, with no hypothesis.

## Implementation notes

*The same three layers as the site-presented proof, with nothing transported.* The proof for a
morphism presented by a morphism of sites,
`Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso_braiding`, has three layers: modules,
complexes and the derived category. Its module layer transports the braided clause of Tag 03EL
along a comparison of two pullbacks. Here there is nothing to transport, because the comparison of
Tag 07A4 for a morphism of ringed topoi is built directly from the pullback of
[Stacks, Tag 03D6] part (2) (`Stacks.Sheaves.DerivedPullback.pullbackTensorTotalIso` at
`f.toModulesHom`):

* **Modules.** `Stacks.SheafOfModules.RingedToposPullback.braiding` is already stated for the
  four-field morphism `f.toModulesHom`. It is used here as it stands, read at the
  `Stacks.SheafOfModules.Tensor.sheafTensorBraiding` spelling of the symmetry.
* **Complexes.** `pullbackTensorTotalIso_braiding` is checked one bidegree at a time. The
  checking uses `Stacks.Sheaves.DerivedPullback.hom_ext_pullbackTotal` and the two summandwise
  formulas `Stacks.Sheaves.DerivedPullback.ι_pullbackTensorTotalIso_hom` and
  `Stacks.SheafOfModules.Tensor.ι_tensorComplexFlipIso_hom`. Both formulas carry the Koszul sign
  `(-1)^{pq}`.
* **The derived category.** At a pair of K-flat complexes with flat terms the chase is
  `CategoryTheory.bifunctor_comparison_braiding_of_models`, with the models given by the K-flat
  comparison of [Stacks, Tag 06YU] on both sides. The descent to arbitrary objects is
  `Stacks.Sheaves.DerivedPullback.natTrans_ext_of_flatKFlat` ([Stacks, Tag 06YS]), which does not
  mention `f`.

*What is reused.* None of the following is restated:

* the comparison of Tag 07A4 and its model pieces, from the module
  `DerivedPullbackTensorComparisonOfToposHom`;
* the computation of Tag 06YY, `flatPullbackIso`, which plays the role the site-presented
  development gives to `pullbackComparisonQ`;
* the braiding clause of Tag 0FPT,
  `Stacks.SheafOfModules.DerivedMonoidal.canonicalComparison_braiding`;
* the bridge between the two spellings of the Koszul symmetry,
  `Stacks.SheafOfModules.Tensor.koszulBraiding_eq_tensorComplexFlipIso`;
* the diagram bookkeeping of the module `DerivedPullbackTensorTotalSquare`.

The only declarations this file adds are the ones that mention a morphism of ringed topoi.

*Instances.* As in the file that builds the comparison, the left-derived-functor instance comes
from `Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy`,
which holds for every morphism of ringed topoi. It is installed locally and is not an argument.

## References

* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 0FPM](https://stacks.math.columbia.edu/tag/0FPM)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 06YM](https://stacks.math.columbia.edu/tag/06YM)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom (pullbackComplex)
open Stacks.Sheaves.DerivedPullback (flatKFlatModelPairsIso flatKFlatModelPairsQ
  transportedIso_hom_comp trans_symm_hom_comp natTrans_ext_of_flatKFlat comp_naturality
  toTensor_eq_canonicalComparisonHom isIso_canonicalComparisonHom)
open Stacks.SheafOfModules.Tensor (sheafTensor sheafTensorBraiding)
open Stacks.SheafOfModules.DerivedMonoidal (canonicalBraidingHom canonicalBraidingHom_naturality
  canonicalBraidingNatTrans canonicalComparisonHom canonicalComparison_braiding
  complexBraidingHom complexBraidingHom_eq DerivedModules)
open scoped CategoryTheory.Prod

attribute [local instance] Stacks.SheafOfModules.Strict.monoidalUnderlyingRingSheaf
  Stacks.SheafOfModules.Strict.braidedUnderlyingRingSheaf

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
  [(sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [(sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)]
  (f : AlgebraicGeometry.RingedToposHom X Y)

/-! ## Complexes -/

section Complexes

omit [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)]
  [(sheafTensor.{u, u, u, u, u} X.O).Additive] [(sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ M, ((sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)] in
/-- **The braided clause of [Stacks, Tag 03EL] for the pullback of a morphism of ringed topoi,
at the `sheafTensorBraiding` spelling of the symmetry.** This is
`Stacks.SheafOfModules.RingedToposPullback.braiding` at `f.toModulesHom`, with the braiding of
the strict monoidal structure identified with the symmetry of the tensor product sheaf at both
ends by `Stacks.SheafOfModules.braiding_eq_tensorSheafBraiding`. -/
theorem pullbackTensorIso_hom_app_braiding
    (A B : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    f.toModulesHom.pullbackModules.map (((sheafTensorBraiding Y.O).hom.app A).app B) ≫
        (Stacks.SheafOfModules.pullbackTensorIso f.toModulesHom).hom.app (B, A) =
      (Stacks.SheafOfModules.pullbackTensorIso f.toModulesHom).hom.app (A, B) ≫
        ((sheafTensorBraiding X.O).hom.app (f.toModulesHom.pullbackModules.obj A)).app
          (f.toModulesHom.pullbackModules.obj B) := by
  refine Eq.trans (congrArg (fun z ↦ f.toModulesHom.pullbackModules.map z ≫
      (Stacks.SheafOfModules.pullbackTensorIso f.toModulesHom).hom.app (B, A))
    (congrArg Iso.hom (Stacks.SheafOfModules.braiding_eq_tensorSheafBraiding Y.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property A B)).symm) ?_
  refine Eq.trans (Stacks.SheafOfModules.RingedToposPullback.braiding f.toModulesHom A B) ?_
  exact congrArg ((Stacks.SheafOfModules.pullbackTensorIso f.toModulesHom).hom.app (A, B) ≫ ·)
    (congrArg Iso.hom (Stacks.SheafOfModules.braiding_eq_tensorSheafBraiding X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property (f.toModulesHom.pullbackModules.obj A)
      (f.toModulesHom.pullbackModules.obj B)))

omit [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)] in
/-- **The comparison of total tensor complexes of [Stacks, Tag 03EL] is braided for the Koszul
symmetry of [Stacks, Tag 06YM]**, for a morphism of ringed topoi and arbitrary unbounded
cochain complexes `K`, `L`. In each bidegree `(p, q)` both sides carry the sign `(-1)^{pq}`. Once
the sign is cancelled, what is left is the braided clause of Tag 03EL at `(K^p, L^q)`. -/
theorem pullbackTensorTotalIso_braiding
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    (pullbackComplex f).map (Stacks.SheafOfModules.Tensor.tensorComplexFlipIso Y.O K L).hom ≫
        (pullbackTensorTotalIso f.toModulesHom L K).hom =
      (pullbackTensorTotalIso f.toModulesHom K L).hom ≫
        (Stacks.SheafOfModules.Tensor.tensorComplexFlipIso X.O
          ((pullbackComplex f).obj K) ((pullbackComplex f).obj L)).hom := by
  refine HomologicalComplex.hom_ext _ _ (fun n => ?_)
  refine hom_ext_pullbackTotal f.toModulesHom K L n (fun p q hpq => ?_)
  have hqp : q + p = n := by omega
  have hFirst :
      f.toModulesHom.pullbackModules.map (HomologicalComplex.ιMapBifunctor K L
            (sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ) p q n hpq) ≫
          f.toModulesHom.pullbackModules.map
            ((Stacks.SheafOfModules.Tensor.tensorComplexFlipIso Y.O K L).hom.f n) =
        ((p * q).negOnePow : ℤˣ) •
          (f.toModulesHom.pullbackModules.map
              (((sheafTensorBraiding Y.O).hom.app (K.X p)).app (L.X q)) ≫
            f.toModulesHom.pullbackModules.map (HomologicalComplex.ιMapBifunctor L K
              (sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ) q p n hqp)) :=
    (f.toModulesHom.pullbackModules.map_comp _ _).symm.trans
      ((congrArg f.toModulesHom.pullbackModules.map
          (Stacks.SheafOfModules.Tensor.ι_tensorComplexFlipIso_hom Y.O K L p q n hpq hqp)).trans
        ((f.toModulesHom.pullbackModules.map_units_smul _ _).trans
          (congrArg (fun morphism => ((p * q).negOnePow : ℤˣ) • morphism)
            (f.toModulesHom.pullbackModules.map_comp _ _))))
  exact (units_smul_comp_reassoc _ hFirst
      (ι_pullbackTensorTotalIso_hom f.toModulesHom L K q p n hqp)).trans
    ((congrArg (fun morphism => ((p * q).negOnePow : ℤˣ) •
        (morphism ≫ HomologicalComplex.ιMapBifunctor ((pullbackComplex f).obj L)
          ((pullbackComplex f).obj K) (sheafTensor.{u, u, u, u, u} X.O)
          (ComplexShape.up ℤ) q p n hqp))
        (pullbackTensorIso_hom_app_braiding f (K.X p) (L.X q))).trans
      (comp_units_smul_reassoc _ (ι_pullbackTensorTotalIso_hom f.toModulesHom K L p q n hpq)
        (Stacks.SheafOfModules.Tensor.ι_tensorComplexFlipIso_hom X.O
          ((pullbackComplex f).obj K) ((pullbackComplex f).obj L) p q n hpq hqp)).symm)

end Complexes

/-! ## The comparison at a pair of K-flat complexes with flat terms -/

section Models

variable (P N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
  (hP : CochainComplex.KFlatBifunctor.KFlat (sheafTensor.{u, u, u, u, u} Y.O) P)
  (hN : CochainComplex.KFlatBifunctor.KFlat (sheafTensor.{u, u, u, u, u} Y.O) N)
  (hflatP : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (P.X i))
  (hflatN : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (N.X i))

/-- **The comparison of [Stacks, Tag 07A4] at a pair of K-flat complexes with flat terms is the
five-step composite it was descended from.** -/
theorem derivedPullbackTensorIso_hom_app_model :
    (derivedPullbackTensorIso f).hom.app
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj N) =
      (derivedPullbackTensorModelIso f P N hP hN hflatP hflatN).hom := by
  have hmodel : ∀ PP : (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat
        (Y := Y)).FullSubcategory ×
      (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat (Y := Y)).FullSubcategory,
      (derivedPullbackTensorIso f).hom.app ((flatKFlatModelPairsQ Y).obj PP) =
        (flatKFlatModelPairsTensorIso f).hom.app PP := by
    intro PP
    have := Stacks.Sheaves.DerivedPullback.flatKFlatModelPairsQ_isLocalization Y
    have hdef : derivedPullbackTensorIso f =
        Localization.liftNatIso (flatKFlatModelPairsQ Y)
          (Stacks.Sheaves.DerivedPullback.flatKFlatModelPairsW Y) _ _ _ _
          (h₁ := ⟨Iso.refl _⟩) (h₂ := ⟨Iso.refl _⟩) (flatKFlatModelPairsTensorIso f) :=
      rfl
    rw [hdef, Localization.liftNatIso_hom, Localization.liftNatTrans_app]
    simp
  let PP : (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat
        (Y := Y)).FullSubcategory ×
      (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat (Y := Y)).FullSubcategory :=
    (⟨(HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P, ⟨hP, hflatP⟩⟩,
      ⟨(HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj N, ⟨hN, hflatN⟩⟩)
  have hnat := (derivedPullbackTensorIso f).hom.naturality (flatKFlatModelPairsIso Y PP).hom
  rw [hmodel PP] at hnat
  refine (cancel_epi ((Functor.uncurry.obj
      (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.O) ⋙
    derivedPullback f).map (flatKFlatModelPairsIso Y PP).hom)).1 (hnat.trans ?_)
  exact transportedIso_hom_comp
    ((Functor.uncurry.obj
        (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.O) ⋙
      derivedPullback f).mapIso (flatKFlatModelPairsIso Y PP))
    (((derivedPullback f).prod (derivedPullback f) ⋙
      Functor.uncurry.obj
        (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O)).mapIso
      (flatKFlatModelPairsIso Y PP))
    (derivedPullbackTensorModelIso f P N hP hN hflatP hflatN)

end Models

/-! ## The computation of Tag 06YY at an arbitrary complex, and the model square -/

section Square

/-- **The comparison `Lf^*(QK) ⟶ Q(f^*K)` of [Stacks, Tag 06YY]** for a morphism of ringed topoi,
from the derived pullback of a complex of `𝒪'`-modules to the image in `D(𝒪)` of its degreewise
pullback. It is defined for every complex, with no K-flatness proof among its arguments. On a
K-flat complex with flat terms it is the isomorphism `flatPullbackIso`
(`flatPullbackIso_hom_eq_pullbackComparisonQ`). -/
def pullbackComparisonQ
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback f).obj
        (DerivedCategory.Q.obj K) ⟶
      DerivedCategory.Q.obj ((KFlatPullbackOfToposHom.pullbackComplex f).obj K) :=
  (derivedPullback f).map ((DerivedCategory.quotientCompQhIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).inv.app K) ≫
    ((derivedPullbackComparison f).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K) ≫
      (DerivedCategory.quotientCompQhIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).hom.app
          ((pullbackComplex f).obj K))

omit [(sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)] in
/-- On a K-flat complex with flat terms the comparison is the isomorphism of Stacks 06YY. -/
lemma flatPullbackIso_hom_eq_pullbackComparisonQ
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat (sheafTensor.{u, u, u, u, u} Y.O) K)
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i)) :
    (flatPullbackIso f K hK hflat).hom = pullbackComparisonQ f K :=
  rfl

omit [(sheafTensor.{u, u, u, u, u} X.O).Additive] [(sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ M, ((sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)] in
/-- **The comparison of Stacks 06YY is natural in the complex.** -/
lemma pullbackComparisonQ_naturality
    {K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ}
    (a : K ⟶ L) :
    (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback f).map
        (DerivedCategory.Q.map a) ≫ pullbackComparisonQ f L =
      pullbackComparisonQ f K ≫
        DerivedCategory.Q.map ((KFlatPullbackOfToposHom.pullbackComplex f).map a) := by
  have h₁ : (derivedPullback f).map (DerivedCategory.Q.map a) ≫
        (derivedPullback f).map ((DerivedCategory.quotientCompQhIso
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).inv.app L) =
      (derivedPullback f).map ((DerivedCategory.quotientCompQhIso
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).inv.app K) ≫
        (derivedPullback f).map (DerivedCategory.Qh.map
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map a)) := by
    rw [← Functor.map_comp, ← Functor.map_comp,
      DerivedCategory.quotientCompQhIso_inv_naturality]
  have h₂ : (derivedPullback f).map (DerivedCategory.Qh.map
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map a)) ≫
        (derivedPullbackComparison f).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj L) =
      (derivedPullbackComparison f).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
          ((pullbackComplex f).map a)) :=
    (derivedPullbackComparison f).naturality
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map a)
  have h₃ := DerivedCategory.quotientCompQhIso_hom_naturality
    (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    ((pullbackComplex f).map a)
  exact comp_naturality h₁ (comp_naturality h₂ h₃)

/-- **The comparison `f^*Tot(K ⊗_{𝒪'} M) ≅ Tot(f^*K ⊗_𝒪 f^*M)` of [Stacks, Tag 03EL]** for a
morphism of ringed topoi, with its source and target written as values of the total tensor
complex functor. That is the spelling in which the Koszul symmetry
`Stacks.SheafOfModules.Tensor.tensorComplexFlipIso` is stated. -/
def pullbackTensorComplexIso
    (K M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    (pullbackComplex f).obj
        (((Stacks.SheafOfModules.Tensor.tensorComplex Y.O).obj K).obj M) ≅
      ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj ((pullbackComplex f).obj K)).obj
        ((pullbackComplex f).obj M) :=
  pullbackTensorTotalIso f.toModulesHom K M

/-- **The model of `Lf^*(QP ⊗^L QN)` on the target**: the comparison of Tag 06YY at the total
tensor complex, followed by the comparison of total tensor complexes of [Stacks, Tag 03EL]. -/
def pullbackTensorModelQ
    (P N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    (derivedPullback f).obj
        (DerivedCategory.Q.obj
          (((Stacks.SheafOfModules.Tensor.tensorComplex Y.O).obj P).obj N)) ⟶
      DerivedCategory.Q.obj
        (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj
          ((pullbackComplex f).obj P)).obj ((pullbackComplex f).obj N)) :=
  pullbackComparisonQ f (((Stacks.SheafOfModules.Tensor.tensorComplex Y.O).obj P).obj N) ≫
    DerivedCategory.Q.map (pullbackTensorComplexIso f P N).hom

/-- **The square of [Stacks, Tag 0FPH] at a pair of K-flat complexes with flat terms, for a
morphism of ringed topoi**, with both comparisons of Tag 06YU at the spelling the clauses of
Tag 0FPT are written at. Both paths are halves of the five-step chain of Tag 07A4. -/
theorem derivedPullbackTensorIso_hom_app_comp_canonicalComparisonHom
    (P N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hP : CochainComplex.KFlatBifunctor.KFlat (sheafTensor.{u, u, u, u, u} Y.O) P)
    (hN : CochainComplex.KFlatBifunctor.KFlat (sheafTensor.{u, u, u, u, u} Y.O) N)
    (hflatP : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (P.X i))
    (hflatN : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (N.X i)) :
    (derivedPullbackTensorIso f).hom.app
          (DerivedCategory.Q.obj P, DerivedCategory.Q.obj N) ≫
        (Functor.uncurry.obj
              (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O)).map
            (pullbackComparisonQ f P ×ₘ pullbackComparisonQ f N) ≫
          canonicalComparisonHom X.O ((pullbackComplex f).obj P) ((pullbackComplex f).obj N)
            (kFlatBifunctor_pullbackComplex f P hP hflatP)
            (kFlatBifunctor_pullbackComplex f N hN hflatN) =
      (derivedPullback f).map (canonicalComparisonHom Y.O P N hP hN) ≫
        pullbackTensorModelQ f P N := by
  rw [derivedPullbackTensorIso_hom_app_model f P N hP hN hflatP hflatN]
  have hR : (derivedPullbackTensorModelRight f P N hP hN hflatP hflatN).hom ≫
        DerivedCategory.Q.map (pullbackTensorComplexIso f P N).hom =
      (Functor.uncurry.obj
              (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O)).map
            (pullbackComparisonQ f P ×ₘ pullbackComparisonQ f N) ≫
          canonicalComparisonHom X.O ((pullbackComplex f).obj P) ((pullbackComplex f).obj N)
            (kFlatBifunctor_pullbackComplex f P hP hflatP)
            (kFlatBifunctor_pullbackComplex f N hN hflatN) :=
    transportedIso_hom_comp
      ((Functor.uncurry.obj
          (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).tensor).mapIso
        ((flatPullbackIso f P hP hflatP).prod (flatPullbackIso f N hN hflatN)))
      (DerivedCategory.Q.mapIso (pullbackTensorComplexIso f P N))
      ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).comparison
        ((pullbackComplex f).obj P) ((pullbackComplex f).obj N)
        (kFlatBifunctor_pullbackComplex f P hP hflatP)
        (kFlatBifunctor_pullbackComplex f N hN hflatN))
  have hL : (derivedPullback f).map (canonicalComparisonHom Y.O P N hP hN) ≫
        pullbackComparisonQ f
          (((Stacks.SheafOfModules.Tensor.tensorComplex Y.O).obj P).obj N) =
      (derivedPullbackTensorModelLeft f P N hP hN hflatP hflatN).hom := by
    rw [← toTensor_eq_canonicalComparisonHom Y P N hP hN,
      (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
        Y.O).toTensor_eq_comparison P N hP hN]
    rfl
  rw [← hR]
  refine (trans_symm_hom_comp (derivedPullbackTensorModelLeft f P N hP hN hflatP hflatN)
    (derivedPullbackTensorModelRight f P N hP hN hflatP hflatN)
    (DerivedCategory.Q.map (pullbackTensorComplexIso f P N).hom)).trans ?_
  rw [← hL]
  exact Category.assoc _ _ _

/-- **The braiding clause of [Stacks, Tag 0FPT] on K-flat complexes, with the Koszul symmetry
written as the flip isomorphism of total tensor complexes.** This is
`Stacks.SheafOfModules.DerivedMonoidal.canonicalComparison_braiding`, with
`Stacks.SheafOfModules.DerivedMonoidal.complexBraidingHom` rewritten by
`Stacks.SheafOfModules.Tensor.koszulBraiding_eq_tensorComplexFlipIso`. That is the spelling in
which the comparison of total tensor complexes of Tag 03EL is braided. -/
theorem canonicalComparison_braiding_flip (Z : RingedTopos.{u, u, u})
    [Z.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [HasSheafify Z.J AddCommGrpCat.{u}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [(sheafTensor.{u, u, u, u, u} Z.O).Additive]
    [∀ M, ((sheafTensor.{u, u, u, u, u} Z.O).obj M).Additive]
    [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ),
      HomologicalComplex.HasMapBifunctor A B (sheafTensor.{u, u, u, u, u} Z.O) (ComplexShape.up ℤ)]
    (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ)
    (hA : CochainComplex.KFlatBifunctor.KFlat (sheafTensor.{u, u, u, u, u} Z.O) A)
    (hB : CochainComplex.KFlatBifunctor.KFlat (sheafTensor.{u, u, u, u, u} Z.O) B) :
    canonicalBraidingHom Z.O (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj B) ≫
        canonicalComparisonHom Z.O B A hB hA =
      canonicalComparisonHom Z.O A B hA hB ≫
        DerivedCategory.Q.map (Stacks.SheafOfModules.Tensor.tensorComplexFlipIso Z.O A B).hom :=
  (canonicalComparison_braiding Z.O A B hA hB).trans
    (congrArg (canonicalComparisonHom Z.O A B hA hB ≫ ·)
      ((complexBraidingHom_eq Z.O A B).trans (congrArg DerivedCategory.Q.map
        (Stacks.SheafOfModules.Tensor.koszulBraiding_eq_tensorComplexFlipIso Z.O A B))))

/-- **The model of `Lf^*(QP ⊗^L QN)` carries the Koszul symmetry of complexes to the Koszul
symmetry of complexes.** The comparison of Tag 06YY is natural in the complex
(`pullbackComparisonQ_naturality`) and the comparison of total tensor complexes is braided
(`pullbackTensorTotalIso_braiding`). -/
theorem pullbackTensorModelQ_braiding
    (P N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    pullbackTensorModelQ f P N ≫
        DerivedCategory.Q.map (Stacks.SheafOfModules.Tensor.tensorComplexFlipIso X.O
          ((pullbackComplex f).obj P) ((pullbackComplex f).obj N)).hom =
      (derivedPullback f).map
          (DerivedCategory.Q.map (Stacks.SheafOfModules.Tensor.tensorComplexFlipIso Y.O P N).hom) ≫
        pullbackTensorModelQ f N P := by
  have hQ : DerivedCategory.Q.map (pullbackTensorComplexIso f P N).hom ≫
        DerivedCategory.Q.map
          (Stacks.SheafOfModules.Tensor.tensorComplexFlipIso X.O ((pullbackComplex f).obj P)
            ((pullbackComplex f).obj N)).hom =
      DerivedCategory.Q.map ((pullbackComplex f).map
          (Stacks.SheafOfModules.Tensor.tensorComplexFlipIso Y.O P N).hom) ≫
        DerivedCategory.Q.map (pullbackTensorComplexIso f N P).hom :=
    (DerivedCategory.Q.map_comp _ _).symm.trans
      ((congrArg DerivedCategory.Q.map (pullbackTensorTotalIso_braiding f P N).symm).trans
        (DerivedCategory.Q.map_comp _ _))
  exact (comp_naturality (pullbackComparisonQ_naturality f
    (Stacks.SheafOfModules.Tensor.tensorComplexFlipIso Y.O P N).hom) hQ.symm).symm

/-- **The comparison of [Stacks, Tag 07A4] carries the commutativity constraint of
[Stacks, Tag 0FPT] on `D(𝒪')` to the one on `D(𝒪)`, at a pair of K-flat complexes with flat
terms**, for a morphism of ringed topoi. The chase is
`CategoryTheory.bifunctor_comparison_braiding_of_models`. Its right-hand corner cancels an
isomorphism, because the computation of Tag 06YY is an isomorphism on such complexes
(`flatPullbackIso_hom_eq_pullbackComparisonQ`) and the degreewise pullbacks are again K-flat
([Stacks, Tag 0G7E]). -/
theorem derivedPullbackTensorIso_braiding_app_of_kFlat
    (P N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hP : CochainComplex.KFlatBifunctor.KFlat (sheafTensor.{u, u, u, u, u} Y.O) P)
    (hN : CochainComplex.KFlatBifunctor.KFlat (sheafTensor.{u, u, u, u, u} Y.O) N)
    (hflatP : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (P.X i))
    (hflatN : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (N.X i)) :
    (derivedPullback f).map
          (canonicalBraidingHom Y.O (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj N)) ≫
        (derivedPullbackTensorIso f).hom.app
          (DerivedCategory.Q.obj N, DerivedCategory.Q.obj P) =
      (derivedPullbackTensorIso f).hom.app
          (DerivedCategory.Q.obj P, DerivedCategory.Q.obj N) ≫
        canonicalBraidingHom X.O
          ((derivedPullback f).obj (DerivedCategory.Q.obj P))
          ((derivedPullback f).obj (DerivedCategory.Q.obj N)) := by
  have hfP := kFlatBifunctor_pullbackComplex f P hP hflatP
  have hfN := kFlatBifunctor_pullbackComplex f N hN hflatN
  have h₁ : IsIso (pullbackComparisonQ f N) := by
    rw [← flatPullbackIso_hom_eq_pullbackComparisonQ f N hN hflatN]
    exact Iso.isIso_hom _
  have h₂ : IsIso (pullbackComparisonQ f P) := by
    rw [← flatPullbackIso_hom_eq_pullbackComparisonQ f P hP hflatP]
    exact Iso.isIso_hom _
  have hpair : IsIso (pullbackComparisonQ f N ×ₘ pullbackComparisonQ f P) :=
    (isIso_prod_iff _ _).2 ⟨h₁, h₂⟩
  have hiso : IsIso ((Functor.uncurry.obj
        (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O)).map
      (pullbackComparisonQ f N ×ₘ pullbackComparisonQ f P) ≫
    canonicalComparisonHom X.O ((pullbackComplex f).obj N)
      ((pullbackComplex f).obj P) hfN hfP) :=
    IsIso.comp_isIso' (@Functor.map_isIso _ _ _ _ _ _ _ _ hpair)
      (isIso_canonicalComparisonHom X ((pullbackComplex f).obj N)
        ((pullbackComplex f).obj P) hfN hfP)
  exact bifunctor_comparison_braiding_of_models
    (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.O))
    (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O))
    (derivedPullbackTensorIso f).hom
    (canonicalBraidingHom Y.O (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj N))
    (canonicalBraidingHom X.O (DerivedCategory.Q.obj ((pullbackComplex f).obj P))
      (DerivedCategory.Q.obj ((pullbackComplex f).obj N)))
    (canonicalBraidingHom X.O ((derivedPullback f).obj (DerivedCategory.Q.obj P))
      ((derivedPullback f).obj (DerivedCategory.Q.obj N)))
    (@IsIso.mono_of_iso _ _ _ _ _ hiso)
    (canonicalComparison_braiding_flip Y P N hP hN)
    (canonicalComparison_braiding_flip X ((pullbackComplex f).obj P)
      ((pullbackComplex f).obj N) hfP hfN)
    (canonicalBraidingHom_naturality X.O (pullbackComparisonQ f P) (pullbackComparisonQ f N))
    (derivedPullbackTensorIso_hom_app_comp_canonicalComparisonHom f P N hP hN hflatP hflatN)
    (derivedPullbackTensorIso_hom_app_comp_canonicalComparisonHom f N P hN hP hflatN hflatP)
    (pullbackTensorModelQ_braiding f P N)

end Square

/-! ## Arbitrary objects of the derived category -/

section Descent

/-- **The comparison of [Stacks, Tag 07A4] carries the commutativity constraint of
[Stacks, Tag 0FPT] on `D(𝒪')` to the one on `D(𝒪)`**, for a morphism of ringed topoi
`f : (Sh(C), 𝒪) ⟶ (Sh(D), 𝒪')` and arbitrary `M, N` in `D(𝒪')`. There is no finiteness,
boundedness, flatness or quasi-coherence hypothesis, and no morphism of the underlying sites is
asked for.

Both sides are natural transformations on `D(𝒪') × D(𝒪')`. By [Stacks, Tag 06YS] the K-flat
complexes with flat terms localize to `D(𝒪')`, so agreement at their images
(`derivedPullbackTensorIso_braiding_app_of_kFlat`) is agreement everywhere. -/
theorem derivedPullbackTensorIso_braiding (M N : DerivedModules Y.O) :
    (derivedPullback f).map (canonicalBraidingHom Y.O M N) ≫
        (derivedPullbackTensorIso f).hom.app (N, M) =
      (derivedPullbackTensorIso f).hom.app (M, N) ≫
        canonicalBraidingHom X.O ((derivedPullback f).obj M) ((derivedPullback f).obj N) := by
  have hτ : Functor.whiskerRight (canonicalBraidingNatTrans Y.O) (derivedPullback f) ≫
        Functor.whiskerLeft (CategoryTheory.Prod.swap _ _) (derivedPullbackTensorIso f).hom =
      (derivedPullbackTensorIso f).hom ≫
        Functor.whiskerLeft ((derivedPullback f).prod (derivedPullback f))
          (canonicalBraidingNatTrans X.O) :=
    natTrans_ext_of_flatKFlat Y _ _ fun P N hP hN hfP hfN =>
      derivedPullbackTensorIso_braiding_app_of_kFlat f P N hP hN hfP hfN
  exact NatTrans.congr_app hτ (M, N)

end Descent

end Stacks.Sheaves.DerivedPullback.OfToposHom

end
