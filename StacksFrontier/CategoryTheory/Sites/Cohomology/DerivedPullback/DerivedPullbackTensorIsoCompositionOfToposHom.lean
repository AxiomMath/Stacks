module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackTensorComp
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorBraidingOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorComparisonOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.FlatKFlatDescent
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackToposTensorIsoCompositionModel
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackToposTensorTotalCompositionLaw
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorIsoCompositionLaw
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.TotalTensorComplexAlongAComposite

/-!
# The comparison of Tag 07A4 along a composite of morphisms of ringed topoi

Let `f : (Sh(C), 𝒪) ⟶ (Sh(D), 𝒪')` and `g : (Sh(D), 𝒪') ⟶ (Sh(E), 𝒪'')` be morphisms of ringed
topoi in the sense of [Stacks, Tag 01D3], part (2) — morphisms of the underlying topoi together
with the structure maps, `AlgebraicGeometry.RingedToposHom`, with no functor between the
underlying sites.  `Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso` is the
comparison of [Stacks, Tag 07A4]

`Lf^*(K ⊗^L_{𝒪'} L) ≅ Lf^*K ⊗^L_𝒪 Lf^*L`

and `Stacks.Cohomology.DerivedPullbackCompositionOfToposHom.derivedPullbackCompIso` is the
composition isomorphism `Lg^* ⋙ Lf^* ≅ L(g ∘ f)^*` of [Stacks, Tag 0D6D].  This file proves that
the second carries the comparison for `g ∘ f` to `Lf^*` of the comparison for `g`, followed by the
comparison for `f` and by the composition isomorphism in each tensor factor
(`derivedPullbackTensorIso_comp`): the composite of two monoidal functors is monoidal with the
composite structure, and the composition isomorphism is monoidal for it.

## Main results

* `derivedPullbackCompIso_hom_app_comp_pullbackComparisonQ`: the composition law for the
  comparison `Lf^*(QK) ⟶ Q(f^*K)` of [Stacks, Tag 06YY]
  (`Stacks.Sheaves.DerivedPullback.OfToposHom.pullbackComparisonQ`, of
  `DerivedPullbackTensorBraidingOfToposHom.lean`), against the
  degreewise composition isomorphism `pullbackComplexCompIso`.
* `pullbackTensorTotalIso_comp`: the composition law of [Stacks, Tag 03EL] for the comparison
  `f^*Tot(K ⊗ L) ≅ Tot(f^*K ⊗ f^*L)`, for arbitrary complexes.
* `toTensor_square_of_kFlat`: [Stacks, Tag 0FPH] at a pair of K-flat complexes with flat terms.
* `derivedPullbackTensorIso_comp` and `derivedPullbackTensorIso_hom_app_comp`: **the composition
  law of [Stacks, Tag 07A4]**, as an identity of natural transformations on
  `D(𝒪'') × D(𝒪'')` and at a pair of objects.

## Implementation notes

The route is the one of the site-presented development
(`PullbackToposTensorIsoCompositionDescent.lean` in the same directory): every comparison in
sight is computed at a pair of K-flat complexes with flat terms by an ordinary total tensor
complex, the identity there is an instance of the category-generic assembly
`Stacks.Cohomology.DerivedPullbackTensor.tensorComparison_comp_of_models`, and it descends to the
whole derived category along the localization of pairs of models
(`Stacks.Sheaves.DerivedPullback.natTrans_ext_of_flatKFlat`).  The generic pieces are reused; only
the statements that mention the morphisms are proved here.  Nothing is transported from the
site-presented case: a morphism of ringed topoi need not be presented by a functor of sites.

The one degreewise input is the composition law of [Stacks, Tag 03EL] for the pullback of
[Stacks, Tag 03D6] part (2), against the composition isomorphism the derived composition
isomorphism is built from; that is
`AlgebraicGeometry.RingedToposHom.pullbackTensorIso_hom_app_comp_toModulesHom`.

Both ringed topoi are at `RingedTopos.{u, u, u}`, the universes at which the derived tensor
product of [Stacks, Tag 06YU] exists; this is inherited from
`Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso`.

## References

* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 0FPH](https://stacks.math.columbia.edu/tag/0FPH)
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.DerivedPullbackCompositionOfToposHom
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction (IsKFlat)
open Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom (pullbackComplex)
open scoped CategoryTheory.Prod

namespace Stacks.Sheaves.DerivedPullback.OfToposHom

universe u

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance]
  Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy


/-! ## The composition law for the comparison of Stacks 06YY -/

section ComparisonComposite

variable {X Y Z : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [Z.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Z.J AddCommGrpCat.{u}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)] [HasSheafify Z.J (Type u)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O) (ComplexShape.up ℤ)]
  (f : AlgebraicGeometry.RingedToposHom X Y) (g : AlgebraicGeometry.RingedToposHom Y Z)

/-- **The composition isomorphism for degreewise pullback on cochain complexes**, `g^* ⋙ f^* ≅
(g ∘ f)^*`: the comparison `AlgebraicGeometry.RingedToposHom.pullbackModulesCompIso` of
Stacks 03D6, applied degreewise.  On the homotopy categories it induces
`Stacks.Cohomology.DerivedPullbackCompositionOfToposHom.pullbackMapHomotopyCompIso`. -/
def pullbackComplexCompIso :
    pullbackComplex g ⋙ pullbackComplex f ≅
      pullbackComplex (AlgebraicGeometry.RingedToposHom.comp (X := X) g f) :=
  Functor.mapHomologicalComplexCompIso
    (AlgebraicGeometry.RingedToposHom.pullbackModulesCompIso f g).symm (ComplexShape.up ℤ)

/-- The composition isomorphism on complexes, in a single degree. -/
lemma pullbackComplexCompIso_hom_app_f
    (M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ)
    (n : ℤ) :
    ((pullbackComplexCompIso f g).hom.app M).f n =
      (AlgebraicGeometry.RingedToposHom.pullbackModulesCompIso f g).symm.hom.app (M.X n) :=
  rfl

/-- **The composition law for the comparison `Lf^*(QM) ⟶ Q(f^*M)` of Stacks 06YY.**  For an
arbitrary cochain complex `M` of `𝒪''`-modules, the composition isomorphism of Stacks 0D6D
followed by the comparison for `g ∘ f` is the comparison for `g` pushed forward by `Lf^*`, then
the comparison for `f`, then the degreewise composition isomorphism.

This is the characterization
`derivedPullbackCompComparison_app_comp_derivedPullbackComparison_app`
of the comparison of Stacks 0D6D on the homotopy category, transported along the isomorphism
`CategoryTheory.DerivedCategory.quotientCompQhIso` at both ends. -/
theorem derivedPullbackCompIso_hom_app_comp_pullbackComparisonQ
    (M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ) :
    (derivedPullbackCompIso f g).hom.app (DerivedCategory.Q.obj M) ≫
        pullbackComparisonQ (AlgebraicGeometry.RingedToposHom.comp (X := X) g f) M =
      (derivedPullback f).map (pullbackComparisonQ g M) ≫
        pullbackComparisonQ f ((pullbackComplex g).obj M) ≫
          DerivedCategory.Q.map ((pullbackComplexCompIso f g).hom.app M) := by
  simp only [pullbackComparisonQ, derivedPullbackCompIso_hom]
  refine Stacks.Sheaves.DerivedPullback.CompositionLaw.comp_of_three_factors (derivedPullback f) ?_
    (derivedPullbackCompComparison_app_comp_derivedPullbackComparison_app f g
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj M)) ?_ ?_
  · exact ((derivedPullbackCompComparison f g).naturality
      ((DerivedCategory.quotientCompQhIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))).inv.app M)).symm
  · exact DerivedCategory.quotientCompQhIso_hom_naturality
      ((pullbackComplexCompIso f g).hom.app M)
  · exact Iso.hom_inv_id_app _ _

end ComparisonComposite


/-! ## Stacks 0FPH at a pair of K-flat complexes with flat terms -/

section Square

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

/-- **Stacks 0FPH at a pair of K-flat complexes with flat terms**, for a morphism of ringed topoi.
There both paths of the square are halves of the five-step chain of Stacks 07A4: the canonical
map to the ordinary total tensor complex is the two-sided K-flat comparison on the source, and
also on the target since `f^*P` and `f^*N` are again K-flat by Stacks 0G7E. -/
lemma toTensor_square_of_kFlat
    (P N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hP : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) P)
    (hN : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) N)
    (hflatP : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (P.X i))
    (hflatN : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (N.X i)) :
    (derivedPullback f).map
          ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct Y.O).toTensor P N) ≫
        pullbackComparisonQ f
            (((Stacks.SheafOfModules.Tensor.tensorComplex Y.O).obj P).obj N) ≫
        DerivedCategory.Q.map (pullbackTensorComplexIso f P N).hom =
      (derivedPullbackTensorIso f).hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj N) ≫
        bifunctorMap (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).tensor
            (pullbackComparisonQ f P) (pullbackComparisonQ f N) ≫
        (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).toTensor
          ((pullbackComplex f).obj P) ((pullbackComplex f).obj N) := by
  have hfP := kFlatBifunctor_pullbackComplex f P hP hflatP
  have hfN := kFlatBifunctor_pullbackComplex f N hN hflatN
  have hL : (derivedPullback f).map
          ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct Y.O).toTensor P N) ≫
        pullbackComparisonQ f
          (((Stacks.SheafOfModules.Tensor.tensorComplex Y.O).obj P).obj N) =
      (derivedPullbackTensorModelLeft f P N hP hN hflatP hflatN).hom := by
    rw [(Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
      Y.O).toTensor_eq_comparison P N hP hN]
    rfl
  have hR : (derivedPullbackTensorModelRight f P N hP hN hflatP hflatN).hom ≫
        DerivedCategory.Q.map (pullbackTensorComplexIso f P N).hom =
      bifunctorMap (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).tensor
          (pullbackComparisonQ f P) (pullbackComparisonQ f N) ≫
        (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).toTensor
          ((pullbackComplex f).obj P) ((pullbackComplex f).obj N) := by
    rw [(Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
      X.O).toTensor_eq_comparison _ _ hfP hfN]
    exact transportedIso_hom_comp
      ((Functor.uncurry.obj
          (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).tensor).mapIso
        ((flatPullbackIso f P hP hflatP).prod (flatPullbackIso f N hN hflatN)))
      (DerivedCategory.Q.mapIso (pullbackTensorTotalIso f.toModulesHom P N))
      ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).comparison
        ((pullbackComplex f).obj P) ((pullbackComplex f).obj N) hfP hfN)
  rw [← Category.assoc, hL,
    derivedPullbackTensorIso_hom_app_model f P N hP hN hflatP hflatN,
    derivedPullbackTensorModelIso, Iso.trans_hom, Iso.symm_hom, Category.assoc, ← hR,
    Iso.inv_hom_id_assoc]
  rfl

/-- The comparison `Lf^*(QK) ⟶ Q(f^*K)` is invertible at a K-flat complex with flat terms. -/
lemma isIso_pullbackComparisonQ_of_kFlat (f : AlgebraicGeometry.RingedToposHom X Y)
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) K)
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i)) :
    IsIso (pullbackComparisonQ f K) := by
  rw [← flatPullbackIso_hom_eq_pullbackComparisonQ f K hK hflat]
  infer_instance

/-- The derived tensor product of the two comparisons `Lf^*(QK) ⟶ Q(f^*K)` is a monomorphism at
a pair of K-flat complexes with flat terms. -/
lemma mono_derivedTensorMap_pullbackComparisonQ (f : AlgebraicGeometry.RingedToposHom X Y)
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) K)
    (hL : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) L)
    (hflatK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i))
    (hflatL : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (L.X i)) :
    Mono ((Functor.uncurry.obj
        (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O)).map
      (pullbackComparisonQ f K ×ₘ pullbackComparisonQ f L)) := by
  have hiK := isIso_pullbackComparisonQ_of_kFlat f K hK hflatK
  have hiL := isIso_pullbackComparisonQ_of_kFlat f L hL hflatL
  have hprod : IsIso (pullbackComparisonQ f K ×ₘ pullbackComparisonQ f L) := by
    rw [isIso_prod_iff]
    exact ⟨hiK, hiL⟩
  infer_instance

/-- The canonical map to the ordinary total tensor complex on the source is a monomorphism at the
degreewise pullbacks of a pair of K-flat complexes with flat terms: those are K-flat by
Stacks 0G7E, and there the canonical map is the K-flat comparison of Stacks 06YU. -/
lemma mono_toTensor_pullbackComplex (f : AlgebraicGeometry.RingedToposHom X Y)
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) K)
    (hL : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) L)
    (hflatK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i))
    (hflatL : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (L.X i)) :
    Mono ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).toTensor
      ((pullbackComplex f).obj K) ((pullbackComplex f).obj L)) := by
  rw [(Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).toTensor_eq_comparison
    _ _ (kFlatBifunctor_pullbackComplex f K hK hflatK)
    (kFlatBifunctor_pullbackComplex f L hL hflatL)]
  infer_instance

end Square

/-! ## The composition law for the comparison of total tensor complexes -/

section TotalComposite

variable {X Y Z : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [Z.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Z.J AddCommGrpCat.{u}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)] [HasSheafify Z.J (Type u)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O) (ComplexShape.up ℤ)]
  (f : AlgebraicGeometry.RingedToposHom X Y) (g : AlgebraicGeometry.RingedToposHom Y Z)

omit [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)] in
/-- The comparison of total tensor complexes on the summand of bidegree `(p, q)`, with the
module-level comparison read as a component of an isomorphism and the bidegree condition written
as the total-complex-shape condition: the spelling the summandwise reduction is stated at.
Recorded once, for variable complexes, so that the instantiation below decides nothing. -/
lemma ι_pullbackTensorTotalIso_hom' (φ : AlgebraicGeometry.RingedToposHom X Y)
    (K L : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (p q n : ℤ) (hpq : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (p, q) = n) :
    φ.toModulesHom.pullbackModules.map (HomologicalComplex.ιMapBifunctor K L
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)
          (ComplexShape.up ℤ) p q n hpq) ≫
        (pullbackTensorComplexIso φ K L).hom.f n =
      ((Stacks.SheafOfModules.pullbackTensorIso φ.toModulesHom).app (K.X p, L.X q)).hom ≫
        HomologicalComplex.ιMapBifunctor
          ((φ.toModulesHom.pullbackModules.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
          ((φ.toModulesHom.pullbackModules.mapHomologicalComplex (ComplexShape.up ℤ)).obj L)
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)
          (ComplexShape.up ℤ) p q n hpq :=
  ι_pullbackTensorTotalIso_hom φ.toModulesHom K L p q n hpq

/-- The degreewise composition isomorphism at a complex, with both sides spelled through
`CategoryTheory.Functor.mapHomologicalComplex`. -/
def pullbackComplexCompIsoApp' (M : CochainComplex
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ) :
    (f.toModulesHom.pullbackModules.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((g.toModulesHom.pullbackModules.mapHomologicalComplex (ComplexShape.up ℤ)).obj M) ⟶
      ((AlgebraicGeometry.RingedToposHom.comp (X := X) g f).toModulesHom.pullbackModules
          |>.mapHomologicalComplex (ComplexShape.up ℤ)).obj M :=
  (pullbackComplexCompIso f g).hom.app M

/-- `pullbackComplexCompIsoApp'` in a single degree. -/
lemma pullbackComplexCompIsoApp'_f (M : CochainComplex
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ) (n : ℤ) :
    (pullbackComplexCompIsoApp' f g M).f n =
      (AlgebraicGeometry.RingedToposHom.pullbackModulesCompIso f g).symm.hom.app (M.X n) :=
  rfl

/-- **The comparison of total tensor complexes of Stacks 03EL is compatible with composition of
morphisms of ringed topoi**, for arbitrary cochain complexes `P`, `N` of `𝒪''`-modules: the
comparison for `g`, then the comparison for `f`, then the degreewise composition isomorphism in
each tensor factor, is the degreewise composition isomorphism followed by the comparison for
`g ∘ f`.

The identity is checked on the summands of the total complex by the geometry-free
`Stacks.TotalTensorComplexComposite.totalComplexComparison_comp`, whose one degreewise input is
the module-level law
`AlgebraicGeometry.RingedToposHom.pullbackTensorIso_hom_app_comp_toModulesHom`. -/
theorem pullbackTensorTotalIso_comp
    (P N : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ) :
    (f.toModulesHom.pullbackModules.mapHomologicalComplex (ComplexShape.up ℤ)).map
          (pullbackTensorComplexIso g P N).hom ≫
        (pullbackTensorComplexIso f
          ((g.toModulesHom.pullbackModules.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
          ((g.toModulesHom.pullbackModules.mapHomologicalComplex (ComplexShape.up ℤ)).obj N)).hom ≫
          HomologicalComplex.mapBifunctorMap (pullbackComplexCompIsoApp' f g P)
            (pullbackComplexCompIsoApp' f g N)
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ) =
      pullbackComplexCompIsoApp' f g (HomologicalComplex.mapBifunctor P N
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O) (ComplexShape.up ℤ)) ≫
        (pullbackTensorComplexIso
          (AlgebraicGeometry.RingedToposHom.comp (X := X) g f) P N).hom :=
  totalComplexComparison_comp_family
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O)
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)
    g.toModulesHom.pullbackModules f.toModulesHom.pullbackModules
    (AlgebraicGeometry.RingedToposHom.comp (X := X) g f).toModulesHom.pullbackModules
    (AlgebraicGeometry.RingedToposHom.pullbackModulesCompIso f g).symm
    (fun a b => (Stacks.SheafOfModules.pullbackTensorIso g.toModulesHom).app (a, b))
    (fun a b => (Stacks.SheafOfModules.pullbackTensorIso f.toModulesHom).app (a, b))
    (fun a b => (Stacks.SheafOfModules.pullbackTensorIso
      (AlgebraicGeometry.RingedToposHom.comp (X := X) g f).toModulesHom).app (a, b))
    P N (AlgebraicGeometry.RingedToposHom.pullbackTensorIso_hom_app_comp_toModulesHom f g)
    (pullbackTensorComplexIso g) (pullbackTensorComplexIso f)
    (pullbackTensorComplexIso (AlgebraicGeometry.RingedToposHom.comp (X := X) g f))
    (ι_pullbackTensorTotalIso_hom' g) (ι_pullbackTensorTotalIso_hom' f)
    (ι_pullbackTensorTotalIso_hom' (AlgebraicGeometry.RingedToposHom.comp (X := X) g f))
    (pullbackComplexCompIsoApp' f g) (pullbackComplexCompIsoApp'_f f g)

/-- **The composition law of Stacks 03EL for the comparison of total tensor complexes, carried
along `CategoryTheory.DerivedCategory.Q`**, with the comparison written through
`pullbackTensorComplexIso`.  This is the shape the model-level composition law below consumes. -/
theorem map_pullbackTensorTotalIso_comp
    (P N : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ) :
    DerivedCategory.Q.map ((pullbackComplexCompIso f g).hom.app
          (((Stacks.SheafOfModules.Tensor.tensorComplex Z.O).obj P).obj N)) ≫
        DerivedCategory.Q.map (pullbackTensorComplexIso
          (AlgebraicGeometry.RingedToposHom.comp (X := X) g f) P N).hom =
      DerivedCategory.Q.map ((pullbackComplex f).map
          (pullbackTensorComplexIso g P N).hom) ≫
        DerivedCategory.Q.map (pullbackTensorComplexIso f
            ((pullbackComplex g).obj P) ((pullbackComplex g).obj N)).hom ≫
          DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap
            ((pullbackComplexCompIso f g).hom.app P)
            ((pullbackComplexCompIso f g).hom.app N)
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)
            (ComplexShape.up ℤ)) := by
  -- The law is first restated with its two sides in the spelling of the conclusion, at which
  -- point carrying it along `DerivedCategory.Q` is a matter of unification only.
  have h : (pullbackComplexCompIso f g).hom.app
          (((Stacks.SheafOfModules.Tensor.tensorComplex Z.O).obj P).obj N) ≫
        (pullbackTensorComplexIso
          (AlgebraicGeometry.RingedToposHom.comp (X := X) g f) P N).hom =
      (pullbackComplex f).map (pullbackTensorComplexIso g P N).hom ≫
        (pullbackTensorComplexIso f
            ((pullbackComplex g).obj P) ((pullbackComplex g).obj N)).hom ≫
          HomologicalComplex.mapBifunctorMap
            ((pullbackComplexCompIso f g).hom.app P)
            ((pullbackComplexCompIso f g).hom.app N)
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)
            (ComplexShape.up ℤ) :=
    (pullbackTensorTotalIso_comp f g P N).symm
  exact Stacks.Cohomology.DerivedPullbackTensor.map_comp_eq_of_comp_eq DerivedCategory.Q
    h.symm rfl

end TotalComposite

/-! ## The composition law of Stacks 07A4 -/

section Composite

variable {X Y Z : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [Z.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Z.J AddCommGrpCat.{u}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)] [HasSheafify Z.J (Type u)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O) (ComplexShape.up ℤ)]
  (f : AlgebraicGeometry.RingedToposHom X Y) (g : AlgebraicGeometry.RingedToposHom Y Z)

/-- **The comparison of Stacks 07A4 is compatible with composition, at a pair of K-flat complexes
with flat terms.**  No diagram chase is performed: every comparison in sight is computed on such a
pair by an ordinary total tensor complex (`toTensor_square_of_kFlat`, which is Stacks 0FPH at a
pair of models), so the identity is an instance of the category-generic assembly
`Stacks.Cohomology.DerivedPullbackTensor.tensorComparison_comp_of_models`. -/
theorem derivedPullbackTensorIso_comp_app_of_kFlat
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O) K)
    (hL : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O) L)
    (hflatK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Z.O) (K.X i))
    (hflatL : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Z.O) (L.X i)) :
    (derivedPullbackCompIso f g).hom.app
          ((Functor.uncurry.obj
              (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.O)).obj
            (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L)) ≫
        (derivedPullbackTensorIso (AlgebraicGeometry.RingedToposHom.comp (X := X) g f)).hom.app
            (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) =
      (derivedPullback f).map
          ((derivedPullbackTensorIso g).hom.app
            (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L)) ≫
        (derivedPullbackTensorIso f).hom.app
            ((derivedPullback g).obj (DerivedCategory.Q.obj K),
              (derivedPullback g).obj (DerivedCategory.Q.obj L)) ≫
          (Functor.uncurry.obj
              (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O)).map
            ((derivedPullbackCompIso f g).hom.app (DerivedCategory.Q.obj K) ×ₘ
              (derivedPullbackCompIso f g).hom.app (DerivedCategory.Q.obj L)) := by
  have h := Stacks.Cohomology.DerivedPullbackTensor.tensorComparison_comp_of_models
    (derivedPullbackCompIso f g).hom
    (derivedPullbackTensorIso g).hom
    (derivedPullbackTensorIso f).hom
    (derivedPullbackTensorIso (AlgebraicGeometry.RingedToposHom.comp (X := X) g f)).hom
    (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)
    (mono_derivedTensorMap_pullbackComparisonQ
      (AlgebraicGeometry.RingedToposHom.comp (X := X) g f) K L hK hL hflatK hflatL)
    (mono_toTensor_pullbackComplex
      (AlgebraicGeometry.RingedToposHom.comp (X := X) g f) K L hK hL hflatK hflatL)
    (derivedPullbackCompIso_hom_app_comp_pullbackComparisonQ f g K)
    (derivedPullbackCompIso_hom_app_comp_pullbackComparisonQ f g L)
    (derivedPullbackCompIso_hom_app_comp_pullbackComparisonQ f g
      (((Stacks.SheafOfModules.Tensor.tensorComplex Z.O).obj K).obj L))
    (pullbackComparisonQ_naturality f (pullbackTensorComplexIso g K L).hom)
    (toTensor_naturality_prod X ((pullbackComplexCompIso f g).hom.app K)
      ((pullbackComplexCompIso f g).hom.app L))
    ((toTensor_square_of_kFlat g K L hK hL hflatK hflatL).symm : _)
    ((toTensor_square_of_kFlat f ((pullbackComplex g).obj K) ((pullbackComplex g).obj L)
      (kFlatBifunctor_pullbackComplex g K hK hflatK)
      (kFlatBifunctor_pullbackComplex g L hL hflatL)
      (fun i => Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom.isFlat_pullbackComplex_X
        g K hflatK i)
      (fun i => Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom.isFlat_pullbackComplex_X
        g L hflatL i)).symm : _)
    ((toTensor_square_of_kFlat (AlgebraicGeometry.RingedToposHom.comp (X := X) g f) K L hK hL
      hflatK hflatL).symm : _)
    (map_pullbackTensorTotalIso_comp f g K L)
  exact h

/-- **[Stacks, Tag 07A4] is compatible with composition of morphisms of ringed topoi**, as an
identity of natural transformations on `D(𝒪'') × D(𝒪'')` with no hypothesis on the objects.  For
morphisms of ringed topoi `f : (Sh(C), 𝒪) ⟶ (Sh(D), 𝒪')` and `g : (Sh(D), 𝒪') ⟶ (Sh(E), 𝒪'')`,
the composition isomorphism `Lg^* ⋙ Lf^* ≅ L(g ∘ f)^*` of [Stacks, Tag 0D6D] followed by the
comparison of [Stacks, Tag 07A4] for `g ∘ f` is `Lf^*` of the comparison for `g`, followed by the
comparison for `f` and by the composition isomorphism in each tensor factor.

Both sides are transformations out of `(K, L) ↦ Lf^*Lg^*(K ⊗^L L)`, and pairs of K-flat
complexes with flat terms localize to `D(𝒪'') × D(𝒪'')`, so the identity is checked at such a
pair, which is `derivedPullbackTensorIso_comp_app_of_kFlat`. -/
theorem derivedPullbackTensorIso_comp :
    Functor.whiskerLeft
          (Functor.uncurry.obj
            (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.O))
          (derivedPullbackCompIso f g).hom ≫
        (derivedPullbackTensorIso (AlgebraicGeometry.RingedToposHom.comp (X := X) g f)).hom =
      Functor.whiskerRight (derivedPullbackTensorIso g).hom (derivedPullback f) ≫
        Functor.whiskerLeft ((derivedPullback g).prod (derivedPullback g))
            (derivedPullbackTensorIso f).hom ≫
          Functor.whiskerRight
            (NatTrans.prod (derivedPullbackCompIso f g).hom (derivedPullbackCompIso f g).hom)
            (Functor.uncurry.obj
              (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O)) :=
  natTrans_ext_of_flatKFlat Z _ _ fun K L hK hL hflatK hflatL =>
    derivedPullbackTensorIso_comp_app_of_kFlat f g K L hK hL hflatK hflatL

/-- **[Stacks, Tag 07A4] is compatible with composition of morphisms of ringed topoi, at a pair of
objects of `D(𝒪'')`**: `derivedPullbackTensorIso_comp` read at `(P, Q)`. -/
theorem derivedPullbackTensorIso_hom_app_comp
    (P Q : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))) :
    (derivedPullbackCompIso f g).hom.app
          ((Functor.uncurry.obj
              (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.O)).obj (P, Q)) ≫
        (derivedPullbackTensorIso (AlgebraicGeometry.RingedToposHom.comp (X := X) g f)).hom.app
          (P, Q) =
      (derivedPullback f).map ((derivedPullbackTensorIso g).hom.app (P, Q)) ≫
        (derivedPullbackTensorIso f).hom.app
            ((derivedPullback g).obj P, (derivedPullback g).obj Q) ≫
          (Functor.uncurry.obj
              (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O)).map
            ((derivedPullbackCompIso f g).hom.app P ×ₘ
              (derivedPullbackCompIso f g).hom.app Q) :=
  NatTrans.congr_app (derivedPullbackTensorIso_comp f g) (P, Q)

end Composite

end Stacks.Sheaves.DerivedPullback.OfToposHom

end
