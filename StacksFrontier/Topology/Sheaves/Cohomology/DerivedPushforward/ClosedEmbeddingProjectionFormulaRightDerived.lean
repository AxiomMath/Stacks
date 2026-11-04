module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ClosedEmbeddingProjectionFormulaDerived
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ClosedEmbeddingProjectionFormulaRightComplexes
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaRight
import StacksCore.Tactic.StacksAttribute
import all StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ClosedEmbeddingProjectionFormulaDerived

/-!
# The right-handed projection formula for a closed embedding, in the derived category

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces whose underlying continuous map is
a homeomorphism onto a closed subset.  This file computes the projection-formula morphism with
the pushforward in the right factor,
`Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMapRight`,

`K ⊗^𝐋_{𝒪_Y} Rf_*E ⟶ Rf_*(Lf^*K ⊗^𝐋_{𝒪_X} E)`,

on representatives: for a K-flat complex `B^•` representing `K` and any complex `A^•`
representing `E`, it is `Q` of the complex-level isomorphism
`Stacks.Cohomology.ClosedEmbeddingProjectionFormulaComplexes.complexProjectionFormulaIsoRight`,
conjugated by the comparisons computing `Rf_*`, `Lf^*` and the two derived tensor products. In
particular it is an isomorphism there: this is [Stacks, Tag 0B55] with the two tensor factors
interchanged, on representatives.

## Main definitions

* `sourceModelIsoRight`, `targetModelIsoRight`: the source and the target of the right-handed
  projection-formula morphism, computed on representatives.
* `derivedModelIsoRight`: the right-handed projection-formula morphism on representatives, as an
  isomorphism.

## Main results

* `Stacks.Cohomology.DerivedProjectionFormula.isIso_projectionFormulaMapRight_congr`:
  invertibility of the right-handed morphism depends on its arguments only through their
  isomorphism classes.
* `projectionFormulaMapRight_eq_derivedModelIsoRight`: on a K-flat representative `B^•` of `K`
  and any representative `A^•` of `E` the morphism is `derivedModelIsoRight`.
* `isIso_projectionFormulaMapRight_Q`: the right-handed morphism is invertible at `(QB^•, QA^•)`
  for `B^•` K-flat.

## References

* [Stacks Project, Tag 0B55](https://stacks.math.columbia.edu/tag/0B55)
* [Stacks Project, Tag 0B53](https://stacks.math.columbia.edu/tag/0B53)
* [Stacks Project, Tag 06YF](https://stacks.math.columbia.edu/tag/06YF)
* [Stacks Project, Tag 06YC](https://stacks.math.columbia.edu/tag/06YC)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 0FP0](https://stacks.math.columbia.edu/tag/0FP0)
* [Stacks Project, Tag 0FP1](https://stacks.math.columbia.edu/tag/0FP1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward derivedPullback
  derivedAdjunction)
open Stacks.DerivedTensor.RingedSite (canonicalDerivedTensorProduct derivedTensorProductFunctor)
open Stacks.SheafOfModules.Tensor (sheafTensor tensorComplex)
open Stacks.Cohomology.DerivedPullbackTensor (pullbackComplex comparisonAppIso
  derivedPullbackNatTrans pullbackTensorComplexNatIso derivedPullbackTensorIso
  derivedPullbackTensorIso_toTensor_comm ι_pullbackTensorComplexIsoOfIsIso_inv
  isIso_derivedPullbackNatTrans_app)
open Stacks.SheafOfModules.KFlatPullback (kFlat_modulePullback_unconditional)
open Stacks.Cohomology.NaiveCupProductOnRingedSpaces (pushforwardComplex complexAdjunction)
open Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces (pushforwardComparisonQ
  derivedCounit_pushforwardComparisonQ)
open Stacks.Cohomology.DerivedProjectionFormula (uncurry_map_id_left uncurry_map_id_right
  projectionFormulaMapRight pullbackTensorComparisonSwap)
open scoped CategoryTheory.Prod

universe u

/-! ### Invariance under isomorphism -/

namespace Stacks.Cohomology.DerivedProjectionFormula

attribute [local instance] HasDerivedCategory.standard

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Invertibility of the right-handed projection-formula map depends on its two arguments only
through their isomorphism classes. -/
theorem isIso_projectionFormulaMapRight_congr
    {K K' : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))}
    {E E' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
    (i : K ≅ K') (e : E ≅ E') :
    IsIso (projectionFormulaMapRight f K E) ↔ IsIso (projectionFormulaMapRight f K' E') := by
  have h1 : IsIso ((Functor.uncurry.obj (derivedTensorProductFunctor Y.sheaf)).map
      (i.hom ×ₘ (derivedPushforward f).map e.hom)) :=
    ((Functor.uncurry.obj (derivedTensorProductFunctor Y.sheaf)).mapIso
      (Iso.prod i ((derivedPushforward f).mapIso e))).isIso_hom
  have h2 : IsIso ((derivedPushforward f).map
      ((Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf)).map
        ((derivedPullback f).map i.hom ×ₘ e.hom))) :=
    ((derivedPushforward f).mapIso ((Functor.uncurry.obj
      (derivedTensorProductFunctor X.sheaf)).mapIso
        (Iso.prod ((derivedPullback f).mapIso i) e))).isIso_hom
  have hnat := congrArg IsIso (projectionFormulaMapRight_natural f i.hom e.hom)
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := hnat.mpr (IsIso.comp_isIso' h h2)
    exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ (projectionFormulaMapRight f K' E') h1 this
  · have := hnat.mp (IsIso.comp_isIso' h1 h)
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ (projectionFormulaMapRight f K E) _ h2 this

end Stacks.Cohomology.DerivedProjectionFormula

namespace Stacks.Cohomology.ClosedEmbeddingProjectionFormulaComplexes

attribute [local instance] HasDerivedCategory.standard

attribute [local implicit_reducible] TopCat.Sheaf StacksDraft.KFlat.modulePullback
  StacksDraft.KFlat.modulePushforward CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-! ### Two identities on summands -/

/-- The comparison of [Stacks, Tag 01CD] on total complexes at the pair `(B^•, f_*A^•)`, on a
summand, followed by an arbitrary morphism. -/
private lemma ιTotal_comp_pullbackTensorComplexNatIso_inv_app_comp_right
    (B : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
    (A : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) ℤ)
    (p q n : ℤ) (hpq : p + q = n)
    {Z : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X}
    (g : (StacksDraft.KFlat.modulePullback f).obj
        ((((tensorComplex Y.sheaf).obj B).obj ((pushforwardComplex f).obj A)).X n) ⟶ Z) :
    HomologicalComplex₂.ιTotal
          ((((sheafTensor X.sheaf).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
            ((pullbackComplex f).obj B)).obj
            ((pullbackComplex f).obj ((pushforwardComplex f).obj A)))
          (.up ℤ) p q n hpq ≫
        ((pullbackTensorComplexNatIso f).inv.app (B, (pushforwardComplex f).obj A)).f n ≫ g =
      (comparisonAppIso f (B.X p) ((StacksDraft.KFlat.modulePushforward f).obj (A.X q))).inv ≫
        (StacksDraft.KFlat.modulePullback f).map
          (HomologicalComplex₂.ιTotal
            ((((sheafTensor Y.sheaf).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj B).obj
              ((pushforwardComplex f).obj A))
            (.up ℤ) p q n hpq) ≫ g := by
  exact (Category.assoc _ _ g).symm.trans ((congrArg (· ≫ g)
    (ι_pullbackTensorComplexIsoOfIsIso_inv f B ((pushforwardComplex f).obj A) p q n hpq)).trans
    (Category.assoc _ _ _))

/-- The counit of `f^* ⊣ f_*` in the right tensor factor, on a summand. -/
private lemma ιTotal_comp_mapBifunctorMap_id_counit
    (B : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
    (A : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) ℤ)
    (p q n : ℤ) (hpq : p + q = n) :
    HomologicalComplex₂.ιTotal
          ((((sheafTensor X.sheaf).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
            ((pullbackComplex f).obj B)).obj
            ((pullbackComplex f).obj ((pushforwardComplex f).obj A)))
          (.up ℤ) p q n hpq ≫
        (HomologicalComplex.mapBifunctorMap (𝟙 ((pullbackComplex f).obj B))
          ((complexAdjunction f).counit.app A) (sheafTensor X.sheaf) (ComplexShape.up ℤ)).f n =
      ((sheafTensor X.sheaf).obj ((StacksDraft.KFlat.modulePullback f).obj (B.X p))).map
          ((modulePullbackPushforwardAdjunction f).counit.app (A.X q)) ≫
        HomologicalComplex₂.ιTotal
          ((((sheafTensor X.sheaf).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
            ((pullbackComplex f).obj B)).obj A)
          (.up ℤ) p q n hpq := by
  have h := HomologicalComplex.ι_mapBifunctorMap (𝟙 ((pullbackComplex f).obj B))
    ((complexAdjunction f).counit.app A) (sheafTensor X.sheaf) (ComplexShape.up ℤ) p q n hpq
  rw [HomologicalComplex.id_f, CategoryTheory.Functor.map_id, NatTrans.id_app,
    Category.id_comp] at h
  exact h

/-- The right-handed complex-level mate identity: the comparison of
[Stacks, Tag 01CD] on total complexes `f^*Tot(B^• ⊗ f_*A^•) ⟶ Tot(f^*B^• ⊗ f^*f_*A^•)`, followed
by the counit in the right tensor factor, is the pullback of `complexProjectionFormulaIsoRight`
followed by the counit of `f^* ⊣ f_*` on complexes. -/
private lemma pullbackTensorComplexNatIso_hom_app_comp_mapBifunctorMap_right
    (hf : Topology.IsClosedEmbedding (ConcreteCategory.hom f.hom.base))
    (B : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
    (A : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) ℤ) :
    (pullbackTensorComplexNatIso f).hom.app (B, (pushforwardComplex f).obj A) ≫
        HomologicalComplex.mapBifunctorMap (𝟙 ((pullbackComplex f).obj B))
          ((complexAdjunction f).counit.app A) (sheafTensor X.sheaf) (ComplexShape.up ℤ) =
      (pullbackComplex f).map (complexProjectionFormulaIsoRight f hf B A).hom ≫
        (complexAdjunction f).counit.app (((tensorComplex X.sheaf).obj
          ((pullbackComplex f).obj B)).obj A) := by
  have hmate := complexProjectionFormulaIsoRight_mate f hf B A
    ((pullbackTensorComplexNatIso f).inv.app (B, (pushforwardComplex f).obj A))
    (fun p q n hpq _ g =>
      ιTotal_comp_pullbackTensorComplexNatIso_inv_app_comp_right f B A p q n hpq g)
    (HomologicalComplex.mapBifunctorMap (𝟙 ((pullbackComplex f).obj B))
      ((complexAdjunction f).counit.app A) (sheafTensor X.sheaf) (ComplexShape.up ℤ))
    (fun p q n hpq => ιTotal_comp_mapBifunctorMap_id_counit f B A p q n hpq)
  exact (congrArg ((pullbackTensorComplexNatIso f).hom.app
      (B, (pushforwardComplex f).obj A) ≫ ·) hmate.symm).trans
    (Iso.hom_inv_id_app_assoc (pullbackTensorComplexNatIso f)
      (B, (pushforwardComplex f).obj A) _)

variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-! ### The two endpoint comparisons, on representatives -/

variable (hf : Topology.IsClosedEmbedding (ConcreteCategory.hom f.hom.base))
  (B : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
  (A : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) ℤ)
  (hB : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex Y B)

include hf hB

/-- The source of the right-handed projection-formula morphism, on representatives:
`Q(Tot(B^• ⊗_{𝒪_Y} f_*A^•)) ≅ QB^• ⊗^𝐋_{𝒪_Y} Rf_*(QA^•)` for `B^•` K-flat: the K-flat comparison
of [Stacks, Tag 06YU] in the left tensor factor, then the comparison `Q(f_*A^•) ⟶ Rf_*(QA^•)` in
the right. -/
def sourceModelIsoRight :
    DerivedCategory.Q.obj (((tensorComplex Y.sheaf).obj B).obj ((pushforwardComplex f).obj A)) ≅
      (Functor.uncurry.obj (derivedTensorProductFunctor Y.sheaf)).obj
        (DerivedCategory.Q.obj B, (derivedPushforward f).obj (DerivedCategory.Q.obj A)) :=
  ((canonicalDerivedTensorProduct Y.sheaf).comparisonLeft
      B ((pushforwardComplex f).obj A) hB).symm ≪≫
    (Functor.uncurry.obj (derivedTensorProductFunctor Y.sheaf)).mapIso
      (Iso.prod (Iso.refl (DerivedCategory.Q.obj B))
        (@asIso _ _ _ _ _ (isIso_pushforwardComparisonQ f hf A)))

/-- The target of the right-handed projection-formula morphism, on representatives:
`Q(Tot(f^*B^• ⊗_{𝒪_X} A^•)) ≅ Lf^*(QB^•) ⊗^𝐋_{𝒪_X} QA^•` for `B^•` K-flat: the K-flat comparison
of [Stacks, Tag 06YU] in the left tensor factor — `f^*B^•` is K-flat by [Stacks, Tag 06YC] —
then the inverse of the comparison `Lf^*(QB^•) ⟶ Q(f^*B^•)`. -/
def targetModelIsoRight :
    DerivedCategory.Q.obj (((tensorComplex X.sheaf).obj ((pullbackComplex f).obj B)).obj A) ≅
      (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf)).obj
        ((derivedPullback f).obj (DerivedCategory.Q.obj B), DerivedCategory.Q.obj A) :=
  ((canonicalDerivedTensorProduct X.sheaf).comparisonLeft ((pullbackComplex f).obj B) A
      (kFlat_modulePullback_unconditional f B hB)).symm ≪≫
    (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf)).mapIso
      (Iso.prod (@asIso _ _ _ _ _ (isIso_derivedPullbackNatTrans_app f B hB)).symm
        (Iso.refl (DerivedCategory.Q.obj A)))

/-- The right-handed projection-formula morphism on representatives, as an isomorphism:
`QB^• ⊗^𝐋_{𝒪_Y} Rf_*(QA^•) ≅ Rf_*(Lf^*(QB^•) ⊗^𝐋_{𝒪_X} QA^•)` for `B^•` K-flat: the two
endpoint comparisons with `Q` of `complexProjectionFormulaIsoRight` and the comparison
`Q(f_*-) ⟶ Rf_*(Q-)` between them. -/
def derivedModelIsoRight :
    (Functor.uncurry.obj (derivedTensorProductFunctor Y.sheaf)).obj
        (DerivedCategory.Q.obj B, (derivedPushforward f).obj (DerivedCategory.Q.obj A)) ≅
      (derivedPushforward f).obj
        ((Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf)).obj
          ((derivedPullback f).obj (DerivedCategory.Q.obj B), DerivedCategory.Q.obj A)) :=
  (sourceModelIsoRight f hf B A hB).symm ≪≫
    DerivedCategory.Q.mapIso (complexProjectionFormulaIsoRight f hf B A) ≪≫
    (@asIso _ _ _ _ _ (isIso_pushforwardComparisonQ f hf
      (((tensorComplex X.sheaf).obj ((pullbackComplex f).obj B)).obj A))) ≪≫
    (derivedPushforward f).mapIso (targetModelIsoRight f B A hB)

/-! ### Identities between the comparisons -/

omit hf hB in
/-- [Stacks, Tag 0FP0] at the pair `(B^•, f_*A^•)`, in the `toTensor` presentation. -/
private theorem derivedPullbackTensorIso_toTensor_comm_toTensor_right :
    (derivedPullbackTensorIso f).hom.app
          (DerivedCategory.Q.obj B, DerivedCategory.Q.obj ((pushforwardComplex f).obj A)) ≫
        (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf)).map
            ((derivedPullbackNatTrans f).app B ×ₘ
              (derivedPullbackNatTrans f).app ((pushforwardComplex f).obj A)) ≫
          (canonicalDerivedTensorProduct X.sheaf).toTensor
            ((pullbackComplex f).obj B)
            ((pullbackComplex f).obj ((pushforwardComplex f).obj A)) =
      (derivedPullback f).map
          ((canonicalDerivedTensorProduct Y.sheaf).toTensor B ((pushforwardComplex f).obj A)) ≫
        (derivedPullbackNatTrans f).app
            (((tensorComplex Y.sheaf).obj B).obj ((pushforwardComplex f).obj A)) ≫
          DerivedCategory.Q.map
            ((pullbackTensorComplexNatIso f).hom.app (B, (pushforwardComplex f).obj A)) :=
  derivedPullbackTensorIso_toTensor_comm f B ((pushforwardComplex f).obj A)

/-- The inverse of `sourceModelIsoRight` followed by the two comparisons it is built from is the
identity. -/
private theorem sourceModelIsoRight_inv_comp_comparisonLeft_inv_comp :
    (sourceModelIsoRight f hf B A hB).inv ≫
        ((canonicalDerivedTensorProduct Y.sheaf).comparisonLeft
            B ((pushforwardComplex f).obj A) hB).inv ≫
          (Functor.uncurry.obj (derivedTensorProductFunctor Y.sheaf)).map
            (𝟙 (DerivedCategory.Q.obj B) ×ₘ pushforwardComparisonQ f A) =
      𝟙 ((Functor.uncurry.obj (derivedTensorProductFunctor Y.sheaf)).obj
        (DerivedCategory.Q.obj B, (derivedPushforward f).obj (DerivedCategory.Q.obj A))) :=
  (sourceModelIsoRight f hf B A hB).inv_hom_id

omit [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}] hf in
/-- The K-flat comparison of [Stacks, Tag 06YU] in the left factor inverts the canonical map to
the ordinary total tensor complex, on the pair `(B^•, f_*A^•)`. -/
private theorem comparisonLeft_inv_comp_toTensor :
    ((canonicalDerivedTensorProduct Y.sheaf).comparisonLeft
          B ((pushforwardComplex f).obj A) hB).inv ≫
        (canonicalDerivedTensorProduct Y.sheaf).toTensor B ((pushforwardComplex f).obj A) =
      𝟙 (DerivedCategory.Q.obj
        (((tensorComplex Y.sheaf).obj B).obj ((pushforwardComplex f).obj A))) := by
  rw [(canonicalDerivedTensorProduct Y.sheaf).toTensor_eq_comparisonLeft
    B ((pushforwardComplex f).obj A) hB, Iso.inv_hom_id]

omit hf in
/-- The canonical map to the ordinary total tensor complex followed by `targetModelIsoRight` is
the inverse of the comparison `Lf^*(QB^•) ⟶ Q(f^*B^•)` in the left tensor factor. -/
private theorem toTensor_comp_targetModelIsoRight_hom :
    (canonicalDerivedTensorProduct X.sheaf).toTensor ((pullbackComplex f).obj B) A ≫
        (targetModelIsoRight f B A hB).hom =
      (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf)).map
        ((@asIso _ _ _ _ _ (isIso_derivedPullbackNatTrans_app f B hB)).inv ×ₘ
          𝟙 (DerivedCategory.Q.obj A)) := by
  rw [(canonicalDerivedTensorProduct X.sheaf).toTensor_eq_comparisonLeft
    ((pullbackComplex f).obj B) A (kFlat_modulePullback_unconditional f B hB)]
  exact Iso.hom_inv_id_assoc _ _

omit [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}] hf hB in
/-- The canonical map to the ordinary total tensor complex is natural in the right factor, at the
identity and the counit of `f^* ⊣ f_*` on complexes. -/
private theorem map_counit_comp_toTensor_right :
    (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf)).map
          (𝟙 (DerivedCategory.Q.obj ((pullbackComplex f).obj B)) ×ₘ
            DerivedCategory.Q.map ((complexAdjunction f).counit.app A)) ≫
        (canonicalDerivedTensorProduct X.sheaf).toTensor ((pullbackComplex f).obj B) A =
      (canonicalDerivedTensorProduct X.sheaf).toTensor
          ((pullbackComplex f).obj B) ((pullbackComplex f).obj ((pushforwardComplex f).obj A)) ≫
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap
          (𝟙 ((pullbackComplex f).obj B)) ((complexAdjunction f).counit.app A)
          (sheafTensor X.sheaf) (ComplexShape.up ℤ)) := by
  have h := (canonicalDerivedTensorProduct X.sheaf).toTensor_naturality
    (𝟙 ((pullbackComplex f).obj B)) ((complexAdjunction f).counit.app A)
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, NatTrans.id_app,
    Category.id_comp] at h
  rw [uncurry_map_id_left]
  exact h

omit [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}] hB in
/-- The right-handed complex-level mate identity, read in the derived category. -/
private theorem map_pullbackTensorComplexNatIso_hom_app_comp_map_mapBifunctorMap_right :
    DerivedCategory.Q.map
          ((pullbackTensorComplexNatIso f).hom.app (B, (pushforwardComplex f).obj A)) ≫
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap
          (𝟙 ((pullbackComplex f).obj B)) ((complexAdjunction f).counit.app A)
          (sheafTensor X.sheaf) (ComplexShape.up ℤ)) =
      DerivedCategory.Q.map
          ((pullbackComplex f).map (complexProjectionFormulaIsoRight f hf B A).hom) ≫
        DerivedCategory.Q.map ((complexAdjunction f).counit.app
          (((tensorComplex X.sheaf).obj ((pullbackComplex f).obj B)).obj A)) :=
  ((DerivedCategory.Q.map_comp _ _).symm.trans
    (congrArg DerivedCategory.Q.map
      (pullbackTensorComplexNatIso_hom_app_comp_mapBifunctorMap_right f hf B A))).trans
    (DerivedCategory.Q.map_comp _ _)

/-! ### The transposed identity -/

omit hf in
/-- The left-hand side of the transposed identity, factored as the comparison
`Lf^*(Q-) ⟶ Q(f^*-)`, followed by `Q` of the comparison of [Stacks, Tag 01CD] on total complexes,
`Q` of the counit in the right tensor factor, and `targetModelIsoRight`. -/
private theorem lhs_fac_geom_right :
    (derivedPullback f).map
          (((canonicalDerivedTensorProduct Y.sheaf).comparisonLeft
              B ((pushforwardComplex f).obj A) hB).inv ≫
            (CategoryTheory.Prod.swap _ _ ⋙
              Functor.uncurry.obj (derivedTensorProductFunctor Y.sheaf)).map
              (pushforwardComparisonQ f A ×ₘ 𝟙 (DerivedCategory.Q.obj B))) ≫
        (pullbackTensorComparisonSwap f).app
            ((derivedPushforward f).obj (DerivedCategory.Q.obj A), DerivedCategory.Q.obj B) ≫
          (CategoryTheory.Prod.swap _ _ ⋙
            Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf)).map
            ((derivedAdjunction f).counit.app (DerivedCategory.Q.obj A) ×ₘ
              𝟙 ((derivedPullback f).obj (DerivedCategory.Q.obj B))) =
      (derivedPullbackNatTrans f).app
            (((tensorComplex Y.sheaf).obj B).obj ((pushforwardComplex f).obj A)) ≫
          DerivedCategory.Q.map
              ((pullbackTensorComplexNatIso f).hom.app (B, (pushforwardComplex f).obj A)) ≫
            DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap
                (𝟙 ((pullbackComplex f).obj B)) ((complexAdjunction f).counit.app A)
                (sheafTensor X.sheaf) (ComplexShape.up ℤ)) ≫
              (targetModelIsoRight f B A hB).hom :=
  lhs_fac (derivedAdjunction f)
    (CategoryTheory.Prod.swap _ _ ⋙ Functor.uncurry.obj (derivedTensorProductFunctor Y.sheaf))
    (CategoryTheory.Prod.swap _ _ ⋙ Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf))
    (pullbackTensorComparisonSwap f)
    (H := DerivedCategory.Q.obj B)
    (pA := pushforwardComparisonQ f A)
    (cY := ((canonicalDerivedTensorProduct Y.sheaf).comparisonLeft
      B ((pushforwardComplex f).obj A) hB).inv)
    (cY' := (canonicalDerivedTensorProduct Y.sheaf).toTensor B ((pushforwardComplex f).obj A))
    (lA := (derivedPullbackNatTrans f).app ((pushforwardComplex f).obj A))
    (lB := (derivedPullbackNatTrans f).app B)
    (eA := DerivedCategory.Q.map ((complexAdjunction f).counit.app A))
    (dB := (@asIso _ _ _ _ _ (isIso_derivedPullbackNatTrans_app f B hB)).inv)
    (tX := (canonicalDerivedTensorProduct X.sheaf).toTensor
      ((pullbackComplex f).obj B) ((pullbackComplex f).obj ((pushforwardComplex f).obj A)))
    (tX' := (canonicalDerivedTensorProduct X.sheaf).toTensor ((pullbackComplex f).obj B) A)
    (m := DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap
      (𝟙 ((pullbackComplex f).obj B)) ((complexAdjunction f).counit.app A)
      (sheafTensor X.sheaf) (ComplexShape.up ℤ)))
    (v := (targetModelIsoRight f B A hB).hom)
    (lT := (derivedPullbackNatTrans f).app
      (((tensorComplex Y.sheaf).obj B).obj ((pushforwardComplex f).obj A)))
    (th := DerivedCategory.Q.map
      ((pullbackTensorComplexNatIso f).hom.app (B, (pushforwardComplex f).obj A)))
    (comparisonLeft_inv_comp_toTensor f B A hB)
    (derivedCounit_pushforwardComparisonQ f A)
    (@asIso _ _ _ _ _ (isIso_derivedPullbackNatTrans_app f B hB)).hom_inv_id
    (toTensor_comp_targetModelIsoRight_hom f B A hB)
    (map_counit_comp_toTensor_right f B A)
    (derivedPullbackTensorIso_toTensor_comm_toTensor_right f B A)

/-- The transposed form of the identity on representatives: applying `Lf^*` to
`derivedModelIsoRight` and following with the counit of `Lf^* ⊣ Rf_*` gives the comparison of
[Stacks, Tag 079U] followed by the counit in the right tensor factor, which is the equation that
characterizes the right-handed projection-formula morphism. -/
private theorem map_derivedModelRight_comp_counit :
    (derivedPullback f).map ((sourceModelIsoRight f hf B A hB).inv ≫
          DerivedCategory.Q.map (complexProjectionFormulaIsoRight f hf B A).hom ≫
          pushforwardComparisonQ f
              (((tensorComplex X.sheaf).obj ((pullbackComplex f).obj B)).obj A) ≫
            (derivedPushforward f).map (targetModelIsoRight f B A hB).hom) ≫
        (derivedAdjunction f).counit.app
          ((CategoryTheory.Prod.swap _ _ ⋙
            Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf)).obj
            (DerivedCategory.Q.obj A, (derivedPullback f).obj (DerivedCategory.Q.obj B))) =
      (pullbackTensorComparisonSwap f).app
          ((derivedPushforward f).obj (DerivedCategory.Q.obj A), DerivedCategory.Q.obj B) ≫
        (CategoryTheory.Prod.swap _ _ ⋙
          Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf)).map
          ((derivedAdjunction f).counit.app (DerivedCategory.Q.obj A) ×ₘ
            𝟙 ((derivedPullback f).obj (DerivedCategory.Q.obj B))) :=
  map_comp_counit_of_fac (derivedAdjunction f)
    (CategoryTheory.Prod.swap _ _ ⋙ Functor.uncurry.obj (derivedTensorProductFunctor Y.sheaf))
    (CategoryTheory.Prod.swap _ _ ⋙ Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf))
    (pullbackTensorComparisonSwap f)
    (H := DerivedCategory.Q.obj B)
    (pA := pushforwardComparisonQ f A)
    (σ := (sourceModelIsoRight f hf B A hB).inv)
    (cY := ((canonicalDerivedTensorProduct Y.sheaf).comparisonLeft
      B ((pushforwardComplex f).obj A) hB).inv)
    (m := DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap
      (𝟙 ((pullbackComplex f).obj B)) ((complexAdjunction f).counit.app A)
      (sheafTensor X.sheaf) (ComplexShape.up ℤ)))
    (v := (targetModelIsoRight f B A hB).hom)
    (lT := (derivedPullbackNatTrans f).app
      (((tensorComplex Y.sheaf).obj B).obj ((pushforwardComplex f).obj A)))
    (th := DerivedCategory.Q.map
      ((pullbackTensorComplexNatIso f).hom.app (B, (pushforwardComplex f).obj A)))
    (qc := DerivedCategory.Q.map (complexProjectionFormulaIsoRight f hf B A).hom)
    (pN := pushforwardComparisonQ f
      (((tensorComplex X.sheaf).obj ((pullbackComplex f).obj B)).obj A))
    (sourceModelIsoRight_inv_comp_comparisonLeft_inv_comp f hf B A hB)
    (lhs_fac_geom_right f B A hB)
    (rhs_fac (derivedAdjunction f) _ _ _ _ _ _ _ _ _
      (map_pullbackTensorComplexNatIso_hom_app_comp_map_mapBifunctorMap_right f hf B A)
      ((derivedPullbackNatTrans f).naturality (complexProjectionFormulaIsoRight f hf B A).hom)
      (derivedCounit_pushforwardComparisonQ f
        (((tensorComplex X.sheaf).obj ((pullbackComplex f).obj B)).obj A)))

/-- The right-handed projection-formula morphism on representatives is the complex-level
projection formula: for a K-flat complex `B^•` of `𝒪_Y`-modules and an arbitrary complex `A^•`
of `𝒪_X`-modules, the morphism

`QB^• ⊗^𝐋_{𝒪_Y} Rf_*(QA^•) ⟶ Rf_*(Lf^*(QB^•) ⊗^𝐋_{𝒪_X} QA^•)`

is `Q` of `complexProjectionFormulaIsoRight`, conjugated by the comparisons that compute the two
derived functors and the derived tensor products on these representatives. -/
theorem projectionFormulaMapRight_eq_derivedModelIsoRight :
    projectionFormulaMapRight f (DerivedCategory.Q.obj B) (DerivedCategory.Q.obj A) =
      (derivedModelIsoRight f hf B A hB).hom := by
  rw [Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMapRight_eq]
  exact Stacks.AlgebraicGeometry.ProjectionFormula.eq_adjunctionTensorMap_of_map_comp_counit
    (derivedAdjunction f) _ _ _ _ _ _ (map_derivedModelRight_comp_counit f hf B A hB)

/-- The right-handed form of [Stacks, Tag 0B55] on representatives: the right-handed
projection-formula morphism is invertible at `(QB^•, QA^•)` for a K-flat complex `B^•` and an
arbitrary complex `A^•`. -/
theorem isIso_projectionFormulaMapRight_Q :
    IsIso (projectionFormulaMapRight f (DerivedCategory.Q.obj B) (DerivedCategory.Q.obj A)) := by
  rw [projectionFormulaMapRight_eq_derivedModelIsoRight f hf B A hB]
  exact (derivedModelIsoRight f hf B A hB).isIso_hom

end Stacks.Cohomology.ClosedEmbeddingProjectionFormulaComplexes

end
