module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactFunctorsTriangle
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.FlatSingleTensor

/-!
# The identification `M[0] ⊗^L_R - ≅ (M ⊗_R -)^L` is natural in the flat module

`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.flatSingleTensorIso` identifies, for a flat
sheaf of `R`-modules `M`, the derived tensor product with `M` placed in degree zero with the
derived functor of the ordinary tensor product `M ⊗_R -`. That identification is natural in `M`:
for a map `ψ : M ⟶ N` of flat modules it carries tensoring with `ψ[0]` to the derived functor of
the sheaf-level transformation `ψ ⊗_R -`.

Both sides are natural transformations between functors on the derived category, so they agree
as soon as they agree on the image of a cochain complex, which is
`CategoryTheory.Localization.natTrans_ext`. There the left K-flat comparison of the derived
tensor product computes both sides on the total tensor complex, where the statement is the
naturality of `HomologicalComplex.singleLeftIsoMapBifunctor` in its single variable.

## Main results

* `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.flatSingleTensorIso_naturality`.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 0D9E](https://stacks.math.columbia.edu/tag/0D9E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.DerivedTensor.RingedSite.DerivedTensorProduct

open Stacks.SheafOfModules.Tensor

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
  [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (T : DerivedTensorProduct R)

attribute [local instance] Stacks.SheafOfModules.Tensor.sheafTensorAdditiveLocal
  Stacks.SheafOfModules.Tensor.sheafTensorObjAdditiveLocal

/-- A rearrangement of composites, extracted so that it is applied as a term. Given
`t ≫ c = c' ≫ u`, `u ≫ q = q' ≫ v` and `f' ≫ d = v ≫ f`, the composite `t ≫ c ≫ q ≫ f` is
`(c' ≫ q' ≫ f') ≫ d`.

It is stated abstractly because the composites it is used on carry two spellings of one object —
`Stacks.SheafOfModules.Tensor.tensorComplex` and `HomologicalComplex.mapBifunctor` — and a
rewrite builds its motive at a transparency at which those do not meet, whereas applying a lemma
is elaborated at default transparency. The same device is used in
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedTensor/OnARingedSite.lean`. -/
private theorem comp_rearrange {D : Type*} [Category D]
    {X₀ X₁ X₂ X₃ X₄ Y₁ Y₂ Y₃ : D}
    (t : X₀ ⟶ X₁) (c : X₁ ⟶ X₂) (q : X₂ ⟶ X₃) (f : X₃ ⟶ X₄)
    (c' : X₀ ⟶ Y₁) (u : Y₁ ⟶ X₂) (q' : Y₁ ⟶ Y₂) (v : Y₂ ⟶ X₃) (f' : Y₂ ⟶ Y₃) (d : Y₃ ⟶ X₄)
    (htc : t ≫ c = c' ≫ u) (huq : u ≫ q = q' ≫ v) (hfd : f' ≫ d = v ≫ f) :
    t ≫ c ≫ q ≫ f = (c' ≫ q' ≫ f') ≫ d := by
  rw [← Category.assoc t c (q ≫ f), htc, Category.assoc c' u (q ≫ f),
    ← Category.assoc u q f, huq, Category.assoc q' v f, ← hfd,
    Category.assoc c' (q' ≫ f') d, Category.assoc q' f' d]

/-- The value of the lifting datum behind `flatSingleTensorIso` on a cochain complex: the left
K-flat comparison, the identification of the total tensor complex with the degreewise tensor
product, and the factorisation of the derived functor. -/
theorem flatSingleLifting_hom_app (M : Modules R)
    (hM : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R) M)
    (L : CochainComplex (Modules R) ℤ) :
    letI := preservesFiniteLimits_sheafTensorObj R M hM
    letI := preservesFiniteColimits_sheafTensorObj R M hM
    (flatSingleLifting R T M hM).hom.app L =
      (T.comparisonLeft ((CochainComplex.singleFunctor (Modules R) 0).obj M) L
          (kFlat_single R M hM)).hom ≫
        DerivedCategory.Q.map
            (HomologicalComplex.singleLeftIsoMapBifunctor (sheafTensor R) M L).inv ≫
          ((sheafTensor R).obj M).mapDerivedCategoryFactors.inv.app L :=
  rfl

variable {M N : Modules R}
  (hM : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R) M)
  (hN : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R) N)

include hM hN

/-- **`flatSingleTensorIso` is natural in the flat module.** -/
theorem flatSingleTensorIso_naturality (ψ : M ⟶ N) :
    letI := preservesFiniteLimits_sheafTensorObj R M hM
    letI := preservesFiniteColimits_sheafTensorObj R M hM
    letI := preservesFiniteLimits_sheafTensorObj R N hN
    letI := preservesFiniteColimits_sheafTensorObj R N hN
    T.tensor.map (DerivedCategory.Q.map
          ((CochainComplex.singleFunctor (Modules R) 0).map ψ)) ≫
        (flatSingleTensorIso R T N hN).hom =
      (flatSingleTensorIso R T M hM).hom ≫
        derivedNatTrans ((sheafTensor R).obj M) ((sheafTensor R).obj N)
          ((sheafTensor R).map ψ) := by
  let := preservesFiniteLimits_sheafTensorObj R M hM
  let := preservesFiniteColimits_sheafTensorObj R M hM
  let := preservesFiniteLimits_sheafTensorObj R N hN
  let := preservesFiniteColimits_sheafTensorObj R N hN
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (Modules R) (ComplexShape.up ℤ)) fun L => ?_
  have hcomp := T.comparisonLeft_naturality
    ((CochainComplex.singleFunctor (Modules R) 0).map ψ) (𝟙 L)
    (kFlat_single R M hM) (kFlat_single R N hN)
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp] at hcomp
  have hslm := HomologicalComplex.singleLeftIsoMapBifunctor_hom_naturality_left
    (sheafTensor R) N L ψ
  have hmbm : HomologicalComplex.mapBifunctorMap
          ((CochainComplex.singleFunctor (Modules R) 0).map ψ) (𝟙 L) (sheafTensor R)
          (ComplexShape.up ℤ) ≫
        (HomologicalComplex.singleLeftIsoMapBifunctor (sheafTensor R) N L).inv =
      (HomologicalComplex.singleLeftIsoMapBifunctor (sheafTensor R) M L).inv ≫
        (NatTrans.mapHomologicalComplex ((sheafTensor R).map ψ) (ComplexShape.up ℤ)).app L := by
    refine (Iso.comp_inv_eq _).2 ?_
    rw [Category.assoc, ← hslm, Iso.inv_hom_id_assoc]
  have hdnt := derivedNatTrans_app_Q ((sheafTensor R).obj M) ((sheafTensor R).obj N)
    ((sheafTensor R).map ψ) L
  have hfac : ((sheafTensor R).obj M).mapDerivedCategoryFactors.inv.app L ≫
        (derivedNatTrans ((sheafTensor R).obj M) ((sheafTensor R).obj N)
          ((sheafTensor R).map ψ)).app (DerivedCategory.Q.obj L) =
      DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex ((sheafTensor R).map ψ)
            (ComplexShape.up ℤ)).app L) ≫
        ((sheafTensor R).obj N).mapDerivedCategoryFactors.inv.app L := by
    refine (cancel_epi (((sheafTensor R).obj M).mapDerivedCategoryFactors.hom.app L)).1 ?_
    rw [Iso.hom_inv_id_app_assoc, ← Category.assoc, ← hdnt, Category.assoc]
    simp
  have hQ : DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap
          ((CochainComplex.singleFunctor (Modules R) 0).map ψ) (𝟙 L) (sheafTensor R)
          (ComplexShape.up ℤ)) ≫
        DerivedCategory.Q.map
          (HomologicalComplex.singleLeftIsoMapBifunctor (sheafTensor R) N L).inv =
      DerivedCategory.Q.map
          (HomologicalComplex.singleLeftIsoMapBifunctor (sheafTensor R) M L).inv ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex ((sheafTensor R).map ψ)
            (ComplexShape.up ℤ)).app L) := by
    rw [← DerivedCategory.Q.map_comp, hmbm, DerivedCategory.Q.map_comp]
  rw [NatTrans.comp_app, NatTrans.comp_app, flatSingleTensorIso_hom_app_Q,
    flatSingleTensorIso_hom_app_Q, flatSingleLifting_hom_app, flatSingleLifting_hom_app]
  exact comp_rearrange _ _ _ _ _ _ _ _ _ _ hcomp hQ hfac

end Stacks.DerivedTensor.RingedSite.DerivedTensorProduct

end
