module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.ShortExact
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.PointResolution.ModuleBicomplex
public import StacksFrontier.Cotangent.ChartSiteStandardResolutionNaturality

/-!
# `(Ω_{𝒪/Λ̲} ⊗_𝒪 𝒪̲_X)(A_{•,U}) = L_{𝒪_X(U)/Λ}` as complexes of presheaves

Let `Λ` be a ring, `X` a scheme over `Λ`, and for an open `U ⊆ X` let `P_{•,U}` be the standard
resolution of `𝒪_X(U)` over `Λ` and `A_{•,U} = Spec(P_{•,U})` the cosimplicial polynomial charts of
Tag 08VB. The proof of Tag 08T9 computes the complex of presheaves
`U ↦ (Ω_{𝒪/Λ̲} ⊗_𝒪 𝒪̲_X)(A_{•,U})` as
`U ↦ Ω_{P_{•,U}/Λ} ⊗_{P_{•,U}} 𝒪_X(U) = L_{𝒪_X(U)/Λ}`, functorially in `U`. This file proves that
computation: the Moore complex of the evaluation of the presheaf
`(U ⟶ A) ↦ 𝒪_X(U) ⊗_{Γ(A)} Ω_{Γ(A)/Λ}` of the chart site on the charts `A_{•,U}`, placed in
non-positive cohomological degrees, is isomorphic to the complex of presheaves
`U ↦ L_{𝒪_X(U)/Λ}`, both read as complexes of presheaves of modules over the lifted structure
sheaf of `X`.

## Main results

* `AlgebraicGeometry.PolynomialChart.chartBaseChangePresheafMooreCochainIso`: the isomorphism of
  complexes of presheaves of the proof of Tag 08T9.

## References

* [Stacks Project, Tag 08T9](https://stacks.math.columbia.edu/tag/08T9)
* [Stacks Project, Tag 08VB](https://stacks.math.columbia.edu/tag/08VB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open scoped ChangeOfRings TensorProduct
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Sites.FibredCategory.FibredCategorySituation

universe u

namespace AlgebraicGeometry.PolynomialChart

variable (Λ : Type u) [CommRing Λ] (X : Scheme.{u})
  (structureMap : X ⟶ Spec (CommRingCat.of Λ))

/-- `cotangentToChart` carries the alternating sum of the faces of the cotangent simplicial module
to the differential of the complex `U ↦ (Ω_{𝒪/Λ̲} ⊗_𝒪 𝒪̲_X)(A_{•,U})`. -/
theorem cotangentToChart_objD (U : X.Opens) (n : ℕ)
    (z : CommAlgCat.cotangentTerm.{u, u} Λ (sectionCotangentAlgebra Λ X structureMap U)
      (op ⦋n + 1⦌)) :
    cotangentToChart Λ X structureMap U ⦋n⦌
        (AlgebraicTopology.AlternatingFaceMapComplex.objD
          (CommAlgCat.cotangentSimplicialModule.{u, u} Λ
            (sectionCotangentAlgebra Λ X structureMap U)).object n z) =
      ((chartBaseChangeMooreComplex Λ X structureMap).d (n + 1) n).app (op U)
        (cotangentToChart Λ X structureMap U ⦋n + 1⦌ z) := by
  have hd := AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq
    (chartBaseChangeSimplicial Λ X structureMap) n
  let evT : ((CommAlgCat.cotangentSimplicialModule.{u, u} Λ
      (sectionCotangentAlgebra Λ X structureMap U)).object.obj (op ⦋n + 1⦌) ⟶
        (CommAlgCat.cotangentSimplicialModule.{u, u} Λ
          (sectionCotangentAlgebra Λ X structureMap U)).object.obj (op ⦋n⦌)) →+
      CommAlgCat.cotangentTerm.{u, u} Λ (sectionCotangentAlgebra Λ X structureMap U) (op ⦋n⦌) :=
    { toFun f := f z
      map_zero' := rfl
      map_add' _ _ := rfl }
  let evS : ((chartBaseChangeSimplicial Λ X structureMap).obj (op ⦋n + 1⦌) ⟶
        (chartBaseChangeSimplicial Λ X structureMap).obj (op ⦋n⦌)) →+
      (chartBaseChangePresheaf Λ X structureMap).obj
        (op (resolutionChart Λ X structureMap U ⦋n⦌)) :=
    { toFun f := (f.app (op U)) (cotangentToChart Λ X structureMap U ⦋n + 1⦌ z)
      map_zero' := rfl
      map_add' _ _ := rfl }
  have h1 := map_sum evT (fun i : Fin (n + 2) => ((-1 : ℤ) ^ (i : ℕ)) •
    (CommAlgCat.cotangentSimplicialModule.{u, u} Λ
      (sectionCotangentAlgebra Λ X structureMap U)).object.δ i) Finset.univ
  have h3 := map_sum evS (fun i : Fin (n + 2) => ((-1 : ℤ) ^ (i : ℕ)) •
    (chartBaseChangeSimplicial Λ X structureMap).δ i) Finset.univ
  refine (congrArg (cotangentToChart Λ X structureMap U ⦋n⦌) h1).trans ?_
  refine Eq.trans ?_ ((congrArg evS hd).trans h3).symm
  refine (map_sum _ _ _).trans (Finset.sum_congr rfl fun i _ => ?_)
  refine ((congrArg (cotangentToChart Λ X structureMap U ⦋n⦌) (map_zsmul evT _ _)).trans
    (map_zsmul _ _ _)).trans (Eq.trans ?_ (map_zsmul evS _ _).symm)
  exact congrArg (((-1 : ℤ) ^ (i : ℕ)) • ·)
    (cotangentToChart_cotangentMap Λ X structureMap U (SimplexCategory.δ i) z)

/-- The degree `n` comparison `U ↦ L^{-n}_{𝒪_X(U)/Λ}` to `U ↦ (Ω_{𝒪/Λ̲} ⊗_𝒪 𝒪̲_X)(A_{n,U})`, as an
isomorphism of presheaves of modules over the lifted structure sheaf. -/
def cotangentChartComponentPresheafIso (n : ℕ) :
    (liftedSectionwiseCotangentComplex Λ X structureMap).X (-(n : ℤ)) ≅
      (chartBaseChangeMooreComplex Λ X structureMap).X n :=
  PresheafOfModules.isoMk (fun V => cotangentChartComponentIso Λ X structureMap V.unop n)
    (fun V W f => by
      ext x
      change cotangentToChart Λ X structureMap W.unop ⦋n⦌
          ((CommAlgCat.cotangentComplex_degreeIso.{u, u} Λ
            (sectionCotangentAlgebra Λ X structureMap W.unop) n).hom
            ((CommAlgCat.squareCotangentComplexMap.{u, u, u}
              (CommAlgCat.idSquare (sectionCotangentAlgebraMap Λ X structureMap f.unop))).f
                (-(n : ℤ)) x.down)) =
        (chartBaseChangePresheaf Λ X structureMap).map
          (((standardResolutionChart Λ X structureMap).map f.unop).app ⦋n⦌).op
          (cotangentToChart Λ X structureMap V.unop ⦋n⦌
            ((CommAlgCat.cotangentComplex_degreeIso.{u, u} Λ
              (sectionCotangentAlgebra Λ X structureMap V.unop) n).hom x.down))
      exact (congrArg (cotangentToChart Λ X structureMap W.unop ⦋n⦌)
        (degreeIso_hom_squareCotangentComplexMap Λ X structureMap f.unop n x.down)).trans
        (cotangentToChart_squareCotangentTermMap Λ X structureMap f.unop ⦋n⦌ _))

/-- The comparison commutes with the differentials. -/
theorem cotangentChartComponentPresheafIso_comm (n : ℕ) :
    (cotangentChartComponentPresheafIso Λ X structureMap (n + 1)).hom ≫
        (chartBaseChangeMooreComplex Λ X structureMap).d (n + 1) n =
      (liftedSectionwiseCotangentComplex Λ X structureMap).d (-(n + 1 : ℕ) : ℤ) (-(n : ℤ)) ≫
        (cotangentChartComponentPresheafIso Λ X structureMap n).hom := by
  ext V x
  show ((chartBaseChangeMooreComplex Λ X structureMap).d (n + 1) n).app V
      (cotangentToChart Λ X structureMap V.unop ⦋n + 1⦌
        ((CommAlgCat.cotangentComplex_degreeIso.{u, u} Λ
          (sectionCotangentAlgebra Λ X structureMap V.unop) (n + 1)).hom x.down)) =
    cotangentToChart Λ X structureMap V.unop ⦋n⦌
      ((CommAlgCat.cotangentComplex_degreeIso.{u, u} Λ
        (sectionCotangentAlgebra Λ X structureMap V.unop) n).hom
        ((CommAlgCat.cotangentComplex.{u, u} Λ (sectionCotangentAlgebra Λ X structureMap V.unop)).d
          (-(n + 1 : ℕ) : ℤ) (-(n : ℤ)) x.down))
  exact (cotangentToChart_objD Λ X structureMap V.unop n _).symm.trans
    (congrArg (cotangentToChart Λ X structureMap V.unop ⦋n⦌)
      (degreeIso_hom_cotangentComplex_d Λ (sectionCotangentAlgebra Λ X structureMap V.unop) n
        x.down).symm)


/-- The terms of `U ↦ L_{𝒪_X(U)/Λ}` vanish in positive degrees. -/
theorem isZero_liftedSectionwiseCotangentComplex_X (i : ℤ) (hi : 0 < i) :
    IsZero ((liftedSectionwiseCotangentComplex Λ X structureMap).X i) := by
  rw [PresheafOfModules.isZero_iff_forall_isZero_obj]
  intro V
  have h := CommAlgCat.cotangentComplex_isZero_pos.{u, u} Λ
    (sectionCotangentAlgebra Λ X structureMap V.unop) i hi
  rw [ModuleCat.isZero_iff_subsingleton] at h ⊢
  exact ⟨fun a b => ULift.ext _ _ (h.elim a.down b.down)⟩

/-- The comparison in each degree, assembled into a map of chain complexes from the restriction of
`U ↦ L_{𝒪_X(U)/Λ}` to non-positive degrees to the Moore complex of
`U ↦ (Ω_{𝒪/Λ̲} ⊗_𝒪 𝒪̲_X)(A_{•,U})`. -/
def restrictionToMooreComplex :
    (liftedSectionwiseCotangentComplex Λ X structureMap).restriction
        (ComplexShape.embeddingUpIntLE (0 : ℤ)) ⟶
      chartBaseChangeMooreComplex Λ X structureMap where
  f n := ((liftedSectionwiseCotangentComplex Λ X structureMap).restrictionXIso
      (ComplexShape.embeddingUpIntLE (0 : ℤ)) (i := n) (i' := -(n : ℤ)) (by simp)).hom ≫
    (cotangentChartComponentPresheafIso Λ X structureMap n).hom
  comm' i j hij := by
    obtain rfl : i = j + 1 := by simp only [ComplexShape.down_Rel] at hij; omega
    rw [HomologicalComplex.restriction_d_eq _ (ComplexShape.embeddingUpIntLE (0 : ℤ))
      (i' := -((j + 1 : ℕ) : ℤ)) (j' := -(j : ℤ)) (by simp) (by simp), Category.assoc,
      cotangentChartComponentPresheafIso_comm, Category.assoc, Category.assoc, Iso.inv_hom_id_assoc]

/-- The map of complexes `U ↦ L_{𝒪_X(U)/Λ}` to the reindexed Moore complex of
`U ↦ (Ω_{𝒪/Λ̲} ⊗_𝒪 𝒪̲_X)(A_{•,U})` attached to `restrictionToMooreComplex`. -/
def liftedSectionwiseToMooreCochain :
    liftedSectionwiseCotangentComplex Λ X structureMap ⟶
      (chartBaseChangeMooreComplex Λ X structureMap).extend
        (ComplexShape.embeddingUpIntLE (0 : ℤ)) :=
  (ComplexShape.embeddingUpIntLE (0 : ℤ)).liftExtend (restrictionToMooreComplex Λ X structureMap)
    (fun _ hj => hj.false_of_isTruncLE.elim)

/-- `liftedSectionwiseToMooreCochain` is an isomorphism in every degree. -/
instance isIso_liftedSectionwiseToMooreCochain :
    IsIso (liftedSectionwiseToMooreCochain Λ X structureMap) := by
  have h : ∀ i, IsIso ((liftedSectionwiseToMooreCochain Λ X structureMap).f i) := fun i => by
    by_cases hi : ∃ n, (ComplexShape.embeddingUpIntLE (0 : ℤ)).f n = i
    · obtain ⟨n, hn⟩ := hi
      exact ((ComplexShape.embeddingUpIntLE (0 : ℤ)).isIso_liftExtend_f_iff _ _ hn).mpr
        (by dsimp only [restrictionToMooreComplex]; infer_instance)
    · have hi' : ∀ n, (ComplexShape.embeddingUpIntLE (0 : ℤ)).f n ≠ i := fun n h => hi ⟨n, h⟩
      exact IsZero.isIso (isZero_liftedSectionwiseCotangentComplex_X Λ X structureMap i
        ((ComplexShape.notMem_range_embeddingUpIntLE_iff 0 i).mp hi'))
        ((chartBaseChangeMooreComplex Λ X structureMap).isZero_extend_X _ i hi') _
  exact HomologicalComplex.Hom.isIso_of_components _

/-- **The computation in the proof of Tag 08T9.** For a scheme `X` over a ring `Λ`, the complex of
presheaves of `𝒪_X`-modules `U ↦ (Ω_{𝒪/Λ̲} ⊗_𝒪 𝒪̲_X)(A_{•,U})` obtained by evaluating the presheaf
`(U ⟶ A) ↦ 𝒪_X(U) ⊗_{Γ(A)} Ω_{Γ(A)/Λ}` of the chart site on the cosimplicial charts
`A_{•,U} = Spec(P_{•,U})` of the standard resolutions `P_{•,U}` of `𝒪_X(U)` over `Λ`, placed in
non-positive degrees, is isomorphic, functorially in `U`, to the complex of presheaves
`U ↦ L_{𝒪_X(U)/Λ} = Ω_{P_{•,U}/Λ} ⊗_{P_{•,U}} 𝒪_X(U)`. Both are read over the lifted structure
sheaf of `X`. In degree `-n` over `U` the isomorphism is `b ⊗ d p ↦ b ⊗ d p`, through
`Γ(Spec P_{n,U}) ≅ P_{n,U}` and the identification of the standard resolutions of
`Γ(U, 𝒪_U)` and `𝒪_X(U)`. -/
def chartBaseChangePresheafMooreCochainIso :
    (modulePointMooreCochain (fibredCategorySituation Λ X structureMap)
        (standardResolutionChart_comp_whiskeringRight Λ X structureMap)
        (ringSheaf (liftedStructureSheaf.{u, u} X)).obj).obj
        (chartBaseChangePresheaf Λ X structureMap) ≅
      ((liftStructurePresheafModules.{u, u} X).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (SchemeOverRing.sectionwiseCotangentComplexConstant Λ structureMap) :=
  (asIso (liftedSectionwiseToMooreCochain Λ X structureMap)).symm

end AlgebraicGeometry.PolynomialChart
