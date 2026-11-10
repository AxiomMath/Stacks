module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.ShortExact
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.PointResolution.ModuleBicomplex
public import StacksFrontier.Cotangent.Spaces.ChartSiteStandardResolutionNaturality

/-!
# `(Ω_{𝒪/Λ̲} ⊗_𝒪 𝒪̲_X)(𝐀_{•,U}) = L_{𝒪_X(U)/Λ}` as complexes of presheaves, for spaces

Let `Λ` be a ring, `X` an algebraic space over `Λ`, and for an object `U` of `X_étale` let
`P_{•,U}` be the standard resolution of `𝒪_X(U)` over `Λ` and `𝐀_{•,U} = Spec(P_{•,U})` the
cosimplicial polynomial charts of Tag 08VL. The proof of Tag 08VM computes the complex of
presheaves `U ↦ (Ω_{𝒪/Λ̲} ⊗_𝒪 𝒪̲_X)(𝐀_{•,U})` as `U ↦ Ω_{P_{•,U}/Λ} ⊗_{P_{•,U}} 𝒪_X(U) =
L_{𝒪_X(U)/Λ}`, functorially in `U`. This file proves that computation: the Moore complex of the
evaluation of `(U ⟶ A) ↦ 𝒪_X(U) ⊗_{Γ(A)} Ω_{Γ(A)/Λ}` on the charts `𝐀_{•,U}`, placed in
non-positive cohomological degrees, is isomorphic to `U ↦ L_{𝒪_X(U)/Λ}`, both read as complexes of
presheaves of modules over the lifted structure sheaf of `X`, and so to the complex of Tag 08SX
over the constant presheaf `U ↦ Λ` at any `φ : Λ̲_X ⟶ 𝒪_X` restricting to the structure maps.

## Main results

* `AlgebraicGeometry.Space.PolynomialChart.chartBaseChangePresheafMooreCochainIso`: the
  isomorphism of complexes of presheaves of the proof of Tag 08VM.
* `AlgebraicGeometry.Space.PolynomialChart.chartBaseChangePresheafMooreCochainIsoConstant`: the
  same, with target `AlgebraicGeometry.Space.sectionwiseCotangentComplexConstant φ`.

## References

* [Stacks Project, Tag 08VM](https://stacks.math.columbia.edu/tag/08VM)
* [Stacks Project, Tag 08VL](https://stacks.math.columbia.edu/tag/08VL)
* [Stacks Project, Tag 08SX](https://stacks.math.columbia.edu/tag/08SX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open scoped ChangeOfRings TensorProduct
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Sites.FibredCategory.FibredCategorySituation

universe u

namespace AlgebraicGeometry.Space.PolynomialChart

variable (Λ : Type u) [CommRing Λ] (B : BigFppfSite.{u})
  (hS : B.Contains (Spec (CommRingCat.of Λ)))
  (X : (BigFppfOver B (Spec (CommRingCat.of Λ)) hS)ᵒᵖ ⥤ Type u)
  (hX : IsAlgebraicSpace B (Spec (CommRingCat.of Λ)) hS X)

/-- `cotangentToChart` carries the alternating sum of the faces of the cotangent simplicial module
to the differential of the complex `U ↦ (Ω_{𝒪/Λ̲} ⊗_𝒪 𝒪̲_X)(𝐀_{•,U})`. -/
theorem cotangentToChart_objD (U : SmallEtale B (Spec (CommRingCat.of Λ)) hS X) (n : ℕ)
    (z : CommAlgCat.cotangentTerm.{u + 1, u + 1} (ULift.{u + 1} Λ)
      (liftedSectionsAlgebra Λ B hS X U) (op ⦋n + 1⦌)) :
    cotangentToChart Λ B hS X hX U ⦋n⦌
        (AlgebraicTopology.AlternatingFaceMapComplex.objD
          (CommAlgCat.cotangentSimplicialModule.{u + 1, u + 1} (ULift.{u + 1} Λ)
            (liftedSectionsAlgebra Λ B hS X U)).object n z) =
      ((chartBaseChangeMooreComplex Λ B hS X hX).d (n + 1) n).app (op U)
        (cotangentToChart Λ B hS X hX U ⦋n + 1⦌ z) := by
  have hd := AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq
    (chartBaseChangeSimplicial Λ B hS X hX) n
  let evT : ((CommAlgCat.cotangentSimplicialModule.{u + 1, u + 1} (ULift.{u + 1} Λ)
      (liftedSectionsAlgebra Λ B hS X U)).object.obj (op ⦋n + 1⦌) ⟶
        (CommAlgCat.cotangentSimplicialModule.{u + 1, u + 1} (ULift.{u + 1} Λ)
          (liftedSectionsAlgebra Λ B hS X U)).object.obj (op ⦋n⦌)) →+
      CommAlgCat.cotangentTerm.{u + 1, u + 1} (ULift.{u + 1} Λ)
        (liftedSectionsAlgebra Λ B hS X U) (op ⦋n⦌) :=
    { toFun f := f z
      map_zero' := rfl
      map_add' _ _ := rfl }
  let evS : ((chartBaseChangeSimplicial Λ B hS X hX).obj (op ⦋n + 1⦌) ⟶
        (chartBaseChangeSimplicial Λ B hS X hX).obj (op ⦋n⦌)) →+
      (chartBaseChangePresheaf Λ B hS X hX).obj
        (op (resolutionChart Λ B hS X hX U ⦋n⦌)) :=
    { toFun f := (f.app (op U)) (cotangentToChart Λ B hS X hX U ⦋n + 1⦌ z)
      map_zero' := rfl
      map_add' _ _ := rfl }
  have h1 := map_sum evT (fun i : Fin (n + 2) => ((-1 : ℤ) ^ (i : ℕ)) •
    (CommAlgCat.cotangentSimplicialModule.{u + 1, u + 1} (ULift.{u + 1} Λ)
      (liftedSectionsAlgebra Λ B hS X U)).object.δ i) Finset.univ
  have h3 := map_sum evS (fun i : Fin (n + 2) => ((-1 : ℤ) ^ (i : ℕ)) •
    (chartBaseChangeSimplicial Λ B hS X hX).δ i) Finset.univ
  refine (congrArg (cotangentToChart Λ B hS X hX U ⦋n⦌) h1).trans ?_
  refine Eq.trans ?_ ((congrArg evS hd).trans h3).symm
  refine (map_sum _ _ _).trans (Finset.sum_congr rfl fun i _ => ?_)
  refine ((congrArg (cotangentToChart Λ B hS X hX U ⦋n⦌) (map_zsmul evT _ _)).trans
    (map_zsmul _ _ _)).trans (Eq.trans ?_ (map_zsmul evS _ _).symm)
  exact congrArg (((-1 : ℤ) ^ (i : ℕ)) • ·)
    (cotangentToChart_cotangentMap Λ B hS X hX U (SimplexCategory.δ i) z)

/-- The degree `n` comparison `U ↦ L^{-n}_{𝒪_X(U)/Λ}` to `U ↦ (Ω_{𝒪/Λ̲} ⊗_𝒪 𝒪̲_X)(𝐀_{n,U})`, as an
isomorphism of presheaves of modules over the lifted structure sheaf. -/
def cotangentChartComponentPresheafIso (n : ℕ) :
    (chartSectionwiseCotangentComplex Λ B hS X hX).X (-(n : ℤ)) ≅
      (chartBaseChangeMooreComplex Λ B hS X hX).X n :=
  PresheafOfModules.isoMk (fun V => cotangentChartComponentIso Λ B hS X hX V.unop n)
    (fun V W f => by
      ext x
      change cotangentToChart Λ B hS X hX W.unop ⦋n⦌
          ((CommAlgCat.cotangentComplex_degreeIso.{u + 1, u + 1} (ULift.{u + 1} Λ)
            (liftedSectionsAlgebra Λ B hS X W.unop) n).hom
            ((CommAlgCat.squareCotangentComplexMap.{u + 1, u + 1, u + 1}
              (CommAlgCat.idSquare ((CommAlgCat.uliftBaseFunctor Λ).map
                (sectionsAlgebraRestrict Λ B hS X f.unop)))).f (-(n : ℤ)) x)) =
        (chartBaseChangePresheaf Λ B hS X hX).map
          (((standardResolutionChart Λ B hS X hX).map f.unop).app ⦋n⦌).op
          (cotangentToChart Λ B hS X hX V.unop ⦋n⦌
            ((CommAlgCat.cotangentComplex_degreeIso.{u + 1, u + 1} (ULift.{u + 1} Λ)
              (liftedSectionsAlgebra Λ B hS X V.unop) n).hom x))
      exact (congrArg (cotangentToChart Λ B hS X hX W.unop ⦋n⦌)
        (degreeIso_hom_squareCotangentComplexMap Λ B hS X f.unop n x)).trans
        (cotangentToChart_squareCotangentTermMap Λ B hS X hX f.unop ⦋n⦌ _))

/-- The comparison commutes with the differentials. -/
theorem cotangentChartComponentPresheafIso_comm (n : ℕ) :
    (cotangentChartComponentPresheafIso Λ B hS X hX (n + 1)).hom ≫
        (chartBaseChangeMooreComplex Λ B hS X hX).d (n + 1) n =
      (chartSectionwiseCotangentComplex Λ B hS X hX).d (-(n + 1 : ℕ) : ℤ) (-(n : ℤ)) ≫
        (cotangentChartComponentPresheafIso Λ B hS X hX n).hom := by
  ext V x
  change ((chartBaseChangeMooreComplex Λ B hS X hX).d (n + 1) n).app V
      (cotangentToChart Λ B hS X hX V.unop ⦋n + 1⦌
        ((CommAlgCat.cotangentComplex_degreeIso.{u + 1, u + 1} (ULift.{u + 1} Λ)
          (liftedSectionsAlgebra Λ B hS X V.unop) (n + 1)).hom x)) =
    cotangentToChart Λ B hS X hX V.unop ⦋n⦌
      ((CommAlgCat.cotangentComplex_degreeIso.{u + 1, u + 1} (ULift.{u + 1} Λ)
        (liftedSectionsAlgebra Λ B hS X V.unop) n).hom
        ((CommAlgCat.cotangentComplex.{u + 1, u + 1} (ULift.{u + 1} Λ)
          (liftedSectionsAlgebra Λ B hS X V.unop)).d (-(n + 1 : ℕ) : ℤ) (-(n : ℤ)) x))
  exact (cotangentToChart_objD Λ B hS X hX V.unop n _).symm.trans
    (congrArg (cotangentToChart Λ B hS X hX V.unop ⦋n⦌)
      (AlgebraicGeometry.PolynomialChart.degreeIso_hom_cotangentComplex_d (ULift.{u + 1} Λ)
        (liftedSectionsAlgebra Λ B hS X V.unop) n x).symm)

/-- The terms of `U ↦ L_{𝒪_X(U)/Λ}` vanish in positive degrees. -/
theorem isZero_chartSectionwiseCotangentComplex_X (i : ℤ) (hi : 0 < i) :
    IsZero ((chartSectionwiseCotangentComplex Λ B hS X hX).X i) := by
  rw [PresheafOfModules.isZero_iff_forall_isZero_obj]
  intro V
  exact CommAlgCat.cotangentComplex_isZero_pos.{u + 1, u + 1} (ULift.{u + 1} Λ)
    (liftedSectionsAlgebra Λ B hS X V.unop) i hi

/-- The comparison in each degree, assembled into a map of chain complexes from the restriction of
`U ↦ L_{𝒪_X(U)/Λ}` to non-positive degrees to the Moore complex of
`U ↦ (Ω_{𝒪/Λ̲} ⊗_𝒪 𝒪̲_X)(𝐀_{•,U})`. -/
def restrictionToMooreComplex :
    (chartSectionwiseCotangentComplex Λ B hS X hX).restriction
        (ComplexShape.embeddingUpIntLE (0 : ℤ)) ⟶
      chartBaseChangeMooreComplex Λ B hS X hX where
  f n := ((chartSectionwiseCotangentComplex Λ B hS X hX).restrictionXIso
      (ComplexShape.embeddingUpIntLE (0 : ℤ)) (i := n) (i' := -(n : ℤ)) (by simp)).hom ≫
    (cotangentChartComponentPresheafIso Λ B hS X hX n).hom
  comm' i j hij := by
    obtain rfl : i = j + 1 := by simp only [ComplexShape.down_Rel] at hij; omega
    rw [HomologicalComplex.restriction_d_eq _ (ComplexShape.embeddingUpIntLE (0 : ℤ))
      (i' := -((j + 1 : ℕ) : ℤ)) (j' := -(j : ℤ)) (by simp) (by simp), Category.assoc,
      cotangentChartComponentPresheafIso_comm, Category.assoc, Category.assoc,
      Iso.inv_hom_id_assoc]

/-- The map of complexes from `U ↦ L_{𝒪_X(U)/Λ}` to the reindexed Moore complex of
`U ↦ (Ω_{𝒪/Λ̲} ⊗_𝒪 𝒪̲_X)(𝐀_{•,U})` attached to `restrictionToMooreComplex`. -/
def chartSectionwiseToMooreCochain :
    chartSectionwiseCotangentComplex Λ B hS X hX ⟶
      (chartBaseChangeMooreComplex Λ B hS X hX).extend
        (ComplexShape.embeddingUpIntLE (0 : ℤ)) :=
  (ComplexShape.embeddingUpIntLE (0 : ℤ)).liftExtend (restrictionToMooreComplex Λ B hS X hX)
    (fun _ hj => hj.false_of_isTruncLE.elim)

/-- `chartSectionwiseToMooreCochain` is an isomorphism in every degree. -/
instance isIso_chartSectionwiseToMooreCochain :
    IsIso (chartSectionwiseToMooreCochain Λ B hS X hX) := by
  have h : ∀ i, IsIso ((chartSectionwiseToMooreCochain Λ B hS X hX).f i) := fun i => by
    by_cases hi : ∃ n, (ComplexShape.embeddingUpIntLE (0 : ℤ)).f n = i
    · obtain ⟨n, hn⟩ := hi
      exact ((ComplexShape.embeddingUpIntLE (0 : ℤ)).isIso_liftExtend_f_iff _ _ hn).mpr
        (by dsimp only [restrictionToMooreComplex]; infer_instance)
    · have hi' : ∀ n, (ComplexShape.embeddingUpIntLE (0 : ℤ)).f n ≠ i := fun n h => hi ⟨n, h⟩
      exact IsZero.isIso (isZero_chartSectionwiseCotangentComplex_X Λ B hS X hX i
        ((ComplexShape.notMem_range_embeddingUpIntLE_iff 0 i).mp hi'))
        ((chartBaseChangeMooreComplex Λ B hS X hX).isZero_extend_X _ i hi') _
  exact HomologicalComplex.Hom.isIso_of_components _

/-- **The computation in the proof of Tag 08VM.** For an algebraic space `X` over a ring `Λ`, the
complex of presheaves of `𝒪_X`-modules `U ↦ (Ω_{𝒪/Λ̲} ⊗_𝒪 𝒪̲_X)(𝐀_{•,U})` on `X_étale`, obtained by
evaluating the presheaf `(U ⟶ A) ↦ 𝒪_X(U) ⊗_{Γ(A)} Ω_{Γ(A)/Λ}` of the chart site on the
cosimplicial charts `𝐀_{•,U} = Spec(P_{•,U})` of the standard resolutions `P_{•,U}` of `𝒪_X(U)`
over `Λ`, placed in non-positive degrees, is isomorphic, functorially in `U`, to the complex of
presheaves `U ↦ L_{𝒪_X(U)/Λ} = Ω_{P_{•,U}/Λ} ⊗_{P_{•,U}} 𝒪_X(U)`, for the `Λ`-algebra structures of
the structure morphisms `U ⟶ Spec Λ`. Both are read over the lifted structure sheaf of `X`. In
degree `-n` over `U` the isomorphism is `b ⊗ d p ↦ b ⊗ d p`, through `Γ(Spec P_{n,U}) ≅ P_{n,U}`
and the universe lift of the standard resolution. -/
def chartBaseChangePresheafMooreCochainIso :
    (modulePointMooreCochain (fibredCategorySituation Λ B hS X hX)
        (standardResolutionChart_comp_whiskeringRight Λ B hS X hX)
        (ringSheaf (smallEtaleStructureSheafULift B (Spec (CommRingCat.of Λ)) hS
          ⟨X, hX⟩)).obj).obj (chartBaseChangePresheaf Λ B hS X hX) ≅
      chartSectionwiseCotangentComplex Λ B hS X hX :=
  (asIso (chartSectionwiseToMooreCochain Λ B hS X hX)).symm

variable {Λ B hS X hX} in
/-- For a homomorphism `φ : Λ̲_X ⟶ 𝒪_X` from the constant sheaf which restricts on the constant
presheaf `U ↦ Λ` to the structure maps `Λ → 𝒪_X(U)` of the structure morphisms `U ⟶ Spec Λ`, the
complex `U ↦ L_{𝒪_X(U)/Λ}` of Tag 08SX at `φ` is the one of the charts. -/
theorem chartSectionwiseCotangentComplex_eq
    (φ : (constantSheaf (SmallEtale.topology B (Spec (CommRingCat.of Λ)) hS X)
      CommRingCat.{u}).obj (CommRingCat.of Λ) ⟶
        (smallEtaleRingedTopos B (Spec (CommRingCat.of Λ)) hS ⟨X, hX⟩).O)
    (hφ : toSheafify (SmallEtale.topology B (Spec (CommRingCat.of Λ)) hS X)
        ((Functor.const _).obj (CommRingCat.of Λ)) ≫ φ.hom =
      etaleConstantStructurePresheafMap Λ B hS X) :
    chartSectionwiseCotangentComplex Λ B hS X hX = sectionwiseCotangentComplexConstant φ := by
  refine congrArg (CategoryTheory.Sheaf.sectionwiseCotangentModuleComplex.{u + 1, u, u} ⊥) ?_
  refine CategoryTheory.Sheaf.hom_ext ?_
  change Functor.whiskerRight (etaleConstantStructurePresheafMap Λ B hS X)
      AlgebraicGeometry.SheafOfModules.commRingCatULift.{u, u + 1} =
    Functor.whiskerRight (toSheafify (SmallEtale.topology B (Spec (CommRingCat.of Λ)) hS X)
        ((Functor.const _).obj (CommRingCat.of Λ)))
      AlgebraicGeometry.SheafOfModules.commRingCatULift.{u, u + 1} ≫
      Functor.whiskerRight φ.hom AlgebraicGeometry.SheafOfModules.commRingCatULift.{u, u + 1}
  exact (congrArg (fun t => Functor.whiskerRight t
    AlgebraicGeometry.SheafOfModules.commRingCatULift.{u, u + 1}) hφ).symm.trans
    (Functor.whiskerRight_comp _ _ _)

variable {Λ B hS X hX} in
/-- **The computation in the proof of Tag 08VM, for the cotangent complex of Tag 08SX at `φ`.**
For a homomorphism `φ : Λ̲_X ⟶ 𝒪_X` from the constant sheaf on `X_étale` which restricts on the
constant presheaf `U ↦ Λ` to the structure maps of the structure morphisms `U ⟶ Spec Λ`, the
Moore complex of `U ↦ (Ω_{𝒪/Λ̲} ⊗_𝒪 𝒪̲_X)(𝐀_{•,U})`, placed in non-positive degrees, is the complex
`U ↦ L_{𝒪_X(U)/Λ}` of `AlgebraicGeometry.Space.sectionwiseCotangentComplexConstant φ`, whose
degreewise sheafification is `L_{𝒪_X/Λ̲_X}`
(`AlgebraicGeometry.Space.sheafifiedSectionwiseCotangentComplexConstantIso`). -/
def chartBaseChangePresheafMooreCochainIsoConstant
    (φ : (constantSheaf (SmallEtale.topology B (Spec (CommRingCat.of Λ)) hS X)
      CommRingCat.{u}).obj (CommRingCat.of Λ) ⟶
        (smallEtaleRingedTopos B (Spec (CommRingCat.of Λ)) hS ⟨X, hX⟩).O)
    (hφ : toSheafify (SmallEtale.topology B (Spec (CommRingCat.of Λ)) hS X)
        ((Functor.const _).obj (CommRingCat.of Λ)) ≫ φ.hom =
      etaleConstantStructurePresheafMap Λ B hS X) :
    (modulePointMooreCochain (fibredCategorySituation Λ B hS X hX)
        (standardResolutionChart_comp_whiskeringRight Λ B hS X hX)
        (ringSheaf (smallEtaleStructureSheafULift B (Spec (CommRingCat.of Λ)) hS
          ⟨X, hX⟩)).obj).obj (chartBaseChangePresheaf Λ B hS X hX) ≅
      sectionwiseCotangentComplexConstant φ :=
  chartBaseChangePresheafMooreCochainIso Λ B hS X hX ≪≫
    eqToIso (chartSectionwiseCotangentComplex_eq φ hφ)

end AlgebraicGeometry.Space.PolynomialChart
