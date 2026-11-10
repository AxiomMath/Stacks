module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.PointResolution.ModuleBasic
public import StacksFrontier.Cotangent.ChartSiteStandardResolutionNaturality
public import StacksFrontier.Cotangent.Spaces.ChartSiteStandardResolutionComparison

/-!
# Naturality of the comparison on the charts of the standard resolutions, for spaces

This file proves that the identification
`𝒪_X(U) ⊗_{Γ(𝐀_{n,U})} Ω_{Γ(𝐀_{n,U})/Λ} = L^{-n}_{𝒪_X(U)/Λ}` of
`StacksFrontier/Cotangent/Spaces/ChartSiteStandardResolutionComparison.lean`, used in the proof of
Tag 08VM, is compatible with the cosimplicial structure of the charts `𝐀_{•,U}` and with the maps
of charts `𝐀_{n,V} ⟶ 𝐀_{n,U}` over arrows `V ⟶ U` of `X_étale`, and assembles it, in each degree,
into an isomorphism of modules over the lifted structure sheaf of `X`.

## Main definitions

* `AlgebraicGeometry.Space.PolynomialChart.chartSectionwiseCotangentComplex`: the complex of
  presheaves `U ↦ L_{𝒪_X(U)/Λ}` on `X_étale`.
* `AlgebraicGeometry.Space.PolynomialChart.chartBaseChangeMooreComplex`: the Moore complex of
  `U ↦ (Ω_{𝒪/Λ̲} ⊗_𝒪 𝒪̲_X)(𝐀_{•,U})`.
* `AlgebraicGeometry.Space.PolynomialChart.cotangentChartComponentIso`: the comparison on the
  sections over an object of `X_étale`, as an isomorphism of modules.

## Main results

* `AlgebraicGeometry.Space.PolynomialChart.cotangentToChart_squareCotangentTermMap`: naturality
  in the object of `X_étale`.
* `AlgebraicGeometry.Space.PolynomialChart.cotangentToChart_cotangentMap`: compatibility with the
  simplicial structure.

## References

* [Stacks Project, Tag 08VM](https://stacks.math.columbia.edu/tag/08VM)
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

/-! ### Naturality of the comparison -/

/-- `cotangentToChart` on a pure differential `1 ⊗ d q`. -/
theorem cotangentToChart_differential (U : SmallEtale B (Spec (CommRingCat.of Λ)) hS X)
    (n : SimplexCategory) (q : resolutionTermAlgebra Λ B hS X U n) :
    cotangentToChart Λ B hS X hX U n
        (CommAlgCat.cotangentTermDifferential.{u + 1, u + 1} (ULift.{u + 1} Λ)
          (liftedSectionsAlgebra Λ B hS X U) (op n) q) =
      letI := ((liftedEvaluation Λ B hS X hX).app
        (op (resolutionChart Λ B hS X hX U n))).hom.toAlgebra
      ((1 : (liftedEtalePresheaf Λ B hS X hX).obj
          (op (resolutionChart Λ B hS X hX U n))) ⊗ₜ[resolutionChartRing Λ B hS X hX U n]
        (ULift.up (CommRingCat.KaehlerDifferential.d
          (resolutionToChartHom Λ B hS X hX U n q)) :
          ULift.{u + 1} (resolutionChartDifferentials Λ B hS X hX U n)) :
        TensorProduct (resolutionChartRing Λ B hS X hX U n)
          ((liftedEtalePresheaf Λ B hS X hX).obj (op (resolutionChart Λ B hS X hX U n)))
          (ULift.{u + 1} (resolutionChartDifferentials Λ B hS X hX U n))) := by
  let := ((liftedEvaluation Λ B hS X hX).app
    (op (resolutionChart Λ B hS X hX U n))).hom.toAlgebra
  change chartSectionsUp Λ B hS X hX U n 1 ⊗ₜ[resolutionChartRing Λ B hS X hX U n]
      (ULift.up (resolutionToChartDifferentials Λ B hS X hX U n
        (KaehlerDifferential.D (ULift.{u + 1} Λ) _ q)) :
          ULift.{u + 1} (resolutionChartDifferentials Λ B hS X hX U n)) = _
  rw [resolutionToChartDifferentials_D, map_one]

/-- If `f ≫ e'.hom = e.hom ≫ g` for isomorphisms `e`, `e'`, then `f` commutes with `g` through
the inverses. -/
private theorem inv_apply_comp_eq {A B A' B' : CommRingCat.{u + 1}} (e : A ≅ B) (e' : A' ≅ B')
    (f : A ⟶ A') (g : B ⟶ B') (hc : f ≫ e'.hom = e.hom ≫ g) (q : B) :
    f (e.inv q) = e'.inv (g q) := by
  have hc' := ConcreteCategory.congr_hom hc (e.inv q)
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply, Iso.inv_hom_id_apply] at hc'
  exact (Iso.hom_inv_id_apply _ _).symm.trans (congrArg _ hc')

/-- The inverse of `chartResolutionIso` is natural in the object of the small étale site. -/
theorem chartResolutionIso_inv_restriction {U V : SmallEtale B (Spec (CommRingCat.of Λ)) hS X}
    (h : V ⟶ U) (n : SimplexCategory) (q : resolutionTermAlgebra Λ B hS X U n) :
    (liftedAffinePresheaf Λ B hS X hX).map (((standardResolutionChart Λ B hS X hX).map h).app n).op
        ((chartResolutionIso Λ B hS X hX U n).inv q) =
      (chartResolutionIso Λ B hS X hX V n).inv
        ((((CommAlgCat.standardResolutionFunctor.{u + 1, u + 1} (ULift.{u + 1} Λ)).map
          ((CommAlgCat.uliftBaseFunctor Λ).map
            (sectionsAlgebraRestrict Λ B hS X h))).left.app (op n)) q) := by
  exact inv_apply_comp_eq _ _ _ _ (chartResolutionIso_hom_restriction Λ B hS X hX h n) q

/-- The inverse of `chartResolutionIso` is compatible with the simplicial structure. -/
theorem chartResolutionIso_inv_naturality (U : SmallEtale B (Spec (CommRingCat.of Λ)) hS X)
    {m n : SimplexCategory} (θ : m ⟶ n) (q : resolutionTermAlgebra Λ B hS X U n) :
    (liftedAffinePresheaf Λ B hS X hX).map (((standardResolutionChart Λ B hS X hX).obj U).map θ).op
        ((chartResolutionIso Λ B hS X hX U n).inv q) =
      (chartResolutionIso Λ B hS X hX U m).inv
        ((CommAlgCat.standardResolution.{u + 1, u + 1} (ULift.{u + 1} Λ)
          (liftedSectionsAlgebra Λ B hS X U)).left.map θ.op q) := by
  exact inv_apply_comp_eq _ _ _ _ (chartResolutionIso_hom_naturality Λ B hS X hX U θ) q

/-- The complex of presheaves of modules `U ↦ L_{𝒪_X(U)/Λ}` on the small étale site of `X`, over
the lifted structure sheaf, for the `Λ`-algebra structures `Λ → 𝒪_X(U)` of the structure
morphisms `U ⟶ Spec Λ`: the sectionwise cotangent complexes of Tag 08SX at `chartBaseHom`. -/
abbrev chartSectionwiseCotangentComplex :
    CochainComplex (PresheafOfModules.{u + 1}
      (ringSheaf (smallEtaleStructureSheafULift B (Spec (CommRingCat.of Λ)) hS ⟨X, hX⟩)).obj) ℤ :=
  CategoryTheory.Sheaf.sectionwiseCotangentModuleComplex.{u + 1, u, u} ⊥
    (chartBaseHom Λ B hS X hX)

/-- The restriction squares of `U ↦ L_{𝒪_X(U)/Λ}` do not move the base ring `ULift Λ`. -/
theorem sectionsRestrictionSquare_chartBaseHom {U V : SmallEtale B (Spec (CommRingCat.of Λ)) hS X}
    (h : V ⟶ U) :
    CategoryTheory.Sheaf.sectionsRestrictionSquare.{u + 1, u, u} ⊥ (chartBaseHom Λ B hS X hX)
        h.op =
      CommAlgCat.idSquare ((CommAlgCat.uliftBaseFunctor Λ).map
        (sectionsAlgebraRestrict Λ B hS X h)) :=
  rfl

/-- The ring map `ULift 𝒪_X(U) → ULift 𝒪_X(V)` along which the restriction maps of both sides of
the comparison over `V ⟶ U` are semilinear. -/
def sectionRestrictionUp {U V : SmallEtale B (Spec (CommRingCat.of Λ)) hS X} (h : V ⟶ U)
    (n : SimplexCategory) :
    liftedSectionsAlgebra Λ B hS X U →+*
      (chartStructureRing Λ B hS X hX).obj.obj (op (resolutionChart Λ B hS X hX V n)) :=
  (chartScalarUp Λ B hS X hX V n).comp
    ((CommAlgCat.uliftBaseFunctor Λ).map (sectionsAlgebraRestrict Λ B hS X h)).hom.toRingHom

/-- **The comparison is natural in the object of the small étale site.** Over `V ⟶ U`,
`cotangentToChart` intertwines the restriction map of `U ↦ L^{-n}_{𝒪_X(U)/Λ}` with the restriction
map of `U ↦ (Ω_{𝒪/Λ̲} ⊗_𝒪 𝒪̲_X)(𝐀_{n,U})` along the map of charts `𝐀_{n,V} ⟶ 𝐀_{n,U}`. -/
theorem cotangentToChart_squareCotangentTermMap
    {U V : SmallEtale B (Spec (CommRingCat.of Λ)) hS X} (h : V ⟶ U) (n : SimplexCategory)
    (z : CommAlgCat.cotangentTerm.{u + 1, u + 1} (ULift.{u + 1} Λ)
      (liftedSectionsAlgebra Λ B hS X U) (op n)) :
    cotangentToChart Λ B hS X hX V n
        ((CommAlgCat.squareCotangentTermMap.{u + 1, u + 1, u + 1}
          (CommAlgCat.idSquare ((CommAlgCat.uliftBaseFunctor Λ).map
            (sectionsAlgebraRestrict Λ B hS X h))) (op n)) z) =
      (chartBaseChangePresheaf Λ B hS X hX).map
        (((standardResolutionChart Λ B hS X hX).map h).app n).op
        (cotangentToChart Λ B hS X hX U n z) := by
  have key := CommAlgCat.cotangentTerm_addMonoidHom_ext (op n)
    (R := (chartStructureRing Λ B hS X hX).obj.obj
      (op (resolutionChart Λ B hS X hX V n)))
    (N := (chartBaseChangePresheaf Λ B hS X hX).obj
      (op (resolutionChart Λ B hS X hX V n)))
    (sectionRestrictionUp Λ B hS X hX h n)
    ((cotangentToChart Λ B hS X hX V n).comp
      (CommAlgCat.squareCotangentTermMap.{u + 1, u + 1, u + 1}
        (CommAlgCat.idSquare ((CommAlgCat.uliftBaseFunctor Λ).map
          (sectionsAlgebraRestrict Λ B hS X h))) (op n)).hom.toAddMonoidHom)
    (((chartBaseChangePresheaf Λ B hS X hX).map
        (((standardResolutionChart Λ B hS X hX).map h).app n).op).hom.toAddMonoidHom.comp
      (cotangentToChart Λ B hS X hX U n))
    (fun b x => (congrArg (cotangentToChart Λ B hS X hX V n)
      ((CommAlgCat.squareCotangentTermMap.{u + 1, u + 1, u + 1} (CommAlgCat.idSquare
        ((CommAlgCat.uliftBaseFunctor Λ).map (sectionsAlgebraRestrict Λ B hS X h)))
          (op n)).hom.map_smul b x)).trans
      (cotangentToChart_smul Λ B hS X hX V n _ _))
    (fun b x => (congrArg ((chartBaseChangePresheaf Λ B hS X hX).map
        (((standardResolutionChart Λ B hS X hX).map h).app n).op).hom
        (cotangentToChart_smul Λ B hS X hX U n b x)).trans
      (((chartBaseChangePresheaf Λ B hS X hX).map
        (((standardResolutionChart Λ B hS X hX).map h).app n).op).hom.map_smul _ _))
    (fun p => by
      let := ((liftedEvaluation Λ B hS X hX).app
        (op (resolutionChart Λ B hS X hX U n))).hom.toAlgebra
      let := ((liftedEvaluation Λ B hS X hX).app
        (op (resolutionChart Λ B hS X hX V n))).hom.toAlgebra
      change cotangentToChart Λ B hS X hX V n ((CommAlgCat.squareCotangentTermMap.{u + 1, u + 1,
          u + 1} (CommAlgCat.idSquare ((CommAlgCat.uliftBaseFunctor Λ).map
            (sectionsAlgebraRestrict Λ B hS X h))) (op n))
            (CommAlgCat.cotangentTermDifferential.{u + 1, u + 1} (ULift.{u + 1} Λ) _ (op n) p)) =
        (chartBaseChangePresheaf Λ B hS X hX).map
          (((standardResolutionChart Λ B hS X hX).map h).app n).op
          (cotangentToChart Λ B hS X hX U n
            (CommAlgCat.cotangentTermDifferential.{u + 1, u + 1} (ULift.{u + 1} Λ) _ (op n) p))
      rw [CommAlgCat.squareCotangentTermMap_D]
      change chartSectionsUp Λ B hS X hX V n 1 ⊗ₜ[resolutionChartRing Λ B hS X hX V n]
          (ULift.up (resolutionToChartDifferentials Λ B hS X hX V n
            (KaehlerDifferential.D (ULift.{u + 1} Λ) _
              (CommAlgCat.standardResolutionSquareMap.{u + 1, u + 1, u + 1}
                (CommAlgCat.idSquare ((CommAlgCat.uliftBaseFunctor Λ).map
                  (sectionsAlgebraRestrict Λ B hS X h))) (op n) p))) :
            ULift.{u + 1} (resolutionChartDifferentials Λ B hS X hX V n)) =
        (liftedEtalePresheaf Λ B hS X hX).map
            (((standardResolutionChart Λ B hS X hX).map h).app n).op
            (chartSectionsUp Λ B hS X hX U n 1) ⊗ₜ[resolutionChartRing Λ B hS X hX V n]
          (ULift.up ((PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'
              (liftedBasePresheafMap Λ B hS X hX)).map
            (((standardResolutionChart Λ B hS X hX).map h).app n).op
            (resolutionToChartDifferentials Λ B hS X hX U n
              (KaehlerDifferential.D (ULift.{u + 1} Λ) _ p))) :
            ULift.{u + 1} (resolutionChartDifferentials Λ B hS X hX V n))
      rw [resolutionToChartDifferentials_D, resolutionToChartDifferentials_D, map_one, map_one,
        map_one]
      refine congrArg (fun m => (1 : (liftedEtalePresheaf Λ B hS X hX).obj
        (op (resolutionChart Λ B hS X hX V n))) ⊗ₜ[resolutionChartRing Λ B hS X hX V n]
          (ULift.up m : ULift.{u + 1} (resolutionChartDifferentials Λ B hS X hX V n))) ?_
      refine Eq.trans ?_
        (PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'_map_d
          _ _ _).symm
      refine congrArg CommRingCat.KaehlerDifferential.d ?_
      change (chartResolutionIso Λ B hS X hX V n).inv
          (CommAlgCat.standardResolutionSquareMap.{u + 1, u + 1, u + 1}
            (CommAlgCat.idSquare ((CommAlgCat.uliftBaseFunctor Λ).map
              (sectionsAlgebraRestrict Λ B hS X h))) (op n) p) =
        (liftedAffinePresheaf Λ B hS X hX).map
          (((standardResolutionChart Λ B hS X hX).map h).app n).op
          ((chartResolutionIso Λ B hS X hX U n).inv p)
      rw [chartResolutionIso_inv_restriction, CommAlgCat.standardResolutionSquareMap_idSquare]
      rfl)
  exact DFunLike.congr_fun key z

/-- The structure maps of the cosimplicial chart `𝐀_{•,U}` lie over the identity of `U`, so the
restriction of lifted sections along them is the identity. -/
theorem chartStructureRing_map_chartScalarUp (U : SmallEtale B (Spec (CommRingCat.of Λ)) hS X)
    {m n : SimplexCategory} (θ : m ⟶ n) (b : liftedSectionsAlgebra Λ B hS X U) :
    (chartStructureRing Λ B hS X hX).obj.map
        (((standardResolutionChart Λ B hS X hX).obj U).map θ).op
        (chartScalarUp Λ B hS X hX U n b) =
      chartScalarUp Λ B hS X hX U m b := by
  change (ringSheaf (smallEtaleStructureSheafULift B (Spec (CommRingCat.of Λ)) hS
      ⟨X, hX⟩)).obj.map (𝟙 (op U)) b = b
  rw [CategoryTheory.Functor.map_id]
  rfl

/-- **The comparison is compatible with the simplicial structure.** For `θ : [m] ⟶ [n]`,
`cotangentToChart` intertwines the simplicial structure map of the cotangent simplicial module of
`ULift 𝒪_X(U)` with the map induced by the cosimplicial structure map `𝐀_{m,U} ⟶ 𝐀_{n,U}`. -/
theorem cotangentToChart_cotangentMap (U : SmallEtale B (Spec (CommRingCat.of Λ)) hS X)
    {m n : SimplexCategory} (θ : m ⟶ n)
    (z : CommAlgCat.cotangentTerm.{u + 1, u + 1} (ULift.{u + 1} Λ)
      (liftedSectionsAlgebra Λ B hS X U) (op n)) :
    cotangentToChart Λ B hS X hX U m
        (CommAlgCat.cotangentMap.{u + 1, u + 1} (ULift.{u + 1} Λ)
          (liftedSectionsAlgebra Λ B hS X U) θ.op z) =
      (chartBaseChangePresheaf Λ B hS X hX).map
        (((standardResolutionChart Λ B hS X hX).obj U).map θ).op
        (cotangentToChart Λ B hS X hX U n z) := by
  have key := CommAlgCat.cotangentTerm_addMonoidHom_ext (op n)
    (R := (chartStructureRing Λ B hS X hX).obj.obj
      (op (resolutionChart Λ B hS X hX U m)))
    (N := (chartBaseChangePresheaf Λ B hS X hX).obj
      (op (resolutionChart Λ B hS X hX U m)))
    (chartScalarUp Λ B hS X hX U m)
    ((cotangentToChart Λ B hS X hX U m).comp
      (CommAlgCat.cotangentMap.{u + 1, u + 1} (ULift.{u + 1} Λ)
        (liftedSectionsAlgebra Λ B hS X U) θ.op).hom.toAddMonoidHom)
    (((chartBaseChangePresheaf Λ B hS X hX).map
        (((standardResolutionChart Λ B hS X hX).obj U).map θ).op).hom.toAddMonoidHom.comp
      (cotangentToChart Λ B hS X hX U n))
    (fun b x => (congrArg (cotangentToChart Λ B hS X hX U m)
      ((CommAlgCat.cotangentMap.{u + 1, u + 1} (ULift.{u + 1} Λ)
        (liftedSectionsAlgebra Λ B hS X U) θ.op).hom.map_smul b x)).trans
      (cotangentToChart_smul Λ B hS X hX U m _ _))
    (fun b x => by
      refine (congrArg ((chartBaseChangePresheaf Λ B hS X hX).map
        (((standardResolutionChart Λ B hS X hX).obj U).map θ).op).hom
        (cotangentToChart_smul Λ B hS X hX U n b x)).trans ?_
      refine (((chartBaseChangePresheaf Λ B hS X hX).map
        (((standardResolutionChart Λ B hS X hX).obj U).map θ).op).hom.map_smul _ _).trans ?_
      change (chartStructureRing Λ B hS X hX).obj.map
          (((standardResolutionChart Λ B hS X hX).obj U).map θ).op
          (chartScalarUp Λ B hS X hX U n b) •
        (show (chartBaseChangePresheaf Λ B hS X hX).obj
            (op (resolutionChart Λ B hS X hX U m)) from
          (chartBaseChangePresheaf Λ B hS X hX).map
            (((standardResolutionChart Λ B hS X hX).obj U).map θ).op
            (cotangentToChart Λ B hS X hX U n x)) = _
      rw [chartStructureRing_map_chartScalarUp]
      rfl)
    (fun p => by
      let := ((liftedEvaluation Λ B hS X hX).app
        (op (resolutionChart Λ B hS X hX U n))).hom.toAlgebra
      let := ((liftedEvaluation Λ B hS X hX).app
        (op (resolutionChart Λ B hS X hX U m))).hom.toAlgebra
      change cotangentToChart Λ B hS X hX U m (CommAlgCat.cotangentMap.{u + 1, u + 1}
          (ULift.{u + 1} Λ) (liftedSectionsAlgebra Λ B hS X U) θ.op
            (CommAlgCat.cotangentTermDifferential.{u + 1, u + 1} (ULift.{u + 1} Λ) _ (op n) p)) =
        (chartBaseChangePresheaf Λ B hS X hX).map
          (((standardResolutionChart Λ B hS X hX).obj U).map θ).op
          (cotangentToChart Λ B hS X hX U n
            (CommAlgCat.cotangentTermDifferential.{u + 1, u + 1} (ULift.{u + 1} Λ) _ (op n) p))
      rw [CommAlgCat.cotangentMap_D]
      change chartSectionsUp Λ B hS X hX U m 1 ⊗ₜ[resolutionChartRing Λ B hS X hX U m]
          (ULift.up (resolutionToChartDifferentials Λ B hS X hX U m
            (KaehlerDifferential.D (ULift.{u + 1} Λ) _
              ((CommAlgCat.standardResolution.{u + 1, u + 1} (ULift.{u + 1} Λ)
                (liftedSectionsAlgebra Λ B hS X U)).left.map θ.op p))) :
            ULift.{u + 1} (resolutionChartDifferentials Λ B hS X hX U m)) =
        (liftedEtalePresheaf Λ B hS X hX).map
            (((standardResolutionChart Λ B hS X hX).obj U).map θ).op
            (chartSectionsUp Λ B hS X hX U n 1) ⊗ₜ[resolutionChartRing Λ B hS X hX U m]
          (ULift.up ((PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'
              (liftedBasePresheafMap Λ B hS X hX)).map
            (((standardResolutionChart Λ B hS X hX).obj U).map θ).op
            (resolutionToChartDifferentials Λ B hS X hX U n
              (KaehlerDifferential.D (ULift.{u + 1} Λ) _ p))) :
            ULift.{u + 1} (resolutionChartDifferentials Λ B hS X hX U m))
      rw [resolutionToChartDifferentials_D, resolutionToChartDifferentials_D, map_one, map_one,
        map_one]
      refine congrArg (fun m' => (1 : (liftedEtalePresheaf Λ B hS X hX).obj
        (op (resolutionChart Λ B hS X hX U m))) ⊗ₜ[resolutionChartRing Λ B hS X hX U m]
          (ULift.up m' : ULift.{u + 1} (resolutionChartDifferentials Λ B hS X hX U m))) ?_
      refine Eq.trans ?_
        (PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'_map_d
          _ _ _).symm
      refine congrArg CommRingCat.KaehlerDifferential.d ?_
      change (chartResolutionIso Λ B hS X hX U m).inv
          ((CommAlgCat.standardResolution.{u + 1, u + 1} (ULift.{u + 1} Λ)
            (liftedSectionsAlgebra Λ B hS X U)).left.map θ.op p) =
        (liftedAffinePresheaf Λ B hS X hX).map
          (((standardResolutionChart Λ B hS X hX).obj U).map θ).op
          ((chartResolutionIso Λ B hS X hX U n).inv p)
      rw [chartResolutionIso_inv_naturality])
  exact DFunLike.congr_fun key z

/-- In degree `-n`, the restriction map of `U ↦ L_{𝒪_X(U)/Λ}` over `V ⟶ U`, read through the
degree isomorphisms, is the map of cotangent terms of the restriction square. -/
theorem degreeIso_hom_squareCotangentComplexMap
    {U V : SmallEtale B (Spec (CommRingCat.of Λ)) hS X} (h : V ⟶ U) (n : ℕ)
    (y : (CommAlgCat.cotangentComplex.{u + 1, u + 1} (ULift.{u + 1} Λ)
      (liftedSectionsAlgebra Λ B hS X U)).X (-(n : ℤ))) :
    (CommAlgCat.cotangentComplex_degreeIso.{u + 1, u + 1} (ULift.{u + 1} Λ)
        (liftedSectionsAlgebra Λ B hS X V) n).hom
        ((CommAlgCat.squareCotangentComplexMap.{u + 1, u + 1, u + 1}
          (CommAlgCat.idSquare ((CommAlgCat.uliftBaseFunctor Λ).map
            (sectionsAlgebraRestrict Λ B hS X h)))).f (-(n : ℤ)) y) =
      CommAlgCat.squareCotangentTermMap.{u + 1, u + 1, u + 1}
        (CommAlgCat.idSquare ((CommAlgCat.uliftBaseFunctor Λ).map
          (sectionsAlgebraRestrict Λ B hS X h))) (op ⦋n⦌)
        ((CommAlgCat.cotangentComplex_degreeIso.{u + 1, u + 1} (ULift.{u + 1} Λ)
          (liftedSectionsAlgebra Λ B hS X U) n).hom y) := by
  rw [CommAlgCat.squareCotangentComplexMap_f]
  exact Iso.inv_hom_id_apply _ _

/-! ### The complexes of presheaves -/

/-- The complex of presheaves of modules `U ↦ (Ω_{𝒪/Λ̲} ⊗_𝒪 𝒪̲_X)(𝐀_{•,U})` on `X_étale` of the
proof of Tag 08VM, before reindexing: the Moore complex of the evaluation of the presheaf
`(U ⟶ A) ↦ 𝒪_X(U) ⊗_{Γ(A)} Ω_{Γ(A)/Λ}` on the cosimplicial charts of the standard resolutions. -/
abbrev chartBaseChangeMooreComplex :
    ChainComplex (PresheafOfModules.{u + 1}
      (ringSheaf (smallEtaleStructureSheafULift B (Spec (CommRingCat.of Λ)) hS ⟨X, hX⟩)).obj) ℕ :=
  (modulePointMooreComplex (fibredCategorySituation Λ B hS X hX)
    (standardResolutionChart_comp_whiskeringRight Λ B hS X hX)
    (ringSheaf (smallEtaleStructureSheafULift B (Spec (CommRingCat.of Λ)) hS ⟨X, hX⟩)).obj).obj
      (chartBaseChangePresheaf Λ B hS X hX)

/-- The simplicial presheaf of modules `U ↦ (Ω_{𝒪/Λ̲} ⊗_𝒪 𝒪̲_X)(𝐀_{•,U})` of the proof of
Tag 08VM. -/
abbrev chartBaseChangeSimplicial :
    SimplicialObject (PresheafOfModules.{u + 1}
      (ringSheaf (smallEtaleStructureSheafULift B (Spec (CommRingCat.of Λ)) hS ⟨X, hX⟩)).obj) :=
  (modulePointEvaluation (fibredCategorySituation Λ B hS X hX)
    (standardResolutionChart_comp_whiskeringRight Λ B hS X hX)
    (ringSheaf (smallEtaleStructureSheafULift B (Spec (CommRingCat.of Λ)) hS ⟨X, hX⟩)).obj).obj
      (chartBaseChangePresheaf Λ B hS X hX)

/-- The identification of the ring of the fibred category situation at a chart over `V` with the
ring at `V` is the identity on sections. -/
theorem pointRingMap_app_apply (V : SmallEtale B (Spec (CommRingCat.of Λ)) hS X)
    (n : SimplexCategory)
    (r : (ringSheaf (smallEtaleStructureSheafULift B (Spec (CommRingCat.of Λ)) hS
      ⟨X, hX⟩)).obj.obj (op V)) :
    (pointRingMap (fibredCategorySituation Λ B hS X hX)
      (standardResolutionChart_comp_whiskeringRight Λ B hS X hX)
      (ringSheaf (smallEtaleStructureSheafULift B (Spec (CommRingCat.of Λ)) hS
        ⟨X, hX⟩)).obj n).app (op V) r = r := by
  change (ringSheaf (smallEtaleStructureSheafULift B (Spec (CommRingCat.of Λ)) hS
    ⟨X, hX⟩)).obj.map (eqToHom (rfl : V = V)).op r = r
  rw [eqToHom_refl, op_id, CategoryTheory.Functor.map_id]
  rfl

/-- The component in degree `n` over `V` of the comparison: the sections over `V` of the degree
`-n` term of `U ↦ L_{𝒪_X(U)/Λ}` to those of `U ↦ (Ω_{𝒪/Λ̲} ⊗_𝒪 𝒪̲_X)(𝐀_{n,U})`. -/
def cotangentChartComponentLinearMap (V : SmallEtale B (Spec (CommRingCat.of Λ)) hS X) (n : ℕ) :
    ((chartSectionwiseCotangentComplex Λ B hS X hX).X (-(n : ℤ))).obj (op V) →ₗ[
      (ringSheaf (smallEtaleStructureSheafULift B (Spec (CommRingCat.of Λ)) hS
        ⟨X, hX⟩)).obj.obj (op V)]
      ((chartBaseChangeMooreComplex Λ B hS X hX).X n).obj (op V) where
  toFun x := cotangentToChart Λ B hS X hX V ⦋n⦌
    ((CommAlgCat.cotangentComplex_degreeIso.{u + 1, u + 1} (ULift.{u + 1} Λ)
      (liftedSectionsAlgebra Λ B hS X V) n).hom x)
  map_add' x y := (congrArg _ (map_add _ x y)).trans (map_add _ _ _)
  map_smul' r x := by
    refine (congrArg (cotangentToChart Λ B hS X hX V ⦋n⦌)
      ((CommAlgCat.cotangentComplex_degreeIso.{u + 1, u + 1} (ULift.{u + 1} Λ)
        (liftedSectionsAlgebra Λ B hS X V) n).hom.hom.map_smul r x)).trans ?_
    refine (cotangentToChart_smul Λ B hS X hX V ⦋n⦌ _ _).trans ?_
    change _ = (show (chartStructureRing Λ B hS X hX).obj.obj
      (op (resolutionChart Λ B hS X hX V ⦋n⦌)) from
        (pointRingMap (fibredCategorySituation Λ B hS X hX)
          (standardResolutionChart_comp_whiskeringRight Λ B hS X hX)
          (ringSheaf (smallEtaleStructureSheafULift B (Spec (CommRingCat.of Λ)) hS
            ⟨X, hX⟩)).obj ⦋n⦌).app (op V) r) •
      (show (chartBaseChangePresheaf Λ B hS X hX).obj
          (op (resolutionChart Λ B hS X hX V ⦋n⦌)) from
        cotangentToChart Λ B hS X hX V ⦋n⦌
          ((CommAlgCat.cotangentComplex_degreeIso.{u + 1, u + 1} (ULift.{u + 1} Λ)
            (liftedSectionsAlgebra Λ B hS X V) n).hom x))
    rw [pointRingMap_app_apply]
    rfl

/-- `cotangentChartComponentLinearMap` is bijective, with inverse `chartToCotangent` read through
the degree isomorphism of the cotangent complex. -/
theorem bijective_cotangentChartComponentLinearMap
    (V : SmallEtale B (Spec (CommRingCat.of Λ)) hS X) (n : ℕ) :
    Function.Bijective (cotangentChartComponentLinearMap Λ B hS X hX V n) := by
  refine Function.bijective_iff_has_inverse.mpr ⟨fun y =>
    (CommAlgCat.cotangentComplex_degreeIso.{u + 1, u + 1} (ULift.{u + 1} Λ)
      (liftedSectionsAlgebra Λ B hS X V) n).inv (chartToCotangent Λ B hS X hX V ⦋n⦌ y),
    fun x => ?_, fun y => ?_⟩
  · change (CommAlgCat.cotangentComplex_degreeIso.{u + 1, u + 1} (ULift.{u + 1} Λ) _ n).inv
      (chartToCotangent Λ B hS X hX V ⦋n⦌ (cotangentToChart Λ B hS X hX V ⦋n⦌
        ((CommAlgCat.cotangentComplex_degreeIso.{u + 1, u + 1} (ULift.{u + 1} Λ) _ n).hom x))) = x
    rw [chartToCotangent_cotangentToChart]
    exact Iso.hom_inv_id_apply _ _
  · change cotangentToChart Λ B hS X hX V ⦋n⦌
      ((CommAlgCat.cotangentComplex_degreeIso.{u + 1, u + 1} (ULift.{u + 1} Λ) _ n).hom
        ((CommAlgCat.cotangentComplex_degreeIso.{u + 1, u + 1} (ULift.{u + 1} Λ) _ n).inv
          (chartToCotangent Λ B hS X hX V ⦋n⦌ y))) = y
    rw [Iso.inv_hom_id_apply]
    exact cotangentToChart_chartToCotangent Λ B hS X hX V ⦋n⦌ y

/-- The component in degree `n` over `V` of the comparison, as an isomorphism of modules. -/
def cotangentChartComponentIso (V : SmallEtale B (Spec (CommRingCat.of Λ)) hS X) (n : ℕ) :
    ((chartSectionwiseCotangentComplex Λ B hS X hX).X (-(n : ℤ))).obj (op V) ≅
      ((chartBaseChangeMooreComplex Λ B hS X hX).X n).obj (op V) :=
  (LinearEquiv.ofBijective (cotangentChartComponentLinearMap Λ B hS X hX V n)
    (bijective_cotangentChartComponentLinearMap Λ B hS X hX V n)).toModuleIso

end AlgebraicGeometry.Space.PolynomialChart
