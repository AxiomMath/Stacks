module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.PointResolution.ModuleBasic
public import StacksFrontier.Cotangent.ChartSiteLiftedModules
public import StacksFrontier.Cotangent.ChartSiteStandardResolutionComparison
public import StacksFrontier.Cotangent.SheavesOfRings.PolynomialChartFibreStandardResolution

/-!
# Naturality of the comparison on the charts of the standard resolutions

This file proves that the identification
`𝒪_X(U) ⊗_{Γ(A_{n,U})} Ω_{Γ(A_{n,U})/Λ} = L^{-n}_{𝒪_X(U)/Λ}` of
`StacksFrontier/Cotangent/ChartSiteStandardResolutionComparison.lean`, used in the proof of
Tag 08T9, is compatible with the cosimplicial structure of the charts `A_{•,U}` and with the maps
of charts `A_{n,V} ⟶ A_{n,U}` over inclusions `V ⊆ U`, and assembles it, in each degree, into an
isomorphism of presheaves of modules over the lifted structure sheaf of `X`.

## Main results

* `AlgebraicGeometry.PolynomialChart.cotangentToChart_squareCotangentTermMap`: naturality in the
  open.
* `AlgebraicGeometry.PolynomialChart.cotangentToChart_cotangentMap`: compatibility with the
  simplicial structure.
* `AlgebraicGeometry.PolynomialChart.cotangentChartComponentIso`: the comparison on the sections
  over an open, as an isomorphism of modules.

## References

* [Stacks Project, Tag 08T9](https://stacks.math.columbia.edu/tag/08T9)
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

/-! ### Naturality of the comparison -/

/-- `cotangentToChart` on a pure differential `1 ⊗ d q`. -/
theorem cotangentToChart_differential (U : X.Opens) (n : SimplexCategory)
    (q : resolutionTermAlgebra Λ X structureMap U n) :
    cotangentToChart Λ X structureMap U n
        (CommAlgCat.cotangentTermDifferential.{u, u} Λ (sectionCotangentAlgebra Λ X structureMap U)
          (op n) q) =
      letI := ((evaluation.{u, u + 1} Λ X structureMap).app
        (op (resolutionChart Λ X structureMap U n))).hom.toAlgebra
      ((1 : (zariskiPresheaf.{u, u + 1} Λ X structureMap).obj
          (op (resolutionChart Λ X structureMap U n))) ⊗ₜ[resolutionChartRing Λ X structureMap U n]
        (ULift.up (CommRingCat.KaehlerDifferential.d
          (resolutionToChartHom Λ X structureMap U n q)) :
          ULift.{u + 1} (resolutionChartDifferentials Λ X structureMap U n)) :
        TensorProduct (resolutionChartRing Λ X structureMap U n)
          ((zariskiPresheaf.{u, u + 1} Λ X structureMap).obj
            (op (resolutionChart Λ X structureMap U n)))
          (ULift.{u + 1} (resolutionChartDifferentials Λ X structureMap U n))) := by
  let := ((evaluation.{u, u + 1} Λ X structureMap).app
    (op (resolutionChart Λ X structureMap U n))).hom.toAlgebra
  show chartSectionsUp Λ X structureMap U n 1 ⊗ₜ[resolutionChartRing Λ X structureMap U n]
      (ULift.up (resolutionToChartDifferentials Λ X structureMap U n
        (KaehlerDifferential.D Λ _ q)) :
          ULift.{u + 1} (resolutionChartDifferentials Λ X structureMap U n)) = _
  rw [resolutionToChartDifferentials_D, map_one]

/-- Transporting a commuting square of ring maps along isomorphisms commutes with inverses. -/
private theorem comp_inv_apply_of_comp_hom_eq {A B C D : CommRingCat.{u}} (e₁ : A ≅ B)
    (e₂ : C ≅ D) (f : A ⟶ C) (g : B ⟶ D) (h : f ≫ e₂.hom = e₁.hom ≫ g) (q : B) :
    f (e₁.inv q) = e₂.inv (g q) := by
  have : e₁.inv ≫ f = g ≫ e₂.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  exact ConcreteCategory.congr_hom this q

/-- The inverse of `chartResolutionIso` is natural in the open. -/
theorem chartResolutionIso_inv_restriction {U V : X.Opens} (h : V ⟶ U) (n : SimplexCategory)
    (q : resolutionTermAlgebra Λ X structureMap U n) :
    Scheme.Γ.map (((standardResolutionChart Λ X structureMap).map h).app n).affine.op
        ((chartResolutionIso Λ X structureMap U n).inv q) =
      (chartResolutionIso Λ X structureMap V n).inv
        ((((CommAlgCat.standardResolutionFunctor.{u, u} Λ).map
          (sectionCotangentAlgebraMap Λ X structureMap h)).left.app (op n)) q) :=
  comp_inv_apply_of_comp_hom_eq _ _ _ _ (chartResolutionIso_hom_restriction Λ X structureMap h n) q

/-- The inverse of `chartResolutionIso` is compatible with the simplicial structure. -/
theorem chartResolutionIso_inv_naturality (U : X.Opens) {m n : SimplexCategory} (θ : m ⟶ n)
    (q : resolutionTermAlgebra Λ X structureMap U n) :
    Scheme.Γ.map (((standardResolutionChart Λ X structureMap).obj U).map θ).affine.op
        ((chartResolutionIso Λ X structureMap U n).inv q) =
      (chartResolutionIso Λ X structureMap U m).inv
        ((CommAlgCat.standardResolution.{u, u} Λ
          (sectionCotangentAlgebra Λ X structureMap U)).left.map θ.op q) :=
  comp_inv_apply_of_comp_hom_eq _ _ _ _ (chartResolutionIso_hom_naturality Λ X structureMap U θ) q

/-- A map of charts carries `cotangentToChart` of a pure differential `1 ⊗ d p` to that of
`1 ⊗ d q`, when `q` corresponds to `p` under the map of the rings of functions. -/
private theorem cotangentToChart_differential_map {U V : X.Opens} {m n : SimplexCategory}
    (f : resolutionChart Λ X structureMap V m ⟶ resolutionChart Λ X structureMap U n)
    (p : resolutionTermAlgebra Λ X structureMap U n)
    (q : resolutionTermAlgebra Λ X structureMap V m)
    (hq : (chartResolutionIso Λ X structureMap V m).inv q =
      Scheme.Γ.map f.affine.op ((chartResolutionIso Λ X structureMap U n).inv p)) :
    cotangentToChart Λ X structureMap V m (CommAlgCat.cotangentTermDifferential.{u, u} Λ
        (sectionCotangentAlgebra Λ X structureMap V) (op m) q) =
      (chartBaseChangePresheaf Λ X structureMap).map f.op (cotangentToChart Λ X structureMap U n
        (CommAlgCat.cotangentTermDifferential.{u, u} Λ
          (sectionCotangentAlgebra Λ X structureMap U) (op n) p)) := by
  rw [cotangentToChart_differential, cotangentToChart_differential]
  let := ((evaluation.{u, u + 1} Λ X structureMap).app
    (op (resolutionChart Λ X structureMap V m))).hom.toAlgebra
  change _ = (zariskiPresheaf.{u, u + 1} Λ X structureMap).map f.op 1 ⊗ₜ[resolutionChartRing Λ X
      structureMap V m]
    (ULift.up ((PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'
        (basePresheafMap.{u, u + 1} Λ X structureMap)).map f.op
        (CommRingCat.KaehlerDifferential.d (resolutionToChartHom Λ X structureMap U n p))) :
      ULift.{u + 1} (resolutionChartDifferentials Λ X structureMap V m))
  rw [map_one]
  refine congrArg (fun m' => 1 ⊗ₜ[resolutionChartRing Λ X structureMap V m] ULift.up m') ?_
  refine Eq.trans ?_
    (PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'_map_d _ _ _).symm
  exact congrArg CommRingCat.KaehlerDifferential.d (ULift.ext hq)

/-- The ring map `𝒪_X(U) → ULift 𝒪_X(V)` along which the restriction maps of both sides of the
comparison over `V ⊆ U` are semilinear. -/
def sectionRestrictionUp {U V : X.Opens} (h : V ⟶ U) (n : SimplexCategory) :
    sectionCotangentAlgebra Λ X structureMap U →+*
      (chartStructureRing Λ X structureMap).obj.obj
        (op (resolutionChart Λ X structureMap V n)) :=
  (chartScalarUp Λ X structureMap V n).comp (sectionCotangentAlgHom Λ X structureMap h).toRingHom

/-- **The comparison is natural in the open.** Over `V ⊆ U`, `cotangentToChart` intertwines the
restriction map of `U ↦ L^{-n}_{𝒪_X(U)/Λ}` with the restriction map of
`U ↦ (Ω_{𝒪/Λ̲} ⊗_𝒪 𝒪̲_X)(A_{n,U})` along the map of charts `A_{n,V} ⟶ A_{n,U}`. -/
theorem cotangentToChart_squareCotangentTermMap {U V : X.Opens} (h : V ⟶ U) (n : SimplexCategory)
    (z : CommAlgCat.cotangentTerm.{u, u} Λ (sectionCotangentAlgebra Λ X structureMap U) (op n)) :
    cotangentToChart Λ X structureMap V n
        ((CommAlgCat.squareCotangentTermMap.{u, u, u}
          (CommAlgCat.idSquare (sectionCotangentAlgebraMap Λ X structureMap h)) (op n)) z) =
      (chartBaseChangePresheaf Λ X structureMap).map
        (((standardResolutionChart Λ X structureMap).map h).app n).op
        (cotangentToChart Λ X structureMap U n z) := by
  have key := CommAlgCat.cotangentTerm_addMonoidHom_ext (op n)
    (R := (chartStructureRing Λ X structureMap).obj.obj
      (op (resolutionChart Λ X structureMap V n)))
    (N := (chartBaseChangePresheaf Λ X structureMap).obj
      (op (resolutionChart Λ X structureMap V n)))
    (sectionRestrictionUp Λ X structureMap h n)
    ((cotangentToChart Λ X structureMap V n).comp
      (CommAlgCat.squareCotangentTermMap.{u, u, u}
        (CommAlgCat.idSquare (sectionCotangentAlgebraMap Λ X structureMap h))
          (op n)).hom.toAddMonoidHom)
    (((chartBaseChangePresheaf Λ X structureMap).map
        (((standardResolutionChart Λ X structureMap).map h).app n).op).hom.toAddMonoidHom.comp
      (cotangentToChart Λ X structureMap U n))
    (fun b x => (congrArg (cotangentToChart Λ X structureMap V n)
      ((CommAlgCat.squareCotangentTermMap.{u, u, u} (CommAlgCat.idSquare
        (sectionCotangentAlgebraMap Λ X structureMap h)) (op n)).hom.map_smul b x)).trans
      (cotangentToChart_smul Λ X structureMap V n _ _))
    (fun b x => (congrArg ((chartBaseChangePresheaf Λ X structureMap).map
        (((standardResolutionChart Λ X structureMap).map h).app n).op).hom
        (cotangentToChart_smul Λ X structureMap U n b x)).trans
      (((chartBaseChangePresheaf Λ X structureMap).map
        (((standardResolutionChart Λ X structureMap).map h).app n).op).hom.map_smul _ _))
    (fun p => by
      change cotangentToChart Λ X structureMap V n (CommAlgCat.squareCotangentTermMap.{u, u, u}
        (CommAlgCat.idSquare (sectionCotangentAlgebraMap Λ X structureMap h)) (op n)
          (CommAlgCat.cotangentTermDifferential.{u, u} Λ _ (op n) p)) = _
      rw [CommAlgCat.squareCotangentTermMap_D]
      refine cotangentToChart_differential_map Λ X structureMap _ p _ ?_
      rw [chartResolutionIso_inv_restriction, CommAlgCat.standardResolutionSquareMap_idSquare]
      rfl)
  exact DFunLike.congr_fun key z


/-- The structure maps of the cosimplicial chart `A_{•,U}` lie over the identity of `U`, so the
restriction of lifted sections along them is the identity. -/
theorem chartStructureRing_map_chartScalarUp (U : X.Opens) {m n : SimplexCategory}
    (θ : m ⟶ n) (b : sectionCotangentAlgebra Λ X structureMap U) :
    (chartStructureRing Λ X structureMap).obj.map
        (((standardResolutionChart Λ X structureMap).obj U).map θ).op
        (chartScalarUp Λ X structureMap U n b) =
      chartScalarUp Λ X structureMap U m b := by
  show ULift.up ((X.presheaf.map (homOfLE (le_refl U)).op) b) = ULift.up b
  rw [Subsingleton.elim (homOfLE (le_refl U)) (𝟙 U), op_id, CategoryTheory.Functor.map_id]
  rfl

/-- **The comparison is compatible with the simplicial structure.** For `θ : [m] ⟶ [n]`,
`cotangentToChart` intertwines the simplicial structure map of the cotangent simplicial module of
`𝒪_X(U)` with the map induced by the cosimplicial structure map `A_{m,U} ⟶ A_{n,U}`. -/
theorem cotangentToChart_cotangentMap (U : X.Opens) {m n : SimplexCategory} (θ : m ⟶ n)
    (z : CommAlgCat.cotangentTerm.{u, u} Λ (sectionCotangentAlgebra Λ X structureMap U) (op n)) :
    cotangentToChart Λ X structureMap U m
        (CommAlgCat.cotangentMap.{u, u} Λ (sectionCotangentAlgebra Λ X structureMap U) θ.op z) =
      (chartBaseChangePresheaf Λ X structureMap).map
        (((standardResolutionChart Λ X structureMap).obj U).map θ).op
        (cotangentToChart Λ X structureMap U n z) := by
  have key := CommAlgCat.cotangentTerm_addMonoidHom_ext (op n)
    (R := (chartStructureRing Λ X structureMap).obj.obj
      (op (resolutionChart Λ X structureMap U m)))
    (N := (chartBaseChangePresheaf Λ X structureMap).obj
      (op (resolutionChart Λ X structureMap U m)))
    (chartScalarUp Λ X structureMap U m)
    ((cotangentToChart Λ X structureMap U m).comp
      (CommAlgCat.cotangentMap.{u, u} Λ (sectionCotangentAlgebra Λ X structureMap U)
        θ.op).hom.toAddMonoidHom)
    (((chartBaseChangePresheaf Λ X structureMap).map
        (((standardResolutionChart Λ X structureMap).obj U).map θ).op).hom.toAddMonoidHom.comp
      (cotangentToChart Λ X structureMap U n))
    (fun b x => (congrArg (cotangentToChart Λ X structureMap U m)
      ((CommAlgCat.cotangentMap.{u, u} Λ (sectionCotangentAlgebra Λ X structureMap U)
        θ.op).hom.map_smul b x)).trans
      (cotangentToChart_smul Λ X structureMap U m _ _))
    (fun b x => by
      refine (congrArg ((chartBaseChangePresheaf Λ X structureMap).map
        (((standardResolutionChart Λ X structureMap).obj U).map θ).op).hom
        (cotangentToChart_smul Λ X structureMap U n b x)).trans ?_
      refine (((chartBaseChangePresheaf Λ X structureMap).map
        (((standardResolutionChart Λ X structureMap).obj U).map θ).op).hom.map_smul _ _).trans ?_
      show (chartStructureRing Λ X structureMap).obj.map
          (((standardResolutionChart Λ X structureMap).obj U).map θ).op
          (chartScalarUp Λ X structureMap U n b) •
        (show (chartBaseChangePresheaf Λ X structureMap).obj
            (op (resolutionChart Λ X structureMap U m)) from
          (chartBaseChangePresheaf Λ X structureMap).map
            (((standardResolutionChart Λ X structureMap).obj U).map θ).op
            (cotangentToChart Λ X structureMap U n x)) = _
      rw [chartStructureRing_map_chartScalarUp]
      rfl)
    (fun p => by
      change cotangentToChart Λ X structureMap U m (CommAlgCat.cotangentMap.{u, u} Λ
        (sectionCotangentAlgebra Λ X structureMap U) θ.op
          (CommAlgCat.cotangentTermDifferential.{u, u} Λ _ (op n) p)) = _
      rw [CommAlgCat.cotangentMap_D]
      exact cotangentToChart_differential_map Λ X structureMap _ p _
        (chartResolutionIso_inv_naturality Λ X structureMap U θ p).symm)
  exact DFunLike.congr_fun key z


/-- In degree `-n`, the restriction map of `U ↦ L_{𝒪_X(U)/Λ}` over `V ⊆ U`, read through the degree
isomorphisms, is the map of cotangent terms of the restriction square. -/
theorem degreeIso_hom_squareCotangentComplexMap {U V : X.Opens} (h : V ⟶ U) (n : ℕ)
    (y : (CommAlgCat.cotangentComplex.{u, u} Λ (sectionCotangentAlgebra Λ X structureMap U)).X
      (-(n : ℤ))) :
    (CommAlgCat.cotangentComplex_degreeIso.{u, u} Λ (sectionCotangentAlgebra Λ X structureMap V)
        n).hom ((CommAlgCat.squareCotangentComplexMap.{u, u, u}
          (CommAlgCat.idSquare (sectionCotangentAlgebraMap Λ X structureMap h))).f (-(n : ℤ)) y) =
      CommAlgCat.squareCotangentTermMap.{u, u, u}
        (CommAlgCat.idSquare (sectionCotangentAlgebraMap Λ X structureMap h)) (op ⦋n⦌)
        ((CommAlgCat.cotangentComplex_degreeIso.{u, u} Λ
          (sectionCotangentAlgebra Λ X structureMap U)
          n).hom y) := by
  rw [CommAlgCat.squareCotangentComplexMap_f]
  exact Iso.inv_hom_id_apply _ _

/-- In degree `-(n + 1)`, the differential of the cotangent complex, read through the degree
isomorphisms, is the alternating sum of the faces of the cotangent simplicial module. -/
theorem degreeIso_hom_cotangentComplex_d (B : CommAlgCat.{u} Λ) (n : ℕ)
    (y : (CommAlgCat.cotangentComplex.{u, u} Λ B).X (-(n + 1 : ℕ) : ℤ)) :
    (CommAlgCat.cotangentComplex_degreeIso.{u, u} Λ B n).hom
        ((CommAlgCat.cotangentComplex.{u, u} Λ B).d (-(n + 1 : ℕ) : ℤ) (-(n : ℤ)) y) =
      AlgebraicTopology.AlternatingFaceMapComplex.objD
        (CommAlgCat.cotangentSimplicialModule.{u, u} Λ B).object n
        ((CommAlgCat.cotangentComplex_degreeIso.{u, u} Λ B (n + 1)).hom y) := by
  rw [CommAlgCat.cotangentComplex_d]
  exact Iso.inv_hom_id_apply _ _


/-! ### The complexes of presheaves -/

/-- The complex of presheaves of `𝒪_X`-modules `U ↦ (Ω_{𝒪/Λ̲} ⊗_𝒪 𝒪̲_X)(A_{•,U})` of the proof of
Tag 08T9, before reindexing: the Moore complex of the evaluation of the presheaf
`(U ⟶ A) ↦ 𝒪_X(U) ⊗_{Γ(A)} Ω_{Γ(A)/Λ}` on the cosimplicial charts of the standard resolutions. -/
abbrev chartBaseChangeMooreComplex :
    ChainComplex (PresheafOfModules.{u + 1} (ringSheaf (liftedStructureSheaf.{u, u} X)).obj) ℕ :=
  (modulePointMooreComplex (fibredCategorySituation Λ X structureMap)
    (standardResolutionChart_comp_whiskeringRight Λ X structureMap)
    (ringSheaf (liftedStructureSheaf.{u, u} X)).obj).obj (chartBaseChangePresheaf Λ X structureMap)

/-- The simplicial presheaf of `𝒪_X`-modules `U ↦ (Ω_{𝒪/Λ̲} ⊗_𝒪 𝒪̲_X)(A_{•,U})` of the proof of
Tag 08T9. -/
abbrev chartBaseChangeSimplicial :
    SimplicialObject (PresheafOfModules.{u + 1} (ringSheaf (liftedStructureSheaf.{u, u} X)).obj) :=
  (modulePointEvaluation (fibredCategorySituation Λ X structureMap)
    (standardResolutionChart_comp_whiskeringRight Λ X structureMap)
    (ringSheaf (liftedStructureSheaf.{u, u} X)).obj).obj (chartBaseChangePresheaf Λ X structureMap)

/-- The complex of presheaves `U ↦ L_{𝒪_X(U)/Λ}`, presented over the lifted structure sheaf. -/
abbrev liftedSectionwiseCotangentComplex :
    CochainComplex (PresheafOfModules.{u + 1} (ringSheaf (liftedStructureSheaf.{u, u} X)).obj) ℤ :=
  ((liftStructurePresheafModules.{u, u} X).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (SchemeOverRing.sectionwiseCotangentComplexConstant Λ structureMap)

/-- The identification of the ring of the fibred category situation at a chart over `V` with the
ring at `V` is the identity on sections. -/
theorem pointRingMap_app_apply (V : X.Opens) (n : SimplexCategory)
    (r : (ringSheaf (liftedStructureSheaf.{u, u} X)).obj.obj (op V)) :
    (pointRingMap (fibredCategorySituation Λ X structureMap)
      (standardResolutionChart_comp_whiskeringRight Λ X structureMap)
      (ringSheaf (liftedStructureSheaf.{u, u} X)).obj n).app (op V) r = r := by
  show (ringSheaf (liftedStructureSheaf.{u, u} X)).obj.map (eqToHom (rfl : V = V)).op r = r
  rw [eqToHom_refl, op_id, CategoryTheory.Functor.map_id]
  rfl

/-- The component in degree `n` over `V` of the comparison: the sections over `V` of the degree
`-n` term of `U ↦ L_{𝒪_X(U)/Λ}` to those of `U ↦ (Ω_{𝒪/Λ̲} ⊗_𝒪 𝒪̲_X)(A_{n,U})`. -/
def cotangentChartComponentLinearMap (V : X.Opens) (n : ℕ) :
    ((liftedSectionwiseCotangentComplex Λ X structureMap).X (-(n : ℤ))).obj (op V) →ₗ[
      (ringSheaf (liftedStructureSheaf.{u, u} X)).obj.obj (op V)]
      ((chartBaseChangeMooreComplex Λ X structureMap).X n).obj (op V) where
  toFun x := cotangentToChart Λ X structureMap V ⦋n⦌
    ((CommAlgCat.cotangentComplex_degreeIso.{u, u} Λ (sectionCotangentAlgebra Λ X structureMap V)
      n).hom x.down)
  map_add' x y := (congrArg _ (map_add _ x.down y.down)).trans (map_add _ _ _)
  map_smul' r x := by
    refine (congrArg (cotangentToChart Λ X structureMap V ⦋n⦌)
      ((CommAlgCat.cotangentComplex_degreeIso.{u, u} Λ (sectionCotangentAlgebra Λ X structureMap V)
        n).hom.hom.map_smul r.down x.down)).trans ?_
    refine (cotangentToChart_smul Λ X structureMap V ⦋n⦌ _ _).trans ?_
    change _ = (show (chartStructureRing Λ X structureMap).obj.obj
      (op (resolutionChart Λ X structureMap V ⦋n⦌)) from
        (pointRingMap (fibredCategorySituation Λ X structureMap)
          (standardResolutionChart_comp_whiskeringRight Λ X structureMap)
          (ringSheaf (liftedStructureSheaf.{u, u} X)).obj ⦋n⦌).app (op V) r) •
      (show (chartBaseChangePresheaf Λ X structureMap).obj
          (op (resolutionChart Λ X structureMap V ⦋n⦌)) from
        cotangentToChart Λ X structureMap V ⦋n⦌
          ((CommAlgCat.cotangentComplex_degreeIso.{u, u} Λ
            (sectionCotangentAlgebra Λ X structureMap V) n).hom x.down))
    rw [pointRingMap_app_apply]
    rfl


/-- `cotangentChartComponentLinearMap` is bijective, with inverse `chartToCotangent` read through
the degree isomorphism of the cotangent complex. -/
theorem bijective_cotangentChartComponentLinearMap (V : X.Opens) (n : ℕ) :
    Function.Bijective (cotangentChartComponentLinearMap Λ X structureMap V n) := by
  refine Function.bijective_iff_has_inverse.mpr ⟨fun y => ULift.up
    ((CommAlgCat.cotangentComplex_degreeIso.{u, u} Λ (sectionCotangentAlgebra Λ X structureMap V)
      n).inv (chartToCotangent Λ X structureMap V ⦋n⦌ y)), fun x => ?_, fun y => ?_⟩
  · refine ULift.ext ?_
    show (CommAlgCat.cotangentComplex_degreeIso.{u, u} Λ _ n).inv
      (chartToCotangent Λ X structureMap V ⦋n⦌ (cotangentToChart Λ X structureMap V ⦋n⦌
        ((CommAlgCat.cotangentComplex_degreeIso.{u, u} Λ _ n).hom x.down))) = x.down
    rw [chartToCotangent_cotangentToChart]
    exact Iso.hom_inv_id_apply _ _
  · show cotangentToChart Λ X structureMap V ⦋n⦌
      ((CommAlgCat.cotangentComplex_degreeIso.{u, u} Λ _ n).hom
        ((CommAlgCat.cotangentComplex_degreeIso.{u, u} Λ _ n).inv
          (chartToCotangent Λ X structureMap V ⦋n⦌ y))) = y
    rw [Iso.inv_hom_id_apply]
    exact cotangentToChart_chartToCotangent Λ X structureMap V ⦋n⦌ y

/-- The component in degree `n` over `V` of the comparison, as an isomorphism of modules. -/
def cotangentChartComponentIso (V : X.Opens) (n : ℕ) :
    ((liftedSectionwiseCotangentComplex Λ X structureMap).X (-(n : ℤ))).obj (op V) ≅
      ((chartBaseChangeMooreComplex Λ X structureMap).X n).obj (op V) :=
  (LinearEquiv.ofBijective (cotangentChartComponentLinearMap Λ X structureMap V n)
    (bijective_cotangentChartComponentLinearMap Λ X structureMap V n)).toModuleIso


end AlgebraicGeometry.PolynomialChart
