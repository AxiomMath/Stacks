module

public import StacksFrontier.Cotangent.BaseChangeComplexCounit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.SectionwiseHomology
public import StacksFrontier.Cotangent.SheavesOfRings.SectionwiseTowerSheafification
public import StacksFrontier.Cotangent.SheavesOfRings.SectionwiseRelativeBaseChange
import all StacksFrontier.Cotangent.Triangle.DisplayedTriangle

/-!
# The sectionwise fundamental triangle

Let `A ⟶ B ⟶ D` be homomorphisms of sheaves of commutative rings on a site such that `B(U) → D(U)`
is injective for every object `U`. Over every `U`, Remark 08SD and Remark 08SE of the Stacks
Project provide, for the ring maps `A(U) → B(U) → D(U)`, a short exact sequence
`0 → L_{B(U)/A(U)} ⊗ D(U) → L_{D(U)/A(U)} → Ω[Q̄_•(U)⁄B(U)] ⊗ D(U) → 0` and quasi-isomorphisms
`Ω[Q̄_•(U)⁄B(U)] ⊗ D(U) → Ω[R̄_•(U)⁄B(U)] ⊗ D(U) ← L_{D(U)/B(U)}`. This file records the
consequences for the complexes of presheaves of modules of
`StacksFrontier.Cotangent.SheavesOfRings.SectionwiseTower` and
`StacksFrontier.Cotangent.SheavesOfRings.SectionwiseRelativeBaseChange`.

## Main definitions

* `CategoryTheory.Sheaf.sectionwiseFundamentalShortComplex`: the sectionwise first map
  `U ↦ (L_{B(U)/A(U)} ⊗ D(U) ⟶ L_{D(U)/A(U)})` and its cokernel.
* `CategoryTheory.Sheaf.sectionwiseFundamentalCokernelMap`: the map from that cokernel to
  `U ↦ Ω[R̄_•(U)⁄B(U)] ⊗ D(U)`.

## Main results

* `CategoryTheory.Sheaf.mono_sectionwiseTowerBaseChangeComplexMap` and
  `CategoryTheory.Sheaf.sectionwiseFundamentalShortComplex_shortExact`: the sectionwise first map
  is a monomorphism, so with its cokernel it forms a short exact sequence.
* `CategoryTheory.Sheaf.quasiIso_evaluation_sectionwiseFundamentalCokernelMap` and
  `CategoryTheory.Sheaf.quasiIso_evaluation_sectionwiseRelativeBaseChangeLeg`: the cokernel map
  and the comparison `L_{D(U)/B(U)} ⟶ Ω[R̄_•(U)⁄B(U)] ⊗ D(U)` are quasi-isomorphisms over every
  `U`.
* `CategoryTheory.Sheaf.exists_distTriang_towerCotangent_of_injective`: **the distinguished
  triangle `L_{B/A} ⊗_B D ⟶ L_{D/A} ⟶ L_{D/B} ⟶ (L_{B/A} ⊗_B D)[1]` of Tag 08SZ** on the two
  canonical arrows, when every `B(U) → D(U)` is injective.

## References

* [Stacks Project, Tag 08SZ](https://stacks.math.columbia.edu/tag/08SZ)
* [Stacks Project, Tag 08SD](https://stacks.math.columbia.edu/tag/08SD)
* [Stacks Project, Tag 08SE](https://stacks.math.columbia.edu/tag/08SE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open scoped ChangeOfRings TensorProduct

universe u v w

namespace CommAlgCat

variable {A : Type u} [CommRing A] {B C : CommAlgCat.{u} A}

/-- The map `L_{B/A} ⊗_B C ⟶ L_{C/A}` of Tag 08QQ sends `1 ⊗ x` to the image of `x` under the
`B`-linear functoriality map of Tag 08PN. -/
theorem cotangentExtendScalarsComplexMap_one_tmul (f : B ⟶ C) (j : ℤ)
    (m : (cotangentComplex.{u, u} A B).X j) :
    (cotangentExtendScalarsComplexMap (A := A) (A' := A) (B := B) (B' := C) f.hom).f j
        ((1 : (C : Type u)) ⊗ₜ[(B : Type u), f.hom.toRingHom] m) =
      (squareCotangentComplexMap.{u, u, u} (idSquare f)).f j m :=
  (congrArg (fun φ : ((ModuleCat.extendScalars f.hom.toRingHom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (cotangentComplex.{u, u} A B) ⟶ cotangentComplex.{u, u} A C =>
      φ.f j ((1 : (C : Type u)) ⊗ₜ[(B : Type u), f.hom.toRingHom] m))
    (cotangentExtendScalarsComplexMap_eq_counit (A := A) (A' := A) (B := B) (B' := C)
      f.hom)).trans
    (ModuleCat.extendRestrictScalarsAdj_counit_app_apply_one_tmul _ _ _)

/-- The comparison `Ω[Q̄_•⁄B] ⊗ C ⟶ Ω[R̄_•⁄B] ⊗ C` of Remark 08SE, out of the third term of the
differential short exact sequence of Tag 08SD. -/
noncomputable def differentialSequenceThirdComparison (f : B ⟶ C) :
    (cotangentDifferentialComplexes.{u, u} A f).X₃ ⟶
      augmentedCotangentCochainComplex (R := (B : Type u)) (D := (relativeBaseChange f).right)
        (relativeBaseChange f).hom :=
  baseChangedCotangentComparison f

/-- The second map of the differential short exact sequence of Tag 08SD followed by the comparison
of Remark 08SE is the functoriality map of the change of base ring followed by the comparison
`L_{C/B} ⟶ Ω[R̄_•⁄B] ⊗ C`. -/
theorem cotangentDifferentialComplexes_g_comp_differentialSequenceThirdComparison
    (f : B ⟶ C) :
    (cotangentDifferentialComplexes.{u, u} A f).g ≫ differentialSequenceThirdComparison f =
      squareCotangentComplexMap.{u, u, u} (baseRingSquareTop f) ≫
        relativeBaseChangeCotangentLeg f :=
  (secondMap_comp_baseChangedCotangentComparison f).trans
    (congrArg (fun z => z ≫ relativeBaseChangeCotangentLeg f)
      (squareCotangentComplexMap_eq_map_cochain f))

/-- For `B → C` injective, the comparison `Ω[Q̄_•⁄B] ⊗ C ⟶ Ω[R̄_•⁄B] ⊗ C` of Remark 08SE is a
quasi-isomorphism. -/
theorem quasiIso_differentialSequenceThirdComparison (f : B ⟶ C)
    (hf : Function.Injective f.hom) : QuasiIso (differentialSequenceThirdComparison f) := by
  let := HasDerivedCategory.standard (ModuleCat.{u} (C : Type u))
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).1
    (isIso_q_baseChangedCotangentComparison f hf
      (trivialKanFibrations_baseChangedStandardResolution_of_injective f hf)
      (trivialKanFibrations_relativeBaseChange_of_injective f hf))

end CommAlgCat

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {A B D : Sheaf J CommRingCat.{max u v w}} (g : A ⟶ B) (h : B ⟶ D)

/-- Over every object `U` with `B(U) → D(U)` injective, the first arrow
`L_{D(U)/B(U)} ⟶ Ω[R̄_•(U)⁄B(U)] ⊗ D(U)` of the comparison of Remark 08SE is a
quasi-isomorphism. -/
theorem quasiIso_sectionsRelativeBaseChangeCotangentLeg (U : Cᵒᵖ)
    (hinj : Function.Injective (h.hom.app U).hom) :
    QuasiIso (sectionsRelativeBaseChangeCotangentLeg J g h U) := by
  let := HasDerivedCategory.standard (ModuleCat.{max u v w} (sectionsAlgebra J h U))
  rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
  exact CommAlgCat.isIso_q_relativeBaseChangeCotangentLeg (sectionsTowerHom J g h U) hinj
    (CommAlgCat.trivialKanFibrations_relativeBaseChange_of_injective _ hinj)

/-- **The comparison `L_{D(U)/B(U)} ⟶ Ω[R̄_•(U)⁄B(U)] ⊗ D(U)` is a quasi-isomorphism over every
`U`**, when every `B(U) → D(U)` is injective. -/
theorem quasiIso_evaluation_sectionwiseRelativeBaseChangeLeg
    (hinj : ∀ U, Function.Injective (h.hom.app U).hom) (U : Cᵒᵖ) :
    QuasiIso (((PresheafOfModules.evaluation _ U).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (sectionwiseRelativeBaseChangeLeg J g h)) :=
  quasiIso_sectionsRelativeBaseChangeCotangentLeg J g h U (hinj U)

/-- The differential short exact sequence of Tag 08SD for `A(U) → B(U) → D(U)`, read as a short
complex of complexes of modules over the sections of the ring sheaf of `D`. -/
noncomputable def sectionsDifferentialShortComplex (U : Cᵒᵖ) :
    ShortComplex (CochainComplex (ModuleCat.{max u v w}
      ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} D).obj.obj U)) ℤ) :=
  CommAlgCat.cotangentDifferentialComplexes.{max u v w, max u v w} (A.obj.obj U)
    (sectionsTowerHom J g h U)

/-- The differential sequence of Tag 08SD over `U` is short exact when `B(U) → D(U)` is
injective. -/
theorem sectionsDifferentialShortComplex_shortExact (U : Cᵒᵖ)
    (hinj : Function.Injective (h.hom.app U).hom) :
    (sectionsDifferentialShortComplex J g h U).ShortExact :=
  CommAlgCat.cotangentDifferentialComplexes_shortExact.{max u v w, max u v w} (A.obj.obj U)
    (sectionsTowerHom J g h U) hinj

/-- Over `U`, the sectionwise first vertex `U ↦ L_{B(U)/A(U)} ⊗_{B(U)} D(U)` is the first term of
the differential short exact sequence of Tag 08SD for `A(U) → B(U) → D(U)`. -/
noncomputable def sectionwiseBaseChangedCotangentComplexEvaluationIso (U : Cᵒᵖ) :
    ((PresheafOfModules.evaluation _ U).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (sectionwiseBaseChangedCotangentComplex J g h) ≅
      (sectionsDifferentialShortComplex J g h U).X₁ :=
  (CommAlgCat.cotangentDifferentialComplexesX₁Iso.{max u v w, max u v w} (A.obj.obj U)
    (sectionsTowerHom J g h U)).symm

/-- Over `U`, the sectionwise first map `L_{B(U)/A(U)} ⊗ D(U) ⟶ L_{D(U)/A(U)}` is the first map
of the differential short exact sequence of Tag 08SD for `A(U) → B(U) → D(U)`. -/
theorem evaluation_sectionwiseTowerBaseChangeComplexMap (U : Cᵒᵖ) :
    ((PresheafOfModules.evaluation _ U).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (sectionwiseTowerBaseChangeComplexMap J g h) =
      (sectionwiseBaseChangedCotangentComplexEvaluationIso J g h U).hom ≫
        (sectionsDifferentialShortComplex J g h U).f := by
  have k := (Iso.eq_inv_comp _).2
    (CommAlgCat.cotangentDifferentialComplexesX₁Iso_hom_comp (sectionsTowerHom J g h U))
  refine HomologicalComplex.hom_ext _ _ fun j => ?_
  by_cases hj : 0 < j
  · exact (CommAlgCat.cotangentComplex_isZero_pos.{max u v w, max u v w} (A.obj.obj U)
      (sectionsAlgebra J (g ≫ h) U) j hj).eq_of_tgt _ _
  · refine ModuleCat.ExtendScalars.hom_ext (f := (h.hom.app U).hom) fun m => ?_
    exact ((Stacks.PresheafOfModules.ChangeOfRings.counitApp_tmul h.hom
      ((sectionwiseTowerBaseChangeMap J g h).f j) U 1 m).trans (one_smul _ _)).trans
        ((CommAlgCat.cotangentExtendScalarsComplexMap_one_tmul (sectionsTowerHom J g h U) j
          m).symm.trans (ConcreteCategory.congr_hom (HomologicalComplex.congr_hom k j) _))

/-- **The sectionwise first map `L_{B(U)/A(U)} ⊗ D(U) ⟶ L_{D(U)/A(U)}` is a monomorphism of
complexes of presheaves of `D`-modules**, when every `B(U) → D(U)` is injective: over every `U` it
is the first map of the differential short exact sequence of Tag 08SD. -/
theorem mono_sectionwiseTowerBaseChangeComplexMap
    (hinj : ∀ U, Function.Injective (h.hom.app U).hom) :
    Mono (sectionwiseTowerBaseChangeComplexMap J g h) := by
  refine HomologicalComplex.mono_of_mono_f _ fun j =>
    PresheafOfModules.mono_of_injective fun ⦃U⦄ => ?_
  have hm : Mono (((PresheafOfModules.evaluation _ U).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (sectionwiseTowerBaseChangeComplexMap J g h)) := by
    rw [evaluation_sectionwiseTowerBaseChangeComplexMap]
    exact @mono_comp _ _ _ _ _ _ (@IsIso.mono_of_iso _ _ _ _ _
      (Iso.isIso_hom (sectionwiseBaseChangedCotangentComplexEvaluationIso J g h U))) _
      (sectionsDifferentialShortComplex_shortExact J g h U (hinj U)).mono_f
  exact (ModuleCat.mono_iff_injective _).1 (inferInstance : Mono
    ((((PresheafOfModules.evaluation _ U).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (sectionwiseTowerBaseChangeComplexMap J g h)).f j))

/-- Over `U`, the sectionwise complex `U ↦ L_{D(U)/A(U)}` is the middle term of the differential
short exact sequence of Tag 08SD for `A(U) → B(U) → D(U)`. -/
noncomputable def sectionwiseCotangentModuleComplexEvaluationIso (U : Cᵒᵖ) :
    ((PresheafOfModules.evaluation _ U).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (sectionwiseCotangentModuleComplex J (g ≫ h)) ≅
      (sectionsDifferentialShortComplex J g h U).X₂ :=
  Iso.refl _

/-- The comparison `Ω[Q̄_•(U)⁄B(U)] ⊗ D(U) ⟶ Ω[R̄_•(U)⁄B(U)] ⊗ D(U)` of Remark 08SE, with target
written as the complex of `CategoryTheory.Sheaf.relativeBaseChangeCotangentComplex`. -/
noncomputable def sectionsDifferentialSequenceThirdComparison (U : Cᵒᵖ) :
    (sectionsDifferentialShortComplex J g h U).X₃ ⟶ relativeBaseChangeCotangentComplex J g h U :=
  CommAlgCat.differentialSequenceThirdComparison (sectionsTowerHom J g h U)

/-- Over `U`, the sectionwise second map `L_{D(U)/A(U)} ⟶ L_{D(U)/B(U)}` followed by the comparison
`L_{D(U)/B(U)} ⟶ Ω[R̄_•(U)⁄B(U)] ⊗ D(U)` is the second map of the differential short exact
sequence of Tag 08SD followed by the comparison `Ω[Q̄_•(U)⁄B(U)] ⊗ D(U) ⟶ Ω[R̄_•(U)⁄B(U)] ⊗ D(U)`
of Remark 08SE. -/
theorem evaluation_sectionwiseTowerChangeOfBaseMap_comp_leg (U : Cᵒᵖ) :
    ((PresheafOfModules.evaluation _ U).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (sectionwiseTowerChangeOfBaseMap J g h ≫ sectionwiseRelativeBaseChangeLeg J g h) =
      (sectionwiseCotangentModuleComplexEvaluationIso J g h U).hom ≫
        (sectionsDifferentialShortComplex J g h U).g ≫
          sectionsDifferentialSequenceThirdComparison J g h U := by
  refine HomologicalComplex.hom_ext _ _ fun j => ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  exact (ConcreteCategory.congr_hom (HomologicalComplex.congr_hom
    (CommAlgCat.cotangentDifferentialComplexes_g_comp_differentialSequenceThirdComparison
      (sectionsTowerHom J g h U)) j) x).symm

/-- The sectionwise first map, the sectionwise second map and the comparison
`L_{D(U)/B(U)} ⟶ Ω[R̄_•(U)⁄B(U)] ⊗ D(U)` compose to zero. -/
theorem sectionwiseTowerBaseChangeComplexMap_comp_changeOfBase_comp_leg :
    sectionwiseTowerBaseChangeComplexMap J g h ≫ sectionwiseTowerChangeOfBaseMap J g h ≫
      sectionwiseRelativeBaseChangeLeg J g h = 0 := by
  refine HomologicalComplex.hom_ext _ _ fun j => PresheafOfModules.Hom.ext (funext fun U => ?_)
  have hU : ((PresheafOfModules.evaluation _ U).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (sectionwiseTowerBaseChangeComplexMap J g h ≫ sectionwiseTowerChangeOfBaseMap J g h ≫
        sectionwiseRelativeBaseChangeLeg J g h) = 0 := by
    refine ((Functor.map_comp _ _ _).trans (congrArg₂ (· ≫ ·)
      (evaluation_sectionwiseTowerBaseChangeComplexMap J g h U)
      (evaluation_sectionwiseTowerChangeOfBaseMap_comp_leg J g h U))).trans ?_
    refine (Category.assoc _ _ _).trans ((congrArg (fun z =>
      (sectionwiseBaseChangedCotangentComplexEvaluationIso J g h U).hom ≫ z)
        ((Category.assoc _ _ _).symm.trans ((congrArg (fun z => z ≫
          sectionsDifferentialSequenceThirdComparison J g h U)
          (sectionsDifferentialShortComplex J g h U).zero).trans zero_comp))).trans comp_zero)
  exact HomologicalComplex.congr_hom hU j

/-- The short complex of complexes of presheaves of `D`-modules
`U ↦ (L_{B(U)/A(U)} ⊗ D(U) ⟶ L_{D(U)/A(U)} ⟶ coker)` formed by the sectionwise first map and its
cokernel. -/
noncomputable def sectionwiseFundamentalShortComplex :
    ShortComplex (CochainComplex (PresheafOfModules.{max u v w}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} D).obj) ℤ) :=
  ShortComplex.mk (sectionwiseTowerBaseChangeComplexMap J g h)
    (cokernel.π (sectionwiseTowerBaseChangeComplexMap J g h)) (cokernel.condition _)

/-- The sectionwise first map and its cokernel form a short exact sequence, when every
`B(U) → D(U)` is injective. -/
theorem sectionwiseFundamentalShortComplex_shortExact
    (hinj : ∀ U, Function.Injective (h.hom.app U).hom) :
    (sectionwiseFundamentalShortComplex J g h).ShortExact :=
  have := mono_sectionwiseTowerBaseChangeComplexMap J g h hinj
  { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)
    mono_f := (inferInstance : Mono (sectionwiseTowerBaseChangeComplexMap J g h))
    epi_g := (inferInstance : Epi (cokernel.π (sectionwiseTowerBaseChangeComplexMap J g h))) }

/-- The map `coker (L_{B(U)/A(U)} ⊗ D(U) ⟶ L_{D(U)/A(U)}) ⟶ Ω[R̄_•(U)⁄B(U)] ⊗ D(U)` induced by the
sectionwise second map followed by the comparison of Remark 08SE. -/
noncomputable def sectionwiseFundamentalCokernelMap :
    (sectionwiseFundamentalShortComplex J g h).X₃ ⟶ sectionwiseRelativeBaseChangeComplex J g h :=
  cokernel.desc _ (sectionwiseTowerChangeOfBaseMap J g h ≫ sectionwiseRelativeBaseChangeLeg J g h)
    (sectionwiseTowerBaseChangeComplexMap_comp_changeOfBase_comp_leg J g h)

/-- The cokernel map composed with the projection is the sectionwise second map followed by the
comparison of Remark 08SE. -/
theorem sectionwiseFundamentalShortComplex_g_comp_cokernelMap :
    (sectionwiseFundamentalShortComplex J g h).g ≫ sectionwiseFundamentalCokernelMap J g h =
      sectionwiseTowerChangeOfBaseMap J g h ≫ sectionwiseRelativeBaseChangeLeg J g h :=
  cokernel.π_desc _ _ _

/-- **The cokernel map is a quasi-isomorphism over every object**, when every `B(U) → D(U)` is
injective: over `U` it is the identification of the cokernel with the third term of the
differential short exact sequence of Tag 08SD, followed by the quasi-isomorphism
`Ω[Q̄_•(U)⁄B(U)] ⊗ D(U) ⟶ Ω[R̄_•(U)⁄B(U)] ⊗ D(U)` of Remark 08SE. -/
theorem quasiIso_evaluation_sectionwiseFundamentalCokernelMap
    (hinj : ∀ U, Function.Injective (h.hom.app U).hom) (U : Cᵒᵖ) :
    QuasiIso (((PresheafOfModules.evaluation _ U).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (sectionwiseFundamentalCokernelMap J g h)) := by
  have hS := sectionwiseFundamentalShortComplex_shortExact J g h hinj
  have hSU : ((sectionwiseFundamentalShortComplex J g h).map
      ((PresheafOfModules.evaluation _ U).mapHomologicalComplex (ComplexShape.up ℤ))).ShortExact :=
    HomologicalComplex.shortExact_of_degreewise_shortExact _ fun j =>
      (((HomologicalComplex.shortExact_iff_degreewise_shortExact _).1 hS j).map_of_exact
        (PresheafOfModules.evaluation _ U))
  have hT := sectionsDifferentialShortComplex_shortExact J g h U (hinj U)
  have comm₁₂ : ((PresheafOfModules.evaluation _ U).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (sectionwiseTowerBaseChangeComplexMap J g h) ≫
        (sectionwiseCotangentModuleComplexEvaluationIso J g h U).hom =
      (sectionwiseBaseChangedCotangentComplexEvaluationIso J g h U).hom ≫
        (sectionsDifferentialShortComplex J g h U).f :=
    (Category.comp_id _).trans (evaluation_sectionwiseTowerBaseChangeComplexMap J g h U)
  have w : ((PresheafOfModules.evaluation _ U).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (sectionwiseTowerBaseChangeComplexMap J g h) ≫
        (sectionwiseCotangentModuleComplexEvaluationIso J g h U).hom ≫
          (sectionsDifferentialShortComplex J g h U).g = 0 :=
    (Category.assoc _ _ _).symm.trans ((congrArg (fun z => z ≫
      (sectionsDifferentialShortComplex J g h U).g) comm₁₂).trans ((Category.assoc _ _ _).trans
          ((congrArg (fun z => (sectionwiseBaseChangedCotangentComplexEvaluationIso J g h U).hom ≫
            z) (sectionsDifferentialShortComplex J g h U).zero).trans comp_zero)))
  let τ₃ := hSU.gIsCokernel.desc (CokernelCofork.ofπ _ w)
  have hτ₃ : ((sectionwiseFundamentalShortComplex J g h).map
      ((PresheafOfModules.evaluation _ U).mapHomologicalComplex (ComplexShape.up ℤ))).g ≫ τ₃ =
      (sectionwiseCotangentModuleComplexEvaluationIso J g h U).hom ≫
        (sectionsDifferentialShortComplex J g h U).g :=
    hSU.gIsCokernel.fac _ WalkingParallelPair.one
  let φ : (sectionwiseFundamentalShortComplex J g h).map
      ((PresheafOfModules.evaluation _ U).mapHomologicalComplex (ComplexShape.up ℤ)) ⟶
      sectionsDifferentialShortComplex J g h U :=
    { τ₁ := (sectionwiseBaseChangedCotangentComplexEvaluationIso J g h U).hom
      τ₂ := (sectionwiseCotangentModuleComplexEvaluationIso J g h U).hom
      τ₃ := τ₃
      comm₁₂ := comm₁₂.symm
      comm₂₃ := hτ₃.symm }
  have := hSU.epi_g
  have := hT.epi_g
  have : Epi φ.τ₁ := @IsIso.epi_of_iso _ _ _ _ _
    (Iso.isIso_hom (sectionwiseBaseChangedCotangentComplexEvaluationIso J g h U))
  have : IsIso φ.τ₂ := Iso.isIso_hom (sectionwiseCotangentModuleComplexEvaluationIso J g h U)
  have : IsIso φ.τ₃ :=
    Stacks.Cohomology.HypercohomologyEdge.isIso_τ₃_of_exact_of_epi φ hSU.exact hT.exact
  have : QuasiIso (sectionsDifferentialSequenceThirdComparison J g h U) :=
    CommAlgCat.quasiIso_differentialSequenceThirdComparison _ (hinj U)
  have hc : ((PresheafOfModules.evaluation _ U).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (sectionwiseFundamentalCokernelMap J g h) =
      τ₃ ≫ sectionsDifferentialSequenceThirdComparison J g h U := by
    refine (cancel_epi ((sectionwiseFundamentalShortComplex J g h).map
      ((PresheafOfModules.evaluation _ U).mapHomologicalComplex (ComplexShape.up ℤ))).g).1 ?_
    refine ((Functor.map_comp _ _ _).symm.trans ((congrArg _
      (sectionwiseFundamentalShortComplex_g_comp_cokernelMap J g h)).trans
        (evaluation_sectionwiseTowerChangeOfBaseMap_comp_leg J g h U))).trans ?_
    exact ((Category.assoc _ τ₃ (sectionsDifferentialSequenceThirdComparison J g h U)).symm.trans
      ((congrArg (fun z => z ≫ sectionsDifferentialSequenceThirdComparison J g h U) hτ₃).trans
        (Category.assoc (sectionwiseCotangentModuleComplexEvaluationIso J g h U).hom
          (sectionsDifferentialShortComplex J g h U).g
          (sectionsDifferentialSequenceThirdComparison J g h U)))).symm
  have : IsIso τ₃ := (inferInstance : IsIso φ.τ₃)
  rw [hc]
  exact quasiIso_comp τ₃ (sectionsDifferentialSequenceThirdComparison J g h U)

/-! ### Sheafification -/

/-- Sheafification of complexes of presheaves of modules over the ring sheaf of `X`. -/
noncomputable abbrev sheafifyTowerComplex (X : Sheaf J CommRingCat.{max u v w}) :
    CochainComplex (PresheafOfModules.{max u v w}
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} X).obj) ℤ ⥤
      CochainComplex (targetModules.{u, v, w} J X) ℤ :=
  (PresheafOfModules.sheafification.{max u v w}
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} X).obj)).mapHomologicalComplex
      (ComplexShape.up ℤ)

/-- The sheafified sectionwise short exact sequence is short exact. -/
theorem sectionwiseFundamentalShortComplex_map_sheafify_shortExact
    (hinj : ∀ U, Function.Injective (h.hom.app U).hom) :
    ((sectionwiseFundamentalShortComplex J g h).map (sheafifyTowerComplex J D)).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun j =>
    (((HomologicalComplex.shortExact_iff_degreewise_shortExact _).1
      (sectionwiseFundamentalShortComplex_shortExact J g h hinj) j).map_of_exact
        (PresheafOfModules.sheafification.{max u v w}
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} D).obj)))

/-- The sheafified cokernel map is a quasi-isomorphism. -/
theorem quasiIso_sheafify_sectionwiseFundamentalCokernelMap
    (hinj : ∀ U, Function.Injective (h.hom.app U).hom) :
    QuasiIso ((sheafifyTowerComplex J D).map (sectionwiseFundamentalCokernelMap J g h)) :=
  PresheafOfModules.quasiIso_sheafification_map_of_sectionwise _
    (quasiIso_evaluation_sectionwiseFundamentalCokernelMap J g h hinj)

/-- The sheafified comparison `L_{D/B} ⟶ (U ↦ Ω[R̄_•(U)⁄B(U)] ⊗ D(U))^#` is a quasi-isomorphism. -/
theorem quasiIso_sheafify_sectionwiseRelativeBaseChangeLeg
    (hinj : ∀ U, Function.Injective (h.hom.app U).hom) :
    QuasiIso ((sheafifyTowerComplex J D).map (sectionwiseRelativeBaseChangeLeg J g h)) :=
  PresheafOfModules.quasiIso_sheafification_map_of_sectionwise _
    (quasiIso_evaluation_sectionwiseRelativeBaseChangeLeg J g h hinj)

universe t in
/-- **The fundamental triangle of Tag 08SZ for a tower whose second map is injective on
sections.** Let `A ⟶ B ⟶ D` be homomorphisms of sheaves of commutative rings on a site such that
`B(U) → D(U)` is injective for every object `U`. Then there is a distinguished triangle

`L_{B/A} ⊗_B D ⟶ L_{D/A} ⟶ L_{D/B} ⟶ (L_{B/A} ⊗_B D)[1]`

in `D(D)` whose first two arrows are the canonical maps
`CategoryTheory.Sheaf.towerCotangentBaseChange` and
`CategoryTheory.Sheaf.towerCotangentChangeOfBase`.

This is the source's proof: over every `U` the differential short exact sequence of Tag 08SD for
`A(U) → B(U) → D(U)` and the quasi-isomorphisms of Tag 08SE are assembled into a short exact
sequence of complexes of presheaves of `D`-modules and a quasi-isomorphism from its cokernel term
to `U ↦ Ω[R̄_•(U)⁄B(U)] ⊗ D(U)`; sheafification is exact, and Tag 08SX identifies the
sheafified terms with the three vertices and the sheafified maps with the two arrows. -/
theorem exists_distTriang_towerCotangent_of_injective
    (hinj : ∀ U, Function.Injective (h.hom.app U).hom)
    [HasDerivedCategory.{t} (targetModules.{u, v, w} J D)] :
    ∃ δ : cotangentComplexDerived.{u, v, w, t} J h ⟶
        (DerivedCategory.Q.obj (baseChangedCotangentComplex.{u, v, w} J g h))⟦(1 : ℤ)⟧,
      Triangle.mk (DerivedCategory.Q.map (towerCotangentBaseChange.{u, v, w} J g h))
          (DerivedCategory.Q.map (towerCotangentChangeOfBase.{u, v, w} J g h)) δ ∈
        distTriang (DerivedCategory (targetModules.{u, v, w} J D)) := by
  have h₁ := sheafification_map_sectionwiseTowerBaseChangeComplexMap J g h
  have h₂ := sheafification_map_sectionwiseTowerChangeOfBaseMap J g h
  have := quasiIso_sheafify_sectionwiseFundamentalCokernelMap J g h hinj
  have := quasiIso_sheafify_sectionwiseRelativeBaseChangeLeg J g h hinj
  let d₃ : DerivedCategory.Q.obj ((sheafifyTowerComplex J D).obj
      (sectionwiseFundamentalShortComplex J g h).X₃) ≅
      DerivedCategory.Q.obj (cotangentComplex J h) :=
    asIso (DerivedCategory.Q.map ((sheafifyTowerComplex J D).map
      (sectionwiseFundamentalCokernelMap J g h))) ≪≫
    (asIso (DerivedCategory.Q.map ((sheafifyTowerComplex J D).map
      (sectionwiseRelativeBaseChangeLeg J g h)))).symm ≪≫
    DerivedCategory.Q.mapIso (sheafifiedSectionwiseCotangentModuleComplexIso J h)
  have key : ∀ {X Y Z : DerivedCategory (targetModules.{u, v, w} J D)}
      (T : Triangle (DerivedCategory (targetModules.{u, v, w} J D)))
      (_ : T ∈ distTriang (DerivedCategory (targetModules.{u, v, w} J D)))
      (d₁ : T.obj₁ ≅ X) (d₂ : T.obj₂ ≅ Y) (d₃ : T.obj₃ ≅ Z) (α : X ⟶ Y) (β : Y ⟶ Z),
      T.mor₁ = d₁.hom ≫ α ≫ d₂.inv → T.mor₂ = d₂.hom ≫ β ≫ d₃.inv →
      ∃ δ : Z ⟶ X⟦(1 : ℤ)⟧, Triangle.mk α β δ ∈
        distTriang (DerivedCategory (targetModules.{u, v, w} J D)) := by
    intro X Y Z T hT d₁ d₂ d₃ α β hα hβ
    exact ⟨d₃.inv ≫ T.mor₃ ≫ d₁.hom⟦(1 : ℤ)⟧', isomorphic_distinguished _ hT _
      (Triangle.isoMk _ _ d₁.symm d₂.symm d₃.symm (by simp [hα]) (by simp [hβ]) (by simp))⟩
  refine key _ (DerivedCategory.triangleOfSES_distinguished
      (sectionwiseFundamentalShortComplex_map_sheafify_shortExact J g h hinj))
    (DerivedCategory.Q.mapIso (sheafifiedSectionwiseBaseChangedCotangentComplexIso J g h))
    (DerivedCategory.Q.mapIso (sheafifiedSectionwiseCotangentModuleComplexIso J (g ≫ h))) d₃
    _ _ ?_ ?_
  · change DerivedCategory.Q.map ((sheafifyTowerComplex J D).map
      (sectionwiseTowerBaseChangeComplexMap J g h)) = _
    rw [h₁, Functor.map_comp, Functor.map_comp]
    rfl
  · change DerivedCategory.Q.map ((sheafifyTowerComplex J D).map
      (sectionwiseFundamentalShortComplex J g h).g) = _
    have hπ : (sheafifyTowerComplex J D).map (sectionwiseFundamentalShortComplex J g h).g ≫
          (sheafifyTowerComplex J D).map (sectionwiseFundamentalCokernelMap J g h) =
        (sheafifyTowerComplex J D).map (sectionwiseTowerChangeOfBaseMap J g h) ≫
          (sheafifyTowerComplex J D).map (sectionwiseRelativeBaseChangeLeg J g h) :=
      ((sheafifyTowerComplex J D).map_comp _ _).symm.trans
        ((congrArg (sheafifyTowerComplex J D).map
          (sectionwiseFundamentalShortComplex_g_comp_cokernelMap J g h)).trans
            ((sheafifyTowerComplex J D).map_comp _ _))
    have : IsIso (DerivedCategory.Q.map ((sheafifyTowerComplex J D).map
        (sectionwiseFundamentalCokernelMap J g h))) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
        (quasiIso_sheafify_sectionwiseFundamentalCokernelMap J g h hinj)
    have : Mono (DerivedCategory.Q.map ((sheafifyTowerComplex J D).map
        (sectionwiseFundamentalCokernelMap J g h))) := IsIso.mono_of_iso _
    refine (cancel_mono (DerivedCategory.Q.map ((sheafifyTowerComplex J D).map
      (sectionwiseFundamentalCokernelMap J g h)))).1 ?_
    refine ((DerivedCategory.Q.map_comp _ _).symm.trans ((congrArg DerivedCategory.Q.map hπ).trans
      ((DerivedCategory.Q.map_comp _ _).trans (congrArg (fun z => DerivedCategory.Q.map z ≫
        DerivedCategory.Q.map ((sheafifyTowerComplex J D).map
          (sectionwiseRelativeBaseChangeLeg J g h))) h₂)))).trans ?_
    have key : d₃.inv ≫ DerivedCategory.Q.map ((sheafifyTowerComplex J D).map
        (sectionwiseFundamentalCokernelMap J g h)) =
        DerivedCategory.Q.map (sheafifiedSectionwiseCotangentModuleComplexIso J h).inv ≫
          DerivedCategory.Q.map ((sheafifyTowerComplex J D).map
            (sectionwiseRelativeBaseChangeLeg J g h)) := by
      simp only [d₃, Iso.trans_inv, Iso.symm_inv, asIso_hom, asIso_inv, Functor.mapIso_inv,
        Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    exact (congrArg (fun z => z ≫ DerivedCategory.Q.map ((sheafifyTowerComplex J D).map
        (sectionwiseRelativeBaseChangeLeg J g h)))
      ((DerivedCategory.Q.map_comp _ _).trans (congrArg (fun z => DerivedCategory.Q.map
        (sheafifiedSectionwiseCotangentModuleComplexIso J (g ≫ h)).hom ≫ z)
          (DerivedCategory.Q.map_comp _ _)))).trans ((Category.assoc _ _ _).trans
      ((congrArg (fun z => DerivedCategory.Q.map
        (sheafifiedSectionwiseCotangentModuleComplexIso J (g ≫ h)).hom ≫ z)
          ((Category.assoc _ _ _).trans ((congrArg (fun z =>
            DerivedCategory.Q.map (towerCotangentChangeOfBase J g h) ≫ z) key.symm).trans
              (Category.assoc _ _ _).symm))).trans (Category.assoc _ _ _).symm))

end CategoryTheory.Sheaf

end
