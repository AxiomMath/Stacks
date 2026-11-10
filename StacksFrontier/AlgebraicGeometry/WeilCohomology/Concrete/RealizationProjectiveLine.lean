module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ProjectiveLineCohomology
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ProjectiveLineSummands
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.RationalPointSummands
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.RealizationFunctor
public import StacksFrontier.CategoryTheory.GradedObject.InvertibleLine
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition

/-!
# The realization of the Lefschetz motive is invertible

Let `W` be data (D0)–(D3) of Section 45.9 (Tag 0FHA) satisfying (A), (B) and (C), with coefficient
field of characteristic zero, and let `G` be the functor of the proof of Stacks 0FHL on
correspondences of degree zero (`Stacks.WeilCohomology.WeilData.corrFunctor`). The last step of the
proof of Stacks 0FHL: the image of `G(c₂)` on `G(P¹_k) = H^*(P¹_k)` is an invertible graded vector
space. By Stacks 0FHI, `H^*(P¹_k)` is one dimensional in degrees `0` and `2` and zero otherwise;
`c₀ = a ∘ b` with `b ∘ a = 1` (proof of Stacks 0FGD), so `G(c₀)` is a projector whose image is
`G(Spec k) = F` in degree `0` (Stacks 0FHE); `1 = c₀ + c₂` (Example 0FG6), so `G(c₂)` is the
projector onto `H^2(P¹_k)`, a line in degree `2`, which is invertible.

## Main results

* `WeilData.exists_isInvertible_image_corrFunctor_map_projectiveLineFibrePoint`:
  `G(c₂)` splits through an invertible graded vector space.

## References

* [Stacks Project, Tag 0FHL](https://stacks.math.columbia.edu/tag/0FHL)
* [Stacks Project, Tag 0FHI](https://stacks.math.columbia.edu/tag/0FHI)
* [Stacks Project, Tag 0FG6](https://stacks.math.columbia.edu/tag/0FG6)
* [Stacks Project, Tag 0FGD](https://stacks.math.columbia.edu/tag/0FGD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Chow MonoidalCategory

universe u w

namespace Stacks.WeilCohomology.WeilData

open SmoothProjectiveScheme

variable {k : Type u} [Field k] {F : Type w} [Field F] [CharZero F] {W : WeilData k F}
  (hA : W.PoincareDuality) (hB : W.Kunneth) (hC : W.CycleClassAxiom hA.perfectPairing)

variable
  (x : (fieldChowSituation k).S ⟶ Stacks.Chow.relativeProjectiveLine (Spec (CommRingCat.of k)))
  (hx : x ≫ (Stacks.Chow.relativeProjectiveLine (Spec (CommRingCat.of k)) ↘
      Spec (CommRingCat.of k)) = 𝟙 (fieldChowSituation k).S)

/-- `Spec k` as an object of the category of correspondences of degree zero. -/
abbrev pointDegreeZero (k : Type u) [Field k] :
    GradedCategory.DegreeZero ℚ (CorrespondenceCategory k) :=
  GradedCompositionData.Obj.mk (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory))

/-- `b = [Γ_x] : P¹_k ⟶ Spec k`, the graph of the rational point. -/
def projectiveLinePointGraph :
    ChowMotiveCat.projectiveLineDegreeZero k ⟶ pointDegreeZero k :=
  GradedCategory.DegreeZero.homMk
    ((canonicalGraphFunctor k).map (ChowMotiveCat.projectiveLinePoint x hx).op)
    (graphHom_mem_grade _)

/-- `a = [Γ_{P¹ → Spec k}] : Spec k ⟶ P¹_k`, the graph of the structure morphism. -/
def projectiveLineStructureGraph (k : Type u) [Field k] :
    pointDegreeZero k ⟶ ChowMotiveCat.projectiveLineDegreeZero k :=
  GradedCategory.DegreeZero.homMk
    ((canonicalGraphFunctor k).map (ChowMotiveCat.toTensorUnit (projectiveLineObj k)).op)
    (graphHom_mem_grade _)

/-- `c₀ = [x × P¹]`, the graph of the constant morphism `P¹_k → x → P¹_k`, as an endomorphism of
`P¹_k` of degree zero. -/
def projectiveLinePointFibreDegreeZero :
    ChowMotiveCat.projectiveLineDegreeZero k ⟶ ChowMotiveCat.projectiveLineDegreeZero k :=
  GradedCategory.DegreeZero.homMk ((canonicalGraphFunctor k).map
      (ChowMotiveCat.toTensorUnit (projectiveLineObj k) ≫
        ChowMotiveCat.projectiveLinePoint x hx).op)
    (graphHom_mem_grade _)

/-- `b ∘ a = 1` (proof of Stacks 0FGD). -/
theorem projectiveLineStructureGraph_comp_pointGraph :
    projectiveLineStructureGraph k ≫ projectiveLinePointGraph x hx = 𝟙 (pointDegreeZero k) := by
  apply GradedCategory.DegreeZero.hom_ext
  rw [GradedCategory.DegreeZero.comp_val, GradedCategory.DegreeZero.id_val]
  change (canonicalGraphFunctor k).map _ ≫ (canonicalGraphFunctor k).map _ = _
  rw [← Functor.map_comp, ← op_comp, ChowMotiveCat.comp_toTensorUnit, op_id,
    CategoryTheory.Functor.map_id]
  rfl

/-- `a ∘ b = c₀` (proof of Stacks 0FGD). -/
theorem projectiveLinePointGraph_comp_structureGraph :
    projectiveLinePointGraph x hx ≫ projectiveLineStructureGraph k =
      projectiveLinePointFibreDegreeZero x hx := by
  apply GradedCategory.DegreeZero.hom_ext
  rw [GradedCategory.DegreeZero.comp_val]
  change (canonicalGraphFunctor k).map _ ≫ (canonicalGraphFunctor k).map _ = _
  rw [← Functor.map_comp, ← op_comp]
  rfl

/-- `1 = c₀ + c₂` (Example 0FG6). -/
theorem projectiveLinePointFibre_add_fibrePoint :
    projectiveLinePointFibreDegreeZero x hx +
        ChowMotiveCat.projectiveLineFibrePointDegreeZero x hx =
      𝟙 (ChowMotiveCat.projectiveLineDegreeZero k) := by
  apply GradedCategory.DegreeZero.hom_ext
  rw [GradedCategory.DegreeZero.add_val, GradedCategory.DegreeZero.id_val]
  have h₀ : GradedCategory.DegreeZero.val (projectiveLinePointFibreDegreeZero x hx) =
      projectiveLinePointFibreHom x hx := by
    rw [projectiveLinePointFibreHom,
      ChowMotiveCat.projectiveLinePointFibreCorr_eq_constantGraphCorr]
    rfl
  rw [h₀]
  exact (projectiveLine_id_eq_add x hx).symm

/-- `G(c₂) = 1 - G(b) ≫ G(a)`. -/
theorem corrFunctor_map_fibrePoint :
    (corrFunctor hA hB hC).map (ChowMotiveCat.projectiveLineFibrePointDegreeZero x hx) =
      𝟙 _ - (corrFunctor hA hB hC).map (projectiveLinePointGraph x hx) ≫
        (corrFunctor hA hB hC).map (projectiveLineStructureGraph k) := by
  have h := congrArg (corrFunctor hA hB hC).map (projectiveLinePointFibre_add_fibrePoint x hx)
  rw [Functor.map_add, CategoryTheory.Functor.map_id,
    ← projectiveLinePointGraph_comp_structureGraph,
    Functor.map_comp] at h
  exact eq_sub_of_add_eq' h

/-- The restriction `G(b) : H^n(P¹_k) → H^n(Spec k)`. -/
abbrev pointRestrict (n : ℤ) :
    W.grade (projectiveLineObj k) n →ₗ[F]
      W.grade (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)) n :=
  ((corrFunctor hA hB hC).map (projectiveLinePointGraph x hx) n).hom

/-- The map `G(a) : H^n(Spec k) → H^n(P¹_k)`. -/
abbrev structureInclude (n : ℤ) :
    W.grade (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)) n →ₗ[F]
      W.grade (projectiveLineObj k) n :=
  ((corrFunctor hA hB hC).map (projectiveLineStructureGraph k) n).hom

/-- The map `G(c₂) : H^n(P¹_k) → H^n(P¹_k)`. -/
abbrev fibrePointMap (n : ℤ) :
    W.grade (projectiveLineObj k) n →ₗ[F] W.grade (projectiveLineObj k) n :=
  ((corrFunctor hA hB hC).map (ChowMotiveCat.projectiveLineFibrePointDegreeZero x hx) n).hom

/-- `G(b) ∘ G(a) = 1` degreewise. -/
theorem pointRestrict_comp_structure (n : ℤ)
    (v : W.grade (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)) n) :
    pointRestrict hA hB hC x hx n (structureInclude hA hB hC n v) = v := by
  have h := congrArg (fun φ ↦ ((φ : _ ⟶ _) n).hom v)
    (((corrFunctor hA hB hC).map_comp (projectiveLineStructureGraph k)
      (projectiveLinePointGraph x hx)).symm.trans
      ((congrArg (corrFunctor hA hB hC).map
        (projectiveLineStructureGraph_comp_pointGraph x hx)).trans
        ((corrFunctor hA hB hC).map_id _)))
  exact h

/-- `G(c₂) = 1 - G(a) ∘ G(b)` degreewise. -/
theorem fibrePointMap_apply (n : ℤ) (v : W.grade (projectiveLineObj k) n) :
    fibrePointMap hA hB hC x hx n v =
      v - structureInclude hA hB hC n (pointRestrict hA hB hC x hx n v) := by
  have h := congrArg (fun φ ↦ ((φ : _ ⟶ _) n).hom v) (corrFunctor_map_fibrePoint hA hB hC x hx)
  exact h

/-- `G(c₂)` lands in the kernel of `G(b)`. -/
theorem pointRestrict_fibrePoint (n : ℤ) (v : W.grade (projectiveLineObj k) n) :
    pointRestrict hA hB hC x hx n (fibrePointMap hA hB hC x hx n v) = 0 := by
  rw [fibrePointMap_apply, map_sub, pointRestrict_comp_structure, sub_self]

/-- `G(c₂)` fixes the kernel of `G(b)`. -/
theorem fibrePoint_apply_of_mem_ker (n : ℤ) (v : W.grade (projectiveLineObj k) n)
    (hv : pointRestrict hA hB hC x hx n v = 0) : fibrePointMap hA hB hC x hx n v = v := by
  rw [fibrePointMap_apply, hv, map_zero, sub_zero]

/-- The image of `G(c₂)`: the kernel of `G(b)`, degree by degree. -/
abbrev fibrePointImage : GradedObject ℤ (ModuleCat.{w} F) :=
  fun n ↦ ModuleCat.of F (LinearMap.ker (pointRestrict hA hB hC x hx n))

/-- In degree `2` the kernel of `G(b)` is all of `H^2(P¹_k)`, a line; in every other degree it
vanishes: `H^n(P¹_k) = 0` for `n ≠ 0, 2` (Stacks 0FHI), and in degree `0` the surjection
`G(b) : H^0(P¹_k) → H^0(Spec k)` from a line to a nonzero space is injective. -/
theorem fibrePointImage_finrank_and_isZero :
    Module.finrank F (fibrePointImage hA hB hC x hx 2) = 1 ∧
      ∀ m, m ≠ 2 → IsZero (fibrePointImage hA hB hC x hx m) := by
  obtain ⟨h0, h2, hbot⟩ := cohomology_projectiveLineObj hA hB hC (k := k)
  have hpt : ∀ i : ℤ, i ≠ 0 → W.grade (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)) i = ⊥ :=
    fun i hi ↦ grade_point_eq_bot hB.kunnethIsomorphism hC.point hi
  refine ⟨?_, fun m hm ↦ ?_⟩
  · have hz : pointRestrict hA hB hC x hx 2 = 0 := by
      have := Submodule.subsingleton_iff_eq_bot.2 (hpt 2 (by norm_num))
      exact LinearMap.ext fun v ↦ Subsingleton.elim _ _
    change Module.finrank F (LinearMap.ker (pointRestrict hA hB hC x hx 2)) = 1
    rw [hz, LinearMap.ker_zero, finrank_top, h2]
  · suffices Subsingleton (LinearMap.ker (pointRestrict hA hB hC x hx m)) from
      ModuleCat.isZero_of_subsingleton
        (ModuleCat.of F (LinearMap.ker (pointRestrict hA hB hC x hx m)))
    by_cases hm0 : m = 0
    · subst hm0
      have hP := isNonemptyEquidimensional_projectiveLineObj k
      have := hA.finiteDimensionality _ 1 hP 0
      have hsurj : Function.Surjective (pointRestrict hA hB hC x hx 0) := fun v ↦
        ⟨_, pointRestrict_comp_structure hA hB hC x hx 0 v⟩
      have : Nontrivial (W.H (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory))) :=
        nontrivial_point (W := W) hC.point
      have hne : (⟨1, SetLike.GradedOne.one_mem⟩ :
          W.grade (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)) 0) ≠ 0 :=
        fun h ↦ one_ne_zero (congrArg Subtype.val h)
      have : Nontrivial (W.grade (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)) 0) :=
        ⟨⟨_, _, hne⟩⟩
      have : FiniteDimensional F (W.grade (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)) 0) :=
        Module.Finite.of_surjective _ hsurj
      have hrank := LinearMap.finrank_range_add_finrank_ker (pointRestrict hA hB hC x hx 0)
      rw [LinearMap.range_eq_top.2 hsurj, finrank_top, h0] at hrank
      have hpos := Module.finrank_pos (R := F)
        (M := W.grade (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)) 0)
      have hker : Module.finrank F (LinearMap.ker (pointRestrict hA hB hC x hx 0)) = 0 := by omega
      exact Submodule.finrank_eq_zero.1 hker ▸ inferInstance
    · have := Submodule.subsingleton_iff_eq_bot.2 (hbot m hm0 hm)
      exact ⟨fun a b ↦ Subtype.ext (Subsingleton.elim _ _)⟩

/-- **The image of `G(c₂)` on `G(P¹_k)` is invertible** (the last step of the proof of
Stacks 0FHL): `G(c₂)` splits through an invertible graded vector space, a line in degree `2`. -/
theorem exists_isInvertible_image_corrFunctor_map_projectiveLineFibrePoint :
    ∃ (U : GradedObject ℤ (ModuleCat.{w} F))
      (i : U ⟶ (corrFunctor hA hB hC).obj (ChowMotiveCat.projectiveLineDegreeZero k))
      (e : (corrFunctor hA hB hC).obj (ChowMotiveCat.projectiveLineDegreeZero k) ⟶ U),
      i ≫ e = 𝟙 U ∧
        e ≫ i = (corrFunctor hA hB hC).map (ChowMotiveCat.projectiveLineFibrePointDegreeZero x hx) ∧
        IsInvertible U := by
  refine ⟨fibrePointImage hA hB hC x hx,
    fun n ↦ ModuleCat.ofHom (LinearMap.ker (pointRestrict hA hB hC x hx n)).subtype,
    fun n ↦ ModuleCat.ofHom (LinearMap.codRestrict (LinearMap.ker (pointRestrict hA hB hC x hx n))
      (fibrePointMap hA hB hC x hx n) (pointRestrict_fibrePoint hA hB hC x hx n)), ?_, ?_, ?_⟩
  · funext n
    ext v
    exact congrArg Subtype.val (fibrePoint_apply_of_mem_ker hA hB hC x hx n v v.2)
  · funext n
    ext v
    rfl
  · obtain ⟨h1, h2⟩ := fibrePointImage_finrank_and_isZero hA hB hC x hx
    exact CategoryTheory.GradedObject.Monoidal.isInvertible_of_finrank_eq_one h1 h2

end Stacks.WeilCohomology.WeilData

end
