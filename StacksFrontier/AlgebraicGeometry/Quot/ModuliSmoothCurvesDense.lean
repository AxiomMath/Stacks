module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesSmoothDense
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesStable
public import StacksFrontier.AlgebraicGeometry.Quot.ModuliCurves

/-!
# `|𝓜_g|` is open and dense in `|𝓜̄_g|` (towards Stacks 0E87)

Let `𝓜̄_g ⊂ Curves` be the open substack of stable curves of genus `g` and `𝓜_g ⊂ Curves` the open
substack of smooth proper curves of genus `g` (Stacks 0E78 and 0E83). The proof of Stacks 0E87:
`𝓜̄_g` is an open substack of `Curves^{lci+}`, a stable family being at-worst-nodal, and
`Curves^{smooth} ∩ 𝓜̄_g = 𝓜_g`; so `|𝓜_g| = |Curves^{smooth}| ∩ |𝓜̄_g|` is open in `|𝓜̄_g|`, and
dense there because `|Curves^{smooth}|` is dense in `|Curves^{lci+}|` (Stacks 0E86) and `|𝓜̄_g|` is
open.

Everything is stated on `AlgebraicGeometry.curvesAlgebraicStack B hZ h`, which takes `h`, the
algebraicity of the stack of curves (Stacks 0D5A). The statement here takes the two open substacks
(`hP`, `hQ`) and the identity `Curves^{smooth} ∩ 𝓜̄_g = 𝓜_g` of the source's proof (`hMg`) as
inputs.

## Main results

* `AlgebraicGeometry.pointSet_inter_subset_of_imp`: if `P ∧ Q ⇒ R` for open loci of curves, then
  `|Curves^P| ∩ |Curves^Q| ⊆ |Curves^R|`; so `|Curves^{smooth}| ∩ |𝓜̄_g| ⊆ |𝓜_g|`.
* `AlgebraicGeometry.isOpen_dense_pointSet_moduliSmoothOfGenus_in_stableOfGenus`: the statement
  of Stacks 0E87 from those inputs.

## References

* [Stacks Project, Tag 0E87](https://stacks.math.columbia.edu/tag/0E87)
* [Stacks Project, Tag 0E86](https://stacks.math.columbia.edu/tag/0E86)
* [Stacks Project, Tag 0E78](https://stacks.math.columbia.edu/tag/0E78)
* [Stacks Project, Tag 0E83](https://stacks.math.columbia.edu/tag/0E83)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u w

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  (h : Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val)

/-- **The points of an intersection of open loci of curves.** Let `P`, `Q` and `R` be open loci of
families of curves with `P ∧ Q ⇒ R`. A point of `|Curves|` lying in `|Curves^P|` and in
`|Curves^Q|` lies in `|Curves^R|`. -/
theorem pointSet_inter_subset_of_imp {P Q R : ObjectProperty (CurveFamily B hZ)}
    (hP : IsOpenCurvesLocus B hZ P) (hQ : IsOpenCurvesLocus B hZ Q)
    (hR : IsOpenCurvesLocus B hZ R) (hPQR : ∀ F, P F → Q F → R F) :
    (curvesSmallOpenSubstack B hZ h hP).pointSet B integerBase hZ ∩
        (curvesSmallOpenSubstack B hZ h hQ).pointSet B integerBase hZ ⊆
      (curvesSmallOpenSubstack B hZ h hR).pointSet B integerBase hZ := by
  rintro x ⟨hxP, hxQ⟩
  obtain ⟨p, hp, rfl⟩ := (Stack.OpenSubstack.mem_pointSet_iff B integerBase hZ _ _).1 hxP
  obtain ⟨p', hp', hpp'⟩ := (Stack.OpenSubstack.mem_pointSet_iff B integerBase hZ _ _).1 hxQ
  obtain ⟨r, ⟨a⟩, ⟨b⟩⟩ :=
    (Stack.class_eq_class_iff_hasCommonExtension B integerBase hZ _ _ p' p).1 hpp'
  have hpr : Stack.pointClass B integerBase hZ _ (curvesAlgebraicStack B hZ h).val.property p =
      Stack.pointClass B integerBase hZ _ (curvesAlgebraicStack B hZ h).val.property r :=
    (Stack.class_eq_class_iff_hasCommonExtension B integerBase hZ _ _ p r).2 ⟨r, ⟨b⟩, ⟨𝟙 _⟩⟩
  rw [hpr]
  refine (Stack.OpenSubstack.mem_pointSet_iff B integerBase hZ _ _).2 ⟨r, ?_, rfl⟩
  let E := curvesSmallEquivalence B hZ h
  let F : CurveFamily B hZ := E.inverse.obj r.obj
  have hFP : P F := (curvesSmallOpenSubstack_property_iff B hZ h hP F).1
    (Stack.OpenSubstack.prop_of_hom B integerBase hZ _ (E.counitIso.hom.app r.obj ≫ b) hp)
  have hFQ : Q F := (curvesSmallOpenSubstack_property_iff B hZ h hQ F).1
    (Stack.OpenSubstack.prop_of_hom B integerBase hZ _ (E.counitIso.hom.app r.obj ≫ a) hp')
  exact Stack.OpenSubstack.prop_of_hom B integerBase hZ _ (E.counitIso.inv.app r.obj)
    ((curvesSmallOpenSubstack_property_iff B hZ h hR F).2 (hPQR F hFP hFQ))

/-- **The statement of Stacks 0E87 from the identity `Curves^{smooth} ∩ 𝓜̄_g = 𝓜_g`**, on the stack
of curves `curvesAlgebraicStack B hZ h`, where `h` is the algebraicity of the stack of curves
(Stacks 0D5A). Let `𝓜̄_g` and `𝓜_g` be the open substacks cut out by being stable of genus `g`
(`hP`, Stacks 0E78) and by being smooth with `f_*𝒪_X = 𝒪_S` universally of genus `g` (`hQ`,
Stacks 0E83), and let `hMg` be the identity `𝓜_g = Curves^{smooth} ∩ 𝓜̄_g` of the source's proof
(true for `g ≥ 2`). Then `|𝓜_g| ⊂ |𝓜̄_g|` is an open dense subset. -/
theorem isOpen_dense_pointSet_moduliSmoothOfGenus_in_stableOfGenus (g : ℕ)
    (hP : IsOpenCurvesLocus B hZ (IsStableCurveFamilyOfGenus B hZ g))
    (hQ : IsOpenCurvesLocus B hZ
      (fun X => IsSmoothH0Family B hZ X ∧ CurveFamily.HasGenus B hZ X g))
    (hMg : ∀ F : CurveFamily B hZ,
      IsSmoothH0Family B hZ F ∧ CurveFamily.HasGenus B hZ F g ↔
        IsSmoothFamily B hZ F ∧ IsStableCurveFamilyOfGenus B hZ g F) :
    letI := Stack.pointTopology B integerBase hZ (curvesAlgebraicStack B hZ h).val
    (curvesSmallOpenSubstack B hZ h hQ).pointSet B integerBase hZ ⊆
      (curvesSmallOpenSubstack B hZ h hP).pointSet B integerBase hZ ∧
    IsOpen (Subtype.val ⁻¹' (curvesSmallOpenSubstack B hZ h hQ).pointSet B integerBase hZ :
      Set ((curvesSmallOpenSubstack B hZ h hP).pointSet B integerBase hZ)) ∧
    Dense (Subtype.val ⁻¹' (curvesSmallOpenSubstack B hZ h hQ).pointSet B integerBase hZ :
      Set ((curvesSmallOpenSubstack B hZ h hP).pointSet B integerBase hZ)) := by
  let := Stack.pointTopology B integerBase hZ (curvesAlgebraicStack B hZ h).val
  have hQP : (curvesSmallOpenSubstack B hZ h hQ).pointSet B integerBase hZ ⊆
      (curvesSmallOpenSubstack B hZ h hP).pointSet B integerBase hZ :=
    Stack.OpenSubstack.pointSet_mono B integerBase hZ
      (curvesOpenSubstackOfIsOpenCurvesLocus_mono B hZ hQ hP (fun F hF => ((hMg F).1 hF).2) _ _ _)
  have hPl : (curvesSmallOpenSubstack B hZ h hP).pointSet B integerBase hZ ⊆
      (curvesSmallOpenSubstack B hZ h (isOpenCurvesLocus_lciPlus B hZ)).pointSet
        B integerBase hZ :=
    Stack.OpenSubstack.pointSet_mono B integerBase hZ
      (curvesOpenSubstackOfIsOpenCurvesLocus_mono B hZ hP (isOpenCurvesLocus_lciPlus B hZ)
        (fun F hF => isAtWorstNodal_le_lciPlus B hZ F hF.1.1.1) _ _ _)
  have hSP := pointSet_inter_subset_of_imp B hZ h (isOpenCurvesLocus_isSmoothFamily B hZ)
    hP hQ (fun F hs hst => (hMg F).2 ⟨hs, hst⟩)
  refine ⟨hQP, (Stack.OpenSubstack.isOpen_pointSet B integerBase hZ _).preimage
    continuous_subtype_val, fun x => ?_⟩
  rw [closure_subtype, Subtype.image_preimage_coe, Set.inter_eq_right.2 hQP]
  have hx := mem_closure_pointSet_curvesSmooth_of_mem_lciPlus B hZ h x.1 (hPl x.2)
  have hx' := (Stack.OpenSubstack.isOpen_pointSet B integerBase hZ _).inter_closure ⟨x.2, hx⟩
  exact closure_mono (fun y hy => hSP ⟨hy.2, hy.1⟩) hx'

end AlgebraicGeometry

end
