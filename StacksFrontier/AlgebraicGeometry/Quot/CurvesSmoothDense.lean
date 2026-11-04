module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyOverFieldScheme
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesLciPlus
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesLciPlusPoints
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesSmallOpenSubstack
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesSmoothingFamily
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenSubstackPoints
public import StacksFrontier.AlgebraicGeometry.Stacks.PointChartSpecialization
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionAtPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.StabilizerPreservingLocus
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.Syntomic
public import StacksFrontier.Deformation.Examples.Geometric.CurvesDeformationComparison

/-!
# The smooth curves inside `Curves^{lci+}` (Stacks 0E86)

Stacks 0E86 says that `|Curves^{smooth}| ⊂ |Curves^{lci+}|` is the inclusion of an open dense
subset. Both are open substacks of the stack of curves (Stacks 0E0E), and `|𝒰| ⊆ |Curves|` is the
point set of the open substack `𝒰` (Stacks 06FJ), the reading of `|𝒰|` that
`AlgebraicGeometry.Stack.OpenSubstack.pointSet` fixes.

The openness half comes from the construction of the topology on the points of an algebraic
stack (Stacks 04XL): a smooth family of curves has local complete intersection fibres with empty
singular locus, so `|Curves^{smooth}| ⊆ |Curves^{lci+}|`, and the point set of an open substack is
open, so `|Curves^{smooth}|` is open in `|Curves^{lci+}|`.

The density half follows the proof of Stacks 0E86. A point of `|Curves^{lci+}|` is represented by
a family of curves over a field `K`; its total space is a scheme `X` (Stacks 0ADD), proper of
dimension at most one over `K`, and by Stacks 0DZX, part (3), `X` is a local complete intersection
over `K`, smooth except at finitely many points. The smoothing of Stacks 0E7Y over `Spec K⟦t⟧`,
made a family of curves in `StacksFrontier.AlgebraicGeometry.Quot.CurvesSmoothingFamily`, and the
specialization argument of `AlgebraicGeometry.Stack.pointsWithin_closure_of_specializes` put the
point in the closure of `|Curves^{smooth}|`.

## Main results

* `AlgebraicGeometry.isOpen_dense_pointSet_curvesSmooth_in_lciPlus_of_equivalence`:
  `|Curves^{smooth}| ⊂ |Curves^{lci+}|` is an open dense subset, in every algebraic stack
  identified with the category of families of curves.
* `AlgebraicGeometry.pointSet_curvesSmooth_subset_lciPlus_of_equivalence`:
  `|Curves^{smooth}| ⊆ |Curves^{lci+}|`.
* `AlgebraicGeometry.isOpen_pointSet_curvesSmooth_in_lciPlus_of_equivalence`: `|Curves^{smooth}|`
  is an open subset of `|Curves^{lci+}|`.
* `AlgebraicGeometry.pointsWithin_closure_curvesSmooth_of_scheme_of_equivalence`: the density
  half at the point classifying a proper scheme over a field which is a local complete
  intersection smooth away from finitely many points.
* `AlgebraicGeometry.mem_closure_pointSet_curvesSmooth_of_mem_lciPlus_of_equivalence`: every
  point of `|Curves^{lci+}|` lies in the closure of `|Curves^{smooth}|`.
* `AlgebraicGeometry.isOpen_dense_pointSet_curvesSmooth_in_lciPlus` and its companions: the same
  statements on the small model `AlgebraicGeometry.curvesAlgebraicStack B hZ h`.

## Implementation notes

Stacks 0E86 itself, on the space `|Curves|` of points of the small model of the stack of curves,
which needs no algebraicity, is `AlgebraicGeometry.curvesPointSet_smooth_isOpen_dense_in_lciPlus`.

The stack of curves is the category of families of curves of Stacks 0D4Z, fibred in groupoids
over the big fppf site of `Spec(ℤ)`. Its algebraicity, Stacks 0D5A, is not proved in this
library, and the points `|𝒳|` and their topology are defined for algebraic stacks. So the
statement is made in every algebraic stack `𝒳` over the big fppf site of `Spec(ℤ)` together with
an equivalence `E` over the site between the category of families of curves and `𝒳`; the open
substacks `Curves^{smooth}` and `Curves^{lci+}` of `𝒳` are those cut out by the two conditions,
`AlgebraicGeometry.curvesOpenSubstackOfIsOpenCurvesLocus`. Specialized to the small model
`AlgebraicGeometry.curvesAlgebraicStack B hZ h`, which takes `h`, the algebraicity of the stack
of curves, these give the statements of the second section.

## References

* [Stacks Project, Tag 0E86](https://stacks.math.columbia.edu/tag/0E86)
* [Stacks Project, Tag 04XL](https://stacks.math.columbia.edu/tag/04XL)
* [Stacks Project, Tag 06FJ](https://stacks.math.columbia.edu/tag/06FJ)
* [Stacks Project, Tag 0ADD](https://stacks.math.columbia.edu/tag/0ADD)
* [Stacks Project, Tag 0DZX](https://stacks.math.columbia.edu/tag/0DZX)
* [Stacks Project, Tag 0D5A](https://stacks.math.columbia.edu/tag/0D5A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  (h : Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val)

/-! ### On any algebraic stack identified with the stack of curves -/

section Equivalence

variable (𝒳 : Stack.AlgebraicStacks.{u, w} B integerBase hZ) (E : CurveFamily B hZ ≌ 𝒳.val.val.obj)
  (hE : E.functor ⋙ 𝒳.val.val.p = curvesProjectionOver B hZ)

/-- **`|Curves^{smooth}| ⊆ |Curves^{lci+}|`**, in any algebraic stack `𝒳` identified with the
category of families of curves by an equivalence `E` over the site. A smooth family of curves is a
local complete intersection morphism whose singular locus is empty, hence finite over the base. -/
theorem pointSet_curvesSmooth_subset_lciPlus_of_equivalence :
    (curvesOpenSubstackOfIsOpenCurvesLocus B hZ (isOpenCurvesLocus_isSmoothFamily B hZ) 𝒳 E
        hE).1.pointSet B integerBase hZ ⊆
      (curvesOpenSubstackOfIsOpenCurvesLocus B hZ (isOpenCurvesLocus_lciPlus B hZ) 𝒳 E
        hE).1.pointSet B integerBase hZ :=
  Stack.OpenSubstack.pointSet_mono B integerBase hZ
    (curvesOpenSubstackOfIsOpenCurvesLocus_mono B hZ _ _ (isSmoothFamily_le_lciPlus B hZ) _ _ _)

/-- **Stacks 0E86, the openness half**, in any algebraic stack `𝒳` identified with the category of
families of curves by an equivalence `E` over the site: `|Curves^{smooth}|` is an open subset of
`|Curves^{lci+}|`, for the topology on the points of `𝒳` of Stacks 04XL. The point set of an open
substack is open (Stacks 06FJ), and it is contained in `|Curves^{lci+}|`. -/
theorem isOpen_pointSet_curvesSmooth_in_lciPlus_of_equivalence :
    letI := Stack.pointTopology B integerBase hZ 𝒳.val
    (curvesOpenSubstackOfIsOpenCurvesLocus B hZ (isOpenCurvesLocus_isSmoothFamily B hZ) 𝒳 E
        hE).1.pointSet B integerBase hZ ⊆
      (curvesOpenSubstackOfIsOpenCurvesLocus B hZ (isOpenCurvesLocus_lciPlus B hZ) 𝒳 E
        hE).1.pointSet B integerBase hZ ∧
    IsOpen (Subtype.val ⁻¹'
      (curvesOpenSubstackOfIsOpenCurvesLocus B hZ (isOpenCurvesLocus_isSmoothFamily B hZ) 𝒳 E
        hE).1.pointSet B integerBase hZ :
      Set ((curvesOpenSubstackOfIsOpenCurvesLocus B hZ (isOpenCurvesLocus_lciPlus B hZ) 𝒳 E
        hE).1.pointSet B integerBase hZ)) := by
  let := Stack.pointTopology B integerBase hZ 𝒳.val
  exact ⟨pointSet_curvesSmooth_subset_lciPlus_of_equivalence B hZ 𝒳 E hE,
    (Stack.OpenSubstack.isOpen_pointSet B integerBase hZ _).preimage continuous_subtype_val⟩

include hE in
/-- A morphism of families of curves, read in an algebraic stack `𝒳` through an equivalence `E`
over the site, lies over its morphism of base schemes. -/
theorem isHomLift_curvesEquivalence_map {F G : CurveFamily B hZ} (m : F ⟶ G) :
    𝒳.val.val.p.IsHomLift m.baseMap (E.functor.map m) := by
  have key : ∀ q : CurveFamily B hZ ⥤ BigFppfOver B integerBase hZ,
      E.functor ⋙ 𝒳.val.val.p = q → 𝒳.val.val.p.IsHomLift (q.map m) (E.functor.map m) := by
    rintro q rfl
    exact IsHomLift.map (p := 𝒳.val.val.p) (E.functor.map m)
  exact key _ hE

/-- **Stacks 0E86, the density half, at the point of a proper curve**, in any algebraic stack `𝒳`
identified with the category of families of curves by an equivalence `E` over the site. Let `X`
be a proper scheme of dimension at most one over a field `k` (with `Spec k` in the site) which is
a local complete intersection over `k` and smooth over `k` except at finitely many points. Then
every point of `|𝒳|` represented through the image under `E` of the family classifying `X` lies in
the closure of `|Curves^{smooth}|`. The smoothing `Y ⟶ Spec k⟦t⟧` of Stacks 0E7Y is a family of
curves through it over the closed point whose generic fibre is smooth, and the generic point of
`Spec k⟦t⟧` specializes to the closed point. -/
theorem pointsWithin_closure_curvesSmooth_of_scheme_of_equivalence {k : Type u} [Field k]
    (hk : B.Contains (Spec (.of k))) (X : Over (Spec (.of k))) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) (hlci : IsLocalCompleteIntersectionMorphism X.hom)
    (hfin : (X.hom.smoothLocus : Set X.left)ᶜ.Finite) :
    Stack.pointsWithin 𝒳
      (@closure _ (Stack.pointTopology B integerBase hZ 𝒳.val)
        ((curvesOpenSubstackOfIsOpenCurvesLocus B hZ (isOpenCurvesLocus_isSmoothFamily B hZ) 𝒳 E
          hE).1.pointSet B integerBase hZ))
      (E.functor.obj (curveFamilyOfScheme X B hZ hk hdim)) := by
  have hsyn : Syntomic X.hom :=
    (syntomic_iff_flat_and_isLocalCompleteIntersectionMorphism X.hom).2 ⟨inferInstance, hlci⟩
  obtain ⟨Y, g, hflat, hproj, hsm, e, he⟩ :=
    Deformation.Examples.Smoothing.exists_flat_isProjective_smoothing_of_isProper k X.hom hsyn hdim
      hfin
  have : IsProper g := IsProjective.isProper hproj
  have : Flat g := hflat
  have hV : B.Contains (Spec (.of (PowerSeries k))) := BigFppfSite.contains_spec_powerSeries B hk
  have hY : B.Contains Y := Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact g hV
  let s : Spec (.of k) ⟶ Spec (.of (PowerSeries k)) :=
    Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := k)))
  let y₀ := curveFamilyOfFiberDimensionLE B hZ (integerSiteMap B hZ hY hV g) hflat
    (inferInstanceAs (IsProper g)) (inferInstanceAs (LocallyOfFinitePresentation g))
    (fun x => topologicalKrullDimAt_fiber_le_one_of_specialFibre X.hom hdim g e he x)
  -- the special fibre
  have hcart₂ : IsPullback (e.hom ≫ pullback.fst g s) X.hom g s :=
    IsPullback.of_iso_pullback ⟨by rw [Category.assoc, pullback.condition, ← he,
      Category.assoc]⟩ e rfl he
  let m₂ : curveFamilyOfScheme X B hZ hk hdim ⟶ y₀ :=
    { baseMap := integerSiteMap B hZ hk hV s
      totalMap := schemeSpaceMap (integerSiteMap B hZ
        (Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact X.hom hk) hY
        (e.hom ≫ pullback.fst g s))
      cartesian := isPullback_schemeSpaceMap_integerSiteMap hcart₂ }
  -- the generic fibre
  let η : Spec (.of (PowerSeries k)) := ⟨⊥, inferInstance⟩
  have hK := BigFppfSite.residueField_spec_contains B hV η
  have hYη : B.Contains (g.fiber η) :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact (g.fiberToSpecResidueField η) hK
  have hdimη : topologicalKrullDim (g.fiber η) ≤ 1 :=
    (fiberDimension_le_one_of_specialFibre X.hom hdim g e he η).trans (by simp)
  let x₁ := curveFamilyOfProperFlatMorphism B hZ
    (integerSiteMap B hZ hYη hK (g.fiberToSpecResidueField η))
    (inferInstanceAs (Flat (g.fiberToSpecResidueField η)))
    (MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsProper)
      (IsPullback.of_hasPullback g _) ‹IsProper g›)
    (inferInstanceAs (LocallyOfFinitePresentation (g.fiberToSpecResidueField η))) hdimη
  let m₁ : x₁ ⟶ y₀ :=
    { baseMap := integerSiteMap B hZ hK hV ((Spec (.of (PowerSeries k))).fromSpecResidueField η)
      totalMap := schemeSpaceMap (integerSiteMap B hZ hYη hY (g.fiberι η))
      cartesian := isPullback_schemeSpaceMap_integerSiteMap (IsPullback.of_hasPullback g _) }
  have hx₁ : (curvesOpenSubstackOfIsOpenCurvesLocus B hZ (isOpenCurvesLocus_isSmoothFamily B hZ)
      𝒳 E hE).1.property (E.functor.obj x₁) :=
    (curvesOpenSubstackOfIsOpenCurvesLocus_property_iff B hZ _ 𝒳 E hE x₁).2
      ((Space.isSmooth_yoneda_map_iff B integerBase hZ _).2 hsm)
  have := isHomLift_curvesEquivalence_map B hZ 𝒳 E hE m₁
  have := isHomLift_curvesEquivalence_map B hZ 𝒳 E hE m₂
  have hy₀ : 𝒳.val.val.p.obj (E.functor.obj y₀) = y₀.base := Functor.congr_obj hE y₀
  refine Stack.pointsWithin_closure_of_isHomLift_of_specializes _ hy₀ m₁.baseMap m₂.baseMap
    (E.functor.map m₁) (E.functor.map m₂) ?_ ?_
  · exact fun v₂ _ => ⟨η, ⟨IsLocalRing.closedPoint _,
      (Spec (.of (PowerSeries k))).fromSpecResidueField_apply η _⟩,
      (PrimeSpectrum.le_iff_specializes η v₂).1 bot_le⟩
  · exact fun q φ => (Stack.OpenSubstack.mem_pointSet_iff B integerBase hZ _ _).2
      ⟨q, Stack.OpenSubstack.prop_of_hom B integerBase hZ _ φ hx₁, rfl⟩

/-- **Stacks 0E86, the density half**, in any algebraic stack `𝒳` identified with the category of
families of curves by an equivalence `E` over the site: every point of `|Curves^{lci+}|` lies in
the closure of `|Curves^{smooth}|`. -/
theorem mem_closure_pointSet_curvesSmooth_of_mem_lciPlus_of_equivalence
    (x : Stack.AlgebraicStacks.points B integerBase hZ 𝒳)
    (hx : x ∈ (curvesOpenSubstackOfIsOpenCurvesLocus B hZ (isOpenCurvesLocus_lciPlus B hZ) 𝒳 E
      hE).1.pointSet B integerBase hZ) :
    x ∈ @closure _ (Stack.pointTopology B integerBase hZ 𝒳.val)
      ((curvesOpenSubstackOfIsOpenCurvesLocus B hZ (isOpenCurvesLocus_isSmoothFamily B hZ) 𝒳 E
        hE).1.pointSet B integerBase hZ) := by
  obtain ⟨_, _, hK, X, _, hdim, hlci, hfin, q, rfl, ⟨m⟩⟩ :=
    exists_fieldValuedPoint_hom_curveFamilyOfScheme_of_mem_lciPlus_of_equivalence B hZ 𝒳 E hE x hx
  exact pointsWithin_closure_curvesSmooth_of_scheme_of_equivalence B hZ 𝒳 E hE hK X hdim hlci hfin
    q m

/-- **`|Curves^{smooth}| ⊂ |Curves^{lci+}|` is open and dense in every algebraic model.** The
stack of curves is read as any algebraic stack `𝒳` over the big fppf site of
`Spec(ℤ)` identified with the category of families of curves (Stacks 0D4Z) by an equivalence `E`
over the site; `|Curves^{smooth}|` and `|Curves^{lci+}|` are the point sets in `|𝒳|` (Stacks 04XL)
of the open substacks of `𝒳` cut out by smoothness of the family and by the conditions of
Stacks 0DZX. The first is contained in the second, it is open in the subspace topology of the
second, and it is dense there. -/
theorem isOpen_dense_pointSet_curvesSmooth_in_lciPlus_of_equivalence :
    letI := Stack.pointTopology B integerBase hZ 𝒳.val
    (curvesOpenSubstackOfIsOpenCurvesLocus B hZ (isOpenCurvesLocus_isSmoothFamily B hZ) 𝒳 E
        hE).1.pointSet B integerBase hZ ⊆
      (curvesOpenSubstackOfIsOpenCurvesLocus B hZ (isOpenCurvesLocus_lciPlus B hZ) 𝒳 E
        hE).1.pointSet B integerBase hZ ∧
    IsOpen (Subtype.val ⁻¹'
      (curvesOpenSubstackOfIsOpenCurvesLocus B hZ (isOpenCurvesLocus_isSmoothFamily B hZ) 𝒳 E
        hE).1.pointSet B integerBase hZ :
      Set ((curvesOpenSubstackOfIsOpenCurvesLocus B hZ (isOpenCurvesLocus_lciPlus B hZ) 𝒳 E
        hE).1.pointSet B integerBase hZ)) ∧
    Dense (Subtype.val ⁻¹'
      (curvesOpenSubstackOfIsOpenCurvesLocus B hZ (isOpenCurvesLocus_isSmoothFamily B hZ) 𝒳 E
        hE).1.pointSet B integerBase hZ :
      Set ((curvesOpenSubstackOfIsOpenCurvesLocus B hZ (isOpenCurvesLocus_lciPlus B hZ) 𝒳 E
        hE).1.pointSet B integerBase hZ)) := by
  let := Stack.pointTopology B integerBase hZ 𝒳.val
  have hsub := pointSet_curvesSmooth_subset_lciPlus_of_equivalence B hZ 𝒳 E hE
  refine ⟨hsub, (isOpen_pointSet_curvesSmooth_in_lciPlus_of_equivalence B hZ 𝒳 E hE).2,
    fun x => ?_⟩
  rw [closure_subtype, Subtype.image_preimage_coe, Set.inter_eq_right.2 hsub]
  exact mem_closure_pointSet_curvesSmooth_of_mem_lciPlus_of_equivalence B hZ 𝒳 E hE x x.2

end Equivalence

/-! ### On the small model of the stack of curves -/

/-- **`|Curves^{smooth}| ⊆ |Curves^{lci+}|`.** A smooth family of curves is a local complete
intersection morphism whose singular locus is empty, hence finite over the base. -/
theorem pointSet_curvesSmooth_subset_lciPlus :
    (curvesSmallOpenSubstack B hZ h (isOpenCurvesLocus_isSmoothFamily B hZ)).pointSet
        B integerBase hZ ⊆
      (curvesSmallOpenSubstack B hZ h (isOpenCurvesLocus_lciPlus B hZ)).pointSet
        B integerBase hZ :=
  pointSet_curvesSmooth_subset_lciPlus_of_equivalence B hZ _ _
    (curvesSmallEquivalence_functor_comp_p B hZ h)

/-- **Stacks 0E86, the openness half.** `|Curves^{smooth}|` is an open subset of `|Curves^{lci+}|`,
for the topology on the points of the stack of curves of Stacks 04XL: the point set of an open
substack is open (Stacks 06FJ), and it is contained in `|Curves^{lci+}|`. -/
theorem isOpen_pointSet_curvesSmooth_in_lciPlus :
    letI := Stack.pointTopology B integerBase hZ (curvesAlgebraicStack B hZ h).val
    (curvesSmallOpenSubstack B hZ h (isOpenCurvesLocus_isSmoothFamily B hZ)).pointSet
        B integerBase hZ ⊆
      (curvesSmallOpenSubstack B hZ h (isOpenCurvesLocus_lciPlus B hZ)).pointSet
        B integerBase hZ ∧
    IsOpen (Subtype.val ⁻¹'
      (curvesSmallOpenSubstack B hZ h (isOpenCurvesLocus_isSmoothFamily B hZ)).pointSet
        B integerBase hZ :
      Set ((curvesSmallOpenSubstack B hZ h (isOpenCurvesLocus_lciPlus B hZ)).pointSet
        B integerBase hZ)) :=
  isOpen_pointSet_curvesSmooth_in_lciPlus_of_equivalence B hZ _ _
    (curvesSmallEquivalence_functor_comp_p B hZ h)

/-- A morphism of families of curves, read in the small model, lies over its morphism of base
schemes. -/
theorem isHomLift_curvesSmallEquivalence_map {F G : CurveFamily B hZ} (m : F ⟶ G) :
    (curvesAlgebraicStack B hZ h).val.val.p.IsHomLift m.baseMap
      ((curvesSmallEquivalence B hZ h).functor.map m) :=
  isHomLift_curvesEquivalence_map B hZ _ _ (curvesSmallEquivalence_functor_comp_p B hZ h) m

/-- **Stacks 0E86, the density half, at the point of a proper curve.** Let `X` be a proper scheme
of dimension at most one over a field `k` (with `Spec k` in the site) which is a local complete
intersection over `k` and smooth over `k` except at finitely many points. Then every point of
`|Curves|` represented through the point `x₀` classifying `X` lies in the closure of
`|Curves^{smooth}|`. The smoothing `Y ⟶ Spec k⟦t⟧` of Stacks 0E7Y is a family of curves through
`x₀` over the closed point whose generic fibre is smooth, and the generic point of `Spec k⟦t⟧`
specializes to the closed point. -/
theorem pointsWithin_closure_curvesSmooth_of_scheme {k : Type u} [Field k]
    (hk : B.Contains (Spec (.of k))) (X : Over (Spec (.of k))) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) (hlci : IsLocalCompleteIntersectionMorphism X.hom)
    (hfin : (X.hom.smoothLocus : Set X.left)ᶜ.Finite) :
    Stack.pointsWithin (curvesAlgebraicStack B hZ h)
      (@closure _ (Stack.pointTopology B integerBase hZ (curvesAlgebraicStack B hZ h).val)
        ((curvesSmallOpenSubstack B hZ h (isOpenCurvesLocus_isSmoothFamily B hZ)).pointSet
          B integerBase hZ))
      ((curvesSmallEquivalence B hZ h).functor.obj (curveFamilyOfScheme X B hZ hk hdim)) :=
  pointsWithin_closure_curvesSmooth_of_scheme_of_equivalence B hZ _ _
    (curvesSmallEquivalence_functor_comp_p B hZ h) hk X hdim hlci hfin

/-- **Stacks 0E86, the density half.** Every point of `|Curves^{lci+}|` lies in the closure of
`|Curves^{smooth}|`. The point is represented by a family of curves over the spectrum of a field
`K`, mapping to the family of a proper scheme `X` of dimension at most one over `K` which is a
local complete intersection over `K` smooth except at finitely many points
(`AlgebraicGeometry.exists_fieldValuedPoint_hom_curveFamilyOfScheme_of_mem_lciPlus`), and
`AlgebraicGeometry.pointsWithin_closure_curvesSmooth_of_scheme` applies. -/
theorem mem_closure_pointSet_curvesSmooth_of_mem_lciPlus
    (x : Stack.AlgebraicStacks.points B integerBase hZ (curvesAlgebraicStack B hZ h))
    (hx : x ∈ (curvesSmallOpenSubstack B hZ h (isOpenCurvesLocus_lciPlus B hZ)).pointSet
      B integerBase hZ) :
    x ∈ @closure _ (Stack.pointTopology B integerBase hZ (curvesAlgebraicStack B hZ h).val)
      ((curvesSmallOpenSubstack B hZ h (isOpenCurvesLocus_isSmoothFamily B hZ)).pointSet
        B integerBase hZ) :=
  mem_closure_pointSet_curvesSmooth_of_mem_lciPlus_of_equivalence B hZ _ _
    (curvesSmallEquivalence_functor_comp_p B hZ h) x hx

/-- **Stacks 0E86 on the stack of curves `curvesAlgebraicStack B hZ h`**, where `h` is the
algebraicity of the stack of curves (Stacks 0D5A): `|Curves^{smooth}| ⊂ |Curves^{lci+}|` is an
open dense subset, for the topology on the points of an algebraic stack (Stacks 04XL). Openness is
`AlgebraicGeometry.isOpen_pointSet_curvesSmooth_in_lciPlus` and density is
`AlgebraicGeometry.mem_closure_pointSet_curvesSmooth_of_mem_lciPlus`. -/
theorem isOpen_dense_pointSet_curvesSmooth_in_lciPlus :
    letI := Stack.pointTopology B integerBase hZ (curvesAlgebraicStack B hZ h).val
    (curvesSmallOpenSubstack B hZ h (isOpenCurvesLocus_isSmoothFamily B hZ)).pointSet
        B integerBase hZ ⊆
      (curvesSmallOpenSubstack B hZ h (isOpenCurvesLocus_lciPlus B hZ)).pointSet
        B integerBase hZ ∧
    IsOpen (Subtype.val ⁻¹'
      (curvesSmallOpenSubstack B hZ h (isOpenCurvesLocus_isSmoothFamily B hZ)).pointSet
        B integerBase hZ :
      Set ((curvesSmallOpenSubstack B hZ h (isOpenCurvesLocus_lciPlus B hZ)).pointSet
        B integerBase hZ)) ∧
    Dense (Subtype.val ⁻¹'
      (curvesSmallOpenSubstack B hZ h (isOpenCurvesLocus_isSmoothFamily B hZ)).pointSet
        B integerBase hZ :
      Set ((curvesSmallOpenSubstack B hZ h (isOpenCurvesLocus_lciPlus B hZ)).pointSet
        B integerBase hZ)) :=
  isOpen_dense_pointSet_curvesSmooth_in_lciPlus_of_equivalence B hZ _ _
    (curvesSmallEquivalence_functor_comp_p B hZ h)

end AlgebraicGeometry

end
