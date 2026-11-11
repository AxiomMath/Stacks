module

public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordPresentationExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineSmoothChartHomAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreGlobalSlicingSequenceAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreSliceChartZeroScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreSlicingSequenceFromIsUnramified
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperClosedSubsetBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkAsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportChartZariski
public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChangeRepresentableBySpace
public import StacksFrontier.AlgebraicGeometry.Stacks.ChartFibreRegularity
public import StacksFrontier.AlgebraicGeometry.Stacks.ChartSliceUnramifiedFieldPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.ChartSlicingFlatness
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleChartFamilySizeBound
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleChartStackPointMembership
public import StacksFrontier.AlgebraicGeometry.Stacks.FibreProjectionUnramified
public import StacksFrontier.AlgebraicGeometry.Stacks.FieldPointFibreChartTransport
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypePointSmoothChart
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianPointsAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeChartAsAlgebraicSpaceChart
public import StacksFrontier.AlgebraicGeometry.Stacks.SliceFibreSubspaceComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismMonotone
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasBridges
public import StacksFrontier.AlgebraicGeometry.Stacks.ZeroLocusSliceSiteObject

/-!
# The étale chart of Stacks 06N3 at one finite type point

This file assembles the local half of the chart construction of **Stacks 06N3**: at a finite type
point `x` of a DM algebraic stack `𝒳`, against a smooth surjective chart `a₀ : U₀ ⟶ 𝒳` by a
scheme of the site, it produces a scheme `Z` of the site, a relatively étale 1-morphism
`Z ⟶ 𝒳` whose image on points contains `x`, and the size bound
`size Z ≤ 2 ^ 2 ^ size U₀` that the family assembly needs uniformly in `x`.

That is exactly the hypothesis `hchart` of
`AlgebraicGeometry.Stack.existsEtalePresentationOfIsAbsolutelyDM_of_forall_exists_chart`, so the
substantial direction of **Stacks 06N3**,
`AlgebraicGeometry.Stack.ExistsEtalePresentationOfIsAbsolutelyDM`, follows; that is the second
result below.

## Main results

* `AlgebraicGeometry.Stack.isSmooth_fibreSpaceStructureMorphism`: **Stacks 075W** at the
  structure morphism `F = U ×_𝒳 Spec k ⟶ Spec k`, read on a representing algebraic space.
* `AlgebraicGeometry.Stack.exists_isRelativelyEtale_chart_size_le_of_isFiniteTypePoint`: the
  chart at one finite type point, with the size bound.
* `AlgebraicGeometry.Stack.existsEtalePresentationOfIsAbsolutelyDM`: hence the substantial
  direction of **Stacks 06N3**.
* `AlgebraicGeometry.Stack.isAbsolutelyDM_iff_isDeligneMumfordStack_unconditional`:
  **Stacks 06N3** itself, the equivalence of (1) DM, (2) Deligne–Mumford and (3) a surjective
  étale presentation by a scheme.

## The source's proof, and where each step is

Let `x` be a finite type point of `𝒳`.

1. **Stacks 06FX** gives a smooth chart `φ : Uc ⟶ 𝒳` by a scheme of the site whose underlying
   scheme is **affine**, with `size Uc ≤ size U₀` and a point over `x`
   (`AlgebraicGeometry.Stack.exists_isClosed_smoothChart_size_le_of_isFiniteTypePoint`). It is
   read as a 1-morphism out of the algebraic space `h_{Uc}` by
   `AlgebraicGeometry.Stack.algebraicSpaceStackChart`, which stays smooth and so is flat and
   locally of finite presentation.
2. **Stacks 06PU** gives an unramified field-valued point `g : Spec k ⟶ 𝒳` with image exactly
   `{x}` (`AlgebraicGeometry.Stack.exists_fieldPointObject_schemeStack_range_eq_singleton`), and
   `F = h_{Uc} ×_𝒳 Spec k` is represented by an algebraic space `Fsp` by **Stacks 0300**. The
   projection `Fsp ⟶ h_{Uc}` is unramified
   (`AlgebraicGeometry.Stack.isUnramified_fibreSpaceProjection_of_relativeProperty`) and `Fsp` is
   regular, **Stacks 06M1** at the smooth structure morphism
   (`AlgebraicGeometry.Stack.hasEtaleLocalProperty_isRegular_fibreSpace`).
3. **Stacks 056U** gives an affine étale chart `Vch` of `Fsp` carrying a morphism of the site to
   the site object on `Spec k`, with a closed point of regular local ring and finite separable
   residue field (`AlgebraicGeometry.Space`
   `.exists_affine_chartGeometricPoint_hom_isClosed_isRegularLocalRing_finiteSeparable`).
4. The slicing sequence is read among the **global** functions of the affine chart `Uc` by
   `AlgebraicGeometry.Space.exists_representedUnitSection_isRegular_etaleLocalRing_of_isAffine`,
   whose square over `Uc` is the Yoneda preimage of the chart followed by the projection, and
   whose unramifiedness is **Stacks 03ZH**, part (1) read on that square
   (`AlgebraicGeometry.Space.unramified_chartMap_of_isUnramified`). Its last conclusion is the
   fibre hypothesis of **Stacks 06MD**, so
   `AlgebraicGeometry.Stack`
   `.exists_openSubspace_isFlat_isLocallyOfFinitePresentation_zeroLocus_of_isRegular`
   gives an open subspace `V ⊆ h_{Uc}` containing the image of the geometric point over which the
   slice `V(c₁, …, c_r) ∩ V ⟶ 𝒳` is flat and locally of finite presentation.
5. The criterion of **Stacks 02GF** on the chart,
   `AlgebraicGeometry.Stack`
   `.forall_unramifiedAt_toScheme_map_rep_snd_comp_of_eq_vanishingSubfunctor`, makes the chart of
   the fibre of the slice unramified over `Spec k`; the germ clause of the slicing sequence makes
   no section of the defining ideal of the zero locus invertible at the point; and the
   membership of step 4 crosses to the inverse image by
   `AlgebraicGeometry.Space.range_pointsMap_ι_preimage`. Together they give the fibre hypothesis
   of **Stacks 06N2** for the slice,
   `AlgebraicGeometry.Stack`
   `.exists_fibreIsUnramifiedNear_zeroLocusOnOpen_of_forall_germ_mem_maximalIdeal`.
6. The slice is a scheme `Z₀` of the site carrying a monomorphism `Z₀ ⟶ Uc`
   (`AlgebraicGeometry.Stack.exists_siteObject_iso_mono_zeroLocusOnOpen`), and **Stacks 06N2**
   with its point-set clause shrinks it to a relatively étale chart `Z ⟶ 𝒳` with `Z ⟶ Z₀` an
   open immersion (`AlgebraicGeometry.Stack`
   `.exists_siteObject_isRelativelyEtale_chart_of_fibreIsUnramifiedNear_mem_range`).
7. The size bound is read off the composite `Z ⟶ Z₀ ⟶ Uc`, a monomorphism of schemes, by
   `AlgebraicGeometry.size_le_of_mono_double_power`, and `size Uc ≤ size U₀` of step 1 then
   gives `size Z ≤ 2 ^ 2 ^ size U₀`: the bound the slice returns is against `Z₀`, which is
   useless on its own, and it is the composite that makes it a bound against `U₀`.

The `@[stacks 06N3]` registration of the whole equivalence sits here, on
`AlgebraicGeometry.Stack.isAbsolutelyDM_iff_isDeligneMumfordStack_unconditional`: it cannot sit in
`StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordPresentationTheorem`, which is upstream of the
family assembly this file uses and so cannot name the implication (1) ⟹ (3). The implication
(2) ⟹ (1) is `AlgebraicGeometry.Stack.isAbsolutelyDM_of_isDeligneMumfordStack` in
`StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordPresentationUnconditional`.

## References

* [Stacks Project, Tag 02GF](https://stacks.math.columbia.edu/tag/02GF)
* [Stacks Project, Tag 056U](https://stacks.math.columbia.edu/tag/056U)
* [Stacks Project, Tag 06FX](https://stacks.math.columbia.edu/tag/06FX)
* [Stacks Project, Tag 06M1](https://stacks.math.columbia.edu/tag/06M1)
* [Stacks Project, Tag 06MD](https://stacks.math.columbia.edu/tag/06MD)
* [Stacks Project, Tag 06N2](https://stacks.math.columbia.edu/tag/06N2)
* [Stacks Project, Theorem 101.21.6 (Tag 06N3)](https://stacks.math.columbia.edu/tag/06N3)
* [Stacks Project, Tag 06PU](https://stacks.math.columbia.edu/tag/06PU)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing Opposite

universe u w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 075W at the structure morphism of the fibre, read on a representing algebraic
space.** If the chart `f : U ⟶ 𝒳` is smooth then the morphism of algebraic spaces
`AlgebraicGeometry.Stack.fibreSpaceStructureMorphism` which **Stacks 04SW** attaches to the
structure 1-morphism `F = U ×_𝒳 Spec k ⟶ Spec k` is smooth.

`AlgebraicGeometry.Stack.isSmooth_fibreStructureMorphism` is the smoothness of the 1-morphism, and
`AlgebraicGeometry.Stack.isSmooth_representingMap_of_isSmooth` is the half of **Stacks 06FM**
which reads it on representing algebraic spaces. It is the input the affine étale chart of
**Stacks 056U** is cut out of, in
`AlgebraicGeometry.Space`
`.exists_affine_chartGeometricPoint_hom_isClosed_isRegularLocalRing_finiteSeparable`. -/
theorem isSmooth_fibreSpaceStructureMorphism (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hU : IsAlgebraicSpace B S hS U)
    (k : Type u) [Field k] (hk : B.Contains (Spec (.of k))) (toBase : Spec (.of k) ⟶ S)
    (f : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳)
    (g : schemeStack.{u, w} B S hS (fieldPointObject B S hS k hk toBase) ⟶ 𝒳)
    (Fsp : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hFsp : IsAlgebraicSpace B S hS Fsp)
    (eF : StacksRepresentableCFG.EquivalenceOver
      (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g).val.val.p
      (presheafOfCategories (Fsp ⋙ typeToCat)).p)
    (hfsm : AlgebraicStacks.IsSmooth B S hS f) :
    Space.IsSmooth B S hS
      (fibreSpaceStructureMorphism B S hS 𝒳 U hU k hk toBase f g Fsp eF) :=
  isSmooth_representingMap_of_isSmooth.{u, w} B S hS
    (Space.isSmoothLocalOnSourceAndTarget_smooth B S hS)
    (𝒳 := fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g)
    (𝒴 := schemeStack.{u, w} B S hS (fieldPointObject B S hS k hk toBase))
    Fsp (yoneda.obj (fieldPointObject B S hS k hk toBase)) hFsp
    (isAlgebraicSpace_yoneda B S hS (fieldPointObject B S hS k hk toBase)) eF
    (PresheafOfCategories.sliceElementsEquivalenceOver.{u} (fieldPointObject B S hS k hk toBase))
    (fibreStructureMorphism B S hS 𝒳 U hU k hk toBase f g)
    (isSmooth_fibreStructureMorphism B S hS 𝒳 U hU k hk toBase f g hfsm)

/-- The fibre `U ×_𝒳 Spec k` of a 1-morphism out of an algebraic space over a field-valued point
is represented by an algebraic space. -/
private theorem isRepresentableByAlgebraicSpace_fibreOverFieldPoint
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hU : IsAlgebraicSpace B S hS U) (k : Type u) [Field k] (hk : B.Contains (Spec (.of k)))
    (toBase : Spec (.of k) ⟶ S) (f : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳)
    (g : schemeStack.{u, w} B S hS (fieldPointObject B S hS k hk toBase) ⟶ 𝒳) :
    IsRepresentableByAlgebraicSpace B S hS
      (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g).val :=
  isRepresentableByAlgebraicSpace_of_isTwoFibreProduct.{u, u, u + 1}
    B S hS (schemeStack.{u, w} B S hS (fieldPointObject B S hS k hk toBase)).val 𝒳.val
    (algebraicSpaceStack.{u, w} B S hS U hU).val g.hom f.hom
    (twoFibreProductSquareAlgebraicStacks B S hS f g).underlying
    (isTwoFibreProduct_underlying_algebraicStacks B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS f g)
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS f g))
    (isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS 𝒳.property
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS
        (fieldPointObject B S hS k hk toBase)) g.hom)
    (isRepresentableByAlgebraicSpace_fibredCategory B S hS U hU)

/-- **The étale chart of Stacks 06N3 at one finite type point, with the size bound.** Let `𝒳` be
a DM algebraic stack over `S`, let `a₀ : U₀ ⟶ 𝒳` be a smooth surjective 1-morphism out of a
scheme of the site and let `x` be a finite type point of `|𝒳|`. Then there are a scheme `Z` of
the site and a 1-morphism `c : Z ⟶ 𝒳` which is relatively étale in the sense of **Stacks 04XB**,
whose image on points contains `x`, and with `size Z ≤ 2 ^ 2 ^ size U₀`.

This is the local half of the chart construction of **Stacks 06N3**; see the module
documentation for the seven steps and where each one is. -/
theorem exists_isRelativelyEtale_chart_size_le_of_isFiniteTypePoint
    (hZ : B.Contains (⊤_ Scheme.{u})) (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : AlgebraicStacks.IsAbsolutelyDM B S hS hZ 𝒳)
    (U₀ : BigFppfOver B S hS) (a₀ : schemeStack.{u, w} B S hS U₀ ⟶ 𝒳)
    (ha₀sm : AlgebraicStacks.IsSmooth B S hS a₀) (ha₀surj : IsSurjective B S hS a₀)
    (x : points B S hS 𝒳.val.val 𝒳.val.property)
    (hx : IsFiniteTypePoint.{u, w} B S hS 𝒳 x) :
    ∃ (Z : BigFppfOver B S hS) (c : schemeStack.{u, w} B S hS Z ⟶ 𝒳),
      IsRelativelyEtale B S hS c.hom ∧
      x ∈ Set.range (AlgebraicStacks.pointsMap B S hS c) ∧
      ((BigFppfOver.toScheme B S hS).obj Z).size ≤
        (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^
          ((BigFppfOver.toScheme B S hS).obj U₀).size := by
  classical
  -- Step 1: Stacks 06FX, read as a chart by the algebraic space the scheme represents
  obtain ⟨Uc, φ, zc, hφsm, -, hφz, hUsize, hUaff⟩ :=
    exists_isClosed_smoothChart_size_le_of_isFiniteTypePoint.{u, w} B S hS 𝒳 U₀ a₀ ha₀sm
      ha₀surj x hx
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj Uc) := hUaff
  have hUy : IsAlgebraicSpace B S hS (yoneda.obj Uc) := isAlgebraicSpace_yoneda B S hS Uc
  have hfsm : AlgebraicStacks.IsSmooth B S hS (algebraicSpaceStackChart.{u, w} B S hS Uc φ) :=
    isSmooth_algebraicSpaceStackChart.{u, w} B S hS Uc φ hφsm
  have hflat : AlgebraicStacks.IsFlat B S hS (algebraicSpaceStackChart.{u, w} B S hS Uc φ) :=
    AlgebraicStacks.isFlat_of_isSmooth B S hS _ hfsm
  have hlfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS
      (algebraicSpaceStackChart.{u, w} B S hS Uc φ) :=
    AlgebraicStacks.isLocallyOfFinitePresentation_of_isSmooth B S hS _ hfsm
  -- Step 2: the unramified field-valued point at `x`, and the fibre
  obtain ⟨k, _, hk, toBase, g, hgunr, hgrange⟩ :=
    exists_fieldPointObject_schemeStack_range_eq_singleton.{u, w} B S hS hZ 𝒳 h𝒳 x hx
  obtain ⟨Fsp, hFsp, ⟨eF⟩⟩ := isRepresentableByAlgebraicSpace_fibreOverFieldPoint.{u, w} B S hS
    𝒳 (yoneda.obj Uc) hUy k hk toBase (algebraicSpaceStackChart.{u, w} B S hS Uc φ) g
  -- the projection of the fibre is unramified, and the fibre is regular
  have hprojunr : Space.IsUnramified B S hS
      (fibreSpaceProjection B S hS 𝒳 (yoneda.obj Uc) hUy k hk toBase
        (algebraicSpaceStackChart.{u, w} B S hS Uc φ) g Fsp eF) :=
    isUnramified_fibreSpaceProjection_of_relativeProperty.{u, w} B S hS 𝒳 (yoneda.obj Uc) hUy
      k hk toBase (algebraicSpaceStackChart.{u, w} B S hS Uc φ) g Fsp hFsp eF hgunr
  have hFreg : Space.HasEtaleLocalProperty B S hS Fsp (fun X : Scheme.{u} => IsRegular X) :=
    hasEtaleLocalProperty_isRegular_fibreSpace.{u, w} B S hS 𝒳 (yoneda.obj Uc) hUy k hk toBase
      (algebraicSpaceStackChart.{u, w} B S hS Uc φ) g Fsp hFsp eF hfsm
  -- the structure morphism of the fibre is smooth
  have hstrsm : Space.IsSmooth B S hS
      (fibreSpaceStructureMorphism B S hS 𝒳 (yoneda.obj Uc) hUy k hk toBase
        (algebraicSpaceStackChart.{u, w} B S hS Uc φ) g Fsp eF) :=
    isSmooth_fibreSpaceStructureMorphism B S hS 𝒳 (yoneda.obj Uc) hUy k hk toBase
      (algebraicSpaceStackChart.{u, w} B S hS Uc φ) g Fsp hFsp eF hfsm
  -- the fibre is nonempty: the chart has a point over `x`
  have hxrange : x ∈ Set.range (AlgebraicStacks.pointsMap B S hS
      (algebraicSpaceStackChart.{u, w} B S hS Uc φ)) := by
    rw [range_pointsMap_algebraicSpaceStackChart.{u, w} B S hS Uc φ]
    exact ⟨zc, hφz⟩
  obtain ⟨uc, huc⟩ := hxrange
  obtain ⟨zst, -⟩ := exists_point_fibreOverFieldPoint_of_range_eq_singleton.{u, w} B S hS 𝒳
    (yoneda.obj Uc) hUy k hk toBase (algebraicSpaceStackChart.{u, w} B S hS Uc φ) g hgrange uc huc
  obtain ⟨x₀, -⟩ := (bijective_spacePointMap_representing B S hS Fsp
    (fibreOverFieldPoint B S hS 𝒳 (yoneda.obj Uc) hUy k hk toBase
      (algebraicSpaceStackChart.{u, w} B S hS Uc φ) g).val eF).2 zst
  -- Step 3: Stacks 056U on an affine étale chart of the fibre over `Spec k`
  obtain ⟨Vch, β, π, v, y, hVaff, hβ, hπ, hβsm, -, -, hvpt, -, hvreg, hvsep⟩ :=
    Space.exists_affine_chartGeometricPoint_hom_isClosed_isRegularLocalRing_finiteSeparable
      B S hS ⟨Fsp, hFsp⟩ (T := fieldPointObject B S hS k hk toBase) (k := k) rfl
      (fibreSpaceStructureMorphism B S hS 𝒳 (yoneda.obj Uc) hUy k hk toBase
        (algebraicSpaceStackChart.{u, w} B S hS Uc φ) g Fsp eF) hstrsm x₀
  have : Smooth ((BigFppfOver.toScheme B S hS).map β) := hβsm
  -- Step 4: the slicing sequence among the global functions of the affine chart `Uc`
  have hsq : Vch.obj.hom ≫ (ObjectProperty.homMk
        (fibreSpaceProjection B S hS 𝒳 (yoneda.obj Uc) hUy k hk toBase
          (algebraicSpaceStackChart.{u, w} B S hS Uc φ) g Fsp eF) :
        (⟨Fsp, hFsp⟩ : AlgebraicSpaces B S hS) ⟶ ⟨yoneda.obj Uc, hUy⟩).hom =
      yoneda.map (yoneda.preimage (Vch.obj.hom ≫
        fibreSpaceProjection B S hS 𝒳 (yoneda.obj Uc) hUy k hk toBase
          (algebraicSpaceStackChart.{u, w} B S hS Uc φ) g Fsp eF)) :=
    (yoneda.map_preimage _).symm
  have hpunr : Unramified ((BigFppfOver.toScheme B S hS).map
      (yoneda.preimage (Vch.obj.hom ≫
        fibreSpaceProjection B S hS 𝒳 (yoneda.obj Uc) hUy k hk toBase
          (algebraicSpaceStackChart.{u, w} B S hS Uc φ) g Fsp eF))) :=
    Space.unramified_chartMap_of_isUnramified B S hS hprojunr Vch (Space.idChart B S hS Uc) _
      (hsq.trans (Category.comp_id _).symm)
  have hplft : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map
      (yoneda.preimage (Vch.obj.hom ≫
        fibreSpaceProjection B S hS 𝒳 (yoneda.obj Uc) hUy k hk toBase
          (algebraicSpaceStackChart.{u, w} B S hS Uc φ) g Fsp eF))) := inferInstance
  have : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map
      (show (Space.SmallEtaleNeighborhood.ofChartGeometricPoint B S hS
            (⟨Fsp, hFsp⟩ : AlgebraicSpaces B S hS) Vch y).chart.obj.left ⟶ Uc from
        yoneda.preimage (Vch.obj.hom ≫
          fibreSpaceProjection B S hS 𝒳 (yoneda.obj Uc) hUy k hk toBase
            (algebraicSpaceStackChart.{u, w} B S hS Uc φ) g Fsp eF))) := hplft
  obtain ⟨cs, -, hcsgen, hcsetale⟩ :=
    Space.exists_representedUnitSection_isRegular_etaleLocalRing_of_isAffine B S hS hUy
      (ObjectProperty.homMk
        (fibreSpaceProjection B S hS 𝒳 (yoneda.obj Uc) hUy k hk toBase
          (algebraicSpaceStackChart.{u, w} B S hS Uc φ) g Fsp eF) :
        (⟨Fsp, hFsp⟩ : AlgebraicSpaces B S hS) ⟶ ⟨yoneda.obj Uc, hUy⟩)
      (Space.SmallEtaleNeighborhood.ofChartGeometricPoint B S hS
        (⟨Fsp, hFsp⟩ : AlgebraicSpaces B S hS) Vch y)
      (yoneda.preimage (Vch.obj.hom ≫
        fibreSpaceProjection B S hS 𝒳 (yoneda.obj Uc) hUy k hk toBase
          (algebraicSpaceStackChart.{u, w} B S hS Uc φ) g Fsp eF))
      hsq
      (Unramified.unramifiedAt (f := (BigFppfOver.toScheme B S hS).map
        (yoneda.preimage (Vch.obj.hom ≫
          fibreSpaceProjection B S hS 𝒳 (yoneda.obj Uc) hUy k hk toBase
            (algebraicSpaceStackChart.{u, w} B S hS Uc φ) g Fsp eF)))
        (Space.chartPoint B S hS Fsp
          (Space.SmallEtaleNeighborhood.ofChartGeometricPoint B S hS
            (⟨Fsp, hFsp⟩ : AlgebraicSpaces B S hS) Vch y)))
      (Space.isRegularLocalRing_chartLocalRing B S hS hFsp
        hFreg (Space.SmallEtaleNeighborhood.ofChartGeometricPoint B S hS
          (⟨Fsp, hFsp⟩ : AlgebraicSpaces B S hS) Vch y))
  -- Stacks 06MD at the geometric point of the fibre
  obtain ⟨V, hV, hmemV, hslflat, hsllfp⟩ :=
    exists_openSubspace_isFlat_isLocallyOfFinitePresentation_zeroLocus_of_isRegular.{u, w}
      B S hS 𝒳 (yoneda.obj Uc) hUy cs (algebraicSpaceStackChart.{u, w} B S hS Uc φ) k hk toBase
      g Fsp hFsp eF hflat hlfp (Space.geometricPointMap Vch.obj.hom y) hcsetale
  -- Step 5: the fibre of the slice is unramified near the sliced point
  subst hvpt
  have : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map β) := inferInstance
  have hpi : (BigFppfOver.toScheme B S hS).map β = π := by
    rw [hπ, eqToHom_refl, Category.comp_id]
  have hp : yoneda.map (yoneda.preimage (Vch.obj.hom ≫
        fibreSpaceProjection B S hS 𝒳 (yoneda.obj Uc) hUy k hk toBase
          (algebraicSpaceStackChart.{u, w} B S hS Uc φ) g Fsp eF)) ≫
      (Space.idChart B S hS Uc).obj.hom =
    Vch.obj.hom ≫ (ObjectProperty.homMk
        (fibreSpaceProjection B S hS 𝒳 (yoneda.obj Uc) hUy k hk toBase
          (algebraicSpaceStackChart.{u, w} B S hS Uc φ) g Fsp eF) :
        (⟨Fsp, hFsp⟩ : AlgebraicSpaces B S hS) ⟶ ⟨yoneda.obj Uc, hUy⟩).hom :=
    (Category.comp_id _).trans hsq.symm
  have hgenB : Ideal.ofList (List.ofFn fun i =>
      (Space.chartScheme Vch).presheaf.germ ⊤
        (Space.chartPoint B S hS Fsp
          (Space.SmallEtaleNeighborhood.ofChartGeometricPoint B S hS
            (⟨Fsp, hFsp⟩ : AlgebraicSpaces B S hS) Vch y)) trivial
        (((BigFppfOver.toScheme B S hS).map (yoneda.preimage (Vch.obj.hom ≫
          fibreSpaceProjection B S hS 𝒳 (yoneda.obj Uc) hUy k hk toBase
            (algebraicSpaceStackChart.{u, w} B S hS Uc φ) g Fsp eF))).appTop.hom
          ((cs i).eval (op (Space.idChart B S hS Uc))))) =
      maximalIdeal ((Space.chartScheme Vch).presheaf.stalk
        (Space.chartPoint B S hS Fsp
          (Space.SmallEtaleNeighborhood.ofChartGeometricPoint B S hS
            (⟨Fsp, hFsp⟩ : AlgebraicSpaces B S hS) Vch y))) := hcsgen
  have hI : Space.definingIdealAt B S hS (⟨Fsp, hFsp⟩ : AlgebraicSpaces B S hS)
        (Space.vanishingSubspace B S hS (⟨Fsp, hFsp⟩ : AlgebraicSpaces B S hS)
          fun i => Space.globalFunctionsMap B S hS (ObjectProperty.homMk
            (fibreSpaceProjection B S hS 𝒳 (yoneda.obj Uc) hUy k hk toBase
              (algebraicSpaceStackChart.{u, w} B S hS Uc φ) g Fsp eF) :
            (⟨Fsp, hFsp⟩ : AlgebraicSpaces B S hS) ⟶ ⟨yoneda.obj Uc, hUy⟩) (cs i))
        (op Vch) =
      Ideal.ofList (List.ofFn fun i =>
        ((BigFppfOver.toScheme B S hS).map (yoneda.preimage (Vch.obj.hom ≫
          fibreSpaceProjection B S hS 𝒳 (yoneda.obj Uc) hUy k hk toBase
            (algebraicSpaceStackChart.{u, w} B S hS Uc φ) g Fsp eF))).appTop.hom
          ((cs i).eval (op (Space.idChart B S hS Uc)))) :=
    Space.definingIdealAt_vanishingSubspace_globalFunctionsMap_eq_ofList B S hS
      (ObjectProperty.homMk
        (fibreSpaceProjection B S hS 𝒳 (yoneda.obj Uc) hUy k hk toBase
          (algebraicSpaceStackChart.{u, w} B S hS Uc φ) g Fsp eF) :
        (⟨Fsp, hFsp⟩ : AlgebraicSpaces B S hS) ⟶ ⟨yoneda.obj Uc, hUy⟩)
      cs (Space.idChart B S hS Uc) Vch
      (yoneda.preimage (Vch.obj.hom ≫
        fibreSpaceProjection B S hS 𝒳 (yoneda.obj Uc) hUy k hk toBase
          (algebraicSpaceStackChart.{u, w} B S hS Uc φ) g Fsp eF)) hp hVaff
  have hgerm : ∀ s ∈ Ideal.ofList (List.ofFn fun i =>
        ((BigFppfOver.toScheme B S hS).map (yoneda.preimage (Vch.obj.hom ≫
          fibreSpaceProjection B S hS 𝒳 (yoneda.obj Uc) hUy k hk toBase
            (algebraicSpaceStackChart.{u, w} B S hS Uc φ) g Fsp eF))).appTop.hom
          ((cs i).eval (op (Space.idChart B S hS Uc)))),
      (Space.chartScheme Vch).presheaf.germ ⊤
          (Space.chartPoint B S hS Fsp
            (Space.SmallEtaleNeighborhood.ofChartGeometricPoint B S hS
              (⟨Fsp, hFsp⟩ : AlgebraicSpaces B S hS) Vch y)) trivial s ∈
        maximalIdeal ((Space.chartScheme Vch).presheaf.stalk
          (Space.chartPoint B S hS Fsp
            (Space.SmallEtaleNeighborhood.ofChartGeometricPoint B S hS
              (⟨Fsp, hFsp⟩ : AlgebraicSpaces B S hS) Vch y))) := by
    intro s hs
    have hle : Ideal.map ((Space.chartScheme Vch).presheaf.germ ⊤
          (Space.chartPoint B S hS Fsp
            (Space.SmallEtaleNeighborhood.ofChartGeometricPoint B S hS
              (⟨Fsp, hFsp⟩ : AlgebraicSpaces B S hS) Vch y)) trivial).hom
        (Ideal.ofList (List.ofFn fun i =>
          ((BigFppfOver.toScheme B S hS).map (yoneda.preimage (Vch.obj.hom ≫
            fibreSpaceProjection B S hS 𝒳 (yoneda.obj Uc) hUy k hk toBase
              (algebraicSpaceStackChart.{u, w} B S hS Uc φ) g Fsp eF))).appTop.hom
            ((cs i).eval (op (Space.idChart B S hS Uc))))) ≤
        maximalIdeal ((Space.chartScheme Vch).presheaf.stalk
          (Space.chartPoint B S hS Fsp
            (Space.SmallEtaleNeighborhood.ofChartGeometricPoint B S hS
              (⟨Fsp, hFsp⟩ : AlgebraicSpaces B S hS) Vch y))) := by
      rw [Ideal.map_span]
      refine Ideal.span_le.mpr ?_
      rintro _ ⟨b, hb, rfl⟩
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hb
      rw [← hgenB]
      exact Ideal.subset_span (List.mem_ofFn.2 ⟨i, rfl⟩)
    exact hle (Ideal.mem_map_of_mem _ hs)
  have hunrB := forall_unramifiedAt_toScheme_map_rep_snd_comp_of_eq_vanishingSubfunctor B S hS
    (ObjectProperty.homMk
      (fibreSpaceProjection B S hS 𝒳 (yoneda.obj Uc) hUy k hk toBase
        (algebraicSpaceStackChart.{u, w} B S hS Uc φ) g Fsp eF) :
      (⟨Fsp, hFsp⟩ : AlgebraicSpaces B S hS) ⟶ ⟨yoneda.obj Uc, hUy⟩)
    cs (Space.idChart B S hS Uc) Vch
    (yoneda.preimage (Vch.obj.hom ≫
      fibreSpaceProjection B S hS 𝒳 (yoneda.obj Uc) hUy k hk toBase
        (algebraicSpaceStackChart.{u, w} B S hS Uc φ) g Fsp eF)) hp hVaff hk toBase β π hpi
    (Space.vanishingSubspace B S hS (⟨Fsp, hFsp⟩ : AlgebraicSpaces B S hS)
      fun i => Space.globalFunctionsMap B S hS (ObjectProperty.homMk
        (fibreSpaceProjection B S hS 𝒳 (yoneda.obj Uc) hUy k hk toBase
          (algebraicSpaceStackChart.{u, w} B S hS Uc φ) g Fsp eF) :
        (⟨Fsp, hFsp⟩ : AlgebraicSpaces B S hS) ⟶ ⟨yoneda.obj Uc, hUy⟩) (cs i)) rfl
    (Space.chartPoint B S hS Fsp
      (Space.SmallEtaleNeighborhood.ofChartGeometricPoint B S hS
        (⟨Fsp, hFsp⟩ : AlgebraicSpaces B S hS) Vch y)) hgenB hvsep
  -- the point of the chart lies over the open subspace Stacks 06MD returns
  have hw : Space.pointsMap B S hS
        (yoneda.obj ((Space.SmallEtale.toOver B S hS Fsp).obj Vch)) Vch.obj.hom
        ((Space.pointsEquivScheme B S hS ((Space.SmallEtale.toOver B S hS Fsp).obj Vch)).symm
          (Space.chartPoint B S hS Fsp
            (Space.SmallEtaleNeighborhood.ofChartGeometricPoint B S hS
              (⟨Fsp, hFsp⟩ : AlgebraicSpaces B S hS) Vch y))) ∈
      Set.range (Space.pointsMap B S hS
        (V.preimage (fibreSpaceProjection B S hS 𝒳 (yoneda.obj Uc) hUy k hk toBase
          (algebraicSpaceStackChart.{u, w} B S hS Uc φ) g Fsp eF)).toFunctor
        (V.preimage (fibreSpaceProjection B S hS 𝒳 (yoneda.obj Uc) hUy k hk toBase
          (algebraicSpaceStackChart.{u, w} B S hS Uc φ) g Fsp eF)).ι) := by
    rw [Space.range_pointsMap_ι_preimage B S hS hFsp hUy
      (fibreSpaceProjection B S hS 𝒳 (yoneda.obj Uc) hUy k hk toBase
        (algebraicSpaceStackChart.{u, w} B S hS Uc φ) g Fsp eF) V hV.1]
    refine Set.mem_preimage.2 ?_
    have hpt : (Space.pointsEquivScheme B S hS
          ((Space.SmallEtale.toOver B S hS Fsp).obj Vch)).symm
        (Space.chartPoint B S hS Fsp
          (Space.SmallEtaleNeighborhood.ofChartGeometricPoint B S hS
            (⟨Fsp, hFsp⟩ : AlgebraicSpaces B S hS) Vch y)) = y.image :=
      (Space.pointsEquivScheme B S hS
        ((Space.SmallEtale.toOver B S hS Fsp).obj Vch)).symm_apply_apply y.image
    rw [hpt]
    exact hmemV
  -- the fibre of the slice over the field-valued point
  have hZslsp : IsAlgebraicSpace B S hS
      (zeroLocusOnOpen B S hS (yoneda.obj Uc) hUy cs V).toFunctor :=
    (isClosedSubspace_zeroLocusOnOpen B S hS (yoneda.obj Uc) hUy cs V hV).1
  obtain ⟨Qq, hQq, ⟨eQ⟩⟩ := isRepresentableByAlgebraicSpace_fibreOverFieldPoint.{u, w} B S hS
    𝒳 _ hZslsp k hk toBase
    (zeroLocusOnOpenToStack.{u, w} B S hS 𝒳 (yoneda.obj Uc) hUy
      (algebraicSpaceStackChart.{u, w} B S hS Uc φ) cs V hV) g
  obtain ⟨xF, hfibunr⟩ :=
    exists_fibreIsUnramifiedNear_zeroLocusOnOpen_of_forall_germ_mem_maximalIdeal.{u, w}
      B S hS 𝒳 (yoneda.obj Uc) hUy k hk toBase
      (algebraicSpaceStackChart.{u, w} B S hS Uc φ) g Fsp hFsp eF cs V
      (zeroLocusOnOpen B S hS (yoneda.obj Uc) hUy cs V) hZslsp rfl Qq hQq eQ
      (Space.vanishingSubspace B S hS (⟨Fsp, hFsp⟩ : AlgebraicSpaces B S hS)
        fun i => Space.globalFunctionsMap B S hS (ObjectProperty.homMk
          (fibreSpaceProjection B S hS 𝒳 (yoneda.obj Uc) hUy k hk toBase
            (algebraicSpaceStackChart.{u, w} B S hS Uc φ) g Fsp eF) :
          (⟨Fsp, hFsp⟩ : AlgebraicSpaces B S hS) ⟶ ⟨yoneda.obj Uc, hUy⟩) (cs i)) rfl
      Vch β hβ hVaff _ hI
      (Space.chartPoint B S hS Fsp
        (Space.SmallEtaleNeighborhood.ofChartGeometricPoint B S hS
          (⟨Fsp, hFsp⟩ : AlgebraicSpaces B S hS) Vch y)) hgerm hunrB
      (V.preimage (fibreSpaceProjection B S hS 𝒳 (yoneda.obj Uc) hUy k hk toBase
        (algebraicSpaceStackChart.{u, w} B S hS Uc φ) g Fsp eF))
      (Space.isOpenSubspace_preimage B S hS
        (fibreSpaceProjection B S hS 𝒳 (yoneda.obj Uc) hUy k hk toBase
          (algebraicSpaceStackChart.{u, w} B S hS Uc φ) g Fsp eF) V hUy hFsp hV) rfl hw
  -- Step 6: the slice as a scheme of the site, and Stacks 06N2 with the point-set clause
  obtain ⟨Z₀, V₀, zz, vv, e, -, -, himm, -, -, -⟩ :=
    exists_siteObject_iso_mono_zeroLocusOnOpen B S hS (yoneda.obj Uc) hUy cs
      (Iso.refl (yoneda.obj Uc)) hV
  obtain ⟨Zfin, zmap, cfin, hzoi, hcet, hcmem, -⟩ :=
    exists_siteObject_isRelativelyEtale_chart_of_fibreIsUnramifiedNear_mem_range.{u, w} B S hS 𝒳
      (zeroLocusOnOpen B S hS (yoneda.obj Uc) hUy cs V).toFunctor hZslsp k hk toBase
      (zeroLocusOnOpenToStack.{u, w} B S hS 𝒳 (yoneda.obj Uc) hUy
        (algebraicSpaceStackChart.{u, w} B S hS Uc φ) cs V hV) g Qq eQ e hslflat hsllfp hgrange
      xF hfibunr
  -- Step 7: the size bound, read along the composite `Zfin ⟶ Z₀ ⟶ V₀ ⟶ Uc`
  have : Mono ((BigFppfOver.toScheme B S hS).map zmap) :=
    _root_.AlgebraicGeometry.IsOpenImmersion.le_monomorphisms _ hzoi
  have : _root_.AlgebraicGeometry.IsImmersion
    ((BigFppfOver.toScheme B S hS).map (zz ≫ vv)) := himm
  have : Mono ((BigFppfOver.toScheme B S hS).map (zz ≫ vv)) := inferInstance
  have : Mono ((BigFppfOver.toScheme B S hS).map (zmap ≫ zz ≫ vv)) := by
    rw [Functor.map_comp]
    infer_instance
  exact ⟨Zfin, cfin, hcet, hcmem, le_trans
    (size_le_of_mono_double_power ((BigFppfOver.toScheme B S hS).map (zmap ≫ zz ≫ vv)))
    (Cardinal.power_le_power_left two_ne_zero
      (Cardinal.power_le_power_left two_ne_zero hUsize))⟩

/-- **Stacks 06N3.** Let `𝒳` be an algebraic stack. The following are equivalent: (1) `𝒳` is DM,
(2) `𝒳` is Deligne–Mumford, and (3) there is a scheme `W` with a surjective étale 1-morphism
`W ⟶ 𝒳`.

As in the source, (3) is the definition of (2) (**Stacks 03YO**,
`AlgebraicGeometry.Stack.IsDeligneMumfordStack`: a scheme of the site carrying a 1-morphism to
`𝒳` that is representable by algebraic spaces, surjective and étale), so the three conditions
are the single equivalence below. Condition (1) is the absolute DM property of **Stacks 050D**,
part (5), which is DM over `Spec ℤ`; the argument `hZ` records that the site contains the
terminal scheme, which is what that definition is stated at, and it always holds
(`AlgebraicGeometry.BigFppfSite.contains_terminal`).

The implication (2) ⟹ (1) is `AlgebraicGeometry.Stack.isAbsolutelyDM_of_isDeligneMumfordStack`,
off part (1) of **Stacks 06MB**. The implication (1) ⟹ (3) is
`AlgebraicGeometry.Stack.existsEtalePresentationOfIsAbsolutelyDM` of this file: the source's
étale chart at each finite type point, with a size bound uniform in the point
(`AlgebraicGeometry.Stack.exists_isRelativelyEtale_chart_size_le_of_isFiniteTypePoint`), and
the disjoint union of these charts
(`AlgebraicGeometry.Stack.existsEtalePresentationOfIsAbsolutelyDM_of_forall_exists_chart`). -/
@[stacks 06N3 "the equivalence of (1) DM, (2) Deligne-Mumford and (3) the existence of a \
surjective etale morphism from a scheme, (2) and (3) being the same condition by the definition \
03YO; (2) => (1) is isAbsolutelyDM_of_isDeligneMumfordStack (06MB part (1)) and (1) => (3) is \
existsEtalePresentationOfIsAbsolutelyDM, the etale chart at each finite type point followed by \
the disjoint union of the charts"]
theorem isAbsolutelyDM_iff_isDeligneMumfordStack_unconditional
    (hZ : B.Contains (⊤_ Scheme.{u})) (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    AlgebraicStacks.IsAbsolutelyDM B S hS hZ 𝒳 ↔
      IsDeligneMumfordStack.{u, w} B S hS 𝒳.val.val :=
  ⟨existsEtalePresentationOfIsAbsolutelyDM.{u, w} B S hS hZ 𝒳,
    isAbsolutelyDM_of_isDeligneMumfordStack.{u, w} B S hS hZ 𝒳⟩

end AlgebraicGeometry.Stack

end
