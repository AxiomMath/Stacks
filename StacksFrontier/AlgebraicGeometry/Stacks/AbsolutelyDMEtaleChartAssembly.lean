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
  direction of **Stacks 06N3**, with no hypothesis left.
* `AlgebraicGeometry.Stack.isAbsolutelyDM_iff_isDeligneMumfordStack_unconditional`:
  **Stacks 06N3** itself, the equivalence of (1) DM, (2) Deligne–Mumford and (3) a surjective
  étale presentation by a scheme, now with no hypothesis either.

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

A `@[stacks 06N3]` registration of the whole equivalence with nothing assumed sits here too, on
`AlgebraicGeometry.Stack.isAbsolutelyDM_iff_isDeligneMumfordStack_unconditional`: it cannot sit in
`StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordPresentationTheorem`, where
`AlgebraicGeometry.Stack.isAbsolutelyDM_iff_isDeligneMumfordStack` states the equivalence with
both implications as arguments, that module being upstream of the family assembly this file uses
and so unable to name the substantial direction. The easy direction keeps its own registration,
on `AlgebraicGeometry.Stack.isAbsolutelyDM_of_isDeligneMumfordStack` in
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

/-- **Stacks 06N3.** An algebraic stack is DM exactly when it is Deligne–Mumford — equivalently,
by **Stacks 03YO**, exactly when there is a scheme of the site carrying a representable,
surjective, étale 1-morphism to it.

Both directions are proved and nothing is assumed. The implication (2) ⟹ (1) — equivalently
(3) ⟹ (1), these being the same condition here — is
`AlgebraicGeometry.Stack.isAbsolutelyDM_of_isDeligneMumfordStack`, off part (1) of
**Stacks 06MB**. The substantial direction (1) ⟹ (3) is
`AlgebraicGeometry.Stack.existsEtalePresentationOfIsAbsolutelyDM` of this file: the source's
étale chart at one finite type point, with the size bound uniform in the point
(`AlgebraicGeometry.Stack.exists_isRelativelyEtale_chart_size_le_of_isFiniteTypePoint`), fed to
the family assembly
`AlgebraicGeometry.Stack.existsEtalePresentationOfIsAbsolutelyDM_of_forall_exists_chart`, which
builds the index type, puts the coproduct in the site, and produces the surjective relatively
étale 1-morphism out of it
(`AlgebraicGeometry.Stack.isDeligneMumfordStack_of_forall_isRelativelyEtale`).

The substantial direction, `AlgebraicGeometry.Stack.ExistsEtalePresentationOfIsAbsolutelyDM`,
reduced to the chart construction `AlgebraicGeometry.Stack.ExistsEtaleChartFamilyOfIsAbsolutelyDM`,
is proved and not carried as a hypothesis. The statement cannot be placed in
`StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordPresentationTheorem`:
`StacksFrontier.AlgebraicGeometry.Stacks.EtaleChartFamilySizeBound`, which this file needs for the
family assembly, imports that module, so naming
`AlgebraicGeometry.Stack.existsEtalePresentationOfIsAbsolutelyDM` there would be an import
cycle.

The attribute below records where each step of the source's argument is. -/
@[stacks 06N3 "the equivalence of (1) DM with (2) Deligne-Mumford and (3) the existence of a \
surjective etale presentation by a scheme; (2) and (3) are the same condition here, since \
Stacks 03YO defines Deligne-Mumford that way. The implication (2) => (1) is proved, from \
Stacks 06MB part (1); the structure theorem (1) => (3) is PROVED, not carried, as \
existsEtalePresentationOfIsAbsolutelyDM of this file -- the chart at ONE finite type point with \
the uniform size bound (exists_isRelativelyEtale_chart_size_le_of_isFiniteTypePoint) fed to the \
family assembly existsEtalePresentationOfIsAbsolutelyDM_of_forall_exists_chart. The statement \
binds only the containment hZ of the terminal scheme, which the absolute Deligne-Mumford \
condition is stated at, and the algebraic stack 𝒳, and nothing stands for the structure \
theorem. The CHART CONSTRUCTION it runs on, the source's etale chart at each \
finite type point together with the site-membership of their coproduct, is isolated as \
ExistsEtaleChartFamilyOfIsAbsolutelyDM, and delivers the presentation by \
existsEtalePresentationOfIsAbsolutelyDM_of_existsEtaleChartFamily. Everything the source does \
after the charts is proved, in isDeligneMumfordStack_of_forall_isRelativelyEtale: the 1-morphism \
out of the coproduct W = ∐_x Z_x is exists_stackMap_comp_iso_sigmaOver_of_lt_cof, its \
surjectivity is exists_isSurjective_stackMap_of_finiteTypePoints_subset_iUnion_range (resting on \
06R7 and the corollary of 06G2 rather than on any property of the assembled chart), and its \
relative etaleness is \
isRelativelyEtale_of_isColimit_of_forall_isRelativelyEtale, the descent of the relative property \
of 03YK along the summand inclusions. NO TAG of the construction is carried. \
Stacks 06N0 is hasSurjectiveEtaleFieldSpectrumCover_unconditional, at its own binders: the \
division of the groupoid of the flat field-valued presentation by the open and closed \
subgroupoid through the identity is exists_division_identityArrowOpens_of_isoSpecField, on \
identityOpenFiniteSubgroupoid and mono_prodLift_of_unramified; the two tags it rests on are \
proved -- all four conclusions of 04S4 are exists_division and condition (2) of 06LZ is \
isRepresentable_of_isLocallyOfFiniteType_over_field; the construction carrying the stack-level \
flat presentation to a GroupoidScheme is the de-realization of the self-intersection groupoid, \
on isRepresentable_objects_pointGroupoid_fieldSpectrum and \
isRepresentable_arrows_pointGroupoid_fieldSpectrum; and the etaleness of Spec k_0 -> Z is \
isOpenImmersion_descended_identity and etale_descended_source read off the presentation through \
the quotient stack of the divided groupoid, by isEtale_quotientProjectionSchemeStackMap across \
the 046T equivalence nonempty_isEquivalenceOver_quotientStackMap_realizationHom, rather than by \
04XD. \
So the \
source's unramified field-valued point at a finite type point follows outright, by \
exists_relativelyUnramified_fieldSpectrum_point_of_isFiniteTypePoint, whose own binders are \
its statement's. The step before it is \
PROVED and not carried: the residual gerbe exists, by 06G3 (1) => (3) \
(existsLocallyOfFiniteTypeResidualGerbe, which needs neither Artin's theorem 06DC nor \
04Y5 (2) => (3), cutting the gerbe out of the target instead), its inclusion is a monomorphism \
(AlgebraicStacks.isMonomorphism_fullSubcategoryInclusion) and the gerbe is a reduced, \
locally Noetherian, one-point DM algebraic stack, which is exactly the hypothesis of 06N0 \
(isReducedLocallyNoetherianSingletonDM_of_isResidualGerbeAt, by 06MZ at that monomorphism). \
So 06G3 (1) => (3) is not carried either. \
Stacks 06MP (1) => (2) and both halves of 06MM are available. What else is missing is the body of \
the source's argument at a single finite type point -- the affine V etale over F = U x_X Spec k, \
its closed point with residue field finite separable over k, the regular sequence, and the \
slicing -- of which two steps are available: from the source's phi(m_u) O_{V,v} = m_v of \
02GF, the regular sequence is \
exists_mem_maximalIdeal_isRegular_ofList_eq_maximalIdeal_fiberStalk_of_smooth, which produces it \
GENERATING the maximal ideal of the fibre stalk and not merely cutting it to dimension zero \
(the fibre stalk of a smooth morphism is regular, so a minimal generating family selected inside \
phi(m_u) by exists_fn_mem_maximalIdeal_ofList_map_eq_maximalIdeal is regular by 00NQ), and the \
residue computation O_{T,v} = kappa(v) off it is \
map_maximalIdeal_comp_eq_of_ofList_eq_maximalIdeal_fiberStalk, read on the scheme-theoretic \
fibre by isField_fiberStalk_comp_of_ofList_eq_maximalIdeal_fiberStalk. Both clauses of 02GF \
that body needs are proved as well, each off the unramifiedness of F -> U that the monomorphy \
of Z_x -> X gives: the PRODUCTION of phi(m_u) O_{V,v} = m_v, and with it the sequence \
generating m_v, is \
exists_fn_mem_maximalIdeal_isRegular_ofList_eq_maximalIdeal_stalk_of_unramifiedAt (with \
exists_isAffineOpen_isRegular_ofList_eq_maximalIdeal_stalk_of_unramifiedAt reading it as \
regular functions on an affine open, the source's first shrinking), and its passage to the \
ETALE local ring where 06MD reads its hypothesis is \
exists_fn_isRegular_ofList_eq_maximalIdeal_etaleLocalRing_of_unramifiedAt across the faithful \
flatness of 05VP and the square of local rings of 05VU, with \
forall_isRegular_etaleLocalRingMap_germ_of_isRegular_chartLocalRing the same passage in the \
germ shape FibreIsRegularSequenceAt is written in, quantifier over etale neighbourhoods \
included (it costs nothing, by etaleLocalRingMap_etaleLocalRingGerm_eval_eq), so that the fibre \
hypothesis of 06MD is reduced to a regular sequence in the ordinary local ring of a scheme \
chart of the fibre; the SECOND clause of 02GF for the slice, the transport \
of the finite separability of kappa(v)/k along O_{V,v} ->> O_{T,v}, is \
unramifiedAt_comp_of_ofList_eq_maximalIdeal_fiberStalk, on \
bijective_residueFieldMap_of_isPreimmersion, with \
unramifiedAt_comp_of_ofList_eq_maximalIdeal_stalk the same statement at a generating sequence \
read in O_{V,v} -- where the sequence above is produced -- the two agreeing over a field-valued \
point of the base by ofList_eq_maximalIdeal_fiberStalk_of_ofList_eq_maximalIdeal. The SLICING \
POINT of that body is proved too, with everything both slicing lemmas read off it: \
exists_isClosed_isAffineOpen_isRegular_ofList_eq_maximalIdeal_finiteSeparable_of_unramified of \
SmoothSliceSeparablePoint takes an unramified q : V -> U of schemes with V nonempty and smooth \
over Spec k and returns the closed point v of 056U, the regularity of O_{V,v}, the sequence of \
regular functions on an affine open of U whose germs generate m_v as a regular sequence, and the \
residue field extension in the shape the criterion of 02GF reads it; the two come stated over \
DIFFERENT renderings of kappa(v) as an extension -- 056U through evaluation of global sections of \
Spec k, the criterion over kappa(pi v) through residueFieldMap -- and the reconciliation is \
finite_separable_residueFieldMap_of_finite_separable_Gammaevaluation of the same file, the two \
algebra structures sitting in one scalar tower by Gammaevaluation_naturality, with \
isRegularLocalRing_stalk_of_smooth_over_field the scheme form of the regularity (056S on stalks \
through 02IT) and unramifiedAt_comp_of_ofList_eq_maximalIdeal_stalk_over_field the \
unramifiedness of the slice with the hypothesis on the base discharged, the local ring of Spec k \
being the field itself. The slicing sequence in the etale local ring is likewise available off \
the hypotheses the assembly PRODUCES rather than off a chart square: \
exists_fn_isRegular_ofList_eq_maximalIdeal_etaleLocalRing_of_isUnramified of \
FibreSlicingSequenceFromIsUnramified asks only for Space.IsUnramified of the projection F -> U \
and regularity of F, discharging the chart-square hypotheses itself by \
unramified_chartMap_of_isUnramified (what Space.IsUnramified says, 03ZH part (1)) and \
isRegularLocalRing_chartLocalRing (06M1's etale-local regularity carried to a prescribed small \
etale neighbourhood by 03E8 and read on the stalk by 02IT). What remains of the body is its \
ASSEMBLY at one finite type point, and that is now exactly the identifications and the plumbing. \
The relative unramifiedness of \
exists_relativelyUnramified_fieldSpectrum_point_of_isFiniteTypePoint is NOT carried: \
read at a chart it is Space.IsUnramified of the projection F -> U of the fibre \
F = U x_X Spec k, by isUnramified_fibreSpaceProjection_of_relativeProperty of \
FibreProjectionUnramified, which carries the relative condition to the projection by 045C \
(hasRelativeProperty_baseChange_algebraicStacks) and reads it on the representing morphism by \
the 04XB bridge (hasRelativeProperty_iff_prop_representingMap); with the regularity of F that \
gives the slicing sequence in the etale local ring off the stack-level hypotheses alone, \
exists_fn_isRegular_ofList_eq_maximalIdeal_etaleLocalRing_fibre of the same file. Its companions \
are proved, the REGULARITY of F being \
hasEtaleLocalProperty_isRegular_fibreSpace of ChartFibreRegularity (06M1 at the structure \
morphism F -> Spec k, smooth by 075W because the chart is, by \
isSmooth_fibreStructureMorphism) in the form isRegularLocalRing_chartLocalRing consumes, and the \
NONEMPTINESS of F being exists_point_fibreOverFieldPoint_of_range_eq_singleton of the same file \
(04XH at a point of Spec k, which the singleton range of the field-valued point supplies). The \
GEOMETRIC POINT over the closed point of an etale chart of F is available too: every point of \
an etale chart is the chart point of a small etale neighbourhood of a geometric point of the \
space, by exists_chartGeometricPoint_chartPoint_eq of ChartSlicingGeometricPoint (03BX part (1) \
and exists_geometricRepresentative on the chart, pushed forward by ofChartGeometricPoint), and \
exists_chartGeometricPoint_isClosed_isRegularLocalRing_finiteSeparable of the same file puts the \
056U closed point of a chart nonempty and smooth over Spec k, with its regular local ring and \
its finite separable residue field extension, at such a geometric point. The PLUMBING of the \
slice as a scheme of the site is proved too, in EtaleChartFamilySizeBound: a monomorphism of \
schemes into a chart U of the site makes its source an object of the site over U of size at most \
2 ^ 2 ^ size U0 whenever size U <= size U0, which is the bound 06FX delivers \
(exists_siteObject_toScheme_map_eq_size_le), and with that bound uniform in the point \
exists_etaleChartFamily_of_forall_isFiniteTypePoint assembles the family of \
ExistsEtaleChartFamilyOfIsAbsolutelyDM with its site-membership conjunct, indexed by the points \
the substantial direction follows from the chart at ONE finite type point, by \
existsEtalePresentationOfIsAbsolutelyDM_of_forall_exists_chart, and nothing about the family, \
the index type or the coproduct is needed. Two further inputs are \
proved. The affine etale chart V of F through a prescribed point of |F|, with its \
scheme smooth over Spec k as a morphism of schemes, is \
exists_affine_smallEtale_smooth_chartScheme_at_point of AffineSmoothChartAtPoint, on \
exists_affine_etale_chart_at_point and on 03ZC part (1) read at the square against the IDENTITY \
chart of the representing object of Spec k (isEtaleChart_id), whose morphism of schemes is the \
chart's own structure morphism -- smooth_chartMap_of_isSmooth and \
smooth_toScheme_map_of_isSmooth_yoneda, the mirrors at smoothness of \
unramified_chartMap_of_isUnramified; with the 056U slicing point on it that is \
exists_affine_chartGeometricPoint_isClosed_isRegularLocalRing_finiteSeparable of the same file, \
and the space-level smoothness it consumes is isSmooth_fibreStructureMorphism read on the \
representing map by isSmooth_representingMap_of_isSmooth. And the shrinking of U that was to \
make the f_i global functions on the algebraic space U is NOT NEEDED: on a chart whose scheme is \
AFFINE the sequence may be chosen among the GLOBAL functions outright, the minimal generating \
family of exists_fn_mem_ofList_eq_maximalIdeal_of_span_eq being selectable inside any prescribed \
generating set and the global germs generating m_u because the stalk of an affine scheme is a \
localization of its global functions (span_image_preimage_germ_top_eq_maximalIdeal and \
exists_global_isRegular_ofList_eq_maximalIdeal_stalk_of_unramifiedAt of \
GlobalSlicingSequenceAffine), and a global function on the representing scheme IS a global \
section of the structure sheaf of the small etale site of a represented algebraic space, the \
identity chart being terminal there (representedUnitSection and eval_representedUnitSection of \
RepresentedGlobalSections, on isTerminal_idChart) -- no etale descent for O and nothing of 05B2 \
enters. The two together give the fibre hypothesis of 06MD and the generation the 02GF criterion \
reads, in exists_representedUnitSection_isRegular_etaleLocalRing_of_isAffine of \
FibreGlobalSlicingSequenceAffine, and that the 06FX chart is affine is recorded in the \
conclusion of exists_isClosed_smoothChart_size_le_of_isFiniteTypePoint. The PLUMBING of that \
body into existsEtalePresentationOfIsAbsolutelyDM_of_forall_exists_chart is PROVED, in \
exists_isRelativelyEtale_chart_size_le_of_isFiniteTypePoint of this file, from the following \
three inputs. The 06FX chart \
schemeStack U -> X is read as the 1-morphism algebraicSpaceStack (yoneda U) -> X that 06MD \
slices by algebraicSpaceStackChart of SchemeChartAsAlgebraicSpaceChart. The vanishing \
hypothesis of unramifiedAt_comp_of_ofList_eq_maximalIdeal_stalk_over_field, which asks for the \
chart of the slice to be identified with the zero scheme of the pulled-back functions, is \
supplied by definingIdealAt_vanishingSubspace_globalFunctionsMap_eq_ofList of \
FibreSliceChartZeroScheme, read at the chart by \
forall_unramifiedAt_toScheme_map_rep_snd_comp_of_eq_vanishingSubfunctor of \
ChartSliceUnramifiedFieldPoint and carried to the fibre hypothesis of 06N2 by \
exists_fibreIsUnramifiedNear_zeroLocusOnOpen_of_forall_germ_mem_maximalIdeal of \
SliceFibreSubspaceComparison. And the shrinking that turns the flat, locally finitely presented \
slice into a relatively etale chart BY A SCHEME OF THE SITE needs NEITHER an etale analogue of \
the relation-slice route NOR the missing direction of the open-substack correspondence: 06N2 \
read as exists_isOpenSubspace_isEtale_mem_range_pointsMap of EtaleChartStackPointMembership \
returns an open SUBSPACE of U, its point-set clause read off the singleton range of the \
field-valued point rather than off any bijectivity of spacePointMap, and \
exists_siteObject_isRelativelyEtale_chart_of_mem_range of EtaleChartOpenSubspaceSiteObject \
reads that subspace as a scheme of the site through a representing isomorphism. \
The FIBRE HYPOTHESIS of 06N2, \
FibreIsUnramifiedNear, is \
PROVED, in FibreUnramifiedNearSubstack, off the unramifiedness of the slice over Spec k at the \
sliced point as a morphism of schemes -- fibreIsUnramifiedNear_of_unramifiedAt. Two steps: that \
scheme-level statement is lifted to Space.IsUnramifiedAt of the structure morphism of the fibre \
read through a representing algebraic space Fsp, hence to an open subspace W of Fsp unramified \
over Spec k around the point \
(exists_isOpenSubspace_isUnramified_fibreSpace_of_unramifiedAt of FibreUnramifiedFromChart, off \
the chart criterion isUnramifiedAt_chartPoint_iff of UnramifiedAtChart, the mirror at \
unramifiedness of isFlatAt_chart_iff); and W is read as an OPEN SUBSTACK cut out by the \
ESSENTIAL IMAGE of S_W -> S_Fsp -> F, which is an open immersion by \
isOpenImmersion_algebraicSpaceStackMap_of_isOpenImmersion and \
isOpenImmersion_comp_of_quasiInverse, so 0506 both makes that essential image an open substack \
and factors the composite through it by an equivalence -- and that factorization is what carries \
all three of the things the clause needs. 003Z (2) upgrades it to an equivalence OVER THE SITE, \
so the open substack is represented by the algebraic space W \
(isRepresentableByAlgebraicSpace_essImage_of_isImmersion); the morphism of representing \
presheaves 04SW attaches to S_W -> F -> Spec k is computed outright to be W.iota followed by \
fibreSpaceStructureMorphism (representingMap_openSubspaceFibreMap_comp, on \
representingMap_associatedMap and representingMap_equivalenceOverInvMap), so the relative \
property of 03YK at unramifiedness holds of S_W -> Spec k by the 04XB bridge \
hasRelativeProperty_iff_prop_representingMap and transports to the open substack by 0457 \
(relativeProperty_of_equivalences_symm), the DM conjunct being 050E (3) at that \
representability; and the point-set membership is mem_range_pointsMap_openSubspaceFibreMap, on \
AlgebraicStacks.pointsMap_comp and pointsMap_eq_of_hom2. The open substack there is NOT the one \
exists_openSubstack_mem_pointSet_of_isOpenSubspace produces from the surjectivity half of 06FJ, \
which carries no representing datum. Invariance of Stack.IsUnramified under precomposition with \
an equivalence with NO representability hypothesis is not needed, and remains available only for \
a 1-morphism representable by algebraic spaces, where IsDM, IsFlat, IsSmooth and \
HasRelativeProperty have it outright. 056U, which gives that closed point \
at an affine etale chart \
of the algebraic space F, is formalized as \
dense_closedPoints_with_finite_separable_residueField_of_smooth, with its space-level form 07W4 \
as dense_setOf_class_finiteSeparable_of_isSmooth, which is stated over the base Spec k itself \
and so is not the form the assembly uses. 06MD is not missing either, in either conjunct: \
exists_openSubspace_isFlat_isLocallyOfFinitePresentation_zeroLocus_of_isRegular carries the tag \
at the hypotheses the source states, so the slice may be cut the source's way and need not go \
through the relation-slice descent the 06MF chart uses; the hypothesis it consumes is the \
regular sequence read in the ETALE local ring of F at a geometric point, which is regular by 06M1 \
(isRegular_of_isSmooth_over_field). The flatness conjunct \
of 06MD is likewise not carried as the hypothesis ZeroLocusIsFlatOverSmoothChart \
of ChartSlicingRegularSequence. Stacks 06N2 is not missing: \
exists_openSubstack_isEtale is proved outright, the comparison of Stacks 0CIT with the relative \
notion of 04XB being available for a representable 1-morphism by \
hasSurjectiveEtaleSmoothDiagram_of_isRepresentableByAlgebraicSpaces, which needs nothing of \
Stacks 0CIA"]
theorem isAbsolutelyDM_iff_isDeligneMumfordStack_unconditional
    (hZ : B.Contains (⊤_ Scheme.{u})) (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    AlgebraicStacks.IsAbsolutelyDM B S hS hZ 𝒳 ↔
      IsDeligneMumfordStack.{u, w} B S hS 𝒳.val.val :=
  ⟨existsEtalePresentationOfIsAbsolutelyDM.{u, w} B S hS hZ 𝒳,
    isAbsolutelyDM_of_isDeligneMumfordStack.{u, w} B S hS hZ 𝒳⟩

end AlgebraicGeometry.Stack

end
