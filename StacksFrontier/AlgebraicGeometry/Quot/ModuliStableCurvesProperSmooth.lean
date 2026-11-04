module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesGenus
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesLciPlusSmooth
public import StacksFrontier.AlgebraicGeometry.Quot.ModuliSmoothCurvesOpenDense
public import StacksFrontier.AlgebraicGeometry.Quot.ModuliSmoothCurvesStable
public import StacksFrontier.AlgebraicGeometry.Quot.ModuliStableCurvesGenusDecomposition
public import StacksFrontier.AlgebraicGeometry.Quot.ModuliStableCurvesOfGenusOpen
public import StacksFrontier.AlgebraicGeometry.Quot.ModuliStableCurvesOfGenusQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Quot.ModuliStableCurvesStableReduction
public import StacksFrontier.AlgebraicGeometry.Quot.StableCurvesSmoothOverSpecZ

/-!
# `𝓜̄_g` is a proper smooth Deligne–Mumford stack

Let `g ≥ 2`. Inside the stack of curves, `𝓜̄_g` is cut out by
`AlgebraicGeometry.IsStableCurveFamilyOfGenus` (stable, `R¹f_*𝒪_X` locally free of rank `g`) and
`𝓜_g` by `IsSmoothH0Family ∧ CurveFamily.HasGenus` (smooth of relative dimension one,
`f_*𝒪_X = 𝒪_S` universally, `R¹f_*𝒪_X` locally free of rank `g`). This file shows that both
loci are open as soon as the stable locus is, that `𝓜̄_g` is quasi-compact, and that `𝓜̄_g` is a
Deligne–Mumford stack, proper and smooth over `Spec(ℤ)`, in which the points of `𝓜_g` are dense,
given the hypotheses listed below.

## Main results

* `AlgebraicGeometry.CurveFamily.genus_eq_of_isPrestableCurveFamily_of_hasGenus`: the fibres of a
  prestable family of genus `g` are curves of genus `g`.
* `AlgebraicGeometry.isOpenCurvesLocus_isStableCurveFamilyOfGenus_of_isStable`: `𝓜̄_g` is an open
  locus when the stable families are.
* `AlgebraicGeometry.isOpenCurvesLocus_isSmoothH0FamilyOfGenus_of_isStable`: `𝓜_g`, `g ≥ 2`, is an
  open locus when the stable families are, since `𝓜_g = Curves^{smooth} ∩ 𝓜̄_g`.
* `AlgebraicGeometry.curvesSmallOpenSubstack_pointSet_eq_curvesPointSet`: the points of an open
  substack of the small model are the points of `|Curves|` it cuts out.
* `AlgebraicGeometry.isQuasiCompactStack_curvesSmallOpenSubstack_isStableCurveFamilyOfGenus`:
  `𝓜̄_g` is quasi-compact.
* `AlgebraicGeometry.moduliStableCurves_isDeligneMumford_proper_smooth_of_stableLocus`: `𝓜̄_g` is
  a proper smooth Deligne–Mumford stack over `Spec(ℤ)` containing `𝓜_g` as a dense open substack.

## Implementation notes

The last result takes as hypotheses:

* `h`: the stack of curves is algebraic;
* `h0E76`: the stable families form an open locus of the stack of curves;
* `hcurves`: `Curves ⟶ Spec(ℤ)` is quasi-separated and locally of finite presentation;
* `hDM`: `𝓜̄_g` is a Deligne–Mumford stack;
* `hsep`: `𝓜̄_g` is separated over `Spec(ℤ)`;
* `hchow`: Chow's lemma for algebraic stacks, in the form used to prove properness;
* `hred`: stable reduction for families of curves of genus `g`.

## References

* [Stacks Project, Tag 0E9C](https://stacks.math.columbia.edu/tag/0E9C)
* [Stacks Project, Tag 0E78](https://stacks.math.columbia.edu/tag/0E78)
* [Stacks Project, Tag 0E83](https://stacks.math.columbia.edu/tag/0E83)
* [Stacks Project, Tag 0E87](https://stacks.math.columbia.edu/tag/0E87)
* [Stacks Project, Tag 0E9B](https://stacks.math.columbia.edu/tag/0E9B)
* [Stacks Project, Tag 0E79](https://stacks.math.columbia.edu/tag/0E79)
-/

@[expose] public section

open CategoryTheory Topology

universe u w

namespace AlgebraicGeometry

attribute [local instance] Space.pointTopology

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

variable {B hZ} in
/-- **The fibres of a prestable family of genus `g` have genus `g`.** If `R¹f_*𝒪_X` of a prestable
family of curves is locally free of rank `g`, every presentation of a fibre over a field-valued
point of the base is a curve of genus `g`: the rank of `R¹f_*𝒪_X` at that point is the genus of
the fibre. -/
theorem CurveFamily.genus_eq_of_isPrestableCurveFamily_of_hasGenus {g : ℕ} {F : CurveFamily B hZ}
    (hF : IsPrestableCurveFamily B hZ F) (hgen : CurveFamily.HasGenus B hZ F g)
    (p : Space.FieldValuedPoint B integerBase hZ (schemeSpace F.base).obj)
    (V : BigFppfOver B integerBase hZ) (v : V ⟶ p.siteObject) (q : yoneda.obj V ⟶ F.total.obj)
    (hq : IsPullback q (yoneda.map v) F.toBase.hom (yonedaEquiv.symm p.value)) :
    genus ((BigFppfOver.toScheme B integerBase hZ).map v) = g :=
  Space.eq_of_mem_rankLocus_of_mem_rankLocus
    (F.mem_rankLocus_firstDirectImage_of_isPullback
      (CurveFamily.bijective_algebraMap_fibre_of_hasUniversallyBijectiveGlobalFunctions hF.2)
      p v q hq)
    (Space.mem_rankLocus_of_isFiniteLocallyFreeOfRank hgen _)

/-- **`𝓜̄_g` is open when `𝓜̄` is.** If the stable families form an open locus of the stack of
curves, so do the stable families with `R¹f_*𝒪_X` locally free of rank `g`: over a stable family
`G` over `S` they are cut out by the locus of points of `S` whose fibre has genus `g`, which is
open and closed, and a family mapping to `G` lies in `𝓜̄_g` exactly when its base lands in that
locus. -/
theorem isOpenCurvesLocus_isStableCurveFamilyOfGenus_of_isStable
    (h0E76 : IsOpenCurvesLocus B hZ (IsStableCurveFamily B hZ)) (g : ℕ) :
    IsOpenCurvesLocus B hZ (IsStableCurveFamilyOfGenus B hZ g) :=
  IsOpenCurvesLocus.of_points_of_isOpenCurvesLocus h0E76 (fun _ hF => hF.1) fun G hG =>
    have hdec := (moduliStableCurves_decomposition_moduliStableCurvesOfGenus (B := B)
      (hZ := hZ)).1 G hG
    ⟨CurveFamily.fibreGenusLocus B hZ G g, (hdec.1 g).isOpen, fun F a =>
      (isStableCurveFamilyOfFibreGenus_iff_isStableCurveFamilyOfGenus B hZ g
        F).symm.trans (hdec.2.2.2 g F a)⟩

/-- **`𝓜_g`, `g ≥ 2`, is open when `𝓜̄` is.** If the stable families form an open locus of the
stack of curves, so do the families in `𝓜_g`: for `g ≥ 2` a family is in `𝓜_g` exactly when it is
smooth and in `𝓜̄_g` (`𝓜_g = Curves^{smooth} ∩ 𝓜̄_g`), and both loci are open. -/
theorem isOpenCurvesLocus_isSmoothH0FamilyOfGenus_of_isStable
    (h0E76 : IsOpenCurvesLocus B hZ (IsStableCurveFamily B hZ)) {g : ℕ} (hg : 2 ≤ g) :
    IsOpenCurvesLocus B hZ (fun F => IsSmoothH0Family B hZ F ∧ CurveFamily.HasGenus B hZ F g) :=
  ((isOpenCurvesLocus_isSmoothFamily B hZ).and
    (isOpenCurvesLocus_isStableCurveFamilyOfGenus_of_isStable B hZ h0E76 g)).of_iff fun F =>
      (isSmoothH0Family_and_hasGenus_iff B hZ hg
        (fun _ hF hgen => CurveFamily.genus_eq_of_isPrestableCurveFamily_of_hasGenus hF hgen)
        F).symm

variable (h : Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val)

/-- **The points of an open substack of curves.** The points of the open substack of the small
model of the stack of curves cut out by an open locus `P` are the points of
`|Curves|` represented by a field-valued point whose family of curves has `P`. -/
theorem curvesSmallOpenSubstack_pointSet_eq_curvesPointSet {P : ObjectProperty (CurveFamily B hZ)}
    (hP : IsOpenCurvesLocus B hZ P) :
    (curvesSmallOpenSubstack B hZ h hP).pointSet B integerBase hZ = curvesPointSet B hZ P := by
  ext x
  rw [Stack.OpenSubstack.mem_pointSet_iff]
  exact exists_congr fun p => and_congr_left fun _ =>
    curvesOpenSubstackOfIsOpenCurvesLocus_property_iff_inverse B hZ hP _ _
      (curvesSmallEquivalence_functor_comp_p B hZ h) p.obj

/-- **`𝓜̄_g` is quasi-compact.** Let `g ≥ 2`. The open substack of `curvesAlgebraicStack B hZ h`
cut out by being stable of genus `g` is quasi-compact. -/
theorem isQuasiCompactStack_curvesSmallOpenSubstack_isStableCurveFamilyOfGenus {g : ℕ}
    (hg : 2 ≤ g) (hP : IsOpenCurvesLocus B hZ (IsStableCurveFamilyOfGenus B hZ g)) :
    Stack.IsQuasiCompactStack.{u, w} B integerBase hZ
      (curvesSmallOpenSubstack B hZ h hP).toAlgebraicStack.val
      (curvesSmallOpenSubstack B hZ h hP).toAlgebraicStack.property := by
  let := locallySmall_curveFamily B hZ
  let := locallySmall_moduliStableCurvesOfGenus B hZ g
  let W := curvesSmallOpenSubstack B hZ h hP
  let E := curvesSmallEquivalence B hZ h
  let Φ : (moduliStableCurvesOfGenusSmall B hZ g).val ⥤ᵇ W.toAlgebraicStack.val.val :=
    { toFunctor := ShrinkHoms.inverse.{u} (moduliStableCurvesOfGenus B hZ g).val.obj ⋙
        ObjectProperty.lift W.property
          (ObjectProperty.ι (IsStableCurveFamilyOfFibreGenus B hZ g) ⋙ E.functor) fun x =>
            (curvesSmallOpenSubstack_property_iff B hZ h hP x.obj).2
              ((isStableCurveFamilyOfFibreGenus_iff_isStableCurveFamilyOfGenus B hZ
                g x.obj).1 x.property)
      w := by
        show ShrinkHoms.inverse.{u} (moduliStableCurvesOfGenus B hZ g).val.obj ⋙
            ObjectProperty.ι (IsStableCurveFamilyOfFibreGenus B hZ g) ⋙ E.functor ⋙
              (curvesAlgebraicStack B hZ h).val.val.p = _
        rw [curvesSmallEquivalence_functor_comp_p]
        rfl }
  have hsurj : Function.Surjective (Stack.pointsMap B integerBase hZ
      (moduliStableCurvesOfGenusSmall B hZ g).val
      (moduliStableCurvesOfGenusSmall B hZ g).property W.toAlgebraicStack.val.property Φ) := by
    refine Quotient.ind fun q => ?_
    refine ⟨Stack.pointClass B integerBase hZ _ (moduliStableCurvesOfGenusSmall B hZ g).property
      { carrier := q.carrier
        field := q.field
        base := q.base
        isSpec := q.isSpec
        obj := ShrinkHoms.toShrinkHoms (⟨E.inverse.obj q.obj.obj,
          (isStableCurveFamilyOfFibreGenus_iff_isStableCurveFamilyOfGenus B hZ g _).2
            ((curvesOpenSubstackOfIsOpenCurvesLocus_property_iff_inverse B hZ hP _ _
              (curvesSmallEquivalence_functor_comp_p B hZ h) q.obj.obj).1 q.obj.property)⟩ :
            ObjectProperty.FullSubcategory (IsStableCurveFamilyOfFibreGenus B hZ g))
        «over» := q.over }, rfl⟩
  exact @Function.Surjective.compactSpace _ _
    (Stack.pointTopology B integerBase hZ (moduliStableCurvesOfGenusSmall B hZ g))
    (Stack.pointTopology B integerBase hZ W.toAlgebraicStack.val) _
    (Stack.continuous_pointsMap B integerBase hZ (moduliStableCurvesOfGenusSmall B hZ g)
      W.toAlgebraicStack.val Φ)
    (compactSpace_points_moduliStableCurvesOfGenusSmall B hZ g hg) hsurj

/-- **`𝓜̄_g` is a proper smooth Deligne–Mumford stack.** Let `g ≥ 2`, and let `𝓜̄_g` and `𝓜_g`
be the open substacks of the small model of the stack of curves cut out by being stable of genus
`g` (`IsStableCurveFamilyOfGenus`) and by being smooth of relative dimension one with
`f_*𝒪_X = 𝒪_S` universally and of genus `g`. Assume that the stack of curves is algebraic (`h`),
that the stable families form an open locus (`h0E76`), that `Curves ⟶ Spec(ℤ)` is quasi-separated
and locally of finite presentation (`hcurves`), that `𝓜̄_g` is a Deligne–Mumford stack (`hDM`)
separated over `Spec(ℤ)` (`hsep`), Chow's lemma for algebraic stacks (`hchow`), and stable
reduction for families of curves of genus `g` (`hred`). Then `𝓜̄_g` is a Deligne–Mumford stack,
proper and smooth over `Spec(ℤ)`, and `𝓜_g` is an open substack of `𝓜̄_g` whose points are dense
in `|𝓜̄_g|`. -/
theorem moduliStableCurves_isDeligneMumford_proper_smooth_of_stableLocus (g : ℕ) (hg : 2 ≤ g)
    (h0E76 : IsOpenCurvesLocus B hZ (IsStableCurveFamily B hZ))
    (hcurves : Stack.AlgebraicStacks.IsQuasiSeparated B integerBase hZ
        (Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h)) ∧
      Stack.AlgebraicStacks.IsLocallyOfFinitePresentation B integerBase hZ
        (Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h)))
    (hDM : Stack.IsDeligneMumfordStack.{u, w} B integerBase hZ
      (curvesSmallOpenSubstack B hZ h
        (isOpenCurvesLocus_isStableCurveFamilyOfGenus_of_isStable B hZ h0E76
          g)).toAlgebraicStack.val.val)
    (hsep : Stack.AlgebraicStacks.IsSeparated B integerBase hZ
      ((curvesSmallOpenSubstack B hZ h
          (isOpenCurvesLocus_isStableCurveFamilyOfGenus_of_isStable B hZ h0E76 g)).inclusion ≫
        Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h)))
    (hchow : ∀ (hT : B.Contains (⊤_ Scheme.{u}))
      {𝒳' : Stack.AlgebraicStacks.{u, w} B integerBase hZ}
      {Y : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B integerBase hZ Y),
      Space.IsQuasiCompactSpace B integerBase hZ Y →
      Space.IsAbsolutelyQuasiSeparated B integerBase hZ hT Y →
      ∀ (f' : 𝒳' ⟶ Stack.algebraicSpaceStack.{u, w} B integerBase hZ Y hY),
        Stack.AlgebraicStacks.IsSeparated B integerBase hZ f' →
        Stack.AlgebraicStacks.IsFiniteType B integerBase hZ f' →
        ∃ (X Xbar : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u)
          (hX : IsAlgebraicSpace B integerBase hZ X)
          (_ : IsAlgebraicSpace B integerBase hZ Xbar)
          (a : Stack.algebraicSpaceStack.{u, w} B integerBase hZ X hX ⟶ 𝒳')
          (i : X ⟶ Xbar) (g : Xbar ⟶ Y),
          Stack.AlgebraicStacks.IsProper B integerBase hZ a ∧
          Stack.IsSurjective B integerBase hZ a ∧
          Space.IsOpenImmersion B integerBase hZ i ∧ Space.IsProper B integerBase hZ g ∧
          Nonempty (a ≫ f' ≅
            Stack.algebraicSpaceStackMap.{u, w} B integerBase hZ hX hY (i ≫ g)))
    (hred : HasStableReductionCurveFamilies B hZ g) :
    Stack.IsDeligneMumfordStack.{u, w} B integerBase hZ
        (curvesSmallOpenSubstack B hZ h
          (isOpenCurvesLocus_isStableCurveFamilyOfGenus_of_isStable B hZ h0E76
            g)).toAlgebraicStack.val.val ∧
      Stack.AlgebraicStacks.IsProper B integerBase hZ
        ((curvesSmallOpenSubstack B hZ h
            (isOpenCurvesLocus_isStableCurveFamilyOfGenus_of_isStable B hZ h0E76 g)).inclusion ≫
          Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h)) ∧
      IsSmoothOverIntegers B hZ h
        (isOpenCurvesLocus_isStableCurveFamilyOfGenus_of_isStable B hZ h0E76 g) ∧
      ∃ hle : (curvesSmallOpenSubstack B hZ h
            (isOpenCurvesLocus_isSmoothH0FamilyOfGenus_of_isStable B hZ h0E76 hg)).property ≤
          (curvesSmallOpenSubstack B hZ h
            (isOpenCurvesLocus_isStableCurveFamilyOfGenus_of_isStable B hZ h0E76 g)).property,
        @Dense _ (Stack.pointTopology B integerBase hZ
            (curvesSmallOpenSubstack B hZ h
              (isOpenCurvesLocus_isStableCurveFamilyOfGenus_of_isStable B hZ h0E76
                g)).toAlgebraicStack.val)
          (Set.range (Stack.AlgebraicStacks.pointsMap B integerBase hZ
            (Stack.OpenSubstack.homOfLE B integerBase hZ
              (curvesSmallOpenSubstack B hZ h
                (isOpenCurvesLocus_isSmoothH0FamilyOfGenus_of_isStable B hZ h0E76 hg))
              (curvesSmallOpenSubstack B hZ h
                (isOpenCurvesLocus_isStableCurveFamilyOfGenus_of_isStable B hZ h0E76 g))
                hle))) := by
  have hP := isOpenCurvesLocus_isStableCurveFamilyOfGenus_of_isStable B hZ h0E76 g
  have hQ := isOpenCurvesLocus_isSmoothH0FamilyOfGenus_of_isStable B hZ h0E76 hg
  have hopen : (curvesSmallOpenSubstack B hZ h hQ).pointSet B integerBase hZ ⊆
        (curvesSmallOpenSubstack B hZ h hP).pointSet B integerBase hZ ∧
      (curvesSmallOpenSubstack B hZ h hP).pointSet B integerBase hZ ⊆
        @closure _ (Stack.pointTopology B integerBase hZ (curvesAlgebraicStack B hZ h).val)
          ((curvesSmallOpenSubstack B hZ h hQ).pointSet B integerBase hZ) := by
    rw [curvesSmallOpenSubstack_pointSet_eq_curvesPointSet B hZ h hP,
      curvesSmallOpenSubstack_pointSet_eq_curvesPointSet B hZ h hQ]
    obtain ⟨hsub, -, hdense⟩ :=
      curvesPointSet_moduliSmoothOfGenus_isOpen_dense_in_stableOfGenus B hZ g hg
    refine ⟨hsub, ?_⟩
    show curvesPointSet B hZ (IsStableCurveFamilyOfGenus B hZ g) ⊆
      closure (curvesPointSet B hZ
        (fun F => IsSmoothH0Family B hZ F ∧ CurveFamily.HasGenus B hZ F g))
    exact fun x hx => closure_mono (Set.image_preimage_subset _ _)
      (closure_subtype.1 (hdense ⟨x, hx⟩))
  have key : ∀ (Q : ObjectProperty (CurveFamily B hZ)) (hQ' : IsOpenCurvesLocus B hZ Q),
      Q = IsSmoothGenusCurveFamily B hZ g →
      (curvesSmallOpenSubstack B hZ h hQ').pointSet B integerBase hZ ⊆
          (curvesSmallOpenSubstack B hZ h hP).pointSet B integerBase hZ ∧
        (curvesSmallOpenSubstack B hZ h hP).pointSet B integerBase hZ ⊆
          @closure _ (Stack.pointTopology B integerBase hZ (curvesAlgebraicStack B hZ h).val)
            ((curvesSmallOpenSubstack B hZ h hQ').pointSet B integerBase hZ) →
      Stack.IsDeligneMumfordStack.{u, w} B integerBase hZ
          (curvesSmallOpenSubstack B hZ h hP).toAlgebraicStack.val.val ∧
        Stack.AlgebraicStacks.IsProper B integerBase hZ
          ((curvesSmallOpenSubstack B hZ h hP).inclusion ≫
            Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h)) ∧
        IsSmoothOverIntegers B hZ h hP ∧
        ∃ hle : (curvesSmallOpenSubstack B hZ h hQ').property ≤
            (curvesSmallOpenSubstack B hZ h hP).property,
          @Dense _ (Stack.pointTopology B integerBase hZ
              (curvesSmallOpenSubstack B hZ h hP).toAlgebraicStack.val)
            (Set.range (Stack.AlgebraicStacks.pointsMap B integerBase hZ
              (Stack.OpenSubstack.homOfLE B integerBase hZ (curvesSmallOpenSubstack B hZ h hQ')
                (curvesSmallOpenSubstack B hZ h hP) hle))) := by
    intro Q hQ' e hopen'
    subst e
    exact moduliStableCurves_isDeligneMumford_proper_smooth_of_stableReduction B hZ h g hg hP hQ'
      hcurves hDM (isSmoothOverIntegers_stableOfGenus B hZ h hcurves.2 g hP) hopen' hsep
      (isQuasiCompactStack_curvesSmallOpenSubstack_isStableCurveFamilyOfGenus B hZ h hg hP)
      hchow hred
  exact key _ hQ (funext fun F => propext (and_congr_left' and_comm)) hopen

end AlgebraicGeometry

end
