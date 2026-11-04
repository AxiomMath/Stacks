module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedCurvesUnconditional
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyTotalScheme
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveOnObjects
public import StacksFrontier.AlgebraicGeometry.AmpleNoetherianDimensionOne.Basic
public import StacksFrontier.AlgebraicGeometry.RelativelyAmple.AffineBase
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineProper
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.ModuleFiniteness
public import StacksFrontier.AlgebraicGeometry.Spaces.LocalRingDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowTwistWitness
public import StacksFrontier.AlgebraicGeometry.Properties.Dimension

/-!
# Every family of curves over a field carries a polarization (Stacks 0D5C)

Stacks 0D5C asserts that the left vertical arrow `PolarizedCurves ⟶ 𝒞urves` of the 2-fibre
product square `PolarizedCurves = 𝒞urves ×_{𝒮paces'_{fp, flat, proper}} 𝒫olarized` is surjective,
"every point is in the image". This is surjectivity on objects in the sense of Stacks 06D4,
proved here in the strong form where no field extension is needed: a family of curves `X ⟶ Spec k`
over a field is the image of a polarized curve over `k` itself. The proof is the one of
Stacks 0DQ0: `X` is a scheme by Stacks 0ADD
(`AlgebraicGeometry.CurveFamily.isRepresentable_total_of_base_eq`), proper of dimension at most one
over `k`, so it carries an ample invertible module by Stacks 09NZ (the input of Stacks 0A26), which
is relatively ample over the one-point base by Stacks 01VT.

## Main results

* `AlgebraicGeometry.CurveFamily.exists_polarizedCurve_hom`: a family of curves over the spectrum
  of a field is identified, over the identity of the base, with the family of curves of a
  polarized curve.
* `AlgebraicGeometry.isSurjectiveOnObjects_polarizedCurvesToCurves`: **Stacks 0D5C**, the
  projection `PolarizedCurves ⟶ 𝒞urves` is surjective on objects.

## Implementation notes

An object of the site whose underlying scheme is the spectrum of a field is only isomorphic to
`Spec k`; the family of curves is first pulled back along that isomorphism, read as a morphism of
the site from an object whose underlying scheme is `Spec k` on the nose, which Stacks 06D4 allows.
The scheme-level properties of the structure morphism of the total space (proper, flat, of finite
presentation) are read off its Yoneda image, which is the structure morphism of the family up to
the representing isomorphism, through Stacks 03ZM and the identity charts of Stacks 03MJ.

## References

* [Stacks Project, Tag 0D5C](https://stacks.math.columbia.edu/tag/0D5C)
* [Stacks Project, Tag 0DQ0](https://stacks.math.columbia.edu/tag/0DQ0)
* [Stacks Project, Tag 06D4](https://stacks.math.columbia.edu/tag/06D4)
* [Stacks Project, Tag 0ADD](https://stacks.math.columbia.edu/tag/0ADD)
* [Stacks Project, Tag 0A26](https://stacks.math.columbia.edu/tag/0A26)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

section Represented

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A morphism of the site whose Yoneda image is of finite presentation and proper is of finite
presentation.** Local finite presentation is read on the identity charts (Stacks 03MJ), and
quasi-compactness and quasi-separatedness come with properness. -/
theorem Space.finitePresentation_toScheme_map_of_yoneda_map {U V : BigFppfOver B S hS}
    (t : U ⟶ V) (hfp : Space.IsFinitePresentation B S hS (yoneda.map t))
    (hp : Space.IsProper B S hS (yoneda.map t)) :
    FinitePresentation ((BigFppfOver.toScheme B S hS).map t) :=
  have := isProper_toScheme_map_of_isProper_yoneda_map B S hS t hp
  FinitePresentation.mk
    ((Space.holdsOnEveryEtaleChart_yoneda_map_iff B S hS
      LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget t).mp hfp.1)
    inferInstance inferInstance

end Represented

section Curves

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- The total space of a family of curves over the spectrum of a field is represented by a
scheme of the site, read over `Spec(ℤ)` (Stacks 0ADD, as
`AlgebraicGeometry.CurveFamily.isRepresentable_total_of_base_eq`). -/
theorem CurveFamily.exists_iso_yoneda_schemeOverIntegers (y : CurveFamily B hZ) {K : Type u}
    [Field K] (hK : (BigFppfOver.toScheme B integerBase hZ).obj y.base = Spec (.of K)) :
    ∃ X : B.Schemes, Nonempty (yoneda.obj ((schemeOverIntegers B).obj X) ≅ y.total.obj) := by
  have := y.isRepresentable_total_of_base_eq hK
  refine ⟨y.total.obj.reprX.left, ⟨yoneda.mapIso (eqToIso ?_) ≪≫ y.total.obj.reprW⟩⟩
  exact congrArg Over.mk ((isTerminal_obj_specULiftZ B hZ).hom_ext _ _)

/-- The scheme representing the total space of a family of curves over the spectrum of a field
has dimension at most one: its local rings are those of the total space, which have dimension at
most one (`AlgebraicGeometry.CurveFamily.localRingDimension_le_one_of_base_eq`), and the
dimension of a scheme is the supremum of the dimensions of its local rings (Stacks 04MU). -/
theorem CurveFamily.topologicalKrullDim_le_one_of_iso (y : CurveFamily B hZ) {K : Type u}
    [Field K] (hK : (BigFppfOver.toScheme B integerBase hZ).obj y.base = Spec (.of K))
    (U : BigFppfOver B integerBase hZ) (e : yoneda.obj U ≅ y.total.obj) :
    topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj U) ≤ 1 := by
  rw [topologicalKrullDim_eq_iSup_krullDimOfRing_stalk]
  refine iSup_le fun u => ?_
  obtain ⟨p, rfl⟩ := Space.surjective_pointsToScheme B integerBase hZ U u
  rw [← Space.localRingDimension_eq_of_chartPoint B integerBase hZ y.total.property U e.hom
    (Space.presheaf_etale_of_iso B integerBase hZ e) _ _
    (Space.chartPoint_pointsToScheme B integerBase hZ U e.hom p)]
  exact_mod_cast y.localRingDimension_le_one_of_base_eq hK _

/-- **Every family of curves over the spectrum of a field carries a polarization.** Let `y` be a
family of curves over a scheme `V` of the site which is the spectrum of a field `K`. Its total
space is a scheme `X` (Stacks 0ADD), proper over `K` of dimension at most one, hence it carries
an ample invertible module `L` (Stacks 09NZ, the input of Stacks 0A26), which is relatively ample
over the one-point affine base (Stacks 01VT). So `(X ⟶ V, L)` is a polarized curve, and its
family of curves is identified with `y` over the identity of `V`. -/
theorem CurveFamily.exists_polarizedCurve_hom (Vs : B.Schemes) {K : Type u} [Field K]
    (hVs : Vs.obj = Spec (.of K)) (y : CurveFamily B hZ)
    (hy : y.base = (schemeOverIntegers B).obj Vs) :
    ∃ (P : (isPolarizedCurve B).FullSubcategory) (c : P.obj.toCurveFamily hZ P.property ⟶ y),
      (curvesProjectionOver B hZ).IsHomLift (𝟙 y.base) c := by
  obtain ⟨base, total, toBase, hflat, hproper, hfp, hdim⟩ := y
  subst hy
  have hK : (BigFppfOver.toScheme B integerBase hZ).obj ((schemeOverIntegers B).obj Vs) =
      Spec (.of K) := hVs
  obtain ⟨X, ⟨e⟩⟩ := CurveFamily.exists_iso_yoneda_schemeOverIntegers
    ⟨(schemeOverIntegers B).obj Vs, total, toBase, hflat, hproper, hfp, hdim⟩ hK
  let t : (schemeOverIntegers B).obj X ⟶ (schemeOverIntegers B).obj Vs :=
    yoneda.preimage (e.hom ≫ toBase.hom)
  have ht : yoneda.map t = e.hom ≫ toBase.hom := yoneda.map_preimage _
  let Y₀ : Comma
      (ObjectProperty.ι (fun F : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B integerBase hZ F))
      (yoneda : BigFppfOver B integerBase hZ ⥤ (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u) :=
    ⟨⟨yoneda.obj ((schemeOverIntegers B).obj X), isAlgebraicSpace_yoneda B integerBase hZ _⟩,
      (schemeOverIntegers B).obj Vs, yoneda.map t⟩
  have hcomm : e.hom ≫ toBase.hom = yoneda.map t ≫ yoneda.map (𝟙 _) := by
    rw [ht, CategoryTheory.Functor.map_id]
    exact (Category.comp_id _).symm
  let φ : Y₀ ≅ ⟨total, (schemeOverIntegers B).obj Vs, toBase.hom⟩ :=
    Comma.isoMk (ObjectProperty.isoMk _ e) (Iso.refl _) hcomm
  have hφlift : (spacesProjection B integerBase hZ).IsHomLift
      (𝟙 ((schemeOverIntegers B).obj Vs)) φ.hom :=
    inferInstanceAs ((spacesProjection B integerBase hZ).IsHomLift
      ((spacesProjection B integerBase hZ).map φ.hom) φ.hom)
  have hc : isCurveSpace B integerBase hZ Y₀ :=
    isCurveSpace_of_isStronglyCartesian B integerBase hZ (𝟙 ((schemeOverIntegers B).obj Vs))
      φ.hom inferInstance
      ⟨⟨hfp, hflat, hproper⟩, hdim⟩
  let g : X.obj ⟶ Vs.obj := (BigFppfOver.toScheme B integerBase hZ).map t
  have hgp : IsProper g := Space.isProper_toScheme_map_of_isProper_yoneda_map _ _ _ t hc.1.2.2
  have hgf : Flat g := Space.flat_of_isFlat_yoneda _ _ _ _ _ t hc.1.2.1
  have hgfp : FinitePresentation g :=
    Space.finitePresentation_toScheme_map_of_yoneda_map _ _ _ t hc.1.1 hc.1.2.2
  have hdimX : topologicalKrullDim X.obj ≤ 1 :=
    CurveFamily.topologicalKrullDim_le_one_of_iso
      ⟨(schemeOverIntegers B).obj Vs, total, toBase, hflat, hproper, hfp, hdim⟩ hK _ e
  let gK : X.obj ⟶ Spec (.of K) := g ≫ eqToHom hVs
  have : IsProper gK := inferInstance
  have : IsNoetherian X.obj := isNoetherian_of_locallyOfFiniteType gK
  have : X.obj.IsSeparated := Scheme.IsSeparated.of_isSeparated gK
  obtain ⟨L, hL, hamp⟩ :=
    Stacks.AmpleNoetherianDimensionOne.exists_isAmple_of_isNoetherian_of_topologicalKrullDim_le_one
      X.obj hdimX
  have : IsAffine Vs.obj := by rw [hVs]; infer_instance
  have : Subsingleton Vs.obj := by rw [hVs]; infer_instance
  let P : PolarizedFamily B :=
    { base := Vs
      total := X.obj
      toBase := g
      proper := hgp
      flat := hgf
      finitePresentation := hgfp
      lineBundle := L
      invertible := hL
      relativelyAmple := Scheme.Modules.isRelativelyAmple_of_isAmple g L hamp }
  have hP : isPolarizedCurve B P := hc.2
  refine ⟨⟨P, hP⟩, ⟨𝟙 _, (ObjectProperty.isoMk _ e).hom, ?_⟩, ?_⟩
  · have : IsIso (schemeSpaceMap (𝟙 ((schemeOverIntegers B).obj Vs))) := by
      rw [show schemeSpaceMap (𝟙 ((schemeOverIntegers B).obj Vs)) = 𝟙 _ from
        ObjectProperty.hom_ext _ (yoneda.map_id _)]
      infer_instance
    show IsPullback _ _ _ (schemeSpaceMap (𝟙 ((schemeOverIntegers B).obj Vs)))
    exact IsPullback.of_horiz_isIso ⟨ObjectProperty.hom_ext _ hcomm⟩
  · exact IsHomLift.of_fac' _ _ _ rfl rfl (by simp; rfl)

end Curves

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- **Stacks 0D5C: every point of `𝒞urves` is in the image of `PolarizedCurves`.** The left
vertical arrow `PolarizedCurves ⟶ 𝒞urves` of the 2-fibre product square is surjective on objects
(Stacks 06D4): every family of curves over the spectrum of a field `k` is, already over `k`
itself, the image of a polarized curve. Its total space is a scheme (Stacks 0ADD), proper of
dimension at most one over `k`, so it carries an ample invertible module (Stacks 0A26, through
Stacks 09NZ). -/
theorem isSurjectiveOnObjects_polarizedCurvesToCurves :
    Stack.IsSurjectiveOnObjects B integerBase hZ
      (polarizedCurvesFiberedCategory B hZ
        (polarizedProjection_comp_schemeOverIntegers_isFiberedInGroupoids B)).val.p
      (curvesFiberedCategory B hZ).val.p
      (CatFiberedInGroupoids.homFunctor (polarizedCurvesSquare B hZ
        (polarizedProjection_comp_schemeOverIntegers_isFiberedInGroupoids B)).snd) := by
  intro U hU y hy
  obtain ⟨K, hK, ⟨eU⟩⟩ := hU
  let := hK
  have hcont : B.Contains (Spec (.of K)) := by
    rw [BigFppfSite.Contains, ← Scheme.size_congr eU]
    exact U.left.property
  let Vs : B.Schemes := B.obj hcont
  let f : (schemeOverIntegers B).obj Vs ⟶ U :=
    Over.homMk (ObjectProperty.homMk eU.inv)
      ((isTerminal_obj_specULiftZ B hZ).hom_ext _ _)
  obtain ⟨y', b, hb⟩ := (curvesFiberedCategory B hZ).isFiberedInGroupoids.exists_lift f y hy
  have hy' : y'.base = (schemeOverIntegers B).obj Vs :=
    IsHomLift.domain_eq (curvesFiberedCategory B hZ).val.p f b
  obtain ⟨P, c, hc⟩ := y'.exists_polarizedCurve_hom Vs rfl hy'
  refine ⟨(schemeOverIntegers B).obj Vs, ⟨K, hK, ⟨Iso.refl _⟩⟩, f,
    polarizedCurveToPolarizedCurves B hZ P,
    (IsHomLift.domain_eq (curvesProjectionOver B hZ) (𝟙 y'.base) c).trans hy', c ≫ b, ?_⟩
  have hc' : (curvesFiberedCategory B hZ).val.p.IsHomLift (𝟙 y'.base) c := hc
  exact IsHomLift.comp_lift_id_left' (p := (curvesFiberedCategory B hZ).val.p) y'.base c f b

end AlgebraicGeometry
