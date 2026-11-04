module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyPicardAmpleLocus
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyBaseChangeFieldFibre
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyOverFieldScheme
public import StacksFrontier.AlgebraicGeometry.AmpleNoetherianDimensionOne.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeAmpleAffineBase.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleBridge.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeModuleRelativeAmpleTransfer

/-!
# The ample locus of the Picard stack meets every fibre (the surjectivity half of Stacks 0DQ0)

Let `X ⟶ T` be a family of curves. In the proof of Stacks 0DQ0 the morphism
`PolarizedCurves ⟶ 𝒞urves` is surjective because every family of curves over a field has a
polarization. Read on the Picard stack `Picardstack_{X/T}` of Stacks 0372 this says that the ample
locus `AlgebraicGeometry.Space.PicardObject.IsInAmpleLocus` meets the fibre over every point of
`T`. This file proves that statement, with no hypothesis.

For a point `t` of `T` take the residue field `κ(t)` and the point `x : Spec κ(t) ⟶ T`. The base
change `X_x = X ×_T Spec κ(t)` (`AlgebraicGeometry.CurveFamily.baseChange`) is a family of curves
over a field, so its total space is a scheme of dimension at most one
(`AlgebraicGeometry.CurveFamily.isRepresentable_total_of_base_eq`, which is where Stacks 0ADD
enters). That scheme is proper over `κ(t)`, Noetherian and separated, so it carries an ample
invertible module (Stacks 09NZ), which is relatively ample over the affine base (Stacks 01VK).
The module moves to the algebraic space `X_x` by
`AlgebraicGeometry.Space.exists_isInvertibleModule_isRelativelyAmple_of_presentation`. Together
with `x` it is an object of the Picard stack over the test scheme `x`, in the ample locus.

No tag is registered in this file.

## Main results

* `AlgebraicGeometry.CurveFamily.exists_isRelativelyAmple_reprX_of_base_eq`: the scheme
  representing the total space of a family of curves over a field carries an invertible module
  ample over the field.
* `AlgebraicGeometry.CurveFamily.exists_picardObject_isInAmpleLocus_of_point`: **through every
  point of the base there is a field-valued point and an object of the Picard stack over it in the
  ample locus.**

## References

* [Stacks Project, Tag 0DQ0](https://stacks.math.columbia.edu/tag/0DQ0)
* [Stacks Project, Tag 0372](https://stacks.math.columbia.edu/tag/0372)
* [Stacks Project, Tag 0ADD](https://stacks.math.columbia.edu/tag/0ADD)
* [Stacks Project, Tag 09NZ](https://stacks.math.columbia.edu/tag/09NZ)
* [Stacks Project, Tag 01VK](https://stacks.math.columbia.edu/tag/01VK)
* [Stacks Project, Tag 0D31](https://stacks.math.columbia.edu/tag/0D31)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace CurveFamily

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- **A family of curves over a field carries an ample module on its representing scheme.** Let
`F` be a family of curves over the spectrum of a field `K` whose total space is a scheme `Z`.
Then `Z` carries an invertible module that is ample relative to the morphism `Z ⟶ Spec K`
induced by the structure morphism.

`Z` is proper over `K` and has dimension at most one
(`AlgebraicGeometry.CurveFamily.dimensionAtPoint_total_le_one_of_base_eq`), hence is Noetherian
and separated, so it has an ample invertible module (Stacks 09NZ). Over the affine base `Spec K`
that module is relatively ample (Stacks 01VK). -/
theorem exists_isRelativelyAmple_reprX_of_base_eq {K : Type u} [Field K]
    (hK : B.Contains (Spec (.of K))) (F : CurveFamily B hZ)
    (hF : F.base = integerSiteObject B hZ hK) (hrep : F.total.obj.IsRepresentable) :
    ∃ (L : ((BigFppfOver.toScheme B integerBase hZ).obj F.total.obj.reprX).Modules)
      (_ : Stacks.Ample.IsInvertibleModule _ L),
      Stacks.RelativeAmple.IsRelativelyAmple ((BigFppfOver.toScheme B integerBase hZ).map
        (yoneda.preimage (F.total.obj.reprW.hom ≫ F.toBase.hom ≫
          (Iso.refl (schemeSpace F.base).obj).hom))) L := by
  have hdim := dimensionAtPoint_total_le_one_of_base_eq hK F hF
  cases F with
  | mk base total toBase hflat hproper hfp hrel => ?_
  change base = _ at hF
  subst hF
  let T : BigFppfOver B integerBase hZ := total.obj.reprX
  let e : schemeSpace T ≅ total :=
    (ObjectProperty.fullyFaithfulι _).preimageIso total.obj.reprW
  let g : T ⟶ integerSiteObject B hZ hK :=
    yoneda.preimage (total.obj.reprW.hom ≫ toBase.hom ≫ (Iso.refl _).hom)
  have hg : yoneda.map g = e.hom.hom ≫ toBase.hom := by
    rw [Functor.map_preimage, Iso.refl_hom]
    exact congrArg (total.obj.reprW.hom ≫ ·) (Category.comp_id toBase.hom)
  let Y : Scheme.{u} := (BigFppfOver.toScheme B integerBase hZ).obj T
  let f : Y ⟶ Spec (.of K) := (BigFppfOver.toScheme B integerBase hZ).map g
  have : IsProper f := by
    refine Space.isProper_toScheme_map_of_isProper_yoneda_map B integerBase hZ g ?_
    rw [hg]
    have : IsIso e.hom.hom := inferInstanceAs (IsIso ((ObjectProperty.ι _).map e.hom))
    exact Space.isProper_comp B integerBase hZ (isAlgebraicSpace_yoneda B integerBase hZ _)
      total.property (isAlgebraicSpace_yoneda B integerBase hZ _) e.hom.hom toBase.hom
      (Space.isProper_of_isIso B integerBase hZ e.hom.hom) hproper
  have : Subsingleton (Spec (.of K)) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have hdimY : topologicalKrullDim (Y : Type u) ≤ 1 := by
    change topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) ≤ 1
    rw [← Space.dimension_yoneda_eq_topologicalKrullDim B integerBase hZ,
      Space.dimension_eq_of_iso B integerBase hZ (isAlgebraicSpace_yoneda B integerBase hZ _)
        total.property ((ObjectProperty.ι _).mapIso e)]
    exact iSup_le hdim
  have : CompactSpace Y := (quasiCompact_iff_compactSpace f).mp inferInstance
  have : IsNoetherian Y :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian f
      toCompactSpace := inferInstance }
  have : Y.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  obtain ⟨L, hL, hamp⟩ :=
    Stacks.AmpleNoetherianDimensionOne.exists_isAmple_of_isNoetherian_of_topologicalKrullDim_le_one
      Y hdimY
  exact ⟨L, hL, (Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple f L).2
    ((Stacks.AmpleBridge.isAmple_iff_isAmple Y L).2 hamp)⟩

/-- **The ample locus of the Picard stack meets every fibre.** For a family of curves `X ⟶ T`
and a point `t` of `T` there are a field `K`, a point `x : Spec K ⟶ T` through `t` and an object
`A` of `Picardstack_{X/T}` over the test scheme `x` whose module is ample on `X_x` relative to
`X_x ⟶ Spec K` (Stacks 0D31).

`K` is the residue field at `t`. The module is an ample module on the scheme representing the
fibre `X_x` (`AlgebraicGeometry.CurveFamily.exists_isRelativelyAmple_reprX_of_base_eq`), moved to
the algebraic space `X_x` by
`AlgebraicGeometry.Space.exists_isInvertibleModule_isRelativelyAmple_of_presentation`. -/
theorem exists_picardObject_isInAmpleLocus_of_point (X : CurveFamily B hZ)
    (t : (BigFppfOver.toScheme B integerBase hZ).obj X.base) :
    ∃ (K : Type u) (_ : Field K) (hK : B.Contains (Spec (.of K)))
      (x : (schemeOverIntegers B).obj (B.obj hK) ⟶ X.base),
      t ∈ Set.range ((BigFppfOver.toScheme B integerBase hZ).map x) ∧
      ∃ A : Space.PicardObject X.picardSituation, A.T = X.picardTestScheme x ∧
        A.IsInAmpleLocus := by
  let Y₀ := (BigFppfOver.toScheme B integerBase hZ).obj X.base
  have hK : B.Contains (Spec (.of (Y₀.residueField t))) :=
    B.residueField_spec_contains X.base.left.property t
  let x : (schemeOverIntegers B).obj (B.obj hK) ⟶ X.base :=
    Over.homMk (B.inclusion.preimage (Y₀.fromSpecResidueField t))
      (ObjectProperty.hom_ext _ (specULiftZIsTerminal.hom_ext _ _))
  refine ⟨Y₀.residueField t, inferInstance, hK, x, ?_, ?_⟩
  · have hx : (BigFppfOver.toScheme B integerBase hZ).map x = Y₀.fromSpecResidueField t :=
      B.inclusion.map_preimage _
    rw [hx]
    obtain ⟨p⟩ : Nonempty (Spec (Y₀.residueField t)) := inferInstance
    exact ⟨p, Scheme.fromSpecResidueField_apply t _⟩
  · let F := X.baseChange x
    have hF : F.base = integerSiteObject B hZ hK := rfl
    have hrep := F.isRepresentable_total_of_base_eq (K := Y₀.residueField t)
      (congrArg (BigFppfOver.toScheme B integerBase hZ).obj hF)
    obtain ⟨L, hL, hamp⟩ := exists_isRelativelyAmple_reprX_of_base_eq hK F hF hrep
    obtain ⟨N, hN, hNamp, -⟩ := Space.exists_isInvertibleModule_isRelativelyAmple_of_presentation
      (Space.baseChangeInclusion X.toBase (X.picardTestScheme x)) F.base (Iso.refl _)
      F.total.obj.reprX F.total.obj.reprW L hamp
    exact ⟨⟨X.picardTestScheme x, N, hN⟩, rfl, hNamp⟩

end CurveFamily

end AlgebraicGeometry

end
