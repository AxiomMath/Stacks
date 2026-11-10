module

public import StacksCore.Tactic.StacksAttribute
public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedCurves
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyRelativeDimension
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveOnObjects
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowTwistWitness
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.Dimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.DimensionSemicontinuity
public import StacksFrontier.AlgebraicGeometry.AmpleNoetherianDimensionOne.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeAmpleAffineBase.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleBridge.Basic

/-!
# Every curve over a field is polarized (the surjectivity half of Stacks 0DQ0)

Stacks 0DQ0 says that the projection `PolarizedCurves ⟶ 𝒞urves` is smooth and surjective. The
surjectivity half of its proof runs as follows. An object of `𝒞urves` over a field `k` is a
proper algebraic space `X` over `k` of dimension at most one. By Stacks 0ADD it is a scheme, so
it is a proper scheme of dimension at most one over `k`, which has an ample invertible module
`ℒ` (Stacks 0A26). Then `(X, ℒ)` is an object of `PolarizedCurves` over `k` mapping to `X`.

This file carries out the second half of that argument: once the total space of a family of
curves over a field is known to be a scheme of dimension at most one, the family carries a
polarization. That is
`AlgebraicGeometry.CurveFamily.exists_polarizedFamily_of_base_eq`. Its two inputs — that the
total space is representable and that it has dimension at most one at each point — are the
conclusions of `AlgebraicGeometry.CurveFamily.isRepresentable_total_of_base_eq` (Stacks 0ADD) and
`AlgebraicGeometry.CurveFamily.dimensionAtPoint_total_le_one_of_base_eq`; they are taken here, in
exactly the shape of those two statements, as explicit hypotheses. The ample module comes from
Stacks 09NZ, the input from which Stacks 0A26 itself is proved, in the form of
`isProjectiveMorphism_of_isProper_of_topologicalKrullDim_le_one` in the namespace
`Stacks.HQuasiProjectiveDimensionOne`. Over the affine base `Spec k` an ample module is relatively
ample by Stacks 01VK.

`AlgebraicGeometry.isSurjectiveOnObjects_polarizedCurvesSquare_snd` assembles the result as
surjectivity on objects (Stacks 06D4) of the projection of the canonical 2-fibre product of
Stacks 0DPY to `𝒞urves`. An object over a field spectrum is first pulled back to the
representative field spectrum `Spec k` of the site, and then the polarization above is
attached.

No tag is registered in this file. Stacks 0DQ0 is stated for morphisms of algebraic stacks,
which needs `𝒞urves` and `PolarizedCurves` to be algebraic (Stacks 0D5A, 0D4X), and its
smoothness half needs Stacks 0D04, 0DPJ and 0D3D.

## Main results

* `AlgebraicGeometry.CurveFamily.exists_polarizedFamily_of_base_eq`: a family of curves over
  `Spec k` whose total space is a scheme of dimension at most one is the image of a polarized
  family, through an isomorphism lying over the identity of `Spec k`.
* `AlgebraicGeometry.isSurjectiveOnObjects_polarizedCurvesSquare_snd`: the projection
  `PolarizedCurves ⟶ 𝒞urves` is surjective on objects.

## References

* [Stacks Project, Tag 0DQ0](https://stacks.math.columbia.edu/tag/0DQ0)
* [Stacks Project, Tag 0ADD](https://stacks.math.columbia.edu/tag/0ADD)
* [Stacks Project, Tag 0A26](https://stacks.math.columbia.edu/tag/0A26)
* [Stacks Project, Tag 09NZ](https://stacks.math.columbia.edu/tag/09NZ)
* [Stacks Project, Tag 01VK](https://stacks.math.columbia.edu/tag/01VK)
* [Stacks Project, Tag 06D4](https://stacks.math.columbia.edu/tag/06D4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

namespace CurveFamily

/-- **A family of curves over a field whose total space is a scheme carries a polarization.**
Let `F` be a family of curves over the spectrum of a field `K`, whose total space is
representable and has dimension at most one at each point. Then there is a polarized family `P`
over `Spec K` and an isomorphism from the family of algebraic spaces underlying `P` to the one
underlying `F`, lying over the identity of `Spec K`.

The total space is a proper scheme `Y` of dimension at most one over `K`. It is Noetherian and
separated, so it has an ample invertible module (Stacks 09NZ), which is relatively ample over the
affine base `Spec K` (Stacks 01VK). -/
theorem exists_polarizedFamily_of_base_eq {K : Type u} [Field K]
    (hK : B.Contains (Spec (.of K))) (F : CurveFamily B hZ)
    (hF : F.base = (schemeOverIntegers B).obj (B.obj hK))
    (hrep : F.total.obj.IsRepresentable)
    (hdim : ∀ x : Space.points B integerBase hZ F.total.obj,
      Space.dimensionAtPoint B integerBase hZ F.total.obj F.total.property x ≤ 1) :
    ∃ (P : PolarizedFamily B)
      (φ : (forgetPolarization B).obj P ≅ (curvesToCartesianProperFlat B hZ).obj F),
      (schemeOverIntegers B).obj P.base = F.base ∧
        (cartesianProperFlatProjection B integerBase hZ).IsHomLift (𝟙 F.base) φ.hom := by
  cases F with
  | mk base total toBase hflat hproper hfp hrel => ?_
  change base = _ at hF
  subst hF
  -- the total space as a scheme of the site, and the structure morphism
  let T : BigFppfOver B integerBase hZ := total.obj.reprX
  let e : schemeSpace T ≅ total :=
    (ObjectProperty.fullyFaithfulι _).preimageIso total.obj.reprW
  let g : T ⟶ (schemeOverIntegers B).obj (B.obj hK) := yoneda.preimage (e.hom.hom ≫ toBase.hom)
  have hg : yoneda.map g = e.hom.hom ≫ toBase.hom := yoneda.map_preimage _
  let Y : Scheme.{u} := (BigFppfOver.toScheme B integerBase hZ).obj T
  let f : Y ⟶ Spec (.of K) := (BigFppfOver.toScheme B integerBase hZ).map g
  have hproperY : IsProper f := by
    refine Space.isProper_toScheme_map_of_isProper_yoneda_map B integerBase hZ g ?_
    rw [hg]
    have : IsIso e.hom.hom := inferInstanceAs (IsIso ((ObjectProperty.ι _).map e.hom))
    exact Space.isProper_comp B integerBase hZ (isAlgebraicSpace_yoneda B integerBase hZ _)
      total.property (isAlgebraicSpace_yoneda B integerBase hZ _) e.hom.hom toBase.hom
      (Space.isProper_of_isIso B integerBase hZ e.hom.hom) hproper
  have := hproperY
  have : Subsingleton (Spec (.of K)) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have : IsLocallyNoetherian (Spec (.of K)) := inferInstance
  have : Flat f := inferInstance
  have : LocallyOfFinitePresentation f := inferInstance
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
  -- the polarization
  obtain ⟨L, hL, hamp⟩ :=
    Stacks.AmpleNoetherianDimensionOne.exists_isAmple_of_isNoetherian_of_topologicalKrullDim_le_one
      Y hdimY
  have : Stacks.Ample.IsInvertibleModule Y L := hL
  have hrelY : Stacks.RelativeAmple.IsRelativelyAmple f L :=
    (Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple f L).2
      ((Stacks.AmpleBridge.isAmple_iff_isAmple Y L).2 hamp)
  let P : PolarizedFamily B :=
    { base := B.obj hK
      total := Y
      toBase := f
      proper := hproperY
      flat := inferInstance
      finitePresentation := ⟨inferInstance, inferInstance, inferInstance⟩
      lineBundle := L
      invertible := hL
      relativelyAmple := hrelY }
  -- the polarized family read as a family of curves
  have hP := P.isProperFlat_yoneda_structureMapOverIntegers
  let G : CurveFamily B hZ :=
    { base := (schemeOverIntegers B).obj (B.obj hK)
      total := schemeSpace ((schemeOverIntegers B).obj P.totalObj)
      toBase := schemeSpaceMap P.structureMapOverIntegers
      flat := hP.2.1
      proper := hP.2.2
      finitePresentation := hP.1
      relativeDimensionLE :=
        Space.relativeDimensionLE_schemeSpaceMap B integerBase hZ
          P.structureMapOverIntegers 1
          (by change topologicalKrullDim (Y : Type u) ≤ _; simpa using hdimY) }
  -- the comparison of the two total spaces
  let ι : (schemeOverIntegers B).obj P.totalObj ≅ T :=
    Over.isoMk (Iso.refl _) (ObjectProperty.hom_ext _ (specULiftZIsTerminal.hom_ext _ _))
  have hιg : ι.hom ≫ g = P.structureMapOverIntegers := by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    rfl
  let τ : G.total ⟶ total := schemeSpaceMap ι.hom ≫ e.hom
  have : IsIso (schemeSpaceMap ι.hom) :=
    inferInstanceAs (IsIso ((schemeSpaceFunctor B integerBase hZ).map ι.hom))
  have : IsIso τ := inferInstance
  have hid : schemeSpaceMap (𝟙 ((schemeOverIntegers B).obj (B.obj hK))) = 𝟙 _ :=
    (schemeSpaceFunctor B integerBase hZ).map_id _
  have : IsIso (schemeSpaceMap (𝟙 ((schemeOverIntegers B).obj (B.obj hK)))) := by
    rw [hid]; infer_instance
  have hw : τ ≫ toBase = G.toBase ≫ schemeSpaceMap (𝟙 _) := by
    rw [hid, Category.comp_id]
    apply ObjectProperty.hom_ext
    change yoneda.map ι.hom ≫ e.hom.hom ≫ toBase.hom = yoneda.map P.structureMapOverIntegers
    rw [← hιg, Functor.map_comp]
    exact congrArg (yoneda.map ι.hom ≫ ·) hg.symm
  let h : G ⟶ ⟨(schemeOverIntegers B).obj (B.obj hK), total, toBase, hflat, hproper, hfp, hrel⟩ :=
    { baseMap := 𝟙 _
      totalMap := τ
      cartesian := IsPullback.of_horiz_isIso ⟨hw⟩ }
  have hlift : (curvesProjectionOver B hZ).IsHomLift
      (𝟙 ((schemeOverIntegers B).obj (B.obj hK))) h :=
    inferInstanceAs ((curvesProjectionOver B hZ).IsHomLift ((curvesProjectionOver B hZ).map h) h)
  have := hlift
  have hp : (curvesProjectionOver B hZ).IsFiberedInGroupoids :=
    (curvesFiberedCategory B hZ).isFiberedInGroupoids
  have := hp.isStronglyCartesian_homLift (𝟙 ((schemeOverIntegers B).obj (B.obj hK))) h
  have : IsIso h := Functor.IsStronglyCartesian.isIso_of_base_isIso
    (curvesProjectionOver B hZ) (𝟙 ((schemeOverIntegers B).obj (B.obj hK))) h
  have hiso : IsIso ((curvesToCartesianProperFlat B hZ).map h) := Functor.map_isIso _ h
  refine ⟨P, @asIso _ _ _ _ ((curvesToCartesianProperFlat B hZ).map h) hiso, rfl, ?_⟩
  exact inferInstanceAs ((cartesianProperFlatProjection B integerBase hZ).IsHomLift
    ((cartesianProperFlatProjection B integerBase hZ).map
      ((curvesToCartesianProperFlat B hZ).map h))
    ((curvesToCartesianProperFlat B hZ).map h))

end CurveFamily

/-- **The projection `PolarizedCurves ⟶ 𝒞urves` is surjective on objects** (Stacks 06D4), given
that the total space of every family of curves over a field is a scheme of dimension at most
one. Those two inputs are the conclusions of
`AlgebraicGeometry.CurveFamily.isRepresentable_total_of_base_eq` (Stacks 0ADD) and
`AlgebraicGeometry.CurveFamily.dimensionAtPoint_total_le_one_of_base_eq`, stated
here in their exact shape.

An object of `𝒞urves` over the spectrum of a field `k` is pulled back to the representative
field spectrum `Spec k` of the site, which is again a field object; there
`AlgebraicGeometry.CurveFamily.exists_polarizedFamily_of_base_eq` polarizes it. The polarized
family, the family of curves and the comparison isomorphism form an object of the 2-fibre
product whose second projection is the pulled-back family. -/
theorem isSurjectiveOnObjects_polarizedCurvesSquare_snd
    (h3Z : (polarizedProjection B ⋙ schemeOverIntegers B).IsFiberedInGroupoids)
    (hrep : ∀ (K : Type u) [Field K] (hK : B.Contains (Spec (.of K))) (F : CurveFamily B hZ),
      F.base = (schemeOverIntegers B).obj (B.obj hK) → F.total.obj.IsRepresentable)
    (hdim : ∀ (K : Type u) [Field K] (hK : B.Contains (Spec (.of K))) (F : CurveFamily B hZ),
      F.base = (schemeOverIntegers B).obj (B.obj hK) →
        ∀ x : Space.points B integerBase hZ F.total.obj,
          Space.dimensionAtPoint B integerBase hZ F.total.obj F.total.property x ≤ 1) :
    Stack.IsSurjectiveOnObjects B integerBase hZ
      (polarizedCurvesFiberedCategory B hZ h3Z).val.p (curvesFiberedCategory B hZ).val.p
      (CatFiberedInGroupoids.homFunctor (polarizedCurvesSquare B hZ h3Z).snd) := by
  intro U ⟨k, hk, ⟨i⟩⟩ y hy
  let : Field k := hk
  have hK : B.Contains (Spec (.of k)) := by
    have hb : ((BigFppfOver.toScheme B integerBase hZ).obj U).size < B.cutoff := U.left.2
    rwa [Scheme.size_congr i] at hb
  let V : BigFppfOver B integerBase hZ := (schemeOverIntegers B).obj (B.obj hK)
  let f : V ⟶ U := Over.homMk (B.inclusion.preimage i.inv)
    (ObjectProperty.hom_ext _ (specULiftZIsTerminal.hom_ext _ _))
  obtain ⟨F, α, hα⟩ := (curvesFiberedCategory B hZ).isFiberedInGroupoids.exists_lift f y hy
  have hF : F.base = V := IsHomLift.domain_eq (curvesFiberedCategory B hZ).val.p f α
  obtain ⟨P, φ, hPb, hφ⟩ :=
    CurveFamily.exists_polarizedFamily_of_base_eq hK F hF (hrep k hK F hF) (hdim k hK F hF)
  refine ⟨V, ⟨k, hk, ⟨Iso.refl _⟩⟩, f,
    { base := F.base, x := P, y := F, hx := hPb, hy := rfl, iso := φ, vertical := hφ },
    hF, α, hα⟩

end AlgebraicGeometry

end
