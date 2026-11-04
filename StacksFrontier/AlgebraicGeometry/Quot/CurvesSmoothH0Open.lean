module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesFieldFibreGlobalFunctionsOpen
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesH01Inputs
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesSmoothH0
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesPrestableOpen
public import StacksFrontier.AlgebraicGeometry.Quot.ModuliCurves
public import StacksFrontier.AlgebraicGeometry.Quot.SmoothProperCurveOverField
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFlatStructureSheafPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.FibreBettiZeroGlobalFunctions

/-!
# The open substack `Curves^{smooth,h0}` of the stack of curves (Stacks 0E81)

Stacks 0E81 cuts out of the stack of curves the open substack `Curves^{smooth,h0}` of families of
curves `f : X → S` which are smooth of relative dimension `1` with `f_*𝒪_X = 𝒪_S`, this holding
after any base change: the property `AlgebraicGeometry.IsSmoothH0Family`.

## Main results

* `AlgebraicGeometry.isSmoothH0Family_iff_isH01CurveFamily_and_isSmoothDimOneFamily`:
  `Curves^{smooth,h0} = Curves^{h0,1} ∩ Curves^{smooth,1}`, objectwise.
* `AlgebraicGeometry.isOpenCurvesLocus_isSmoothH0Family_of`: condition (o) of Section 0E0E for
  `Curves^{smooth,h0}`, from condition (o) for `Curves^{h0,1}`.
* `AlgebraicGeometry.isSmoothH0Family_curveFamilyOfSchemeMorphism_iff_of`: condition (2)(b) on
  the family of a proper scheme over a field.
* `AlgebraicGeometry.curvesSmoothH0Family_isOpenSubstack_and_factors_iff_and_tfae_of`: the whole
  statement of Stacks 0E81, from condition (o) for `Curves^{h0,1}`.
* `AlgebraicGeometry.curvesSmoothH0_isOpenSubstack_and_factors_iff_and_tfae`: **Stacks 0E81**.

## Implementation notes

Stacks 0E81 (1)(a) reads "the classifying morphism factors through `Curves^{smooth}`"; the
substack meant is `Curves^{smooth,h0}`, the one the lemma constructs (with `Curves^{smooth}` the
equivalence would be false: a smooth proper family with disconnected fibres factors through
`Curves^{smooth}`). The formal statement uses `Curves^{smooth,h0}`.

"`f_*𝒪_X = 𝒪_S`, this holds after any base change" is
`AlgebraicGeometry.HasUniversallyBijectiveGlobalFunctions`: after every base change along an
algebraic space over the base, pullback of global functions along the projection is bijective.

## References

* [Stacks Project, Tag 0E81](https://stacks.math.columbia.edu/tag/0E81)
* [Stacks Project, Tag 0E6I](https://stacks.math.columbia.edu/tag/0E6I)
* [Stacks Project, Tag 0DZZ](https://stacks.math.columbia.edu/tag/0DZZ)
* [Stacks Project, Tag 0E0E](https://stacks.math.columbia.edu/tag/0E0E)
* [Stacks Project, Tag 0FD3](https://stacks.math.columbia.edu/tag/0FD3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- **`Curves^{smooth,h0} = Curves^{h0,1} ∩ Curves^{smooth,1}`, objectwise.** A family is smooth
of relative dimension `1` with `f_*𝒪_X = 𝒪_S` universally exactly when it lies in
`Curves^{h0,1}` (`f_*𝒪_X = 𝒪_S` universally and fibres of dimension `1`) and is smooth of
relative dimension `1`. -/
theorem isSmoothH0Family_iff_isH01CurveFamily_and_isSmoothDimOneFamily (X : CurveFamily B hZ) :
    IsSmoothH0Family B hZ X ↔ IsH01CurveFamily B hZ X ∧ IsSmoothDimOneFamily B hZ X :=
  ⟨fun h => ⟨⟨h.2,
      CurveFamily.hasFibresOfDimensionOne_of_hasRelativeDimension_one h.1.2
        (CurveFamily.exists_point_over_of_hasUniversallyBijectiveGlobalFunctions h.2)⟩, h.1⟩,
    fun h => ⟨h.2, h.1.1⟩⟩

/-- If `Curves^{h0,1}` satisfies condition (o) of Section 0E0E, then so does
`Curves^{smooth,h0}`. -/
theorem isOpenCurvesLocus_isSmoothH0Family_of
    (hH01 : IsOpenCurvesLocus B hZ (IsH01CurveFamily B hZ)) :
    IsOpenCurvesLocus B hZ (IsSmoothH0Family B hZ) := by
  intro G
  obtain ⟨W, hW, hchar⟩ :=
    (hH01.and fun G => CurveFamily.exists_isOpenSubspace_smoothDimOne B hZ G) G
  exact ⟨W, hW, fun F a =>
    (isSmoothH0Family_iff_isH01CurveFamily_and_isSmoothDimOneFamily F).trans (hchar F a)⟩

/-! ### Part (2): a proper scheme of dimension at most one over a field -/

section OverField

variable {T W : BigFppfOver B integerBase hZ} (g : T ⟶ W)
  (k : Type u) [Field k] (hW : (BigFppfOver.toScheme B integerBase hZ).obj W = Spec (.of k))
  (hflat : Flat ((BigFppfOver.toScheme B integerBase hZ).map g))
  (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map g))
  (hlfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B integerBase hZ).map g))
  (hqc : Space.IsQuasiCompact B integerBase hZ (schemeSpaceMap g).hom)
  (hsep : Space.IsSeparated B integerBase hZ (schemeSpaceMap g).hom)
  (hqsep : Space.IsQuasiSeparated B integerBase hZ (schemeSpaceMap g).hom)
  (hdim : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) ≤ 1)

include hW in
/-- **Condition (2)(b) of Stacks 0E81 on a proper scheme over a field.** For the family of
curves of a proper scheme `X = T` of dimension at most one over a field `k = W`, given that
`f_*𝒪_X = 𝒪_S` universally is, for this family, `H⁰(X, 𝒪_X) = H⁰(Spec k, 𝒪)`, the family is in
`Curves^{smooth,h0}` exactly when `X` is smooth over `k`, `dim X = 1` and `k = H⁰(X, 𝒪_X)`. -/
theorem isSmoothH0Family_curveFamilyOfSchemeMorphism_iff_of
    (hUB : HasUniversallyBijectiveGlobalFunctions B hZ
        (curveFamilyOfSchemeMorphism B hZ g hflat hproper hlfp hqc hsep hqsep hdim) ↔
      Function.Bijective ((BigFppfOver.toScheme B integerBase hZ).map g).appTop) :
    IsSmoothH0Family B hZ
        (curveFamilyOfSchemeMorphism B hZ g hflat hproper hlfp hqc hsep hqsep hdim) ↔
      Smooth ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW) ∧
        topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) = 1 ∧
        IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫
          ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW).appTop) := by
  have := hproper
  let f := (BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW
  have hsm : Smooth f ↔ Smooth ((BigFppfOver.toScheme B integerBase hZ).map g) := by
    refine ⟨fun _ => ?_, fun _ => inferInstance⟩
    rw [show (BigFppfOver.toScheme B integerBase hZ).map g = f ≫ eqToHom hW.symm by simp [f]]
    infer_instance
  have hbij : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) ↔
      Function.Bijective ((BigFppfOver.toScheme B integerBase hZ).map g).appTop := by
    have : IsIso (eqToHom hW).appTop :=
      inferInstanceAs (IsIso (Scheme.Γ.map (eqToHom hW).op))
    rw [Scheme.Hom.comp_appTop, ← Category.assoc, isIso_comp_left_iff,
      ConcreteCategory.isIso_iff_bijective]
  have key := fun hi => isSmoothDimOneFamily_curveFamilyOfSchemeMorphism_iff B hZ g hflat hproper
    hlfp hqc hsep hqsep hdim k hW (nonempty_of_isIso_globalSections_comp_eqToHom g k hW hi)
  constructor
  · rintro ⟨hS, hU⟩
    have hi := hbij.mpr (hUB.mp hU)
    have h := (key hi).mp hS
    exact ⟨hsm.mpr h.1, h.2.2, hi⟩
  · rintro ⟨hs, hd, hi⟩
    have : IsProper f := by dsimp only [f]; infer_instance
    have h13 := (smoothProperCurve_tfae k f (AlgebraicClosure k)).out 1 3
    have : GeometricallyIntegral f := (h13.mp ⟨hs, hd, hi⟩).2.2
    have : IsIntegral ((BigFppfOver.toScheme B integerBase hZ).obj T) :=
      GeometricallyIntegral.isIntegral_of_subsingleton f
    refine ⟨(key hi).mpr ⟨hsm.mp hs, ?_, hd⟩, hUB.mpr (hbij.mp hi)⟩
    exact TopologicalSpace.Equidimensional.of_preirreducibleSpace _

end OverField

/-! ### The open substack `Curves^{smooth,h0}` -/

variable (B hZ) in
/-- **Stacks 0E81, from condition (o) for `Curves^{h0,1}` (Stacks 0E6I).** Given that
`Curves^{h0,1}` satisfies condition (o) of Section 0E0E, `𝓜 = Curves^{smooth,h0} ⊂ Curves` is an
open substack (its inclusion is representable by algebraic spaces and an open immersion), part
(1) of the source holds, and so do the five equivalences of part (2). -/
theorem curvesSmoothH0Family_isOpenSubstack_and_factors_iff_and_tfae_of
    (hH01 : IsOpenCurvesLocus B hZ (IsH01CurveFamily B hZ)) :
    ((ObjectProperty.IsClosedUnderIsomorphisms (IsSmoothH0Family B hZ) ∧
      Stack.IsRepresentableByAlgebraicSpaces B integerBase hZ
        (moduliSmoothCurvesInclusion B hZ).hom ∧
      Stack.IsOpenImmersion B integerBase hZ (moduliSmoothCurvesInclusion B hZ)) ∧
    ∀ (U : BigFppfOver B integerBase hZ)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ),
      y ⋙ curvesProjectionOver B hZ = Over.map U.hom →
      ((∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
          ObjectProperty.FullSubcategory (IsSmoothH0Family B hZ),
          z ⋙ ObjectProperty.ι (IsSmoothH0Family B hZ) = y) ↔
        IsSmoothH0Family B hZ (y.obj (Over.mk (𝟙 U.left))))) ∧
    ∀ {T W : BigFppfOver B integerBase hZ} (g : T ⟶ W) (k : Type u) [Field k]
      (hW : (BigFppfOver.toScheme B integerBase hZ).obj W = Spec (.of k))
      (hflat : Flat ((BigFppfOver.toScheme B integerBase hZ).map g))
      (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map g))
      (hlfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B integerBase hZ).map g))
      (hqc : Space.IsQuasiCompact B integerBase hZ (schemeSpaceMap g).hom)
      (hsep : Space.IsSeparated B integerBase hZ (schemeSpaceMap g).hom)
      (hqsep : Space.IsQuasiSeparated B integerBase hZ (schemeSpaceMap g).hom)
      (hdim : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) ≤ 1)
      (y : BigFppfOver B W.left.1 W.left.2 ⥤ CurveFamily B hZ)
      (_hy : y ⋙ curvesProjectionOver B hZ = Over.map W.hom)
      (_e : y.obj (Over.mk (𝟙 W.left)) ≅
        curveFamilyOfSchemeMorphism B hZ g hflat hproper hlfp hqc hsep hqsep hdim),
      List.TFAE [
        ∃ z : BigFppfOver B W.left.1 W.left.2 ⥤
            ObjectProperty.FullSubcategory (IsSmoothH0Family B hZ),
          z ⋙ ObjectProperty.ι (IsSmoothH0Family B hZ) = y,
        Smooth ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW) ∧
          topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) = 1 ∧
          IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫
            ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW).appTop),
        Smooth ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW) ∧
          topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) = 1 ∧
          GeometricallyConnected ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW),
        Smooth ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW) ∧
          topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) = 1 ∧
          GeometricallyIntegral ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW),
        Smooth (pullback.snd ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW)
            (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))) ∧
          IsCurve (AlgebraicClosure k)
            (pullback.snd ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW)
              (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))))] := by
  have hP : IsOpenCurvesLocus B hZ (IsSmoothH0Family B hZ) :=
    isOpenCurvesLocus_isSmoothH0Family_of hH01
  refine ⟨isOpenImmersion_curvesSubstackInclusion_and_factors_iff hP, ?_⟩
  intro T W g k _ hW hflat hproper hlfp hqc hsep hqsep hdim y hy e
  have := hproper
  rw [List.tfae_cons_cons]
  refine ⟨(factors_curvesSubstack_iff_of_iso hP W y hy _ e).trans
    (isSmoothH0Family_curveFamilyOfSchemeMorphism_iff_of g k hW hflat hproper hlfp hqc hsep hqsep
      hdim (CurveFamily.hasUniversallyBijectiveGlobalFunctions_curveFamilyOfSchemeMorphism_iff_of
        CurveFamily.hasUniversallyBijectiveGlobalFunctions_of_fieldFibres g k hW hflat hproper hlfp
          hqc hsep hqsep hdim)), ?_⟩
  exact smoothProperCurve_tfae k _ (AlgebraicClosure k)

variable (B hZ) in
/-- There is an open substack `Curves^{smooth,h0} ⊂ Curves` — the moduli stack
`𝓜 = AlgebraicGeometry.moduliSmoothCurves` of Stacks 0E82, the strictly full subcategory of
families of curves satisfying `AlgebraicGeometry.IsSmoothH0Family`; its inclusion
`AlgebraicGeometry.moduliSmoothCurvesInclusion` is representable by algebraic spaces and an open
immersion — such that:

1. for a family of curves `f : X → S`, classified by a scheme-valued point `y` of `Curves` over
   `S`, the classifying morphism factors through `Curves^{smooth,h0}` exactly when
   `f_*𝒪_X = 𝒪_S`, this holding after any base change, and `f` is smooth of relative dimension
   `1` (`IsSmoothH0Family` of the family `y(S)`);
2. for a scheme `X = T` proper over a field `k = W` with `dim X ≤ 1`, classified by `y` over
   `Spec k`, the following are equivalent: (a) the classifying morphism factors through
   `Curves^{smooth,h0}`; (b) `X` is smooth, `dim X = 1` and `k = H⁰(X, 𝒪_X)`; (c) `X` is smooth,
   `dim X = 1` and geometrically connected; (d) `X` is smooth, `dim X = 1` and geometrically
   integral; (e) `X_{k̄}` is a smooth curve over an algebraic closure `k̄` of `k`.

Part (1)(a) of the source says "factors through `Curves^{smooth}`"; the substack meant is the one
constructed, `Curves^{smooth,h0}` (see the module documentation). -/
@[stacks 0E81 "the open substack Curves^{smooth,h0} (the moduli stack M of 0E82), its family \
characterization (1) and the five equivalent conditions (2) over a field"]
theorem curvesSmoothH0_isOpenSubstack_and_factors_iff_and_tfae :
    ((ObjectProperty.IsClosedUnderIsomorphisms (IsSmoothH0Family B hZ) ∧
      Stack.IsRepresentableByAlgebraicSpaces B integerBase hZ
        (moduliSmoothCurvesInclusion B hZ).hom ∧
      Stack.IsOpenImmersion B integerBase hZ (moduliSmoothCurvesInclusion B hZ)) ∧
    ∀ (U : BigFppfOver B integerBase hZ)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ),
      y ⋙ curvesProjectionOver B hZ = Over.map U.hom →
      ((∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
          ObjectProperty.FullSubcategory (IsSmoothH0Family B hZ),
          z ⋙ ObjectProperty.ι (IsSmoothH0Family B hZ) = y) ↔
        IsSmoothH0Family B hZ (y.obj (Over.mk (𝟙 U.left))))) ∧
    ∀ {T W : BigFppfOver B integerBase hZ} (g : T ⟶ W) (k : Type u) [Field k]
      (hW : (BigFppfOver.toScheme B integerBase hZ).obj W = Spec (.of k))
      (hflat : Flat ((BigFppfOver.toScheme B integerBase hZ).map g))
      (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map g))
      (hlfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B integerBase hZ).map g))
      (hqc : Space.IsQuasiCompact B integerBase hZ (schemeSpaceMap g).hom)
      (hsep : Space.IsSeparated B integerBase hZ (schemeSpaceMap g).hom)
      (hqsep : Space.IsQuasiSeparated B integerBase hZ (schemeSpaceMap g).hom)
      (hdim : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) ≤ 1)
      (y : BigFppfOver B W.left.1 W.left.2 ⥤ CurveFamily B hZ)
      (_hy : y ⋙ curvesProjectionOver B hZ = Over.map W.hom)
      (_e : y.obj (Over.mk (𝟙 W.left)) ≅
        curveFamilyOfSchemeMorphism B hZ g hflat hproper hlfp hqc hsep hqsep hdim),
      List.TFAE [
        ∃ z : BigFppfOver B W.left.1 W.left.2 ⥤
            ObjectProperty.FullSubcategory (IsSmoothH0Family B hZ),
          z ⋙ ObjectProperty.ι (IsSmoothH0Family B hZ) = y,
        Smooth ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW) ∧
          topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) = 1 ∧
          IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫
            ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW).appTop),
        Smooth ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW) ∧
          topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) = 1 ∧
          GeometricallyConnected ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW),
        Smooth ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW) ∧
          topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) = 1 ∧
          GeometricallyIntegral ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW),
        Smooth (pullback.snd ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW)
            (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))) ∧
          IsCurve (AlgebraicClosure k)
            (pullback.snd ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW)
              (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))))] :=
  curvesSmoothH0Family_isOpenSubstack_and_factors_iff_and_tfae_of B hZ
    CurveFamily.isOpenCurvesLocus_isH01CurveFamily

end AlgebraicGeometry

end
