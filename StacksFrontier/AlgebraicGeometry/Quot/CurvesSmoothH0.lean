module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesH01
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesPrestableOpen
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesSmooth
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.DimensionSemicontinuity
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.DimensionUpperSemicontinuity
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionChart
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.SmoothProperCurveCriteria

/-!
# The open substack `Curves^{smooth,h0}` of the stack of curves (towards Stacks 0E81)

Stacks 0E81 cuts out of the stack of curves the open substack `Curves^{smooth,h0}` of families of
curves `f : X → S` with `f_*𝒪_X = 𝒪_S`, universally, and `f` smooth of relative dimension `1`.
Its proof is the identity `Curves^{smooth,h0} = Curves^{smooth} ∩ Curves^{h0,1}` (the source
writes `Curves^{smooth}`; the relative dimension `1` comes from `Curves^{h0,1}`, whose fibres
have dimension `1`), with the openness of the two substacks on the right given by Stacks 0DZZ and
Stacks 0E6I, and the method of Section 0E0E. For a proper scheme `X` over a field `k` the
condition becomes "`X` smooth, `dim X = 1`, `H⁰(X, 𝒪_X) = k`", and this is equivalent to the
three further conditions of part (2) by Stacks 0FD3
(`AlgebraicGeometry.smooth_dimOne_tfae_geometricallyConnected_isCurve_algebraicClosure`).

## Main definitions

* `AlgebraicGeometry.IsSmoothH0CurveFamily`: `f_*𝒪_X = 𝒪_S` universally and `f` smooth of
  relative dimension `1`, condition (1)(b) of Stacks 0E81.

## Main results

* `AlgebraicGeometry.CurveFamily.hasFibresOfDimensionOne_of_hasRelativeDimension_one`: a
  surjective family of relative dimension `1` has fibres of dimension `1`.
* `AlgebraicGeometry.isOpenCurvesLocus_isSmoothDimOneFamily`: condition (o) of Section 0E0E for
  smoothness of relative dimension `1`, from Stacks 0DZZ.
* `AlgebraicGeometry.isOpenCurvesLocus_isSmoothH0CurveFamily_of`: condition (o) for
  `Curves^{smooth,h0}`, from condition (o) for `Curves^{h0,1}`.
* `AlgebraicGeometry.isSmoothH0CurveFamily_curveFamilyOfSchemeMorphism_iff_of`: the condition on
  the family of a proper scheme over a field is condition (2)(b).

## Implementation notes

The inputs from Stacks 0E6I enter as explicit hypotheses, in the exact form the 0E6I files of this
development state them; nothing here is registered.

## References

* [Stacks Project, Tag 0E81](https://stacks.math.columbia.edu/tag/0E81)
* [Stacks Project, Tag 0E6I](https://stacks.math.columbia.edu/tag/0E6I)
* [Stacks Project, Tag 0DZZ](https://stacks.math.columbia.edu/tag/0DZZ)
* [Stacks Project, Tag 0E0E](https://stacks.math.columbia.edu/tag/0E0E)
* [Stacks Project, Tag 0FD3](https://stacks.math.columbia.edu/tag/0FD3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

attribute [local instance] Space.pointTopology

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- **Condition (1)(b) of Stacks 0E81.** A family of curves `f : X → S` with `f_*𝒪_X = 𝒪_S`, this
holding after any base change, and `f` smooth of relative dimension `1`. -/
abbrev IsSmoothH0CurveFamily (X : CurveFamily B hZ) : Prop :=
  HasUniversallyBijectiveGlobalFunctions B hZ X ∧ IsSmoothDimOneFamily B hZ X

variable {B hZ}

namespace CurveFamily

/-- **A surjective family of relative dimension `1` has fibres of dimension `1`.** Every fibre is
nonempty, and at each of its points the relative dimension is `1`, so the infimum defining the
fibre dimension is `1`. -/
theorem hasFibresOfDimensionOne_of_hasRelativeDimension_one {X : CurveFamily B hZ}
    (hrel : Space.HasRelativeDimension 1 B integerBase hZ X.toBase.hom)
    (hsurj : ∀ s : Space.points B integerBase hZ (schemeSpace X.base).obj,
      s ∈ Set.range (Space.pointsMap B integerBase hZ X.total.obj X.toBase.hom)) :
    HasFibresOfDimensionOne B hZ X := by
  intro s
  obtain ⟨x, hx⟩ := hsurj s
  have hrel1 (x' : Space.points B integerBase hZ X.total.obj) :
      Space.HasRelativeDimensionAt (1 : ℕ∞) B integerBase hZ X.toBase.hom x' := by
    exact_mod_cast hrel x'
  have hle : Space.fiberDimension B integerBase hZ X.toBase.hom s ≤ ((1 : ℕ) : WithBot ℕ∞) :=
    (Space.fiberDimension_le_iff B integerBase hZ X.toBase.hom s 1).2
      fun x' _ => ⟨1, hrel1 x', by simp⟩
  have hnle : ¬ Space.fiberDimension B integerBase hZ X.toBase.hom s ≤ ((0 : ℕ) : WithBot ℕ∞) := by
    intro h
    obtain ⟨e, he, he0⟩ := (Space.fiberDimension_le_iff B integerBase hZ X.toBase.hom s 0).1 h x hx
    obtain ⟨c⟩ := Space.exists_etaleChartAtPoint B integerBase hZ X.total.property
      (schemeSpace X.base).property X.toBase.hom x
    have h1 := (hasFiberDimensionAt_ofSchemeHom_iff _ _ _).1 (hrel1 x c)
    have h0 := (hasFiberDimensionAt_ofSchemeHom_iff _ _ _).1 (he c)
    rw [h1] at h0
    have h10 : ((1 : ℕ∞) : WithBot ℕ∞) ≤ ((0 : ℕ) : WithBot ℕ∞) := h0 ▸ he0
    exact absurd (WithBot.coe_le_coe.mp h10) (by simp)
  have hbot : Space.fiberDimension B integerBase hZ X.toBase.hom s ≠ ⊥ :=
    fun hb => (Space.fiberDimension_eq_bot_iff B integerBase hZ X.toBase.hom s).1 hb ⟨x, hx⟩
  generalize Space.fiberDimension B integerBase hZ X.toBase.hom s = d at hle hnle hbot ⊢
  induction d using WithBot.recBotCoe with
  | bot => exact absurd rfl hbot
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      have h : (⊤ : ℕ∞) ≤ 1 := by exact_mod_cast hle
      exact absurd (top_le_iff.mp h) ENat.one_ne_top
    | coe n =>
      have h1 : n ≤ 1 := by exact_mod_cast hle
      have h0 : ¬ n ≤ 0 := fun h => hnle (by exact_mod_cast h)
      obtain rfl : n = 1 := by omega
      rfl

end CurveFamily

/-- **Condition (o) of Section 0E0E for `Curves^{smooth,1}`** (Stacks 0DZZ): the open subspace of
the base over which a family becomes smooth of relative dimension `1`, compatibly with base
change. -/
theorem isOpenCurvesLocus_isSmoothDimOneFamily :
    IsOpenCurvesLocus B hZ (IsSmoothDimOneFamily B hZ) :=
  fun G => CurveFamily.exists_isOpenSubspace_smoothDimOne B hZ G

/-- `Curves^{smooth,h0} = Curves^{smooth,1} ∩ Curves^{h0,1}`, objectwise: a family is in
`Curves^{smooth,h0}` exactly when it is smooth of relative dimension `1` and in `Curves^{h0,1}`.
The one point that is not formal is that the fibres have dimension `1`: a family with
`f_*𝒪_X = 𝒪_S` universally is surjective, and it has relative dimension `1` at every point. -/
theorem isSmoothH0CurveFamily_iff (X : CurveFamily B hZ) :
    IsSmoothH0CurveFamily B hZ X ↔ IsH01CurveFamily B hZ X ∧ IsSmoothDimOneFamily B hZ X :=
  ⟨fun h => ⟨⟨h.1, CurveFamily.hasFibresOfDimensionOne_of_hasRelativeDimension_one h.2.2
      (CurveFamily.exists_point_over_of_hasUniversallyBijectiveGlobalFunctions h.1)⟩, h.2⟩,
    fun h => ⟨h.1.1, h.2⟩⟩

/-- **Condition (o) of Section 0E0E for `Curves^{smooth,h0}`**, from condition (o) for
`Curves^{h0,1}` (Stacks 0E6I) and condition (o) for `Curves^{smooth,1}` (Stacks 0DZZ), through
`Curves^{smooth,h0} = Curves^{smooth,1} ∩ Curves^{h0,1}`. -/
theorem isOpenCurvesLocus_isSmoothH0CurveFamily_of
    (hH01 : IsOpenCurvesLocus B hZ (IsH01CurveFamily B hZ)) :
    IsOpenCurvesLocus B hZ (IsSmoothH0CurveFamily B hZ) := by
  intro G
  obtain ⟨W, hW, hchar⟩ := (hH01.and isOpenCurvesLocus_isSmoothDimOneFamily) G
  exact ⟨W, hW, fun F a => (isSmoothH0CurveFamily_iff F).trans (hchar F a)⟩

/-- **Stacks 0E81, part (1), from condition (o) for `Curves^{h0,1}`.** The strictly full
subcategory `Curves^{smooth,h0}` of families of curves with `f_*𝒪_X = 𝒪_S` universally and `f`
smooth of relative dimension `1` is an open substack of `Curves` — its inclusion is representable
by algebraic spaces and an open immersion — and the classifying morphism of a family of curves
factors through it exactly when the family satisfies these two conditions. The input is
condition (o) for `Curves^{h0,1}` (Stacks 0E6I). -/
theorem curvesSmoothH0_isOpenSubstack_and_factors_iff_of
    (hH01 : IsOpenCurvesLocus B hZ (IsH01CurveFamily B hZ)) :
    (ObjectProperty.IsClosedUnderIsomorphisms (IsSmoothH0CurveFamily B hZ) ∧
      Stack.IsRepresentableByAlgebraicSpaces B integerBase hZ
        (curvesSubstackInclusion B hZ (IsSmoothH0CurveFamily B hZ)
          (isOpenCurvesLocus_isSmoothH0CurveFamily_of hH01).prop_of_hom).hom ∧
      Stack.IsOpenImmersion B integerBase hZ
        (curvesSubstackInclusion B hZ (IsSmoothH0CurveFamily B hZ)
          (isOpenCurvesLocus_isSmoothH0CurveFamily_of hH01).prop_of_hom)) ∧
    ∀ (U : BigFppfOver B integerBase hZ)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ),
      y ⋙ curvesProjectionOver B hZ = Over.map U.hom →
      ((∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
          ObjectProperty.FullSubcategory (IsSmoothH0CurveFamily B hZ),
          z ⋙ ObjectProperty.ι (IsSmoothH0CurveFamily B hZ) = y) ↔
        IsSmoothH0CurveFamily B hZ (y.obj (Over.mk (𝟙 U.left)))) :=
  isOpenImmersion_curvesSubstackInclusion_and_factors_iff
    (isOpenCurvesLocus_isSmoothH0CurveFamily_of hH01)

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

/-- For a morphism `g : T → W` of the site with `W = Spec k`, the canonical map from `k` to the
global functions of `T` along `T → W = Spec k` is an isomorphism exactly when pullback of global
functions along `g` is bijective. -/
theorem isIso_globalSections_comp_eqToHom_iff :
    IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫
        ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW).appTop) ↔
      Function.Bijective ((BigFppfOver.toScheme B integerBase hZ).map g).appTop := by
  have : IsIso (eqToHom hW).appTop :=
    inferInstanceAs (IsIso (Scheme.Γ.map (eqToHom hW).op))
  rw [Scheme.Hom.comp_appTop, ← Category.assoc, isIso_comp_left_iff,
    ConcreteCategory.isIso_iff_bijective]

include hW in
/-- For a morphism `g : T → W` of the site with `W = Spec k`, if `H⁰(T, 𝒪_T) = k` then `T` is
nonempty: its ring of global functions is a field. -/
theorem nonempty_of_isIso_globalSections_comp_eqToHom
    (h : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫
        ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW).appTop)) :
    Nonempty ((BigFppfOver.toScheme B integerBase hZ).obj T) := by
  let e := (asIso ((Scheme.ΓSpecIso (.of k)).inv ≫
    ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW).appTop)).commRingCatIsoToRingEquiv
  have : Nontrivial Γ((BigFppfOver.toScheme B integerBase hZ).obj T, ⊤) :=
    e.symm.surjective.nontrivial
  by_contra hne
  rw [not_nonempty_iff] at hne
  exact not_subsingleton_iff_nontrivial.mpr ‹_› inferInstance

include hW in
/-- **The condition (1)(b) of Stacks 0E81 on a proper scheme over a field.** For the family of
curves of a proper scheme `X = T` of dimension at most one over a field `k = W`: given that
`f_*𝒪_X = 𝒪_S` universally is, for this family, `H⁰(X, 𝒪_X) = H⁰(Spec k, 𝒪)` (Stacks 0E6I,
from Stacks 0E6B part (a) and flat base change), the family is in `Curves^{smooth,h0}` exactly
when `X` is smooth over `k`, `dim X = 1` and `k = H⁰(X, 𝒪_X)`. -/
theorem isSmoothH0CurveFamily_curveFamilyOfSchemeMorphism_iff_of
    (hUB : HasUniversallyBijectiveGlobalFunctions B hZ
        (curveFamilyOfSchemeMorphism B hZ g hflat hproper hlfp hqc hsep hqsep hdim) ↔
      Function.Bijective ((BigFppfOver.toScheme B integerBase hZ).map g).appTop) :
    IsSmoothH0CurveFamily B hZ
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
  have hbij := isIso_globalSections_comp_eqToHom_iff g k hW
  constructor
  · rintro ⟨hU, hS⟩
    have hi := hbij.mpr (hUB.mp hU)
    have hne := nonempty_of_isIso_globalSections_comp_eqToHom g k hW hi
    have h := (isSmoothDimOneFamily_curveFamilyOfSchemeMorphism_iff B hZ g hflat hproper hlfp hqc
      hsep hqsep hdim k hW hne).mp hS
    exact ⟨hsm.mpr h.1, h.2.2, hi⟩
  · rintro ⟨hs, hd, hi⟩
    have hne := nonempty_of_isIso_globalSections_comp_eqToHom g k hW hi
    have hb : Smooth f ∧ topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) = 1 ∧
        IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) := ⟨hs, hd, hi⟩
    have : GeometricallyIntegral f := by
      have h13 := (smooth_dimOne_tfae_geometricallyConnected_isCurve_algebraicClosure k f).out 1 3
      exact (h13.mp hb).2.2
    have : IsIntegral ((BigFppfOver.toScheme B integerBase hZ).obj T) :=
      GeometricallyIntegral.isIntegral_of_subsingleton f
    exact ⟨hUB.mpr (hbij.mp hi), (isSmoothDimOneFamily_curveFamilyOfSchemeMorphism_iff B hZ g
      hflat hproper hlfp hqc hsep hqsep hdim k hW hne).mpr
        ⟨hsm.mp hs, TopologicalSpace.Equidimensional.of_preirreducibleSpace _, hd⟩⟩

include hW in
/-- **Stacks 0E81, part (2), from its inputs.** For the family of curves of a proper scheme
`X = T` of dimension at most one over a field `k = W`, classified by a scheme-valued point `y` of
the stack of curves over `Spec k`, the following are equivalent:

1. the classifying morphism `Spec k → Curves` factors through `Curves^{smooth,h0}`;
2. `X` is smooth over `k`, `dim X = 1`, and `k = H⁰(X, 𝒪_X)`;
3. `X` is smooth over `k`, `dim X = 1`, and `X` is geometrically connected;
4. `X` is smooth over `k`, `dim X = 1`, and `X` is geometrically integral;
5. `X_{k̄}` is a smooth curve over the algebraic closure `k̄` of `k`.

The inputs are condition (o) for `Curves^{h0,1}` and, for this family, the reading of
`f_*𝒪_X = 𝒪_S` universally as `H⁰(X, 𝒪_X) = H⁰(Spec k, 𝒪)` (Stacks 0E6I, part (2)). -/
theorem curvesSmoothH0_factors_tfae_of
    (hH01 : IsOpenCurvesLocus B hZ (IsH01CurveFamily B hZ))
    (hUB : HasUniversallyBijectiveGlobalFunctions B hZ
        (curveFamilyOfSchemeMorphism B hZ g hflat hproper hlfp hqc hsep hqsep hdim) ↔
      Function.Bijective ((BigFppfOver.toScheme B integerBase hZ).map g).appTop)
    (y : BigFppfOver B W.left.1 W.left.2 ⥤ CurveFamily B hZ)
    (hy : y ⋙ curvesProjectionOver B hZ = Over.map W.hom)
    (e : y.obj (Over.mk (𝟙 W.left)) ≅
      curveFamilyOfSchemeMorphism B hZ g hflat hproper hlfp hqc hsep hqsep hdim) :
    List.TFAE [
      ∃ z : BigFppfOver B W.left.1 W.left.2 ⥤
          ObjectProperty.FullSubcategory (IsSmoothH0CurveFamily B hZ),
        z ⋙ ObjectProperty.ι (IsSmoothH0CurveFamily B hZ) = y,
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
      IsCurve (AlgebraicClosure k)
          (pullback.snd ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW)
            (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))) ∧
        Smooth (pullback.snd ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW)
          (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))))] := by
  have := hproper
  rw [List.tfae_cons_cons]
  refine ⟨(factors_curvesSubstack_iff_of_iso (isOpenCurvesLocus_isSmoothH0CurveFamily_of hH01)
    W y hy _ e).trans (isSmoothH0CurveFamily_curveFamilyOfSchemeMorphism_iff_of g k hW hflat
      hproper hlfp hqc hsep hqsep hdim hUB), ?_⟩
  exact smooth_dimOne_tfae_geometricallyConnected_isCurve_algebraicClosure k
    ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW)

end OverField

/-- **Stacks 0E81, the whole statement, from its inputs.** `Curves^{smooth,h0} ⊂ Curves` is an
open substack whose points are characterized by parts (1) and (2) of the source:

* (open substack) the inclusion is representable by algebraic spaces and an open immersion;
* (1) the classifying morphism of a family of curves factors through `Curves^{smooth,h0}`
  exactly when `f_*𝒪_X = 𝒪_S` universally and `f` is smooth of relative dimension `1`;
* (2) for a proper scheme `X` of dimension at most one over a field `k`, the five conditions of
  `AlgebraicGeometry.curvesSmoothH0_factors_tfae_of` are equivalent.

The inputs are condition (o) for `Curves^{h0,1}` and the reading of `f_*𝒪_X = 𝒪_S` universally
over a field (Stacks 0E6I). -/
theorem curvesSmoothH0_isOpenSubstack_and_factors_iff_and_tfae_of
    (hH01 : IsOpenCurvesLocus B hZ (IsH01CurveFamily B hZ))
    (hUB : ∀ {T W : BigFppfOver B integerBase hZ} (g : T ⟶ W) (k : Type u) [Field k]
      (_hW : (BigFppfOver.toScheme B integerBase hZ).obj W = Spec (.of k))
      (hflat : Flat ((BigFppfOver.toScheme B integerBase hZ).map g))
      (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map g))
      (hlfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B integerBase hZ).map g))
      (hqc : Space.IsQuasiCompact B integerBase hZ (schemeSpaceMap g).hom)
      (hsep : Space.IsSeparated B integerBase hZ (schemeSpaceMap g).hom)
      (hqsep : Space.IsQuasiSeparated B integerBase hZ (schemeSpaceMap g).hom)
      (hdim : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) ≤ 1),
      HasUniversallyBijectiveGlobalFunctions B hZ
          (curveFamilyOfSchemeMorphism B hZ g hflat hproper hlfp hqc hsep hqsep hdim) ↔
        Function.Bijective ((BigFppfOver.toScheme B integerBase hZ).map g).appTop) :
    ((ObjectProperty.IsClosedUnderIsomorphisms (IsSmoothH0CurveFamily B hZ) ∧
      Stack.IsRepresentableByAlgebraicSpaces B integerBase hZ
        (curvesSubstackInclusion B hZ (IsSmoothH0CurveFamily B hZ)
          (isOpenCurvesLocus_isSmoothH0CurveFamily_of hH01).prop_of_hom).hom ∧
      Stack.IsOpenImmersion B integerBase hZ
        (curvesSubstackInclusion B hZ (IsSmoothH0CurveFamily B hZ)
          (isOpenCurvesLocus_isSmoothH0CurveFamily_of hH01).prop_of_hom)) ∧
    ∀ (U : BigFppfOver B integerBase hZ)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ),
      y ⋙ curvesProjectionOver B hZ = Over.map U.hom →
      ((∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
          ObjectProperty.FullSubcategory (IsSmoothH0CurveFamily B hZ),
          z ⋙ ObjectProperty.ι (IsSmoothH0CurveFamily B hZ) = y) ↔
        IsSmoothH0CurveFamily B hZ (y.obj (Over.mk (𝟙 U.left))))) ∧
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
            ObjectProperty.FullSubcategory (IsSmoothH0CurveFamily B hZ),
          z ⋙ ObjectProperty.ι (IsSmoothH0CurveFamily B hZ) = y,
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
        IsCurve (AlgebraicClosure k)
            (pullback.snd ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW)
              (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))) ∧
          Smooth (pullback.snd ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW)
            (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))))] :=
  ⟨curvesSmoothH0_isOpenSubstack_and_factors_iff_of hH01,
    fun g k _ hW hflat hproper hlfp hqc hsep hqsep hdim y hy e =>
      curvesSmoothH0_factors_tfae_of g k hW hflat hproper hlfp hqc hsep hqsep hdim hH01
        (hUB g k hW hflat hproper hlfp hqc hsep hqsep hdim) y hy e⟩

/-- **Stacks 0E81, the whole statement, from the two cohomological inputs of Stacks 0E6I.** The
statement of `AlgebraicGeometry.curvesSmoothH0_isOpenSubstack_and_factors_iff_and_tfae_of`, with
its inputs supplied by the 0E6I files from the openness of the fibrewise condition
`k = H⁰(X_k, 𝒪_{X_k})` (Stacks 0E0R at `i = 0`) and Stacks 0E6B, part (a). -/
theorem curvesSmoothH0_isOpenSubstack_and_factors_iff_and_tfae_of_cohomology
    (hopen : IsOpenCurvesLocus B hZ (CurveFamily.HasBijectiveGlobalFunctionsOnFieldFibres B hZ))
    (hpush : ∀ X : CurveFamily B hZ, CurveFamily.HasBijectiveGlobalFunctionsOnFieldFibres B hZ X →
      HasUniversallyBijectiveGlobalFunctions B hZ X) :
    ((ObjectProperty.IsClosedUnderIsomorphisms (IsSmoothH0CurveFamily B hZ) ∧
      Stack.IsRepresentableByAlgebraicSpaces B integerBase hZ
        (curvesSubstackInclusion B hZ (IsSmoothH0CurveFamily B hZ)
          (isOpenCurvesLocus_isSmoothH0CurveFamily_of
            (isOpenCurvesLocus_isH01CurveFamily_of hopen hpush)).prop_of_hom).hom ∧
      Stack.IsOpenImmersion B integerBase hZ
        (curvesSubstackInclusion B hZ (IsSmoothH0CurveFamily B hZ)
          (isOpenCurvesLocus_isSmoothH0CurveFamily_of
            (isOpenCurvesLocus_isH01CurveFamily_of hopen hpush)).prop_of_hom)) ∧
    ∀ (U : BigFppfOver B integerBase hZ)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ),
      y ⋙ curvesProjectionOver B hZ = Over.map U.hom →
      ((∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
          ObjectProperty.FullSubcategory (IsSmoothH0CurveFamily B hZ),
          z ⋙ ObjectProperty.ι (IsSmoothH0CurveFamily B hZ) = y) ↔
        IsSmoothH0CurveFamily B hZ (y.obj (Over.mk (𝟙 U.left))))) ∧
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
            ObjectProperty.FullSubcategory (IsSmoothH0CurveFamily B hZ),
          z ⋙ ObjectProperty.ι (IsSmoothH0CurveFamily B hZ) = y,
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
        IsCurve (AlgebraicClosure k)
            (pullback.snd ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW)
              (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))) ∧
          Smooth (pullback.snd ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW)
            (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))))] :=
  curvesSmoothH0_isOpenSubstack_and_factors_iff_and_tfae_of
    (isOpenCurvesLocus_isH01CurveFamily_of hopen hpush)
    (fun g k _ hW hflat hproper hlfp hqc hsep hqsep hdim =>
      CurveFamily.hasUniversallyBijectiveGlobalFunctions_curveFamilyOfSchemeMorphism_iff_of hpush g
        k hW hflat hproper hlfp hqc hsep hqsep hdim)

end AlgebraicGeometry

end
