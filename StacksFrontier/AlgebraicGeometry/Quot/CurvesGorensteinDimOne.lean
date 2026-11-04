module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesCohenMacaulay
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesOpenSubstackRelative
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesSmallOpenSubstack
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesSmooth
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyOverField
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Gorenstein.CohenMacaulay

/-!
# Gorenstein curves of relative dimension one (Stacks 0E6M)

Stacks 0E6M produces the open substack `Curves^{Gorenstein, 1} ⊂ Curves` of families of curves
which are Gorenstein and have relative dimension one, with its two universal properties: the
classifying morphism of a family factors through it exactly when the family is Gorenstein of
relative dimension one, and for a proper scheme `X` of dimension at most one over a field the
classifying morphism of `X` factors through it exactly when `X` is Gorenstein and equidimensional
of dimension one.

The source proves this from Tags 0E1M and 0E1F: a Gorenstein morphism is Cohen–Macaulay
(Tag 0C06), so `Curves^{Gorenstein, 1}` is the intersection of `Curves^{Gorenstein}` with
`Curves^{CM, 1}`. Tag 0E1M is not in this library; its proof rests on Tag 0E19. Every
statement here that needs it takes the statement of Tag 0E1M as the explicit hypothesis
`h0E1M`, and so carries no tag.

## Main definitions

* `AlgebraicGeometry.IsGorensteinDimOneFamily`: the defining condition of
  `Curves^{Gorenstein, 1}`, Gorensteinness together with relative dimension one in the sense of
  part (2) of Tag 06LR.

## Main results

* `AlgebraicGeometry.isOpenCurvesLocus_isGorensteinDimOneFamily`: condition (o) of Section 0E0E
  for `Curves^{Gorenstein, 1}`, from the statement of Tag 0E1M.
* `AlgebraicGeometry.isGorensteinDimOneFamily_curveFamilyOfScheme_iff`: over a field, the family
  of curves of a proper scheme `X` of dimension at most one is Gorenstein of relative dimension
  one exactly when `X` is Gorenstein and equidimensional of dimension one.
* `AlgebraicGeometry.curvesGorensteinDimOne_isOpenSubstack`,
  `AlgebraicGeometry.factors_curvesGorensteinDimOne_iff` and
  `AlgebraicGeometry.factors_curvesGorensteinDimOne_over_field_iff`: the open substack and its
  parts (1) and (2), and `AlgebraicGeometry.curvesGorensteinDimOne_isOpenSubstack_and_factors_iff`
  the whole statement of Tag 0E6M, on the category of families of curves.
* `AlgebraicGeometry.exists_curvesGorensteinDimOne_openSubstack`: the same open substack of the
  small model `AlgebraicGeometry.curvesAlgebraicStack` of the stack of curves, which also needs
  the algebraicity of the stack of curves, Tag 0D5A.

## Implementation notes

The statement of Tag 0E1M is taken in the form of the rest of this library's open substacks of
curves: condition (o) of Section 0E0E for the property that the structure morphism be Gorenstein
in the sense of Tag 0E14, which by Tag 0E0E is the open substack `Curves^{Gorenstein}` together
with its part (1), and its part (2) on the family of curves of a proper scheme of dimension at
most one over a field.

Condition (o) for `Curves^{Gorenstein, 1}` is then
`AlgebraicGeometry.IsOpenCurvesLocus.and_of_baseLocus` applied to `Curves^{Gorenstein}` and to the
locus of relative dimension one in the base: that locus commutes with base change (part (1) of
Tag 04NS), and it is open over a Cohen–Macaulay family by the registered part of Tag 0E1F
(`AlgebraicGeometry.CurveFamily.isOpen_relativeDimensionOneBaseLocus`), which applies over
`Curves^{Gorenstein}` because a Gorenstein morphism of algebraic spaces is Cohen–Macaulay
(`AlgebraicGeometry.Space.isCohenMacaulay_of_isGorenstein`).

"Equidimensional of dimension one" in part (2) is read as in Tag 0058: every irreducible
component has dimension one. Read this way part (2) needs no non-emptiness hypothesis, the empty
scheme being Gorenstein of relative dimension one with no irreducible component.

## References

* [Stacks Project, Tag 0E6M](https://stacks.math.columbia.edu/tag/0E6M)
* [Stacks Project, Tag 0E1M](https://stacks.math.columbia.edu/tag/0E1M)
* [Stacks Project, Tag 0E1F](https://stacks.math.columbia.edu/tag/0E1F)
* [Stacks Project, Tag 0E0E](https://stacks.math.columbia.edu/tag/0E0E)
* [Stacks Project, Tag 0C06](https://stacks.math.columbia.edu/tag/0C06)
* [Stacks Project, Tag 06LR](https://stacks.math.columbia.edu/tag/06LR)
* [Stacks Project, Tag 0058](https://stacks.math.columbia.edu/tag/0058)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u w

namespace AlgebraicGeometry

attribute [local instance] Space.pointTopology

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- The defining condition of `Curves^{Gorenstein, 1}`: the structure morphism of the family of
curves is Gorenstein in the sense of Tag 0E14 and has relative dimension one in the sense of part
(2) of Tag 06LR. -/
abbrev IsGorensteinDimOneFamily : ObjectProperty (CurveFamily B hZ) := fun X =>
  Space.IsGorenstein B integerBase hZ X.toBase.hom ∧
    Space.HasRelativeDimension 1 B integerBase hZ X.toBase.hom

/-- A family of curves has relative dimension one exactly when the locus in its base of relative
dimension one is the whole base. -/
theorem hasRelativeDimension_one_iff_relativeDimensionOneBaseLocus_eq_univ (X : CurveFamily B hZ) :
    Space.HasRelativeDimension 1 B integerBase hZ X.toBase.hom ↔
      CurveFamily.relativeDimensionOneBaseLocus B hZ X = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  exact ⟨fun hX _ x _ => hX x,
    fun hX x => hX (Space.pointsMap B integerBase hZ X.total.obj X.toBase.hom x) x rfl⟩

section Gorenstein

/- The statement of Tag 0E1M: condition (o) of Section 0E0E for Gorenstein
families of curves, and its part (2) on the family of curves of a proper scheme of dimension at
most one over a field. -/
variable (h0E1M :
  IsOpenCurvesLocus B hZ (fun X : CurveFamily B hZ => Space.IsGorenstein B integerBase hZ
      X.toBase.hom) ∧
    ∀ {T U : BigFppfOver B integerBase hZ} (g : T ⟶ U)
      (hflat : Flat ((BigFppfOver.toScheme B integerBase hZ).map g))
      (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map g))
      (hlfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B integerBase hZ).map g))
      (hqc : Space.IsQuasiCompact B integerBase hZ (schemeSpaceMap g).hom)
      (hsep : Space.IsSeparated B integerBase hZ (schemeSpaceMap g).hom)
      (hqsep : Space.IsQuasiSeparated B integerBase hZ (schemeSpaceMap g).hom)
      (hdim : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) ≤ 1)
      (k : Type u) [Field k],
      (BigFppfOver.toScheme B integerBase hZ).obj U = Spec (.of k) →
      (Space.IsGorenstein B integerBase hZ
          (curveFamilyOfSchemeMorphism B hZ g hflat hproper hlfp hqc hsep hqsep hdim).toBase.hom ↔
        IsGorenstein ((BigFppfOver.toScheme B integerBase hZ).obj T)))

include h0E1M

/-- **Condition (o) of Section 0E0E for `Curves^{Gorenstein, 1}`** (the step of the proof of
Stacks 0E6M), from the statement of Tag 0E1M, `h0E1M` (its proof rests on Tag 0E19).
Unregistered, since it takes that hypothesis.

`Curves^{Gorenstein, 1}` is `Curves^{Gorenstein}` intersected with the locus of relative dimension
one, which is open over every Gorenstein family: such a family is Cohen–Macaulay, and over a
Cohen–Macaulay family the locus is open by Tag 0E1F. -/
theorem isOpenCurvesLocus_isGorensteinDimOneFamily :
    IsOpenCurvesLocus B hZ (IsGorensteinDimOneFamily B hZ) :=
  h0E1M.1.and_of_baseLocus (CurveFamily.relativeDimensionOneBaseLocus B hZ)
    (CurveFamily.preimage_relativeDimensionOneBaseLocus B hZ)
    (hasRelativeDimension_one_iff_relativeDimensionOneBaseLocus_eq_univ B hZ)
    (fun G hG => CurveFamily.isOpen_relativeDimensionOneBaseLocus B hZ G
      (Space.isCohenMacaulay_of_isGorenstein B integerBase hZ hG))

/-- **Part (2) of Stacks 0E6M, on the family of a morphism of the site.** For a proper flat
morphism of schemes of finite presentation onto the spectrum of a field whose source has
dimension at most one, the attached family of curves is Gorenstein of relative dimension one
exactly when the source is Gorenstein and equidimensional of dimension one, every irreducible
component of it having dimension one. This takes the statement of Tag 0E1M as `h0E1M` and so
is unregistered. -/
theorem isGorensteinDimOneFamily_curveFamilyOfSchemeMorphism_iff
    {T U : BigFppfOver B integerBase hZ} (g : T ⟶ U)
    (hflat : Flat ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hlfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hqc : Space.IsQuasiCompact B integerBase hZ (schemeSpaceMap g).hom)
    (hsep : Space.IsSeparated B integerBase hZ (schemeSpaceMap g).hom)
    (hqsep : Space.IsQuasiSeparated B integerBase hZ (schemeSpaceMap g).hom)
    (hdim : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) ≤ 1)
    (k : Type u) [Field k]
    (hU : (BigFppfOver.toScheme B integerBase hZ).obj U = Spec (.of k)) :
    IsGorensteinDimOneFamily B hZ
        (curveFamilyOfSchemeMorphism B hZ g hflat hproper hlfp hqc hsep hqsep hdim) ↔
      (IsGorenstein ((BigFppfOver.toScheme B integerBase hZ).obj T) ∧
        TopologicalSpace.Equidimensional ((BigFppfOver.toScheme B integerBase hZ).obj T) ∧
        ∀ W ∈ irreducibleComponents ((BigFppfOver.toScheme B integerBase hZ).obj T),
          topologicalKrullDim W = (1 : WithBot ℕ∞)) := by
  have hgor := h0E1M.2 g hflat hproper hlfp hqc hsep hqsep hdim k hU
  have hdimOne := hasRelativeDimension_schemeSpaceMap_iff_forall_irreducibleComponents B hZ 1 g k
    hU inferInstance
  rw [show ((1 : ℕ) : WithBot ℕ∞) = (1 : WithBot ℕ∞) by norm_num] at hdimOne
  refine ⟨fun hX => ?_, fun hX => ⟨hgor.mpr hX.1, hdimOne.mpr hX.2.2⟩⟩
  have hcomp := hdimOne.mp hX.2
  exact ⟨hgor.mp hX.1, fun C hC D hD => (hcomp C hC).trans (hcomp D hD).symm, hcomp⟩

/-- **Part (2) of Stacks 0E6M, on the family of curves of a proper scheme.** The family of curves
of a proper scheme `X` of dimension at most one over a field `k` is Gorenstein of relative
dimension one exactly when `X` is Gorenstein and equidimensional of dimension one. This takes the
statement of Tag 0E1M as `h0E1M` and so is unregistered. -/
theorem isGorensteinDimOneFamily_curveFamilyOfScheme_iff
    (k : Type u) [Field k] (hk : B.Contains (Spec (.of k)))
    (X : Over (Spec (.of k))) [IsProper X.hom] (hdim : topologicalKrullDim X.left ≤ 1) :
    IsGorensteinDimOneFamily B hZ (curveFamilyOfScheme X B hZ hk hdim) ↔
      (IsGorenstein X.left ∧ TopologicalSpace.Equidimensional X.left ∧
        ∀ W ∈ irreducibleComponents X.left, topologicalKrullDim W = (1 : WithBot ℕ∞)) := by
  let g := integerSiteMap B hZ (Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact X.hom hk) hk
    X.hom
  have hqc : Space.IsQuasiCompact B integerBase hZ (schemeSpaceMap g).hom :=
    Space.isQuasiCompact_yoneda_map_of_quasiCompact B integerBase hZ g
      (inferInstanceAs (QuasiCompact X.hom))
  have hsep : Space.IsSeparated B integerBase hZ (schemeSpaceMap g).hom :=
    (Space.isSeparated_yoneda_map_iff B integerBase hZ g).2 (inferInstanceAs (IsSeparated X.hom))
  have hqsep : Space.IsQuasiSeparated B integerBase hZ (schemeSpaceMap g).hom :=
    (Space.isQuasiSeparated_yoneda_map_iff B integerBase hZ g).2
      (inferInstanceAs (QuasiSeparated X.hom))
  exact isGorensteinDimOneFamily_curveFamilyOfSchemeMorphism_iff B hZ h0E1M g
    (inferInstanceAs (Flat X.hom)) (inferInstanceAs (IsProper X.hom))
    (inferInstanceAs (LocallyOfFinitePresentation X.hom)) hqc hsep hqsep hdim k rfl

/-- **Stacks 0E6M, the open substack.** `Curves^{Gorenstein, 1}`, the strictly full subcategory of
families of curves which are Gorenstein of relative dimension one, is an open substack of
`Curves`: its inclusion is representable by algebraic spaces and an open immersion. This takes
the statement of Tag 0E1M as `h0E1M` (its proof rests on Tag 0E19) and so is unregistered. -/
theorem curvesGorensteinDimOne_isOpenSubstack :
    ObjectProperty.IsClosedUnderIsomorphisms (IsGorensteinDimOneFamily B hZ) ∧
      Stack.IsRepresentableByAlgebraicSpaces B integerBase hZ
        (curvesSubstackInclusion B hZ _
          (isOpenCurvesLocus_isGorensteinDimOneFamily B hZ h0E1M).prop_of_hom).hom ∧
      Stack.IsOpenImmersion B integerBase hZ
        (curvesSubstackInclusion B hZ _
          (isOpenCurvesLocus_isGorensteinDimOneFamily B hZ h0E1M).prop_of_hom) :=
  isOpenImmersion_curvesSubstackInclusion (isOpenCurvesLocus_isGorensteinDimOneFamily B hZ h0E1M)

/-- **Stacks 0E6M, part (1).** The classifying morphism of a family of curves `X ⟶ S` factors
through `Curves^{Gorenstein, 1}` exactly when `X ⟶ S` is Gorenstein and has relative dimension
one. This takes the statement of Tag 0E1M as `h0E1M` and so is unregistered. -/
theorem factors_curvesGorensteinDimOne_iff (U : BigFppfOver B integerBase hZ)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ)
    (hy : y ⋙ curvesProjectionOver B hZ = Over.map U.hom) :
    (∃ z : BigFppfOver B U.left.1 U.left.2 ⥤ (IsGorensteinDimOneFamily B hZ).FullSubcategory,
        z ⋙ (IsGorensteinDimOneFamily B hZ).ι = y) ↔
      Space.IsGorenstein B integerBase hZ (y.obj (Over.mk (𝟙 U.left))).toBase.hom ∧
        Space.HasRelativeDimension 1 B integerBase hZ (y.obj (Over.mk (𝟙 U.left))).toBase.hom :=
  factors_curvesSubstack_iff (isOpenCurvesLocus_isGorensteinDimOneFamily B hZ h0E1M) U y hy

/-- **Stacks 0E6M, part (2).** Let `X` be a proper scheme of dimension at most one over a field
`k` (with `Spec k` in the site, so that the classifying morphism `Spec k ⟶ Curves` of `X`
exists). The classifying morphism of `X` factors through `Curves^{Gorenstein, 1}` exactly when
`X` is Gorenstein and equidimensional of dimension one. This takes the statement of Tag 0E1M as
`h0E1M` and so is unregistered. -/
theorem factors_curvesGorensteinDimOne_over_field_iff
    (k : Type u) [Field k] (hk : B.Contains (Spec (.of k)))
    (X : Over (Spec (.of k))) [IsProper X.hom] (hdim : topologicalKrullDim X.left ≤ 1)
    (U : BigFppfOver B integerBase hZ)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ)
    (hy : y ⋙ curvesProjectionOver B hZ = Over.map U.hom)
    (e : y.obj (Over.mk (𝟙 U.left)) ≅ curveFamilyOfScheme X B hZ hk hdim) :
    (∃ z : BigFppfOver B U.left.1 U.left.2 ⥤ (IsGorensteinDimOneFamily B hZ).FullSubcategory,
        z ⋙ (IsGorensteinDimOneFamily B hZ).ι = y) ↔
      (IsGorenstein X.left ∧ TopologicalSpace.Equidimensional X.left ∧
        ∀ W ∈ irreducibleComponents X.left, topologicalKrullDim W = (1 : WithBot ℕ∞)) :=
  (factors_curvesSubstack_iff_of_iso (isOpenCurvesLocus_isGorensteinDimOneFamily B hZ h0E1M) U y
    hy _ e).trans (isGorensteinDimOneFamily_curveFamilyOfScheme_iff B hZ h0E1M k hk X hdim)

/-- **Stacks 0E6M.** There is an open substack `Curves^{Gorenstein, 1} ⊂ Curves` — the strictly
full subcategory of families of curves which are Gorenstein of relative dimension one, whose
inclusion is representable by algebraic spaces and an open immersion — such that (1) the
classifying morphism of a family of curves `X ⟶ S` factors through it exactly when `X ⟶ S` is
Gorenstein and has relative dimension one, and (2) for a proper scheme `X` of dimension at most
one over a field `k`, the classifying morphism of `X` factors through it exactly when `X` is
Gorenstein and equidimensional of dimension one.

This takes the statement of Tag 0E1M as `h0E1M` (its proof rests on Tag 0E19) and so is
unregistered. -/
theorem curvesGorensteinDimOne_isOpenSubstack_and_factors_iff :
    (ObjectProperty.IsClosedUnderIsomorphisms (IsGorensteinDimOneFamily B hZ) ∧
      Stack.IsRepresentableByAlgebraicSpaces B integerBase hZ
        (curvesSubstackInclusion B hZ _
          (isOpenCurvesLocus_isGorensteinDimOneFamily B hZ h0E1M).prop_of_hom).hom ∧
      Stack.IsOpenImmersion B integerBase hZ
        (curvesSubstackInclusion B hZ _
          (isOpenCurvesLocus_isGorensteinDimOneFamily B hZ h0E1M).prop_of_hom)) ∧
    (∀ (U : BigFppfOver B integerBase hZ)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ),
      y ⋙ curvesProjectionOver B hZ = Over.map U.hom →
      ((∃ z : BigFppfOver B U.left.1 U.left.2 ⥤ (IsGorensteinDimOneFamily B hZ).FullSubcategory,
          z ⋙ (IsGorensteinDimOneFamily B hZ).ι = y) ↔
        Space.IsGorenstein B integerBase hZ (y.obj (Over.mk (𝟙 U.left))).toBase.hom ∧
          Space.HasRelativeDimension 1 B integerBase hZ
            (y.obj (Over.mk (𝟙 U.left))).toBase.hom)) ∧
    (∀ (k : Type u) [Field k] (hk : B.Contains (Spec (.of k)))
      (X : Over (Spec (.of k))) [IsProper X.hom] (hdim : topologicalKrullDim X.left ≤ 1)
      (U : BigFppfOver B integerBase hZ)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ),
      y ⋙ curvesProjectionOver B hZ = Over.map U.hom →
      (y.obj (Over.mk (𝟙 U.left)) ≅ curveFamilyOfScheme X B hZ hk hdim) →
      ((∃ z : BigFppfOver B U.left.1 U.left.2 ⥤ (IsGorensteinDimOneFamily B hZ).FullSubcategory,
          z ⋙ (IsGorensteinDimOneFamily B hZ).ι = y) ↔
        (IsGorenstein X.left ∧ TopologicalSpace.Equidimensional X.left ∧
          ∀ W ∈ irreducibleComponents X.left, topologicalKrullDim W = (1 : WithBot ℕ∞)))) :=
  ⟨curvesGorensteinDimOne_isOpenSubstack B hZ h0E1M,
    factors_curvesGorensteinDimOne_iff B hZ h0E1M,
    fun k _ hk X _ hdim U y hy e =>
      factors_curvesGorensteinDimOne_over_field_iff B hZ h0E1M k hk X hdim U y hy e⟩

/-- **Stacks 0E6M on the small model of the stack of curves.** Given that the stack of curves is
algebraic (`h`, the statement of Tag 0D5A), its small model
`AlgebraicGeometry.curvesAlgebraicStack` has an open substack whose objects are exactly the
families of curves which are Gorenstein of relative dimension one; in particular a proper scheme
`X` of dimension at most one over a field lies in it exactly when `X` is Gorenstein and
equidimensional of dimension one. This takes `h` and the statement of Tag 0E1M as `h0E1M` and
so is unregistered. -/
theorem exists_curvesGorensteinDimOne_openSubstack
    (h : Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val) :
    ∃ U : Stack.OpenSubstack (curvesAlgebraicStack B hZ h),
      (∀ F : CurveFamily B hZ,
        U.property ((curvesSmallEquivalence B hZ h).functor.obj F) ↔
          Space.IsGorenstein B integerBase hZ F.toBase.hom ∧
            Space.HasRelativeDimension 1 B integerBase hZ F.toBase.hom) ∧
      ∀ (k : Type u) [Field k] (hk : B.Contains (Spec (.of k)))
        (X : Over (Spec (.of k))) [IsProper X.hom] (hdim : topologicalKrullDim X.left ≤ 1),
        U.property ((curvesSmallEquivalence B hZ h).functor.obj
            (curveFamilyOfScheme X B hZ hk hdim)) ↔
          (IsGorenstein X.left ∧ TopologicalSpace.Equidimensional X.left ∧
            ∀ W ∈ irreducibleComponents X.left, topologicalKrullDim W = (1 : WithBot ℕ∞)) :=
  ⟨curvesSmallOpenSubstack B hZ h (isOpenCurvesLocus_isGorensteinDimOneFamily B hZ h0E1M),
    fun F => curvesSmallOpenSubstack_property_iff B hZ h _ F,
    fun k _ hk X _ hdim => (curvesSmallOpenSubstack_property_iff B hZ h _ _).trans
      (isGorensteinDimOneFamily_curveFamilyOfScheme_iff B hZ h0E1M k hk X hdim)⟩

end Gorenstein

end AlgebraicGeometry

end
