module

public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinMorphisms.OverAField
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesCohenMacaulayDimOne
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Gorenstein.BaseLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Gorenstein.EtaleCharts

/-!
# Gorenstein families of curves

A family of curves `f : X → S` is *Gorenstein* when its structure morphism is Gorenstein in the
sense of Tag 0E14; this is the defining condition of the open substack `Curves^{Gorenstein}` of
Stacks 0E1M. The family is Gorenstein exactly when the locus `S'` of points of the base over which
it is Gorenstein is the whole base. By Tag 0E19 the Gorenstein locus `W` of `X` is open and its
formation commutes with arbitrary base change; since `f` is proper, `S' = S ∖ f(|X| ∖ W)` is open,
and its formation commutes with arbitrary base change because that of `W` does. This is
condition (o) of Section 0E0E, from which that section makes the open substack.

Over the spectrum of a field the condition is read off the proper scheme itself: the family of
curves of a proper scheme `X` of dimension at most one over a field is Gorenstein exactly when
`X` is a Gorenstein scheme.

## Main definitions

* `AlgebraicGeometry.IsGorensteinFamily`: the defining condition of `Curves^{Gorenstein}`.

## Main results

* `AlgebraicGeometry.isGorensteinFamily_iff_gorensteinBaseLocus_eq_univ`: a family is Gorenstein
  exactly when its Gorenstein locus in the base is the whole base.
* `AlgebraicGeometry.CurveFamily.isOpen_gorensteinBaseLocus` and
  `AlgebraicGeometry.CurveFamily.preimage_gorensteinBaseLocus`: that locus is open, and its
  formation commutes with base change.
* `AlgebraicGeometry.isOpenCurvesLocus_isGorensteinFamily`: condition (o) of Section 0E0E for
  `Curves^{Gorenstein}`.
* `AlgebraicGeometry.isGorenstein_schemeSpaceMap_iff_of_target_eq_spec`: over the spectrum of a
  field, the structure morphism of a flat family whose total space is a scheme is Gorenstein
  exactly when that scheme is.
* `AlgebraicGeometry.isGorensteinFamily_curveFamilyOfSchemeMorphism_iff`: the family of curves
  of a proper scheme of dimension at most one over a field is Gorenstein exactly when the scheme
  is Gorenstein.

## Implementation notes

Over a field the comparison is Tag 0E15 for a morphism of represented presheaves
(`AlgebraicGeometry.Space.isGorenstein_yoneda_map_iff`) followed by Tag 0C05 over the spectrum
of a field, whose only fibre is the source. The family of curves of a proper scheme over a field
is `AlgebraicGeometry.curveFamilyOfSchemeMorphism` with all of its hypotheses discharged, as in
`AlgebraicGeometry.isCohenMacaulayDimOneFamily_curveFamilyOfSchemeMorphism_iff`.

The open substack itself, and the two characterizations of it, are in
`StacksFrontier.AlgebraicGeometry.Quot.CurvesGorensteinSubstack`.

## References

* [Stacks Project, Tag 0E1M](https://stacks.math.columbia.edu/tag/0E1M)
* [Stacks Project, Tag 0E0E](https://stacks.math.columbia.edu/tag/0E0E)
* [Stacks Project, Tag 0E14](https://stacks.math.columbia.edu/tag/0E14)
* [Stacks Project, Tag 0E15](https://stacks.math.columbia.edu/tag/0E15)
* [Stacks Project, Tag 0E19](https://stacks.math.columbia.edu/tag/0E19)
* [Stacks Project, Tag 0C05](https://stacks.math.columbia.edu/tag/0C05)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

attribute [local instance] Space.pointTopology

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- The defining condition of `Curves^{Gorenstein}`: the structure morphism of the family of
curves is Gorenstein in the sense of Tag 0E14. -/
abbrev IsGorensteinFamily (X : CurveFamily B hZ) : Prop :=
  Space.IsGorenstein B integerBase hZ X.toBase.hom

/-- A family of curves is Gorenstein exactly when the locus in its base over which it is
Gorenstein is the whole base. -/
theorem isGorensteinFamily_iff_gorensteinBaseLocus_eq_univ (X : CurveFamily B hZ) :
    IsGorensteinFamily B hZ X ↔
      Space.gorensteinBaseLocus B integerBase hZ X.toBase.hom = Set.univ :=
  Space.isGorenstein_iff_gorensteinBaseLocus_eq_univ B integerBase hZ X.toBase.hom

/-- **The Gorenstein locus in the base is open.** For every family of curves `f : X → S`, the set
of points of `S` over which `f` is Gorenstein is open: the Gorenstein locus of `X` is open by
Tag 0E19, and `f` is proper, so the image of its complement, the complement of the locus, is
closed. -/
theorem CurveFamily.isOpen_gorensteinBaseLocus (X : CurveFamily B hZ) :
    IsOpen (Space.gorensteinBaseLocus B integerBase hZ X.toBase.hom) :=
  Space.isOpen_gorensteinBaseLocus_of_isProper B integerBase hZ X.total.property
    (schemeSpace X.base).property X.toBase.hom X.flat X.finitePresentation.1 X.proper

/-- **The Gorenstein locus in the base commutes with base change.** For a morphism of families of
curves, the Gorenstein locus in the base of the source is the inverse image of the Gorenstein
locus in the base of the target under the morphism of base schemes: a morphism of families is a
cartesian square, and the formation of the Gorenstein locus commutes with arbitrary base change
by Tag 0E19. -/
theorem CurveFamily.preimage_gorensteinBaseLocus {X Y : CurveFamily B hZ} (φ : X ⟶ Y) :
    Space.pointsMap B integerBase hZ (schemeSpace X.base).obj (schemeSpaceMap φ.baseMap).hom ⁻¹'
        Space.gorensteinBaseLocus B integerBase hZ Y.toBase.hom =
      Space.gorensteinBaseLocus B integerBase hZ X.toBase.hom :=
  Space.preimage_gorensteinBaseLocus_of_isPullback B integerBase hZ Y.toBase
    (schemeSpaceMap φ.baseMap) (AlgebraicSpaces.isPullback_hom B integerBase hZ φ.cartesian)
    Y.flat Y.finitePresentation.1

/-- **Condition (o) of Section 0E0E for `Curves^{Gorenstein}`.** For every family of curves
`X → S` there is an open subset `S'` of the base such that a family of curves mapping to `X → S`
is Gorenstein exactly when its base maps into `S'`: the Gorenstein locus in the base, which is
open for every family and commutes with base change. -/
theorem isOpenCurvesLocus_isGorensteinFamily :
    IsOpenCurvesLocus B hZ (IsGorensteinFamily B hZ) :=
  IsOpenCurvesLocus.of_baseLocus
    (fun X => Space.gorensteinBaseLocus B integerBase hZ X.toBase.hom)
    (CurveFamily.isOpen_gorensteinBaseLocus B hZ)
    (CurveFamily.preimage_gorensteinBaseLocus B hZ)
    (isGorensteinFamily_iff_gorensteinBaseLocus_eq_univ B hZ)

/-- **The Gorenstein condition over a field.** For a flat morphism of the big fppf site of the
integers with locally Noetherian fibres whose target is the spectrum of a field, the induced
morphism of algebraic spaces is Gorenstein exactly when its source scheme is Gorenstein: by
Tag 0E15 it is Gorenstein exactly when the morphism of schemes is flat with Gorenstein fibres,
and over a field the only fibre is the source. -/
theorem isGorenstein_schemeSpaceMap_iff_of_target_eq_spec
    {T U : BigFppfOver B integerBase hZ} (g : T ⟶ U) (k : Type u) [Field k]
    (hU : (BigFppfOver.toScheme B integerBase hZ).obj U = Spec (.of k))
    [Flat ((BigFppfOver.toScheme B integerBase hZ).map g)]
    (hfib : ∀ v : (BigFppfOver.toScheme B integerBase hZ).obj U,
      IsLocallyNoetherian (((BigFppfOver.toScheme B integerBase hZ).map g).fiber v)) :
    Space.IsGorenstein B integerBase hZ (schemeSpaceMap g).hom ↔
      IsGorenstein ((BigFppfOver.toScheme B integerBase hZ).obj T) := by
  refine (Space.isGorenstein_yoneda_map_iff B integerBase hZ T U g hfib).trans
    ((and_iff_right (inferInstanceAs (Flat ((BigFppfOver.toScheme B integerBase hZ).map g)))).trans
      ?_)
  have key : ∀ (Y : Scheme.{u}) (_ : Y = Spec (.of k))
      (h : (BigFppfOver.toScheme B integerBase hZ).obj T ⟶ Y),
      (∀ y : Y, IsGorenstein (h.fiber y)) ↔
        IsGorenstein ((BigFppfOver.toScheme B integerBase hZ).obj T) := by
    intro Y hY h
    subst hY
    exact isGorenstein_iff_forall_fiber_of_field k h
  exact key _ hU _

/-- **The Gorenstein condition on the family of a proper scheme over a field.** Let `g : T ⟶ U`
be a morphism of the big fppf site of the integers whose target scheme is the spectrum of a field
`k`, whose underlying morphism of schemes is proper, and whose source scheme has dimension at
most one. Then the family of curves of `g` is Gorenstein exactly when the source scheme is
Gorenstein. -/
theorem isGorensteinFamily_curveFamilyOfSchemeMorphism_iff
    {T U : BigFppfOver B integerBase hZ} (g : T ⟶ U) (k : Type u) [Field k]
    (hU : (BigFppfOver.toScheme B integerBase hZ).obj U = Spec (.of k))
    (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hdim : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) ≤ 1) :
    IsGorensteinFamily B hZ
        (curveFamilyOfSchemeMorphism B hZ g
          (flat_of_eq_spec_field _ k hU) hproper
          (locallyOfFinitePresentation_of_eq_spec_field _ k hU)
          (Space.isQuasiCompact_yoneda_map B integerBase hZ g inferInstance)
          ((Space.isSeparated_yoneda_map_iff B integerBase hZ g).2 inferInstance)
          ((Space.isQuasiSeparated_yoneda_map_iff B integerBase hZ g).2 inferInstance)
          hdim) ↔
      IsGorenstein ((BigFppfOver.toScheme B integerBase hZ).obj T) := by
  set F := BigFppfOver.toScheme B integerBase hZ
  have := flat_of_eq_spec_field (F.map g) k hU
  have hfib : ∀ v : F.obj U, IsLocallyNoetherian ((F.map g).fiber v) := fun v => by
    have : LocallyOfFiniteType ((F.map g).fiberToSpecResidueField v) := by
      change LocallyOfFiniteType (pullback.snd (F.map g) ((F.obj U).fromSpecResidueField v))
      infer_instance
    exact LocallyOfFiniteType.isLocallyNoetherian ((F.map g).fiberToSpecResidueField v)
  exact isGorenstein_schemeSpaceMap_iff_of_target_eq_spec B hZ g k hU hfib

end AlgebraicGeometry

end
