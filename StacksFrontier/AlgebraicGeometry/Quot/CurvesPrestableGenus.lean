module

public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.Basic
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesGenus
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesPrestableOpen

/-!
# The families of `Curves^{prestable}_g` (towards Stacks 0E6V)

Stacks 0E6V decomposes the open substack `Curves^{prestable}` of the stack of curves (Stacks
0E6U) into open and closed substacks `Curves^{prestable}_g`, `g ≥ 0`: a family of curves
`f : X → S` lies in `Curves^{prestable}_g` when it is prestable (Stacks 0E6T) and `R¹f_*𝒪_X` is a
locally free `𝒪_S`-module of rank `g`. The source deduces this from Stacks 0E6U and 0E6K, since
`Curves^{prestable} ⊂ Curves^{h0,1}`: `Curves^{prestable}_g = Curves^{prestable} ∩ Curves_g`.

This file defines the families of `Curves^{prestable}_g` and proves condition (1)(b) and the
characterization (2)(b) on a proper scheme over a field. The latter takes its three inputs (the
implication of Stacks 0E6B (a) for families of curves, `hpush`; the criterion for at-worst-nodal
morphisms over a field, `hsch`; the rank of `R¹f_*𝒪_X` over a field, `hrk`) as explicit
hypotheses; they are supplied in
`StacksFrontier.AlgebraicGeometry.Quot.CurvesPrestableGenusDecomposition`, which registers Stacks
0E6V. No declaration of this file carries a `stacks` attribute.

## Main definitions

* `AlgebraicGeometry.IsPrestableGenusCurveFamily`: the families of `Curves^{prestable}_g`, the
  conjunction of `AlgebraicGeometry.IsPrestableCurveFamily` and
  `AlgebraicGeometry.IsGenusCurveFamily`.

## Main results

* `AlgebraicGeometry.isPrestableGenusCurveFamily_iff`: condition (1)(b) of Stacks 0E6V, a
  prestable family with `R¹f_*𝒪_X` locally free of rank `g`.
* `AlgebraicGeometry.isPrestableGenusCurveFamily_curveFamilyOverFieldOfProper_iff_of`: condition
  (2)(b) of Stacks 0E6V for the family of a proper scheme over a field, from the three inputs.

## References

* [Stacks Project, Tag 0E6V](https://stacks.math.columbia.edu/tag/0E6V)
* [Stacks Project, Tag 0E6U](https://stacks.math.columbia.edu/tag/0E6U)
* [Stacks Project, Tag 0E6K](https://stacks.math.columbia.edu/tag/0E6K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

variable (B hZ) in
/-- **The families of `Curves^{prestable}_g` (Stacks 0E6V).** A prestable family of curves
(Stacks 0E6T) lying in `Curves_g` (Stacks 0E6K): `Curves^{prestable}_g` is the intersection
`Curves^{prestable} ∩ Curves_g` of open substacks of `Curves`. -/
abbrev IsPrestableGenusCurveFamily (g : ℕ) (X : CurveFamily B hZ) : Prop :=
  IsPrestableCurveFamily B hZ X ∧ IsGenusCurveFamily B hZ g X

/-- **Condition (1)(b) of Stacks 0E6V.** A family of curves `f : X → S` lies in
`Curves^{prestable}_g` exactly when it is prestable and `R¹f_*𝒪_X` is a locally free
`𝒪_S`-module of rank `g`: a prestable family lies in `Curves^{h0,1}`. -/
theorem isPrestableGenusCurveFamily_iff (g : ℕ) (X : CurveFamily B hZ) :
    IsPrestableGenusCurveFamily B hZ g X ↔
      IsPrestableCurveFamily B hZ X ∧
        RingedSite.IsFiniteLocallyFreeOfRank
          (Space.smallEtaleRingedSite B integerBase hZ (schemeSpace X.base).1
            (schemeSpace X.base).2)
          (X.firstDirectImage B hZ) g :=
  ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, isH01CurveFamily_of_isPrestableCurveFamily h.1, h.2⟩⟩


/-! ### Part (2): a proper scheme of dimension at most one over a field -/

section OverField

variable
    (hpush : ∀ X : CurveFamily B hZ, CurveFamily.HasBijectiveGlobalFunctionsOnFieldFibres B hZ X →
      HasUniversallyBijectiveGlobalFunctions B hZ X)
    (hsch : ∀ (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
      [LocallyOfFiniteType (X ↘ Spec (.of k))],
      IsAtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of k)) ↔
        (Stacks.Curves.HasAtWorstNodalSingularities k X ∧ TopologicalSpace.Equidimensional X ∧
          ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z = (1 : WithBot ℕ∞)))
    (hrk : ∀ (k : Type u) [Field k] {T W : BigFppfOver B integerBase hZ} (p : T ⟶ W)
      (hW : (BigFppfOver.toScheme B integerBase hZ).obj W = Spec (.of k))
      (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map p))
      (hdim : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) ≤ 1),
      IsH01CurveFamily B hZ (curveFamilyOverFieldOfProper B hZ p k hW hproper hdim) →
      RingedSite.IsFiniteLocallyFreeOfRank
        (Space.smallEtaleRingedSite B integerBase hZ
          (schemeSpace (curveFamilyOverFieldOfProper B hZ p k hW hproper hdim).base).1
          (schemeSpace (curveFamilyOverFieldOfProper B hZ p k hW hproper hdim).base).2)
        ((curveFamilyOverFieldOfProper B hZ p k hW hproper hdim).firstDirectImage B hZ)
        (genus ((BigFppfOver.toScheme B integerBase hZ).map p ≫ eqToHom hW)))

include hpush hsch hrk in
/-- **Condition (2)(b) of Stacks 0E6V for the family of a proper scheme over a field.** Let
`p : T ⟶ W` be a proper morphism of the site with `W = Spec k` and `dim(T) ≤ 1`. Its family of
curves lies in `Curves^{prestable}_g` exactly when the singularities of `X = T` are
at-worst-nodal, `dim(X) = 1`, `k = H⁰(X, 𝒪_X)` and the genus of `X` is `g`.

The prestable half is Stacks 0E6U (2) (from Stacks 0E6B (a), `hpush`, and the at-worst-nodal
criterion over a field, `hsch`); the rank half is part (2) of Stacks 0E6K,
`AlgebraicGeometry.CurveFamily.isGenusCurveFamily_curveFamilyOfSchemeMorphism_iff_of`, whose
input `hrk` is that for a family in `Curves^{h0,1}` the module `R¹f_*𝒪_X` over `Spec k` is
locally free of rank the genus `dim_k H¹(X, 𝒪_X)` (Stacks 0BY7). -/
theorem isPrestableGenusCurveFamily_curveFamilyOverFieldOfProper_iff_of (g : ℕ)
    (k : Type u) [Field k] {T W : BigFppfOver B integerBase hZ} (p : T ⟶ W)
    (hW : (BigFppfOver.toScheme B integerBase hZ).obj W = Spec (.of k))
    (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map p))
    (hdim : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) ≤ 1) :
    letI : ((BigFppfOver.toScheme B integerBase hZ).obj T).Over (Spec (.of k)) :=
      ⟨(BigFppfOver.toScheme B integerBase hZ).map p ≫ eqToHom hW⟩
    IsPrestableGenusCurveFamily B hZ g (curveFamilyOverFieldOfProper B hZ p k hW hproper hdim) ↔
      (Stacks.Curves.HasAtWorstNodalSingularities k
          ((BigFppfOver.toScheme B integerBase hZ).obj T) ∧
        topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) = 1 ∧
        Function.Bijective
          ((BigFppfOver.toScheme B integerBase hZ).map p ≫ eqToHom hW).appTop ∧
        genus ((BigFppfOver.toScheme B integerBase hZ).map p ≫ eqToHom hW) = g) := by
  have := hproper
  have hfl := flat_and_locallyOfFinitePresentation_of_obj_eq_specField p k hW hproper
  have hqc : Space.IsQuasiCompact B integerBase hZ (schemeSpaceMap p).hom :=
    Space.isQuasiCompact_yoneda_map B integerBase hZ p inferInstance
  have hsep : Space.IsSeparated B integerBase hZ (schemeSpaceMap p).hom :=
    (Space.isSeparated_yoneda_map_iff B integerBase hZ p).mpr inferInstance
  have hqsep : Space.IsQuasiSeparated B integerBase hZ (schemeSpaceMap p).hom :=
    (Space.isQuasiSeparated_yoneda_map_iff B integerBase hZ p).mpr inferInstance
  have hP := isPrestableCurveFamily_curveFamilyOfSchemeMorphism_iff_of B hZ p k hW hfl.1 hproper
    hfl.2 hqc hsep hqsep hdim hsch
    (CurveFamily.isH01CurveFamily_curveFamilyOfSchemeMorphism_iff_of hpush p k hW hfl.1 hproper
      hfl.2 hqc hsep hqsep hdim)
  have hG := CurveFamily.isGenusCurveFamily_curveFamilyOfSchemeMorphism_iff_of hpush p k hW hfl.1
    hproper hfl.2 hqc hsep hqsep hdim (hrk k p hW hproper hdim) g
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨hn, hd, hb⟩ := hP.1 h1
    exact ⟨hn, hd, hb, (hG.1 h2).2⟩
  · rintro ⟨hn, hd, hb, hg⟩
    exact ⟨hP.2 ⟨hn, hd, hb⟩, hG.2 ⟨⟨hb, hd⟩, hg⟩⟩

end OverField

end AlgebraicGeometry

end
