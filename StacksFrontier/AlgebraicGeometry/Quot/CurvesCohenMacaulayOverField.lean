module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesCohenMacaulayOpenSubstack
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesNodalOverField
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenSubstackOfFibered

/-!
# Part (2) of Stacks 0E0I under the source's own hypotheses

Part (2) of **Stacks 0E0I** reads: for a scheme `X` proper over a field `k` with `dim(X) ≤ 1`,
the classifying morphism `Spec(k) → Curves` factors through `Curves^{CM}` exactly when `X` is
Cohen–Macaulay. The source assumes nothing beyond properness and the dimension bound, because
over a field the remaining conditions making `X → Spec(k)` a family of curves are automatic.

`AlgebraicGeometry.lifts_cohenMacaulayCurves_iff_of_field` states part (2) for the family of
curves `AlgebraicGeometry.curveFamilyOfSchemeMorphism` and so inherits that construction's five
further hypotheses — flatness and local finite presentation of the morphism of schemes, and
quasi-compactness, separatedness and quasi-separatedness of the induced morphism of algebraic
spaces. All five are discharged over a field by
`AlgebraicGeometry.curveFamilyOfProperOverFieldEqSpec`, which part (2) of Stacks 0DSY is already
stated on; this file restates part (2) of Stacks 0E0I on the same family, so with the source's
hypotheses and nothing else.

## Main results

* `AlgebraicGeometry.isCohenMacaulayFamily_curveFamilyOfProperOverField_iff`: the family of
  curves attached to a scheme proper over a field with `dim ≤ 1` is Cohen–Macaulay exactly when
  that scheme is.
* `AlgebraicGeometry.lifts_cohenMacaulayCurves_iff_of_properOverField` and
  `AlgebraicGeometry.lifts_cohenMacaulayCurvesInclusion_curveFamilyOfProperOverField_iff`:
  part (2) of Stacks 0E0I, under exactly the source's hypotheses — a scheme proper over a
  field with `dim ≤ 1` lifts through the inclusion `Curves^{CM} ⊂ Curves` exactly when it is
  Cohen–Macaulay. The first reads the inclusion as that of the strictly full subcategory
  `AlgebraicGeometry.CurvesCM`, the second as the 1-morphism
  `AlgebraicGeometry.cohenMacaulayCurvesInclusion` whose representability and open-immersion
  properties are the substack content.
* `AlgebraicGeometry.exists_cohenMacaulayCurves_openSubstack`: **Stacks 0E0I** — the open
  substack `Curves^{CM} ⊂ Curves` exists, and parts (1) and (2) hold for it.

## Implementation notes

`AlgebraicGeometry.exists_cohenMacaulayCurves_openSubstack` states the whole lemma: the existence
of the open substack `Curves^{CM} ⊂ Curves`, in the sense of
`AlgebraicGeometry.Stack.FiberedOpenSubstack`, together with parts (1) and (2). That notion of
open substack is Stacks 04YM without its clause that `Curves^{CM}` be an algebraic stack, a
clause which for an algebraic `Curves` follows from the others by Stacks 05UM
(`AlgebraicGeometry.Stack.openSubstackEquivFibered`), so no presentation of `Curves` as an
algebraic stack (Stacks 0D5A) enters.

## References

* [Stacks Project, Tag 0E0I](https://stacks.math.columbia.edu/tag/0E0I)
* [Stacks Project, Tag 0D4Z](https://stacks.math.columbia.edu/tag/0D4Z)
* [Stacks Project, Tag 04YM](https://stacks.math.columbia.edu/tag/04YM)
* [Stacks Project, Tag 05UM](https://stacks.math.columbia.edu/tag/05UM)
-/


@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- **Part (2) of Stacks 0E0I, on the family of curves.** The family of curves attached to a
scheme proper over a field whose topological Krull dimension is at most one is Cohen–Macaulay
exactly when that scheme is Cohen–Macaulay. -/
theorem isCohenMacaulayFamily_curveFamilyOfProperOverField_iff
    {T W : BigFppfOver B integerBase hZ} (g : T ⟶ W) (k : Type u) [Field k]
    (hW : (BigFppfOver.toScheme B integerBase hZ).obj W = Spec (.of k))
    (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hdim : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) ≤ 1) :
    IsCohenMacaulayFamily B hZ (curveFamilyOfProperOverFieldEqSpec B hZ g k hW hproper hdim) ↔
      IsCohenMacaulay ((BigFppfOver.toScheme B integerBase hZ).obj T) :=
  have := hproper
  isCohenMacaulayFamily_curveFamilyOfSchemeMorphism_iff B hZ g
    (flat_and_locallyOfFinitePresentation_of_target_eq_spec _ k hW).1 hproper
    (flat_and_locallyOfFinitePresentation_of_target_eq_spec _ k hW).2
    (Space.isQuasiCompact_yoneda_map_of_quasiCompact B integerBase hZ g inferInstance)
    ((Space.isSeparated_yoneda_map_iff B integerBase hZ g).mpr inferInstance)
    ((Space.isQuasiSeparated_yoneda_map_iff B integerBase hZ g).mpr inferInstance)
    hdim k hW

/-- **Part (2) of Stacks 0E0I, under exactly the source's hypotheses.** Let `X` be a scheme
proper over a field `k` whose topological Krull dimension is at most one. Then the family of
curves `X → Spec(k)` lifts through the inclusion `Curves^{CM} ⊂ Curves` exactly when `X` is
Cohen–Macaulay.

Nothing is assumed beyond properness of the morphism of schemes and the dimension bound, which
are the source's own hypotheses: the flatness and the local finite presentation of the morphism
and the quasi-compactness, separatedness and quasi-separatedness of the induced morphism of
algebraic spaces are all discharged, so the family of curves is
`AlgebraicGeometry.curveFamilyOfProperOverFieldEqSpec`. -/
theorem lifts_cohenMacaulayCurves_iff_of_properOverField
    {T W : BigFppfOver B integerBase hZ} (g : T ⟶ W) (k : Type u) [Field k]
    (hW : (BigFppfOver.toScheme B integerBase hZ).obj W = Spec (.of k))
    (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hdim : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) ≤ 1) :
    (∃ Y : CurvesCM B hZ, Y.obj = curveFamilyOfProperOverFieldEqSpec B hZ g k hW hproper hdim) ↔
      IsCohenMacaulay ((BigFppfOver.toScheme B integerBase hZ).obj T) :=
  (lifts_cohenMacaulayCurves_iff B hZ _).trans
    (isCohenMacaulayFamily_curveFamilyOfProperOverField_iff B hZ g k hW hproper hdim)

/-- **Part (2) of Stacks 0E0I, under exactly the source's hypotheses, through the inclusion
1-morphism.** Let `X` be a scheme proper over a field `k` whose topological Krull dimension is
at most one. Then the classifying morphism `Spec(k) → Curves` factors through the open substack
`Curves^{CM}` — that is, the family of curves `X → Spec(k)` is in the image on objects of
`AlgebraicGeometry.cohenMacaulayCurvesInclusion` — exactly when `X` is Cohen–Macaulay.

Nothing is assumed beyond properness of the morphism of schemes and the dimension bound, which
are the source's own hypotheses. -/
theorem lifts_cohenMacaulayCurvesInclusion_curveFamilyOfProperOverField_iff
    {T W : BigFppfOver B integerBase hZ} (g : T ⟶ W) (k : Type u) [Field k]
    (hW : (BigFppfOver.toScheme B integerBase hZ).obj W = Spec (.of k))
    (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hdim : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) ≤ 1) :
    (∃ Y : (cohenMacaulayCurvesFibered B hZ).based.obj,
        (CatFiberedInGroupoids.homFunctor (cohenMacaulayCurvesInclusion B hZ)).obj Y =
          curveFamilyOfProperOverFieldEqSpec B hZ g k hW hproper hdim) ↔
      IsCohenMacaulay ((BigFppfOver.toScheme B integerBase hZ).obj T) :=
  (lifts_cohenMacaulayCurvesInclusion_iff B hZ _).trans
    (isCohenMacaulayFamily_curveFamilyOfProperOverField_iff B hZ g k hW hproper hdim)

/-- There is an open substack `Curves^{CM} ⊂ Curves` such that

1. for a family of curves `X → S`, the classifying morphism `S → Curves` factors through
   `Curves^{CM}` if and only if `X → S` is Cohen–Macaulay;
2. for a scheme `X` proper over a field `k` with `dim(X) ≤ 1`, the classifying morphism
   `Spec(k) → Curves` factors through `Curves^{CM}` if and only if `X` is Cohen–Macaulay.

`Curves` is the category fibred in groupoids of families of curves of Stacks 0D4Z,
`AlgebraicGeometry.curvesFiberedCategory`, over the big fppf site of `Spec(ℤ)`, and an open
substack is an `AlgebraicGeometry.Stack.FiberedOpenSubstack`: a strictly full subcategory, fibred
in groupoids (so closed under base change), whose inclusion is representable by algebraic spaces
and an open immersion. That is Stacks 04YM without its clause "`Curves^{CM}` is an algebraic
stack", which for an algebraic `Curves` follows from the others by Stacks 05UM, so that the two
notions agree there (`AlgebraicGeometry.Stack.openSubstackEquivFibered`); the source produces the
open substack by the method of Section 109.6, which only uses the open locus in the base and its
compatibility with base change, and nothing here depends on `Curves` being algebraic (Stacks
0D5A).

The classifying morphism of a family `F` factoring through `Curves^{CM}` is `F` lying in the image
on objects of the inclusion `Curves^{CM} → Curves`; in part (2) the family is
`AlgebraicGeometry.curveFamilyOfProperOverFieldEqSpec`, the family `X → Spec(k)` attached to a
proper morphism `g` of the site onto the spectrum of a field, and dimension is topological Krull
dimension. -/
@[stacks 0E0I]
theorem exists_cohenMacaulayCurves_openSubstack :
    ∃ U : Stack.FiberedOpenSubstack (curvesFiberedCategory B hZ),
      (∀ F : CurveFamily B hZ,
        (∃ Y : U.toFibered.val.obj, (CatFiberedInGroupoids.homFunctor U.inclusion).obj Y = F) ↔
          IsCohenMacaulayFamily B hZ F) ∧
      (∀ {T W : BigFppfOver B integerBase hZ} (g : T ⟶ W) (k : Type u) [Field k]
          (hW : (BigFppfOver.toScheme B integerBase hZ).obj W = Spec (.of k))
          (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map g))
          (hdim : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) ≤ 1),
        (∃ Y : U.toFibered.val.obj, (CatFiberedInGroupoids.homFunctor U.inclusion).obj Y =
            curveFamilyOfProperOverFieldEqSpec B hZ g k hW hproper hdim) ↔
          IsCohenMacaulay ((BigFppfOver.toScheme B integerBase hZ).obj T)) := by
  let U := curvesFiberedOpenSubstackOfBaseLocus B hZ
    (show ObjectProperty (CurveFamily B hZ) from IsCohenMacaulayFamily B hZ)
    (fun a hG => CurveFamily.isCohenMacaulayFamily_of_hom B hZ a hG)
    (CurveFamily.exists_cohenMacaulay_baseOpen B hZ)
  have hU : ∀ F : CurveFamily B hZ, U.property F ↔ IsCohenMacaulayFamily B hZ F := fun F => by
    rw [curvesFiberedOpenSubstackOfBaseLocus_property]
  have h := fun F => (U.exists_obj_eq_iff F).trans (hU F)
  exact ⟨U, h, fun g k _ hW hproper hdim =>
    (h _).trans (isCohenMacaulayFamily_curveFamilyOfProperOverField_iff B hZ g k hW hproper hdim)⟩

end AlgebraicGeometry

end
