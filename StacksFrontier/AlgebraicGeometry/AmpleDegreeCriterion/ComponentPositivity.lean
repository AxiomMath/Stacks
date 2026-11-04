module

public import StacksFrontier.AlgebraicGeometry.AmpleCurve.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.CurveInputs
public import StacksFrontier.AlgebraicGeometry.AmplePullback.Affine
public import StacksFrontier.AlgebraicGeometry.ComponentDegrees.Degree
public import StacksFrontier.AlgebraicGeometry.CurveDegreeTensor.Devissage
public import StacksFrontier.AlgebraicGeometry.InvertibleClasses.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.NonpositiveDegreeSection
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SectionDegree
import StacksCore.Tactic.StacksAttribute

/-!
# Positive degree on the one-dimensional components of an ample invertible module

[Stacks, Tag 0B5Y] says: let `k` be a field, let `X` be a proper scheme over `k` of dimension at
most one, let `𝓛` be an invertible `𝒪_X`-module and let `C₁, …, C_t ⊆ X` be the irreducible
components of dimension one. Then

1. `𝓛` is ample

if and only if

2. `deg(𝓛|_{C_i}) > 0` for every `i`.

This file proves the implication (1) ⟹ (2) with no hypothesis beyond the tag's own, at the tag's
own indexing: the `C_i` are the one-dimensional irreducible components of `X` taken with their
reduced induced closed subscheme structure, which is
`Stacks.AlgebraicGeometry.ComponentDegrees.reducedComponent` indexed by the generic points
`Stacks.AlgebraicGeometry.ComponentDegrees.genericPointsOne X` of the components of dimension
one.

Getting there needs the forward direction of [Stacks, Tag 0B5X] on a proper curve with no
hypothesis, and that in turn needs the invertible case of [Stacks, Tag 0AYX]. Both are proved
below, so the whole of the implication rests on proved results.

## Main results

The elided prefix is `AlgebraicGeometry`.

* `invertibleCurveDegree_tensorSheaf_eq_add_of_topologicalKrullDim_le_one`: **the invertible case
  of [Stacks, Tag 0AYX]**, `deg(ℳ ⊗ 𝒩) = deg(ℳ) + deg(𝒩)`, with no hypothesis.
* `invertibleCurveDegree_tensorPower_eq_mul_of_topologicalKrullDim_le_one`:
  `deg(𝓛^{⊗ n}) = n · deg(𝓛)` for every integer `n`, with no hypothesis.
* `invertibleCurveDegree_pos_of_isAmple_of_isCurve`: **the implication "ample ⟹ positive degree"
  of [Stacks, Tag 0B5X]** on a proper curve over a field, with no hypothesis.
* `invertibleCurveDegree_pullback_pos_of_isAmple`: the same on a closed subscheme of `X` that is
  a proper curve over `k`.
* `invertibleCurveDegree_reducedComponent_pos_of_isAmple`: **the implication (1) ⟹ (2) of
  [Stacks, Tag 0B5Y]** at the tag's own indexing.

## How the hypotheses of the degree reduction are discharged

`AlgebraicGeometry.invertibleCurveDegree_pos_of_isAmple` of `../AmpleCurve/Basic.lean` reduces
the forward direction of [Stacks, Tag 0B5X] to two degree computations, `hmul` and `hpos`, and
both are proved results.

**`hmul` is the invertible case of [Stacks, Tag 0AYX].** The tag itself — for finite locally free
sheaves of constant ranks on a proper scheme of dimension at most one — is
`AlgebraicGeometry.curveDegree_tensorSheaf_eq_add_of_topologicalKrullDim_le_one`, proved with no
hypothesis in `../CurveDegreeTensor/Devissage.lean`. An invertible module is finite locally free
of rank one (`AlgebraicGeometry.SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible`)
and the two degrees then agree by
`AlgebraicGeometry.invertibleCurveDegree_eq_curveDegree`, so the tag at both ranks equal to one
is the invertible case, and
`AlgebraicGeometry.invertibleCurveDegree_tensorPower_eq_mul` ascends it to the tensor powers.

**`hpos` is part (2) of [Stacks, Tag 0B40]**,
`AlgebraicGeometry.invertibleCurveDegree_pos_of_eval_top_ne_zero`, proved with no hypothesis in
`../Variety/Curve/SectionDegree.lean`: an invertible module on a proper integral scheme of
dimension at most one over a field with a nonzero global section vanishing somewhere has positive
degree. A section whose nonvanishing locus is nonempty is nonzero
(`AlgebraicGeometry.eval_top_ne_zero_of_mem_nonvanishingLocus`), a nonvanishing locus that is not
everything misses a point, and a curve is integral because it is a variety.

## Implementation notes

**The degree is applied with its instance arguments written out.** `invertibleCurveDegree` takes
properness and invertibility as instance arguments, and at the component neither is found by
instance search: properness of `C_i ⟶ Spec k` is
`Stacks.AlgebraicGeometry.ComponentDegrees.isProper_reducedComponentι_comp` and invertibility of
the restriction of `𝓛` is `AlgebraicGeometry.SheafOfModules.isInvertible_pullback`. They are
therefore passed positionally with `@`, which also keeps them out of the binder list: no
hypothesis of the statements below is anything other than the tag's own.

**Two spellings of the tensor product of sheaves of modules occur, and they are the same term.**
[Stacks, Tag 0AYX] is stated with
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf X.toRingedSpace`, while the hypothesis
`hadd` of `AlgebraicGeometry.invertibleCurveDegree_tensorPower_eq_mul` is stated with
`Stacks.SheafOfModules.TensorSheafification.tensorSheaf X.toRingedSpace.presheaf
(structureSheafRing X.toRingedSpace).property`. They are definitionally equal, and the
local-freeness instance that the first carries is transported to the second by `rfl` on the whole
`curveDegree` application, which is possible because
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank` is `Prop`-valued. Rewriting between
the two spellings fails its motive check, which is why the identification is a `rfl`-proved
equation between the two degree applications rather than a `rw`.

**Instance search does not see the local-freeness of a tensor product.** The tensor sheaf is
typed as a bare `SheafOfModules (structureSheafRing X.toRingedSpace)` rather than as `X.Modules`,
and `AlgebraicGeometry.SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible` is keyed on
the latter, so the instance has to be named and passed; otherwise the failure is reported at
the statement of the comparison.

## References

* [Stacks Project, Tag 0B5Y](https://stacks.math.columbia.edu/tag/0B5Y)
* [Stacks Project, Tag 0B5X](https://stacks.math.columbia.edu/tag/0B5X)
* [Stacks Project, Tag 0AYX](https://stacks.math.columbia.edu/tag/0AYX)
* [Stacks Project, Tag 0AYR](https://stacks.math.columbia.edu/tag/0AYR)
* [Stacks Project, Tag 0B40](https://stacks.math.columbia.edu/tag/0B40)
* [Stacks Project, Tag 01PU](https://stacks.math.columbia.edu/tag/01PU)
* [Stacks Project, Tag 0A23](https://stacks.math.columbia.edu/tag/0A23)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.SheafOfModules (nonvanishingLocus)
open Stacks.SheafOfModules.Invertible (tensorPower tensorPower_isInvertible)
open Stacks.AlgebraicGeometry.ComponentDegrees

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-! ### The invertible case of [Stacks, Tag 0AYX] -/

/-- **The invertible case of [Stacks, Tag 0AYX]**: `deg(ℳ ⊗ 𝒩) = deg(ℳ) + deg(𝒩)` for `ℳ` and
`𝒩` invertible on a scheme proper of dimension at most one over a field. **No hypothesis.**

Both ranks are one, so the tag's `rank(ℳ)·deg(𝒩) + rank(𝒩)·deg(ℳ)` reads as the plain sum. The
three invertibility witnesses are explicit arguments rather than instances, matching the
hypothesis `hadd` of `AlgebraicGeometry.invertibleCurveDegree_tensorPower_eq_mul`; this is no
strengthening, because the body of `AlgebraicGeometry.invertibleCurveDegree` does not mention its
instance argument, so any two witnesses give the same degree.

This supersedes `AlgebraicGeometry.invertibleCurveDegree_tensorSheaf_eq_add_of_devissage`, which
reaches the same equation through the dévissage of [Stacks, Tag 01YH] and [Stacks, Tag 02O6]; the
rank-general tag is proved outright, and the invertible case is read off it. -/
public theorem invertibleCurveDegree_tensorSheaf_eq_add_of_topologicalKrullDim_le_one [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (M N : X.Modules)
    (hM : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M)
    (hN : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N)
    (hMN : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.toRingedSpace.presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ (X.toRingedSpace.presheaf)
          (forget₂ CommRingCat RingCat)
          ((structureSheafRing X.toRingedSpace).property)⟩).obj (M)).obj (N)))) :
    @invertibleCurveDegree k _ X f _ hdim
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.toRingedSpace.presheaf,
          Presheaf.isSheaf_of_isSheaf_comp _ (X.toRingedSpace.presheaf)
            (forget₂ CommRingCat RingCat)
            ((structureSheafRing X.toRingedSpace).property)⟩).obj (M)).obj (N))) hMN =
      @invertibleCurveDegree k _ X f _ hdim M hM +
        @invertibleCurveDegree k _ X f _ hdim N hN := by
  have := hM
  have := hN
  have := hMN
  have h := curveDegree_tensorSheaf_eq_add_of_topologicalKrullDim_le_one k f hdim M N 1 1
  have e : ∀ (P : X.Modules) (hP : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 P),
      @invertibleCurveDegree k _ X f _ hdim P hP = curveDegree k f hdim P 1 := fun P hP =>
    have := hP
    have := SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X P
    invertibleCurveDegree_eq_curveDegree k f hdim P
  have hTfl : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.toRingedSpace.presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ (X.toRingedSpace.presheaf)
          (forget₂ CommRingCat RingCat)
          ((structureSheafRing X.toRingedSpace).property)⟩).obj (M)).obj (N))) 1 :=
    SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X _
  have hspell : @curveDegree k _ X f _ hdim
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.toRingedSpace.presheaf,
          Presheaf.isSheaf_of_isSheaf_comp _ (X.toRingedSpace.presheaf)
            (forget₂ CommRingCat RingCat)
            ((structureSheafRing X.toRingedSpace).property)⟩).obj (M)).obj (N))) 1 hTfl
      = @curveDegree k _ X f _ hdim
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
          ((X.toRingedSpace)).IsSheaf⟩).obj (M)).obj (N))) (1 * 1)
        (SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf X M N 1 1) := rfl
  rw [e M hM, e N hN, e _ hMN, hspell, h]
  push_cast
  ring

/-- **The degree of a tensor power of an invertible module on a proper scheme of dimension at most
one over a field**, `deg(𝓛^{⊗ n}) = n · deg(𝓛)` for every integer `n`. **No hypothesis.**

`AlgebraicGeometry.invertibleCurveDegree_tensorPower_eq_mul` ascends additivity in the tensor
product from exponent zero in both directions; the additivity is the invertible case of
[Stacks, Tag 0AYX] above. -/
public theorem invertibleCurveDegree_tensorPower_eq_mul_of_topologicalKrullDim_le_one [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L] (n : ℤ) :
    @invertibleCurveDegree k _ X f _ hdim
        (tensorPower X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property L n)
        (tensorPower_isInvertible X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property L n) =
      n * invertibleCurveDegree k f hdim L :=
  invertibleCurveDegree_tensorPower_eq_mul k f hdim L
    (invertibleCurveDegree_tensorSheaf_eq_add_of_topologicalKrullDim_le_one k f hdim) n

/-! ### The implication (1) ⟹ (2) of [Stacks, Tag 0B5Y] -/

/-- **The implication (1) ⟹ (2) of [Stacks, Tag 0B5Y] at an arbitrary closed subcurve.** Let `X`
be proper over a field `k`, let `𝓛` be an ample invertible `𝒪_X`-module, and let `i : C ⟶ X` be a
closed immersion whose source is a proper curve over `k`. Then `deg(𝓛|_C) > 0`.

The restriction `𝓛|_C` is ample by [Stacks, Tag 01PU],
`AlgebraicGeometry.Scheme.Modules.isAmple_pullback_of_isClosedImmersion`, and the implication
"ample ⟹ positive degree" of [Stacks, Tag 0B5X] on the curve `C` gives the positivity. -/
public theorem invertibleCurveDegree_pullback_pos_of_isAmple [IsProper f] {C : Scheme.{u}}
    (i : C ⟶ X) [IsClosedImmersion i] [IsCurve k (i ≫ f)]
    (hdim : topologicalKrullDim C ≤ 1) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hL : Scheme.Modules.IsAmple X L) :
    0 < @invertibleCurveDegree k _ C (i ≫ f) inferInstance hdim
      ((Scheme.Modules.pullback i).obj L)
      (SheafOfModules.isInvertible_pullback i L) :=
  have hinv := SheafOfModules.isInvertible_pullback i L
  @invertibleCurveDegree_pos_of_isAmple_of_isCurve k _ C (i ≫ f) _ inferInstance hdim _ hinv
    (Scheme.Modules.isAmple_pullback_of_isClosedImmersion i L hL)

/-- **The implication (1) ⟹ (2) of [Stacks, Tag 0B5Y].** Let `k` be a field, let `X` be proper of
dimension at most one over `k` and let `𝓛` be an ample invertible `𝒪_X`-module. Then the degree
of the restriction of `𝓛` to every one-dimensional irreducible component of `X`, taken with its
reduced induced closed subscheme structure, is positive.

The components of dimension one are indexed by their generic points,
`Stacks.AlgebraicGeometry.ComponentDegrees.genericPointsOne X`, and the reduced induced subscheme
is `Stacks.AlgebraicGeometry.ComponentDegrees.reducedComponent`; that it is a proper curve over
`k` — integral, separated, of finite type and of dimension exactly one — is
`Stacks.AlgebraicGeometry.ComponentDegrees.isCurve_reducedComponentι_comp` together with
`Stacks.AlgebraicGeometry.ComponentDegrees.isProper_reducedComponentι_comp`, both proved with no
hypothesis. So this is the tag's own family `C₁, …, C_t` and its own conclusion.

**No hypothesis beyond the tag's own.** The reverse implication is
`AlgebraicGeometry.isAmple_iff_forall_invertibleCurveDegree_reducedComponent_pos` of
`ComponentCriterion.lean`, which states the full equivalence. -/
@[stacks 0B5Y "the implication (1) ⟹ (2), at the tag's own indexing by the one-dimensional \
  irreducible components with their reduced induced structure, with no hypothesis beyond the \
  tag's own; the full equivalence is registered on \
  `isAmple_iff_forall_invertibleCurveDegree_reducedComponent_pos`"]
public theorem invertibleCurveDegree_reducedComponent_pos_of_isAmple [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hL : Scheme.Modules.IsAmple X L) (ξ : genericPointsOne X) :
    0 < @invertibleCurveDegree k _ (reducedComponent X ξ) (reducedComponentι X ξ ≫ f)
      (isProper_reducedComponentι_comp k f ξ)
      (topologicalKrullDim_reducedComponent_le X hdim ξ)
      ((Scheme.Modules.pullback (reducedComponentι X ξ)).obj L)
      (SheafOfModules.isInvertible_pullback (reducedComponentι X ξ) L) :=
  have := isProper_reducedComponentι_comp k f ξ
  have := isCurve_reducedComponentι_comp k f ξ
  invertibleCurveDegree_pullback_pos_of_isAmple k f (reducedComponentι X ξ)
    (topologicalKrullDim_reducedComponent_le X hdim ξ) L hL

end AlgebraicGeometry

end
