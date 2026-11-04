module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesGenus
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesSmoothH0
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesStableOpen
public import StacksFrontier.AlgebraicGeometry.Quot.ModuliCurves
public import StacksFrontier.AlgebraicGeometry.Quot.ModuliStableCurvesOfGenusOpen

/-!
# Condition (o) for `𝓜̄`, `𝓜̄_g` and `𝓜_g` (towards Stacks 0E76, 0E78 and 0E83)

The theorems of Stacks 0E79, 0E9A and 0E78 on the moduli stacks of stable and of smooth curves
consume the openness of three loci of the stack of curves, in the form of condition (o) of
Section 0E0E (`AlgebraicGeometry.IsOpenCurvesLocus`):

* `𝓜̄ = Curves^{stable}`: the stable families (Stacks 0E75), open by Stacks 0E76;
* `𝓜̄_g`: the stable families with `R¹f_*𝒪_X` locally free of rank `g` (Stacks 0E78);
* `𝓜_g`: the families smooth of relative dimension one with `f_*𝒪_X = 𝒪_S` universally and
  `R¹f_*𝒪_X` locally free of rank `g` (Stacks 0E83).

This file assembles the three statements in exactly the shapes those consumers take them, from
the source's own inputs.

## Main results

* `AlgebraicGeometry.isOpenCurvesLocus_isStableCurveFamily_of_isH01`: condition (o) for `𝓜̄`
  (the openness of Stacks 0E76).
* `AlgebraicGeometry.isOpenCurvesLocus_isGenusCurveFamily_of_isH01`: condition (o) for
  `Curves_g ⊂ Curves^{h0,1}` (part (1) of Stacks 0E6K).
* `AlgebraicGeometry.isOpenCurvesLocus_isStableCurveFamilyOfGenus_of_isH01`: condition (o) for
  `𝓜̄_g` (the openness part of Stacks 0E78).
* `AlgebraicGeometry.isOpenCurvesLocus_isSmoothH0Family_and_hasGenus_of_isH01`: condition (o)
  for `𝓜_g` (part (1) of Stacks 0E83).

## Implementation notes

No declaration here carries a `stacks` attribute: each takes the results of other tags it rests
on as explicit hypotheses, as in the source's proofs.

* `h0E6I`: condition (o) for `Curves^{h0,1}`, the openness of Stacks 0E6I. With Stacks 0DSY it
  gives `Curves^{prestable} = Curves^{nodal} ∩ Curves^{h0,1}` (Stacks 0E6U), and with Stacks
  0DZZ it gives `Curves^{smooth,h0} = Curves^{smooth,1} ∩ Curves^{h0,1}` (Stacks 0E81).
* `hrel`: the stable-fibre condition of Stacks 0E75 satisfies condition (o) relative to prestable
  families (`AlgebraicGeometry.IsOpenCurvesLocusWithin`): over a prestable family, the points of
  the base with a stable fibre form an open, and formation of that open commutes with base
  change. This is what the source's proof of Stacks 0E76 extracts from Stacks 0E74 (the fibre is
  stable exactly when `ω_{X/S}` is ample near it), Stacks 0D3D (the relatively ample locus is
  open) and the insensitivity of stability to ground field extension (Stacks 0E3L, 0E3Q, 0D2P).
* `h2`, `h3`: parts (2) and (3) of Stacks 0E1J: over a family with `κ(s) = H⁰(X_s, 𝒪_{X_s})` for
  all `s`, `R¹f_*𝒪_X` is finite locally free and its formation commutes with base change. These
  are the inputs of the genus decomposition of Stacks 0E6K.

The genus statement repeats the proof of
`AlgebraicGeometry.isOpenCurvesLocus_isGenusCurveFamily_of` with condition (o) for `Curves^{h0,1}`
in place of its two cohomological inputs, which is all of them that proof uses.

## References

* [Stacks Project, Tag 0E76](https://stacks.math.columbia.edu/tag/0E76)
* [Stacks Project, Tag 0E78](https://stacks.math.columbia.edu/tag/0E78)
* [Stacks Project, Tag 0E83](https://stacks.math.columbia.edu/tag/0E83)
* [Stacks Project, Tag 0E6K](https://stacks.math.columbia.edu/tag/0E6K)
* [Stacks Project, Tag 0E6I](https://stacks.math.columbia.edu/tag/0E6I)
* [Stacks Project, Tag 0E74](https://stacks.math.columbia.edu/tag/0E74)
* [Stacks Project, Tag 0E1J](https://stacks.math.columbia.edu/tag/0E1J)
* [Stacks Project, Tag 0E0E](https://stacks.math.columbia.edu/tag/0E0E)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

attribute [local instance] Space.pointTopology

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- **Condition (o) for `𝓜̄ = Curves^{stable}`** (the openness of Stacks 0E76). From condition (o)
for `Curves^{h0,1}` (`h0E6I`, Stacks 0E6I), which with Stacks 0DSY gives condition (o) for
`Curves^{prestable}` (Stacks 0E6U), and the openness of the stable-fibre locus of a prestable
family together with the compatibility of its formation with base change (`hrel`, Stacks 0E74
with Stacks 0D3D). -/
theorem isOpenCurvesLocus_isStableCurveFamily_of_isH01
    (h0E6I : IsOpenCurvesLocus B hZ (IsH01CurveFamily B hZ))
    (hrel : IsOpenCurvesLocusWithin B hZ (IsPrestableCurveFamily B hZ)
      (CurveFamily.HasStableFibres B hZ)) :
    IsOpenCurvesLocus B hZ (IsStableCurveFamily B hZ) :=
  isOpenCurvesLocus_isStableCurveFamily_of_prestable
    (isOpenCurvesLocus_isPrestableCurveFamily_of h0E6I) hrel

/-- **Condition (o) for `Curves_g`** (part (1) of Stacks 0E6K). Over a family `G` in
`Curves^{h0,1}`, `R¹f_*𝒪_G` is finite locally free and its formation commutes with base change
(`h2`, `h3`, Stacks 0E1J), so a family mapping to `G` is in `Curves_g` exactly when its base maps
into the open rank locus of `g`; and `Curves^{h0,1}` is open (`h0E6I`, Stacks 0E6I). -/
theorem isOpenCurvesLocus_isGenusCurveFamily_of_isH01 (g : ℕ)
    (h0E6I : IsOpenCurvesLocus B hZ (IsH01CurveFamily B hZ))
    (h2 : ∀ X : CurveFamily B hZ, X.HasResidueFieldGlobalFunctions →
      X.HasFiniteLocallyFreeFirstHigherDirectImage)
    (h3 : ∀ X : CurveFamily B hZ, X.HasResidueFieldGlobalFunctions →
      X.FirstHigherDirectImageCommutesWithBaseChange) :
    IsOpenCurvesLocus B hZ (IsGenusCurveFamily B hZ g) := by
  refine IsOpenCurvesLocus.of_points_of_isOpenCurvesLocus h0E6I (fun _ h => h.1) fun G hG =>
    ⟨Space.rankLocus (G.firstDirectImage B hZ) g, Space.isOpen_rankLocus _ g, fun F a => ?_⟩
  have hres := CurveFamily.hasResidueFieldGlobalFunctions_of_hasUniversallyBijectiveGlobalFunctions
    hG.1
  have hR : SheafOfModules.IsFiniteLocallyFreeOnSite (G.firstDirectImage B hZ) :=
    Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_of_isFiniteLocallyFree _ (h2 G hres)
  have hF : IsH01CurveFamily B hZ F := h0E6I.prop_of_hom a hG
  obtain ⟨e⟩ := h3 G hres F a
  rw [← Space.isFiniteLocallyFreeOfRank_modulePullback_iff (schemeSpaceMap a.baseMap) hR g]
  exact ⟨fun h => RingedSite.IsFiniteLocallyFreeOfRank.of_iso _ _ e.symm h.2,
    fun h => ⟨hF, RingedSite.IsFiniteLocallyFreeOfRank.of_iso _ _ e h⟩⟩

/-- **Condition (o) for `𝓜̄_g`** (the openness part of Stacks 0E78): `𝓜̄_g = 𝓜̄ ∩ Curves_g`,
from condition (o) for `𝓜̄` (`AlgebraicGeometry.isOpenCurvesLocus_isStableCurveFamily_of_isH01`)
and for `Curves_g` (`AlgebraicGeometry.isOpenCurvesLocus_isGenusCurveFamily_of_isH01`), a stable
family being in `Curves^{h0,1}`. -/
theorem isOpenCurvesLocus_isStableCurveFamilyOfGenus_of_isH01 (g : ℕ)
    (h0E6I : IsOpenCurvesLocus B hZ (IsH01CurveFamily B hZ))
    (hrel : IsOpenCurvesLocusWithin B hZ (IsPrestableCurveFamily B hZ)
      (CurveFamily.HasStableFibres B hZ))
    (h2 : ∀ X : CurveFamily B hZ, X.HasResidueFieldGlobalFunctions →
      X.HasFiniteLocallyFreeFirstHigherDirectImage)
    (h3 : ∀ X : CurveFamily B hZ, X.HasResidueFieldGlobalFunctions →
      X.FirstHigherDirectImageCommutesWithBaseChange) :
    IsOpenCurvesLocus B hZ (IsStableCurveFamilyOfGenus B hZ g) :=
  ((isOpenCurvesLocus_isStableCurveFamily_of_isH01 B hZ h0E6I hrel).and
      (isOpenCurvesLocus_isGenusCurveFamily_of_isH01 B hZ g h0E6I h2 h3)).of_iff fun _ =>
    ⟨fun h => ⟨h.1, h.2.2⟩,
      fun h => ⟨h.1, isH01CurveFamily_of_isPrestableCurveFamily h.1.1, h.2⟩⟩

/-- **Condition (o) for `𝓜_g`** (part (1) of Stacks 0E83): `𝓜_g = Curves^{smooth,h0} ∩ Curves_g`,
from condition (o) for `Curves^{smooth,h0}` (Stacks 0E81, from `h0E6I` and Stacks 0DZZ) and for
`Curves_g` (`AlgebraicGeometry.isOpenCurvesLocus_isGenusCurveFamily_of_isH01`). The property is
the one cutting out `𝓜_g` in the separatedness of `𝓜̄_g` (Stacks 0E9A): smooth of relative
dimension one, `f_*𝒪_X = 𝒪_S` universally, and `R¹f_*𝒪_X` locally free of rank `g`. -/
theorem isOpenCurvesLocus_isSmoothH0Family_and_hasGenus_of_isH01 (g : ℕ)
    (h0E6I : IsOpenCurvesLocus B hZ (IsH01CurveFamily B hZ))
    (h2 : ∀ X : CurveFamily B hZ, X.HasResidueFieldGlobalFunctions →
      X.HasFiniteLocallyFreeFirstHigherDirectImage)
    (h3 : ∀ X : CurveFamily B hZ, X.HasResidueFieldGlobalFunctions →
      X.FirstHigherDirectImageCommutesWithBaseChange) :
    IsOpenCurvesLocus B hZ
      (fun X => IsSmoothH0Family B hZ X ∧ CurveFamily.HasGenus B hZ X g) :=
  ((isOpenCurvesLocus_isSmoothH0CurveFamily_of h0E6I).and
      (isOpenCurvesLocus_isGenusCurveFamily_of_isH01 B hZ g h0E6I h2 h3)).of_iff fun X =>
    ⟨fun h => ⟨⟨h.1.2, h.1.1⟩, h.2.2⟩,
      fun h => ⟨⟨h.1.2, h.1.1⟩, ((isSmoothH0CurveFamily_iff X).1 ⟨h.1.2, h.1.1⟩).1, h.2⟩⟩

end AlgebraicGeometry

end
