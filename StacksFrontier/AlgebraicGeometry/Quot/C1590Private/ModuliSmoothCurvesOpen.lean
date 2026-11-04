module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurvesPrestableGenus
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesCohenMacaulayDimOne
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesSmoothH0
public import StacksFrontier.AlgebraicGeometry.Quot.ModuliSmoothCurvesStable
public import StacksFrontier.AlgebraicGeometry.Quot.ModuliStableCurvesOfGenusOpen

/-!
# The open substacks `𝓜 = Curves^{smooth, h0}` and `𝓜_g` of `Curves` (towards Stacks 0E81, 0E83)

Stacks 0E81 produces the open substack `𝓜 = Curves^{smooth, h0} ⊂ Curves` of families of curves
`f : X → S` which are smooth of relative dimension one with `f_*𝒪_X = 𝒪_S`, universally
(`AlgebraicGeometry.IsSmoothH0Family`, base's `AlgebraicGeometry.moduliSmoothCurves`); Stacks
0E83 decomposes it into open and closed substacks `𝓜_g`. This file defines `𝓜_g` and proves the
openness of `𝓜` and `𝓜_g` in the intrinsic form of condition (o) of Stacks 0E0E
(`AlgebraicGeometry.IsOpenCurvesLocus`), which by Stacks 0E0E
(`AlgebraicGeometry.isOpenImmersion_curvesSubstackInclusion_and_factors_iff`) makes them open
substacks of `Curves` with the universal properties (1) of Stacks 0E81 and 0E83, and the
decomposition `𝓜 = ∐_g 𝓜_g`.

`Curves^{smooth, 1}` is open unconditionally: it is `Curves^{smooth} ∩ Curves^{CM, 1}` (Stacks
0DZZ), both of which satisfy condition (o). The condition `f_*𝒪_X = 𝒪_S` universally is the `H⁰`
half of `Curves^{h0, 1}` (Stacks 0E6I), and `𝓜` is the intersection
`Curves^{smooth, 1} ∩ {f_*𝒪_X = 𝒪_S universally}`. A family in `𝓜` is prestable, a smooth
morphism of relative dimension one being at-worst-nodal (Stacks 0CD7), so `𝓜_g` is the
intersection of `𝓜` with the prestable families of genus `g` (Stacks 0E6V), and the decomposition
of `𝓜` is the restriction of that of `Curves^{prestable}`.

## Main definitions

* `AlgebraicGeometry.C1590Private.IsSmoothH0FamilyOfFibreGenus`: in `𝓜`, with all fibres of
  genus `g`.
* `AlgebraicGeometry.C1590Private.moduliSmoothCurvesOfGenus`: the stack `𝓜_g`, with inclusion
  `AlgebraicGeometry.C1590Private.moduliSmoothCurvesOfGenusInclusion` into `Curves`.

## Main results

* `AlgebraicGeometry.C1590Private.isPrestableCurveFamily_of_isSmoothH0Family`: a family in `𝓜`
  is prestable.
* `AlgebraicGeometry.C1590Private.isOpenCurvesLocus_isSmoothH0Family_of` and
  `AlgebraicGeometry.C1590Private.moduliSmoothCurves_isOpenSubstack_and_factors_iff_of`: `𝓜` is an
  open substack of `Curves` with property (1) of Stacks 0E81.
* `AlgebraicGeometry.C1590Private.isSmoothH0FamilyOfFibreGenus_iff_hasGenus`: the genus of the
  fibres is the rank of `R¹f_*𝒪_X`, the form of part (1)(b) of Stacks 0E83.
* `AlgebraicGeometry.C1590Private.moduliSmoothCurves_genus_decomposition`: `𝓜 = ∐_g 𝓜_g` over every
  family in `𝓜`.
* `AlgebraicGeometry.C1590Private.isOpenCurvesLocus_isSmoothH0FamilyOfFibreGenus_of` and
  `AlgebraicGeometry.C1590Private.moduliSmoothCurvesOfGenus_isOpenSubstack_and_factors_iff_of`:
  `𝓜_g` is an open substack of `Curves` with property (1) of Stacks 0E83.

## Implementation notes

The genus of `𝓜_g` is that of the fibres, `AlgebraicGeometry.CurveFamily.HasFibresOfGenus`, as for
`Curves^{prestable}_g` (`AlgebraicGeometry.C1590Private.IsPrestableCurveFamilyOfFibreGenus`); this
condition is stable under every morphism of families, so the substack `𝓜_g` exists without
cohomology and base change. Part (1)(b) of Stacks 0E83 phrases it through `R¹f_*𝒪_X`; part (2)
through the genus of the fibre.

The inputs are explicit hypotheses and nothing here carries a `stacks` attribute. `hΓ` is
condition (o) for `AlgebraicGeometry.HasUniversallyBijectiveGlobalFunctions`, which needs the
openness of the locus `κ(s) = H⁰(X_s, 𝒪_{X_s})` (Stacks 0E0R) and Stacks 0E6B for algebraic
spaces. `hopen` (`AlgebraicGeometry.C1590Private.PrestableGenusLociOpen`) and `hR`
(`AlgebraicGeometry.C1590Private.PrestableHasGenusIff`) are the consequences of Stacks 0E1J (2),
(3) for prestable families: the genus loci are open, and the genus of the fibres is the rank of
`R¹f_*𝒪_X`.

Part (1)(b) of Stacks 0E83 as printed omits "of relative dimension `1`", which part (2) and
Stacks 0E81 contain: for `g = 0` the identity `Spec(k) → Spec(k)` is smooth, with
`f_*𝒪_X = 𝒪_S` universally and `R¹f_*𝒪_X = 0`, but is not in `𝓜`. The condition here keeps the
relative dimension, through `AlgebraicGeometry.IsSmoothH0Family`.

## References

* [Stacks Project, Tag 0E81](https://stacks.math.columbia.edu/tag/0E81)
* [Stacks Project, Tag 0E82](https://stacks.math.columbia.edu/tag/0E82)
* [Stacks Project, Tag 0E83](https://stacks.math.columbia.edu/tag/0E83)
* [Stacks Project, Tag 0E6I](https://stacks.math.columbia.edu/tag/0E6I)
* [Stacks Project, Tag 0E6V](https://stacks.math.columbia.edu/tag/0E6V)
* [Stacks Project, Tag 0E1J](https://stacks.math.columbia.edu/tag/0E1J)
* [Stacks Project, Tag 0DZZ](https://stacks.math.columbia.edu/tag/0DZZ)
* [Stacks Project, Tag 0E0E](https://stacks.math.columbia.edu/tag/0E0E)
* [Stacks Project, Tag 0CD7](https://stacks.math.columbia.edu/tag/0CD7)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.C1590Private

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- **A family in `𝓜` is prestable.** A smooth morphism of relative dimension one is at-worst-nodal
of relative dimension one (Stacks 0CD7, `Space.isAtWorstNodalOfRelativeDimensionOne_of_isSmooth`),
and `f_*𝒪_X = 𝒪_S` universally is part of both conditions. -/
theorem isPrestableCurveFamily_of_isSmoothH0Family {X : CurveFamily B hZ}
    (hX : IsSmoothH0Family B hZ X) : IsPrestableCurveFamily B hZ X :=
  ⟨Space.isAtWorstNodalOfRelativeDimensionOne_of_isSmooth B integerBase hZ hX.1.1 hX.1.2, hX.2⟩

/-- **Condition (o) for `𝓜 = Curves^{smooth, h0}`** (the openness of Stacks 0E81), given condition
(o) `hΓ` for `f_*𝒪_X = 𝒪_S` universally: `𝓜` is the intersection of `Curves^{smooth, 1}` with that
locus. -/
theorem isOpenCurvesLocus_isSmoothH0Family_of
    (hΓ : IsOpenCurvesLocus B hZ (HasUniversallyBijectiveGlobalFunctions B hZ)) :
    IsOpenCurvesLocus B hZ (IsSmoothH0Family B hZ) :=
  (isOpenCurvesLocus_isSmoothDimOneFamily (B := B) (hZ := hZ)).and hΓ

/-- **`𝓜 = Curves^{smooth, h0}` is an open substack of `Curves`, with property (1) of Stacks
0E81**, given condition (o) `hΓ` for `f_*𝒪_X = 𝒪_S` universally: the inclusion `𝓜 ⟶ Curves`
(`AlgebraicGeometry.moduliSmoothCurvesInclusion`) is representable by algebraic spaces and an open
immersion, and the classifying morphism of a family of curves `f : X → S` factors through `𝓜`
exactly when `f` is smooth of relative dimension one with `f_*𝒪_X = 𝒪_S`, universally. -/
theorem moduliSmoothCurves_isOpenSubstack_and_factors_iff_of
    (hΓ : IsOpenCurvesLocus B hZ (HasUniversallyBijectiveGlobalFunctions B hZ)) :
    (ObjectProperty.IsClosedUnderIsomorphisms (IsSmoothH0Family B hZ) ∧
      Stack.IsRepresentableByAlgebraicSpaces B integerBase hZ
        (moduliSmoothCurvesInclusion B hZ).hom ∧
      Stack.IsOpenImmersion B integerBase hZ (moduliSmoothCurvesInclusion B hZ)) ∧
    ∀ (U : BigFppfOver B integerBase hZ)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ),
      y ⋙ curvesProjectionOver B hZ = Over.map U.hom →
      ((∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
          ObjectProperty.FullSubcategory (IsSmoothH0Family B hZ),
          z ⋙ ObjectProperty.ι (IsSmoothH0Family B hZ) = y) ↔
        IsSmoothH0Family B hZ (y.obj (Over.mk (𝟙 U.left)))) :=
  isOpenImmersion_curvesSubstackInclusion_and_factors_iff
    (isOpenCurvesLocus_isSmoothH0Family_of B hZ hΓ)

/-! ### The moduli stack `𝓜_g` -/

/-- A family of curves is *in `𝓜_g`* when it is in `𝓜 = Curves^{smooth, h0}` and all its fibres
have genus `g`. -/
abbrev IsSmoothH0FamilyOfFibreGenus (g : ℕ) (X : CurveFamily B hZ) : Prop :=
  IsSmoothH0Family B hZ X ∧ X.HasFibresOfGenus g

/-- A family of curves mapping to a family in `𝓜_g` is in `𝓜_g`. -/
theorem isSmoothH0FamilyOfFibreGenus_of_hom (g : ℕ) {X Y : CurveFamily B hZ} (φ : X ⟶ Y)
    (hY : IsSmoothH0FamilyOfFibreGenus B hZ g Y) : IsSmoothH0FamilyOfFibreGenus B hZ g X :=
  ⟨CurveFamily.isSmoothH0Family_of_hom B hZ φ hY.1, hY.2.of_hom φ⟩

/-- The moduli stack `𝓜_g` of smooth proper curves of genus `g` of Stacks 0E82 and 0E83, as a
category fibred in groupoids over the big fppf site of `Spec(ℤ)`: the substack of
`𝓜 = Curves^{smooth, h0}` (`AlgebraicGeometry.moduliSmoothCurves`) of families all of whose fibres
have genus `g`, the characterization of `𝓜_g` in part (2) of Stacks 0E83. By
`AlgebraicGeometry.C1590Private.isSmoothH0FamilyOfFibreGenus_iff_hasGenus` its objects are the
families with `R¹f_*𝒪_X` locally free of rank `g` of part (1)(b), once the genus of a prestable
family is compared with the rank of `R¹f_*𝒪_X`. -/
abbrev moduliSmoothCurvesOfGenus (g : ℕ) :
    CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1} (BigFppfOver B integerBase hZ) :=
  curvesSubstack B hZ (IsSmoothH0FamilyOfFibreGenus B hZ g)
    (isSmoothH0FamilyOfFibreGenus_of_hom B hZ g)

/-- The inclusion `𝓜_g ⟶ Curves`. -/
abbrev moduliSmoothCurvesOfGenusInclusion (g : ℕ) :
    moduliSmoothCurvesOfGenus B hZ g ⟶ curvesFiberedCategory B hZ :=
  curvesSubstackInclusion B hZ (IsSmoothH0FamilyOfFibreGenus B hZ g)
    (isSmoothH0FamilyOfFibreGenus_of_hom B hZ g)

variable {B hZ}

/-- **Part (1)(b) of Stacks 0E83 for `𝓜_g`**, given the comparison `hR` of the genus of the fibres
of a prestable family with the rank of `R¹f_*𝒪_X` (Stacks 0E1J): a family is in `𝓜_g` exactly when
it is smooth of relative dimension one with `f_*𝒪_X = 𝒪_S` universally and `R¹f_*𝒪_X` is locally
free of rank `g`. -/
theorem isSmoothH0FamilyOfFibreGenus_iff_hasGenus (hR : PrestableHasGenusIff B hZ) (g : ℕ)
    (X : CurveFamily B hZ) :
    IsSmoothH0FamilyOfFibreGenus B hZ g X ↔
      IsSmoothH0Family B hZ X ∧ CurveFamily.HasGenus B hZ X g :=
  and_congr_right fun hX => (hR X (isPrestableCurveFamily_of_isSmoothH0Family B hZ hX) g).symm

/-- **The decomposition `𝓜 = ∐_g 𝓜_g` over a family in `𝓜`** (Stacks 0E83), given the openness
`hopen` of the genus loci of prestable families (Stacks 0E1J). For a family of curves `G` over `S`
in `𝓜`, the genus loci `Ω_g` of `G` are open and closed in `S`, pairwise disjoint and cover `S`,
and a family of curves mapping to `G` is in `𝓜_g` exactly when its morphism of bases lands in
`Ω_g`: the base change of `𝓜_g ⊂ 𝓜` along `S → 𝓜` is the open and closed subscheme `Ω_g`, and these
partition `S`. -/
theorem moduliSmoothCurves_genus_decomposition (hopen : PrestableGenusLociOpen B hZ)
    (G : CurveFamily B hZ) (hG : IsSmoothH0Family B hZ G) :
    ∃ Ω : ℕ → Set ((BigFppfOver.toScheme B integerBase hZ).obj G.base),
      (∀ g, IsOpen (Ω g) ∧ IsClosed (Ω g)) ∧ Pairwise (fun g g' => Disjoint (Ω g) (Ω g')) ∧
        ⋃ g, Ω g = Set.univ ∧
        ∀ (g : ℕ) (F : CurveFamily B hZ) (a : F ⟶ G),
          IsSmoothH0FamilyOfFibreGenus B hZ g F ↔
            Set.range ((BigFppfOver.toScheme B integerBase hZ).map a.baseMap) ⊆ Ω g := by
  obtain ⟨Ω, hΩ, hdisj, hcov, hchar⟩ := prestable_genus_decomposition hopen G
    (isPrestableCurveFamily_of_isSmoothH0Family B hZ hG)
  refine ⟨Ω, hΩ, hdisj, hcov, fun g F a => ?_⟩
  have hF := CurveFamily.isSmoothH0Family_of_hom B hZ a hG
  rw [← hchar g F a]
  exact and_congr_left fun _ =>
    ⟨fun _ => isPrestableCurveFamily_of_isSmoothH0Family B hZ hF, fun _ => hF⟩

/-- **Condition (o) for `𝓜_g`** (the openness of Stacks 0E83), given condition (o) `hΓ` for
`f_*𝒪_X = 𝒪_S` universally and the openness `hopen` of the genus loci of prestable families
(Stacks 0E1J). A family in `𝓜` is prestable, so `𝓜_g` is the intersection of `𝓜` with the
prestable families of genus `g` (Stacks 0E6V), and `Curves^{prestable}` is
`Curves^{nodal} ∩ {f_*𝒪_X = 𝒪_S universally}`. -/
theorem isOpenCurvesLocus_isSmoothH0FamilyOfFibreGenus_of
    (hΓ : IsOpenCurvesLocus B hZ (HasUniversallyBijectiveGlobalFunctions B hZ))
    (hopen : PrestableGenusLociOpen B hZ) (g : ℕ) :
    IsOpenCurvesLocus B hZ (IsSmoothH0FamilyOfFibreGenus B hZ g) :=
  ((isOpenCurvesLocus_isSmoothH0Family_of B hZ hΓ).and
    (isOpenCurvesLocus_isPrestableCurveFamilyOfFibreGenus
      ((isOpenCurvesLocus_isAtWorstNodal B hZ).and hΓ) hopen g)).of_iff fun _ =>
    ⟨fun h => ⟨h.1, h.2.2⟩,
      fun h => ⟨h.1, isPrestableCurveFamily_of_isSmoothH0Family B hZ h.1, h.2⟩⟩

/-- **`𝓜_g` is an open substack of `Curves`, with property (1) of Stacks 0E83**, given condition
(o) `hΓ` for `f_*𝒪_X = 𝒪_S` universally, the openness `hopen` of the genus loci of prestable
families and the comparison `hR` of the genus of the fibres with the rank of `R¹f_*𝒪_X` (Stacks
0E1J): the inclusion `𝓜_g ⟶ Curves` is representable by algebraic spaces and an open immersion, and
the classifying morphism of a family of curves `f : X → S` factors through `𝓜_g` exactly when `f`
is smooth of relative dimension one, `f_*𝒪_X = 𝒪_S` universally and `R¹f_*𝒪_X` is locally free of
rank `g`. -/
theorem moduliSmoothCurvesOfGenus_isOpenSubstack_and_factors_iff_of
    (hΓ : IsOpenCurvesLocus B hZ (HasUniversallyBijectiveGlobalFunctions B hZ))
    (hopen : PrestableGenusLociOpen B hZ) (hR : PrestableHasGenusIff B hZ) (g : ℕ) :
    (ObjectProperty.IsClosedUnderIsomorphisms (IsSmoothH0FamilyOfFibreGenus B hZ g) ∧
      Stack.IsRepresentableByAlgebraicSpaces B integerBase hZ
        (moduliSmoothCurvesOfGenusInclusion B hZ g).hom ∧
      Stack.IsOpenImmersion B integerBase hZ (moduliSmoothCurvesOfGenusInclusion B hZ g)) ∧
    ∀ (U : BigFppfOver B integerBase hZ)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ),
      y ⋙ curvesProjectionOver B hZ = Over.map U.hom →
      ((∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
          ObjectProperty.FullSubcategory (IsSmoothH0FamilyOfFibreGenus B hZ g),
          z ⋙ ObjectProperty.ι (IsSmoothH0FamilyOfFibreGenus B hZ g) = y) ↔
        IsSmoothH0Family B hZ (y.obj (Over.mk (𝟙 U.left))) ∧
          CurveFamily.HasGenus B hZ (y.obj (Over.mk (𝟙 U.left))) g) := by
  obtain ⟨h₁, h₂⟩ := isOpenImmersion_curvesSubstackInclusion_and_factors_iff
    (isOpenCurvesLocus_isSmoothH0FamilyOfFibreGenus_of hΓ hopen g)
  exact ⟨h₁, fun U y hy =>
    (h₂ U y hy).trans (isSmoothH0FamilyOfFibreGenus_iff_hasGenus hR g _)⟩

end AlgebraicGeometry.C1590Private

end
