module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.MultiplicityAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorGeneratorRatio
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionGeneratingChart
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionSheafGenerator
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineMemberThroughPoint

/-!
# An affine étale chart through a point trivializing two invertible modules

The third step of the proof of Stacks 0EQV chooses, at the generic point `ζ` of an integral
closed subspace of `X`, an étale neighbourhood `(U, u) → (X, ζ)` over which the invertible
modules `ℒ` and `𝒩` are trivial, so that the regular meromorphic sections `s` and `t` become
meromorphic functions `f` and `g` on `U` which are units of the total ring of fractions
`Q(Γ(U, 𝒪_U))`. This file constructs that chart, for an arbitrary point of `|X|`.

The chart is produced by two refinements and one Zariski shrinking, each of which carries a point
over the given one along.

1. Stacks 0B8Q on the small étale site
   (`AlgebraicGeometry.Space.exists_generator_cover_smul_of_isInvertible`) gives a covering
   family of a chart through the point over each member of which `ℒ` is free of rank one,
   compatibly with restriction; a member through the point is chosen by the pointwise criterion
   for covering sieves (`AlgebraicGeometry.Space.SmallEtale.mem_topology_iff_exists_mem_range`).
2. The same for `𝒩`, over that member, with an *affine* member through the point
   (`AlgebraicGeometry.Space.SmallEtale.exists_affine_mem_range_of_mem_topology`).

Over the resulting affine chart `W` both modules carry compatible families of free generators,
the ratios `s / e_ℒ` and `t / e_𝒩` are the meromorphic functions
`AlgebraicGeometry.Space.chartRatio`, and regularity of the sections makes them units of
`𝒦_X(W)`, which is the total ring of fractions of `𝒪_X(W)` by Stacks 0EN6(2).

## Main results

* `AlgebraicGeometry.Space.isUnit_chartRatio_of_isRegularMeromorphicSection`: over an affine
  chart carrying a compatible family of free generators, the ratio of a regular meromorphic
  section against the generator is a unit of the total ring of fractions.
* `AlgebraicGeometry.Space.exists_affine_chart_free_free_of_chart`: through every point of every
  chart there is an affine chart over it on which two invertible modules are free.
* `AlgebraicGeometry.Space.exists_affine_chart_isUnit_chartRatio`: **the chart of the third step
  of Stacks 0EQV**, through a prescribed point of `|X|`.

## References

* [Stacks Project, Tag 0EQV](https://stacks.math.columbia.edu/tag/0EQV)
* [Stacks Project, Tag 0EN6](https://stacks.math.columbia.edu/tag/0EN6)
* [Stacks Project, Tag 0B8Q](https://stacks.math.columbia.edu/tag/0B8Q)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TensorProduct

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] chartMeromorphicAlgebra

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- **The ratio of a regular meromorphic section against a free generator over an affine chart
is a unit of the total ring of fractions.** Let `X` satisfy hypotheses (a) and (b) of
Stacks 0ENA, let `V` be an affine étale chart of `X` over which `ℒ` carries the compatible family
`e` of free generators, and let `t` be a regular meromorphic section of `ℒ`. Then the ratio
`t / e` (`AlgebraicGeometry.Space.chartRatio`) is a unit of `𝒦_X(V)`.

The ratio kills no meromorphic function, by regularity of `t`
(`AlgebraicGeometry.Space.eq_zero_of_mul_eq_zero_of_eval_eq_tmul`), and `𝒦_X(V)` is the total
ring of fractions of `𝒪_X(V)` by Stacks 0EN6(2), in which every nonzerodivisor is a unit. -/
theorem isUnit_chartRatio_of_isRegularMeromorphicSection
    (hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS X, localRingDimension B S hS z = 0)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X.1)
    (L : Modules.{u, u} B S hS X.1 X.2) (V : SmallEtale B S hS X.1)
    (hV : IsAffine (chartScheme V))
    (e : (W : SmallEtale B S hS X.1) → (W ⟶ V) → L.val.obj (op W))
    (hcompat : ∀ (W W' : SmallEtale B S hS X.1) (k : W ⟶ V) (g : W' ⟶ W),
      (L.val.map g.op).hom (e W k) = e W' (g ≫ k))
    (hfree : ∀ (W : SmallEtale B S hS X.1) (k : W ⟶ V),
      Function.Bijective fun r : chartRing B S hS X.1 X.2 W ↦ r • e W k)
    (t : MeromorphicSection.{u, u} B S hS X.1 X.2 L)
    (ht : IsRegularMeromorphicSection.{u, u} B S hS X.1 X.2 L t) :
    IsUnit (chartRatio B S hS X.1 X.2 L V e hcompat hfree t) := by
  have hz := eq_zero_of_mul_eq_zero_of_eval_eq_tmul B S hS X.1 X.2 L t ht V (e V (𝟙 V))
    (chartRatio B S hS X.1 X.2 L V e hcompat hfree t)
    (eval_eq_toMeromorphicSectionSheaf_tmul_chartRatio B S hS X.1 X.2 L V e hcompat hfree t)
  let : Algebra ((structurePresheaf B S hS X.1).obj (op V))
      ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op V)) :=
    ((toMeromorphicFunctionSheaf B S hS X.1 X.2).hom.app (op V)).hom.toAlgebra
  have := isFractionRing_meromorphicFunctionSheaf_obj B S hS X hwa hfin V hV
  have hmem : meromorphicChartRingEquiv B S hS X.1 X.2 V
      (chartRatio B S hS X.1 X.2 L V e hcompat hfree t) ∈
        nonZeroDivisors ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op V)) :=
    mem_nonZeroDivisors_iff_right.mpr fun y hy => hz _ hy
  rw [IsFractionRing.nonZeroDivisors_eq_isUnit ((structurePresheaf B S hS X.1).obj (op V))] at hmem
  exact (IsUnit.map (meromorphicChartRingEquiv B S hS X.1 X.2 V).symm hmem :)

/-- A compatible family of generators over `W` restricts to a compatible family over any chart
`V ⟶ W`. -/
private theorem restrict_generator_family_compat (L : Modules.{u, u} B S hS X.1 X.2)
    {W V : SmallEtale B S hS X.1} (c : V ⟶ W)
    (e : (W' : SmallEtale B S hS X.1) → (W' ⟶ W) → L.val.obj (op W'))
    (hcompat : ∀ (W₁ W₂ : SmallEtale B S hS X.1) (k : W₁ ⟶ W) (g : W₂ ⟶ W₁),
      (L.val.map g.op).hom (e W₁ k) = e W₂ (g ≫ k))
    (W₁ W₂ : SmallEtale B S hS X.1) (k : W₁ ⟶ V) (g : W₂ ⟶ W₁) :
    (L.val.map g.op).hom (e W₁ (k ≫ c)) = e W₂ (g ≫ k ≫ c) :=
  (hcompat W₁ W₂ (k ≫ c) g).trans (congrArg (e W₂) (Category.assoc g k c).symm)

/-- **Through every point of every chart there is an affine chart over it on which an invertible
module is free.** For an étale chart `C` of `X` and a point `x` of its scheme, there is an étale
chart `W ⟶ C` with affine scheme, a point `w` of it mapping to `x`, and a compatible family of free
generators of `ℒ` over the charts over `W`.

Stacks 0B8Q on the small étale site gives a covering family of `C` over each member of which `ℒ`
is free; a covering sieve has an affine member through every point
(`AlgebraicGeometry.Space.SmallEtale.exists_affine_mem_range_of_mem_topology`), and the family of
the member it factors through restricts to it. -/
theorem exists_affine_chart_free_of_chart (L : Modules.{u, u} B S hS X.1 X.2)
    (hL : IsInvertibleModule X L) (C : SmallEtale B S hS X.1) (x : chartScheme C) :
    ∃ (W : SmallEtale B S hS X.1) (κ : W ⟶ C) (_ : IsAffine (chartScheme W))
      (w : chartScheme W)
      (e : (W' : SmallEtale B S hS X.1) → (W' ⟶ W) → L.val.obj (op W'))
      (_ : ∀ (W₁ W₂ : SmallEtale B S hS X.1) (k : W₁ ⟶ W) (g : W₂ ⟶ W₁),
        (L.val.map g.op).hom (e W₁ k) = e W₂ (g ≫ k))
      (_ : ∀ (W₁ : SmallEtale B S hS X.1) (k : W₁ ⟶ W),
        Function.Bijective fun r : chartRing B S hS X.1 X.2 W₁ ↦ r • e W₁ k),
      (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X.1).map κ) w = x := by
  obtain ⟨I, V, a, hcov, hgen⟩ := exists_generator_cover_smul_of_isInvertible B S hS X L
    (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hL) C
  obtain ⟨Q, φ, hφ, hQaff, w, hw⟩ :=
    SmallEtale.exists_affine_mem_range_of_mem_topology B S hS X.1 (x := C)
      (T := Sieve.ofArrows V a) hcov x
  obtain ⟨i, c, rfl⟩ := (Sieve.mem_ofArrows_iff V a φ).1 hφ
  obtain ⟨e, hcompat, hfree⟩ := hgen i
  exact ⟨Q, c ≫ a i, hQaff, w, fun W' k ↦ e W' (k ≫ c),
    restrict_generator_family_compat B S hS X L c e hcompat, fun W₁ k ↦ hfree W₁ (k ≫ c), hw⟩

/-- **Through every point of every chart there is an affine chart over it on which two invertible
modules are free.** For an étale chart `C` of `X` and a point `x` of its scheme, there is an
étale chart `W ⟶ C` with affine scheme, a point `w` of it mapping to `x`, and compatible families
of free generators of `ℒ` and of `𝒩` over the charts over `W`. This is
`AlgebraicGeometry.Space.exists_affine_chart_free_of_chart` applied twice; the family of the
first module restricts along the second refinement. -/
theorem exists_affine_chart_free_free_of_chart (L N : Modules.{u, u} B S hS X.1 X.2)
    (hL : IsInvertibleModule X L) (hN : IsInvertibleModule X N)
    (C : SmallEtale B S hS X.1) (x : chartScheme C) :
    ∃ (W : SmallEtale B S hS X.1) (κ : W ⟶ C) (_ : IsAffine (chartScheme W))
      (w : chartScheme W)
      (eL : (W' : SmallEtale B S hS X.1) → (W' ⟶ W) → L.val.obj (op W'))
      (_ : ∀ (W₁ W₂ : SmallEtale B S hS X.1) (k : W₁ ⟶ W) (g : W₂ ⟶ W₁),
        (L.val.map g.op).hom (eL W₁ k) = eL W₂ (g ≫ k))
      (_ : ∀ (W₁ : SmallEtale B S hS X.1) (k : W₁ ⟶ W),
        Function.Bijective fun r : chartRing B S hS X.1 X.2 W₁ ↦ r • eL W₁ k)
      (eN : (W' : SmallEtale B S hS X.1) → (W' ⟶ W) → N.val.obj (op W'))
      (_ : ∀ (W₁ W₂ : SmallEtale B S hS X.1) (k : W₁ ⟶ W) (g : W₂ ⟶ W₁),
        (N.val.map g.op).hom (eN W₁ k) = eN W₂ (g ≫ k))
      (_ : ∀ (W₁ : SmallEtale B S hS X.1) (k : W₁ ⟶ W),
        Function.Bijective fun r : chartRing B S hS X.1 X.2 W₁ ↦ r • eN W₁ k),
      (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X.1).map κ) w = x := by
  obtain ⟨V₁, κ₁, -, x₁, eL, hcL, hfL, hx₁⟩ := exists_affine_chart_free_of_chart B S hS X L hL C x
  obtain ⟨Q, κ₂, hQ, w, eN, hcN, hfN, hw⟩ := exists_affine_chart_free_of_chart B S hS X N hN V₁ x₁
  refine ⟨Q, κ₂ ≫ κ₁, hQ, w, fun W' k ↦ eL W' (k ≫ κ₂),
    restrict_generator_family_compat B S hS X L κ₂ eL hcL, fun W₁ k ↦ hfL W₁ (k ≫ κ₂),
    eN, hcN, hfN, ?_⟩
  rw [Functor.map_comp, Functor.map_comp, Scheme.Hom.comp_apply, hw]
  exact hx₁

/-- **The chart of the third step of Stacks 0EQV.** Let `X` satisfy hypotheses (a) and (b) of
Stacks 0ENA, let `ℒ` and `𝒩` be invertible `𝒪_X`-modules with regular meromorphic sections `s`
and `t`, and let `ζ ∈ |X|`. There is an étale chart `W` of `X` with affine scheme and a point `w`
of it over `ζ`, compatible families `e_ℒ`, `e_𝒩` of free generators of `ℒ` and `𝒩` over the
charts over `W`, such that the ratios `s / e_ℒ` and `t / e_𝒩` are units of the total ring of
fractions `𝒦_X(W) = Q(𝒪_X(W))`. -/
theorem exists_affine_chart_isUnit_chartRatio
    (hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS X, localRingDimension B S hS z = 0)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X.1)
    (L N : Modules.{u, u} B S hS X.1 X.2)
    (hL : IsInvertibleModule X L) (hN : IsInvertibleModule X N)
    (s : MeromorphicSection.{u, u} B S hS X.1 X.2 L)
    (hs : IsRegularMeromorphicSection.{u, u} B S hS X.1 X.2 L s)
    (t : MeromorphicSection.{u, u} B S hS X.1 X.2 N)
    (ht : IsRegularMeromorphicSection.{u, u} B S hS X.1 X.2 N t)
    (ζ : points B S hS X.1) :
    ∃ (W : SmallEtale B S hS X.1) (_ : IsAffine (chartScheme W)) (w : chartScheme W)
      (eL : (W' : SmallEtale B S hS X.1) → (W' ⟶ W) → L.val.obj (op W'))
      (hcL : ∀ (W₁ W₂ : SmallEtale B S hS X.1) (k : W₁ ⟶ W) (g : W₂ ⟶ W₁),
        (L.val.map g.op).hom (eL W₁ k) = eL W₂ (g ≫ k))
      (hfL : ∀ (W₁ : SmallEtale B S hS X.1) (k : W₁ ⟶ W),
        Function.Bijective fun r : chartRing B S hS X.1 X.2 W₁ ↦ r • eL W₁ k)
      (eN : (W' : SmallEtale B S hS X.1) → (W' ⟶ W) → N.val.obj (op W'))
      (hcN : ∀ (W₁ W₂ : SmallEtale B S hS X.1) (k : W₁ ⟶ W) (g : W₂ ⟶ W₁),
        (N.val.map g.op).hom (eN W₁ k) = eN W₂ (g ≫ k))
      (hfN : ∀ (W₁ : SmallEtale B S hS X.1) (k : W₁ ⟶ W),
        Function.Bijective fun r : chartRing B S hS X.1 X.2 W₁ ↦ r • eN W₁ k),
      chartSchemeToPoints B S hS X.1 W w = ζ ∧
        IsUnit (chartRatio B S hS X.1 X.2 L W eL hcL hfL s) ∧
        IsUnit (chartRatio B S hS X.1 X.2 N W eN hcN hfN t) := by
  obtain ⟨C, x, hx⟩ := exists_chartSchemeToPoints_eq B S hS X ζ
  obtain ⟨W, κ, hW, w, eL, hcL, hfL, eN, hcN, hfN, hw⟩ :=
    exists_affine_chart_free_free_of_chart B S hS X L N hL hN C x
  refine ⟨W, hW, w, eL, hcL, hfL, eN, hcN, hfN, ?_,
    isUnit_chartRatio_of_isRegularMeromorphicSection B S hS X hwa hfin L W hW eL hcL hfL s hs,
    isUnit_chartRatio_of_isRegularMeromorphicSection B S hS X hwa hfin N W hW eN hcN hfN t ht⟩
  rw [← chartSchemeToPoints_map B S hS X.1 κ w, hw, hx]

end AlgebraicGeometry.Space

end
