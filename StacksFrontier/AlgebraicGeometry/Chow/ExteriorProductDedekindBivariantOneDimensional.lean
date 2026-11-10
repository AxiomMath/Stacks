module

public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductDedekindBivariantIdentification
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductDedekindRepresentation
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductDedekind.DimensionParts
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.RankZero

/-!
# Stacks 0FC5 over the one-dimensional part of the base

Let `(S, δ)` be a base as in Stacks section 42.63. A field is a Dedekind domain, so `S` may have
zero-dimensional components, and over them Stacks 0FC5 fails (see
`Stacks.Chow.not_injective_bivariantCapBaseFundamentalClass_fieldChowSituation`). This file proves
Stacks 0FC5 for every `X` locally of finite type over `S` which has **no point over the
zero-dimensional part** `S₀` of `S`, with no hypothesis on `S` beyond section 42.63: the canonical
map

  `A^p(X → S) ⟶ CH_{1-p}(X)`,   `c ↦ c ∩ [S]₁`,

is bijective. This is the case `X = X₁` of the decomposition `X = X₀ ⊔ X₁` along
`S = S₀ ⊔ S₁` (`Stacks.Chow.IsDedekindChowBase.isClopenDecomposition_dimensionPart`), and the form
in which Stacks 0FC5 enters the proof of Stacks 0FCB over a base which may have field components.

The proof is that of `Stacks.Chow.bivariantCapBaseFundamentalClass_bijective`, with its hypothesis
`Stacks.Chow.HasNoZeroDimensionalComponent` on all of `S` replaced by the hypothesis on `X`. The
two places where the global hypothesis was used are a test scheme `T` whose generic point lies over
a generic point of `S`, and the flat generators of `CH_{1-p}(X)`. In the second, the points of `X`
lie over `S₁` by hypothesis. In the first, if the generic point of `T` lies over a zero-dimensional
point `s`, then all of `T` lies over `s` and the fibre product `X ×_S T` is empty, so every cap
product into it vanishes.

## Main results

* `Stacks.Chow.IsDedekindChowBase.isEmpty_pullback_of_forall_not_isZeroDimensionalBasePoint` —
  `X ×_S T = ∅` when `X` avoids `S₀` and `T` is irreducible over a point of `S₀`.
* `Stacks.Chow.bivariantCapBaseFundamentalClass_bijective_of_forall_not_isZeroDimensionalBasePoint`
  — **Stacks 0FC5** for `X` over the one-dimensional part.
* `isExteriorProductOverBase_bivariantCapBaseFundamentalClass_of_forall_not_isZeroDimBasePoint`
  — the inverse of that map acts by the exterior product of Stacks 0FC4,
  `c ∩ α' = (c ∩ [S]₁) × α'`.

## References

* [Stacks Project, Tag 0FC5](https://stacks.math.columbia.edu/tag/0FC5)
* [Stacks Project, Section 42.63 (Tag 0FC3)](https://stacks.math.columbia.edu/tag/0FC3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

variable {C : ChowSituation.{u}}

namespace IsDedekindChowBase

variable (hS : IsDedekindChowBase C)

include hS in
/-- **A scheme over the one-dimensional part meets no test scheme over a zero-dimensional point.**
Let `X` have no point over the zero-dimensional part of a base as in section 42.63, and let `T` be
irreducible over the base with generic point over a generic point `s` of the base with `δ(s) ≠ 1`.
Then `X ×_S T` is empty: `s` is closed, so every point of `T` lies over `s`, which is
zero-dimensional, while no point of `X` does. -/
theorem isEmpty_pullback_of_forall_not_isZeroDimensionalBasePoint {X T : Scheme.{u}}
    (sX : X ⟶ C.S) (hX : ∀ x : X, ¬ IsZeroDimensionalBasePoint C (sX.base x)) [IrreducibleSpace T]
    (t : T ⟶ C.S) (hgen : t.base (genericPoint T) ∈ genericPoints C.S)
    (hne : C.dimensionFunction (t.base (genericPoint T)) ≠ 1) :
    IsEmpty (pullback sX t : Scheme.{u}) := by
  have hcl : IsClosed ({t.base (genericPoint T)} : Set C.S) := by
    by_contra h
    exact hne (hS.2.2 _ h)
  refine ⟨fun z ↦ hX ((pullback.fst sX t).base z) ?_⟩
  have hspec : t.base (genericPoint T) ⤳ t.base ((pullback.snd sX t).base z) :=
    ((genericPoint_spec T).specializes (Set.mem_univ _)).map t.continuous
  have heq : t.base ((pullback.snd sX t).base z) = t.base (genericPoint T) := by
    have hmem := specializes_iff_mem_closure.mp hspec
    rwa [hcl.closure_eq, Set.mem_singleton_iff] at hmem
  have hfst : sX.base ((pullback.fst sX t).base z) = t.base ((pullback.snd sX t).base z) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
  rw [hfst, heq]
  exact ⟨hcl, hgen⟩

end IsDedekindChowBase

/-! ### Injectivity -/

section Injective

variable (C) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (p : ℤ)

/-- **The final paragraph of the proof of Stacks 0FC5, over the one-dimensional part.** Let `X`
have no point over the zero-dimensional part of a base as in section 42.63. A class
`c ∈ A^p(X → S)` killing `[S]₁` kills the fundamental class of every integral scheme `T` locally of
finite type over the base. If the generic point of `T` lies over a generic point `s` of the base
with `δ(s) = 1`, this is
`Stacks.Chow.cap_fundamentalChowClass_eq_zero_of_dimensionFunction_eq_one`; otherwise `X ×_S T`
is empty. -/
theorem cap_fundamentalChowClass_eq_zero_of_forall_not_isZeroDimensionalBasePoint
    (hS : IsDedekindChowBase C) (hX : ∀ x : X, ¬ IsZeroDimensionalBasePoint C (sX.base x))
    (c : BivariantClass C (gysinSystemOfInvertible C) sX (𝟙 C.S) sX (Category.comp_id sX) p)
    (hc : c.cap (𝟙 C.S) 1 (baseFundamentalChowClass C) = 0)
    {T : Scheme.{u}} (g : T ⟶ C.S) [LocallyOfFiniteType g] [IsIntegral T] (k : ℤ) :
    c.cap g k (fundamentalChowClass C (g ≫ 𝟙 C.S) k) = 0 := by
  by_cases h : g.base (genericPoint T) ∈ genericPoints C.S →
      C.dimensionFunction (g.base (genericPoint T)) = 1
  · exact cap_fundamentalChowClass_eq_zero_of_dimensionFunction_eq_one C sX p hS c hc g k h
  · push Not at h
    have := hS.isEmpty_pullback_of_forall_not_isZeroDimensionalBasePoint sX hX g h.1 h.2
    exact @Subsingleton.elim _ (subsingleton_chowGroup_of_isEmpty C _ _) _ 0

/-- **Stacks 0FC5, injectivity, over the one-dimensional part.** For `X` with no point over the
zero-dimensional part of a base as in section 42.63, the canonical map
`A^p(X → S) → CH_{1-p}(X)`, `c ↦ c ∩ [S]₁`, is injective. -/
theorem bivariantCapBaseFundamentalClass_injective_of_forall_not_isZeroDimensionalBasePoint
    (hS : IsDedekindChowBase C) (hX : ∀ x : X, ¬ IsZeroDimensionalBasePoint C (sX.base x)) :
    Function.Injective (bivariantCapBaseFundamentalClass C (gysinSystemOfInvertible C) sX p) := by
  intro c d h
  rw [← sub_eq_zero, BivariantClass.eq_zero_iff_capsIntegral_canonical]
  intro T g _ _ k
  refine cap_fundamentalChowClass_eq_zero_of_forall_not_isZeroDimensionalBasePoint C sX p hS hX
    (c - d) ?_ g k
  rw [BivariantClass.sub_cap, sub_eq_zero]
  refine chowPushforwardOfIso_injective C _ _ (basePullbackProjection C sX) rfl (1 - p) ?_
  exact h

end Injective

/-! ### Surjectivity -/

section Surjective

variable (C) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (p : ℤ)

/-- **The flat generators, at points over one-dimensional components.** Over a base as in
section 42.63, the cycle `∑_j [y_j]` attached to a locally finite family of points of
delta-dimension `1 - p` lying over generic points `s_j` of the base with `δ(s_j) = 1` is in the
image of the canonical map of Stacks 0FC5. This is the argument of
`Stacks.Chow.exists_cycle_mem_range_of_mem_genericPoints`, which reads `δ(s_j) = 1` off the
absence of zero-dimensional components; here it is a hypothesis on the points. -/
theorem exists_cycle_mem_range_of_mem_genericPoints_of_dimensionFunction_eq_one
    (hS : IsDedekindChowBase C) {J : Type u} (y : J → X)
    (hlf : LocallyFinite fun j ↦ Set.range (integralComponentAt (y j)).subschemeι)
    (hδ : ∀ j, relativeDimension C.dimensionFunction sX (y j) = 1 - p)
    (hgen : ∀ j, sX.base (y j) ∈ genericPoints C.S)
    (hδ1 : ∀ j, C.dimensionFunction (sX.base (y j)) = 1) :
    ∃ P : CycleGroup C sX (1 - p),
      QuotientAddGroup.mk' (rationalEquivalences C sX (1 - p)) P ∈
          (bivariantCapBaseFundamentalClass C (gysinSystemOfInvertible C) sX p).range ∧
        ∀ x, P.1 x = ∑ᶠ j ∈ y ⁻¹' {x}, (1 : ℤ) := by
  by_cases hJ : IsEmpty J
  · refine ⟨0, zero_mem _, fun x ↦ ?_⟩
    rw [Set.eq_empty_of_isEmpty (y ⁻¹' {x}), finsum_mem_empty]
    rfl
  obtain ⟨j₀⟩ := not_isEmpty_iff.mp hJ
  have hp : p ≤ 0 := by
    have h1 := hδ j₀
    have h2 : C.dimensionFunction (sX.base (y j₀)) ≤
        relativeDimension C.dimensionFunction sX (y j₀) := by
      change _ ≤ C.dimensionFunction (sX.base (y j₀)) +
        (Cardinal.toNat (residueTrdeg sX (y j₀)) : ℤ)
      omega
    rw [hδ1] at h2
    omega
  obtain ⟨r, rfl⟩ : ∃ r : ℕ, p = -(r : ℤ) := ⟨(-p).toNat, by omega⟩
  set Zs := fun j ↦ (integralComponentAt (y j)).subscheme with hZs
  set v : ∀ j, Zs j ⟶ X := fun j ↦ (integralComponentAt (y j)).subschemeι with hv
  have _ : IsProper (Sigma.desc v) := isProper_sigmaDesc_of_locallyFinite Zs v hlf
  have hflat : ∀ j, Flat (v j ≫ sX) := fun j ↦ by
    have _ := isIntegral_integralComponentAt (y j)
    refine hS.flat_of_mem_genericPoints _ ?_
    rw [Scheme.Hom.comp_apply, subschemeι_genericPoint_integralComponentAt]
    exact hgen j
  have hdesc : Sigma.desc v ≫ sX = Sigma.desc fun j ↦ v j ≫ sX := by
    refine Sigma.hom_ext _ _ fun j ↦ ?_
    simp
  have _ : Flat (Sigma.desc v ≫ sX) := by
    have := hflat
    rw [hdesc]
    infer_instance
  have hr : AlgebraicGeometry.RelativeDimension (Sigma.desc v ≫ sX) r := by
    refine AlgebraicGeometry.RelativeDimension.of_sigmaι_comp Zs _ fun j ↦ ?_
    have _ := hflat j
    have h := hS.relativeDimension_integralComponentAt_comp sX (y j) (hgen j)
    have e : (relativeDimension C.dimensionFunction sX (y j) -
        C.dimensionFunction (sX.base (y j))).toNat = r := by
      rw [hδ j, hδ1]
      omega
    rw [e] at h
    exact AlgebraicGeometry.RelativeDimension.of_eq (Sigma.ι_comp_desc_assoc _ _ _).symm h
  exact exists_cycle_mem_range_of_sigma C sX (-(r : ℤ)) y hδ
    (flatPullbackBivariantClassOfInvertible C (Sigma.desc v ≫ sX) (𝟙 C.S) (Sigma.desc v ≫ sX)
        (Category.comp_id _) r hr)
    (bivariantCapBaseFundamentalClass_flatPullbackBivariantClass C _ _ r hr _
      (isBivariantFlatPullback_flatPullbackBivariantClassOfInvertible C (Sigma.desc v ≫ sX)
        (𝟙 C.S) (Sigma.desc v ≫ sX) (Category.comp_id _) r hr)
      (hS.schemeDeltaDimension_le_one (𝟙 C.S ≫ 𝟙 C.S)))


/-- **Stacks 0FC5, surjectivity, over the one-dimensional part.** For `X` with no point over the
zero-dimensional part of a base as in section 42.63, every class in `CH_{1-p}(X)` is `c ∩ [S]₁`
for some `c ∈ A^p(X → S)`. The proof is that of
`Stacks.Chow.bivariantCapBaseFundamentalClass_surjective`: a point of `X` over a generic point `s`
of the base has `δ(s) = 1`, because `s` is not zero-dimensional and so is not closed. -/
theorem bivariantCapBaseFundamentalClass_surjective_of_forall_not_isZeroDimensionalBasePoint
    (hS : IsDedekindChowBase C) (hX : ∀ x : X, ¬ IsZeroDimensionalBasePoint C (sX.base x)) :
    Function.Surjective
      (bivariantCapBaseFundamentalClass C (gysinSystemOfInvertible C) sX p) := by
  classical
  intro α
  induction α using QuotientAddGroup.induction_on with
  | H a =>
  have hh := fun M ↦ exists_cycle_mem_range_of_multiplicity C sX p a
    (fun x ↦ sX.base x ∈ genericPoints C.S)
    (fun y hlf hδ hQ ↦ exists_cycle_mem_range_of_mem_genericPoints_of_dimensionFunction_eq_one C
      sX p hS y hlf hδ hQ fun j ↦ hS.2.2 _ fun hcl ↦ hX (y j) ⟨hcl, hQ j⟩) M
  have hv := fun M ↦ exists_cycle_mem_range_of_multiplicity C sX p a
    (fun x ↦ sX.base x ∉ genericPoints C.S)
    (fun y hlf hδ hQ ↦ exists_cycle_mem_range_of_notMem_genericPoints C sX p hS y hlf hδ hQ) M
  obtain ⟨P₁, hP₁, hP₁y⟩ := hh fun i ↦ (a.1 i).toNat
  obtain ⟨P₂, hP₂, hP₂y⟩ := hh fun i ↦ (-a.1 i).toNat
  obtain ⟨P₃, hP₃, hP₃y⟩ := hv fun i ↦ (a.1 i).toNat
  obtain ⟨P₄, hP₄, hP₄y⟩ := hv fun i ↦ (-a.1 i).toNat
  have hsub : a = P₁ - P₂ + (P₃ - P₄) := by
    refine Subtype.ext (Function.locallyFinsuppWithin.ext fun x ↦ ?_)
    change a.1 x = P₁.1 x - P₂.1 x + (P₃.1 x - P₄.1 x)
    rw [hP₁y, hP₂y, hP₃y, hP₄y]
    by_cases hx : x ∈ Function.support (a.1 : X → ℤ)
    · by_cases hg : sX.base x ∈ genericPoints C.S <;> simp [hx, hg]
    · simp at hx
      simp [hx]
  have hmem : QuotientAddGroup.mk' (rationalEquivalences C sX (1 - p)) a ∈
      (bivariantCapBaseFundamentalClass C (gysinSystemOfInvertible C) sX p).range := by
    rw [hsub, map_add, map_sub, map_sub]
    exact add_mem (sub_mem hP₁ hP₂) (sub_mem hP₃ hP₄)
  exact hmem

/-- **Stacks 0FC5 over the one-dimensional part.** Let `(S, δ)` be a base as in section 42.63 of
the Stacks Project, possibly with zero-dimensional components, and let `X` be locally of finite
type over `S` with no point over the zero-dimensional part `S₀`. Then `c ↦ c ∩ [S]₁` is a
bijection `A^p(X → S) → CH_{1-p}(X)` for every `p ∈ ℤ`. -/
theorem bivariantCapBaseFundamentalClass_bijective_of_forall_not_isZeroDimensionalBasePoint
    (hS : IsDedekindChowBase C) (hX : ∀ x : X, ¬ IsZeroDimensionalBasePoint C (sX.base x)) :
    Function.Bijective
      (bivariantCapBaseFundamentalClass C (gysinSystemOfInvertible C) sX p) :=
  ⟨bivariantCapBaseFundamentalClass_injective_of_forall_not_isZeroDimensionalBasePoint C sX p hS hX,
    bivariantCapBaseFundamentalClass_surjective_of_forall_not_isZeroDimensionalBasePoint C sX p hS
      hX⟩

end Surjective

/-! ### The inverse acts by exterior product -/

section Representation

variable {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (p : ℤ)

/-- **The inverse of the map of Stacks 0FC5 acts by exterior product, over the one-dimensional
part.** For `X` with no point over the zero-dimensional part of a base as in section 42.63, every
`c ∈ A^p(X → S)` caps as the exterior product of Stacks 0FC4 with `c ∩ [S]₁`:
`c ∩ α' = (c ∩ [S]₁) × α'`. This is the argument of
`Stacks.Chow.isExteriorProductOverBase_bivariantCapBaseFundamentalClass`; a test scheme over a
zero-dimensional point has empty fibre product with `X`, where both sides vanish. -/
theorem isExteriorProductOverBase_bivariantCapBaseFundamentalClass_of_forall_not_isZeroDimBasePoint
    (hS : IsDedekindChowBase C) (hX : ∀ x : X, ¬ IsZeroDimensionalBasePoint C (sX.base x))
    (c : BivariantClass C (gysinSystemOfInvertible C) sX (𝟙 C.S) sX (Category.comp_id sX) p) :
    IsExteriorProductOverBase C (gysinSystemOfInvertible C) sX (1 - p) p
      (bivariantCapBaseFundamentalClass C (gysinSystemOfInvertible C) sX p c) c := by
  obtain ⟨a, ha⟩ := QuotientAddGroup.mk'_surjective (rationalEquivalences C sX (1 - p))
    (bivariantCapBaseFundamentalClass C (gysinSystemOfInvertible C) sX p c)
  intro U u _ k hfac α'
  induction α' using QuotientAddGroup.induction_on with
  | H b =>
  rw [← ha]
  refine cap_heq_exteriorProductDedekindCycles_of_forall_isIntegral C _ sX (1 - p) p c a rfl
    (fun t _ _ l ↦ ?_) u k b
  by_cases hgen : t.base (genericPoint _) ∈ genericPoints C.S
  · by_cases hδ : C.dimensionFunction (t.base (genericPoint _)) = 1
    · exact cap_fundamentalCycle_heq_of_mem_genericPoints_of_dimensionFunction_eq_one _ sX p hS c
        a ha.symm t hgen hδ l
    · have := hS.isEmpty_pullback_of_forall_not_isZeroDimensionalBasePoint sX hX t hgen hδ
      refine (heq_of_eq (@Subsingleton.elim _ (subsingleton_chowGroup_of_isEmpty C _ _) _ 0)).trans
        ((heq_zero_chowGroup_of_degree_eq C _ (by ring)).trans
          (heq_of_eq (@Subsingleton.elim _ (subsingleton_chowGroup_of_isEmpty C _ _) _ 0).symm))
  · exact cap_fundamentalCycle_heq_of_notMem_genericPoints sX p hS c a ha.symm t hgen l

end Representation

end Stacks.Chow

end
