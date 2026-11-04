module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.IntersectionSymmetry
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SpecialFiberPrincipal
public import StacksFrontier.AlgebraicGeometry.Meromorphic.RegularSectionExistence
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.LinearAlgebra.DiagonallyDominant
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.Divisors.InvertibleSheafPullback
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SectionDegree
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SpecialFiberComponentProperCurve

/-!
# The properties of the intersection form on a regular model

In the situation of [Stacks, Tag 0C61] write the special fibre of the model as a sum
`X_k = Σ mᵢ Cᵢ` of effective Cartier divisors and let

`(Σᵢ aᵢCᵢ · Σⱼ bⱼCⱼ) = ⟨a, 𝒪_X(Σⱼ bⱼCⱼ)⟩`

be the symmetric bilinear form of [Stacks, Tag 0C65]. [Stacks, Tag 0C66] records four properties
of this form: nonnegativity of `(Cᵢ · Cⱼ)` for `i ≠ j` with equality exactly for disjoint
components, orthogonality of the whole special fibre `Σ mᵢCᵢ` to each component, connectedness
of the intersection graph, and negative semidefiniteness with nullspace the line `ℚ·m`.

What is proved here are the inputs to those four properties that live at an abstract family of
components: the orthogonality of `Σ mᵢCᵢ` to *every* integral combination of the components,
because the invertible sheaf `𝒪_X(X_k)` is trivial and the degree of the structure sheaf on a
proper curve vanishes; the sign of `deg(𝒪_X(E)|_D)` for an integral proper curve `D ⊄ E`; and the
deduction of the fourth property from the other three through [Stacks, Tag 0C5X]. The four
properties themselves are assembled at the irreducible components of the special fibre in
`StacksFrontier/AlgebraicGeometry/Curves/Models/SpecialFiberIntersectionForm.lean`, which carries a
`@[stacks 0C66]` attribute for each of the four. The orthogonality statement of this file keeps the
`@[stacks 0C66]` attribute it has always had, on its own orientation of part (2).

## Main definitions

* `Stacks.Models.divisorSheafIsoUnit_specialFiber` — the trivialization
  `𝒪_X(Σ mᵢCᵢ) ≅ 𝒪_X` of the sheaf of the special fibre, in the spelling of
  `Stacks.Models.divisorSheaf`.

## Main results

* `Stacks.Models.componentDegree_unit_eq_zero`, `Stacks.Models.degreePairing_unit_eq_zero` — the
  structure sheaf has degree zero on every component, so `⟨a, 𝒪_X⟩ = 0`.
* `Stacks.Models.componentDegree_divisorSheaf_specialFiber_eq_zero` — `𝒪_X(X_k)` has degree zero
  on every component, `deg(𝒪_X(Σ mᵢCᵢ)|_{Cⱼ}) = 0`.
* `Stacks.Models.intersectionProduct_specialFiber_eq_zero` — `(Σ aᵢCᵢ · Σ mᵢCᵢ) = 0`, the
  orthogonality property in the orientation the triviality of `𝒪_X(X_k)` gives directly.
* `Stacks.Models.componentDegree_invertibleSheaf_nonneg`,
  `Stacks.Models.componentDegree_invertibleSheaf_pos_iff` — for an integral proper curve `D` not
  contained in an effective Cartier divisor `E`, `deg(𝒪_X(E)|_D) ≥ 0`, and it is positive exactly
  when `D` meets `E`. This is the geometric input to part (1) of [Stacks, Tag 0C66].
* `Stacks.Models.sum_multiplicity_mul_intersectionMatrix_eq_zero_of_expansion` — the
  intersection matrix kills the multiplicity vector, given the bilinear expansion of
  [Stacks, Tag 0AYX].
* `Stacks.Models.intersectionForm_nonpos_of_properties`,
  `Stacks.Models.intersectionForm_eq_zero_iff_of_properties` — negative semidefiniteness and its
  equality case for a symmetric matrix with the other three properties, the source's own
  deduction through [Stacks, Tag 0C5X].

## Implementation notes

**Where the four properties of Tag 0C66 are.** All four are proved, at the irreducible
components of the special fibre, in
`StacksFrontier/AlgebraicGeometry/Curves/Models/SpecialFiberIntersectionForm.lean`, each carrying a
`@[stacks 0C66]` attribute. The orthogonality statement here carries one too, on its own
orientation of part (2); a tag registered on more than one declaration is not a duplication, and
the registration predates this file's present shape. This file holds the parts of the argument
that do not need the components to be the irreducible ones:

* the orthogonality property in the orientation `⟨a, 𝒪_X(Σ mᵢCᵢ)⟩ = 0`, for every integral family
  `a`. The source states it as `(Σ mᵢCᵢ · Cⱼ) = 0`, that is as `⟨m, 𝒪_X(Cⱼ)⟩`, and the two are
  the same number by the symmetry of the form of [Stacks, Tag 0C65]. That symmetry is
  [Stacks, Tag 0C64], proved in
  `StacksFrontier/AlgebraicGeometry/Curves/Models/DegreePairingSymmetry.lean`, so the source's own
  orientation is registered there as well; the statement here is the one the triviality
  of `𝒪_X(X_k)` gives directly, which is the input the source itself uses.
* the sign of `deg(𝒪_X(E)|_D)` for an integral proper curve `D ⊄ E`, through parts (1) and (2) of
  [Stacks, Tag 0B40]: the canonical section of `𝒪_X(E)` restricts to a nonzero section on `D`
  with zero scheme `D ∩ E`.
* the deduction of negative semidefiniteness and its equality case from the other three
  properties, through [Stacks, Tag 0C5X]. The two statements take those three as the hypotheses
  `hoffDiag`, `hsymm`, `hker` and `hconnected` because they are stated at an abstract matrix; they
  are discharged at the intersection matrix of the special fibre in the module named above.
  `hker` is supplied by
  `Stacks.Models.sum_multiplicity_mul_intersectionMatrix_eq_zero_of_expansion`, which is the
  orthogonality property together with the bilinear expansion of [Stacks, Tag 0AYX].

**The intersection matrix is an abstract family.** As in
`Stacks.Models.intersectionProduct_comm_of_expansion_of_matrix_symm`, the matrix `(Cᵢ · Cⱼ)` is
taken to be an abstract `N : ι → ι → ℤ` constrained by the expansion hypothesis `hexpand`, which
pins each entry down by taking the coefficient family supported at a single index. The form of
`Stacks.Models.intersectionProduct` cannot state negative semidefiniteness directly: its second
coefficient family is `ℕ`-valued, because only a nonnegative combination of the components is an
effective Cartier divisor, while the clause quantifies over rational `a`.

**Rational, not integral, coefficients.** The equality case asserts `aᵢ = q·mᵢ` for a rational
`q`, so the quadratic form is taken on `ι → ℚ`; the matrix lemmas of
`StacksFrontier/AlgebraicGeometry/SemistableReduction/LinearAlgebra/DiagonallyDominant.lean` apply
over any linearly ordered field.

## References

* [Stacks Project, Tag 0C66](https://stacks.math.columbia.edu/tag/0C66)
* [Stacks Project, Tag 0C65](https://stacks.math.columbia.edu/tag/0C65)
* [Stacks Project, Tag 0C61](https://stacks.math.columbia.edu/tag/0C61)
* [Stacks Project, Tag 0C5Z](https://stacks.math.columbia.edu/tag/0C5Z)
* [Stacks Project, Tag 0C5X](https://stacks.math.columbia.edu/tag/0C5X)
* [Stacks Project, Tag 0C62](https://stacks.math.columbia.edu/tag/0C62)
* [Stacks Project, Tag 0C64](https://stacks.math.columbia.edu/tag/0C64)
* [Stacks Project, Tag 0B40](https://stacks.math.columbia.edu/tag/0B40)
* [Stacks Project, Tag 0AYX](https://stacks.math.columbia.edu/tag/0AYX)
* [Stacks Project, Tag 0AYY](https://stacks.math.columbia.edu/tag/0AYY)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Matrix

universe u

namespace Stacks.Models

/-- The quadratic form of a matrix, written as the pairing of a vector with its image. -/
private theorem sum_sum_mul_eq_dotProduct_mulVec {ι : Type*} [Fintype ι] (A : Matrix ι ι ℚ)
    (x : ι → ℚ) :
    ∑ i, ∑ j, x i * x j * A i j = x ⬝ᵥ (A *ᵥ x) := by
  simp only [mulVec, dotProduct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-! ### The degree of the structure sheaf on a component -/

/-- The structure sheaf of a scheme, as a module over itself, is invertible in the spelling
`Stacks.SheafOfModules.IsInvertible` that `Stacks.Models.componentDegree` consumes. -/
theorem isTensorInvertible_unit (X : Scheme.{u}) :
    Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property (SheafOfModules.unit X.ringCatSheaf) :=
  Stacks.SheafOfModules.isInvertible_unit X.presheaf
    (structureSheafRing X.toRingedSpace).property

/-- **The structure sheaf has degree zero on a component**, `deg(𝒪_X|_D) = 0`: its restriction to
a closed subscheme is the structure sheaf of that subscheme, whose degree is the difference of
its own Euler characteristic with itself. -/
theorem componentDegree_unit_eq_zero (k : Type u) [Field k] {X : Scheme.{u}}
    (D : X.IdealSheafData) (g : D.subscheme ⟶ Spec (.of k)) (hg : IsProper g)
    (hdim : topologicalKrullDim D.subscheme ≤ 1)
    (hL : Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property (SheafOfModules.unit X.ringCatSheaf)) :
    componentDegree k D g hg hdim (SheafOfModules.unit X.ringCatSheaf) hL = 0 :=
  @invertibleCurveDegree_eq_zero_of_iso_unit k _ _ g hg hdim _
    (isInvertible_restrict D _ hL) (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso D.subschemeι)

/-! ### The degree of `𝒪_X(E)` on an integral curve `D` -/

section CurveDivisorDegree

open Opposite

/-- A point lies on the closed subscheme cut out by an ideal sheaf exactly when it is in the range
of its closed immersion. -/
private theorem mem_supportSet_iff_mem_range {Y : Scheme.{u}} (I : Y.IdealSheafData) (y : Y) :
    y ∈ I.supportSet ↔ y ∈ Set.range I.subschemeι := by
  rw [Scheme.IdealSheafData.range_subschemeι]
  rfl

/-- The structure sheaf of an empty scheme has a single global section. -/
private theorem subsingleton_unit_sections_of_isEmpty (Y : Scheme.{u}) [IsEmpty Y] :
    Subsingleton Γ(SheafOfModules.unit Y.ringCatSheaf, ⊤) :=
  (inferInstance : Subsingleton Γ(Y, ⊤))

variable (k : Type u) [Field k] {X : Scheme.{u}} (D E : X.IdealSheafData)
  [IsIntegral D.subscheme] [Stacks.Divisors.IsEffectiveCartierDivisor E]
  (g : D.subscheme ⟶ Spec (.of k)) (hg : IsProper g)
  (hdim : topologicalKrullDim D.subscheme ≤ 1)

omit [IsIntegral D.subscheme] in
/-- The zero scheme of the restriction to `D` of the canonical section `1_E` of `𝒪_X(E)` is the
scheme-theoretic intersection `E ∩ D`, read on `D`; its points are the points of `D` lying on
`E`. -/
theorem mem_supportSet_zeroScheme_pullbackCanonicalSection_iff (z : D.subscheme) :
    z ∈ (Stacks.Divisors.zeroScheme D.subscheme
        ((Scheme.Modules.pullback D.subschemeι).obj (Stacks.Divisors.invertibleSheaf' E))
        (Stacks.Divisors.pullbackCanonicalSection D.subschemeι E)).supportSet ↔
      D.subschemeι z ∈ E.supportSet := by
  refine (iff_of_eq (congrArg (fun I : D.subscheme.IdealSheafData => z ∈ I.supportSet)
    (Stacks.Divisors.zeroScheme_pullbackCanonicalSection D.subschemeι E))).trans ?_
  rw [Scheme.IdealSheafData.mem_supportSet_iff_mem_support,
    Scheme.IdealSheafData.support_comap, Scheme.IdealSheafData.mem_supportSet_iff_mem_support]
  rfl

omit [IsIntegral D.subscheme] in
/-- **The restriction to `D` of the canonical section `1_E` is nonzero when `D ⊄ E`**: the zero
section has the whole of `D` as its zero scheme, while the zero scheme of the restriction of `1_E`
is `E ∩ D`. -/
theorem pullbackCanonicalSection_subschemeι_ne_zero (hDE : ¬ D.supportSet ⊆ E.supportSet) :
    Stacks.Divisors.pullbackCanonicalSection D.subschemeι E ≠ 0 := by
  intro h0
  apply hDE
  intro x hx
  rw [mem_supportSet_iff_mem_range] at hx
  obtain ⟨z, rfl⟩ := hx
  refine (mem_supportSet_zeroScheme_pullbackCanonicalSection_iff D E z).1 ?_
  have hbot : Stacks.Divisors.zeroScheme D.subscheme
      ((Scheme.Modules.pullback D.subschemeι).obj (Stacks.Divisors.invertibleSheaf' E)) 0 = ⊥ := by
    refine Scheme.IdealSheafData.ext (funext fun U ↦ le_antisymm ?_ bot_le)
    refine (Scheme.IdealSheafData.ideal_ofIdeals_le _ U).trans ?_
    rw [Ideal.span_le]
    rintro a ⟨φ, rfl⟩
    simp
  rw [h0, hbot, Scheme.IdealSheafData.mem_supportSet_iff_mem_support,
    Scheme.IdealSheafData.support_bot]
  trivial

/-- **The degree of `𝒪_X(E)` on an integral proper curve `D ⊄ E` is nonnegative**: the
restriction of the canonical section `1_E` is a nonzero global section of `𝒪_X(E)|_D`, and
[Stacks, Tag 0B40] part (1) applies. -/
theorem componentDegree_invertibleSheaf_nonneg (hDE : ¬ D.supportSet ⊆ E.supportSet) :
    0 ≤ componentDegree k D g hg hdim (Stacks.Divisors.invertibleSheaf' E)
      (Stacks.Divisors.isTensorInvertible_invertibleSheaf E) := by
  have := hg
  exact invertibleCurveDegree_nonneg_of_eval_top_ne_zero k g hdim _
    (Stacks.Divisors.sectionsOfTop _ (Stacks.Divisors.pullbackCanonicalSection D.subschemeι E))
    (by
      rw [Stacks.Divisors.sectionsOfTop_eval_top]
      exact pullbackCanonicalSection_subschemeι_ne_zero D E hDE)

/-- **The degree of `𝒪_X(E)` on an integral proper curve `D ⊄ E` is positive exactly when `D`
meets `E`.** If `D ∩ E ≠ ∅` the restriction of `1_E` is a nonzero section with a zero, and
[Stacks, Tag 0B40] part (2) applies. If `D ∩ E = ∅` that section has empty zero scheme, and the
degree, which is the dimension of the sections of `𝒪_X(E)|_{D ∩ E}` over the empty scheme, is
zero. -/
theorem componentDegree_invertibleSheaf_pos_iff (hDE : ¬ D.supportSet ⊆ E.supportSet) :
    0 < componentDegree k D g hg hdim (Stacks.Divisors.invertibleSheaf' E)
        (Stacks.Divisors.isTensorInvertible_invertibleSheaf E) ↔
      (D.supportSet ∩ E.supportSet).Nonempty := by
  have := hg
  have hst : (Stacks.Divisors.sectionsOfTop
      ((Scheme.Modules.pullback D.subschemeι).obj (Stacks.Divisors.invertibleSheaf' E))
      (Stacks.Divisors.pullbackCanonicalSection D.subschemeι E)).eval (op ⊤) =
      Stacks.Divisors.pullbackCanonicalSection D.subschemeι E :=
    Stacks.Divisors.sectionsOfTop_eval_top _ _
  have hs : (Stacks.Divisors.sectionsOfTop
      ((Scheme.Modules.pullback D.subschemeι).obj (Stacks.Divisors.invertibleSheaf' E))
      (Stacks.Divisors.pullbackCanonicalSection D.subschemeι E)).eval (op ⊤) ≠ 0 := by
    rw [hst]
    exact pullbackCanonicalSection_subschemeι_ne_zero D E hDE
  have hne : Nonempty (Stacks.Divisors.zeroScheme D.subscheme
      ((Scheme.Modules.pullback D.subschemeι).obj (Stacks.Divisors.invertibleSheaf' E))
      (Stacks.Divisors.pullbackCanonicalSection D.subschemeι E)).subscheme ↔
      (D.supportSet ∩ E.supportSet).Nonempty := by
    refine ⟨fun ⟨w⟩ => ⟨_, (mem_supportSet_iff_mem_range _ _).2 ⟨_, rfl⟩,
      (mem_supportSet_zeroScheme_pullbackCanonicalSection_iff D E _).1
        ((mem_supportSet_iff_mem_range _ _).2 ⟨w, rfl⟩)⟩, ?_⟩
    rintro ⟨x, hxD, hxE⟩
    obtain ⟨z, rfl⟩ := (mem_supportSet_iff_mem_range _ _).1 hxD
    obtain ⟨w, -⟩ := (mem_supportSet_iff_mem_range _ _).1
      ((mem_supportSet_zeroScheme_pullbackCanonicalSection_iff D E z).2 hxE)
    exact ⟨w⟩
  rw [← hst] at hne
  constructor
  · intro hpos
    by_contra hemp
    have hE : IsEmpty (Stacks.Divisors.zeroScheme D.subscheme
        ((Scheme.Modules.pullback D.subschemeι).obj (Stacks.Divisors.invertibleSheaf' E))
        ((Stacks.Divisors.sectionsOfTop
          ((Scheme.Modules.pullback D.subschemeι).obj (Stacks.Divisors.invertibleSheaf' E))
          (Stacks.Divisors.pullbackCanonicalSection D.subschemeι E)).eval (op ⊤))).subscheme :=
      not_nonempty_iff.1 fun h => hemp (hne.1 h)
    obtain ⟨e⟩ := nonempty_pullback_zeroScheme_iso_unit k g hdim _ _ hs
    have hzero : componentDegree k D g hg hdim (Stacks.Divisors.invertibleSheaf' E)
        (Stacks.Divisors.isTensorInvertible_invertibleSheaf E) = 0 := by
      show @invertibleCurveDegree k _ _ g hg hdim
        ((Scheme.Modules.pullback D.subschemeι).obj (Stacks.Divisors.invertibleSheaf' E))
        (Stacks.Divisors.isInvertible_pullback_invertibleSheaf D.subschemeι E) = 0
      rw [invertibleCurveDegree_eq_finrank_cohomologyOverField_zero_zeroScheme k g hdim _ _ hs
          (forall_finiteDimensional_cohomologyOverField_unit k g),
        finrank_cohomologyOverField_eq_of_iso k _ e 0]
      have := @subsingleton_unit_sections_of_isEmpty _ hE
      rw [Nat.cast_eq_zero]
      exact @Module.finrank_zero_of_subsingleton _ _ _ _ _ _
        (cohomologyOverFieldZeroEquivSections k _ _).subsingleton
    exact (lt_irrefl (0 : ℤ)) (hzero ▸ hpos)
  · intro h
    exact invertibleCurveDegree_pos_of_nonempty_zeroScheme k g hdim _ _ hs (hne.2 h)

end CurveDivisorDegree

variable (S : RegularProperModelSituation.{u}) {ι : Type*} (s : Finset ι)
  (C : ι → S.X.IdealSheafData) (g : ∀ i, (C i).subscheme ⟶ Spec (.of S.k))
  (hg : ∀ i, IsProper (g i)) (hdim : ∀ i, topologicalKrullDim (C i).subscheme ≤ 1)

/-- **The degree pairing against the structure sheaf vanishes**, `⟨a, 𝒪_X⟩ = 0`, every term of
the defining sum having a vanishing component degree. -/
theorem degreePairing_unit_eq_zero (a : ι → ℤ) :
    degreePairing S s C g hg hdim a (SheafOfModules.unit S.X.ringCatSheaf)
      (isTensorInvertible_unit S.X) = 0 :=
  Finset.sum_eq_zero fun i _ => by
    rw [componentDegree_unit_eq_zero S.k (C i) (g i) (hg i) (hdim i)
      (isTensorInvertible_unit S.X), mul_zero]

/-! ### The special fibre is orthogonal to every combination of its components -/

/-- **The sheaf of the special fibre is trivial**, `𝒪_X(Σ mᵢCᵢ) ≅ 𝒪_X`, in the spelling
`Stacks.Models.divisorSheaf`: the sum `Σ mᵢCᵢ` is the special fibre, and the special fibre is cut
out by a uniformizer, which is a regular global section of the structure sheaf. -/
def divisorSheafIsoUnit_specialFiber (m : ι → ℕ)
    (hdec : S.specialFiberIdeal = ∏ i ∈ s, C i ^ m i) :
    divisorSheaf S s C m ≅ SheafOfModules.unit S.X.ringCatSheaf :=
  eqToIso (congrArg Stacks.Divisors.invertibleSheaf' hdec.symm) ≪≫
    invertibleSheafIso_specialFiberIdeal S

/-- **The sheaf of the special fibre has degree zero on every component**,
`deg(𝒪_X(Σ mᵢCᵢ)|_{Cⱼ}) = 0`, because that sheaf is trivial. -/
theorem componentDegree_divisorSheaf_specialFiber_eq_zero (m : ι → ℕ) (i : ι)
    (hC : ∀ j ∈ s, Stacks.Divisors.IsEffectiveCartierDivisor (C j))
    (hdec : S.specialFiberIdeal = ∏ j ∈ s, C j ^ m j) :
    componentDegree S.k (C i) (g i) (hg i) (hdim i) (divisorSheaf S s C m)
      (isInvertible_divisorSheaf S s C m hC) = 0 := by
  rw [componentDegree_eq_of_iso S.k (C i) (g i) (hg i) (hdim i) (divisorSheaf S s C m)
    (SheafOfModules.unit S.X.ringCatSheaf) (isInvertible_divisorSheaf S s C m hC)
    (isTensorInvertible_unit S.X) (divisorSheafIsoUnit_specialFiber S s C m hdec)]
  exact componentDegree_unit_eq_zero S.k (C i) (g i) (hg i) (hdim i)
    (isTensorInvertible_unit S.X)

/-- **The special fibre is orthogonal to every integral combination of the components**,
`(Σ aᵢCᵢ · Σ mᵢCᵢ) = 0`, because the sheaf `𝒪_X(Σ mᵢCᵢ) = 𝒪_X(X_k)` is trivial and the structure
sheaf has degree zero on each component.

This is part (2) of [Stacks, Tag 0C66] at an abstract family of components and in the orientation
that the triviality of `𝒪_X(X_k)` gives directly. The clause as the source states it,
`(Σ mᵢCᵢ · Cⱼ) = 0` at the irreducible components of the special fibre, is
`Stacks.Models.RegularProperModelSituation.specialFiberIntersectionProduct_multiplicity_eq_zero`
of `StacksFrontier/AlgebraicGeometry/Curves/Models/SpecialFiberIntersectionForm.lean`, and follows
from this statement by the symmetry of the form, [Stacks, Tag 0C64]. Both are registered. -/
@[stacks 0C66 "part (2), in the orientation (∑ aᵢCᵢ · ∑ mᵢCᵢ) = 0 of the symmetric form"]
theorem intersectionProduct_specialFiber_eq_zero (a : ι → ℤ) (m : ι → ℕ)
    (hC : ∀ j ∈ s, Stacks.Divisors.IsEffectiveCartierDivisor (C j))
    (hdec : S.specialFiberIdeal = ∏ j ∈ s, C j ^ m j) :
    intersectionProduct S s C g hg hdim a m hC = 0 := by
  rw [intersectionProduct_eq_degreePairing_divisorSheaf]
  exact Finset.sum_eq_zero fun i _ => by
    rw [componentDegree_divisorSheaf_specialFiber_eq_zero S s C g hg hdim m i hC hdec, mul_zero]

/-! ### The components of the special fibre: containment and meeting -/

namespace RegularProperModelSituation

variable (S : RegularProperModelSituation.{u})

/-- Two distinct irreducible components of the special fibre: neither is contained in the other,
read on their ideal sheaves in `X`. -/
theorem not_supportSet_specialFiberComponentIdeal_subset
    {Z W : irreducibleComponents S.specialFiber} (h : Z ≠ W) :
    ¬ (S.specialFiberComponentIdeal Z).supportSet ⊆
      (S.specialFiberComponentIdeal W).supportSet := by
  intro hsub
  refine S.toRegularModelSituation.genericPoint_specialFiberComponent_notMem_support (Ne.symm h)
    (hsub ?_)
  rw [Scheme.IdealSheafData.mem_supportSet_iff_mem_support, ← SetLike.mem_coe,
    ← Scheme.IdealSheafData.range_subschemeι]
  exact ⟨_, rfl⟩

/-- The two components meet in the special fibre exactly when their ideal sheaves have a common
point in `X`. -/
theorem nonempty_inter_supportSet_specialFiberComponentIdeal_iff
    (Z W : irreducibleComponents S.specialFiber) :
    ((S.specialFiberComponentIdeal Z).supportSet ∩
        (S.specialFiberComponentIdeal W).supportSet).Nonempty ↔
      ((Z.1 : Set S.specialFiber) ∩ W.1).Nonempty := by
  have hc : ∀ Y : irreducibleComponents S.specialFiber,
      (S.specialFiberComponentIdeal Y).supportSet =
        S.specialFiberι.base '' (Y.1 : Set S.specialFiber) := fun Y => by
    rw [← S.toRegularModelSituation.coe_support_specialFiberComponentIdeal Y]
    rfl
  rw [hc, hc, ← Set.image_inter S.specialFiberι.isClosedEmbedding.injective, Set.image_nonempty]

/-- Every point of the special fibre lies on one of its irreducible components. -/
theorem exists_mem_specialFiberComponent (y : S.specialFiber) :
    ∃ Z : irreducibleComponents S.specialFiber, y ∈ (Z.1 : Set S.specialFiber) := by
  obtain ⟨Z, hZ, hyZ⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    ({y} : Set S.specialFiber) isIrreducible_singleton
  exact ⟨⟨Z, hZ⟩, hyZ rfl⟩

end RegularProperModelSituation

/-! ### Negative semidefiniteness, from the three other clauses -/

section NegativeSemidefinite

variable [Fintype ι] (N : ι → ι → ℤ) (m : ι → ℕ)
  (hC : ∀ j, Stacks.Divisors.IsEffectiveCartierDivisor (C j))

/-- **The intersection matrix kills the multiplicity vector**, `Σⱼ mⱼ(Cᵢ · Cⱼ) = 0`. This is the
orthogonality clause of [Stacks, Tag 0C66] read entry by entry: the left-hand side is the
expansion of `deg(𝒪_X(Σ mⱼCⱼ)|_{Cᵢ})`, which vanishes because that sheaf is trivial. The
expansion is the hypothesis `hexpand`, the invertible case of [Stacks, Tag 0AYX]. -/
theorem sum_multiplicity_mul_intersectionMatrix_eq_zero_of_expansion
    (hexpand : ∀ c : ι → ℕ, ∀ i, componentDegree S.k (C i) (g i) (hg i) (hdim i)
      (divisorSheaf S Finset.univ C c)
      (isInvertible_divisorSheaf S Finset.univ C c fun j _ => hC j) =
        ∑ j, (c j : ℤ) * N i j)
    (hdec : S.specialFiberIdeal = ∏ j, C j ^ m j) (i : ι) :
    ∑ j, (m j : ℤ) * N i j = 0 :=
  (hexpand m i).symm.trans (componentDegree_divisorSheaf_specialFiber_eq_zero S Finset.univ C g hg
    hdim m i (fun j _ => hC j) hdec)

variable (hoffDiag : ∀ i j, i ≠ j → 0 ≤ N i j) (hsymm : ∀ i j, N i j = N j i)
  (hm : ∀ i, 0 < m i) (hker : ∀ i, ∑ j, (m j : ℤ) * N i j = 0)

include hoffDiag hsymm hm hker

omit [Fintype ι] hoffDiag hm hker in
/-- The intersection matrix, read over the rationals, is symmetric. -/
private theorem intersectionMatrix_isSymm :
    Matrix.IsSymm (A := (fun i j => (N i j : ℚ))) := by
  refine Matrix.ext fun i j => ?_
  show (N j i : ℚ) = (N i j : ℚ)
  exact_mod_cast hsymm j i

omit hoffDiag hsymm hm in
/-- The intersection matrix, read over the rationals, kills the multiplicity vector. -/
private theorem intersectionMatrix_mulVec_multiplicity :
    (fun i j => (N i j : ℚ)) *ᵥ (fun i => (m i : ℚ)) = (0 : ι → ℚ) := by
  funext i
  have h : ((∑ j, (m j : ℤ) * N i j : ℤ) : ℚ) = 0 := by rw [hker i, Int.cast_zero]
  push_cast at h
  simpa [mulVec, dotProduct, mul_comm] using h

/-- **The quadratic form of the intersection matrix is nonpositive**,
`(Σ aᵢCᵢ · Σ aᵢCᵢ) ≤ 0`. This is the negative semidefiniteness clause of [Stacks, Tag 0C66],
deduced as the source deduces it from the other three clauses: the matrix is symmetric with
nonnegative off-diagonal entries and kills the strictly positive multiplicity vector, so
[Stacks, Tag 0C5X] applies.

No attribute is attached here: the statement is about an abstract matrix, with the first and
second properties of the tag as the hypotheses `hoffDiag` and `hker`. Both are discharged at the
intersection matrix of the special fibre in
`Stacks.Models.RegularProperModelSituation.specialFiberIntersectionForm_nonpos_and_eq_zero_iff`,
which carries the attribute. -/
theorem intersectionForm_nonpos_of_properties (x : ι → ℚ) :
    ∑ i, ∑ j, x i * x j * (N i j : ℚ) ≤ 0 := by
  rw [sum_sum_mul_eq_dotProduct_mulVec (A := fun i j => (N i j : ℚ)) x]
  exact Matrix.dotProduct_mulVec_nonpos_of_positive_kernel
    (intersectionMatrix_isSymm N hsymm)
    (fun i j hij => by exact_mod_cast hoffDiag i j hij)
    (fun i => by exact_mod_cast hm i)
    (intersectionMatrix_mulVec_multiplicity N m hker) x

/-- **The quadratic form of the intersection matrix vanishes exactly on the rational multiples of
the multiplicity vector.** This is the equality case of the negative semidefiniteness clause of
[Stacks, Tag 0C66], deduced as the source deduces it: `hconnected` is the third clause of the
tag, and with the other two [Stacks, Tag 0C5X] identifies the nullspace of the form with the line
spanned by the multiplicity vector.

No attribute is attached here: the statement is about an abstract matrix, with the three other
properties of the tag as the hypotheses `hoffDiag`, `hker` and `hconnected`. All three are
discharged at the intersection matrix of the special fibre in
`Stacks.Models.RegularProperModelSituation.specialFiberIntersectionForm_nonpos_and_eq_zero_iff`,
which carries the attribute. -/
theorem intersectionForm_eq_zero_iff_of_properties
    (hconnected : ∀ I : Set ι, I.Nonempty → I ≠ Set.univ → ¬ ∀ i ∈ I, ∀ j ∉ I, N i j = 0)
    (x : ι → ℚ) :
    ∑ i, ∑ j, x i * x j * (N i j : ℚ) = 0 ↔ ∃ q : ℚ, ∀ i, x i = q * (m i : ℚ) := by
  rw [sum_sum_mul_eq_dotProduct_mulVec (A := fun i j => (N i j : ℚ)) x,
    Matrix.dotProduct_mulVec_eq_zero_iff_of_positive_kernel
      (intersectionMatrix_isSymm N hsymm)
      (fun i j hij => by exact_mod_cast hoffDiag i j hij)
      (fun i => by exact_mod_cast hm i)
      (intersectionMatrix_mulVec_multiplicity N m hker)
      (fun I hI hIne hzero => hconnected I hI hIne fun i hi j hj => by
        exact_mod_cast hzero i hi j hj)]
  exact ⟨fun ⟨q, hq⟩ => ⟨q, fun i => by rw [hq]; rfl⟩,
    fun ⟨q, hq⟩ => ⟨q, funext fun i => by rw [hq i]; rfl⟩⟩

end NegativeSemidefinite

end Stacks.Models

end
