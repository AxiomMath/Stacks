module

public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalTails.DualizingSheafDegree
public import StacksFrontier.AlgebraicGeometry.Curves.GenusZeroPositiveDegree.CanonicalComponents
public import StacksFrontier.AlgebraicGeometry.Curves.GenusZeroPositiveDegree.CanonicalPowers
public import StacksFrontier.AlgebraicGeometry.Curves.GenusZeroPositiveDegree.Conic
public import StacksFrontier.AlgebraicGeometry.CohomologyZeroLinear.Basic

/-!
# The dualizing sheaf of a nodal curve without rational tails

Let `X` be a proper scheme of dimension one over a field `k` with `H⁰(X, 𝒪_X) = k`, with
at-worst-nodal singularities and without rational tails. Then `ω_X` is invertible, and according
as the genus is `0`, `1` or at least `2`, `X` is an irreducible plane conic with `ω_X^{⊗ -1}` very
ample, `ω_X ≅ 𝒪_X`, or `ω_X^{⊗ m}` is globally generated for `m ≥ 2`: this is
[Stacks, Tag 0E3K].

## Main results

* `AlgebraicGeometry.exists_planeCurveData_deg_two_of_subcurve_bound`: an invertible module of
  degree `-2` satisfying the subcurve bound on a reduced curve of genus `0` exhibits `X` as an
  irreducible plane conic, with very ample inverse.
* `exists_planeCurveData_deg_two_of_forall_not_isRationalTail`,
  `nonempty_dualizingSheafOverField_iso_unit_of_forall_not_isRationalTail`,
  `isGeneratedByGlobalSections_tensorPower_dualizingSheafOverField_of_forall_not_isRationalTail`:
  [Stacks, Tag 0E3K], parts (1), (2), (3).

## References

* [Stacks Project, Tag 0E3K](https://stacks.math.columbia.edu/tag/0E3K)
* [Stacks Project, Tag 0E3J](https://stacks.math.columbia.edu/tag/0E3J)
* [Stacks Project, Tag 0E37](https://stacks.math.columbia.edu/tag/0E37)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open Stacks.SheafOfModules.Invertible (tensorPower tensorPower_isInvertible)
open Stacks.Curves

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **In genus zero the subcurve bound for a module of degree `-2` gives an irreducible plane
conic.** Let `X` be a proper reduced scheme of dimension one over `k` with `H⁰(X, 𝒪_X) = k` and
genus `0`, and `𝒩` an invertible module of degree `-2` with `dim H¹(Y, 𝒪_Y) ≤ deg(𝒩|_Y)` on proper
subcurves. Then `X` is irreducible (`AlgebraicGeometry.irreducibleSpace_of_subcurve_bound`), so
integral; `𝒩^{⊗ -1}` has degree `2`, so `X` is isomorphic to a plane curve of degree `2`, and
`𝒩^{⊗ -1}` is very ample. -/
theorem exists_planeCurveData_deg_two_of_subcurve_bound [IsProper f] [IsReduced X]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] (hdim : topologicalKrullDim X = 1)
    (hgenus : genus f = 0) (N : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N] (hsub : SubcurveBound f N)
    (hN : invertibleCurveDegree k f hdim.le N = -2) :
    (∃ C : ProjectiveSpectrum.Proj.PlaneCurveData k, C.deg = 2 ∧ IrreducibleSpace C.Z ∧
      ∃ e : X ≅ C.Z, e.hom ≫ C.toSpec = f) ∧
    letI := tensorPower_isInvertible X.presheaf X.ringCatSheaf.2 N (-1)
    Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple f
      (tensorPower X.presheaf X.ringCatSheaf.2 N (-1)) := by
  have : IrreducibleSpace X :=
    irreducibleSpace_of_subcurve_bound f hdim.le N hsub (by rw [hN]; norm_num)
  have : IsIntegral X := isIntegral_of_irreducibleSpace_of_isReduced X
  refine ⟨?_, isRelativelyVeryAmple_tensorPower_neg_one_of_genus_eq_zero f hdim.le hgenus N hN⟩
  let := tensorPower_isInvertible X.presheaf X.ringCatSheaf.2 N (-1)
  obtain ⟨C, hC, e, he⟩ := exists_planeCurveData_deg_two_of_invertibleCurveDegree_eq_two f hdim
    hgenus (tensorPower X.presheaf X.ringCatSheaf.2 N (-1))
    (by rw [invertibleCurveDegree_tensorPower k f hdim.le N (-1), hN]; norm_num)
  have : IsIntegral C.Z := IsIntegral.of_isIso e.hom
  exact ⟨C, hC, inferInstance, e, he⟩

/-- **A nonzero `H⁰` gives a nonzero global section.** If `H⁰(X, ℱ)` has positive dimension over
`k`, then `Γ(X, ℱ)` is nontrivial. -/
theorem nontrivial_globalSections_of_finrank_cohomologyOverField_zero_pos (F : X.Modules)
    (h : 0 < Module.finrank k (cohomologyOverField k f F 0)) : Nontrivial Γ(F, ⊤) := by
  have := Module.nontrivial_of_finrank_pos h
  exact (cohomologyOverFieldZeroLinearIso k f F).toLinearEquiv.toEquiv.symm.nontrivial

section NoRationalTail

variable [X.Over (Spec (.of k))]

/-- **Stacks Project, Tag 0E3K, part (1).** Let `X` be a proper scheme of dimension one over a
field `k` with `H⁰(X, 𝒪_X) = k`, with at-worst-nodal singularities and no rational tail. If `X`
has genus `0`, then `X` is isomorphic to an irreducible plane conic and `ω_X^{⊗ -1}` is very
ample.

`ω_X` is invertible of degree `2g - 2 = -2` ([Stacks, Tag 0E37], [Stacks, Tag 0C19]) and
satisfies the subcurve bound of [Stacks, Tag 0E3J], so
`AlgebraicGeometry.exists_planeCurveData_deg_two_of_subcurve_bound` applies. -/
@[stacks 0E3K "part (1)"]
theorem exists_planeCurveData_deg_two_of_forall_not_isRationalTail
    [IsProper (X ↘ Spec (.of k))] (hdim : topologicalKrullDim X = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
    (hnodal : HasAtWorstNodalSingularities k X)
    (htail : ∀ C : X.IdealSheafData, ¬ IsRationalTail k X C)
    (hgenus : genus (X ↘ Spec (.of k)) = 0) :
    (∃ C : ProjectiveSpectrum.Proj.PlaneCurveData k, C.deg = 2 ∧ IrreducibleSpace C.Z ∧
      ∃ e : X ≅ C.Z, e.hom ≫ C.toSpec = X ↘ Spec (.of k)) ∧
    haveI := connectedSpace_of_isIso_globalSections k (X ↘ Spec (.of k))
    letI := isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities k X hdim hnodal
    letI := tensorPower_isInvertible X.presheaf X.ringCatSheaf.2
      (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))) (-1)
    Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple (X ↘ Spec (.of k))
      (tensorPower X.presheaf X.ringCatSheaf.2
        (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))) (-1)) := by
  have := connectedSpace_of_isIso_globalSections k (X ↘ Spec (.of k))
  let := isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities k X hdim hnodal
  have : IsReduced X := isReduced_of_hasAtWorstNodalSingularities k X hnodal
  have hω := invertibleCurveDegree_dualizingSheafOverField_of_isInvertible k (X ↘ Spec (.of k))
    hdim.le
  rw [hgenus] at hω
  exact exists_planeCurveData_deg_two_of_subcurve_bound (X ↘ Spec (.of k)) hdim hgenus _
    (fun Y _ _ hY hYX =>
      finrank_cohomologyOverField_one_le_invertibleCurveDegree_of_forall_not_isRationalTail
        hdim hnodal htail Y hY hYX)
    (by rw [hω]; norm_num)

/-- **Stacks Project, Tag 0E3K, part (2).** Let `X` be a proper scheme of dimension one over a
field `k` with `H⁰(X, 𝒪_X) = k`, with at-worst-nodal singularities and no rational tail. If `X`
has genus `1`, then `ω_X ≅ 𝒪_X`.

`ω_X` is invertible of degree `2g - 2 = 0` with `h⁰(ω_X) = g = 1`, and satisfies the subcurve
bound of [Stacks, Tag 0E3J]; so every component degree is nonnegative, they sum to `0`
([Stacks, Tag 0AYW]), and [Stacks, Tag 0E22] applies
(`AlgebraicGeometry.isTrivial_of_subcurve_bound`). -/
@[stacks 0E3K "part (2)"]
theorem nonempty_dualizingSheafOverField_iso_unit_of_forall_not_isRationalTail
    [IsProper (X ↘ Spec (.of k))] (hdim : topologicalKrullDim X = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
    (hnodal : HasAtWorstNodalSingularities k X)
    (htail : ∀ C : X.IdealSheafData, ¬ IsRationalTail k X C)
    (hgenus : genus (X ↘ Spec (.of k)) = 1) :
    Nonempty (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k)) ≅
      SheafOfModules.unit X.ringCatSheaf) := by
  have := connectedSpace_of_isIso_globalSections k (X ↘ Spec (.of k))
  let := isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities k X hdim hnodal
  have : IsReduced X := isReduced_of_hasAtWorstNodalSingularities k X hnodal
  have hω := invertibleCurveDegree_dualizingSheafOverField_of_isInvertible k (X ↘ Spec (.of k))
    hdim.le
  rw [hgenus] at hω
  have h0 := Stacks.Duality.finrank_cohomologyOverField_zero_dualizingSheafOverField
    (X ↘ Spec (.of k)) hdim.le
  rw [hgenus] at h0
  exact isTrivial_of_subcurve_bound (X ↘ Spec (.of k))
    (equidimensional_of_isIso_globalSections_of_dimension_one k (X ↘ Spec (.of k)) hdim) hdim _
    (fun Y _ _ hY hYX =>
      finrank_cohomologyOverField_one_le_invertibleCurveDegree_of_forall_not_isRationalTail
        hdim hnodal htail Y hY hYX)
    (by rw [hω]; norm_num)
    (nontrivial_globalSections_of_finrank_cohomologyOverField_zero_pos (X ↘ Spec (.of k)) _
      (by rw [h0]; norm_num))

/-- **Stacks Project, Tag 0E3K, part (3).** Let `X` be a proper scheme of dimension one over a
field `k` with `H⁰(X, 𝒪_X) = k`, with at-worst-nodal singularities and no rational tail. If the
genus of `X` is at least `2`, then `ω_X^{⊗ m}` is globally generated for every `m ≥ 2`.

`ω_X` is invertible of degree `2g - 2` and satisfies the subcurve bound of [Stacks, Tag 0E3J],
which with `g ≥ 2` and `m ≥ 2` gives the inequalities of [Stacks, Tag 0E3F]
(`AlgebraicGeometry.isGeneratedByGlobalSections_tensorPower_of_subcurve_bound`). -/
@[stacks 0E3K "part (3)"]
theorem isGeneratedByGlobalSections_tensorPower_dualizingSheafOverField_of_forall_not_isRationalTail
    [IsProper (X ↘ Spec (.of k))] (hdim : topologicalKrullDim X = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
    (hnodal : HasAtWorstNodalSingularities k X)
    (htail : ∀ C : X.IdealSheafData, ¬ IsRationalTail k X C)
    (hgenus : 2 ≤ genus (X ↘ Spec (.of k))) (m : ℕ) (hm : 2 ≤ m) :
    haveI := connectedSpace_of_isIso_globalSections k (X ↘ Spec (.of k))
    letI := isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities k X hdim hnodal
    SheafOfModules.IsGeneratedByGlobalSections
      (tensorPower X.presheaf X.ringCatSheaf.2
        (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))) m) := by
  have := connectedSpace_of_isIso_globalSections k (X ↘ Spec (.of k))
  let := isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities k X hdim hnodal
  have : IsReduced X := isReduced_of_hasAtWorstNodalSingularities k X hnodal
  exact isGeneratedByGlobalSections_tensorPower_of_subcurve_bound (X ↘ Spec (.of k)) hdim hgenus _
    (invertibleCurveDegree_dualizingSheafOverField_of_isInvertible k (X ↘ Spec (.of k)) hdim.le)
    (fun Y _ _ hY hYX =>
      finrank_cohomologyOverField_one_le_invertibleCurveDegree_of_forall_not_isRationalTail
        hdim hnodal htail Y hY hYX)
    m hm

end NoRationalTail

end AlgebraicGeometry

end
