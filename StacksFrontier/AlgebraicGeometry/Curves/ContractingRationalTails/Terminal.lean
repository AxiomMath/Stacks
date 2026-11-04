module

public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalTails.Iterated
public import StacksFrontier.AlgebraicGeometry.Curves.GenusZeroPositiveDegree.CanonicalNodal

/-!
# Contracting rational tails until none are left

Let `X` be a proper scheme of dimension one over a field `k` with `H⁰(X, 𝒪_X) = k` and
at-worst-nodal singularities, and let `X = X₀ → X₁ → ⋯ → Xₙ = X'` be a chain of contractions of
rational tails such that `X'` has no rational tail. Then `X'` is an irreducible plane conic if `X`
has genus `0`, `ω_{X'} ≅ 𝒪_{X'}` if `X` has genus `1`, and `ω_{X'}^{⊗ m}` is globally generated for
`m ≥ 2` if `X` has genus at least `2`: this is [Stacks, Tag 0E3L], parts (1), (2), (3).

## Main results

In the namespace `AlgebraicGeometry.IsIteratedContractionOfRationalTails`:

* `exists_planeCurveData_deg_two`, `nonempty_dualizingSheafOverField_iso_unit`,
  `isGeneratedByGlobalSections_tensorPower_dualizingSheafOverField`: [Stacks, Tag 0E3L],
  parts (1), (2), (3).

## Implementation notes

The target `X'` of the chain is again proper, one-dimensional, at worst nodal, with `H⁰ = k` and
of the genus of `X` (`AlgebraicGeometry.IsIteratedContractionOfRationalTails.isProper_target` and
its companions, Tag 0E3H), so [Stacks, Tag 0E3K] applies to `X'` over `k`.

## References

* [Stacks Project, Tag 0E3L](https://stacks.math.columbia.edu/tag/0E3L)
* [Stacks Project, Tag 0E3K](https://stacks.math.columbia.edu/tag/0E3K)
* [Stacks Project, Tag 0E3H](https://stacks.math.columbia.edu/tag/0E3H)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.SheafOfModules.Invertible (tensorPower)

universe u

namespace AlgebraicGeometry.IsIteratedContractionOfRationalTails

variable {k : Type u} [Field k]
  {X Y : Scheme.{u}} {fX : X ⟶ Spec (.of k)} {fY : Y ⟶ Spec (.of k)} {c : X ⟶ Y}
  (hseq : IsIteratedContractionOfRationalTails k fX fY c) [IsProper fX]
  (hdim : topologicalKrullDim X = 1) [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ fX.appTop)]
  (hnodal : letI : X.Over (Spec (.of k)) := ⟨fX⟩
    Stacks.Curves.HasAtWorstNodalSingularities k X)
  (hterminal : ∀ C : Y.IdealSheafData, ¬ @IsRationalTail k _ Y ⟨fY⟩ C)

include hseq hdim hnodal hterminal

/-- **Stacks Project, Tag 0E3L, part (1).** Let `X` be a proper scheme of dimension one over a
field `k` with `H⁰(X, 𝒪_X) = k` and at-worst-nodal singularities, and `X → X'` a chain of
contractions of rational tails after which none are left. If `X` has genus `0`, then `X'` is an
irreducible plane conic over `k`. -/
@[stacks 0E3L "part (1)"]
theorem exists_planeCurveData_deg_two (hgenus : genus fX = 0) :
    ∃ C : ProjectiveSpectrum.Proj.PlaneCurveData k, C.deg = 2 ∧ IrreducibleSpace C.Z ∧
      ∃ e : Y ≅ C.Z, e.hom ≫ C.toSpec = fY := by
  let : Y.Over (Spec (.of k)) := ⟨fY⟩
  have : IsProper (Y ↘ Spec (.of k)) := isProper_target hseq hdim hnodal
  have : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (Y ↘ Spec (.of k)).appTop) :=
    isIso_globalSections_target hseq hdim hnodal
  exact (exists_planeCurveData_deg_two_of_forall_not_isRationalTail
    (topologicalKrullDim_target hseq hdim hnodal) (hasAtWorstNodalSingularities_target hseq hdim
      hnodal) hterminal ((genus_target hseq hdim hnodal).trans hgenus)).1

/-- **Stacks Project, Tag 0E3L, part (2).** Let `X` be a proper scheme of dimension one over a
field `k` with `H⁰(X, 𝒪_X) = k` and at-worst-nodal singularities, and `X → X'` a chain of
contractions of rational tails after which none are left. If `X` has genus `1`, then
`ω_{X'} ≅ 𝒪_{X'}`. -/
@[stacks 0E3L "part (2)"]
theorem nonempty_dualizingSheafOverField_iso_unit (hgenus : genus fX = 1) :
    haveI : IsProper fY := isProper_target hseq hdim hnodal
    Nonempty (Stacks.Duality.dualizingSheafOverField fY ≅ SheafOfModules.unit Y.ringCatSheaf) := by
  let : Y.Over (Spec (.of k)) := ⟨fY⟩
  have : IsProper (Y ↘ Spec (.of k)) := isProper_target hseq hdim hnodal
  have : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (Y ↘ Spec (.of k)).appTop) :=
    isIso_globalSections_target hseq hdim hnodal
  exact nonempty_dualizingSheafOverField_iso_unit_of_forall_not_isRationalTail
    (topologicalKrullDim_target hseq hdim hnodal) (hasAtWorstNodalSingularities_target hseq hdim
      hnodal) hterminal ((genus_target hseq hdim hnodal).trans hgenus)

/-- **Stacks Project, Tag 0E3L, part (3).** Let `X` be a proper scheme of dimension one over a
field `k` with `H⁰(X, 𝒪_X) = k` and at-worst-nodal singularities, and `X → X'` a chain of
contractions of rational tails after which none are left. If the genus of `X` is at least `2`,
then `ω_{X'}` is invertible and `ω_{X'}^{⊗ m}` is globally generated for every `m ≥ 2`. -/
@[stacks 0E3L "part (3)"]
theorem isGeneratedByGlobalSections_tensorPower_dualizingSheafOverField
    (hgenus : 2 ≤ genus fX) (m : ℕ) (hm : 2 ≤ m) :
    letI : Y.Over (Spec (.of k)) := ⟨fY⟩
    haveI : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ fY.appTop) :=
      isIso_globalSections_target hseq hdim hnodal
    haveI := connectedSpace_of_isIso_globalSections k fY
    haveI : IsProper fY := isProper_target hseq hdim hnodal
    letI : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
        (Stacks.Duality.dualizingSheafOverField fY) :=
      @isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities k _ Y _ this _
        (topologicalKrullDim_target hseq hdim hnodal)
        (hasAtWorstNodalSingularities_target hseq hdim hnodal)
    SheafOfModules.IsGeneratedByGlobalSections
      (tensorPower Y.presheaf Y.ringCatSheaf.2 (Stacks.Duality.dualizingSheafOverField fY) m) := by
  let : Y.Over (Spec (.of k)) := ⟨fY⟩
  have : IsProper (Y ↘ Spec (.of k)) := isProper_target hseq hdim hnodal
  have : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (Y ↘ Spec (.of k)).appTop) :=
    isIso_globalSections_target hseq hdim hnodal
  exact isGeneratedByGlobalSections_tensorPower_dualizingSheafOverField_of_forall_not_isRationalTail
    (topologicalKrullDim_target hseq hdim hnodal) (hasAtWorstNodalSingularities_target hseq hdim
      hnodal) hterminal (hgenus.trans_eq (genus_target hseq hdim hnodal).symm) m hm

end AlgebraicGeometry.IsIteratedContractionOfRationalTails

end
