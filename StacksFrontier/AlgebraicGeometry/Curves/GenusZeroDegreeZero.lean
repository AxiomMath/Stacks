module

public import StacksFrontier.AlgebraicGeometry.Curves.GenusZeroPositiveDegree.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.LinearSeries
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingExtension
public import StacksFrontier.AlgebraicGeometry.QuasiAffineNonvanishing.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SectionDegree
public import StacksCore.Tactic.StacksAttribute

/-!
# A degree-zero invertible sheaf on a genus-zero curve is trivial

Let `X` be a proper curve over a field `k` with `H⁰(X, 𝒪_X) = k`. If `X` has genus `0`, then
every invertible `𝒪_X`-module `ℒ` of degree `0` is trivial.

The hypothesis `H⁰(X, 𝒪_X) = k` is `IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)`, "proper
curve over `k`" is `AlgebraicGeometry.IsCurve` together with `AlgebraicGeometry.IsProper`, the
genus is `AlgebraicGeometry.genus`, and the degree is `AlgebraicGeometry.invertibleCurveDegree`.

## Main results

* `AlgebraicGeometry.isTrivial_of_genus_eq_zero_of_invertibleCurveDegree_eq_zero`: on a proper
  curve of genus `0` with `H⁰(X, 𝒪_X) = k`, an invertible module of degree `0` is trivial.

## References

* [Stacks Project, Tag 0C6M](https://stacks.math.columbia.edu/tag/0C6M)
* [Stacks Project, Tag 0B40](https://stacks.math.columbia.edu/tag/0B40)
* [Stacks Project, Tag 0AYR](https://stacks.math.columbia.edu/tag/0AYR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- Let `X` be a proper curve over a field `k` with `H⁰(X, 𝒪_X) = k`. If `X` has genus `0`, then
every invertible `𝒪_X`-module `ℒ` of degree `0` is trivial. -/
@[stacks 0C6M]
public theorem isTrivial_of_genus_eq_zero_of_invertibleCurveDegree_eq_zero [IsCurve k f]
    [IsProper f] [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property L]
    (hgenus : genus f = 0)
    (hdeg : invertibleCurveDegree k f
      (IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)).le L = 0) :
    SheafOfModules.IsTrivial X.presheaf X.ringCatSheaf.property L := by
  set hdim : topologicalKrullDim X ≤ 1 :=
    (IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)).le
  have hvan : ∀ (F : X.Modules) (m : ℕ), 2 ≤ m → IsZero (cohomologyOverField k f F m) :=
    fun F m hm => isZero_cohomologyOverField_of_topologicalKrullDim_le k f F (d := 1)
      (by exact_mod_cast hdim) (by omega)
  have hdeg' := hdeg
  rw [invertibleCurveDegree_eq_sub_of_isZero k f hdim L (hvan L)
      (hvan (SheafOfModules.unit X.ringCatSheaf)),
    finrank_cohomologyOverField_unit_zero_eq_one f,
    finrank_cohomologyOverField_unit_one_eq_zero_of_genus_eq_zero k f hgenus] at hdeg'
  have hpos : 0 < Module.finrank k (cohomologyOverField k f L 0) := by
    push_cast at hdeg'
    omega
  have _ : Nontrivial (cohomologyOverField k f L 0) := Module.nontrivial_of_finrank_pos hpos
  have _ : Nontrivial Γ(L, ⊤) :=
    (cohomologyOverFieldZeroEquivSections k f L).injective.nontrivial
  obtain ⟨t, ht⟩ := exists_ne (0 : Γ(L, ⊤))
  let : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L := by
    show SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property L
    infer_instance
  exact isTrivial_of_invertibleCurveDegree_nonpos k f hdim L
    (Stacks.SheafOfModules.sectionsOfTopOfRingSheaf L t)
    (ne_of_eq_of_ne (Stacks.SheafOfModules.sectionsOfTopOfRingSheaf_eval_top L t) ht)
    (le_of_eq hdeg)

end AlgebraicGeometry

end
