module

public import Mathlib.RingTheory.GradedAlgebra.FiniteType
public import StacksFrontier.AlgebraicGeometry.Algebraization.LefschetzCone.FiniteSheaves
public import StacksFrontier.AlgebraicGeometry.Curves.VeryAmpleInvertibleSheaves.SectionRingDegreeTwo
public import StacksFrontier.AlgebraicGeometry.ProjNoetherian.Basic
public import StacksFrontier.AlgebraicGeometry.VeroneseVeryAmple.Basic

/-!
# Stacks Tag 0E8W: the square of a globally generated invertible sheaf on a curve

Let `k` be a field and `X` a proper scheme over `k` of dimension `1` with `H⁰(X, 𝒪_X) = k`. Let
`ℒ` be an invertible `𝒪_X`-module which is globally generated, has `H¹(X, ℒ) = 0`, and is ample.
**Stacks Tag 0E8W** asserts that `ℒ^{⊗ 2}` is very ample on `X` over `k`.

Very ampleness is `Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple` for the structure morphism
`f : X ⟶ Spec k` ([Stacks, Tag 01VM]).

## Main results

* `Stacks.Curves.VeryAmpleSquare.isRelativelyVeryAmple_tensorPowModule_two`: **Stacks Tag 0E8W**,
  with no hypothesis beyond the source's.

## Implementation notes

The source's proof shows that the section ring `S = ⨁_{n ≥ 0} H⁰(X, ℒ^{⊗ n})` is generated in
degrees `0, 1, 2`, so that `S^{(2)}` is generated in degree one, and concludes with the closing
sentence of [Stacks, Tag 0E8V]: `X = Proj(S)`, so `ℒ^{⊗ 2}` is very ample.

* The generation statement is
  `Stacks.Curves.SectionRingDegreeTwo.veroneseGeneratedInDegOne_two`. The source obtains the
  surjectivity of `H⁰(ℒ) ⊗ H⁰(ℒ^{⊗ n}) ⟶ H⁰(ℒ^{⊗ n+1})` for `n ≥ 2` by passing to the algebraic
  closure ([Stacks, Tag 02L6]) and choosing a regular section using that `X` is Cohen–Macaulay
  ([Stacks, Tag 0BY5]); that module instead proves it over `k` itself, from the Koszul complex of
  the surjection `𝒪_X^{⊕ r} ⟶ ℒ` given by finitely many generating global sections
  ([Stacks, Tag 01ND]) and the vanishing of `H²` on the one-dimensional `X` ([Stacks, Tag 02UZ]).
* The closing step is
  `Stacks.VeroneseVeryAmple.isRelativelyVeryAmple_tensorPowModule_of_generators`, which uses
  `X = Proj(S)` ([Stacks, Tag 0C6J]) and the canonical morphism of [Stacks, Tag 01PZ]. It asks for
  finitely many homogeneous generators of `S` of positive degree; `S` is Noetherian
  (`Stacks.LefschetzCone.isNoetherianRing_sectionRing`), hence of finite type over `S₀`
  (`Stacks.AlgebraicGeometry.Proj.finiteType_of_isNoetherianRing`), and Mathlib's
  `GradedAlgebra.exists_finset_adjoin_eq_top_and_homogeneous_ne_zero` provides them.

## References

* [Stacks Project, Tag 0E8W](https://stacks.math.columbia.edu/tag/0E8W)
* [Stacks Project, Tag 0E8V](https://stacks.math.columbia.edu/tag/0E8V)
* [Stacks Project, Tag 01ND](https://stacks.math.columbia.edu/tag/01ND)
* [Stacks Project, Tag 01PZ](https://stacks.math.columbia.edu/tag/01PZ)
* [Stacks Project, Tag 0C6J](https://stacks.math.columbia.edu/tag/0C6J)
* [Stacks Project, Tag 01VM](https://stacks.math.columbia.edu/tag/01VM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Ample
open Stacks.GradedSections (sectionRing)
open Stacks.AmpleFiniteAvoidance (grading)

universe u

namespace Stacks.Curves.VeryAmpleSquare

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso Stacks.SheafInternalHom.isLocalization_sheafify
  Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

variable {X : Scheme.{u}} (L : X.Modules) [IsInvertibleModule X L]

/-- **The section ring of an ample invertible module on a proper scheme over a field is generated
over its degree-zero part by finitely many homogeneous elements of positive degree.** -/
theorem exists_homogeneous_generators (k : Type u) [Field k] (f : X ⟶ Spec (.of k))
    [IsProper f] (hample : IsAmple X L) :
    ∃ (r : ℕ) (g : Fin r → sectionRing L) (deg : Fin r → ℕ), (∀ i, 1 ≤ deg i) ∧
      (∀ i, g i ∈ grading L (deg i)) ∧
        Algebra.adjoin (Stacks.Veronese.gradeZero (grading L)) (Set.range g) = ⊤ := by
  classical
  have := Stacks.LefschetzCone.isNoetherianRing_sectionRing f L hample
  have := Stacks.AlgebraicGeometry.Proj.finiteType_of_isNoetherianRing (grading L)
  obtain ⟨t, ht, hthom⟩ :=
    GradedAlgebra.exists_finset_adjoin_eq_top_and_homogeneous_ne_zero (grading L)
  choose deg' hdeg' using hthom
  let e := t.equivFin
  refine ⟨t.card, fun i => (e.symm i : sectionRing L),
    fun i => deg' (e.symm i) (e.symm i).2, fun i => Nat.one_le_iff_ne_zero.2 (hdeg' _ _).1,
    fun i => (hdeg' _ _).2, ?_⟩
  have hrange : Set.range (fun i => (e.symm i : sectionRing L)) = (t : Set (sectionRing L)) := by
    ext x
    refine ⟨?_, fun hx => ⟨e ⟨x, hx⟩, by simp⟩⟩
    rintro ⟨i, rfl⟩
    exact (e.symm i).2
  rw [hrange, eq_top_iff]
  rintro x -
  have hx : x ∈ Algebra.adjoin (grading L 0) (t : Set (sectionRing L)) := ht ▸ Algebra.mem_top
  induction hx using Algebra.adjoin_induction with
  | mem x hx => exact Algebra.subset_adjoin hx
  | algebraMap r =>
    exact Subalgebra.algebraMap_mem _ (⟨r.1, r.2⟩ : Stacks.Veronese.gradeZero (grading L))
  | add x y _ _ hx hy => exact Subalgebra.add_mem _ hx hy
  | mul x y _ _ hx hy => exact Subalgebra.mul_mem _ hx hy

/-- Let `k` be a field and `f : X ⟶ Spec k` proper with `X` of dimension `1` and
`H⁰(X, 𝒪_X) = k`. Let `ℒ` be an invertible `𝒪_X`-module which is globally generated, has
`H¹(X, ℒ) = 0`, and is ample. Then `ℒ^{⊗ 2}` is very ample relative to `f`. -/
@[stacks 0E8W]
theorem isRelativelyVeryAmple_tensorPowModule_two (k : Type u) [Field k]
    (f : X ⟶ Spec (.of k)) [IsProper f] [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]
    (hdim : topologicalKrullDim X = 1)
    (hgg : _root_.SheafOfModules.IsGeneratedByGlobalSections L)
    (hH1 : IsZero (cohomologyOverField k f L 1)) (hample : IsAmple X L) :
    Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple f (tensorPowModule X L 2) := by
  obtain ⟨r, g, deg, hdeg1, hg, hgen⟩ := exists_homogeneous_generators L k f hample
  exact Stacks.VeroneseVeryAmple.isRelativelyVeryAmple_tensorPowModule_of_generators L k f hample
    g deg hdeg1 hg hgen (d := 2) (by omega)
    (Stacks.Curves.SectionRingDegreeTwo.veroneseGeneratedInDegOne_two L k f hdim.le hgg hH1)

end Stacks.Curves.VeryAmpleSquare

end
