module

public import StacksFrontier.AlgebraicGeometry.ProjectiveCohomology.CechWeightSplitting

/-!
# The Laurent weight decomposition of the Čech terms of a twist on projective space

`Stacks.ProjectiveCohomology.cechTwistTermEquiv` identifies the degree-`p` term of the Čech
complex of `𝒪(d)` for the `n + 1` standard coordinate charts of `Proj R[T₀, …, Tₙ]` with the
product, over the tuples `x` of `p + 1` coordinate indices, of the degree-`d` parts
`Stacks.ProjectiveCohomology.twistWeightSpan` of the localizations. This file decomposes those
terms along the `ℤ^{n+1}`-valued Laurent weight and shows that the Čech differential respects the
decomposition, so that the weight pieces form subcomplexes.

## Main definitions

* `Stacks.ProjectiveCohomology.piChartWeight`: the weight-`e` piece of the degree-`p` Čech
  term, on the product side.
* `Stacks.ProjectiveCohomology.piCechD`: the Čech differential of `𝒪(d)` on the product of the
  degree-`d` parts of the localizations, as an `R`-linear map.

## Main results

* `Stacks.ProjectiveCohomology.iSup_twistChartWeight_eq_top` and
  `Stacks.ProjectiveCohomology.iSupIndep_twistChartWeight`: **a Čech term is the internal
  direct sum of its Laurent weight pieces of total degree `d`.**
* `Stacks.ProjectiveCohomology.iSup_piChartWeight_eq_top` and
  `Stacks.ProjectiveCohomology.iSupIndep_piChartWeight`: **the degree-`p` Čech term is the
  internal direct sum of its Laurent weight pieces**, over the same index set.
* `Stacks.ProjectiveCohomology.cechTwistComp_cechTwistD_eq_piCechD`: the term identification
  intertwines the Čech differential with `piCechD`.
* `Stacks.ProjectiveCohomology.piCechD_piCechD`: `piCechD` squares to zero.
* `Stacks.ProjectiveCohomology.piCechD_mem_piChartWeight`: **the differential preserves each
  weight piece**, so the weight pieces are subcomplexes.

## Implementation notes

**`DirectSum.IsInternal` is NOT stated, and that is a measurement rather than an omission by
taste.** `DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top` applied to either family
below is a deterministic `isDefEq`/`whnf` timeout at 200000 heartbeats, and the heartbeat limit
is not raised in this library. The pair `iSupIndep` + `iSup = ⊤` carries exactly the same
information, and it is the form
`StacksFrontier/AlgebraicGeometry/ProjectiveCohomology/WeightSplitting.lean` itself states for
one chart, so a consumer that wants the bundled form can build it where it is cheap.

**The two `ℤ`-scalar steps of `piCechD` are Mathlib's `smul_add` and `smul_comm`, applied
directly against the goal.** `↥(twistWeightSpan R s d)` carries *two* `SMul ℤ` paths —
`AddSubgroupClass.instZSMul`, which is the one the goals below present, and
`DistribMulAction.toDistribSMul.toSMul` coming from `Module R`. They are definitionally equal,
and the expected type fixes the instances: elaborated without it, as `(smul_comm m c v :)`, the
`SMulCommClass ℤ R _` problem is stuck on a metavariable.

## References

* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
* [Stacks Project, Tag 01M6](https://stacks.math.columbia.edu/tag/01M6)
-/


@[expose] public noncomputable section


open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpectrum.Proj CategoryTheory
open CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.CategoryTheory.CechComplex
open Stacks.Cohomology.CechSheaf
open Stacks.PartialLaurent

universe u

namespace Stacks.ProjectiveCohomology

attribute [local instance] MvPolynomial.gradedAlgebra

section Decomposition

variable (R : Type u) [CommRing R] (n : ℕ) (d : ℤ)

/-- **The weight pieces of total degree `d` exhaust a Čech term.** -/
theorem iSup_twistChartWeight_eq_top {r : ℕ} (s : Fin (r + 1) → Fin (n + 1)) :
    (⨆ e : DegreeWeight n d, twistChartWeight R n d s e.1) = ⊤ := by
  refine Submodule.map_injective_of_injective (twistWeightSpan R s d).injective_subtype ?_
  rw [Submodule.map_iSup, Submodule.map_top, Submodule.range_subtype]
  refine Eq.trans ?_ (iSup_chartWeight_eq_twistWeightSpan R s d)
  refine iSup_congr fun e => ?_
  rw [twistChartWeight, Submodule.map_comap_subtype, inf_eq_right]
  exact chartWeight_le_twistWeightSpan R s d e.1 e.2

/-- **The weight pieces of total degree `d` of a Čech term are independent.** -/
theorem iSupIndep_twistChartWeight {r : ℕ} (s : Fin (r + 1) → Fin (n + 1)) :
    iSupIndep (fun e : DegreeWeight n d => twistChartWeight R n d s e.1) := by
  rw [iSupIndep_def] at *
  intro e
  refine Submodule.disjoint_def.2 fun v hv hv' => ?_
  have h := Submodule.disjoint_def.1 (iSupIndep_def.1 (iSupIndep_chartWeight R s d) e)
    (v : chartRing R s) hv
  have hmap : (⨆ e' : DegreeWeight n d, ⨆ _ : e' ≠ e, twistChartWeight R n d s e'.1) ≤
      Submodule.comap (twistWeightSpan R s d).subtype
        (⨆ e' : DegreeWeight n d, ⨆ _ : e' ≠ e, chartWeight R s e'.1) :=
    iSup₂_le fun e' he' =>
      Submodule.comap_mono (le_iSup₂_of_le e' he' le_rfl)
  exact Subtype.ext (h (hmap hv'))

/-- **The weight-`e` piece of the degree-`p` Čech term**, in the product spelling that
`Stacks.ProjectiveCohomology.cechTwistTermEquiv` identifies the term with. -/
abbrev piChartWeight (p : ℕ) (e : Fin (n + 1) →₀ ℤ) :
    Submodule R
      (∀ x : Fin (p + 1) → ULift.{u} (Fin (n + 1)), twistWeightSpan R (chartIndices x) d) :=
  Submodule.pi Set.univ fun x => twistChartWeight R n d (chartIndices x) e

/-- A family lies in the weight-`e` piece of the degree-`p` Čech term exactly when each of its
components lies in the weight-`e` part of the corresponding chart. -/
theorem mem_piChartWeight {p : ℕ} (e : Fin (n + 1) →₀ ℤ)
    {g : ∀ x : Fin (p + 1) → ULift.{u} (Fin (n + 1)), twistWeightSpan R (chartIndices x) d} :
    g ∈ piChartWeight R n d p e ↔
      ∀ x, g x ∈ twistChartWeight R n d (chartIndices x) e :=
  ⟨fun hg x => hg x trivial, fun hg x _ => hg x⟩

/-- **The weight pieces of total degree `d` exhaust the degree-`p` Čech term.** -/
theorem iSup_piChartWeight_eq_top (p : ℕ) :
    (⨆ e : DegreeWeight n d, piChartWeight R n d p e.1) = ⊤ := by
  classical
  refine le_antisymm le_top ?_
  rw [← Submodule.pi_top (Set.univ : Set (Fin (p + 1) → ULift.{u} (Fin (n + 1)))),
    ← Submodule.iSup_map_single]
  refine iSup_le fun x => ?_
  rw [← iSup_twistChartWeight_eq_top R n d (chartIndices x), Submodule.map_iSup]
  refine iSup_le fun e => le_iSup_of_le e ?_
  exact Submodule.map_le_iff_le_comap.2
    (Submodule.le_comap_single_pi fun y => twistChartWeight R n d (chartIndices y) e.1)

/-- **The weight pieces of total degree `d` of the degree-`p` Čech term are independent.** -/
theorem iSupIndep_piChartWeight (p : ℕ) :
    iSupIndep (fun e : DegreeWeight n d => piChartWeight R n d p e.1) := by
  rw [iSupIndep_def]
  intro e
  refine Submodule.disjoint_def.2 fun g hg hg' => funext fun x => ?_
  have hle : (⨆ e' : DegreeWeight n d, ⨆ _ : e' ≠ e, piChartWeight R n d p e'.1) ≤
      Submodule.comap (LinearMap.proj x)
        (⨆ e' : DegreeWeight n d, ⨆ _ : e' ≠ e,
          twistChartWeight R n d (chartIndices x) e'.1) :=
    iSup₂_le fun e' he' _ hh =>
      Submodule.mem_iSup_of_mem e'
        (Submodule.mem_iSup_of_mem he' ((mem_piChartWeight R n d e'.1).1 hh x))
  exact Submodule.disjoint_def.1
    (iSupIndep_def.1 (iSupIndep_twistChartWeight R n d (chartIndices x)) e) (g x)
    ((mem_piChartWeight R n d e).1 hg x) (hle hg')


/-! ### The differential on the product side -/

/-- The localization map on the degree-`d` parts is linear over the coefficient ring. -/
theorem chartTransitionWeight_smul {q r : ℕ} (s : Fin (r + 1) → Fin (n + 1))
    (t : Fin (q + 1) → Fin (n + 1)) (hst : Set.range s ⊆ Set.range t) (c : R)
    (z : twistWeightSpan R s d) :
    chartTransitionWeight R n d s t hst (c • z) =
      c • chartTransitionWeight R n d s t hst z :=
  Subtype.ext (chartTransition_smul R s t hst c (z : chartRing R s))

/-- **The Čech differential of `𝒪(d)`, on the product of the degree-`d` parts of the
localizations.** By `Stacks.ProjectiveCohomology.cechTwistComp_cechTwistD` this is the Čech
differential read through `Stacks.ProjectiveCohomology.cechTwistTermEquiv`. -/
def piCechD (p : ℕ) :
    (∀ x : Fin (p + 1) → ULift.{u} (Fin (n + 1)), twistWeightSpan R (chartIndices x) d) →ₗ[R]
      (∀ y : Fin (p + 2) → ULift.{u} (Fin (n + 1)), twistWeightSpan R (chartIndices y) d) where
  toFun g := fun y => ∑ a : Fin (p + 2), (-1 : ℤ) ^ (a : ℕ) •
    chartTransitionWeight R n d (chartIndices (y ∘ a.succAbove)) (chartIndices y)
      (range_chartIndices_subset n y a) (g (y ∘ a.succAbove))
  map_add' g h := funext fun y => by
    simp only [Pi.add_apply, map_add]
    refine Eq.trans (Finset.sum_congr rfl fun a _ =>
      smul_add ((-1 : ℤ) ^ (a : ℕ)) _ _) ?_
    exact Finset.sum_add_distrib
  map_smul' c g := funext fun y => by
    simp only [Pi.smul_apply, chartTransitionWeight_smul, RingHom.id_apply, Finset.smul_sum]
    exact Finset.sum_congr rfl fun a _ =>
      smul_comm ((-1 : ℤ) ^ (a : ℕ)) c _

/-- The `y`-component of `piCechD` is the alternating sum over `a` of the localizations of the
components of `g` at the faces `y ∘ a.succAbove`. -/
@[simp]
theorem piCechD_apply {p : ℕ}
    (g : ∀ x : Fin (p + 1) → ULift.{u} (Fin (n + 1)), twistWeightSpan R (chartIndices x) d)
    (y : Fin (p + 2) → ULift.{u} (Fin (n + 1))) :
    piCechD R n d p g y =
      ∑ a : Fin (p + 2), (-1 : ℤ) ^ (a : ℕ) •
        chartTransitionWeight R n d (chartIndices (y ∘ a.succAbove)) (chartIndices y)
          (range_chartIndices_subset n y a) (g (y ∘ a.succAbove)) := rfl

/-- **The term identification intertwines the two differentials.** -/
theorem cechTwistComp_cechTwistD_eq_piCechD {p : ℕ}
    (s : ToType ((cechTwistComplex R n d).X p)) :
    (fun y => cechTwistComp R n d (cechTwistD R n d s) y) =
      piCechD R n d p (fun x => cechTwistComp R n d s x) :=
  funext fun y => cechTwistComp_cechTwistD R n d s y

/-- Taking components kills the zero cochain. -/
theorem cechTwistComp_zero {p : ℕ} (x : Fin (p + 1) → ULift.{u} (Fin (n + 1))) :
    cechTwistComp R n d (0 : ToType ((cechTwistComplex R n d).X p)) x = 0 :=
  left_eq_add.1
    ((congrArg (fun t => cechTwistComp R n d t x)
        (add_zero (0 : ToType ((cechTwistComplex R n d).X p)))).symm.trans
      (cechTwistComp_add R n d (0 : ToType ((cechTwistComplex R n d).X p)) 0 x))

/-- **The differential on the product side squares to zero.** -/
theorem piCechD_piCechD (p : ℕ)
    (g : ∀ x : Fin (p + 1) → ULift.{u} (Fin (n + 1)), twistWeightSpan R (chartIndices x) d) :
    piCechD R n d (p + 1) (piCechD R n d p g) = 0 := by
  have hg : (fun x => cechTwistComp R n d (cechTwistMk R n d g) x) = g :=
    funext fun x => cechTwistComp_cechTwistMk R n d g x
  have h2 : cechTwistD R n d (cechTwistD R n d (cechTwistMk R n d g)) = 0 :=
    (ConcreteCategory.comp_apply _ _ _).symm.trans
      (ConcreteCategory.congr_hom
        ((cechTwistComplex R n d).d_comp_d p (p + 1) (p + 2)) (cechTwistMk R n d g))
  have step1 : piCechD R n d p g =
      fun y => cechTwistComp R n d (cechTwistD R n d (cechTwistMk R n d g)) y :=
    (congrArg (fun h => piCechD R n d p h) hg.symm).trans
      (cechTwistComp_cechTwistD_eq_piCechD R n d (cechTwistMk R n d g)).symm
  refine Eq.trans (congrArg (fun h => piCechD R n d (p + 1) h) step1) ?_
  refine Eq.trans (cechTwistComp_cechTwistD_eq_piCechD R n d
    (cechTwistD R n d (cechTwistMk R n d g))).symm ?_
  refine Eq.trans (congrArg (fun t => fun z => cechTwistComp R n d t z) h2) ?_
  exact funext fun z => cechTwistComp_zero R n d z

/-- **The differential preserves each Laurent weight piece**, so the weight-`e` pieces form a
subcomplex of the Čech complex. -/
theorem piCechD_mem_piChartWeight {p : ℕ} (e : Fin (n + 1) →₀ ℤ)
    {g : ∀ x : Fin (p + 1) → ULift.{u} (Fin (n + 1)), twistWeightSpan R (chartIndices x) d}
    (hg : g ∈ piChartWeight R n d p e) :
    piCechD R n d p g ∈ piChartWeight R n d (p + 1) e := by
  refine (mem_piChartWeight R n d e).2 fun y => ?_
  rw [piCechD_apply]
  refine Submodule.sum_mem _ fun a _ => Submodule.smul_of_tower_mem _ _ ?_
  exact chartTransitionWeight_mem_twistChartWeight R n d _ _
    (range_chartIndices_subset n y a) e ((mem_piChartWeight R n d e).1 hg (y ∘ a.succAbove))

end Decomposition

end Stacks.ProjectiveCohomology

end
