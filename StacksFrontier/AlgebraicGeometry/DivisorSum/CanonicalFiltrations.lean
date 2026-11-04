module

public import StacksFrontier.AlgebraicGeometry.DivisorSum.FittingGradedRank
public import StacksFrontier.AlgebraicGeometry.DivisorSum.FittingGradedRankDecr
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.FittingIdealLocalDescription

/-!
# Stacks tag 0ESU: the canonical filtrations of a module after an admissible blowup

Let `ℱ` be an `𝒪_X`-module of finite presentation on a scheme `X` which vanishes on an open
`U ⊆ X`. Stacks tag 0ESU asserts that there is a `U`-admissible blowup `b : X' → X` and effective
Cartier divisors `D_1, D_2, …` on `X'`, locally finite, such that `b^*ℱ` has two canonical
locally finite filtrations

```
0 = F⁰ ⊆ F¹ ⊆ F² ⊆ ⋯ ⊆ b^*ℱ        and        b^*ℱ = F₁ ⊇ F₂ ⊇ F₃ ⊇ ⋯ ⊇ 0,
```

whose graded pieces `Fⁱ/Fⁱ⁻¹` and `F_i/F_{i+1}` are finite locally free of rank `i` on `D_i`.

This file assembles that single statement out of the parts the directory proves, and is where the
tag is recorded.

## Main results

* `AlgebraicGeometry.exists_isAdmissibleBlowup_canonicalFiltrations`: the whole of tag 0ESU — the
  blowup, the divisors, their local finiteness, the two filtrations with their monotonicity,
  their endpoints, their local finiteness, the finite local freeness of every graded piece on its
  divisor, the canonicity of both filtrations, and the local equations.

## Implementation notes

**The filtrations are the global subsheaves of the directory, not local data.** They are
`AlgebraicGeometry.fittingIncr`, the ideal multiple `ℐ_{i+1} · b^*ℱ` of the tail
`D_{i+1} + D_{i+2} + ⋯`, and `AlgebraicGeometry.fittingDecr`, the subsheaf annihilated by the
ideal of the tail `D_i + D_{i+1} + ⋯`. Neither refers to a chart, which is what makes the
canonicity clauses — the last two conjuncts but one — true at all.

**Indexing.** `D j` is the source's `D_{j+1}`, as throughout the directory. So the increasing
graded piece between degrees `i` and `i + 1` and the decreasing one between degrees `i + 2` and
`i + 1` both live on `D i` and both have rank `i + 1`, which is the source's rank `i` on `D_i`
read at `i ↦ i + 1`.

**The graded clauses quantify over the proof of the inclusion.**
`AlgebraicGeometry.submoduleGraded` takes the inclusion of the two steps as an argument, and the
monotonicity conjuncts of the statement supply one; quantifying over every such proof rather than
naming one keeps the clause independent of which proof a consumer has in hand.

**Local finiteness of the divisors is stated twice**, once as
`Stacks.Divisors.IsLocallyFiniteFamily` — all but finitely many of the `D j` are the unit ideal on
each affine open — and once as the disjointness of the support of `D n`, for `n` large, from a
neighbourhood of a given point. The second follows from the first and is the form the source's
"locally finite" reads as.

## References

* [Stacks Project, Tag 0ESU](https://stacks.math.columbia.edu/tag/0ESU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Stacks.Divisors

universe u

namespace AlgebraicGeometry

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (F : X.Modules)

/-- **Stacks Project, Tag 0ESU.** Let `ℱ` be an `𝒪_X`-module of finite presentation vanishing on
an open `U ⊆ X`. Then there is a `U`-admissible blowup `b : X' → X` and a locally finite family of
effective Cartier divisors `D_j` on `X'` such that the pullback `b^*ℱ` has two locally finite
filtrations

```
0 = F⁰ ⊆ F¹ ⊆ ⋯ ⊆ b^*ℱ        and        b^*ℱ = F₁ ⊇ F₂ ⊇ ⋯ ⊇ 0
```

— the global subsheaves `AlgebraicGeometry.fittingIncr` and `AlgebraicGeometry.fittingDecr` of the
family — whose graded pieces are, on the divisor `D i`, the direct images of modules finite locally
free of rank `i + 1` there. Both filtrations are invariant under every automorphism of `b^*ℱ`, and
around every point an affine open with local equations `e_1, …, e_N` for the divisors describes
them as the multiples of `e_{i+1} ⋯ e_N` and the sections killed by `e_{i+1} ⋯ e_N`.

Finite presentation is more general than the source's hypothesis that `ℱ` be perfect of Tor
dimension at most one: a perfect module of Tor dimension at most one is of finite presentation,
and the conclusion here is the source's for every module of finite presentation.

In the indexing of this directory `D j` is the source's `D_{j+1}`, so the rank `i + 1` on `D i` is
the source's rank `i` on `D_i`. -/
@[stacks 0ESU "the blowup, the divisors, both canonical filtrations and every graded piece's rank"]
theorem exists_isAdmissibleBlowup_canonicalFiltrations [F.IsFinitePresentation] (U : X.Opens)
    (hzero : IsZero ((Scheme.Modules.pullback U.ι).obj F)) :
    ∃ (X' : Scheme.{u}) (b : X' ⟶ X) (_ : Stacks.Blowup.IsAdmissibleBlowup U b)
      (_ : ((Scheme.Modules.pullback b).obj F).IsQuasicoherent)
      (D : ℕ → X'.IdealSheafData),
      (∀ j, IsEffectiveCartierDivisor (D j)) ∧
      IsLocallyFiniteFamily D ∧
      (∀ x : X', ∃ V : X'.Opens, x ∈ (V : Set X') ∧ ∃ m : ℕ, ∀ n ≥ m,
        Disjoint (V : Set X') ((D n).support : Set X')) ∧
      (∀ k : ℕ, fittingIdeal ((Scheme.Modules.pullback b).obj F) (k : ℤ) =
        locallyFiniteSum D fun j => (j + 1) - k) ∧
      Monotone (fittingIncr D ((Scheme.Modules.pullback b).obj F)) ∧
      Antitone (fittingDecr D ((Scheme.Modules.pullback b).obj F)) ∧
      fittingIncr D ((Scheme.Modules.pullback b).obj F) 0 = ⊥ ∧
      fittingDecr D ((Scheme.Modules.pullback b).obj F) 1 = ⊤ ∧
      (∀ x : X', ∃ V : X'.Opens, x ∈ (V : Set X') ∧ ∃ m : ℕ, ∀ n ≥ m,
        IsZero ((Scheme.Modules.pullback V.ι).obj (cokernel (C := X'.Modules)
          (fittingIncr D ((Scheme.Modules.pullback b).obj F) n).ι))) ∧
      (∀ x : X', ∃ V : X'.Opens, x ∈ (V : Set X') ∧ ∃ m : ℕ, ∀ n ≥ m,
        IsZero ((Scheme.Modules.pullback V.ι).obj
          (fittingDecr D ((Scheme.Modules.pullback b).obj F) n).asModules)) ∧
      (∀ (i : ℕ) (hle : fittingIncr D ((Scheme.Modules.pullback b).obj F) i ≤
          fittingIncr D ((Scheme.Modules.pullback b).obj F) (i + 1)),
        ∃ G : (D i).subscheme.Modules,
          SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} G (i + 1) ∧
          Nonempty (submoduleGraded hle ≅
            (Scheme.Modules.pushforward (D i).subschemeι).obj G)) ∧
      (∀ (i : ℕ) (hle : fittingDecr D ((Scheme.Modules.pullback b).obj F) (i + 2) ≤
          fittingDecr D ((Scheme.Modules.pullback b).obj F) (i + 1)),
        ∃ G : (D i).subscheme.Modules,
          SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} G (i + 1) ∧
          Nonempty (submoduleGraded hle ≅
            (Scheme.Modules.pushforward (D i).subschemeι).obj G)) ∧
      (∀ (e : (Scheme.Modules.pullback b).obj F ≅ (Scheme.Modules.pullback b).obj F) (i : ℕ),
        Scheme.Modules.rangeSubmodule
            ((fittingIncr D ((Scheme.Modules.pullback b).obj F) i).ιModules ≫ e.hom) =
          fittingIncr D ((Scheme.Modules.pullback b).obj F) i) ∧
      (∀ (e : (Scheme.Modules.pullback b).obj F ≅ (Scheme.Modules.pullback b).obj F) (i : ℕ),
        Scheme.Modules.rangeSubmodule
            ((fittingDecr D ((Scheme.Modules.pullback b).obj F) i).ιModules ≫ e.hom) =
          fittingDecr D ((Scheme.Modules.pullback b).obj F) i) ∧
      ∀ x : X', ∃ V : X'.affineOpens, x ∈ (V.1 : Set X') ∧
        ∃ (N : ℕ) (e : ℕ → Γ(X', V.1)),
          (∀ j, j + 1 ≤ N → (D j).ideal V = Ideal.span {e (j + 1)}) ∧
          (∀ j, N ≤ j → (D j).ideal V = ⊤) ∧
          (∀ j, e j ∈ nonZeroDivisors Γ(X', V.1)) ∧
          (∀ j, N < j → IsUnit (e j)) ∧
          (∀ k : ℕ, (fittingIdeal ((Scheme.Modules.pullback b).obj F) (k : ℤ)).ideal V =
            ∏ j ∈ Finset.Icc (k + 1) N, Ideal.span {e j} ^ (j - k)) ∧
          (∀ (i : ℕ) (s : Γ((Scheme.Modules.pullback b).obj F, V.1)),
            s ∈ (fittingIncr D ((Scheme.Modules.pullback b).obj F) i).toSubmodule.obj (op V.1) ↔
              ∃ t : Γ((Scheme.Modules.pullback b).obj F, V.1),
                (∏ j ∈ Finset.Icc (i + 1) N, e j) • t = s) ∧
          (∀ (i : ℕ) (s : Γ((Scheme.Modules.pullback b).obj F, V.1)),
            s ∈ (fittingDecr D ((Scheme.Modules.pullback b).obj F)
                (i + 1)).toSubmodule.obj (op V.1) ↔
              (∏ j ∈ Finset.Icc (i + 1) N, e j) • s = 0) := by
  classical
  obtain ⟨X', b, hb, hqc, D, hDcart, hlf, hsum, hchart⟩ :=
    exists_isAdmissibleBlowup_divisors_filtrations F U hzero
  have := hqc
  have : ((Scheme.Modules.pullback b).obj F).IsFinitePresentation :=
    @Stacks.SheafOfModules.modulePullback_isFinitePresentation _ _ b.toLRSHom.toShHom F ‹_›
  have : ((Scheme.Modules.pullback b).obj F).IsFiniteType :=
    SheafOfModules.instIsFiniteTypeOfIsFinitePresentation _
  -- The chart data with the Fitting-ideal product formula, as the endpoints and the ranks want it.
  have hchart₅ : ∀ x : X', ∃ V : X'.affineOpens, x ∈ (V.1 : Set X') ∧
      ∃ (N : ℕ) (e : ℕ → Γ(X', V.1)),
        (∀ j, j + 1 ≤ N → (D j).ideal V = Ideal.span {e (j + 1)}) ∧
        (∀ j, N ≤ j → (D j).ideal V = ⊤) ∧
        (∀ j, e j ∈ nonZeroDivisors Γ(X', V.1)) ∧
        (∀ j, N < j → IsUnit (e j)) ∧
        (∀ k : ℕ, (fittingIdeal ((Scheme.Modules.pullback b).obj F) (k : ℤ)).ideal V =
          ∏ j ∈ Finset.Icc (k + 1) N, Ideal.span {e j} ^ (j - k)) := fun x => by
    obtain ⟨V, hxV, N, e, hlow, htop, hmem, hunit, hprod, -, -⟩ := hchart x
    exact ⟨V, hxV, N, e, hlow, htop, hmem, hunit, hprod⟩
  -- The two clauses of it that the local finiteness of the filtrations wants.
  have hchart₂ : ∀ x : X', ∃ V : X'.affineOpens, x ∈ (V.1 : Set X') ∧
      ∃ (N : ℕ) (e : ℕ → Γ(X', V.1)),
        (∀ j, j + 1 ≤ N → (D j).ideal V = Ideal.span {e (j + 1)}) ∧
        (∀ j, N ≤ j → (D j).ideal V = ⊤) := fun x => by
    obtain ⟨V, hxV, N, e, hlow, htop, -, -, -, -, -⟩ := hchart x
    exact ⟨V, hxV, N, e, hlow, htop⟩
  refine ⟨X', b, hb, hqc, D, hDcart, hlf, ?_, hsum, fittingIncr_mono D _,
    fittingDecr_antitone D _, fittingIncr_zero_eq_bot _ hlf hchart₅,
    fittingDecr_one_eq_top _ hlf hchart₅,
    exists_isZero_pullback_cokernel_fittingIncr _ hlf hchart₂,
    exists_isZero_pullback_fittingDecr _ hlf hDcart hchart₂,
    fun i hle => exists_isFiniteLocallyFreeOfRank_submoduleGraded_fittingIncr hlf hchart₅ i hle,
    fun i hle =>
      exists_isFiniteLocallyFreeOfRank_submoduleGraded_fittingDecr hlf hDcart hchart₅ i hle,
    fun e i => rangeSubmodule_fittingIncr_comp _ e i,
    fun e i => rangeSubmodule_fittingDecr_comp _ e i, hchart⟩
  -- Local finiteness of the family, read as disjointness of the supports from an affine open.
  intro x
  obtain ⟨V, hxV⟩ := exists_affineOpens_mem x
  obtain ⟨t, ht⟩ := hlf V
  refine ⟨V.1, hxV, t.sup id + 1, fun n hn => ?_⟩
  refine Scheme.IdealSheafData.disjoint_support_of_forall_exists_ideal_eq_top _ V.1 fun y hy => ?_
  refine ⟨V, hy, ht n fun hnt => ?_⟩
  have : n ≤ t.sup id := Finset.le_sup (f := id) hnt
  omega

end AlgebraicGeometry

end
