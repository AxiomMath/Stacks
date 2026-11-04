module

public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Coherent
public import StacksFrontier.AlgebraicGeometry.DivisorSum.FittingFiltrationsCanonical
public import StacksFrontier.AlgebraicGeometry.DivisorSum.FittingGradedPieces
public import StacksFrontier.AlgebraicGeometry.Scheme.AffineOpenNeighborhood
public import StacksFrontier.RingTheory.Fitting.GlobalGradedPieces

/-!
# The graded pieces of 0ESU's two filtrations live on the divisors

Stacks tag 0ESU asserts that the graded pieces `Fⁱ⁺¹/Fⁱ` and `F_{i+1}/F_{i+2}` of the two
filtrations of `ℱ` are modules *on the divisor* `D_{i+1}`, not merely on the ambient scheme. This
file proves that for both, in the two equivalent forms the rest of the library consumes.

The mathematics is one line once the local description of the filtration is available. Over an
affine open `V` carrying local equations `e_1, …, e_N` for the divisors the sections of the
increasing graded piece are the ring-level graded piece
`Stacks.FittingFiltration.gradedQuot (incr Γ(ℱ, V) e N i) (incr Γ(ℱ, V) e N (i + 1))`, by
`AlgebraicGeometry.sectionsSubmodule_fittingIncr` and
`AlgebraicGeometry.submoduleGradedSectionsEquiv`, and
`Stacks.FittingFiltration.isTorsionBySet_gradedQuot_incr` says that is killed by `(e_{i+1})` —
which is exactly `(D i).ideal V`, the ideal of the divisor whose index matches the graded degree.
Past the last divisor, where `(D i).ideal V = ⊤` and no equation is available, both steps of the
filtration are already all of `Γ(ℱ, V)`, so the graded piece has one element and is killed by
everything.

The decreasing filtration is the same argument with
`AlgebraicGeometry.sectionsSubmodule_fittingDecr` and
`Stacks.FittingFiltration.isTorsionBySet_gradedQuot_decr` in place of their twins: its graded
piece in degree `i` is `F_{i+1}/F_{i+2}`, the steps being antitone, and the degenerate degrees
are those where both steps have already reached zero
(`Stacks.FittingFiltration.decr_eq_bot`) rather than the whole module.

## Main results

* `AlgebraicGeometry.annihilatedByKer_submoduleGraded_fittingIncr` and
  `AlgebraicGeometry.annihilatedByKer_submoduleGraded_fittingDecr`: the graded pieces
  `Fⁱ⁺¹/Fⁱ` and `F_{i+1}/F_{i+2}` are annihilated by the ideal sheaf cutting out `D i`.
* `AlgebraicGeometry.essImage_pushforward_submoduleGraded_fittingIncr` and
  `AlgebraicGeometry.essImage_pushforward_submoduleGraded_fittingDecr`: therefore each is the
  direct image along `(D i).subschemeι` of a module on that divisor — the descent asserted by
  the source. Their rank on the divisor, the other half of the source's clause, is
  `AlgebraicGeometry.exists_isFiniteLocallyFreeOfRank_submoduleGraded_fittingDecr` of
  `StacksFrontier.AlgebraicGeometry.DivisorSum.FittingGradedRankDecr`.

## Implementation notes

The three ring-level lemmas below are the transport of
`Stacks.FittingFiltration.isTorsionBySet_gradedQuot_incr`,
`Stacks.FittingFiltration.isTorsionBySet_gradedQuot_decr` and
`Stacks.FittingFiltration.subsingleton_gradedQuot_self` along an *equality of submodules*.
`Stacks.FittingFiltration.gradedQuot` takes the two submodules as arguments, so the sections of
the sheaf-level graded piece are a `gradedQuot` of the submodules of sections rather than of the
local filtration steps; the two are equal, but the equality has to be substituted into a type,
and these statements are where that substitution happens once and for all. The one for the
degenerate degrees serves both filtrations.

The effective-Cartier hypothesis appears in the decreasing results and not in the increasing
ones: a step of the decreasing filtration is an annihilator subsheaf, and its quasi-coherence
(`AlgebraicGeometry.isQuasicoherent_fittingDecr`) needs the ideal sheaf of the divisor tail to be
of finite type, which is `AlgebraicGeometry.isFiniteType_idealSubsheaf_divisorTail`.

**The chart hypothesis is the per-point one, not one for every affine open.** The ideal of an
effective Cartier divisor is principal near every point but need not be principal on a *given*
affine open, so the producer of the divisors,
`AlgebraicGeometry.exists_isAdmissibleBlowup_divisors_filtrations`, supplies local equations only
around every point. Annihilation is nevertheless sheaf-local, so it is enough to test it on a
cofinal family of affine opens — which is
`Stacks.ClosedImmersion.annihilatedByKer_of_forall_exists_affineOpen` — and the chart data of a
point restricts to any affine open around it by the shrinking step
`AlgebraicGeometry.exists_forall_ideal_eq_span_and_eq_top_of_le`, these two clauses restricting
along `AlgebraicGeometry.Scheme.IdealSheafData.map_ideal` with no flatness involved. The kernel
ideal sheaf there is identified with `D i` itself by Mathlib's
`AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι`. The descent is then
`Stacks.ClosedImmersion.pushforward_essImage_iff`, whose right-hand side is literally the
annihilation condition, so the second result carries no mathematics beyond the first.

## References

* [Stacks Project, Tag 0ESU](https://stacks.math.columbia.edu/tag/0ESU)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
-/

@[expose] public noncomputable section

universe u v

namespace Stacks.FittingFiltration

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- **A graded piece of the increasing filtration is killed by the equation of its divisor,
stated for submodules merely *equal* to the two filtration steps.** This is
`Stacks.FittingFiltration.isTorsionBySet_gradedQuot_incr` with the two equalities substituted
into the type of the graded piece, which is what a consumer holding the sections of a sheaf-level
graded piece needs: those sections are a `gradedQuot` of the submodules of sections, and only an
equation identifies them with the local filtration steps. -/
theorem smul_eq_zero_of_mem_span_gradedQuot_incr {N P : _root_.Submodule R M} {e : ℕ → R}
    {n i : ℕ} (hN : N = incr M e n i) (hP : P = incr M e n (i + 1)) {a : R}
    (ha : a ∈ Ideal.span {e (i + 1)}) (x : gradedQuot N P) : a • x = 0 := by
  subst hN
  subst hP
  exact isTorsionBySet_gradedQuot_incr (M := M) e n i (x := x) (a := ⟨a, ha⟩)

/-- **A graded piece of the decreasing filtration is killed by the equation of its divisor,
stated for submodules merely *equal* to the two filtration steps.** This is
`Stacks.FittingFiltration.isTorsionBySet_gradedQuot_decr` with the two equalities substituted
into the type of the graded piece, the twin of
`Stacks.FittingFiltration.smul_eq_zero_of_mem_span_gradedQuot_incr`. Note the indexing: the
graded piece of the decreasing filtration in degree `i` is `F_{i+1}/F_{i+2}`, so the smaller
submodule is the later step. -/
theorem smul_eq_zero_of_mem_span_gradedQuot_decr {N P : _root_.Submodule R M} {e : ℕ → R}
    {n i : ℕ} (hN : N = decr M e n (i + 2)) (hP : P = decr M e n (i + 1)) {a : R}
    (ha : a ∈ Ideal.span {e (i + 1)}) (x : gradedQuot N P) : a • x = 0 := by
  subst hN
  subst hP
  exact isTorsionBySet_gradedQuot_decr (M := M) e n i (x := x) (a := ⟨a, ha⟩)

/-- **A graded piece of a pair of equal submodules is killed by every scalar**: it has one
element, by `Stacks.FittingFiltration.subsingleton_gradedQuot_self`. This is the degenerate
degrees of either filtration, where the two steps have already met — the increasing one at the
whole module, the decreasing one at zero — and the divisor contributing the equation is empty. -/
theorem smul_eq_zero_of_eq_gradedQuot {N P : _root_.Submodule R M} (h : N = P) (a : R)
    (x : gradedQuot N P) : a • x = 0 := by
  subst h
  have := subsingleton_gradedQuot_self N
  rw [Subsingleton.elim x 0, smul_zero]

end Stacks.FittingFiltration

namespace AlgebraicGeometry

open CategoryTheory Opposite Stacks.Divisors Stacks.FittingFiltration

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {F : X.Modules}

/-- **The graded piece of 0ESU's increasing filtration is annihilated by the ideal sheaf of its
divisor.** On an affine open carrying local equations the sections of `Fⁱ⁺¹/Fⁱ` are the ring-level
graded piece of `Stacks.FittingFiltration.incr` in degrees `i` and `i + 1`, which
`Stacks.FittingFiltration.isTorsionBySet_gradedQuot_incr` kills by `(e_{i+1}) = (D i).ideal V`.

Note the index: the divisor is `D i`, the source's `D_{i+1}`, and not the tail `D_{i+1} + ⋯` that
defines the step `Fⁱ`. -/
theorem annihilatedByKer_submoduleGraded_fittingIncr [F.IsQuasicoherent]
    {D : ℕ → X.IdealSheafData} (hD : IsLocallyFiniteFamily D)
    (hchart : ∀ x : X, ∃ V : X.affineOpens, x ∈ (V.1 : Set X) ∧ ∃ (N : ℕ) (e : ℕ → Γ(X, V.1)),
      (∀ j, j + 1 ≤ N → (D j).ideal V = Ideal.span {e (j + 1)}) ∧
      (∀ j, N ≤ j → (D j).ideal V = ⊤))
    (i : ℕ) (hle : fittingIncr D F i ≤ fittingIncr D F (i + 1)) :
    Stacks.ClosedImmersion.AnnihilatedByKer (D i).subschemeι (submoduleGraded hle) := by
  have := isQuasicoherent_fittingIncr D F i
  have := isQuasicoherent_fittingIncr D F (i + 1)
  refine Stacks.ClosedImmersion.annihilatedByKer_of_forall_exists_affineOpen _ _
    fun B x hxB => ?_
  obtain ⟨V, hxV, N, e, hlow, htop⟩ := hchart x
  obtain ⟨W, hxW, hWle⟩ := exists_affineOpen_mem_le x (B ⊓ V.1) ⟨hxB, hxV⟩
  obtain ⟨e', hlow', htop'⟩ :=
    exists_forall_ideal_eq_span_and_eq_top_of_le hlow htop (hWle.trans inf_le_right)
  refine ⟨W, hWle.trans inf_le_left, hxW, fun a ha m => ?_⟩
  rw [Scheme.IdealSheafData.ker_subschemeι] at ha
  have h1 := sectionsSubmodule_fittingIncr (F := F) hD W hlow' htop' i
  have h2 := sectionsSubmodule_fittingIncr (F := F) hD W hlow' htop' (i + 1)
  set E := submoduleGradedSectionsEquiv hle W
  have hz : a • E.symm m = 0 := by
    rcases le_or_gt (i + 1) N with hi | hi
    · refine smul_eq_zero_of_mem_span_gradedQuot_incr h1 h2 ?_ _
      rw [← hlow' i hi]
      exact ha
    · refine smul_eq_zero_of_eq_gradedQuot ?_ a _
      rw [h1, h2, incr_eq_top e' (by omega : N ≤ i), incr_eq_top e' (by omega : N ≤ i + 1)]
  calc a • m = a • E (E.symm m) := by rw [E.apply_symm_apply]
    _ = E (a • E.symm m) := (map_smul E a _).symm
    _ = 0 := by rw [hz, map_zero]

/-- **The graded piece of 0ESU's increasing filtration descends to its divisor.** It is the
direct image along `(D i).subschemeι` of a sheaf of modules on the closed subscheme cut out by
`D i`, which is the source's assertion that `Fⁱ⁺¹/Fⁱ` is a module on `D_{i+1}`.

This is `Stacks.ClosedImmersion.pushforward_essImage_iff` applied to
`AlgebraicGeometry.annihilatedByKer_submoduleGraded_fittingIncr`: the essential image of direct
image along a closed immersion is cut out by exactly that annihilation condition. -/
theorem essImage_pushforward_submoduleGraded_fittingIncr [F.IsQuasicoherent]
    {D : ℕ → X.IdealSheafData} (hD : IsLocallyFiniteFamily D)
    (hchart : ∀ x : X, ∃ V : X.affineOpens, x ∈ (V.1 : Set X) ∧ ∃ (N : ℕ) (e : ℕ → Γ(X, V.1)),
      (∀ j, j + 1 ≤ N → (D j).ideal V = Ideal.span {e (j + 1)}) ∧
      (∀ j, N ≤ j → (D j).ideal V = ⊤))
    (i : ℕ) (hle : fittingIncr D F i ≤ fittingIncr D F (i + 1)) :
    (Scheme.Modules.pushforward (D i).subschemeι).essImage (submoduleGraded hle) :=
  (Stacks.ClosedImmersion.pushforward_essImage_iff _ _).mpr
    (annihilatedByKer_submoduleGraded_fittingIncr hD hchart i hle)

/-- **The graded piece of 0ESU's decreasing filtration is annihilated by the ideal sheaf of its
divisor.** On an affine open carrying local equations the sections of `F_{i+1}/F_{i+2}` are the
ring-level graded piece of `Stacks.FittingFiltration.decr` in degrees `i + 2` and `i + 1`, which
`Stacks.FittingFiltration.isTorsionBySet_gradedQuot_decr` kills by `(e_{i+1}) = (D i).ideal V`.

The index is the one of the increasing twin: the divisor is `D i`, the source's `D_{i+1}`, whose
equation `e_{i+1}` is the factor by which the two consecutive kernels differ. Past the last
divisor both steps are already zero, by `Stacks.FittingFiltration.decr_eq_bot`, so the graded
piece has one element and is killed by everything.

The effective-Cartier hypothesis is not needed by the increasing twin and is needed here: the
decreasing filtration is an annihilator subsheaf, whose quasi-coherence
(`AlgebraicGeometry.isQuasicoherent_fittingDecr`) rests on the ideal sheaf of the divisor tail
being of finite type. -/
theorem annihilatedByKer_submoduleGraded_fittingDecr [F.IsQuasicoherent]
    {D : ℕ → X.IdealSheafData} (hD : IsLocallyFiniteFamily D)
    (hDcart : ∀ j, IsEffectiveCartierDivisor (D j))
    (hchart : ∀ x : X, ∃ V : X.affineOpens, x ∈ (V.1 : Set X) ∧ ∃ (N : ℕ) (e : ℕ → Γ(X, V.1)),
      (∀ j, j + 1 ≤ N → (D j).ideal V = Ideal.span {e (j + 1)}) ∧
      (∀ j, N ≤ j → (D j).ideal V = ⊤))
    (i : ℕ) (hle : fittingDecr D F (i + 2) ≤ fittingDecr D F (i + 1)) :
    Stacks.ClosedImmersion.AnnihilatedByKer (D i).subschemeι (submoduleGraded hle) := by
  have := isQuasicoherent_fittingDecr_of_isEffectiveCartierDivisor D F hD hDcart (i + 2)
  have := isQuasicoherent_fittingDecr_of_isEffectiveCartierDivisor D F hD hDcart (i + 1)
  refine Stacks.ClosedImmersion.annihilatedByKer_of_forall_exists_affineOpen _ _
    fun B x hxB => ?_
  obtain ⟨V, hxV, N, e, hlow, htop⟩ := hchart x
  obtain ⟨W, hxW, hWle⟩ := exists_affineOpen_mem_le x (B ⊓ V.1) ⟨hxB, hxV⟩
  obtain ⟨e', hlow', htop'⟩ :=
    exists_forall_ideal_eq_span_and_eq_top_of_le hlow htop (hWle.trans inf_le_right)
  refine ⟨W, hWle.trans inf_le_left, hxW, fun a ha m => ?_⟩
  rw [Scheme.IdealSheafData.ker_subschemeι] at ha
  have h1 := sectionsSubmodule_fittingDecr (F := F) hD W hlow' htop' (i + 1)
  have h2 := sectionsSubmodule_fittingDecr (F := F) hD W hlow' htop' i
  set E := submoduleGradedSectionsEquiv hle W
  have hz : a • E.symm m = 0 := by
    rcases le_or_gt (i + 1) N with hi | hi
    · refine smul_eq_zero_of_mem_span_gradedQuot_decr h1 h2 ?_ _
      rw [← hlow' i hi]
      exact ha
    · refine smul_eq_zero_of_eq_gradedQuot ?_ a _
      rw [h1, h2, decr_eq_bot e' (by omega : N < i + 2), decr_eq_bot e' (by omega : N < i + 1)]
  calc a • m = a • E (E.symm m) := by rw [E.apply_symm_apply]
    _ = E (a • E.symm m) := (map_smul E a _).symm
    _ = 0 := by rw [hz, map_zero]

/-- **The graded piece of 0ESU's decreasing filtration descends to its divisor.** It is the
direct image along `(D i).subschemeι` of a sheaf of modules on the closed subscheme cut out by
`D i`, which is the source's assertion that `F_{i+1}/F_{i+2}` is a module on `D_{i+1}`.

This is `Stacks.ClosedImmersion.pushforward_essImage_iff` applied to
`AlgebraicGeometry.annihilatedByKer_submoduleGraded_fittingDecr`, the twin of
`AlgebraicGeometry.essImage_pushforward_submoduleGraded_fittingIncr`. -/
theorem essImage_pushforward_submoduleGraded_fittingDecr [F.IsQuasicoherent]
    {D : ℕ → X.IdealSheafData} (hD : IsLocallyFiniteFamily D)
    (hDcart : ∀ j, IsEffectiveCartierDivisor (D j))
    (hchart : ∀ x : X, ∃ V : X.affineOpens, x ∈ (V.1 : Set X) ∧ ∃ (N : ℕ) (e : ℕ → Γ(X, V.1)),
      (∀ j, j + 1 ≤ N → (D j).ideal V = Ideal.span {e (j + 1)}) ∧
      (∀ j, N ≤ j → (D j).ideal V = ⊤))
    (i : ℕ) (hle : fittingDecr D F (i + 2) ≤ fittingDecr D F (i + 1)) :
    (Scheme.Modules.pushforward (D i).subschemeι).essImage (submoduleGraded hle) :=
  (Stacks.ClosedImmersion.pushforward_essImage_iff _ _).mpr
    (annihilatedByKer_submoduleGraded_fittingDecr hD hDcart hchart i hle)

end AlgebraicGeometry

end
