module

public import StacksFrontier.AlgebraicGeometry.Blowup.SecondCentre
public import StacksFrontier.AlgebraicGeometry.Blowup.StrictTransformProblem.LocalGlobal
public import StacksFrontier.AlgebraicGeometry.Blowup.SuccessiveCentre
public import StacksFrontier.AlgebraicGeometry.StrictTransform.CompositionModule

/-!
# The successive reduction of the strict-transform problem

This is the reduction of [Stacks, Tag 080Y] stated in the paragraph beginning *"The general
strategy will be to use that a composition of `U`-admissible blowups is a `U`-admissible
blowup"*: to solve the problem it suffices to find a sequence of `U`-admissible blowups
`S = S₀ ← S₁ ← … ← Sₙ` such that, setting `F₀ = F` and `X₀ = X` and taking `Fᵢ/Xᵢ` to be the
strict transform of `Fᵢ₋₁/Xᵢ₋₁`, the triple `Fₙ/Xₙ/Sₙ` has the property `P`.

Each stage of such a sequence is the problem `AlgebraicGeometry.StrictTransformProblem.transform`
of the previous one, whose distinguished open is the inverse image of the previous one, so the
sequence is exactly a chain of admissible centres for the successive transformed problems.

## Main definitions

* `AlgebraicGeometry.StrictTransformProblem.IsSolvableIn`: solvability in a prescribed number of
  admissible stages. This is the sequence `S = S₀ ← S₁ ← … ← Sₙ` of the source.

## Main results

* `AlgebraicGeometry.StrictTransformProblem.isSolvable_of_transform`: a problem whose transform
  along one admissible centre is solvable is itself solvable. This is the step that turns two
  successive stages into one.
* `AlgebraicGeometry.StrictTransformProblem.isSolvable_of_isSolvableIn`: **[Stacks, Tag 080Y],
  the successive reduction.**

## Implementation notes

**Where the two stages become one.** The two centres are amalgamated by
`Stacks.Blowup.exists_centre_of_successive`, which is [Stacks, Tag 080B] fed by the second-centre
factorization of [Stacks, Tag 0803]; the factorization is supplied by
`AlgebraicGeometry.secondCentreFactorization`, so nothing here is conditional. What comes back is
a single admissible centre `K` on `S` whose support is `Supp C ∪ b(Supp Z)` and whose blowup is
the two-step blowup over `S` — precisely the two hypotheses of [Stacks, Tag 080I]. That tag, in
the form `AlgebraicGeometry.exists_strictTransformBlowUpModule_iso_comp`, then identifies the
iterated strict transform of the triple with its strict transform in `K`, and the
isomorphism-invariance of `P` transports the property across.

**The number of stages.** `IsSolvableIn` recurses on the number of stages rather than quantifying
over a chain of schemes, which keeps every intermediate base canonical: stage `i + 1` is a centre
on the blowup produced by stage `i`. A problem presented by some other representative of that
blowup is brought into this shape by the isomorphism-invariance of `P`, which is a field of
`AlgebraicGeometry.StrictTransformProblem`.

## References

* [Stacks Project, Tag 080Y](https://stacks.math.columbia.edu/tag/080Y)
* [Stacks Project, Tag 080B](https://stacks.math.columbia.edu/tag/080B)
* [Stacks Project, Tag 080I](https://stacks.math.columbia.edu/tag/080I)
* [Stacks Project, Tag 0803](https://stacks.math.columbia.edu/tag/0803)
* [Stacks Project, Tag 080L](https://stacks.math.columbia.edu/tag/080L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

namespace StrictTransformProblem

/-! ### One admissible stage absorbs the next -/

/-- **Two successive stages of a strict-transform problem are one stage.** If `C` is a centre on
`S` of finite presentation whose support avoids `U`, and the transformed problem over the blowup
of `S` in `C` is solvable, then the original problem is solvable.

The solving centre is the amalgamation of `C` with the solving centre of the transformed problem,
by `Stacks.Blowup.exists_centre_of_successive`; the iterated strict transform is identified with
the strict transform in the amalgamated centre by [Stacks, Tag 080I]. -/
public theorem isSolvable_of_transform (D : StrictTransformProblem.{u}) (C : D.S.IdealSheafData)
    (hC : FinitePresentation C.subschemeι)
    (hCU : Disjoint (D.U : Set D.S) (C.support : Set D.S))
    (hsol : (D.transform C hC).IsSolvable) : D.IsSolvable := by
  obtain ⟨Z, hZfp, hZU, hZP⟩ := hsol
  obtain ⟨K, hKfp, hKU, hKsupp, ⟨e⟩⟩ := Stacks.Blowup.exists_centre_of_successive
    secondCentreFactorization.{u} D.U C hC hCU Z hZfp hZU
  obtain ⟨k, hk, ⟨hkF⟩⟩ := exists_strictTransformBlowUpModule_iso_comp D.f C K Z hKsupp e D.F
  refine ⟨K, hKfp, hKU, (D.p_strictTransform_iff D.f D.F K).mpr ?_⟩
  exact (D.invariant_under_iso _ _ _ _ k ((Over.forget D.S).mapIso e) hk.symm hkF).mp
    ((D.p_strictTransform_iff (strictTransformToBlowUp D.f C)
      (strictTransformBlowUpModule D.f C D.F) Z).mp hZP)

/-! ### A finite succession of admissible stages -/

/-- **Solvability of a strict-transform problem in a prescribed number of admissible stages.**
`IsSolvableIn n D` says that there is a sequence of `n` admissible centres, each on the blowup
produced by the previous one and avoiding the inverse image there of the distinguished open, after
which the iterated strict transform of the triple has the property `P`.

This is the sequence `S = S₀ ← S₁ ← … ← Sₙ` of [Stacks, Tag 080Y]: stage `i + 1` is a centre on
the base of `AlgebraicGeometry.StrictTransformProblem.transform` applied at stage `i`, and the
triple carried there is the strict transform of the triple carried at stage `i`. -/
public def IsSolvableIn : ℕ → StrictTransformProblem.{u} → Prop
  | 0 => fun D ↦ D.P D.f D.F
  | n + 1 => fun D ↦ ∃ (C : D.S.IdealSheafData) (hC : FinitePresentation C.subschemeι),
      Disjoint (D.U : Set D.S) (C.support : Set D.S) ∧ (D.transform C hC).IsSolvableIn n

/-- A sequence of no blowups solves the problem exactly when the triple already has the
property. -/
public lemma isSolvableIn_zero (D : StrictTransformProblem.{u}) :
    D.IsSolvableIn 0 ↔ D.P D.f D.F :=
  Iff.rfl

/-- A sequence of `n + 1` blowups is an admissible centre on `S` followed by a sequence of `n`
blowups for the transformed problem. -/
public lemma isSolvableIn_succ (D : StrictTransformProblem.{u}) (n : ℕ) :
    D.IsSolvableIn (n + 1) ↔ ∃ (C : D.S.IdealSheafData) (hC : FinitePresentation C.subschemeι),
      Disjoint (D.U : Set D.S) (C.support : Set D.S) ∧ (D.transform C hC).IsSolvableIn n :=
  Iff.rfl

/-- **[Stacks, Tag 080Y], the successive reduction.** To solve the strict-transform problem it
suffices to find a *sequence* of `U`-admissible blowups `S = S₀ ← S₁ ← … ← Sₙ` whose iterated
strict transform has the property `P`: such a sequence is replaced by a single `U`-admissible
blowup with the same effect.

The sequence is contracted one stage at a time: the amalgamation of [Stacks, Tag 080B], fed by
the second-centre factorization of [Stacks, Tag 0803], replaces the last two centres by a single
admissible centre on the previous base, and [Stacks, Tag 080I] identifies the iterated strict
transform with the strict transform in it. -/
@[stacks 080Y "the successive reduction, the paragraph beginning `The general strategy will be \
to use that a composition of U-admissible blowups is a U-admissible blowup': it suffices to find \
a sequence of U-admissible blowups S = S_0 <- S_1 <- ... <- S_n such that, setting F_0 = F and \
X_0 = X and F_i/X_i the strict transform of F_{i-1}/X_{i-1}, the triple F_n/X_n/S_n has P. The \
sequence is IsSolvableIn n and the single blowup it is replaced by is IsSolvable"]
public theorem isSolvable_of_isSolvableIn (n : ℕ) (D : StrictTransformProblem.{u})
    (h : D.IsSolvableIn n) : D.IsSolvable := by
  induction n generalizing D with
  | zero => exact D.isSolvable_of_property ((isSolvableIn_zero D).mp h)
  | succ n ih =>
    obtain ⟨C, hC, hCU, hrest⟩ := (isSolvableIn_succ D n).mp h
    exact D.isSolvable_of_transform C hC hCU (ih _ hrest)

end StrictTransformProblem

end AlgebraicGeometry

end
