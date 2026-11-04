module

public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import StacksCore.Tactic.StacksAttribute

/-!
# The weighted polynomial algebra `k[x, y, z]` with weights `1, 2, 3`

Let `k` be a field and grade `S = k[x, y, z]` by giving `x`, `y` and `z` the degrees `1`, `2`
and `3`. This file sets up that graded algebra, its degree-zero localization `S₍z₎` at `z`, the
three distinguished fractions

`u = x³/z`,  `v = xy/z`,  `w = y³/z²`

of `S₍z₎`, the ideal they generate, and the internal gradings of the twists `S(t)` of the
regular module.

## Main definitions

* `Stacks.WeightedPolynomialSituation`: a ground field, packaging the example.
* `Stacks.WeightedPolynomialSituation.S`: the polynomial ring `k[x, y, z]`.
* `Stacks.WeightedPolynomialSituation.weight` and
  `Stacks.WeightedPolynomialSituation.naturalWeight`: the weights `1, 2, 3` of the variables,
  as integers and as naturals.
* `Stacks.WeightedPolynomialSituation.grading` and
  `Stacks.WeightedPolynomialSituation.naturalGrading`: the weighted homogeneous pieces of `S`,
  indexed by `ℤ` and by `ℕ`.
* `Stacks.WeightedPolynomialSituation.x`, `y`, `z`: the three variables.
* `Stacks.WeightedPolynomialSituation.R`: the degree-zero localization `S₍z₎`, and
  `Stacks.WeightedPolynomialSituation.ordinaryLocalization`: the ordinary localization `S_z`.
* `Stacks.WeightedPolynomialSituation.twistGrading`: the internal grading of the twist `S(t)`,
  with `firstTwistGrading` and `secondTwistGrading` the cases `t = 1, 2`.
* `Stacks.WeightedPolynomialSituation.u`, `v`, `w`: the fractions `x³/z`, `xy/z`, `y³/z²`.
* `Stacks.WeightedPolynomialSituation.vertexIdeal`: the ideal `(u, v, w)` of `S₍z₎`.

## Implementation notes

The variables are indexed by `Fin 3` and the weight of the `i`-th is `i + 1`. Two gradings are
carried, by `ℕ` and by `ℤ`, because they serve different purposes: Mathlib's homogeneous
localization needs a nonnegative grading, while the twists `S(t)` are graded by `ℤ`. Both are
`MvPolynomial.weightedHomogeneousSubmodule` for the corresponding weight function, so they
agree in nonnegative degrees; `mem_grading_of_mem_naturalGrading` is that comparison.

Every twist `S(t)` has the same underlying `S`-module, namely `S` with its regular action; only
the grading changes, the degree-`n` piece of `S(t)` being `S_{n + t}`. Accordingly `twistGrading`
is a reindexing of `grading`, and its `DirectSum.Decomposition` is obtained by transporting the
decomposition of `S` along the bijection `n ↦ n + t` of `ℤ`. The `SetLike.GradedSMul` instance
records that the nonnegatively graded ring acts on each shifted grading, which is what the
graded-module APIs require.

## References

* [Stacks Project, Tag 01ML](https://stacks.math.columbia.edu/tag/01ML)
-/

@[expose] public noncomputable section

universe u

namespace Stacks

/-- A field over which the weighted polynomial example `k[x, y, z]`, with weights `1`, `2`, `3`,
is formed. -/
public structure WeightedPolynomialSituation where
  /-- The ground field. -/
  k : Type u
  /-- The field structure on the ground field. -/
  [field : Field k]

attribute [instance] WeightedPolynomialSituation.field

namespace WeightedPolynomialSituation

/-- A nonnegative ring degree acts on an integer module degree by addition. Mathlib has no
`VAdd ℕ ℤ` instance and `SetLike.GradedSMul` for an `ℕ`-graded ring acting on a `ℤ`-graded
module needs one; it is file-local here, as in
`StacksFrontier/AlgebraicGeometry/Constructions/ProjTwist.lean`. -/
local instance instVAddNatInt : VAdd ℕ ℤ where
  vadd n z := (n : ℤ) + z

/-- The polynomial ring `k[x, y, z]`. -/
public abbrev S (E : WeightedPolynomialSituation) := MvPolynomial (Fin 3) E.k

/-- The weights `1`, `2`, and `3` of `x`, `y`, and `z`. -/
public def weight (_E : WeightedPolynomialSituation) : Fin 3 → ℤ :=
  fun i ↦ (i : ℤ) + 1

/-- The nonnegative weights of the variables. -/
public def naturalWeight (_E : WeightedPolynomialSituation) : Fin 3 → ℕ :=
  fun i ↦ (i : ℕ) + 1

/-- The natural-number grading used by homogeneous localization. -/
public abbrev naturalGrading (E : WeightedPolynomialSituation) : ℕ → Submodule E.k E.S :=
  MvPolynomial.weightedHomogeneousSubmodule E.k E.naturalWeight

/-- The canonical graded-algebra structure on the nonnegative grading. -/
public instance naturalGradingGradedAlgebra (E : WeightedPolynomialSituation) :
    GradedAlgebra E.naturalGrading :=
  MvPolynomial.weightedGradedAlgebra E.k E.naturalWeight

/-- The weighted homogeneous pieces of `k[x, y, z]`. -/
public abbrev grading (E : WeightedPolynomialSituation) : ℤ → Submodule E.k E.S :=
  MvPolynomial.weightedHomogeneousSubmodule E.k E.weight

/-- The canonical graded-algebra structure on the weighted homogeneous pieces. -/
public instance gradingGradedAlgebra (E : WeightedPolynomialSituation) :
    GradedAlgebra E.grading :=
  MvPolynomial.weightedGradedAlgebra E.k E.weight

/-- The variable `x`, of weight one. -/
public abbrev x (E : WeightedPolynomialSituation) : E.S := MvPolynomial.X 0

/-- The variable `y`, of weight two. -/
public abbrev y (E : WeightedPolynomialSituation) : E.S := MvPolynomial.X 1

/-- The variable `z`, of weight three. -/
public abbrev z (E : WeightedPolynomialSituation) : E.S := MvPolynomial.X 2

/-- The degree-zero homogeneous localization `S₍z₎`. -/
public abbrev R (E : WeightedPolynomialSituation) :=
  HomogeneousLocalization.Away E.naturalGrading E.z

/-- The canonical ground-field algebra structure on the degree-zero localization. -/
public noncomputable instance algebraR (E : WeightedPolynomialSituation) : Algebra E.k E.R :=
  ((algebraMap (E.naturalGrading 0) E.R).comp
    (algebraMap E.k (E.naturalGrading 0))).toAlgebra

/-- The ordinary localization `S_z`. -/
public abbrev ordinaryLocalization (E : WeightedPolynomialSituation) :=
  Localization.Away E.z

/-- The internal integer grading of the twist `S(t)`, whose degree-`n` piece is `S_{n + t}`.
The underlying `S`-module of every twist is `S` with its regular action. -/
public abbrev twistGrading (E : WeightedPolynomialSituation) (t : ℤ) :
    ℤ → Submodule E.k E.S :=
  fun n ↦ E.grading (n + t)

/-- Reindexing the weighted decomposition gives the grading on each twist. -/
public noncomputable instance twistGradingDecomposition (E : WeightedPolynomialSituation)
    (t : ℤ) : DirectSum.Decomposition (E.twistGrading t) := by
  let e : ℤ ≃ ℤ := Equiv.addRight t
  refine (?_ : DirectSum.IsInternal (E.grading ∘ e)).chooseDecomposition
  have h0 := DirectSum.Decomposition.isInternal E.grading
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top] at h0 ⊢
  exact ⟨h0.1.comp e.injective, (e.iSup_comp (g := E.grading)).trans h0.2⟩

/-- The integer weight is the image of the nonnegative weight. -/
private theorem weight_eq_intCast (E : WeightedPolynomialSituation) (d : Fin 3 →₀ ℕ) :
    (Finsupp.weight E.naturalWeight d : ℤ) = Finsupp.weight E.weight d := by
  simp [Finsupp.weight_apply, Finsupp.sum, naturalWeight, weight]

/-- A naturally weighted homogeneous polynomial has the same integer weight. -/
private theorem mem_grading_of_mem_naturalGrading (E : WeightedPolynomialSituation) (n : ℕ)
    (a : E.S) (ha : a ∈ E.naturalGrading n) : a ∈ E.grading (n : ℤ) := by
  intro d hd
  rw [← E.weight_eq_intCast d]
  exact congrArg (fun q : ℕ => (q : ℤ)) (ha hd)

/-- The natural weighted grading acts compatibly on every shifted integer grading. -/
public instance twistGradingGradedSMul (E : WeightedPolynomialSituation) (t : ℤ) :
    SetLike.GradedSMul E.naturalGrading (E.twistGrading t) := by
  refine ⟨?_⟩
  intro i j a b ha hb
  have ha' := E.mem_grading_of_mem_naturalGrading i a ha
  change a * b ∈ E.grading ((i : ℤ) + j + t)
  change MvPolynomial.IsWeightedHomogeneous E.weight (a * b) ((i : ℤ) + j + t)
  simpa only [twistGrading, add_assoc] using MvPolynomial.IsWeightedHomogeneous.mul ha' hb

/-- The internal grading of `M = S(1)` on the regular `S`-module. -/
public abbrev firstTwistGrading (E : WeightedPolynomialSituation) : ℤ → Submodule E.k E.S :=
  E.twistGrading 1

/-- The internal grading of `N = S(2)` on the regular `S`-module. -/
public abbrev secondTwistGrading (E : WeightedPolynomialSituation) : ℤ → Submodule E.k E.S :=
  E.twistGrading 2

/-- The element `u = x³/z` of `S₍z₎`. -/
public def u (E : WeightedPolynomialSituation) : E.R :=
  HomogeneousLocalization.Away.mk E.naturalGrading
    (MvPolynomial.isWeightedHomogeneous_X E.k E.naturalWeight 2) 1 (E.x ^ 3)
    (by
      change MvPolynomial.IsWeightedHomogeneous E.naturalWeight (E.x ^ 3)
        (1 • E.naturalWeight 2)
      simpa [naturalWeight] using
        (MvPolynomial.isWeightedHomogeneous_X E.k E.naturalWeight 0).pow 3)

/-- The element `v = xy/z` of `S₍z₎`. -/
public def v (E : WeightedPolynomialSituation) : E.R :=
  HomogeneousLocalization.Away.mk E.naturalGrading
    (MvPolynomial.isWeightedHomogeneous_X E.k E.naturalWeight 2) 1 (E.x * E.y)
    (by
      change MvPolynomial.IsWeightedHomogeneous E.naturalWeight (E.x * E.y)
        (1 • E.naturalWeight 2)
      simpa [naturalWeight] using
        (MvPolynomial.isWeightedHomogeneous_X E.k E.naturalWeight 0).mul
          (MvPolynomial.isWeightedHomogeneous_X E.k E.naturalWeight 1))

/-- The element `w = y³/z²` of `S₍z₎`. -/
public def w (E : WeightedPolynomialSituation) : E.R :=
  HomogeneousLocalization.Away.mk E.naturalGrading
    (MvPolynomial.isWeightedHomogeneous_X E.k E.naturalWeight 2) 2 (E.y ^ 3)
    (by
      change MvPolynomial.IsWeightedHomogeneous E.naturalWeight (E.y ^ 3)
        (2 • E.naturalWeight 2)
      simpa [naturalWeight] using
        (MvPolynomial.isWeightedHomogeneous_X E.k E.naturalWeight 1).pow 3)

/-- The ideal `(u, v, w)` of `S₍z₎`. -/
public def vertexIdeal (E : WeightedPolynomialSituation) : Ideal E.R :=
  Ideal.span ({E.u, E.v, E.w} : Set E.R)

end WeightedPolynomialSituation

end Stacks

end
