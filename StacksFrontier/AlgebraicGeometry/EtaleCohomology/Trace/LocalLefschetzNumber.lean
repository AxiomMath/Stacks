module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.FilteredDerived.Perfectness.Trace

/-!
# The local Lefschetz number

Let `Λ` be a finite ring, `X` a projective curve over a finite field `k` and `K` an object of
`D_ctf(X, Λ)`. For a geometric point `x̄` of `X` the stalk `K_x̄` is a perfect complex of
`Λ`-modules and the Frobenius `π_x` acts on it, so it has a trace in the additive commutator
quotient `Λ^natural`. The local Lefschetz number of `K` is the sum of those traces over the
`k`-rational points of `X`.

## Main definitions

* `Stacks.EtaleCohomology.FrobeniusActionOnStalks` — the datum the definition operates on: a
  perfect object of `D(Λ)` with an endomorphism for each rational point.
* `Stacks.EtaleCohomology.localLefschetzNumber` — the local Lefschetz number.

## Main results

* `Stacks.EtaleCohomology.localLefschetzNumber_eq_sum_alternatingTrace` — the local Lefschetz
  number is the sum over the rational points of the alternating sums of the traces of any
  cochain endomorphisms representing the Frobenius actions on any bounded finite-projective
  representatives of the stalks.
* `Stacks.EtaleCohomology.localLefschetzNumber_of_isEmpty` and
  `Stacks.EtaleCohomology.localLefschetzNumber_unique` — the values on no rational points and
  on a single rational point.

## Implementation notes

The coefficient ring is an arbitrary, possibly noncommutative, finite ring, as in the source:
the traces in play are those of `CategoryTheory.FilteredDerived.perfectDerivedTrace`, valued in
`Λ^natural`, and `Λ^natural` is a proper quotient of `Λ` exactly when `Λ` is noncommutative. No
commutativity hypothesis enters anywhere.

The geometric input enters only where the source uses it. The set `X(k)` of rational points is
a finite index type, and for each of its elements the perfect complex `K_x̄` and the action
`π_x` on it are taken as data, matching the treatment of `RΓ(X_k̄, K|_{X_k̄})` and `π_X^*` in
`Stacks.EtaleCohomology.FrobeniusActionOnCohomology`. So the projectivity of `X`, its
dimension, and the constructibility and finite Tor dimension of `K` — hypotheses the definition
itself does not need, only its well-posedness does — are not imposed. The ring, module and
point universes are independent.

[Stacks, Tag 03TY] itself, in which the index type is the set `X(k)` of `k`-rational points of
an actual scheme over an actual finite field, the stalks are the derived étale stalks of an
object of `D_ctf(X_étale, Λ)` at the geometric points above them, the endomorphisms are the
geometric Frobenius of [Stacks, Tag 03SW], and perfection of the stalks is *derived* rather than
given, is `Stacks.EtaleCohomology.localLefschetzNumberOfCtf` in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Trace/LocalLefschetzNumberConstructibleFlat.lean`.

## References

* [Stacks Project, Tag 03TY](https://stacks.math.columbia.edu/tag/03TY)
* [Stacks Project, Tag 03TX](https://stacks.math.columbia.edu/tag/03TX)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v w

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-- The datum underlying the local Lefschetz number: for each `k`-rational point `x` of `X`
the perfect complex `K_x̄` of `Λ`-modules together with the Frobenius action `π_x` on it.

See [Stacks Project, Tag 03TY](https://stacks.math.columbia.edu/tag/03TY). -/
public structure FrobeniusActionOnStalks.{u', v', w'} (Λ : Type u') [Ring Λ] [Finite Λ]
    (points : Type w') where
  /-- The stalk `K_x̄` at the geometric point above `x`. -/
  stalk : points → CategoryTheory.FilteredDerived.PerfectDerivedCategory.{u', v'} Λ
  /-- The Frobenius action `π_x` on `K_x̄`. -/
  frobeniusAction : (x : points) → (stalk x).obj ⟶ (stalk x).obj

/-- The local Lefschetz number of `K`: the sum over the `k`-rational points `x` of `X` of the
trace of the Frobenius action `π_x` on the perfect complex `K_x̄`, an element of the additive
commutator quotient `Λ^natural`.

This is the shape of the sum alone: the ring is an arbitrary finite, possibly noncommutative,
ring and the perfect complexes `K_x̄` with their endomorphisms `π_x` are arbitrary data.  The
definition of [Stacks, Tag 03TY] is `Stacks.EtaleCohomology.localLefschetzNumberOfCtf`, in which
`X(k)`, the stalks `K_x̄` and the Frobenius actions `π_x` are computed from an object of
`D_ctf(X_étale, Λ)` on a scheme over a finite field and perfection of the stalks is *proved*
rather than given.

See [Stacks Project, Tag 03TY](https://stacks.math.columbia.edu/tag/03TY). -/
public def localLefschetzNumber (Λ : Type u) [Ring Λ] [Finite Λ]
    (points : Type w) [Fintype points] (D : FrobeniusActionOnStalks.{u, v, w} Λ points) :
    CategoryTheory.FilteredDerived.AdditiveCommutatorQuotient Λ :=
  ∑ x : points, CategoryTheory.FilteredDerived.perfectDerivedTrace Λ (D.stalk x)
    (D.frobeniusAction x)

/-- The local Lefschetz number is the sum over the rational points of the alternating sums of
the traces of any cochain endomorphisms representing the Frobenius actions on any bounded
finite-projective representatives of the stalks. -/
public theorem localLefschetzNumber_eq_sum_alternatingTrace (Λ : Type u) [Ring Λ] [Finite Λ]
    (points : Type w) [Fintype points] (D : FrobeniusActionOnStalks.{u, v, w} Λ points)
    (P : points → CochainComplex (ModuleCat.{v} Λ) ℤ)
    (hP : ∀ x, CategoryTheory.FilteredDerived.finiteProjectiveComplex Λ (P x))
    (e : ∀ x, DerivedCategory.Q.obj (P x) ≅ (D.stalk x).obj) (g : ∀ x, P x ⟶ P x)
    (hg : ∀ x, DerivedCategory.Q.map (g x) =
      (e x).hom ≫ D.frobeniusAction x ≫ (e x).inv) :
    localLefschetzNumber Λ points D =
      ∑ x : points, CategoryTheory.FilteredDerived.alternatingTrace Λ (P x) (hP x) (g x) :=
  Finset.sum_congr rfl fun x _ =>
    CategoryTheory.FilteredDerived.perfectDerivedTrace_eq_alternatingTrace Λ (D.stalk x)
      (D.frobeniusAction x) (P x) (hP x) (e x) (g x) (hg x)

/-- A curve with no rational points has local Lefschetz number zero. -/
@[simp]
public theorem localLefschetzNumber_of_isEmpty (Λ : Type u) [Ring Λ] [Finite Λ]
    (points : Type w) [Fintype points] [IsEmpty points]
    (D : FrobeniusActionOnStalks.{u, v, w} Λ points) :
    localLefschetzNumber Λ points D = 0 := by
  simp [localLefschetzNumber]

/-- With a single rational point the local Lefschetz number is the trace of the Frobenius
action on the stalk there. -/
public theorem localLefschetzNumber_unique (Λ : Type u) [Ring Λ] [Finite Λ]
    (points : Type w) [Fintype points] [Unique points]
    (D : FrobeniusActionOnStalks.{u, v, w} Λ points) :
    localLefschetzNumber Λ points D =
      CategoryTheory.FilteredDerived.perfectDerivedTrace Λ (D.stalk default)
        (D.frobeniusAction default) := by
  simp [localLefschetzNumber, Finset.sum_unique_nonempty]

end Stacks.EtaleCohomology

end
