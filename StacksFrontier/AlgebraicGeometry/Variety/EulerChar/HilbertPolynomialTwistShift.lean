module

public import StacksFrontier.AlgebraicGeometry.EulerCharIso.Basic
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.TwistAdd
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.HilbertPolynomial

/-!
# The Hilbert polynomial of a twist is a shift

For a coherent sheaf `ℱ` on `ℙⁿ_k` over a field and an integer `m`, the Hilbert polynomial of
the twist `ℱ(m)` is the Hilbert polynomial of `ℱ` shifted by `m`:
`χ(ℙⁿ_k, ℱ(m)(d)) = χ(ℙⁿ_k, ℱ(d + m))`.

## Main results

* `AlgebraicGeometry.hilbertPolynomial_projectiveTwist`: the Hilbert polynomial of `ℱ(m)`
  evaluated at `d` is the Hilbert polynomial of `ℱ` evaluated at `d + m`.

## Implementation notes

The Hilbert polynomial is a sum of dimensions of cohomology of the twists, and dimensions of
cohomology are invariant under isomorphism
(`AlgebraicGeometry.finrank_cohomologyOverField_eq_of_iso`). The isomorphism `(ℱ(m))(d) ≅ ℱ(m + d)`
is `AlgebraicGeometry.ProjectiveQuot.twistTwistIso` over the base `Spec k`, where the twist of
`AlgebraicGeometry.ProjectiveQuot` is `AlgebraicGeometry.projectiveTwist` on the nose
(`AlgebraicGeometry.ProjectiveQuot.twist_spec`).
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry

universe u

/-- **The Hilbert polynomial of a twist is the shifted Hilbert polynomial.** For a coherent sheaf
`ℱ` on `ℙⁿ_k` over a field `k` and integers `m, d`, the Hilbert polynomial of `ℱ(m)` at `d`
equals the Hilbert polynomial of `ℱ` at `d + m`, because `(ℱ(m))(d) ≅ ℱ(m + d)`
(`AlgebraicGeometry.ProjectiveQuot.twistTwistIso`). The coherence of `ℱ(m)` is an instance argument
so that any proof of it may be used; one is `AlgebraicGeometry.isCoherent_projectiveTwist`. -/
theorem hilbertPolynomial_projectiveTwist (k : Type u) [Field k] (n : ℕ)
    (F : (projectiveSpaceOverRing n (.of k)).Modules) [F.IsCoherent] (m d : ℤ)
    [(projectiveTwist n F m).IsCoherent] :
    hilbertPolynomial k n (projectiveTwist n F m) d = hilbertPolynomial k n F (d + m) := by
  have e : projectiveTwist n (projectiveTwist n F m) d ≅ projectiveTwist n F (m + d) :=
    ProjectiveQuot.twistTwistIso (Spec (.of k)) m d F
  unfold hilbertPolynomial
  refine finsum_congr fun i => ?_
  rw [add_comm d m, finrank_cohomologyOverField_eq_of_iso k
    (projectiveSpaceOverRing n (.of k) ↘ Spec (.of k)) e i]

end AlgebraicGeometry

end
