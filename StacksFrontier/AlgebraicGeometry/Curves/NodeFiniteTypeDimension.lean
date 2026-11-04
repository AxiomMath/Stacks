module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.KrullDimension
public import StacksFrontier.AlgebraicGeometry.Curves.NodeFiniteTypeWitness
public import StacksFrontier.AlgebraicGeometry.Curves.NodeStalkCharacterization
public import StacksFrontier.RingTheory.MvPolynomial.HypersurfaceDimension
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The witness curve and its control are one-dimensional schemes

`StacksFrontier.AlgebraicGeometry.Curves.NodeFiniteTypeWitness` exhibits the origin of the affine
nodal plane curve `Spec k[x, y]/(xy)` as a node on a scheme locally of finite type over `k`, and
computes the Krull dimension of the **local ring** there.  The results about nodes that are stated
for a scheme — notably the equivalence of conditions (2) and (6) of Tag 0C4D,
`isNodalAlgebra_stalk_iff_deltaInvariant_eq_one_and_two_geometricBranches` — carry instead the
hypothesis `topologicalKrullDim X = 1` on the whole scheme.  This file supplies that, for the
witness and for its negative control.

The local computation does not supply it on its own.  The height of the origin ideal equals the
Krull dimension of the local ring there, and a height is a **lower** bound for the dimension of
the ring; dimension is a supremum over points, so one point can never bound it above.  The upper
bound comes from the ambient affine plane: `k[x, y]/(xy)` is a hypersurface, and
`Stacks.MvPolynomial.ringKrullDim_quotient_span_singleton` computes the dimension of a
hypersurface in affine space over a field with no hypothesis that the quotient is a domain.  Both
bounds are recorded below, and they agree.

## Main results

* `Stacks.Curves.not_isDomain_nodalPlaneAlgebra` — `k[x, y]/(xy)` is **not** a domain, which is
  why the `[IsDomain]` dimension formula for finite-type algebras over a field does not reach it.
* `Stacks.Curves.ringKrullDim_nodalPlaneAlgebra` — `dim k[x, y]/(xy) = 1`.
* `Stacks.Curves.topologicalKrullDim_nodalPlaneScheme` — the witness scheme is one-dimensional,
  which is the hypothesis the scheme-level node characterizations take.
* `Stacks.Curves.height_nodalPlaneOriginIdeal` — the origin has height one, the local half of the
  same computation.
* `Stacks.Curves.deltaInvariant_eq_one_and_numberOfGeometricBranches_eq_two_nodalPlaneScheme` —
  the consequence of the dimension computation: the node of `Spec k[x, y]/(xy)` has delta invariant
  one and exactly two geometric branches.
* `Stacks.Curves.not_isDomain_doubleLinePlaneAlgebra`,
  `Stacks.Curves.ringKrullDim_doubleLinePlaneAlgebra` and
  `Stacks.Curves.topologicalKrullDim_doubleLinePlaneScheme` — the same for the double line
  `Spec k[x, y]/(x²)`, which together with
  `Stacks.Curves.not_isNode_doubleLinePlaneScheme` makes it a **full** negative control: it
  satisfies every hypothesis of the node characterizations — locally of finite type over `k`,
  one-dimensional — and is not a node.

## Implementation notes

No statement here names `Spec`, which is why none has to spell it `AlgebraicGeometry.Spec`: a
root-level `abbrev Spec` in this file's import closure would make the bare name ambiguous.

The passage from the scheme to the prime spectrum of its coordinate ring costs a `rfl`: the
carrier of `AlgebraicGeometry.Spec (CommRingCat.of A)` *is* `PrimeSpectrum A`, with the same
topology, so `PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim` applies once the spelling is
crossed.  `rfl` does cross it; a `rw` cannot, since the two spellings are not syntactically
equal.

## References

* [Stacks Project, Tag 0C4D](https://stacks.math.columbia.edu/tag/0C4D)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial

universe u

namespace Stacks.Curves

variable (k : Type u) [Field k]

/-! ### The nodal plane curve -/

/-- The nodal equation `xy` is a nonunit of `k[x, y]`. -/
theorem not_isUnit_X_zero_mul_X_one :
    ¬ IsUnit ((MvPolynomial.X 0 : MvPolynomial (Fin 2) k) * MvPolynomial.X 1) := fun h =>
  (MvPolynomial.X_prime (i := (0 : Fin 2)) (R := k)).not_isUnit (isUnit_of_mul_isUnit_left h)

/-- A product `X i * X j` of two variables does not divide `X i`. -/
private theorem not_X_mul_X_dvd_left (i j : Fin 2) :
    ¬ ((MvPolynomial.X i : MvPolynomial (Fin 2) k) * MvPolynomial.X j ∣ MvPolynomial.X i) := by
  rintro ⟨c, hc⟩
  rw [mul_assoc] at hc
  exact (MvPolynomial.X_prime (i := j) (R := k)).not_isUnit
    (isUnit_of_dvd_one ⟨c, mul_left_cancel₀ (MvPolynomial.X_ne_zero i)
      (by rwa [mul_one])⟩)

/-- A nonzero nonunit of `k[x, y]` cuts out a one-dimensional hypersurface. -/
private theorem ringKrullDim_quotient_span_singleton_eq_one (f : MvPolynomial (Fin 2) k)
    (hf : f ≠ 0) (hu : ¬ IsUnit f) :
    ringKrullDim (MvPolynomial (Fin 2) k ⧸ Ideal.span {f}) = 1 := by
  simpa using Stacks.MvPolynomial.ringKrullDim_quotient_span_singleton k (Fin 2)
    (n := 1) (by simp) f hf hu

/-- A ring of Krull dimension one has a one-dimensional spectrum. -/
private theorem topologicalKrullDim_spec_eq_one {A : Type u} [CommRing A]
    (h : ringKrullDim A = 1) :
    topologicalKrullDim (AlgebraicGeometry.Spec (CommRingCat.of A)) = 1 :=
  (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim A).trans h

/-- **The coordinate ring of the affine nodal plane curve is not a domain.**

This is why the repository's dimension formula for a finite-type algebra over a field —
`StacksFrontier.RingTheory.KrullDimension.FiniteTypeOverField`, which carries `[IsDomain S]` — does
not apply to the witness, and it is a *theorem* rather than a synthesis failure: the images of `x`
and `y` are nonzero and their product vanishes. -/
theorem not_isDomain_nodalPlaneAlgebra : ¬ IsDomain (nodalPlaneAlgebra k) := by
  intro h
  have hzero : (Ideal.Quotient.mk _ (MvPolynomial.X 0) : nodalPlaneAlgebra k) *
      Ideal.Quotient.mk _ (MvPolynomial.X 1) = 0 := by
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self _
  rcases mul_eq_zero.mp hzero with h0 | h1
  · exact not_X_mul_X_dvd_left k 0 1
      (Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp h0))
  · refine not_X_mul_X_dvd_left k 1 0 ?_
    rw [mul_comm]
    exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp h1)

/-- **The coordinate ring of the affine nodal plane curve is one-dimensional.**

`k[x, y]/(xy)` is **not** a domain, so the dimension formula for a finite-type domain over a field
does not apply to it.  What does apply is that it is a hypersurface in the affine plane: the
plane is equidimensional of dimension two, so cutting it by the single nonzero nonunit `xy`
leaves dimension one. -/
theorem ringKrullDim_nodalPlaneAlgebra : ringKrullDim (nodalPlaneAlgebra k) = 1 :=
  ringKrullDim_quotient_span_singleton_eq_one k _ (by simp) (not_isUnit_X_zero_mul_X_one k)

/-- **The origin of the affine nodal plane curve has height one.**  This is the local half of
`ringKrullDim_nodalPlaneAlgebra`, obtained from the Krull dimension of the local ring there; on
its own it gives only the lower bound `1 ≤ dim k[x, y]/(xy)`. -/
theorem height_nodalPlaneOriginIdeal : (nodalPlaneOriginIdeal k).height = 1 := by
  have h : ringKrullDim (nodalPlaneLocalRing k) =
      ((nodalPlaneOriginIdeal k).height : WithBot ℕ∞) :=
    IsLocalization.AtPrime.ringKrullDim_eq_height _ _
  rw [ringKrullDim_nodalPlaneLocalRing k] at h
  exact_mod_cast h.symm

/-- **The affine nodal plane curve is a one-dimensional scheme.**  This is the dimension
hypothesis carried by the scheme-level characterizations of a node, in particular by the
equivalence of conditions (2) and (6) of Tag 0C4D. -/
theorem topologicalKrullDim_nodalPlaneScheme :
    topologicalKrullDim (nodalPlaneScheme k) = 1 :=
  topologicalKrullDim_spec_eq_one (ringKrullDim_nodalPlaneAlgebra k)

/-- **The node of `Spec k[x, y]/(xy)` has delta invariant one and exactly two geometric
branches.**

This is where the dimension hypothesis enters.  The equivalence of conditions (2) and (6) of
Tag 0C4D requires `topologicalKrullDim X = 1`, which `topologicalKrullDim_nodalPlaneScheme`
supplies for the witness; with it, the known nodality of the stalk yields both numerical invariants of the node outright. -/
@[sga "7 X 2.24" "partial"]
theorem deltaInvariant_eq_one_and_numberOfGeometricBranches_eq_two_nodalPlaneScheme
    [IsAlgClosed k] :
    Ring.deltaInvariant ((nodalPlaneScheme k).presheaf.stalk (nodalPlaneOrigin k)) = 1 ∧
      numberOfGeometricBranches (nodalPlaneScheme k) (nodalPlaneOrigin k) = 2 := by
  let : Algebra k ((nodalPlaneScheme k).presheaf.stalk (nodalPlaneOrigin k)) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫
      (nodalPlaneScheme k ↘ AlgebraicGeometry.Spec (.of k)).appTop ≫
        (nodalPlaneScheme k).presheaf.germ ⊤ (nodalPlaneOrigin k) (by simp)).hom.toAlgebra
  exact ((isNodalAlgebra_stalk_iff_deltaInvariant_eq_one_and_two_geometricBranches k
    (nodalPlaneScheme k) (topologicalKrullDim_nodalPlaneScheme k) (nodalPlaneOrigin k)).mp
      (isNodalAlgebra_of_ringEquiv k k (nodalPlaneStalkRingEquiv k).symm
        (isNodalAlgebra_nodalPlaneLocalRing k k))).2.2

/-! ### The double line, the negative control -/

/-- The double-line equation `x²` is a nonunit of `k[x, y]`. -/
theorem not_isUnit_X_zero_sq :
    ¬ IsUnit ((MvPolynomial.X 0 : MvPolynomial (Fin 2) k) ^ 2) := by
  rw [pow_two]
  exact fun h => (MvPolynomial.X_prime (i := (0 : Fin 2)) (R := k)).not_isUnit
    (isUnit_of_mul_isUnit_left h)

/-- **The coordinate ring of the double line is not a domain either**, so the control is outside
the reach of the `[IsDomain]` formula for the same reason the witness is. -/
theorem not_isDomain_doubleLinePlaneAlgebra : ¬ IsDomain (doubleLinePlaneAlgebra k) := by
  intro h
  have hzero : (Ideal.Quotient.mk _ (MvPolynomial.X 0) : doubleLinePlaneAlgebra k) ^ 2 = 0 := by
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self _
  refine not_X_mul_X_dvd_left k 0 0 ?_
  rw [← pow_two]
  exact Ideal.mem_span_singleton.mp
    (Ideal.Quotient.eq_zero_iff_mem.mp (pow_eq_zero_iff two_ne_zero |>.mp hzero))

/-- **The coordinate ring of the double line is one-dimensional.**  `k[x, y]/(x²)` is not reduced,
so no dimension formula resting on reducedness or on being a domain applies; the hypersurface
computation does. -/
theorem ringKrullDim_doubleLinePlaneAlgebra :
    ringKrullDim (doubleLinePlaneAlgebra k) = 1 :=
  ringKrullDim_quotient_span_singleton_eq_one k _ (pow_ne_zero 2 (MvPolynomial.X_ne_zero 0))
    (not_isUnit_X_zero_sq k)

/-- **The double line is a one-dimensional scheme.**  With
`Stacks.Curves.locallyOfFiniteType_doubleLinePlaneScheme` and
`Stacks.Curves.not_isNode_doubleLinePlaneScheme` this makes `Spec k[x, y]/(x²)` a control
satisfying every hypothesis of the scheme-level node characterizations while failing to be a
node. -/
theorem topologicalKrullDim_doubleLinePlaneScheme :
    topologicalKrullDim (doubleLinePlaneScheme k) = 1 :=
  topologicalKrullDim_spec_eq_one (ringKrullDim_doubleLinePlaneAlgebra k)

end Stacks.Curves

end
