module

public import StacksFrontier.AlgebraicGeometry.Chow.Symbols.PeriodicExactness
public import StacksFrontier.AlgebraicGeometry.Variety.DeltaInvariant.FiniteLength
public import StacksCore.Tactic.StacksAttribute

/-!
# Exact periodic complexes from two nonzerodivisors

If two elements `a` and `b` of a Noetherian local ring `A` act injectively on a finite
`A`-module `M` whose support has dimension one, then the alternating multiplication maps
induced on `M / abM` form an exact two-periodic complex of finite length. The same holds for
`A` itself when its Krull dimension is one. These are exactly the inputs needed to form the
periodic determinant of the complex, and hence the symbol of `M` at `a` and `b`.

## Main results

* `AlgebraicGeometry.isFiniteLength_quotient_mul` gives finite length for the module quotient.
* `AlgebraicGeometry.exact_mul_left_right` and `AlgebraicGeometry.exact_mul_right_left` give
  the two exactness assertions.
* `AlgebraicGeometry.isFiniteLength_ring_quotient_mul`,
  `AlgebraicGeometry.exact_ring_mul_left_right` and
  `AlgebraicGeometry.exact_ring_mul_right_left` are the corresponding assertions for the ring
  itself.

## Implementation notes

The quotient by `abM` is presented as the quotient by the range of the composite endomorphism
given by multiplication by `b` followed by multiplication by `a`. The two induced
differentials are `AlgebraicGeometry.periodicQuotientPhi` and
`AlgebraicGeometry.periodicQuotientPsi`, whose commutation hypothesis is supplied by
commutativity of scalar multiplication. The finite-length and exactness assertions are kept
separate so that either can be used on its own.

## References

* [Stacks Project, Tag 02PY](https://stacks.math.columbia.edu/tag/02PY)
-/

@[expose] public section

namespace AlgebraicGeometry

variable {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]

/-- The two composites of a pair of scalar-multiplication maps have the same range. -/
theorem range_lsmul_comp_comm (a b : A) :
    LinearMap.range ((LinearMap.lsmul A M a) ∘ₗ (LinearMap.lsmul A M b)) =
      LinearMap.range ((LinearMap.lsmul A M b) ∘ₗ (LinearMap.lsmul A M a)) := by
  congr 1
  ext m
  exact smul_comm a b m

/-- **Stacks Project, Tag 02PY.** The quotient by `abM` has finite length. -/
@[stacks 02PY "part (1): finite length"]
theorem isFiniteLength_quotient_mul [IsNoetherianRing A] [IsLocalRing A]
    [Module.Finite A M] (a b : A)
    (ha : IsSMulRegular M a) (hb : IsSMulRegular M b)
    (hdim : Module.supportDim A M = 1) :
    IsFiniteLength A
    (M ⧸ LinearMap.range
        ((LinearMap.lsmul A M a) ∘ₗ (LinearMap.lsmul A M b))) :=
  Module.isFiniteLength_quotient_range_of_injective _ (ha.comp hb) hdim

/-- **Stacks Project, Tag 02PY.** Exactness at the differential induced by multiplication
by `b`. -/
@[stacks 02PY "part (1): exactness at b"]
theorem exact_mul_left_right (a b : A)
    (hb : IsSMulRegular M b) :
    Function.Exact
      (periodicQuotientPhi
        (LinearMap.lsmul A M a) (LinearMap.lsmul A M b)
        (range_lsmul_comp_comm a b))
      (periodicQuotientPsi
        (LinearMap.lsmul A M a) (LinearMap.lsmul A M b)
        (range_lsmul_comp_comm a b)) :=
  exact_periodicQuotient_phi_psi
    (LinearMap.lsmul A M a) (LinearMap.lsmul A M b) hb (range_lsmul_comp_comm a b)

/-- **Stacks Project, Tag 02PY.** Exactness at the differential induced by multiplication
by `a`. -/
@[stacks 02PY "part (1): exactness at a"]
theorem exact_mul_right_left (a b : A)
    (ha : IsSMulRegular M a) :
    Function.Exact
      (periodicQuotientPsi
        (LinearMap.lsmul A M a) (LinearMap.lsmul A M b)
        (range_lsmul_comp_comm a b))
      (periodicQuotientPhi
        (LinearMap.lsmul A M a) (LinearMap.lsmul A M b)
        (range_lsmul_comp_comm a b)) :=
  exact_periodicQuotient_psi_phi
    (LinearMap.lsmul A M a) (LinearMap.lsmul A M b) ha (range_lsmul_comp_comm a b)

/-- **Stacks Project, Tag 02PY.** The ring quotient `A/(ab)` has finite length when `A` has
dimension one. -/
@[stacks 02PY "part (2): finite length"]
theorem isFiniteLength_ring_quotient_mul
    [IsNoetherianRing A] [IsLocalRing A]
    (a b : A) (ha : IsSMulRegular A a) (hb : IsSMulRegular A b)
    (hdim : ringKrullDim A = 1) :
    IsFiniteLength A
      (A ⧸ LinearMap.range
        ((LinearMap.lsmul A A a) ∘ₗ (LinearMap.lsmul A A b))) :=
  isFiniteLength_quotient_mul a b ha hb ((Module.supportDim_self_eq_ringKrullDim A).trans hdim)

/-- **Stacks Project, Tag 02PY.** Exactness at multiplication by `b` on `A/(ab)`. -/
@[stacks 02PY "part (2): exactness at b"]
theorem exact_ring_mul_left_right
    (a b : A) (hb : IsSMulRegular A b) :
    Function.Exact
      (periodicQuotientPhi
        (LinearMap.lsmul A A a) (LinearMap.lsmul A A b)
        (range_lsmul_comp_comm a b))
      (periodicQuotientPsi
        (LinearMap.lsmul A A a) (LinearMap.lsmul A A b)
        (range_lsmul_comp_comm a b)) :=
  exact_mul_left_right a b hb

/-- **Stacks Project, Tag 02PY.** Exactness at multiplication by `a` on `A/(ab)`. -/
@[stacks 02PY "part (2): exactness at a"]
theorem exact_ring_mul_right_left
    (a b : A) (ha : IsSMulRegular A a) :
    Function.Exact
      (periodicQuotientPsi
        (LinearMap.lsmul A A a) (LinearMap.lsmul A A b)
        (range_lsmul_comp_comm a b))
      (periodicQuotientPhi
        (LinearMap.lsmul A A a) (LinearMap.lsmul A A b)
        (range_lsmul_comp_comm a b)) :=
  exact_mul_right_left a b ha

end AlgebraicGeometry
