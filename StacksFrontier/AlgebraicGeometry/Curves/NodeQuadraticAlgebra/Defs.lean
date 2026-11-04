module

public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# The quadratic algebra associated to a node

For a local ring `A`, its normalization `A' = integralClosure A (FractionRing A)` inside its
total ring of fractions has a canonical fibre over the closed point, namely the quotient of `A'`
by the extension `𝔪_A A'` of the maximal ideal of `A`. For a nodal local algebra this fibre is
the *quadratic algebra associated to the node*: a separable algebra of degree two over the
residue field of `A`, which is a separable quadratic field extension at a non-split node and
`κ × κ` at a split one.

The fibre is defined for every commutative local ring, and it is an algebra over the residue
field of `A`.

## Main definitions

* `Stacks.Curves.quadraticAlgebra`: the closed fibre of the normalization of a local ring
  inside its total ring of fractions.

## References

* [Stacks Project, Tag 0CBT](https://stacks.math.columbia.edu/tag/0CBT)
-/

@[expose] public noncomputable section

open IsLocalRing

universe u

namespace Stacks.Curves

/-- The quadratic algebra associated to a local ring: the closed fibre of its normalization
inside its total ring of fractions. -/
@[stacks 0CBT "quadratic_algebra_associated_to_a_node"]
public abbrev quadraticAlgebra (A : Type u) [CommRing A] [IsLocalRing A] :=
  integralClosure A (FractionRing A) ⧸
    (maximalIdeal A).map (algebraMap A (integralClosure A (FractionRing A)))

/-- The quadratic algebra of a local ring is an algebra over its residue field, through the map
induced by `A → A' → A' ⧸ 𝔪_A A'`. -/
public instance instAlgebraResidueFieldQuadraticAlgebra (A : Type u) [CommRing A]
    [IsLocalRing A] : Algebra (ResidueField A) (quadraticAlgebra A) :=
  let B := integralClosure A (FractionRing A)
  let J := (maximalIdeal A).map (algebraMap A B)
  let f : A →+* (B ⧸ J) := (Ideal.Quotient.mk J).comp (algebraMap A B)
  let g : ResidueField A →+* (B ⧸ J) := Ideal.Quotient.lift (maximalIdeal A) f fun _ ha ↦
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem (algebraMap A B) ha)
  g.toAlgebra' fun c x ↦ by
    obtain ⟨y⟩ := g c
    obtain ⟨z⟩ := x
    exact congr_arg Submodule.Quotient.mk (mul_comm y z)

/-- The residue-field algebra structure on the quadratic algebra is compatible with any base
`k` of `A`. -/
public instance instIsScalarTowerResidueFieldQuadraticAlgebra (k : Type*) (A : Type u)
    [CommRing k] [CommRing A] [IsLocalRing A] [Algebra k A]
    [Algebra k ↥(integralClosure A (FractionRing A))]
    [IsScalarTower k A ↥(integralClosure A (FractionRing A))] :
    IsScalarTower k (ResidueField A) (quadraticAlgebra A) :=
  IsScalarTower.of_algebraMap_eq fun c ↦
    congrArg (Ideal.Quotient.mk _) (IsScalarTower.algebraMap_apply k A _ c)

end Stacks.Curves

end
