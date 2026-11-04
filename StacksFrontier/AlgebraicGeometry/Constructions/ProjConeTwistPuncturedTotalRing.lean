module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UngradedAlgebras
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjConeTwistPuncturedCoproduct
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjConeTwistPuncturedMul

/-!
# The functions on the punctured cone as the ungraded realization of the twist algebra

Let `A = ⨁_{d ≥ 0} 𝒜 d` be a graded ring, `P = Proj A`, and let `π : L ⟶ P` be the cone attached
to the truncation algebra, with `U ⊆ L` the punctured cone. The ungraded realization of the sheaf
of graded algebras `Stacks.AlgebraicGeometry.ProjConeTwist.integerTwistAlgebra` of
[Stacks, Tag 01CF] has, over an open `V` of `P`, the direct sum `⨁_{m ∈ ℤ} Γ(V, 𝒪_P(m))` of the
sections of the twisting sheaves as its ring of sections, and the degreewise inclusions assemble
into an additive map from that direct sum into `Γ(U, (π|_U)⁻¹V)`, which is
`Stacks.AlgebraicGeometry.ProjConeTwist.puncturedTwistDirectSumHom`.

**This file proves that that map is a ring homomorphism**: the comparison
`Γ(V, ⨁_{m ∈ ℤ} 𝒪_P(m)) ⟶ Γ(U, (π|_U)⁻¹V)` of *rings*, degreewise the inclusion, that the
identification of `(π|_U)_* 𝒪_U` with the twist algebra of [Stacks, Tag 0EKG] is about — as
opposed to the identification of the underlying sheaves of `𝒪_P`-modules, which is
`Stacks.AlgebraicGeometry.ProjConeTwist.puncturedConeStructureCoproductIso`.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjConeTwist.integerTwistPresheafAlgebra`: the algebra of all
  integral twists read as a graded algebra of presheaves of modules.
* `Stacks.AlgebraicGeometry.ProjConeTwist.puncturedTotalMap`: the degreewise inclusions on the
  sections over an open, as a map into the functions on the punctured cone.
* `Stacks.AlgebraicGeometry.ProjConeTwist.puncturedTotalRingHom`: **the same as a ring
  homomorphism `Γ(V, ⨁_{m ∈ ℤ} 𝒪_P(m)) →+* Γ(U, (π|_U)⁻¹V)`**, over every open `V` of `P`.

## Main results

* `Stacks.AlgebraicGeometry.ProjConeTwist.puncturedTwistDirectSumHom_app_incl`: the comparison
  out of the objectwise direct sum sends the `m`-th summand to the degreewise inclusion. This is
  `puncturedTwistDirectSumHom_app_of` over an arbitrary open rather than over a standard one.
* `Stacks.AlgebraicGeometry.ProjConeTwist.puncturedTotalMap_mul` and
  `puncturedTotalMap_one`: **that map is multiplicative and unital.**
* `Stacks.AlgebraicGeometry.ProjConeTwist.puncturedTotalRingHom_incl` and
  `puncturedTotalMap_incl`: the comparison is the degreewise inclusion on each homogeneous
  summand.

## Implementation notes

Products of sections of the direct image are formed in
`Stacks.AlgebraicGeometry.ProjConeTwist.puncturedConeSections`, the functions on the part of the
punctured cone over the open; the sections of the direct sum are read as
`Stacks.GradedAlgebra.Total`, the type synonym that carries the ring structure of the graded
algebra. The two readings of a section of the direct sum are the same by definition, so the ring
homomorphism is the comparison itself with no transport.

## References

* [Stacks Project, Tag 0EKG](https://stacks.math.columbia.edu/tag/0EKG)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpectrum.Proj CategoryTheory Opposite
open TopologicalSpace
open Stacks.AlgebraicGeometry.ProjAndSpecTruncation Stacks.Truncation
open Stacks.AlgebraicGeometry.ProjTwistComparison

namespace Stacks.AlgebraicGeometry.ProjConeTwist

universe u

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  PresheafOfModules.presheaf SheafOfModules.toSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {A : Type u} {σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- The algebra of all integral twists read as a graded algebra of presheaves of modules. -/
abbrev integerTwistPresheafAlgebra :
    Stacks.GradedAlgebra fun m : ℤ => (twistingSheaf 𝒜 m).val :=
  (integerTwistAlgebra 𝒜).toPresheafGradedAlgebra

/-- **The comparison out of the objectwise direct sum sends the `m`-th summand to the degreewise
inclusion**, over every open of `P`. -/
theorem puncturedTwistDirectSumHom_app_incl (m : ℤ) (V : Opens (ProjectiveSpectrum.top 𝒜))
    (x : (twistingSheaf 𝒜 m).val.obj (op V)) :
    (puncturedTwistDirectSumHom 𝒜).app (op V) (DirectSum.of _ m x) =
      (puncturedTwistHom 𝒜 m).val.app (op V) x :=
  congrArg (fun q : (twistingSheaf 𝒜 m).val ⟶
      (Stacks.Morphisms.pushforwardStructureSheaf ((openUInL 𝒜).ι ≫ pi 𝒜)).val => q.app (op V) x)
    (Stacks.inclHom_directSumDesc (fun k : ℤ => (twistingSheaf 𝒜 k).val)
      (fun k => (puncturedTwistHom 𝒜 k).val) m)

/-- **The degreewise inclusions on the sections over an open**, as a map from the sections of the
ungraded realization of the algebra of all integral twists into the functions on the part of the
punctured cone lying over that open. -/
def puncturedTotalMap (V : Opens (ProjectiveSpectrum.top 𝒜))
    (z : (integerTwistPresheafAlgebra 𝒜).Total (op V)) : puncturedConeSections 𝒜 V :=
  (puncturedTwistDirectSumHom 𝒜).app (op V) z

/-- The map is the degreewise inclusion on each homogeneous summand. -/
theorem puncturedTotalMap_incl (V : Opens (ProjectiveSpectrum.top 𝒜)) (m : ℤ)
    (x : (twistingSheaf 𝒜 m).val.obj (op V)) :
    puncturedTotalMap 𝒜 V ((integerTwistPresheafAlgebra 𝒜).incl m x) =
      (puncturedTwistHom 𝒜 m).val.app (op V) x :=
  puncturedTwistDirectSumHom_app_incl 𝒜 m V x

/-- The map sends zero to zero. -/
@[simp] theorem puncturedTotalMap_zero (V : Opens (ProjectiveSpectrum.top 𝒜)) :
    puncturedTotalMap 𝒜 V 0 = 0 :=
  map_zero (ConcreteCategory.hom ((puncturedTwistDirectSumHom 𝒜).app (op V)))

/-- The map is additive. -/
theorem puncturedTotalMap_add (V : Opens (ProjectiveSpectrum.top 𝒜))
    (z w : (integerTwistPresheafAlgebra 𝒜).Total (op V)) :
    puncturedTotalMap 𝒜 V (z + w) = puncturedTotalMap 𝒜 V z + puncturedTotalMap 𝒜 V w :=
  map_add (ConcreteCategory.hom ((puncturedTwistDirectSumHom 𝒜).app (op V))) z w

/-- **The map is unital.** -/
theorem puncturedTotalMap_one (V : Opens (ProjectiveSpectrum.top 𝒜)) :
    puncturedTotalMap 𝒜 V 1 = 1 := by
  rw [Stacks.GradedAlgebra.one_eq_incl (integerTwistPresheafAlgebra 𝒜) (op V),
    puncturedTotalMap_incl]
  exact puncturedTwistHom_one_app 𝒜 V

/-- **The map is multiplicative on two homogeneous summands.** -/
theorem puncturedTotalMap_incl_mul_incl (V : Opens (ProjectiveSpectrum.top 𝒜)) (i j : ℤ)
    (x : (twistingSheaf 𝒜 i).val.obj (op V)) (y : (twistingSheaf 𝒜 j).val.obj (op V)) :
    puncturedTotalMap 𝒜 V ((integerTwistPresheafAlgebra 𝒜).incl i x *
        (integerTwistPresheafAlgebra 𝒜).incl j y) =
      puncturedTotalMap 𝒜 V ((integerTwistPresheafAlgebra 𝒜).incl i x) *
        puncturedTotalMap 𝒜 V ((integerTwistPresheafAlgebra 𝒜).incl j y) := by
  have h1 := Stacks.GradedAlgebra.incl_mul_incl (integerTwistPresheafAlgebra 𝒜) i j x y
  have h2 := puncturedTotalMap_incl 𝒜 V (i + j)
    (((integerTwistPresheafAlgebra 𝒜).mul i j).app (op V) x y)
  have h3 := puncturedTotalMap_incl 𝒜 V i x
  have h4 := puncturedTotalMap_incl 𝒜 V j y
  have h5 := puncturedTwistHom_mul_app 𝒜 i j V x y
  exact ((congrArg (puncturedTotalMap 𝒜 V) h1).trans h2).trans
    (h5.trans (congrArg₂ (· * ·) h3.symm h4.symm))

/-- The map is multiplicative when the left factor is homogeneous. -/
theorem puncturedTotalMap_incl_mul (V : Opens (ProjectiveSpectrum.top 𝒜)) (i : ℤ)
    (x : (twistingSheaf 𝒜 i).val.obj (op V))
    (w : (integerTwistPresheafAlgebra 𝒜).Total (op V)) :
    puncturedTotalMap 𝒜 V ((integerTwistPresheafAlgebra 𝒜).incl i x * w) =
      puncturedTotalMap 𝒜 V ((integerTwistPresheafAlgebra 𝒜).incl i x) *
        puncturedTotalMap 𝒜 V w := by
  induction w using Stacks.GradedAlgebra.incl_induction with
  | zero => rw [mul_zero, puncturedTotalMap_zero, mul_zero]
  | incl j y => exact puncturedTotalMap_incl_mul_incl 𝒜 V i j x y
  | add w w' hw hw' =>
    rw [mul_add, puncturedTotalMap_add, hw, hw', puncturedTotalMap_add, mul_add]

/-- **The map is multiplicative.** -/
@[stacks 0EKG "the comparison from the objectwise direct sum of the twisting sheaves to the \
functions on the punctured cone is multiplicative, over every open of P"]
theorem puncturedTotalMap_mul (V : Opens (ProjectiveSpectrum.top 𝒜))
    (z w : (integerTwistPresheafAlgebra 𝒜).Total (op V)) :
    puncturedTotalMap 𝒜 V (z * w) = puncturedTotalMap 𝒜 V z * puncturedTotalMap 𝒜 V w := by
  induction z using Stacks.GradedAlgebra.incl_induction with
  | zero => rw [zero_mul, puncturedTotalMap_zero, zero_mul]
  | incl i x => exact puncturedTotalMap_incl_mul 𝒜 V i x w
  | add z z' hz hz' =>
    rw [add_mul, puncturedTotalMap_add, hz, hz', puncturedTotalMap_add, add_mul]

/-- **The degreewise inclusions as a ring homomorphism
`Γ(V, ⨁_{m ∈ ℤ} 𝒪_P(m)) →+* Γ(U, (π|_U)⁻¹V)`.** The sections of the ungraded realization of the
algebra of all integral twists over `V` map to the functions on the part of the punctured cone
lying over `V`, degreewise by the inclusion of the twisting sheaf. -/
@[stacks 0EKG "the degreewise inclusions as a ring homomorphism from the sections of the \
ungraded realization of the integral twist algebra to the functions on the punctured cone, over \
every open of P, for the truncation cone"]
def puncturedTotalRingHom (V : Opens (ProjectiveSpectrum.top 𝒜)) :
    (integerTwistPresheafAlgebra 𝒜).Total (op V) →+* puncturedConeSections 𝒜 V where
  toFun := puncturedTotalMap 𝒜 V
  map_one' := puncturedTotalMap_one 𝒜 V
  map_mul' := puncturedTotalMap_mul 𝒜 V
  map_zero' := puncturedTotalMap_zero 𝒜 V
  map_add' := puncturedTotalMap_add 𝒜 V

/-- The ring homomorphism is the degreewise inclusion on each homogeneous summand. -/
theorem puncturedTotalRingHom_incl (V : Opens (ProjectiveSpectrum.top 𝒜)) (m : ℤ)
    (x : (twistingSheaf 𝒜 m).val.obj (op V)) :
    puncturedTotalRingHom 𝒜 V ((integerTwistPresheafAlgebra 𝒜).incl m x) =
      (puncturedTwistHom 𝒜 m).val.app (op V) x :=
  puncturedTotalMap_incl 𝒜 V m x

end Stacks.AlgebraicGeometry.ProjConeTwist

end
