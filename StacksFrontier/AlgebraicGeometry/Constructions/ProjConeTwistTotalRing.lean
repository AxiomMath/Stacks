module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UngradedAlgebras
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjConeTwistConeCoproduct
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjConeTwistUnit

/-!
# The functions on the cone as the ungraded realization of the twist algebra

Let `A = ⨁_{d ≥ 0} 𝒜 d` be a graded ring, `P = Proj A`, and let `π : L ⟶ P` be the cone attached
to the truncation algebra. The ungraded realization of the sheaf of graded algebras
`Stacks.AlgebraicGeometry.ProjConeTwist.nonnegTwistAlgebra` of [Stacks, Tag 01CF] has, over an
open `U` of `P`, the direct sum `⨁_{m ∈ ℤ} Γ(U, 𝒪_P(m))` of the sections of the homogeneous
pieces as its ring of sections, which is `Stacks.GradedAlgebra.Total`. The degreewise inclusions
assemble into an additive map from that direct sum into `Γ(L, π⁻¹U)`, which is
`Stacks.AlgebraicGeometry.ProjConeTwist.coneTwistDirectSumHom`.

**This file proves that that map is a ring homomorphism**: the comparison
`Γ(U, ⨁_{m ≥ 0} 𝒪_P(m)) ⟶ Γ(L, π⁻¹U)` of *rings*, degreewise the inclusion, that the
identification of `π_* 𝒪_L` with the twist algebra of [Stacks, Tag 0EKG] is about — as opposed to
the identification of the underlying sheaves of `𝒪_P`-modules, which is
`Stacks.AlgebraicGeometry.ProjConeTwist.coneStructureCoproductIso`.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjConeTwist.nonnegTwistPresheafAlgebra`: the algebra of nonnegative
  twists read as a graded algebra of presheaves of modules.
* `Stacks.AlgebraicGeometry.ProjConeTwist.coneTotalMap`: the degreewise inclusions on the
  sections over an open, as a map into the functions on the cone.
* `Stacks.AlgebraicGeometry.ProjConeTwist.coneTotalRingHom`: **the same as a ring homomorphism
  `Γ(U, ⨁_{m ≥ 0} 𝒪_P(m)) →+* Γ(L, π⁻¹U)`**, over every open `U` of `P`.

## Main results

* `Stacks.AlgebraicGeometry.ProjConeTwist.coneTwistDirectSumHom_app_incl`: the comparison out of
  the objectwise direct sum sends the `m`-th summand to the inclusion of the `m`-th homogeneous
  piece. This is `coneTwistDirectSumHom_app_of` over an arbitrary open rather than over a
  standard one.
* `Stacks.AlgebraicGeometry.ProjConeTwist.coneTotalMap_mul` and
  `Stacks.AlgebraicGeometry.ProjConeTwist.coneTotalMap_one`: **that map is multiplicative and
  unital.**
* `Stacks.AlgebraicGeometry.ProjConeTwist.coneTotalRingHom_incl` and
  `Stacks.AlgebraicGeometry.ProjConeTwist.coneTotalMap_incl`: the comparison is the degreewise
  inclusion on each homogeneous summand.

## Implementation notes

Products of sections of the direct image are formed in
`Stacks.AlgebraicGeometry.ProjConeTwist.coneSections`, the functions on the part of the cone over
the open; the sections of the direct sum are read as `Stacks.GradedAlgebra.Total`, the type
synonym that carries the ring structure of the graded algebra. The two readings of a section of
the direct sum — as an element of `Total` and as an element of the sections of the presheaf of
modules the comparison is defined on — are the same by definition, so the ring homomorphism is
the comparison itself with no transport.

## References

* [Stacks Project, Tag 0EKG](https://stacks.math.columbia.edu/tag/0EKG)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpectrum.Proj CategoryTheory Opposite
open TopologicalSpace
open Stacks.AlgebraicGeometry.ProjAndSpecTruncation Stacks.Truncation

namespace Stacks.AlgebraicGeometry.ProjConeTwist

universe u

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  PresheafOfModules.presheaf SheafOfModules.toSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {A : Type u} {σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- The algebra of nonnegative twists read as a graded algebra of presheaves of modules. -/
abbrev nonnegTwistPresheafAlgebra :
    Stacks.GradedAlgebra fun m : ℤ => (nonnegTwistingSheaf 𝒜 m).val :=
  (nonnegTwistAlgebra 𝒜).toPresheafGradedAlgebra

/-- **The comparison out of the objectwise direct sum sends the `m`-th summand to the inclusion
of the `m`-th homogeneous piece**, over every open of `P`. -/
theorem coneTwistDirectSumHom_app_incl (m : ℤ) (U : Opens (ProjectiveSpectrum.top 𝒜))
    (x : (nonnegTwistingSheaf 𝒜 m).val.obj (op U)) :
    (coneTwistDirectSumHom 𝒜).app (op U) (DirectSum.of _ m x) =
      (coneIota 𝒜 m).val.app (op U) x :=
  congrArg (fun q : (nonnegTwistingSheaf 𝒜 m).val ⟶
      (Stacks.Morphisms.pushforwardStructureSheaf (pi 𝒜)).val => q.app (op U) x)
    (Stacks.inclHom_directSumDesc (fun k : ℤ => (nonnegTwistingSheaf 𝒜 k).val)
      (fun k => (coneIota 𝒜 k).val) m)

/-- **The degreewise inclusions on the sections over an open**, as a map from the sections of the
ungraded realization of the algebra of nonnegative twists into the functions on the part of the
cone lying over that open. This is
`Stacks.AlgebraicGeometry.ProjConeTwist.coneTwistDirectSumHom` on sections, with the source read
as `Stacks.GradedAlgebra.Total` so that it carries the ring structure and the target as a ring of
functions. -/
def coneTotalMap (U : Opens (ProjectiveSpectrum.top 𝒜))
    (z : (nonnegTwistPresheafAlgebra 𝒜).Total (op U)) : coneSections 𝒜 U :=
  (coneTwistDirectSumHom 𝒜).app (op U) z

/-- The map is the degreewise inclusion on each homogeneous summand. -/
theorem coneTotalMap_incl (U : Opens (ProjectiveSpectrum.top 𝒜)) (m : ℤ)
    (x : (nonnegTwistingSheaf 𝒜 m).val.obj (op U)) :
    coneTotalMap 𝒜 U ((nonnegTwistPresheafAlgebra 𝒜).incl m x) =
      (coneIota 𝒜 m).val.app (op U) x :=
  coneTwistDirectSumHom_app_incl 𝒜 m U x

/-- The map sends zero to zero. -/
@[simp] theorem coneTotalMap_zero (U : Opens (ProjectiveSpectrum.top 𝒜)) :
    coneTotalMap 𝒜 U 0 = 0 :=
  map_zero (ConcreteCategory.hom ((coneTwistDirectSumHom 𝒜).app (op U)))

/-- The map is additive. -/
theorem coneTotalMap_add (U : Opens (ProjectiveSpectrum.top 𝒜))
    (z w : (nonnegTwistPresheafAlgebra 𝒜).Total (op U)) :
    coneTotalMap 𝒜 U (z + w) = coneTotalMap 𝒜 U z + coneTotalMap 𝒜 U w :=
  map_add (ConcreteCategory.hom ((coneTwistDirectSumHom 𝒜).app (op U))) z w

/-- **The map is unital.** -/
theorem coneTotalMap_one (U : Opens (ProjectiveSpectrum.top 𝒜)) :
    coneTotalMap 𝒜 U 1 = 1 := by
  rw [Stacks.GradedAlgebra.one_eq_incl (nonnegTwistPresheafAlgebra 𝒜) (op U),
    coneTotalMap_incl]
  exact coneIota_one 𝒜 U

/-- **The map is multiplicative.** -/
@[stacks 0EKG "the comparison from the objectwise direct sum of the homogeneous pieces of the \
nonnegative twist algebra to the functions on the cone is multiplicative, over every open of P"]
theorem coneTotalMap_mul (U : Opens (ProjectiveSpectrum.top 𝒜))
    (z w : (nonnegTwistPresheafAlgebra 𝒜).Total (op U)) :
    coneTotalMap 𝒜 U (z * w) = coneTotalMap 𝒜 U z * coneTotalMap 𝒜 U w := by
  induction z using Stacks.GradedAlgebra.incl_induction with
  | zero => simp
  | incl i x =>
    induction w using Stacks.GradedAlgebra.incl_induction with
    | zero => simp
    | incl j y =>
      rw [Stacks.GradedAlgebra.incl_mul_incl, coneTotalMap_incl, coneTotalMap_incl,
        coneTotalMap_incl]
      exact coneIota_mul 𝒜 i j U x y
    | add w w' hw hw' => simp only [mul_add, coneTotalMap_add, hw, hw']
  | add z z' hz hz' => simp only [add_mul, coneTotalMap_add, hz, hz']

/-- **The degreewise inclusions as a ring homomorphism `Γ(U, ⨁_{m ≥ 0} 𝒪_P(m)) →+* Γ(L, π⁻¹U)`.**
The sections of the ungraded realization of the algebra of nonnegative twists over `U` map to the
functions on the part of the cone lying over `U`, degreewise by the inclusion of the homogeneous
piece. -/
@[stacks 0EKG "the degreewise inclusions as a ring homomorphism from the sections of the \
ungraded realization of the nonnegative twist algebra to the functions on the cone, over every \
open of P, for the truncation cone"]
def coneTotalRingHom (U : Opens (ProjectiveSpectrum.top 𝒜)) :
    (nonnegTwistPresheafAlgebra 𝒜).Total (op U) →+* coneSections 𝒜 U where
  toFun := coneTotalMap 𝒜 U
  map_one' := coneTotalMap_one 𝒜 U
  map_mul' := coneTotalMap_mul 𝒜 U
  map_zero' := coneTotalMap_zero 𝒜 U
  map_add' := coneTotalMap_add 𝒜 U

/-- The ring homomorphism is the degreewise inclusion on each homogeneous summand. -/
theorem coneTotalRingHom_incl (U : Opens (ProjectiveSpectrum.top 𝒜)) (m : ℤ)
    (x : (nonnegTwistingSheaf 𝒜 m).val.obj (op U)) :
    coneTotalRingHom 𝒜 U ((nonnegTwistPresheafAlgebra 𝒜).incl m x) =
      (coneIota 𝒜 m).val.app (op U) x :=
  coneTotalMap_incl 𝒜 U m x

end Stacks.AlgebraicGeometry.ProjConeTwist

end
