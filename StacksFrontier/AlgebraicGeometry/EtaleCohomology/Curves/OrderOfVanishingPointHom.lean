module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.OrderOfVanishingSupport
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The order of vanishing at one point, as a homomorphism on the units of the function field

The second map of the divisor sequence of Stacks 03RM,
`j_* 𝐆_{m,K} ⟶ ⨁_x i_{x,*} ℤ`,
has one component for each closed point, and that component must be a homomorphism of abelian
groups: its source is the group of sections of `j_* 𝐆_{m,K}`, written additively, and its target
is `ℤ`. The content of the component is the order of vanishing at the point, which is
multiplicative in the rational function, so this is a matter of packaging — but the packaging is
what a morphism of abelian sheaves asks for, and it is what
`AlgebraicGeometry.Scheme.ord` does not supply: `ord` is a function of two arguments with a junk
value at `0`, and its multiplicativity `AlgebraicGeometry.Scheme.ord_mul` is conditional on both
arguments being nonzero.

Restricting to the *units* of the function field removes the condition, and this file records the
resulting homomorphism at a single point. It is the pointwise form of
`AlgebraicGeometry.Scheme.principalDivisorHom`, which assembles the same data over all points at
once into an algebraic cycle; the pointwise form needs no finiteness hypothesis, since no support
condition is being checked.

## Main definitions

* `AlgebraicGeometry.Scheme.ordAddMonoidHom`: **the order of vanishing at a point of a locally
  Noetherian integral scheme, as a homomorphism from the units of the function field, written
  additively, to `ℤ`.**

## Main results

* `AlgebraicGeometry.Scheme.ordAddMonoidHom_eq_zero_of_coheight_ne_one`: the homomorphism is zero
  at a point that is not of codimension one, so on a curve only the non-generic points
  contribute.
* `AlgebraicGeometry.Scheme.principalDivisorHom_apply_eq_ordAddMonoidHom`: the divisor of a unit
  of the function field has the homomorphism's values as its coefficients.
* `AlgebraicGeometry.IsCurve.finite_support_ordAddMonoidHom`: on a locally Noetherian curve the
  homomorphism is nonzero at only finitely many points, which is the finiteness that makes the
  family of components of the second map of the divisor sequence a section of a coproduct.

## Implementation notes

The source is `Additive (↥X.functionField)ˣ` rather than a multiplicative group, matching
`AlgebraicGeometry.Scheme.principalDivisorHom` and the additive coefficients
`AddCommGrpCat` in which this library computes étale cohomology: the sheaf `𝐆_m` of
`Stacks.Kummer.multiplicativeSheaf` is the additive group of the units of the structure sheaf.

No hypothesis of codimension one on the point is imposed. `AlgebraicGeometry.Scheme.ord` is total
and takes the value `0` off codimension one, so the homomorphism exists at every point and is
zero where the order of vanishing is not meaningful; this is what lets a consumer index the family
of components by all points, or by the closed points, without carrying a codimension hypothesis.
-/

@[expose] public noncomputable section

open CategoryTheory Order TopologicalSpace
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry

namespace Scheme

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- **The order of vanishing at a point of a locally Noetherian integral scheme, as a homomorphism
from the units of the function field, written additively, to `ℤ`.**

Multiplicativity of the order of vanishing, `AlgebraicGeometry.Scheme.ord_mul`, is conditional on
both arguments being nonzero; on the units of the function field the condition is automatic, so
the order of vanishing at a fixed point becomes a homomorphism of abelian groups. This is the form
in which it is a component of the second map `j_* 𝐆_{m,K} ⟶ ⨁_x i_{x,*} ℤ` of the divisor sequence
of Stacks 03RM. -/
@[ega "IV 21.6.7" "special case"]
def ordAddMonoidHom (x : X) : Additive ((↥X.functionField)ˣ) →+ ℤ where
  toFun g := ord ((Additive.toMul g : (↥X.functionField)ˣ) : ↥X.functionField) x
  map_zero' := by simp
  map_add' g h := by simp

/-- The value of `AlgebraicGeometry.Scheme.ordAddMonoidHom x` at `g` is the order of vanishing at
`x` of the underlying rational function of `g`. -/
@[simp]
theorem ordAddMonoidHom_apply (x : X) (g : Additive ((↥X.functionField)ˣ)) :
    ordAddMonoidHom x g = ord ((Additive.toMul g : (↥X.functionField)ˣ) : ↥X.functionField) x :=
  rfl

/-- **The order of vanishing at a point that is not of codimension one is trivial.** On a curve
this leaves only the non-generic points, where the local ring has dimension one. -/
@[simp]
theorem ordAddMonoidHom_eq_zero_of_coheight_ne_one {x : X} (hx : coheight x ≠ 1) :
    ordAddMonoidHom x = 0 :=
  AddMonoidHom.ext fun _ => ord_eq_zero_of_coheight_neq_one hx _

/-- **The coefficients of the divisor of a unit of the function field are the values of the order
of vanishing at the points.** The two packagings of the order of vanishing agree: the algebraic
cycle `AlgebraicGeometry.Scheme.principalDivisorHom` collects over all points at once what
`AlgebraicGeometry.Scheme.ordAddMonoidHom` gives at one. -/
theorem principalDivisorHom_apply_eq_ordAddMonoidHom [NoetherianSpace X]
    (g : Additive ((↥X.functionField)ˣ)) (x : X) :
    principalDivisorHom g x = ordAddMonoidHom x g :=
  rfl

end Scheme

namespace IsCurve

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve k f]
  [IsLocallyNoetherian X]

/-- **On a locally Noetherian curve the order of vanishing of a unit of the function field is
nonzero at only finitely many points.**

This is `AlgebraicGeometry.IsCurve.finite_support_ord` for the homomorphism form of the order of
vanishing: the family of components of the second map of the divisor sequence of Stacks 03RM,
evaluated on a section, has finite support, which is what makes it a section of the coproduct
`⨁_x i_{x,*} ℤ`. -/
theorem finite_support_ordAddMonoidHom (g : Additive ((↥X.functionField)ˣ)) :
    {x : X | Scheme.ordAddMonoidHom x g ≠ 0}.Finite :=
  finite_support_ord f _

end IsCurve

end AlgebraicGeometry

end
