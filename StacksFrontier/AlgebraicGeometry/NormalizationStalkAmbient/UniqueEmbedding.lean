module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.NormalizationQuotient.Defs

/-!
# The canonical embedding of the normalization stalk in the total ring of fractions

For a reduced scheme `X` the stalk `A' = (ν_* 𝒪_{X^ν})_x` of the pushforward of the structure
sheaf of the normalization is the integral closure of the local ring `A = 𝒪_{X,x}` in the total
ring of fractions of `A`.  That identification is *canonical*: there is exactly one `A`-algebra
map `A' ⟶ Frac A` which is injective with image the integral closure.

## Main results

* `Subalgebra.algHom_eq_id_of_fractionRing`: an `A`-algebra endomorphism of a subalgebra of the
  total ring of fractions of `A` is the identity.
* `AlgebraicGeometry.existsUnique_algHom_normalizationPushforwardStalk_fractionRing`: the
  canonical embedding of the normalization stalk into the total ring of fractions is the unique
  injective `A`-algebra map with image the integral closure.

## Implementation notes

Uniqueness comes from a statement about subalgebras of `Frac A` alone: an element of such a
subalgebra is `a / b` for some `a : A` and some non-zerodivisor `b : A`, the relation
`b • y = a` is preserved by any `A`-algebra map, and `b` is a unit in `Frac A`, so `y` is
determined.  The hypotheses of [Stacks Project, Tag 0C1R] on the dimension and on the point
being closed are not used; neither is the Nagata hypothesis, which enters only through the
finiteness of irreducible components needed to form the normalization at all.

## References

* [Stacks Project, Tag 0C1R](https://stacks.math.columbia.edu/tag/0C1R)
* [Stacks Project, Tag 0C3B](https://stacks.math.columbia.edu/tag/0C3B)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry

universe u

namespace Subalgebra

/-- An `A`-algebra endomorphism of a subalgebra of the total ring of fractions of `A` is the
identity: every element of the subalgebra is a fraction `a / b` with `a : A` and `b` a
non-zerodivisor of `A`, and both are fixed. -/
public theorem algHom_eq_id_of_fractionRing {A : Type*} [CommRing A]
    (S : Subalgebra A (FractionRing A)) (α : S →ₐ[A] S) : α = AlgHom.id A S := by
  refine AlgHom.ext fun y => Subtype.ext ?_
  set p := IsLocalization.sec (nonZeroDivisors A) (y : FractionRing A)
  have hby := IsLocalization.sec_spec (nonZeroDivisors A) (y : FractionRing A)
  have hmul : algebraMap A S (p.2 : A) * y = algebraMap A S p.1 := by
    refine Subtype.ext ?_
    change algebraMap A (FractionRing A) (p.2 : A) * (y : FractionRing A) = _
    simpa [mul_comm] using hby
  have hcoe : ∀ z : S, algebraMap A S (p.2 : A) * z = algebraMap A S p.1 →
      algebraMap A (FractionRing A) (p.2 : A) * (z : FractionRing A) =
        algebraMap A (FractionRing A) p.1 := fun z h => by
    simpa using congrArg (fun z : S => (z : FractionRing A)) h
  refine (IsLocalization.map_units (FractionRing A) p.2).mul_left_cancel
    ((hcoe _ ?_).trans (hcoe y hmul).symm)
  simpa using congrArg α hmul

end Subalgebra

namespace AlgHom

/-- An algebra identified with the integral closure of `A` in the total ring of fractions of `A`
carries exactly one injective `A`-algebra map to `Frac A` with image that integral closure. -/
public theorem existsUnique_injective_range_eq_integralClosure {A B : Type*} [CommRing A]
    [CommRing B] [Algebra A B]
    (e : B ≃ₐ[A] integralClosure A (FractionRing A)) :
    ∃! f : B →ₐ[A] FractionRing A,
      Function.Injective f ∧ f.range = integralClosure A (FractionRing A) := by
  set C := integralClosure A (FractionRing A)
  refine ⟨C.val.comp e.toAlgHom, ⟨Subtype.val_injective.comp e.injective, ?_⟩, ?_⟩
  · refine le_antisymm (fun y hy => ?_) fun y hy => ?_
    · obtain ⟨z, rfl⟩ := hy
      exact (e z).property
    · exact ⟨e.symm ⟨y, hy⟩, by simp⟩
  · intro g hg
    let gC : B →ₐ[A] C := g.codRestrict C fun z => hg.2 ▸ ⟨z, rfl⟩
    have hα : gC.comp e.symm.toAlgHom = AlgHom.id A C :=
      Subalgebra.algHom_eq_id_of_fractionRing C _
    have hcomp : gC = e.toAlgHom :=
      AlgHom.ext fun z => by simpa using DFunLike.congr_fun hα (e z)
    calc g = C.val.comp gC := rfl
      _ = C.val.comp e.toAlgHom := congrArg _ hcomp

end AlgHom

namespace AlgebraicGeometry

open Stacks.NormalizationStalkAmbient
open Stacks.AlgebraicGeometry.NormalizationQuotient

/-- **Stacks Project, Tag 0C1R.** At a point of a reduced scheme the stalk of the pushforward of
the structure sheaf of the normalization carries exactly one injective algebra map into the total
ring of fractions of the local ring whose image is the integral closure: the canonical embedding
of the normalization stalk.

Neither the dimension-one hypothesis nor the closedness of the point is used, and the Nagata
hypothesis of the source enters only through the finiteness of irreducible components needed to
form the normalization. -/
@[stacks 0C1R "normalization_stalk"]
public theorem existsUnique_algHom_normalizationPushforwardStalk_fractionRing
    (X : Scheme.{u}) [IsReduced X]
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) (x : X) :
    letI : Algebra (X.presheaf.stalk x) (normalizationPushforwardStalk X hX x) :=
      normalizationPushforwardStalkAlgebra X hX x
    ∃! f : normalizationPushforwardStalk X hX x →ₐ[X.presheaf.stalk x]
        FractionRing (X.presheaf.stalk x),
      Function.Injective f ∧
        f.range = integralClosure (X.presheaf.stalk x) (FractionRing (X.presheaf.stalk x)) := by
  let : Algebra (X.presheaf.stalk x) (normalizationPushforwardStalk X hX x) :=
    normalizationPushforwardStalkAlgebra X hX x
  exact AlgHom.existsUnique_injective_range_eq_integralClosure
    (normalizationStalkAlgEquivIntegralClosureSelf X hX x)

end AlgebraicGeometry
