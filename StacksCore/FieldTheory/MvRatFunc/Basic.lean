module

public import Mathlib.FieldTheory.RatFunc.Basic

/-! # Multivariate rational functions -/

@[expose] public section

/-- **Stacks 030E** (part 2).
The field of multivariate rational functions in the variables indexed by `σ` over `R`,
defined as the fraction ring of the multivariate polynomial ring `MvPolynomial σ R`. -/
@[stacks 030E "2"]
abbrev MvRatFunc (σ R : Type*) [CommRing R] : Type _ :=
  FractionRing (MvPolynomial σ R)

namespace MvRatFunc
variable {R σ : Type*} [CommRing R] [IsDomain R]

/-- The algebraic equivalence between `RatFunc R` and `MvRatFunc Unit R`. -/
noncomputable def ofRatFunc (R : Type*) [CommRing R] [IsDomain R] :
    RatFunc R ≃ₐ[R] MvRatFunc Unit R :=
  (RatFunc.toFractionRingAlgEquiv R R).trans <|
    IsFractionRing.algEquivOfAlgEquiv (MvPolynomial.uniqueAlgEquiv R Unit).symm

/-- Two ring homomorphisms out of `MvRatFunc σ R` are equal as soon as they agree on the
image of the constants `R` and on each variable `X i`. -/
@[ext high] theorem ext_ringHom {R σ A : Type*} [CommRing R] [Ring A]
    {f g : MvRatFunc σ R →+* A}
    (hC : f.comp (algebraMap R (MvRatFunc σ R)) = g.comp (algebraMap R (MvRatFunc σ R)))
    (hX : ∀ i, f (algebraMap (MvPolynomial σ R) (MvRatFunc σ R) (.X i)) =
      g (algebraMap (MvPolynomial σ R) (MvRatFunc σ R) (.X i))) :
    f = g :=
  IsLocalization.ringHom_ext (nonZeroDivisors (MvPolynomial σ R)) <|
    MvPolynomial.ringHom_ext (fun r ↦ congr($hC r)) hX

/-- Two `R`-algebra homomorphisms out of `MvRatFunc σ R` are equal as soon as they agree on
each variable `X i`. -/
@[ext high] theorem ext_algHom {R σ A : Type*} [CommRing R] [Ring A] [Algebra R A]
    {f g : MvRatFunc σ R →ₐ[R] A}
    (hX : ∀ i, f (algebraMap (MvPolynomial σ R) (MvRatFunc σ R) (.X i)) =
      g (algebraMap (MvPolynomial σ R) (MvRatFunc σ R) (.X i))) :
    f = g := AlgHom.coe_ringHom_injective <| ext_ringHom (by simp) hX

end MvRatFunc
