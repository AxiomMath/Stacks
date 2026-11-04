module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Dualizing.DerivedHomothety.DerivedCoextensionIsDualizing
public import StacksFrontier.RingTheory.Dualizing.DualizingComplexes.MvPolynomialBaseChange
public import StacksFrontier.RingTheory.Dualizing.NormalizedShift
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.Defs

/-!
# Algebraic upper shriek preserves dualizing complexes

For a finite type homomorphism `f : R →+* A` of Noetherian rings, the algebraic upper shriek
functor of a polynomial presentation of `f` sends a dualizing complex for `R` to a dualizing
complex for `A`.

## Main results

* `Dualizing.PolynomialPresentation.upperShriekFunctor_isDualizingComplex` — [stacks 0BZL].

## Implementation notes

Upper shriek is only defined up to isomorphism, so the statement is made for an arbitrary
polynomial presentation; being a dualizing complex is invariant under isomorphism, so this is
the strongest reading and it does not depend on [stacks 0BZJ].

The proof is the one in the source: derived base change along the polynomial algebra is handled
by iterating [stacks 0A7J], derived Hom along the surjection by [stacks 0AX0], and the final
shift leaves a dualizing complex dualizing.

## References

* [Stacks Project, Tag 0BZL](https://stacks.math.columbia.edu/tag/0BZL)
-/

@[expose] public section

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

namespace PolynomialPresentation

variable {R A : Type u} [CommRing R] [CommRing A] {f : R →+* A}

/-- The derived base change attached to a presentation is extension of scalars to its polynomial
algebra. -/
private theorem derivedExtension_eq (p : PolynomialPresentation f) :
    p.derivedExtension.{u, u} = mvPolynomialExtension R p.variableCount := rfl

/-- **Stacks Project, Tag 0BZL.** Algebraic upper shriek along a finite type homomorphism of
Noetherian rings carries a dualizing complex to a dualizing complex. -/
@[stacks 0BZL]
theorem upperShriekFunctor_isDualizingComplex [IsNoetherianRing R] [IsNoetherianRing A]
    (p : PolynomialPresentation f) (K : DerivedCategory (ModuleCat.{u} R))
    (hK : IsDualizingComplex K) :
    IsDualizingComplex (p.upperShriekFunctor.{u, u}.obj K) := by
  have hP : IsNoetherianRing p.Poly := inferInstance
  have hbase : IsDualizingComplex (p.derivedExtension.{u, u}.obj K) := by
    rw [p.derivedExtension_eq]
    exact mvPolynomialBaseChange_isDualizingComplex p.variableCount K hK
  rw [p.upperShriekFunctor_obj K]
  exact isDualizingComplex_shift _
    (isDualizingComplex_derivedHom_of_finite p.toRingHom p.finite_toRingHom _ hbase)
    (p.variableCount : ℤ)

end PolynomialPresentation

end Dualizing

end
