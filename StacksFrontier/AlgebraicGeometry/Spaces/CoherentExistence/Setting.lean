module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentCompletionProperSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.FormalAlgebraization
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperGlobalSections.BaseIdeal

/-!
# The setting of Grothendieck's existence theorem for algebraic spaces

Let `A` be a Noetherian ring complete with respect to an ideal `I` and let `X` be an algebraic
space over `Spec A`, with structure morphism `f : X ⟶ Spec A` to the base read as the terminal
object `AlgebraicGeometry.Space.baseObject` of the big fppf category over itself.  This file fixes
the local Noetherianity of `X` which the completion functor of Stacks 08B4 is indexed by; the
ideal sheaf `𝓘 = I 𝒪_X` of Situation 08B7 is the base's `AlgebraicGeometry.Space.baseIdealSheaf`,
quasi-coherent by `AlgebraicGeometry.Space.isQuasicoherentOnSite_baseIdealSheaf`, so that
Grothendieck's existence theorem (Stacks 08BE) can be stated as the equivalence of the arrow
`AlgebraicGeometry.Space.completionFunctorProperOver` of Stacks 08B8.

## Main results

* `AlgebraicGeometry.Space.hasEtaleLocalProperty_isLocallyNoetherian_of_isFiniteType_baseObject`
  — an algebraic space locally of finite type over `Spec A`, `A` Noetherian, has locally
  Noetherian étale charts.

## References

* [Stacks Project, Tag 08B7](https://stacks.math.columbia.edu/tag/08B7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (A : Type u) [CommRing A] (I : Ideal A) (B : BigFppfSite.{u})
  (hA : B.Contains (Spec (.of A)))
  {X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u}
  (hX : IsAlgebraicSpace B (Spec (.of A)) hA X) (f : X ⟶ yoneda.obj (baseObject A B hA))

include hX in
/-- An algebraic space locally of finite type over the spectrum of a Noetherian ring has locally
Noetherian étale charts. -/
theorem hasEtaleLocalProperty_isLocallyNoetherian_of_isFiniteType_baseObject
    [IsNoetherianRing A] (hf : IsLocallyOfFiniteType B (Spec (.of A)) hA f) :
    HasEtaleLocalProperty B (Spec (.of A)) hA X (fun T : Scheme.{u} => IsLocallyNoetherian T) :=
  hasEtaleLocalProperty_isLocallyNoetherian_of_isLocallyOfFiniteType B (Spec (.of A)) hA hX
    (isAlgebraicSpace_yoneda B (Spec (.of A)) hA (baseObject A B hA)) f hf
    (hasEtaleLocalProperty_isLocallyNoetherian_baseObject A B hA)

end AlgebraicGeometry.Space

end
