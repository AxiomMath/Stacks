module

public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsCompConjugate
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.RingCohomologyMapNaturality

/-!
# The composition isomorphism of derived extension of scalars along an equation, conjugated

## Main results

* `StacksDraft.DerivedInverseLimit.conjugateEquiv_totalDerivedExtensionScalarsCompOfEq_inv`: for
  ring maps `f : A →+* B`, `g : B →+* C` and `c : A →+* C` with `g ∘ f = c`, the conjugate of the
  inverse of `totalDerivedExtensionScalarsCompOfEq f g c hc` under the derived change-of-rings
  adjunctions is `derivedRestrictScalarsComp f g c`.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace StacksDraft.DerivedInverseLimit

universe u

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C)

/-- For `g ∘ f = c`, the conjugate of the inverse of
`totalDerivedExtensionScalarsCompOfEq f g c hc`, under the derived change-of-rings adjunctions,
is `derivedRestrictScalarsComp f g c`. -/
theorem conjugateEquiv_totalDerivedExtensionScalarsCompOfEq_inv (c : A →+* C)
    (hc : g.comp f = c) :
    conjugateEquiv ((RingTheory.TorIndependence.totalDerivedExtensionScalarsAdjunction f).comp
        (RingTheory.TorIndependence.totalDerivedExtensionScalarsAdjunction g))
      (RingTheory.TorIndependence.totalDerivedExtensionScalarsAdjunction c)
      (RingTheory.TorIndependence.totalDerivedExtensionScalarsCompOfEq f g c hc).inv =
      (derivedRestrictScalarsComp.{u, u} f g c hc.symm).hom := by
  subst hc
  rw [RingTheory.TorIndependence.totalDerivedExtensionScalarsCompOfEq_rfl]
  exact conjugateEquiv_totalDerivedExtensionScalarsComp_inv f g

end StacksDraft.DerivedInverseLimit

end
