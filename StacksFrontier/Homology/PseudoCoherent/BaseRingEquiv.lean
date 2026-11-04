module

public import StacksFrontier.Homology.PseudoCoherent.Basic
public import StacksFrontier.Homology.PseudoCoherent.ChangeOfRings

/-! # Pseudo-coherence of a module under an isomorphism of the coefficient ring

`StacksDraft.PseudoCoherence.pseudoCoherent_iff_of_ringEquiv` transports pseudo-coherence of a
complex along an isomorphism of the coefficient ring, in the derived category. A module placed in
degree zero is such a complex, and restriction of coefficients along an exact functor commutes
with that placement, so pseudo-coherence of a *module* transports as well.

The coefficient rings are allowed to lie in different universes, which is what the application
needs: a polynomial ring and the copy of it moved into the universe of an object built out of it
are isomorphic, not equal.

## Main results

* `StacksDraft.PseudoCoherence.isModulePseudoCoherent_restrictScalars_of_ringEquiv` — a
  pseudo-coherent module stays pseudo-coherent after restricting its coefficients along a ring
  isomorphism.

## References

* [Stacks Project, Tag 064T](https://stacks.math.columbia.edu/tag/064T)
-/

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

@[expose] public section

namespace StacksDraft.PseudoCoherence

universe u u' v

/-- **A pseudo-coherent module stays pseudo-coherent after restricting its coefficients along a
ring isomorphism.** -/
public theorem isModulePseudoCoherent_restrictScalars_of_ringEquiv
    {A : Type u} {B : Type u'} [Ring A] [Ring B] (e : A ≃+* B) (N : ModuleCat.{v} B)
    (h : IsModulePseudoCoherent (R := B) N) :
    IsModulePseudoCoherent (R := A) ((ModuleCat.restrictScalars e.toRingHom).obj N) :=
  IsPseudoCoherent.ofIso
    ((pseudoCoherent_iff_of_ringEquiv e
      ((DerivedCategory.singleFunctor (ModuleCat.{v} B) 0).obj N)).2.1 h)
    (((ModuleCat.restrictScalars.{v} e.toRingHom).mapDerivedCategorySingleFunctor 0).app N)

end StacksDraft.PseudoCoherence

end
