module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Homology.PseudoCoherent.BaseChange
public import StacksFrontier.RingTheory.Dualizing.TrivialDuality.BaseChange

/-!
# The base-change map for derived Hom, at the constructed derived extension of scalars

`Dualizing.derivedHomBaseChange` builds the map

`RHom_R(A, -) ⊗ᴸ_A (A ⊗_R R') ⟶ RHom_{R'}(A ⊗_R R', - ⊗ᴸ_R R')`

of [Stacks, Equation 47.14.0.1] from an *arbitrary* pair of functors certified as the two
derived extensions of scalars. This file removes those parameters: it instantiates the
construction at `StacksDraft.PseudoCoherence.extendScalarsDerived`, the total left derived
functor of extension of scalars, whose comparison map
`StacksDraft.PseudoCoherence.extendScalarsDerivedCounit` and universal property
`StacksDraft.PseudoCoherence.isLeftDerivedFunctor_extendScalarsDerivedCounit` are proved rather
than assumed. The result is a natural transformation between two concrete functors, which a
`∀ D, P D` statement over certified functors does not provide.

## Main definitions

* `Dualizing.derivedHomBaseChangeCanonical` — the base-change map of
  [Stacks, Equation 47.14.0.1] at the constructed derived extensions of scalars.

## Main results

* `Dualizing.derivedHomBaseChangeCanonical_eq` — it is the instantiation of
  `Dualizing.derivedHomBaseChange`, so the characterization
  `Dualizing.derivedHomBaseChange_eq` applies to it verbatim.
* `Dualizing.derivedHomBaseChangeCanonical_app` — the resulting characterization: after the
  restriction/base-change identification, the adjoint transpose of the component at `K` is the
  derived extension along `R → R'` of the evaluation counit `Res_A^R RHom_R(A, K) ⟶ K`.

## Implementation notes

**Universes.** `StacksDraft.PseudoCoherence.extendScalarsDerived` is single-universe: it is
defined for rings in `Type u` and modules in `Type u`, because its construction goes through
`CochainComplex.isKProjective_of_projective` and the acyclicity argument of
`StacksDraft.PseudoCoherence.acyclic_extendScalars_of_projective`, both written at
`ModuleCat.{u}` over `Type u`. `Dualizing.derivedHomBaseChange`, by contrast, carries
independent universes `uR`, `uA`, `uRp` for the three rings and `v` for the module size. The
instantiation is therefore stated at the common universe `uR = uA = uRp = v = u`: the three
rings `R`, `A`, `R'` all live in `Type u` and the modules in `Type u`. The parametrized
`Dualizing.derivedHomBaseChange` keeps its independent universes and its own `@[stacks 0E29]`
attribute; nothing here narrows it. Lifting this instantiation to independent universes needs
`extendScalarsDerived` at independent universes first, which the library does not have.

The pushout ring `A ⊗_R R'` is `TensorProduct R A R'`, which lies in `Type u` as well, so the
second derived extension of scalars is `extendScalarsDerived (algebraMap A (TensorProduct R A R'))`
and no universe lift intervenes.

Tor independence of `A` and `R'` over `R` is still a hypothesis: it is what the source assumes
before the map exists at all.

## References

* [Stacks Project, Tag 0E29](https://stacks.math.columbia.edu/tag/0E29)
* [Stacks Project, Tag 0E28](https://stacks.math.columbia.edu/tag/0E28)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor
open StacksDraft.PseudoCoherence

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The canonical base-change map
`RHom_R(A, -) ⊗ᴸ_A (A ⊗_R R') ⟶ RHom_{R'}(A ⊗_R R', - ⊗ᴸ_R R')`
of [Stacks, Equation 47.14.0.1], functorial in the object of `D(R)`, with the two derived
extensions of scalars taken to be the constructed functor
`StacksDraft.PseudoCoherence.extendScalarsDerived` rather than certified parameters.

All three rings and the module size live in the single universe `u`, which is the generality
`extendScalarsDerived` is available in. -/
@[stacks 0E29 "at the constructed derived extensions of scalars; one universe for all rings"]
noncomputable def derivedHomBaseChangeCanonical
    {R : Type u} {A : Type u} {R' : Type u} [CommRing R] [CommRing A] [CommRing R']
    [Algebra R A] [Algebra R R']
    (hTor : RingTheory.TorIndependence.TorIndependent R A R') :
    derivedHom.{u, u, u} (algebraMap R A) ⋙
        extendScalarsDerived (algebraMap A (TensorProduct R A R')) ⟶
      extendScalarsDerived (algebraMap R R') ⋙ derivedHom.{u, u, u}
        (Algebra.TensorProduct.includeRight :
          R' →ₐ[R] TensorProduct R A R').toRingHom :=
  derivedHomBaseChange hTor
    (extendScalarsDerived (algebraMap R R'))
    (extendScalarsDerivedCounit (algebraMap R R'))
    (isLeftDerivedFunctor_extendScalarsDerivedCounit (algebraMap R R'))
    (extendScalarsDerived (algebraMap A (TensorProduct R A R')))
    (extendScalarsDerivedCounit (algebraMap A (TensorProduct R A R')))
    (isLeftDerivedFunctor_extendScalarsDerivedCounit
      (algebraMap A (TensorProduct R A R')))

/-- The canonical base-change map is the instantiation of the parametrized one, so every
statement proved about `Dualizing.derivedHomBaseChange` applies to it. -/
theorem derivedHomBaseChangeCanonical_eq
    {R : Type u} {A : Type u} {R' : Type u} [CommRing R] [CommRing A] [CommRing R']
    [Algebra R A] [Algebra R R']
    (hTor : RingTheory.TorIndependence.TorIndependent R A R') :
    derivedHomBaseChangeCanonical hTor =
      derivedHomBaseChange hTor
        (extendScalarsDerived (algebraMap R R'))
        (extendScalarsDerivedCounit (algebraMap R R'))
        (isLeftDerivedFunctor_extendScalarsDerivedCounit (algebraMap R R'))
        (extendScalarsDerived (algebraMap A (TensorProduct R A R')))
        (extendScalarsDerivedCounit (algebraMap A (TensorProduct R A R')))
        (isLeftDerivedFunctor_extendScalarsDerivedCounit
          (algebraMap A (TensorProduct R A R'))) :=
  rfl

/-- The defining characterization of the canonical base-change map: after the
restriction/base-change identification supplied by Tor independence, its adjoint transpose at
`K` is the derived extension along `R → R'` of the evaluation counit
`Res_A^R RHom_R(A, K) ⟶ K`. -/
theorem derivedHomBaseChangeCanonical_app
    {R : Type u} {A : Type u} {R' : Type u} [CommRing R] [CommRing A] [CommRing R']
    [Algebra R A] [Algebra R R']
    (hTor : RingTheory.TorIndependence.TorIndependent R A R')
    (K : DerivedCategory (ModuleCat.{u} R)) :
    (derivedHomBaseChangeCanonical hTor).app K =
      (derivedHomAdjunction.{u, u, u}
        (Algebra.TensorProduct.includeRight :
          R' →ₐ[R] TensorProduct R A R').toRingHom).homEquiv _ _
        ((restrictionBaseChangeIso hTor
            (extendScalarsDerived (algebraMap R R'))
            (extendScalarsDerivedCounit (algebraMap R R'))
            (isLeftDerivedFunctor_extendScalarsDerivedCounit (algebraMap R R'))
            (extendScalarsDerived (algebraMap A (TensorProduct R A R')))
            (extendScalarsDerivedCounit (algebraMap A (TensorProduct R A R')))
            (isLeftDerivedFunctor_extendScalarsDerivedCounit
              (algebraMap A (TensorProduct R A R')))).hom.app K ≫
          (extendScalarsDerived (algebraMap R R')).map
            ((derivedHomAdjunction.{u, u, u} (algebraMap R A)).counit.app K)) :=
  rfl

end Dualizing

end
