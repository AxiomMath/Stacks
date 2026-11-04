module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicPullbackExact
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentModulePullback

/-!
# Exactness of the inverse image of coherent adic systems along a flat morphism

Let `f : X' ⟶ X` be a flat morphism of Noetherian algebraic spaces over a scheme `S`, let
`𝓘 ⊆ 𝒪_X` be a quasi-coherent sheaf of ideals and let `𝓘' ⊆ 𝒪_{X'}` be a quasi-coherent sheaf
of ideals with which the inverse image of modules is compatible, in the sense of
`AlgebraicGeometry.Space.IdealPowerMultipleCompatible`.  **This file proves that the functor
`f^* : Coh(X, 𝓘) ⥤ Coh(X', 𝓘')` is exact.**  Part (3) of Stacks 089P is the instance
`𝓘' = f⁻¹𝓘 · 𝒪_{X'}`, `AlgebraicGeometry.Space.coherentAdicInverseImage_exact`, where the
quasi-coherence of `𝓘'` and the compatibility are proved rather than assumed.

The exactness argument is
`AlgebraicGeometry.Space.coherentAdicPullback_exact_of_preservesCoherence` of
`StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicPullbackExact`, which carries one hypothesis
more: a witness that termwise inverse image takes a coherent `𝒪_X`-module to a coherent
`𝒪_{X'}`-module.  That is free, because `f` is a morphism of *Noetherian* algebraic spaces, and it
is `AlgebraicGeometry.Space.isCoherent_modulePullback` applied to the local Noetherianity of `X'`
— the third component of the Noetherian hypothesis `hN'`.

## Main results

* `AlgebraicGeometry.Space.coherentAdicPullback_exact` — **for a flat morphism of Noetherian
  algebraic spaces the inverse image functor on coherent adic systems is exact.**
* `AlgebraicGeometry.Space.preservesFiniteLimits_coherentAdicPullback` — the half of it which
  flatness supplies.

## Implementation notes

The file exists only to apply the discharge, and that is why it is a file rather than two more
declarations in `StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicPullbackExact`: the discharge
needs `AlgebraicGeometry.Space.isCoherent_modulePullback`, and that file is kept clear of its
import closure.

Both statements name the discharge inside the functor they are about, since
`AlgebraicGeometry.Space.coherentAdicPullback` takes the coherence witness as an argument and the
functor cannot be written without one.  The witness is a proof, not a hypothesis: nothing about it
is assumed here.

## References

* [Stacks Project, Tag 089P](https://stacks.math.columbia.edu/tag/089P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X X' : AlgebraicSpaces B S hS} (f : X' ⟶ X)
    (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))).Submodule)
    (𝓘' : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X'.1 X'.2).O))).Submodule)
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (hN : IsNoetherian B S hS hZ X.1) (hN' : IsNoetherian B S hS hZ X'.1)
    (hIcart : IsCartesianOnAffineCharts 𝓘.toSheafOfModules)
    (hIcart' : IsCartesianOnAffineCharts 𝓘'.toSheafOfModules)
    (hw : IdealPowerMultipleCompatible B S hS (modulePullback B S hS f) 𝓘 𝓘')

include hZ hN hIcart hIcart' in
/-- **The inverse image functor along a flat morphism of Noetherian algebraic spaces is exact.**
For a flat morphism `f : X' ⟶ X` of Noetherian algebraic spaces and quasi-coherent sheaves of
ideals `𝓘 ⊆ 𝒪_X`, `𝓘' ⊆ 𝒪_{X'}` with which the inverse image is compatible, the functor
`f^* : Coh(X, 𝓘) ⥤ Coh(X', 𝓘')` preserves finite limits and finite colimits.

This is `AlgebraicGeometry.Space.coherentAdicPullback_exact_of_preservesCoherence` with its
coherence witness supplied by `AlgebraicGeometry.Space.isCoherent_modulePullback`.  Part (3) of
Stacks 089P is the instance `𝓘' = f⁻¹𝓘 · 𝒪_{X'}`,
`AlgebraicGeometry.Space.coherentAdicInverseImage_exact`. -/
theorem coherentAdicPullback_exact (hf : IsFlat B S hS f.hom) :
    exactFunctor (CoherentAdicSystems B S hS X.1 X.2 𝓘)
        (CoherentAdicSystems B S hS X'.1 X'.2 𝓘')
      (coherentAdicPullback B S hS f 𝓘 𝓘' hw
        (isCoherent_modulePullback_of_hasEtaleLocalProperty B S hS f hN'.2.2)) :=
  coherentAdicPullback_exact_of_preservesCoherence B S hS f 𝓘 𝓘' hZ hN hN' hIcart hIcart' hw
    (isCoherent_modulePullback_of_hasEtaleLocalProperty B S hS f hN'.2.2) hf

include hZ hN hIcart hIcart' in
/-- **The inverse image functor along a flat morphism of Noetherian algebraic spaces preserves
finite limits**, the half of `AlgebraicGeometry.Space.coherentAdicPullback_exact` which flatness
supplies. -/
theorem preservesFiniteLimits_coherentAdicPullback (hf : IsFlat B S hS f.hom) :
    PreservesFiniteLimits (coherentAdicPullback B S hS f 𝓘 𝓘' hw
      (isCoherent_modulePullback_of_hasEtaleLocalProperty B S hS f hN'.2.2)) :=
  ((exactFunctor_iff _).1
    (coherentAdicPullback_exact B S hS f 𝓘 𝓘' hZ hN hN' hIcart hIcart' hw hf)).1

end AlgebraicGeometry.Space

end
