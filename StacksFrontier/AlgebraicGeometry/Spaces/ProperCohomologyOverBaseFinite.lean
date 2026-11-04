module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyOverBaseUniverseLift
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentUniverseDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperCohomologyFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperModuleCohomologyFinite

/-!
# Finite cohomology over the base of a coherent module on a proper algebraic space

[Stacks, Tag 08AS] asserts that for a Noetherian ring `A`, a proper morphism of algebraic spaces
`f : X ⟶ Spec A` and a coherent `𝒪_X`-module `F`, every cohomology module `H^i(X, F)` is a finite
`A`-module.  This file states and proves it for `AlgebraicGeometry.Space.cohomologyOverBase`,
the cohomology over the base ring of an `𝒪_X`-module in `Modules.{u, max (u + 1) w}`.  That is
the module universe at which cohomology on the small étale site is defined for every universe of
sections containing that of the site.

## Main results

* `AlgebraicGeometry.Space.moduleFinite_cohomologyOverBase_of_isProper_of_isCoherent`:
  **[Stacks, Tag 08AS]**.

## Implementation notes

The finiteness itself is proved on base at the module universe `u` of the structure rings, which
is where direct images of modules along a morphism of algebraic spaces exist:
`AlgebraicGeometry.Space.moduleFinite_cohomology_of_isProper`, via the dévissage of Stacks 08AN,
Chow's lemma and Serre vanishing, as in the source's proof of Stacks 08AR.  Here it is moved to
the module universe of `AlgebraicGeometry.Space.cohomologyOverBase` in two steps.

* A coherent module in `Modules.{u, max (u + 1) w}` is, up to isomorphism, the universe lift of a
  coherent module in `Modules.{u, u}`
  (`AlgebraicGeometry.Space.exists_iso_uliftForPresentation_of_isCoherent`).
* The cohomology over the base of a universe lift is the universe lift of the universe-`u`
  cohomology, so the two are finite together:
  `AlgebraicGeometry.Space.moduleFinite_cohomologyOverBase_uliftForPresentation_iff_rightDerived`.

Finiteness then transports along the isomorphism
(`AlgebraicGeometry.Space.moduleFinite_cohomologyOverBase_of_iso`).  The base's conditional
`AlgebraicGeometry.Space.moduleFinite_cohomologyOverBase_of_isProper` carries finiteness below a
vanishing bound as a hypothesis; the declaration here carries nothing.

## References

* [Stacks Project, Tag 08AS](https://stacks.math.columbia.edu/tag/08AS)
* [Stacks Project, Tag 08AR](https://stacks.math.columbia.edu/tag/08AR)
-/

@[expose] public section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.Space

/-- **Stacks 08AS.**  Let `A` be a Noetherian ring, `f : X ⟶ Spec A` a proper morphism of
algebraic spaces and `F` a coherent `𝒪_X`-module.  Then `Hⁱ(X, F)` is a finite `A`-module for
every `i ≥ 0`.

Here `Hⁱ(X, F)` is `AlgebraicGeometry.Space.cohomologyOverBase`, at any module universe
`max (u + 1) w`.  `F` is the universe lift of a coherent module at the universe `u` of the
structure rings, where the finiteness is
`AlgebraicGeometry.Space.moduleFinite_cohomology_of_isProper` (the affine case of Stacks 08AR),
and the cohomology over the base of a lift is the lift of the cohomology. -/
@[stacks 08AS]
theorem moduleFinite_cohomologyOverBase_of_isProper_of_isCoherent
    (A : Type u) [CommRing A] (B : BigFppfSite.{u}) (hA : B.Contains (Spec (.of A)))
    [IsNoetherianRing A]
    (X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of A)) hA X)
    (f : X ⟶ yoneda.obj (baseObject A B hA)) (hf : IsProper B (Spec (.of A)) hA f)
    (F : Modules.{u, max (u + 1) w} B (Spec (.of A)) hA X hX)
    [IsCoherent B (Spec (.of A)) hA X hX F] (i : ℕ) :
    Module.Finite A (cohomologyOverBase.{u, w} A B hA X hX F i) := by
  obtain ⟨M, hM, ⟨e⟩⟩ :=
    exists_iso_uliftForPresentation_of_isCoherent.{u, w} B (Spec (.of A)) hA X hX F
  have := hM
  have : Module.Finite A (cohomologyOverBase.{u, w} A B hA X hX
      (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, max (u + 1) w} M) i) :=
    (moduleFinite_cohomologyOverBase_uliftForPresentation_iff_rightDerived.{u, w}
      A B hA X hX M i).2 (moduleFinite_cohomology_of_isProper X hX f hf M (i := i))
  exact moduleFinite_cohomologyOverBase_of_iso.{u, w} A B hA X hX e i

end AlgebraicGeometry.Space

end
