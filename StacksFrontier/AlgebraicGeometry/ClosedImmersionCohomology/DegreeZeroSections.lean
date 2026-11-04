module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCohomology.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEpi.QuasicoherentSectionsEqualizer

/-!
# The degree-zero conclusion of Stacks 0D2M (B) is restriction of sections

`Stacks.Cohomology.FormalFunctions.exists_surjective_fibreCohomology_twistModule` — assertion (B)
of [Stacks, Tag 0D2M] over a local base — concludes that, for `d` large, the map

`H⁰ of the unit of v^* ⊣ v_*`, followed by
`Stacks.Cohomology.ClosedImmersion.cohomologyObjIsoPushforward`,

is surjective.  That composite is the cohomological spelling of the source's
`H⁰(X, ℱ(d)) ⟶ H⁰(V, v^* ℱ(d))`: it is `((Γ_X)ʀ⁰)` applied to the unit `ℱ ⟶ v_* v^* ℱ`, carried
into the cohomology of the fibre by the closed-immersion comparison of `ClosedImmersionCohomology`.

This file proves that this composite is surjective **exactly when** the elementary
restriction-of-sections map `AlgebraicGeometry.pullbackGlobalSections v N` of
`StacksFrontier/AlgebraicGeometry/Descent/EffectiveEpi/QuasicoherentSections.lean`,

`Γ(N, ⊤) ⟶ Γ((Scheme.Modules.pullback v).obj N, ⊤)`,

is surjective.  So a consumer of assertion (B) may read its conclusion as the statement in the
source's own words: every section of `v^* ℱ(d)` over the fibre is the restriction of a section of
`ℱ(d)` over `X`.  No cohomology is unwound to get there, and in particular
`cohomologyObjIsoPushforward` is never opened.

Nothing about closed immersions, properness or coherence enters: the equivalence is a
cancellation of isomorphisms, valid for an arbitrary morphism of schemes.  The
`AlgebraicGeometry.IsClosedImmersion` instance is a binder of the *statement* only, because
`cohomologyObjIsoPushforward` — whose construction is where closedness is spent — is defined for
a closed immersion and therefore appears in the hypothesis.

## Main results

Both are in the namespace `Stacks.Cohomology.ClosedImmersion`.

* `surjective_pullbackGlobalSections_iff_rightDerivedZero`: the two surjectivity statements are
  equivalent.
* `surjective_pullbackGlobalSections_of_surjective_rightDerivedZero`: the implication assertion
  (B) is consumed through, in the one-way form a caller wants.

## Implementation notes

**No `@[stacks]` attribute is attached, and none should be.**  The clause of [Stacks, Tag 0D2M]
lives at `exists_surjective_fibreCohomology_twistModule` and at the `@[stacks 0D2M]` site in
`StacksFrontier/AlgebraicGeometry/FormalFunctions/AmpleFibreTwistStalkSurjective.lean`; everything here
is a translation between two spellings of one degree-zero map, with none of the source's hypotheses
and none of its content.  Tagging a re-spelling would register the tag a second time on a
statement that proves nothing the source asserts.

**The three steps.**  Writing `F = Stacks.Cohomology.AffineBase.moduleGlobalSections X` and
`u : N ⟶ v_* v^* N` for the unit:

1. The second factor of the composite is the `.hom` of an isomorphism of `ModuleCat Γ(X, ⊤)`, so
   `CategoryTheory.epi_comp_iff_of_isIso` reduces surjectivity of the composite to surjectivity
   of `(F.rightDerived 0).map u`.  Surjectivity and `Epi` are interchanged throughout by
   `ModuleCat.epi_iff_surjective`, which is what lets a one-sided cancellation be used on a
   two-sided categorical statement.
2. `F` is an evaluation of sheaves of modules, hence left exact, so Mathlib's
   `CategoryTheory.Functor.rightDerivedZeroIsoSelf` is available at it; the naturality square of
   that isomorphism at `u` conjugates `(F.rightDerived 0).map u` into `F.map u`, and both
   conjugating maps are isomorphisms.  The same isomorphism at the same functor is packaged as
   `Stacks.Cohomology.FormalFunctions.moduleGlobalSectionsRightDerivedZeroIso`, which is that
   Mathlib term verbatim; it is used here through Mathlib rather than through that module, so no
   second copy of it is declared and this file's import set stays at two modules.
3. `F.map u` acts on sections as `u.app ⊤`, and `u.app ⊤` *is* `pullbackGlobalSections v N` on
   elements: that is `AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_unit`, which
   already records that the restriction `Γ(v^* N, v ⁻¹ᵁ ⊤) ⟶ Γ(v^* N, ⊤)` appearing in the
   definition of `pullbackGlobalSections` is the identity.  Surjectivity is therefore carried
   across by an equality of functions, with no further isomorphism to cancel.

## References

* [Stacks Project, Tag 0D2M](https://stacks.math.columbia.edu/tag/0D2M)
* [Stacks Project, Tag 01EX](https://stacks.math.columbia.edu/tag/01EX)
-/

@[expose] public section

open CategoryTheory Opposite
open scoped AlgebraicGeometry

namespace Stacks.Cohomology.ClosedImmersion

open Stacks.Cohomology.AffineBase

universe u

variable {Z X : AlgebraicGeometry.Scheme.{u}} (v : Z ⟶ X)

/-- **The degree-zero statement of [Stacks, Tag 0D2M] assertion (B) is restriction of sections.**
Zeroth cohomology of the unit of `v^* ⊣ v_*`, followed by the identification of the cohomology of
a direct image along a closed immersion with the cohomology upstairs, is surjective exactly when
the canonical map `Γ(N, ⊤) ⟶ Γ(v^* N, ⊤)` on global sections is surjective.

Both sides live in `ModuleCat Γ(X, ⊤)`, and the equivalence is a cancellation of isomorphisms:
the closed-immersion comparison is one, the canonical map from zeroth right derived global
sections to global sections is another, and the restriction along `v ⁻¹ᵁ ⊤ = ⊤` hidden inside
`AlgebraicGeometry.pullbackGlobalSections` is the identity.  No hypothesis on `v` is used; the
instance binder is present because `cohomologyObjIsoPushforward` carries it. -/
theorem surjective_pullbackGlobalSections_iff_rightDerivedZero
    [AlgebraicGeometry.IsClosedImmersion v] (N : X.Modules) :
    Function.Surjective
      ((((moduleGlobalSections X).rightDerived 0).map
            ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction v).unit.app N) ≫
          (cohomologyObjIsoPushforward v
            ((AlgebraicGeometry.Scheme.Modules.pullback v).obj N) 0).hom).hom) ↔
      Function.Surjective (AlgebraicGeometry.pullbackGlobalSections v N) := by
  set u := (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction v).unit.app N
  -- Step 3, as an equality of functions: the unit on global sections is the pullback map.
  have hsec : Function.Surjective ((moduleGlobalSections X).map u).hom ↔
      Function.Surjective (AlgebraicGeometry.pullbackGlobalSections v N) := by
    refine ⟨fun hmap t => ?_, fun hpb t => ?_⟩
    · obtain ⟨s, hs⟩ := hmap t
      exact ⟨s, (AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_unit v N s).trans hs⟩
    · obtain ⟨s, hs⟩ := hpb t
      exact ⟨s,
        (AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_unit v N s).symm.trans hs⟩
  -- Step 1: discard the closed-immersion comparison, which is an isomorphism.
  rw [← hsec, ← ModuleCat.epi_iff_surjective, ← ModuleCat.epi_iff_surjective,
    epi_comp_iff_of_isIso]
  -- Step 2: conjugate along the naturality square of `rightDerivedZeroIsoSelf` at `u`.
  rw [← epi_comp_iff_of_isIso (((moduleGlobalSections X).rightDerived 0).map u)
      ((moduleGlobalSections X).rightDerivedZeroIsoSelf.hom.app _),
    (moduleGlobalSections X).rightDerivedZeroIsoSelf.hom.naturality u, epi_comp_iff_of_epi]

/-- **Assertion (B) of [Stacks, Tag 0D2M] gives surjectivity of restriction of sections.**  The
direction of `surjective_pullbackGlobalSections_iff_rightDerivedZero` a consumer of
`Stacks.Cohomology.FormalFunctions.exists_surjective_fibreCohomology_twistModule` needs: its
degree-zero conclusion at a module `N` says precisely that every global section of `v^* N` is the
restriction of a global section of `N`. -/
theorem surjective_pullbackGlobalSections_of_surjective_rightDerivedZero
    [AlgebraicGeometry.IsClosedImmersion v] (N : X.Modules)
    (h : Function.Surjective
      ((((moduleGlobalSections X).rightDerived 0).map
            ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction v).unit.app N) ≫
          (cohomologyObjIsoPushforward v
            ((AlgebraicGeometry.Scheme.Modules.pullback v).obj N) 0).hom).hom)) :
    Function.Surjective (AlgebraicGeometry.pullbackGlobalSections v N) :=
  (surjective_pullbackGlobalSections_iff_rightDerivedZero v N).1 h

end Stacks.Cohomology.ClosedImmersion

end
