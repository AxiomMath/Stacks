module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.AffineCase
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.DenseSubsite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.DescentEffective
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The small étale sites of a universal homeomorphism are isomorphic

Let `f : X ⟶ Y` be a universal homeomorphism of schemes. Base change along `f` is an isomorphism
of the small étale site of `Y` onto the small étale site of `X`: it is an equivalence of the
underlying categories, and a sieve on a scheme étale over `Y` is covering exactly when its image
under base change is covering. This is part (1) of Stacks Project, Tag 03SI.

Both halves are now available. The categorical half is Stacks Project, Tag 04DZ,
`Stacks.Etale.etalePullback_isEquivalence`; the
covering half holds for any surjection, by
`Stacks.EtaleCohomology.functorPushforward_mem_smallEtaleTopology_iff`.

## Main results

* `Stacks.EtaleCohomology.smallEtaleBaseChange_isEquivalence_of_universalHomeomorphism` — base
  change along a universal homeomorphism is an equivalence of small étale categories, read on
  `Stacks.EtaleCohomology.smallEtaleBaseChange`.
* `Stacks.EtaleCohomology.smallEtaleSite_iso_of_universalHomeomorphism` — part (1) of Stacks
  Project, Tag 03SI.
  inclusion, now obtained from the isomorphism of sites rather than from cover-density alone.

## Implementation notes

An isomorphism of sites is rendered as the conjunction of the two conditions it asserts about
the one functor `Stacks.EtaleCohomology.smallEtaleBaseChange`: that it is an equivalence of
categories, and that it matches up the covering sieves in both directions. No separate structure
is introduced, so the statement is not weaker than the assertion it formalizes — in particular
the functor is the base-change functor itself and not an arbitrary functor isomorphic to it.

`Stacks.EtaleCohomology.smallEtaleBaseChange` is by definition the functor that Tag 04DZ is
proved about, so the categorical half transfers by unfolding; the instance arguments the functor
needs are supplied in the same way in both places.

## References

* [Stacks Project, Tag 03SI](https://stacks.math.columbia.edu/tag/03SI)
* [Stacks Project, Tag 04DZ](https://stacks.math.columbia.edu/tag/04DZ)
* [Stacks Project, Tag 04DF](https://stacks.math.columbia.edu/tag/04DF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

variable {X Y : Scheme.{u}}

/-- **Base change along a universal homeomorphism is an equivalence of small étale categories.**
This is Stacks Project, Tag 04DZ read on `Stacks.EtaleCohomology.smallEtaleBaseChange`, which is
by definition the functor the tag is proved about. -/
theorem smallEtaleBaseChange_isEquivalence_of_universalHomeomorphism (f : X ⟶ Y)
    [UniversalHomeomorphism f] : (smallEtaleBaseChange f).IsEquivalence := by
  obtain ⟨hint, hinj, hsurj⟩ :=
    (universalHomeomorphism_iff_integral_universallyInjective_surjective f).mp inferInstance
  have : IsIntegralHom f := hint
  have : UniversallyInjective f := hinj
  have : Surjective f := hsurj
  have h := Stacks.Etale.etalePullback_isEquivalence f
  exact h

/-- **Part (1) of Stacks Project, Tag 03SI: the small étale sites of a universal homeomorphism
are isomorphic.** Let `f : X ⟶ Y` be a universal homeomorphism. Base change along `f` is an
equivalence from the small étale category of `Y` to that of `X`, and a sieve on a scheme étale
over `Y` is covering exactly when its image under base change is covering.

The equivalence of categories is Stacks Project, Tag 04DZ; the correspondence of coverings holds
for any surjection. -/
@[stacks 03SI "part (1): the isomorphism of sites, as the equivalence of the small etale
categories induced by base change together with the correspondence of covering sieves. The
source's hypothesis is a universal homeomorphism, which is this statement's hypothesis as
well.",
  sga "1 IX 1.7" "more general",
  sga "1 IX 4.10",
  sga "4 XIV 1.11" "more general",
  sga "4½ Th_finitude 2.7" "more general"]
theorem smallEtaleSite_iso_of_universalHomeomorphism (f : X ⟶ Y) [UniversalHomeomorphism f] :
    (smallEtaleBaseChange f).IsEquivalence ∧
      ∀ (V : Y.Etale) (S : Sieve V),
        S.functorPushforward (smallEtaleBaseChange f) ∈
            smallEtaleTopology X ((smallEtaleBaseChange f).obj V) ↔
          S ∈ smallEtaleTopology Y V := by
  have hsurj : Surjective f :=
    ((universalHomeomorphism_iff_integral_universallyInjective_surjective f).mp
      inferInstance).2.2
  have : Surjective f := hsurj
  exact ⟨smallEtaleBaseChange_isEquivalence_of_universalHomeomorphism f,
    fun V S ↦ functorPushforward_mem_smallEtaleTopology_iff f S⟩

end Stacks.EtaleCohomology

end
