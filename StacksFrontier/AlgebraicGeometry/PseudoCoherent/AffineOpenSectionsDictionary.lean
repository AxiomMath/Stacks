module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorAmplitudeOpenImmersion
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffineSectionsComparison
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.SideCondition

/-!
# Stacks 08E7 at an affine open: pseudo-coherence of `E|_U` is pseudo-coherence of `RΓ(U, E)`

Let `X` be a scheme, let `E` be an object of the derived category of `𝒪_X`-modules whose
cohomology sheaves are quasi-coherent, and let `U` be an affine open of `X`.  Then the
restriction `E|_U` is pseudo-coherent on the ringed space `U` exactly when the complex
`RΓ(U, E)` of `Γ(X, U)`-modules is pseudo-coherent.

This is the last leg of the chain that the étale-chart localization of Stacks 0DII has to cross:
after the chart comparisons and Stacks 08HE have carried the condition to the small Zariski site
of an affine chart, and `AlgebraicGeometry.Scheme.isPseudoCoherent_zariskiRingedSite_iff` has
carried it from that site to the ringed space, what is left is to name the complex of modules,
and this names it.

## Main results

* `AlgebraicGeometry.isPseudoCoherent_pushforwardTilde_iff`: pseudo-coherence of the pushforward
  along an isomorphism `Spec R ≅ Y` of the complex of associated sheaves of an object `K` of
  `D(R)` is pseudo-coherence of `K`.
* `AlgebraicGeometry.isPseudoCoherent_restrictFunctor_iff_derivedSectionsUnbounded`: the
  statement of the header.

## How it is proved

Every ingredient is already in the library; only the composition is new.

* Stacks 06Z0 at an affine open, in the form
  `AlgebraicGeometry.affineDerivedSectionsPresentation`, produces an object `K` of
  `D(Γ(X, U))` with `E|_U ≅ (isoSpec⁻¹)_* (K^~)` and `K ≅ RΓ(U, E)`.  That is the sentence
  "`E|_U` is quasi-isomorphic to the complex of quasi-coherent sheaves associated with the object
  `RΓ(U, E)` of `D(A)`" of the source's proof of Stacks 09VF, and it is where
  `AlgebraicGeometry.IsAffineOpen.isoSpec` enters.
* Pushing forward along the isomorphism `isoSpec⁻¹` neither creates nor destroys
  pseudo-coherence, by
  `AlgebraicGeometry.Scheme.Modules.isPseudoCoherent_pushforward_isIso_iff` (Stacks 09VA at an
  isomorphism, in all degrees).
* On `Spec Γ(X, U)` the condition on `K^~` is pseudo-coherence of `K`, which is Stacks 08E7 at an
  object of the derived category,
  `AlgebraicGeometry.RingedSpace.isPseudoCoherent_derivedTilde_iff`.
* The two isomorphisms are absorbed by
  `AlgebraicGeometry.RingedSpace.IsPseudoCoherent.of_iso` and
  `StacksDraft.PseudoCoherence.IsPseudoCoherent.ofIso`, both predicates depending only on the
  isomorphism class of their object.

## Implementation notes

The two middle steps are taken in a separate declaration,
`AlgebraicGeometry.isPseudoCoherent_pushforwardTilde_iff`, which names neither the affine open nor
its ring of sections: taken together with the presentation in one declaration they exceed the
heartbeat ceiling, the predicates involved being `abbrev`s whose unfolded existentials have then
to be unified at the two spellings `AlgebraicGeometry.Scheme.Modules` and
`StrictlyPerfect.OXMod` of one category of modules at once.  Split, each half is cheap, and the
general statement is the reusable half.

That general statement quantifies over no free object of `D(𝒪_Y)`, and may not.  Stated with an
object `A` of `D(𝒪_Y)` and an isomorphism `A ≅ k_*(K^~)` it does not elaborate: the module
universe of `AlgebraicGeometry.RingedSpace.IsPseudoCoherent` is then pinned by `A`'s type while
its derived-category universe is left to `CategoryTheory.HasDerivedCategory.standard`, and the
elaborator is asked for `u =?= max ?u ?v` — "stuck at solving universe constraint".
With both sides of the `iff` built from `K` every universe is determined by a term, and the
transport of the isomorphism moves to the consumer, where `A` is a concrete restriction.

`AlgebraicGeometry.RingedSpace.IsPseudoCoherent.of_iso` is spelled in full rather than reached by
dot notation on a hypothesis, for the reason recorded at
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFromAfterPushforward_iff_of_iso`: the predicate
is an `abbrev`, and resolving the projection against a hypothesis of that type sends the
elaborator through the unfolded existential.

**Its ringed space is passed by name.**  `of_iso` takes it implicitly, so leaving it out asks the
elaborator to solve `StrictlyPerfect.structureSheafOfRings ?X =?= U.toScheme.ringCatSheaf` — to
invert a projection on the term `U.toScheme`, which is `X.restrict U.isOpenEmbedding`.  That is
not a pattern and the search does not terminate inside the ceiling: without `(X := ...)` this
declaration dies at `whnf` after 200 000 heartbeats, and with it the file checks in about a
second.

No `stacks` tag is placed: the statement is Stacks 08E7 transported along Stacks 06Z0 and
Stacks 09VA, and the bare attributes for all three sit on their own statements.

## References

* [Stacks Project, Tag 08E7](https://stacks.math.columbia.edu/tag/08E7)
* [Stacks Project, Tag 08CB](https://stacks.math.columbia.edu/tag/08CB)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 09VA](https://stacks.math.columbia.edu/tag/09VA)
* [Stacks Project, Tag 09VF](https://stacks.math.columbia.edu/tag/09VF)
* [Stacks Project, Tag 0DII](https://stacks.math.columbia.edu/tag/0DII)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry

/-- **Stacks 08E7 across an isomorphism with a spectrum.**  Let `k : Spec R ⟶ Y` be an
isomorphism of schemes and let `K` be an object of `D(R)`.  Then `k_*(K^~)` is pseudo-coherent on
the ringed space `Y` if and only if `K` is pseudo-coherent.

Pushforward along an isomorphism neither creates nor destroys pseudo-coherence
(`AlgebraicGeometry.Scheme.Modules.isPseudoCoherent_pushforward_isIso_iff`, Stacks 09VA at an
isomorphism), and on `Spec R` the condition on `K^~` is Stacks 08E7,
`AlgebraicGeometry.RingedSpace.isPseudoCoherent_derivedTilde_iff`. -/
public theorem isPseudoCoherent_pushforwardTilde_iff {Y : Scheme.{u}} {R : CommRingCat.{u}}
    (k : Spec R ⟶ Y) [IsIso k] (K : DerivedCategory (ModuleCat.{u} R)) :
    RingedSpace.IsPseudoCoherent (X := Y.toRingedSpace)
        ((Scheme.Modules.pushforward k).mapDerivedCategory.obj
          ((tilde.functor R).mapDerivedCategory.obj K)) ↔
      StacksDraft.PseudoCoherence.IsPseudoCoherent K :=
  (Scheme.Modules.isPseudoCoherent_pushforward_isIso_iff k
      ((tilde.functor R).mapDerivedCategory.obj K)).trans
    (RingedSpace.isPseudoCoherent_derivedTilde_iff R K)

/-- **Stacks 08E7 at an affine open.**  Let `E` be an object of the derived category of
`𝒪_X`-modules all of whose cohomology sheaves are quasi-coherent, and let `U` be an affine open
of `X`.  Then `E|_U` is pseudo-coherent on the ringed space `U` if and only if the complex
`RΓ(U, E)` of `Γ(X, U)`-modules is pseudo-coherent.

See "How it is proved" in the module documentation for the inputs; the only
quasi-coherence used is the hypothesis `hE`, which is what Stacks 06Z0 consumes. -/
public theorem isPseudoCoherent_restrictFunctor_iff_derivedSectionsUnbounded {X : Scheme.{u}}
    (E : DerivedCategory X.Modules)
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsQuasicoherent)
    {U : X.Opens} (hU : IsAffineOpen U) :
    RingedSpace.IsPseudoCoherent (X := U.toScheme.toRingedSpace)
        ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj E) ↔
      StacksDraft.PseudoCoherence.IsPseudoCoherent ((derivedSectionsUnbounded X U).obj E) := by
  obtain ⟨K, ⟨hEK⟩, ⟨hKΓ⟩⟩ := affineDerivedSectionsPresentation E hE U hU
  refine Iff.trans
    ⟨fun h => RingedSpace.IsPseudoCoherent.of_iso (X := U.toScheme.toRingedSpace) h hEK,
      fun h => RingedSpace.IsPseudoCoherent.of_iso (X := U.toScheme.toRingedSpace) h hEK.symm⟩ ?_
  exact (isPseudoCoherent_pushforwardTilde_iff hU.isoSpec.inv K).trans
    ⟨fun h => StacksDraft.PseudoCoherence.IsPseudoCoherent.ofIso h hKΓ,
      fun h => StacksDraft.PseudoCoherence.IsPseudoCoherent.ofIso h hKΓ.symm⟩

end AlgebraicGeometry

end
