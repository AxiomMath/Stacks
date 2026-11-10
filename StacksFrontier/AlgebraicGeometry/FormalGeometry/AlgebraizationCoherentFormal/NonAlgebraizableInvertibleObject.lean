module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicSystemsOnComplement
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.GlobalProperOverCompleteLocal
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.NonAlgebraizableAlgebraizing
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.NonAlgebraizableExample
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicInvertible

/-!
# The conclusion of the non-algebraizable example

Let `k` be a field and let `A = k[x,y][[t]]`, `I = (t)`, `𝔞 = (x,y,t)`, so that `U` is the
punctured spectrum of `A`. The conclusion of [Stacks, Tag 0EHE] is that `Coh(U, I𝒪_U)` contains
an invertible object which is not the completion of any coherent `𝒪_U`-module: the family
`(𝓛ₙ)` glued from `A_x/tⁿA_x` and `A_y/tⁿA_y` along the unit
`u = 1 + t/(xy) + ∑_{m ≥ 2} aₘ tᵐ/(xy)^{φ(m)}` of `A_{xy}/tⁿA_{xy}`.

This file writes that conclusion down as a proposition about `k`, in the two notions it is
phrased in: `Stacks.Coherent.IsInvertibleAdic` for "invertible object of `Coh(U, I𝒪_U)`" and
`Stacks.Algebraization.IsCompletionOfCoherent` for "is the completion of a coherent
`𝒪_U`-module", the latter being the image of the completion functor
`Stacks.Algebraization.completionFunctor`.

## Main definitions

* `Stacks.Algebraization.NonAlgebraizableExample.HasNonAlgebraizableInvertibleObject` — the
  conclusion of Tag 0EHE for the field `k`.

## Main results

* `Stacks.Algebraization.NonAlgebraizableExample.hasNonAlgebraizableInvertibleObject` — **the
  conclusion of Tag 0EHE**: that proposition holds for every field `k`.

## Implementation notes

The ideal `I𝒪_U` is `Stacks.Algebraization.idealOnOpen (situation k)`, the comap along `U ⟶ X`
of the ideal sheaf of `(t)`. The completion functor needs `U` to be locally Noetherian, and that
instance is already found by instance search, `U` being open in the spectrum of a Noetherian
ring.

The conclusion is existentially quantified over the object rather than asserted of a constructed
`(𝓛ₙ)`, which is what the example asserts; the witness is now available, as
`Stacks.Algebraization.NonAlgebraizableExample.levelCoherentAdicSystem`, with its invertibility
`Stacks.Algebraization.NonAlgebraizableExample.isInvertibleAdic_levelCoherentAdicSystem`.

`Stacks.Algebraization.isCoherentAdicSystem_of_affine_ker` reduces all of membership in
`Coh(U, I𝒪_U)` to affine-local data: for transition maps that are epimorphisms it is enough to
identify the kernel of `𝓛ₙ₊₁ ⟶ 𝓛ₙ` over each affine open with `I(U)^{n+1} 𝓛ₙ₊₁(U)`. The
chartwise computation does not reach every affine open of the punctured spectrum — the basic open
`D(x̄ + ȳ)` lies in neither chart, so `𝓛ₙ₊₁` is not trivialized over it — and
`Stacks.Algebraization.isCoherentAdicSystem_of_basis_ker` is the form that asks only for the
basic opens contained in a chart, which is all the chartwise computation offers and still a basis
because the two charts cover.

What exists towards that. The terms are built:
`Stacks.Algebraization.NonAlgebraizableExample.levelModule` is `𝓛ₙ`, glued from the two charts
`D(x̄)` and `D(ȳ)` of `Spec(A/tⁿA)` along the transition element, and
`Stacks.Algebraization.NonAlgebraizableExample.isInvertibleModule_levelModule` says it is
invertible on the punctured spectrum
`Stacks.Algebraization.NonAlgebraizableExample.levelOpen` of `A/tⁿA`. Those charts are the
spectra of the chart rings by
`Stacks.Algebraization.NonAlgebraizableExample.chartOpenEquiv`, and the chartwise kernel of the
reduction is `Stacks.Algebraization.NonAlgebraizableExample.ker_chartReduction`.

The three pieces of machinery the system itself needs are also built.
`Stacks.SheafOfModules.UnitTransitionCocycle.glueHomOfIntertwines` makes a morphism
`D.glue ⟶ f_* D'.glue` of glued modules out of a morphism of schemes `f` carrying the transition
units of one unit cocycle to those of another, which is what
`Stacks.Algebraization.NonAlgebraizableExample.chartReduction_transitionElement` supplies
chartwise; `Stacks.Algebraization.NonAlgebraizableExample.levelModuleOnOpen` is `𝓛ₙ` transported
to `U` as the direct image along
`Stacks.Algebraization.NonAlgebraizableExample.levelStructureMap`, which exists because the
punctured spectrum of `A/tⁿA` is the preimage of `U`
(`Stacks.Algebraization.NonAlgebraizableExample.preimage_U_levelToAmbient`); and
`Stacks.Algebraization.NonAlgebraizableExample.exists_subschemeIso_levelOpen` is the
identification `(idealOnOpen (situation k) ^ n).subscheme ≅ (levelOpen k n).toScheme`, together
with the square identifying the closed immersion of that subscheme with
`Stacks.Algebraization.NonAlgebraizableExample.levelStructureMap`, which is the spelling
`Stacks.Coherent.IsInvertibleAdic` asks for. Its two ingredients are general:
`Stacks.IdealSheaf.comap_pow` commutes the inverse image of an ideal sheaf with powers, and
`AlgebraicGeometry.Scheme.IdealSheafData.exists_subschemeIso_resLE` identifies the closed
subscheme cut out by the restriction to an open `U` of the kernel ideal sheaf of a closed
immersion `i : Y ⟶ X` with the open `i ⁻¹ᵁ U` of `Y`.

The intertwining hypothesis for the level cocycles is now supplied as well:
`Stacks.Algebraization.NonAlgebraizableExample.app_levelOverlapUnit` says that the closed
immersion of punctured spectra carries the transition unit of level `n + 1` to the one of level
`n`, `Stacks.Algebraization.NonAlgebraizableExample.levelTransition` and
`levelTransitionOnOpen` are the resulting maps `𝓛ₙ₊₁ ⟶ 𝓛ₙ` upstairs and on `U`, both
epimorphisms (`epi_levelTransitionOnOpen`), and
`Stacks.Algebraization.NonAlgebraizableExample.levelSystem` is the system as a diagram over
`ℕᵒᵖ`.

The second clause has its engine and its obstruction, which is the whole mathematical content of
the source's proof sketch.
`Stacks.Algebraization.NonAlgebraizableExample.isTrivial_of_isInvertible_ambientOpen` is the
source's "the ring `A` is a UFD hence we see `M ≅ A`": every invertible module on every open of
`Spec(A)` is trivial, `A = k[x,y][[t]]` being a unique factorization domain
(`uniqueFactorizationMonoid_ambientRing`), so that [Stacks, Tag 0BDA] applies with no recourse to
the extension step [Stacks, Tag 0BD9]. And
`Stacks.Algebraization.NonAlgebraizableExample.not_isTrivial_levelModule_two` is the source's
"`𝓛₂ ≇ 𝒪_U/I²𝒪_U` by construction", for every choice of `a` and `φ`. The two combine into
`Stacks.Algebraization.NonAlgebraizableExample.not_nonempty_pullback_iso_levelModule_two`: no
invertible module on any open `V ⊆ Spec(A)` pulls back to `𝓛₂` along any morphism from the
punctured spectrum of `A/t²A` to `V`.

What closes it. Membership of `levelSystem` in `Coh(U, I𝒪_U)` is
`Stacks.Algebraization.NonAlgebraizableExample.isCoherentAdicSystem_levelSystem`, whose one
remaining input was the kernel computation
`Stacks.Algebraization.NonAlgebraizableExample.ker_app_levelSystem_map_succ`, and invertibility
of the resulting object is
`Stacks.Algebraization.NonAlgebraizableExample.isInvertibleAdic_levelCoherentAdicSystem`; that is
the first clause. The second clause is
`Stacks.Algebraization.NonAlgebraizableExample.not_isCompletionOfCoherent_levelCoherentAdicSystem`,
which runs the source's first proof on the two comparisons it needs:

* Local invertibility of an algebraizing module, as
  `Stacks.Algebraization.exists_isInvertibleModule_restrict_of_isInvertibleAdic_completionIso`:
  if `𝓛` is a coherent `𝒪_U`-module whose completion is isomorphic to an invertible object of
  `Coh(U, I𝒪_U)`, then there is an open `V` with `U ∩ Y ⊆ V ⊆ U` on which `𝓛` is invertible. This
  is the source's "the completion of the stalk `𝓛_y` would be an invertible module hence `𝓛_y` is
  invertible", followed by the spreading out of invertibility from the stalks at the points of
  `U ∩ Y` to a neighbourhood.
* The comparison of the level terms with pullbacks, as
  `Stacks.Algebraization.NonAlgebraizableExample.idealPowerQuotientIsoPushforwardPullbackOnOpen`:
  for such a `𝓛` and such a `V`, the term
  `Stacks.Algebraization.idealPowerQuotient (idealOnOpen (situation k)) n 𝓛` is the direct image
  along `levelStructureMap k n` of the pullback of `𝓛|_V`.

With these two, `not_isTrivial_levelModule_two` — through the full faithfulness of direct image
along a closed immersion, [Stacks, Tag 08KS] — closes `¬ IsCompletionOfCoherent`, and
`Stacks.Algebraization.NonAlgebraizableExample.hasNonAlgebraizableInvertibleObject` is the
conclusion of the tag.

Nothing in any of this constrains `a` or `φ`, and nothing should: the obstruction lives modulo
`t²`, where the transition element is `1 + t/(xy)` whatever the parameters are. The source's
second, independent proof — through the vanishing of `lim H⁰(U, 𝓛ₙ)` — is the one that needs a
parameter condition, and that condition is
`Stacks.Algebraization.NonAlgebraizableExample.IsVanishingSectionsParameter`.

## References

* [Stacks Project, Tag 0EHE](https://stacks.math.columbia.edu/tag/0EHE)
* [Stacks Project, Tag 0EHC](https://stacks.math.columbia.edu/tag/0EHC)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open scoped AlgebraicGeometry

universe u

namespace Stacks.Algebraization.NonAlgebraizableExample

variable (k : Type u) [Field k]

/-- **Stacks Project, Tag 0EHE (the conclusion).** The category `Coh(U, I𝒪_U)` of the situation
`A = k[x,y][[t]]`, `I = (t)`, `𝔞 = (x,y,t)` contains an invertible object which is not the
completion of any coherent `𝒪_U`-module. -/
public def HasNonAlgebraizableInvertibleObject : Prop :=
  ∃ L : Stacks.Coherent.CoherentAdicSystems (idealOnOpen (situation k)),
    Stacks.Coherent.IsInvertibleAdic (idealOnOpen (situation k)) L ∧
      ¬ IsCompletionOfCoherent (idealOnOpen (situation k)) L

/-- **Stacks Project, Tag 0EHE.** The category `Coh(U, I𝒪_U)` of the situation
`A = k[x,y][[t]]`, `I = (t)`, `𝔞 = (x,y,t)` contains an invertible object which is not the
completion of any coherent `𝒪_U`-module.

The witness is the family `(𝓛ₙ)` of the example,
`Stacks.Algebraization.NonAlgebraizableExample.levelCoherentAdicSystem`, with the source's own
choice `aₘ = 1`, `φ(m) = 2ᵐ` of parameters — though neither clause depends on that choice.
Invertibility is
`Stacks.Algebraization.NonAlgebraizableExample.isInvertibleAdic_levelCoherentAdicSystem` and
non-algebraizability is `not_isCompletionOfCoherent_levelCoherentAdicSystem`.
-/
@[stacks 0EHE "Coh(U, I O_U) contains an invertible object which is not the completion of a \
coherent O_U-module"]
public theorem hasNonAlgebraizableInvertibleObject : HasNonAlgebraizableInvertibleObject k :=
  ⟨levelCoherentAdicSystem k (fun _ => 1) (fun m => 2 ^ m),
    isInvertibleAdic_levelCoherentAdicSystem k (fun _ => 1) (fun m => 2 ^ m),
    not_isCompletionOfCoherent_levelCoherentAdicSystem k (fun _ => 1) (fun m => 2 ^ m)⟩

end Stacks.Algebraization.NonAlgebraizableExample

end
