module

public import StacksFrontier.AlgebraicGeometry.Chow.SubbundleTopChernClass
public import StacksFrontier.AlgebraicGeometry.Constructions.VectorBundleMapClosedImmersion
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The closed embedding of a subbundle

Let `X` be a scheme and `0 ⟶ 𝒩' ⟶ 𝒩 ⟶ ℰ ⟶ 0` a short exact sequence of finite locally free
`𝒪_X`-modules. Dualising and taking relative spectra of symmetric algebras gives the vector
bundles `N' = Spec_X(Sym((𝒩')^∨))` and `N = Spec_X(Sym(𝒩^∨))` over `X` and the canonical morphism
`i = Stacks.Chow.subbundleEmbedding : N' ⟶ N` over `X`. Because the dual `𝒩^∨ ⟶ (𝒩')^∨` of the
inclusion is surjective ([Stacks, Tag 0FV8]), `i` is a closed immersion: this is the closed
embedding of the setup of [Stacks, Tag 0FAA].

## Main results

* `Stacks.Chow.subbundleEmbedding_isClosedImmersion_of_shortExact` — `i` is a closed immersion.

## References

* [Stacks Project, Tag 0FAA](https://stacks.math.columbia.edu/tag/0FAA)
* [Stacks Project, Tag 0FV8](https://stacks.math.columbia.edu/tag/0FV8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace Stacks.Chow

variable {X : Scheme.{u}} (N' N E : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N']
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]

/-- **The closed embedding of the setup of [Stacks, Tag 0FAA].** Given a short exact sequence
`0 ⟶ 𝒩' ⟶ 𝒩 ⟶ ℰ ⟶ 0` of finite locally free `𝒪_X`-modules, the canonical morphism
`i : N' = Spec_X(Sym((𝒩')^∨)) ⟶ N = Spec_X(Sym(𝒩^∨))` is a closed immersion.

The sequence is used through `Stacks.Chow.epi_dualMap_of_subbundleShortExact`: it makes the dual
`𝒩^∨ ⟶ (𝒩')^∨` surjective, and a surjection of quasi-coherent modules gives a closed immersion of
vector bundles, `AlgebraicGeometry.Scheme.Modules.isClosedImmersion_vectorBundleMap_of_epi`. -/
@[sga "3 XXII 5.3.0" "partial"]
theorem subbundleEmbedding_isClosedImmersion_of_shortExact
    (inc : N' ⟶ N) (pr : N ⟶ E) (w : inc ≫ pr = 0)
    (hseq : (ShortComplex.mk inc pr w).ShortExact) :
    IsClosedImmersion (subbundleEmbedding N' N inc) :=
  @Scheme.Modules.isClosedImmersion_vectorBundleMap_of_epi X _ _ _ _ (dualMap inc)
    (epi_dualMap_of_subbundleShortExact N' N E inc pr w hseq)

end Stacks.Chow

end
