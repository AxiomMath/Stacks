module

public import Mathlib.RingTheory.Smooth.Basic
public import StacksFrontier.Cotangent.SurjectivePresentationSequence
public import StacksFrontier.RingTheory.NaiveCotangent.LocalizationBaseAndTarget

/-!
# A morphism between two formally smooth presentations is a quasi-isomorphism

Let `S` be an `R`-algebra and let `P`, `P'` be two extensions of `S` over `R`, that is two
surjections of `R`-algebras onto `S`.  A morphism of extensions `f : P ⟶ P'` induces a chain map
`NL(P) ⟶ NL(P')` of the two-term complexes `I/I² ⟶ Ω[P.Ring⁄R] ⊗ S`
(`NaiveCotangent.nlExtensionMap`).  If **both** presenting rings are formally smooth over `R`,
that chain map is a quasi-isomorphism.

`NaiveCotangent.nlExtensionMap_isQuasiIso` already gives this when a morphism `P' ⟶ P` exists in
the other direction, which makes the two chain maps mutually inverse up to homotopy.  That
hypothesis is unavailable in the situation this file is written for: `P` is a polynomial
presentation of `S` and `P'` is a formally smooth `R`-algebra surjecting onto `S`, and a morphism
`P' ⟶ P` would be a lift of `P'.Ring ⟶ S` along `P.Ring ⟶ S`, whose kernel is not nilpotent.

## Main results

* `NaiveCotangent.bijective_onH₁_nlExtensionMap_of_formallySmooth`: the induced map on
  `H₁ = ker d` is bijective.  This is Mathlib's
  `Algebra.Extension.H1Cotangent.equivOfFormallySmooth` read on the two-term complex.
* `NaiveCotangent.bijective_onH₀_nlExtensionMap`: the induced map on `H₀ = coker d` is bijective
  for **every** morphism of extensions, no smoothness needed: both cokernels are `Ω[S⁄R]`,
  compatibly.
* `NaiveCotangent.nlExtensionMap_isQuasiIso_of_formallySmooth`: the chain map is a
  quasi-isomorphism.

## Route

`H₁` is `Algebra.Extension.H1Cotangent` on the nose — both are `LinearMap.ker` of
`Algebra.Extension.cotangentComplex` — and `NaiveCotangent.ChainMap.onH₁` of the chain map is
`Algebra.Extension.H1Cotangent.map` on the nose, both being the restriction of
`Algebra.Extension.Cotangent.map`.  Mathlib's
`Algebra.Extension.H1Cotangent.equivOfFormallySmooth` says that map is bijective when the two
presenting rings are formally smooth; it is proved there by passing to the infinitesimal
thickenings, where the lift that is unavailable for `P'` itself does exist.

For `H₀` the criterion is `NaiveCotangent.bijective_onH₀_of_surjective_square` applied with both
outer modules `Ω[S⁄R]`, the two projections `Algebra.Extension.toKaehler` and the identity: each
projection is surjective with kernel the image of the differential
(`Algebra.Extension.toKaehler_surjective`,
`Algebra.Extension.exact_cotangentComplex_toKaehler`), and the square commutes by the second
clause of `Stacks.Cotangent.outerTerms_constant`.

## References

* [Stacks Project, Tag 00S1](https://stacks.math.columbia.edu/tag/00S1)
* [Stacks Project, Tag 0D0L](https://stacks.math.columbia.edu/tag/0D0L)
-/

@[expose] public section

namespace NaiveCotangent

open Algebra

universe w u v

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
  {P P' : Extension.{w} R S}

/-- **The map induced on `H₁` by a morphism of two formally smooth presentations is bijective.**

`H₁ (nlOfExtension P)` is `Algebra.Extension.H1Cotangent P` and the induced map is
`Algebra.Extension.H1Cotangent.map`, both on the nose; Mathlib's
`Algebra.Extension.H1Cotangent.equivOfFormallySmooth` says that map is an isomorphism. -/
theorem bijective_onH₁_nlExtensionMap_of_formallySmooth (f : P.Hom P')
    [Algebra.FormallySmooth R P.Ring] [Algebra.FormallySmooth R P'.Ring] :
    Function.Bijective (nlExtensionMap f).onH₁ := by
  have hb : Function.Bijective (Extension.H1Cotangent.map f) := by
    rw [← Extension.H1Cotangent.equivOfFormallySmooth_toLinearMap f]
    exact (Extension.H1Cotangent.equivOfFormallySmooth P P').bijective
  have hmk : ∀ (x : P.Cotangent) (hx : x ∈ LinearMap.ker P.cotangentComplex),
      (Extension.H1Cotangent.map f (show P.H1Cotangent from ⟨x, hx⟩)).1 =
        Extension.Cotangent.map f x := fun _ _ ↦ rfl
  refine bijective_onH₁_of_bijOn _ ⟨fun x hx ↦ ?_, fun x hx y hy hxy ↦ ?_, fun y hy ↦ ?_⟩
  · exact (hmk x hx) ▸ (Extension.H1Cotangent.map f (show P.H1Cotangent from ⟨x, hx⟩)).2
  · have h := hb.1 (a₁ := show P.H1Cotangent from ⟨x, hx⟩)
      (a₂ := show P.H1Cotangent from ⟨y, hy⟩)
      (Subtype.ext (((hmk x hx).trans hxy).trans (hmk y hy).symm))
    exact congrArg (fun t : P.H1Cotangent ↦ t.1) h
  · obtain ⟨x, hx⟩ := hb.2 (show P'.H1Cotangent from ⟨y, hy⟩)
    exact ⟨x.1, x.2, (hmk x.1 x.2).symm.trans (congrArg (fun t : P'.H1Cotangent ↦ t.1) hx)⟩

/-- **The map induced on `H₀` by a morphism of extensions is bijective.**  No hypothesis is
needed: the cokernel of the differential of `NL(P)` is `Ω[S⁄R]` for every extension `P`, and the
chain map is compatible with the two projections onto it. -/
theorem bijective_onH₀_nlExtensionMap (f : P.Hom P') :
    Function.Bijective (nlExtensionMap f).onH₀ := by
  have hsq : P'.toKaehler ∘ₗ Extension.CotangentSpace.map f =
      (LinearMap.id : Ω[S⁄R] →ₗ[S] Ω[S⁄R]) ∘ₗ P.toKaehler :=
    ((Stacks.Cotangent.outerTerms_constant f).2).trans (LinearMap.id_comp _).symm
  exact bijective_onH₀_of_surjective_square (A := nlOfExtension P) (B := nlOfExtension P')
    (Ω[S⁄R]) (Ω[S⁄R]) (nlExtensionMap f) P.toKaehler P'.toKaehler LinearMap.id
    P.toKaehler_surjective
    (LinearMap.exact_iff.mp P.exact_cotangentComplex_toKaehler)
    (LinearMap.exact_iff.mp P'.exact_cotangentComplex_toKaehler) hsq Function.bijective_id

/-- **A morphism between two formally smooth presentations of `S` over `R` induces a
quasi-isomorphism of naive cotangent complexes.**  For extensions `P`, `P'` of `S` over `R` whose
presenting rings are both formally smooth over `R`, and any morphism of extensions
`f : P ⟶ P'`, the chain map `NL(P) ⟶ NL(P')` is bijective on `H₁` and on `H₀`.

Unlike `NaiveCotangent.nlExtensionMap_isQuasiIso` this does not ask for a morphism in the other
direction. -/
theorem nlExtensionMap_isQuasiIso_of_formallySmooth (f : P.Hom P')
    [Algebra.FormallySmooth R P.Ring] [Algebra.FormallySmooth R P'.Ring] :
    IsQuasiIso (nlExtensionMap f) :=
  ⟨bijective_onH₁_nlExtensionMap_of_formallySmooth f, bijective_onH₀_nlExtensionMap f⟩

end NaiveCotangent

end
