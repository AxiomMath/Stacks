module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.NonAlgebraizableExample
public import StacksFrontier.AlgebraicGeometry.PicardGroup.OpenUFD
public import StacksFrontier.AlgebraicGeometry.PicardGroup.Scheme
public import StacksFrontier.RingTheory.PowerSeries.UniqueFactorization

/-!
# Every invertible module on an open of `Spec(k[x,y][[t]])` is trivial

The proof sketch of [Stacks, Tag 0EHE] runs: an algebraizing coherent module `𝓛` on the
punctured spectrum `U` would have invertible stalks along `U ∩ Y`, hence would be invertible on
some open `V` with `U ∩ Y ⊆ V ⊆ U`; "by Divisors, Lemma [Stacks, Tag 0BD9] we find an invertible
`A`-module `M` with `M̃|_V ≅ 𝓛|_V`. However the ring `A` is a UFD hence we see `M ≅ A`, which
would imply `𝓛ₙ ≅ 𝒪_U/Iⁿ𝒪_U`." This file is that step: the Picard group of **every** open
subscheme of `Spec(A)`, `A = k[x,y][[t]]`, vanishes.

The source routes it through Tag 0BD9, extending the invertible module across the complement of
`V` and then trivializing it on `Spec(A)`. That detour is unnecessary here, because
[Stacks, Tag 0BDA] — `Stacks.PicardUFD.subsingleton_picardGroup_open_spectrum` — already covers
an arbitrary open of the spectrum of a unique factorization domain with no Noetherian hypothesis
and no extension step, and `A` is a unique factorization domain by
`PowerSeries.uniqueFactorizationMonoid_mvPolynomial`.

## Main results

* `Stacks.Algebraization.NonAlgebraizableExample.uniqueFactorizationMonoid_ambientRing` — the
  ambient ring `A = k[x,y][[t]]` of the example is a unique factorization domain.
* `Stacks.Algebraization.NonAlgebraizableExample.subsingleton_picardGroup_ambientOpen` — the
  Picard group of every open subscheme of `Spec(A)` is trivial.
* `Stacks.Algebraization.NonAlgebraizableExample.isTrivial_of_isInvertible_ambientOpen` — every
  invertible module on an open subscheme of `Spec(A)` is isomorphic to the structure sheaf.

## Implementation notes

The opens are opens of `Spec (CommRingCat.of (AmbientRing k))` rather than of
`(situation k).X`. The two are the same scheme, but the second freezes the `CommRing` structure
as the projection `(situation k).commRingA`, which is `rfl`-equal to and not syntactically equal
to the instance that instance search finds, so rewriting along anything stated at the first spelling
fails there. `subsingleton_picardGroup_situationOpen` is the restatement for an open of
`(situation k).X`, and in particular for `U`; it is the only place the transport happens.

## References

* [Stacks Project, Tag 0EHE](https://stacks.math.columbia.edu/tag/0EHE)
* [Stacks Project, Tag 0BDA](https://stacks.math.columbia.edu/tag/0BDA)
* [Stacks Project, Tag 0BD9](https://stacks.math.columbia.edu/tag/0BD9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Algebraization.NonAlgebraizableExample

variable (k : Type u) [Field k]

/-- **The ambient ring `A = k[x,y][[t]]` of the example is a unique factorization domain.** The
polynomial ring `k[x,y]` is regular and factorial, so its Picard group is trivial, and the power
series ring over a regular factorial ring is factorial. -/
@[stacks 0EHE "the ring A = k[x,y][[t]] is a UFD"]
public theorem uniqueFactorizationMonoid_ambientRing :
    UniqueFactorizationMonoid (AmbientRing k) :=
  PowerSeries.uniqueFactorizationMonoid_mvPolynomial k (Fin 2)

/-- **`Pic` of an open of the ambient affine scheme vanishes.** The Picard group of every open
subscheme of `Spec(A)`, `A = k[x,y][[t]]`, is trivial: `A` is a unique factorization domain, and
[Stacks, Tag 0BDA] trivializes the Picard group of every open of the spectrum of one. -/
@[stacks 0EHE "Pic of every open of Spec(k[x,y][[t]]) is trivial"]
public theorem subsingleton_picardGroup_ambientOpen
    (V : (Spec (CommRingCat.of (AmbientRing k))).Opens) :
    Subsingleton V.toScheme.picardGroup := by
  have : UniqueFactorizationMonoid (AmbientRing k) := uniqueFactorizationMonoid_ambientRing k
  exact Stacks.PicardUFD.subsingleton_picardGroup_open_spectrum (AmbientRing k) V

/-- **An invertible module on an open of `Spec(A)` is trivial.** An invertible module on an open
`V ⊆ Spec(k[x,y][[t]])` — for instance on an open `V` with `U ∩ Y ⊆ V ⊆ U` on which an
algebraizing coherent module becomes invertible — is isomorphic to the structure sheaf of `V`. -/
@[stacks 0EHE "an invertible module on an open of Spec(k[x,y][[t]]) is trivial"]
public theorem isTrivial_of_isInvertible_ambientOpen
    {V : (Spec (CommRingCat.of (AmbientRing k))).Opens} (L : V.toScheme.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible V.toScheme.presheaf V.toScheme.ringCatIsSheaf L) :
    Stacks.SheafOfModules.IsTrivial V.toScheme.presheaf V.toScheme.ringCatIsSheaf L := by
  have := subsingleton_picardGroup_ambientOpen k V
  exact (Scheme.picardClass_eq_zero_iff _ L hL).1 (Subsingleton.elim _ _)

/-- The vanishing of `Pic` for an open of the ambient scheme of the situation, in particular for
the punctured spectrum `U` itself. -/
public theorem subsingleton_picardGroup_situationOpen (V : (situation k).X.Opens) :
    Subsingleton V.toScheme.picardGroup :=
  subsingleton_picardGroup_ambientOpen k V

end Stacks.Algebraization.NonAlgebraizableExample

end
