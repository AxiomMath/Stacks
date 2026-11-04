module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjVeroneseTwistedSectionsSemilinear
public import StacksFrontier.AlgebraicGeometry.FiniteDirectImageCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.ProjNoetherian.Basic

/-!
# Coherence transports along the Veronese isomorphism

Let `S` be a graded ring, `d ≥ 1`, `S⁽ᵈ⁾` the `d`-th Veronese subring and
`i : X = Proj S ≅ X' = Proj S⁽ᵈ⁾` the isomorphism of [Stacks, Tag 0B5J]. The proof of
[Stacks, Tag 0B5R] works on `X'`, where the graded ring is generated in degree one for a suitable
`d` and so the whole degree-one theory applies, and reads its conclusions back on `X`. A sheaf of
modules is carried from `X` to `X'` by `Stacks.Veronese.veronesePushforward`, the direct image
along `i`; this file proves that **a coherent module stays coherent** under that transport, which
is what lets the degree-one results on `X'` be applied to `i_*ℱ` for a coherent `ℱ` on `X`.

## Main results

* `Stacks.AlgebraicGeometry.isCoherent_pushforward_of_isIso`: for an isomorphism of schemes
  `g : X ⟶ Y` with `X` locally Noetherian, the direct image along `g` of a coherent module is
  coherent.
* `Stacks.Veronese.isCoherent_veronesePushforward`: the specialization to the Veronese
  isomorphism. For `S` Noetherian and `ℱ` a coherent `𝒪_X`-module, `i_*ℱ` is a coherent
  `𝒪_{X'}`-module.

## Implementation notes

Nothing here is proved from scratch. Coherence of the direct image along a **finite** morphism to
a locally Noetherian scheme is [Stacks, Tag 01Y6] and is already formalized as
`Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.isCoherent_pushforward_of_isFinite`; an
isomorphism is finite, so the only thing the general lemma below adds is that for an isomorphism
the Noetherian hypothesis need not be assumed on the *target*. It is a hypothesis on the source
instead, transported along the inverse by
`AlgebraicGeometry.isLocallyNoetherian_of_isOpenImmersion` — an isomorphism is an open immersion
— and that is the form the Veronese application needs: what is known is that `S` is Noetherian,
hence that `Proj S` is a Noetherian scheme by [Stacks, Tag 0B5Q]
(`Stacks.AlgebraicGeometry.Proj.isNoetherian_proj`), whereas Noetherianity of the Veronese subring
`S⁽ᵈ⁾` is a separate statement (`Stacks.Veronese.isNoetherianRing_veroneseSubring`) available only
for the `d` built from a fixed finite set of generators. No such hypothesis is needed, and none is
taken.

The coherence predicate throughout is `_root_.SheafOfModules.IsCoherent`, the ringed-space
predicate of [Stacks, Tag 01BW] — the spelling the `Proj` finiteness results are stated against —
and not the sheaf-theoretic variant `Stacks.SheafOfModules.IsCoherent` of [Stacks, Tag 01BV].

The local reducibility attributes are the ones of the neighbouring `Proj` files: the statement
mixes the scheme-level spelling `(Proj 𝒮).Modules` with the spelled-out sheaf of modules over
`ProjectiveSpectrum.Proj.structureSheaf` in which `Stacks.Veronese.veronesePushforward` is
phrased, and crossing between them is what they enable.

## References

* [Stacks Project, Tag 0B5R](https://stacks.math.columbia.edu/tag/0B5R)
* [Stacks Project, Tag 0B5J](https://stacks.math.columbia.edu/tag/0B5J)
* [Stacks Project, Tag 01Y6](https://stacks.math.columbia.edu/tag/01Y6)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 0B5Q](https://stacks.math.columbia.edu/tag/0B5Q)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u w

namespace Stacks.AlgebraicGeometry

/-- **The direct image of a coherent module along an isomorphism of schemes is coherent.**

This is [Stacks, Tag 01Y6] for an isomorphism, with the locally Noetherian hypothesis placed on
the *source*: an isomorphism is an open immersion in both directions, so Noetherianity of `X`
gives Noetherianity of `Y` and
`Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.isCoherent_pushforward_of_isFinite` applies,
an isomorphism being finite. -/
public theorem isCoherent_pushforward_of_isIso {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [IsLocallyNoetherian X] (F : X.Modules) (hF : _root_.SheafOfModules.IsCoherent F) :
    _root_.SheafOfModules.IsCoherent ((Scheme.Modules.pushforward g).obj F) := by
  have := hF
  have : IsLocallyNoetherian Y :=
    isLocallyNoetherian_of_isOpenImmersion (CategoryTheory.inv g)
  exact FiniteDirectImageCoherent.isCoherent_pushforward_of_isFinite g F

end Stacks.AlgebraicGeometry

namespace Stacks.Veronese

attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- **Coherence transports along the Veronese isomorphism.** For `S` a Noetherian graded ring,
`d ≥ 1` and `ℱ` a coherent `𝒪_X`-module on `X = Proj S`, the direct image of `ℱ` along the
isomorphism `i : X ≅ X' = Proj S⁽ᵈ⁾` of [Stacks, Tag 0B5J] is a coherent `𝒪_{X'}`-module.

Noetherianity is assumed of `S` only: it makes `X` a Noetherian scheme by [Stacks, Tag 0B5Q], and
`X' ≅ X` inherits that, so nothing has to be known about the Veronese subring `S⁽ᵈ⁾`. -/
public theorem isCoherent_veronesePushforward [IsNoetherianRing S] (d : ℕ) (hd : 0 < d)
    (F : (AlgebraicGeometry.Proj 𝒮).Modules) (hF : _root_.SheafOfModules.IsCoherent F) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    _root_.SheafOfModules.IsCoherent (veronesePushforward 𝒮 d hd F) :=
  let := veroneseGradingGradedRing 𝒮 d hd
  have : IsIso (veroneseProjIso 𝒮 d hd).hom := (veroneseProjIso 𝒮 d hd).isIso_hom
  _root_.Stacks.AlgebraicGeometry.isCoherent_pushforward_of_isIso
    (veroneseProjIso 𝒮 d hd).hom F hF

end Stacks.Veronese

end
