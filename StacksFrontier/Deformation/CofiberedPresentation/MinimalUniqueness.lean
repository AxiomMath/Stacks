module

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverComp
public import StacksFrontier.Deformation.Cofibered
public import StacksFrontier.Deformation.GroupoidQuotient.MinimalAutoequivalence
public import StacksFrontier.Deformation.GroupoidQuotient.MinimalEquivalence
public import StacksFrontier.Deformation.Minimality
public import StacksFrontier.Deformation.Presentation

/-!
# Uniqueness of a minimal smooth prorepresentable presentation

Let `ℱ` be a category cofibered in groupoids over `𝒞_Λ` and suppose that `ℱ` is presented
both by a minimal smooth prorepresentable groupoid in functors `(U, R, s, t, c)` and by a
minimal smooth prorepresentable groupoid in functors `(U', R', s', t', c')`. Then the two
groupoids in functors are isomorphic.

## Main results

* `Deformation.GroupoidInFunctors.nonempty_iso_of_presentations`: **Stacks Project, Tag 06L3.**

## Implementation notes

A presentation is an equivalence over `𝒞_Λ` out of the quotient, so the two presentations of
`ℱ` compose to an equivalence over `𝒞_Λ` between the two quotients: that is
`StacksRepresentableCFG.EquivalenceOver.trans` applied to the first presentation and the
reverse of the second. Its forward 1-morphism is induced, up to isomorphism of functors, by a
morphism `F` of groupoids in functors, and `F` is then an isomorphism by Tag 06KR,
`Deformation.GroupoidInFunctors.isIso_hom_of_quotientMaps_isEquivalence`.

The realisation of a 1-morphism of quotients by a morphism of groupoids in functors is the
observation the source proof attributes to Definition 06KB. It is
`Deformation.GroupoidInFunctors.exists_hom_of_morphismOver`, which asks that the source be
prorepresentable and the target smooth; both presentations here are minimal smooth
prorepresentable, so it applies in either direction. It is used in both directions:
Tag 06KR asks for a morphism of groupoids in functors *the other way*, from `H` to `G`, whose
induced functor on quotients is an equivalence, and the backward 1-morphism `e.inv` of an
equivalence over `𝒞_Λ` is exactly such a 1-morphism of quotients to realise.

No compatibility between the two realisations is required. Tag 06KR concludes from a morphism
each way whose induced functors are *both* equivalences, without asking that the second realise
a quasi-inverse of the first: it composes them and uses that a morphism of minimal smooth
prorepresentable groupoids inducing an equivalence is an isomorphism, in each direction. So it
is enough that `e.inv.functor` is an equivalence, which it is by
`StacksRepresentableCFG.EquivalenceOver.isEquivalence_inv_functor`.

The statement is at third universe `max v w`, that is `IsMinimal.{u, v, w, v}`, rather than at
a general universe `z`, which is not reachable: Tag 06KR
rests on the endomorphism case, Tag 06KQ
(`Deformation.GroupoidInFunctors.isIso_quotientMap_of_isEquivalence`), which is itself fixed
at `IsMinimal.{u, v, w, v}`, so this statement at general `z` would need Tag 06KQ at general
`z` first.

`IsNoetherianRing Λ` and `Module.Finite Λ k` are carried because Tag 06KQ consumes them, where
they give finite dimensionality of the tangent space over `k`; they are the standing
assumptions on `Λ` throughout the source's chapter and so are not extra hypotheses on the
statement.

The conclusion is `Nonempty (G ≅ H)`: the source asserts that the two groupoids in functors
are isomorphic, and no particular isomorphism is singled out.

That `ℱ` is cofibered in groupoids is part of the source statement and is carried as the
hypothesis `hp`, even though this reduction does not consume it: the granted hypothesis is
already stated for the quotients, which are cofibered in groupoids outright by
`Deformation.quotientProjection_cofibered`, and Tag 06KR is a statement about the groupoids in
functors themselves.

## References

* [Stacks Project, Tag 06L3](https://stacks.math.columbia.edu/tag/06L3)
* [Stacks Project, Tag 06KR](https://stacks.math.columbia.edu/tag/06KR)
* [Stacks Project, Tag 06KB](https://stacks.math.columbia.edu/tag/06KB)
* [Stacks Project, Tag 06KX](https://stacks.math.columbia.edu/tag/06KX)
-/

@[expose] public section

namespace Deformation

/-! ### Uniqueness of a minimal smooth prorepresentable presentation -/

section
open CategoryTheory

universe u v w u₁ v₁

namespace GroupoidInFunctors

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- **Stacks Project, Tag 06L3.** Let `ℱ` be a category cofibered in groupoids over `𝒞_Λ`.
If `ℱ` admits presentations by minimal smooth prorepresentable groupoids in functors
`(U, R, s, t, c)` and `(U', R', s', t', c')`, then the two are isomorphic.

The two presentations compose to an equivalence `[U/R] → [U'/R']` over `𝒞_Λ`. Both its
forward and its backward 1-morphism of quotients is induced, up to isomorphism of functors, by
a morphism of groupoids in functors, so the forward morphism induces an equivalence of the
quotients whose quasi-inverse is induced as well, and it is therefore an isomorphism by
Tag 06KR. -/
@[stacks 06L3 "the statement is specialised to third universe `max v w`, that is \
`IsMinimal.{u, v, w, v}`, which is where Stacks 06KR and the Stacks 06KQ under it are fixed; \
`IsNoetherianRing Λ` and `Module.Finite Λ k` are the chapter's standing assumptions on Λ, \
which Stacks 06KQ consumes"]
public theorem nonempty_iso_of_presentations [IsNoetherianRing Λ] [Module.Finite Λ k]
    {ℱ : Type u₁} [Category.{v₁} ℱ] (p : ℱ ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (hp : Deformation.IsCofiberedInGroupoids p)
    (G H : GroupoidInFunctors.{_, max v w, max v w}
      (ArtinianLocalAlgCat.{u, max v w, w} Λ k))
    (hGpro : IsProrepresentable G) (hGsmooth : IsSmooth G) (hGmin : IsMinimal.{u, v, w, v} G)
    (hGpres : Deformation.Presentation G p)
    (hHpro : IsProrepresentable H) (hHsmooth : IsSmooth H) (hHmin : IsMinimal.{u, v, w, v} H)
    (hHpres : Deformation.Presentation H p) :
    Nonempty (G ≅ H) := by
  have _hp := hp
  let e := hGpres.trans hHpres.symm
  have hequiv : e.hom.functor.IsEquivalence := e.isEquivalence_hom_functor
  obtain ⟨F, ⟨α⟩⟩ := exists_hom_of_morphismOver G H hGpro hHsmooth e.hom
  have hF : (quotientMap F).IsEquivalence := Functor.isEquivalence_of_iso α.symm
  obtain ⟨F', ⟨β⟩⟩ := exists_hom_of_morphismOver H G hHpro hGsmooth e.inv
  have hinv : e.inv.functor.IsEquivalence := e.isEquivalence_inv_functor
  have hF' : (quotientMap F').IsEquivalence := Functor.isEquivalence_of_iso β.symm
  have := isIso_hom_of_quotientMaps_isEquivalence G H
    hGpro hGsmooth hGmin hHpro hHsmooth hHmin F F'
  exact ⟨asIso F⟩

end GroupoidInFunctors

end

end Deformation
