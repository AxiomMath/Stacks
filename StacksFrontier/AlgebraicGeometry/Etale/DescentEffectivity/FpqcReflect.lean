module

public import StacksFrontier.AlgebraicGeometry.Descent.PullbackFullyFaithful.SourceFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Etale.DescentEffectivity.PullbackSquare

/-!
# Étale effectivity is reflected by a fully faithful pullback

Let `a : X ⟶ S` and `a' : X' ⟶ S` be two morphisms to a common base and let `p : X' ⟶ X` be a
morphism over `S`. Pullback along `p` sends a descent datum relative to `X / S` to one relative
to `X' / S`, and sends the canonical datum of a scheme over `S` to the canonical datum of the
same scheme. So if that pullback functor is fully faithful it *reflects* étale effectivity: a
datum whose pullback along `p` is étale effective is itself étale effective.

Full faithfulness holds when `X' ⟶ S` is an fpqc covering,
[Stacks, Tag 040K](https://stacks.math.columbia.edu/tag/040K), and in particular when `p` itself
is an fpqc covering of `X`, [Stacks, Tag 0241](https://stacks.math.columbia.edu/tag/0241). That
second case is what the proof of [Stacks, Tag 0BTP](https://stacks.math.columbia.edu/tag/0BTP)
uses to pass from a flat covering of the base: for `w : W ⟶ S` flat, surjective and
quasi-compact, `X ×_S W ⟶ X` is an fpqc covering of `X`, so effectivity of a datum relative to
`X / S` may be checked after pulling back to `X ×_S W / S`.

## Main results

* `AlgebraicGeometry.DescentDatum.isEtaleEffective_of_pullbackSquare_of_fullyFaithful`:
  **étale effectivity is reflected by a fully faithful pullback functor over a fixed base.**
* `AlgebraicGeometry.DescentDatum.isEtaleEffective_of_pullbackSquare_of_fpqc`: the same with
  full faithfulness supplied by `p` being an fpqc covering of `X`.
* `AlgebraicGeometry.DescentDatum.isEtaleEffective_of_isEtaleEffective_changeBase`: **étale
  effectivity of a datum may be checked after pulling back along a flat surjective quasi-compact
  morphism of the base**, read as a datum relative to the composite `X ×_S W ⟶ S`.

## Implementation notes

The reflection does not go through the full subcategory of descent data with étale underlying
scheme. Étale effectivity is membership in the essential image of
`AlgebraicGeometry.etaleDescentFunctor`, whose objects are the canonical data of étale schemes,
and an isomorphism in a full subcategory is an isomorphism of the underlying objects; so the
witness is obtained by applying `CategoryTheory.Functor.FullyFaithful.preimageIso` to the
underlying isomorphism of descent data and putting it back into the subcategory with
`CategoryTheory.ObjectProperty.isoMk`. The identification of the pullback of a canonical datum
with a canonical datum is `AlgebraicGeometry.DescentData.canonicalDatumPullbackIso`, whose
target mentions `Over.pullback (𝟙 S)` and is brought back to the scheme itself by
`AlgebraicGeometry.DescentData.pullbackIdObjIso`.

## References

* [Stacks Project, Tag 0241](https://stacks.math.columbia.edu/tag/0241)
* [Stacks Project, Tag 040K](https://stacks.math.columbia.edu/tag/040K)
* [Stacks Project, Tag 0BTP](https://stacks.math.columbia.edu/tag/0BTP)
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory Limits

namespace DescentDatum

variable {S X X' : Scheme.{u}} {a : X ⟶ S} {a' : X' ⟶ S} {p : X' ⟶ X}
  {hp : p ≫ a = a' ≫ 𝟙 S} (P : DescentData.PullbackFunctor a a' (𝟙 S) p hp)

/-- **Étale effectivity is reflected by a fully faithful pullback functor over a fixed base.**
The pullback of the canonical datum of an étale scheme over `S` is the canonical datum of the
same scheme, so the isomorphism witnessing effectivity of the pullback is the image under the
pullback functor of an isomorphism witnessing effectivity of the datum itself. -/
theorem isEtaleEffective_of_pullbackSquare_of_fullyFaithful
    (hff : P.functor.FullyFaithful) (D : DescentDatum a) [Etale D.over.hom]
    [Etale (pullbackSquareDatum P D).over.hom]
    (h : (pullbackSquareDatum P D).IsEtaleEffective) :
    D.IsEtaleEffective := by
  obtain ⟨U, ⟨e⟩⟩ := h
  refine ⟨U, ⟨ObjectProperty.isoMk _ (hff.preimageIso ?_)⟩⟩
  exact DescentData.canonicalDatumPullbackIso P ((Scheme.Etale.forget S).obj U) ≪≫
    (DescentData.canonicalFunctor a').mapIso
      (DescentData.pullbackIdObjIso ((Scheme.Etale.forget S).obj U)).symm ≪≫
    (IsEtaleDescentData a').ι.mapIso e

/-- **Étale effectivity is reflected by pullback along an fpqc covering of the source over a
fixed base.** This is Tag 0241 fed into
`AlgebraicGeometry.DescentDatum.isEtaleEffective_of_pullbackSquare_of_fullyFaithful`. -/
theorem isEtaleEffective_of_pullbackSquare_of_fpqc
    (hcover : Presieve.singleton p ∈ Scheme.fpqcPrecoverage X)
    (D : DescentDatum a) [Etale D.over.hom]
    [Etale (pullbackSquareDatum P D).over.hom]
    (h : (pullbackSquareDatum P D).IsEtaleEffective) :
    D.IsEtaleEffective :=
  isEtaleEffective_of_pullbackSquare_of_fullyFaithful P
    (pullbackFunctor_fullyFaithful_of_fpqc P hcover).some D h

end DescentDatum

/-- The pullback functor from descent data relative to `X / S` to descent data relative to the
composite `X ×_S W ⟶ X ⟶ S`, for `W ⟶ S` a morphism of the base. The target base is still `S`:
this is pullback along a refinement of `{X ⟶ S}`, not base change of the datum. -/
abbrev DescentDatum.changeBasePullbackFunctor {S X W : Scheme.{u}} (f : X ⟶ S) (w : W ⟶ S) :
    DescentData.PullbackFunctor f (pullback.fst f w ≫ f) (𝟙 S) (pullback.fst f w)
      (by simp) :=
  DescentData.pullbackFunctor _ _ _ _ _

namespace DescentDatum

variable {S X W : Scheme.{u}} (f : X ⟶ S) (w : W ⟶ S)

/-- **Étale effectivity of a descent datum may be checked after pulling back along a flat
surjective quasi-compact morphism of the base.** The datum is read relative to the composite
`X ×_S W ⟶ S`, which refines `X ⟶ S` by a morphism that is an fpqc covering of `X`, being a base
change of `w`. -/
theorem isEtaleEffective_of_isEtaleEffective_changeBase [Flat w] [Surjective w] [QuasiCompact w]
    (D : DescentDatum f) [Etale D.over.hom]
    [Etale (pullbackSquareDatum (changeBasePullbackFunctor f w) D).over.hom]
    (h : (pullbackSquareDatum (changeBasePullbackFunctor f w) D).IsEtaleEffective) :
    D.IsEtaleEffective := by
  refine isEtaleEffective_of_pullbackSquare_of_fpqc (changeBasePullbackFunctor f w) ?_ D h
  have hfl : Flat (pullback.fst f w) := inferInstance
  have hsu : Surjective (pullback.fst f w) := inferInstance
  have hqc : QuasiCompact (pullback.fst f w) := inferInstance
  exact (pullback.fst f w).singleton_mem_fpqcPrecoverage

end DescentDatum

end AlgebraicGeometry

end
