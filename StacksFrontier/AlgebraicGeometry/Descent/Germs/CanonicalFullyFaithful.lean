module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EffectiveDescentData
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EffectiveDescentFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.PullbackFullyFaithful

/-!
# Schemes over the base form a full subcategory of the descent data

For a morphism `f : X ⟶ S` which is an fpqc covering of `S` on its own — surjective, flat and
quasi-compact, say — the canonical descent datum functor `Over S ⥤ DescentDatum f` is fully
faithful: a morphism of canonical descent data is the canonical datum of a unique morphism of
schemes over `S`, and two schemes over `S` with isomorphic canonical data are isomorphic over
`S`.

## Main results

* `AlgebraicGeometry.DescentData.canonicalFunctor_fullyFaithful_of_fpqc` : the canonical
  descent datum functor along a single-morphism fpqc covering is fully faithful.
* `AlgebraicGeometry.DescentData.canonicalFunctor_fullyFaithful_of_flat_surjective_quasiCompact`:
  the same for a surjective flat quasi-compact morphism.
* `AlgebraicGeometry.DescentData.existsUnique_canonicalFunctor_map_eq` : a morphism of
  canonical descent data is the image of exactly one morphism of schemes over `S`.
* `AlgebraicGeometry.DescentData.nonempty_iso_of_canonicalFunctor_iso` : two schemes over `S`
  whose canonical descent data are isomorphic are isomorphic over `S`.

## Implementation notes

`AlgebraicGeometry.DescentData.canonicalFunctor` is by definition the composite of
`AlgebraicGeometry.DescentData.trivialFunctor` with the pullback functor of the square
`f ≫ 𝟙 S = f ≫ 𝟙 S`, so full faithfulness factors into two independent halves. The pullback
half is Stacks 0241, `AlgebraicGeometry.pullbackFunctor_fullyFaithful_of_fpqc`, instantiated
with `a := 𝟙 S`, whose covering hypothesis asks for `f` to be a singleton fpqc covering of `S`.
The trivial half is `AlgebraicGeometry.DescentData.trivialFunctorFullyFaithful`: a morphism of
descent data relative to `{𝟙 S}` has a single component, which is already a morphism of schemes
over `S`, and the compatibility square carries no information.

Full faithfulness is produced as `Nonempty _` rather than as data, matching
`AlgebraicGeometry.pullbackFunctor_fullyFaithful_of_fpqc`.

## References

* [Stacks Project, Tag 02W0](https://stacks.math.columbia.edu/tag/02W0)
* [Stacks Project, Tag 0241](https://stacks.math.columbia.edu/tag/0241)
* [Stacks Project, Tag 023Z](https://stacks.math.columbia.edu/tag/023Z)
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.DescentData

open CategoryTheory Limits

variable {S X : Scheme.{u}}

/-- If the single morphism `f : X ⟶ S` is an fpqc covering of `S`, then the canonical descent
datum functor `Over S ⥤ DescentDatum f` is fully faithful, so schemes over `S` form a full
subcategory of the descent data relative to `f`. -/
@[stacks 02W0 "in particular, for a covering by a single morphism", sga "1 VIII 5.2" "more general"]
theorem canonicalFunctor_fullyFaithful_of_fpqc (f : X ⟶ S)
    (hcover : Presieve.singleton f ∈ Scheme.fpqcPrecoverage.coverings S) :
    Nonempty (canonicalFunctor f).FullyFaithful := by
  obtain ⟨hP⟩ := pullbackFunctor_fullyFaithful_of_fpqc
    (pullbackFunctor (𝟙 S) f (𝟙 S) f (by simp)) hcover
  exact ⟨(trivialFunctorFullyFaithful S).comp hP⟩

/-- The canonical descent datum functor along a surjective flat quasi-compact morphism is fully
faithful, such a morphism being an fpqc covering on its own. -/
@[sga "3 IV 3.4"]
theorem canonicalFunctor_fullyFaithful_of_flat_surjective_quasiCompact (f : X ⟶ S) [Flat f]
    [Surjective f] [QuasiCompact f] :
    Nonempty (canonicalFunctor f).FullyFaithful :=
  canonicalFunctor_fullyFaithful_of_fpqc f (Scheme.Hom.singleton_mem_fpqcPrecoverage f)

/-- A morphism between the canonical descent data of two schemes over `S`, along a surjective
flat quasi-compact morphism, is the canonical datum of exactly one morphism of schemes
over `S`. -/
theorem existsUnique_canonicalFunctor_map_eq (f : X ⟶ S)
    [Flat f] [Surjective f] [QuasiCompact f] {W W' : Over S}
    (g : (canonicalFunctor f).obj W ⟶ (canonicalFunctor f).obj W') :
    ∃! h : W ⟶ W', (canonicalFunctor f).map h = g := by
  obtain ⟨hff⟩ := canonicalFunctor_fullyFaithful_of_flat_surjective_quasiCompact f
  refine ⟨hff.preimage g, hff.map_preimage g, fun h hh ↦ ?_⟩
  rw [← hh, hff.preimage_map]

/-- Two schemes over `S` whose canonical descent data along a surjective flat quasi-compact
morphism are isomorphic are themselves isomorphic over `S`. -/
theorem nonempty_iso_of_canonicalFunctor_iso (f : X ⟶ S)
    [Flat f] [Surjective f] [QuasiCompact f] {W W' : Over S}
    (e : (canonicalFunctor f).obj W ≅ (canonicalFunctor f).obj W') : Nonempty (W ≅ W') :=
  (canonicalFunctor_fullyFaithful_of_flat_surjective_quasiCompact f).elim fun hff ↦
    ⟨hff.preimageIso e⟩

end AlgebraicGeometry.DescentData

end
