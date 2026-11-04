module

public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Sites

/-!
# Cartesian base-change squares in a big étale site

Fix a morphism of schemes `f : T ⟶ S` and an object `g : S' ⟶ S` of the big étale category
over `S`. Base changing `f` along `g` produces the fibre product `T' = T ×_S S'` together with
its two projections, and this is the square along which the base-change comparison maps for
étale cohomology are formed.

All four schemes are objects of one chosen bounded big étale site, which is the universe
bookkeeping implicit in the notation `(Sch/S)_étale`.

## Main definitions

* `AlgebraicGeometry.CartesianBaseChangeSituation` packages the morphism `f` with the object
  `g` of the big étale category over its target.
* `AlgebraicGeometry.CartesianBaseChangeSituation.S'` is the scheme underlying `g`,
  `CartesianBaseChangeSituation.T'` is the fibre product `T ×_S S'`, and
  `CartesianBaseChangeSituation.g'`, `CartesianBaseChangeSituation.f'` are its projections.

## Implementation notes

The field `g` is an object of the slice category defining the big étale category over `S`, so
its underlying scheme and its structure morphism are both recovered canonically. The fibre
product is the chosen pullback of schemes rather than an extra datum equipped with a
cartesianness proof; that it lies below the site's size cutoff is `Scheme.size_pullback_lt`.

## References

* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A morphism `f : T ⟶ S` of a big étale site together with an object `g : S' ⟶ S` of the big
étale category over `S`, along which `f` is to be base changed. -/
public structure CartesianBaseChangeSituation where
  /-- The ambient bounded big étale site. -/
  B : BigEtaleSite.{u}
  /-- The target scheme `S`. -/
  S : B.Scheme
  /-- The source scheme `T`. -/
  T : B.Scheme
  /-- The morphism `f : T ⟶ S`. -/
  f : T ⟶ S
  /-- The object `g : S' ⟶ S` of `(Sch/S)_étale`. -/
  g : BigEtaleOver B (B.inclusion.obj S) S.property

namespace CartesianBaseChangeSituation

/-- The scheme `S'` underlying the object `g : S' ⟶ S`. -/
public abbrev S' (D : CartesianBaseChangeSituation.{u}) : D.B.Scheme :=
  D.g.left

/-- The canonical fibre product `T' = T ×_S S'`. -/
public noncomputable def T' (D : CartesianBaseChangeSituation.{u}) : D.B.Scheme :=
  ⟨pullback (D.B.inclusion.map D.f) (D.B.inclusion.map D.g.hom),
    Scheme.size_pullback_lt _ _ D.T.property D.S'.property⟩

/-- The projection `g' : T' ⟶ T`. -/
public noncomputable def g' (D : CartesianBaseChangeSituation.{u}) : D.T' ⟶ D.T :=
  ObjectProperty.homMk
    (pullback.fst (D.B.inclusion.map D.f) (D.B.inclusion.map D.g.hom))

/-- The projection `f' : T' ⟶ S'`. -/
public noncomputable def f' (D : CartesianBaseChangeSituation.{u}) : D.T' ⟶ D.S' :=
  ObjectProperty.homMk
    (pullback.snd (D.B.inclusion.map D.f) (D.B.inclusion.map D.g.hom))

end CartesianBaseChangeSituation

end AlgebraicGeometry
