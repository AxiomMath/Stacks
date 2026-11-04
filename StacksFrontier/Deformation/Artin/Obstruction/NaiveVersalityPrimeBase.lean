module

public import StacksFrontier.Deformation.Artin.Infinitesimal.SiteContainment
public import StacksFrontier.Deformation.Artin.Obstruction.NaiveVersalityStalkBase

/-!
# Versality over the affine open, at the residue field of the prime

The degree `-1` half of the direction `(1) ⇒ (2)` of [Stacks, Tag 07YM] tests versality against
a small extension built from `Λ`-algebras, `Λ` being the ring of the affine open `Spec A` maps
into, and it does so at the residue field `κ(𝔭)` of the *prime* `𝔭 = u₀` of `A` — the field in
which the whole chain is written. `Deformation.Artin.IsVersalAt`, by contrast, is the lifting
property over the local ring `𝒪_{S,s}` at the scheme-theoretic residue field
`Deformation.Artin.residueFieldAlgebra`. Two independent changes separate the two, and both are
already available:

* `Deformation.Artin.liftsAtResiduePoint_of_isVersalAt` moves the *field* from the scheme's
  residue field at `u₀` to `Ideal.ResidueField u₀.asIdeal`, through
  `AlgebraicGeometry.Scheme.Spec.residueFieldIso`;
* `Deformation.Artin.liftsAtResiduePoint_changeBase` moves the *deformation base* from
  `𝒪_{S,s}` to `Λ`.

This file composes them in that order, which is the one in which no comparison of residue
fields over `Λ` is needed: the field change happens over the local ring, where the isomorphism
is linear by construction, and only then is the base moved. It also records the one size
estimate the chain needs beyond those of
`StacksFrontier.Deformation.Artin.Infinitesimal.SiteContainment`, namely that a quotient of a ring
already small enough is small enough.

## Main results

* `Deformation.Artin.contains_spec_quotient_of_mk_le` — `Spec (R ⧸ I)` lies in a site
  containing `Spec A` as soon as `R` is no larger than `max ℵ₀ #A`: a quotient is no larger
  than its source.
* `Deformation.Artin.liftsAtResiduePoint_prime_base_of_isVersalAt` — **the form of versality
  the degree `-1` endgame consumes**: versality of `x` at `u₀` gives the lifting property with
  an arbitrary `Spec Λ ⟶ S` as deformation base, at the point of `Spec A` determined by the
  `A`-algebra structure of `Ideal.ResidueField u₀.asIdeal`.

## Implementation notes

The `Λ`-algebra structure of `Ideal.ResidueField u₀.asIdeal` is a plain instance binder with no
compatibility hypothesis: `Deformation.Artin.liftsAtResiduePoint_changeBase` asks nothing of it
beyond that it exist, the compatibility between the residue point and the base being carried by
`Deformation.Artin.specMap_primeResidueFieldAlgebra_comp_fromSpecStalk`, which mentions only the
`A`-algebra structure. Nothing is asked of `Spec Λ ⟶ S` — in particular not that it be an open
immersion, nor a monomorphism; that is the content of
`Deformation.Artin.liftsAtResiduePoint_changeBase`.

Locality of the structure map of `κ(𝔭)` over `𝒪_{S,s}`, which that transfer does ask for, is
the only computation here: the map is `AlgebraicGeometry.Scheme.stalkClosedPointTo` followed by
the isomorphism of residue fields, the first local because it is a map of local rings induced by
a morphism of schemes and the second because a ring homomorphism between fields is local.

## References

* [Stacks Project, Tag 07YM](https://stacks.math.columbia.edu/tag/07YM)
* [Stacks Project, Tag 07XF](https://stacks.math.columbia.edu/tag/07XF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Deformation.Artin

universe u v w

/-! ### A quotient of a small ring is small -/

/-- A quotient of a commutative ring no larger than `max ℵ₀ #A` has its spectrum in a big fppf
site containing `Spec A`: the quotient map is surjective, so the quotient is no larger than the
ring, and `Deformation.Artin.contains_spec_of_mk_le` applies.

This is the estimate that puts the two Artinian quotients `A ⧸ 𝔭 ^ n` and `A' ⧸ (𝔭') ^ n` of
[Stacks, Tag 07YM] in the site: `A` is there by hypothesis and `A'` by
`Cardinal.mk_le_max_of_surjective_of_mk_ker_le_max`. -/
public theorem contains_spec_quotient_of_mk_le (B : BigFppfSite.{u}) {A : Type u} [CommRing A]
    (hA : B.Contains (Spec (CommRingCat.of A))) {R : Type u} [CommRing R] (I : Ideal R)
    (h : Cardinal.mk R ≤ max Cardinal.aleph0 (Cardinal.mk A)) :
    B.Contains (Spec (CommRingCat.of (R ⧸ I))) :=
  contains_spec_of_mk_le B hA (R ⧸ I)
    ((Cardinal.mk_le_of_surjective Ideal.Quotient.mk_surjective).trans h)

/-! ### Versality over the affine open at the residue field of the prime -/

section PrimeBase

variable {Λ A : Type u} [CommRing Λ] [CommRing A] [Algebra Λ A]
  {S : Scheme.{u}} (toS : Spec (CommRingCat.of A) ⟶ S) (u₀ : Spec (CommRingCat.of A))
  [Algebra Λ u₀.asIdeal.ResidueField] (iΛ : Spec (CommRingCat.of Λ) ⟶ S)

/-- The structure map of `κ(𝔭)` over the local ring of `S` at the image of the point is a local
homomorphism: it is `AlgebraicGeometry.Scheme.stalkClosedPointTo` of the residue-field point,
which is local, followed by `AlgebraicGeometry.Scheme.Spec.residueFieldIso`, which is local
because it is a ring homomorphism between fields.

This is the hypothesis `Deformation.Artin.liftsAtResiduePoint_changeBase` asks of the chosen
residue point. -/
public theorem isLocalHom_primeResidueFieldAlgebra :
    letI := primeResidueFieldAlgebra toS u₀
    IsLocalHom (algebraMap (S.presheaf.stalk (basePoint (Over.mk toS) u₀))
      u₀.asIdeal.ResidueField) := by
  let := residueFieldAlgebra (Over.mk toS) u₀
  let := primeResidueFieldAlgebra toS u₀
  have h1 : IsLocalHom (algebraMap (S.presheaf.stalk (basePoint (Over.mk toS) u₀))
      ((Over.mk toS).left.residueField u₀)) :=
    show IsLocalHom
      (Scheme.stalkClosedPointTo (residueFieldBasePoint (Over.mk toS) u₀)).hom from
      inferInstance
  have h2 : IsLocalHom (Scheme.Spec.residueFieldIso (CommRingCat.of A) u₀).hom.hom :=
    ⟨fun a ha => isUnit_iff_ne_zero.mpr fun hzero => by
      rw [hzero, map_zero] at ha
      exact not_isUnit_zero ha⟩
  exact RingHom.isLocalHom_comp _ _

variable {X : Type v} [Category.{w} X] (q : X ⥤ Over S) (x : X)
  (hx : q.obj x = Over.mk toS)

omit [Algebra Λ A] in
include hx in
/-- **Stacks 07YM, versality in the form the degree `-1` endgame consumes.** If `x` is versal at
a point `u₀` of `Spec A`, then the lifting property holds with *any* `Spec Λ ⟶ S` as deformation
base, at the point of `Spec A` determined by the `A`-algebra structure of the residue field
`Ideal.ResidueField u₀.asIdeal` of the prime.

`Deformation.Artin.liftsAtResiduePoint_of_isVersalAt` is versality read at that field over the
local ring `𝒪_{S,s}`, and `Deformation.Artin.liftsAtResiduePoint_changeBase` moves the base to
`Λ`; the compatibility of the residue point with the local ring that the move asks for is
`Deformation.Artin.specMap_primeResidueFieldAlgebra_comp_fromSpecStalk`, and the locality of the
structure map is `Deformation.Artin.isLocalHom_primeResidueFieldAlgebra`.

Nothing is asked of `Spec Λ ⟶ S`: not that it be an open immersion, nor a monomorphism. -/
@[stacks 07YM "versality over any affine base at the residue field of the prime"]
public theorem liftsAtResiduePoint_prime_base_of_isVersalAt
    (hversal : IsVersalAt (Over.mk toS) q u₀ x hx) :
    LiftsAtResiduePoint (Λ := Λ) (k := u₀.asIdeal.ResidueField) iΛ q (Over.mk toS) x hx
      (Spec.map (CommRingCat.ofHom (algebraMap A u₀.asIdeal.ResidueField))) :=
  let := primeResidueFieldAlgebra toS u₀
  liftsAtResiduePoint_changeBase iΛ (basePoint (Over.mk toS) u₀)
    (isLocalHom_primeResidueFieldAlgebra toS u₀) q (Over.mk toS) x hx
    (Spec.map (CommRingCat.ofHom (algebraMap A u₀.asIdeal.ResidueField)))
    (specMap_primeResidueFieldAlgebra_comp_fromSpecStalk toS u₀).symm
    (liftsAtResiduePoint_of_isVersalAt toS u₀ q x hx hversal)

end PrimeBase

end Deformation.Artin
