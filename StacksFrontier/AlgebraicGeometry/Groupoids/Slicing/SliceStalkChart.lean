module

public import Mathlib.RingTheory.Flat.Basic
public import StacksFrontier.AlgebraicGeometry.Groupoids.Slicing.SliceBaseChangeChart

/-!
# The slice's local ring as an algebra over the base

`AlgebraicGeometry.quotientStalkEquivStalkPullbackSndOfSpan` identifies the local ring of the
base change of a slice with a quotient of the local ring of the source, but only as a ring. For
clause (4) of Stacks 0461 the identification has to be an isomorphism of algebras over the local
ring of the base, because what is transported across it is flatness. This file supplies the
missing compatibility and the transport it makes possible.

The compatibility is the statement that the identification, precomposed with the quotient map, is
the map of local rings induced by the second projection:

```
𝒪_{X, pr₂ z} ⟶ 𝒪_{X, pr₂ z} ⧸ (w) ≅ 𝒪_{Z ×_Y X, z}   is   pr₂ on local rings.
```

Both sides are ring maps out of `𝒪_{X, pr₂ z}`, which is a localization of `Γ(X, U)` at the prime
of `pr₂ z`, and on the germ of a section over `U` both give the germ of its image; so they agree
by uniqueness of maps out of a localization. The germ computation is
`AlgebraicGeometry.quotientStalkEquivStalkPullbackSndOfSpan_mk_germ` on one side and
`AlgebraicGeometry.Scheme.Hom.germ_stalkMap_apply` on the other.

Composing with a further morphism `f : X ⟶ Y'` out of `X` then turns flatness of the quotient
over `𝒪_{Y', f(pr₂ z)}` into flatness of `𝒪_{Z ×_Y X, z}` over the same ring — which is the
flatness half of the Cohen-Macaulayness of `pr₂ ≫ f` at `z`.

## Main results

* `AlgebraicGeometry.exists_isAffineOpen_mem_le_preimage`: around a point of the source there is
  an affine open carried into a given open of the target. This is how the affine charts the
  chart argument needs are produced.
* `AlgebraicGeometry.quotientStalkEquivStalkPullbackSndOfSpan_comp_mk`: the identification is a
  map of algebras over the local ring of the source — the compatibility above.
* `AlgebraicGeometry.flat_stalk_pullback_snd_comp_of_flat_quotient`: flatness of the quotient
  transports to flatness of the local ring of the base change.

## Implementation notes

Flatness is transported by `Module.Flat.of_linearEquiv` applied to the `R`-linear equivalence
underlying the algebra isomorphism; the algebra isomorphism is `AlgEquiv.ofRingEquiv` fed with the
compatibility, which is why the compatibility is stated as an equality of ring homomorphisms
rather than pointwise.

## References

* [Stacks Project, Tag 0461](https://stacks.math.columbia.edu/tag/0461)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Flatness transports along a ring isomorphism which is a map of algebras. -/
private lemma flat_of_ringEquiv_comp {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (e : A ≃+* B)
    (he : (e : A →+* B).comp (algebraMap R A) = algebraMap R B) (hA : Module.Flat R A) :
    Module.Flat R B :=
  have := hA
  Module.Flat.of_linearEquiv (AlgEquiv.ofRingEquiv (f := e)
    (fun x => congrArg (fun φ : R →+* B => φ x) he)).symm.toLinearEquiv

/-- **An affine chart adapted to a point and to an open of the target.** Around a point of the
source of a morphism there is an affine open carried into any given open of the target
containing the image of the point.

This is how the chart arguments below obtain their affine opens: the slicing lemma fixes an
affine chart `A` of the object scheme around `u`, and the charts of the arrow scheme and of the
source fibre are then produced by this lemma rather than assumed. -/
public lemma exists_isAffineOpen_mem_le_preimage {X Y : Scheme.{u}} (t : X ⟶ Y) (x : X)
    {V : Y.Opens} (hx : t x ∈ V) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ U ≤ t ⁻¹ᵁ V := by
  obtain ⟨U, hU, hxU, hUV⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := t ⁻¹ᵁ V) hx
  exact ⟨U, hU, hxU, hUV⟩

section AlgebraSquare

variable {X Y : Scheme.{u}} (t : X ⟶ Y) {U : X.Opens} (hU : IsAffineOpen U) {Z : Scheme.{u}}
  (gL : Z ⟶ Y) (hW : IsAffineOpen (pullback.snd gL t ⁻¹ᵁ U))
  (hsurj : Function.Surjective ((pullback.snd gL t).app U).hom) {w : Γ(X, U)}
  (hker : RingHom.ker ((pullback.snd gL t).app U).hom = Ideal.span {w})
  {z : ↥(pullback gL t)} (hz : pullback.snd gL t z ∈ U)

include hU hW hsurj hker in
/-- **The local ring of a base change cut out by one section, as an algebra.** The identification
of `AlgebraicGeometry.quotientStalkEquivStalkPullbackSndOfSpan`, precomposed with the quotient
map, is the map of local rings induced by the second projection of the base change.

The local ring of `X` at `pr₂ z` is a localization of `Γ(X, U)`, so two ring maps out of it agree
as soon as they agree on germs of sections over `U`; there one side is pinned by
`quotientStalkEquivStalkPullbackSndOfSpan_mk_germ` and the other by
`Scheme.Hom.germ_stalkMap_apply`, and both give the germ of the image section. -/
public theorem quotientStalkEquivStalkPullbackSndOfSpan_comp_mk :
    (quotientStalkEquivStalkPullbackSndOfSpan t hU gL hW hsurj hker hz : _ →+* _).comp
        (Ideal.Quotient.mk
          (Ideal.span {(X.presheaf.germ U (pullback.snd gL t z) hz).hom w})) =
      ((pullback.snd gL t).stalkMap z).hom := by
  let _alg : Algebra Γ(X, U) (X.presheaf.stalk (pullback.snd gL t z)) :=
    (X.presheaf.germ U (pullback.snd gL t z) hz).hom.toAlgebra
  have _hloc : IsLocalization.AtPrime (X.presheaf.stalk (pullback.snd gL t z))
      (hU.primeIdealOf (⟨pullback.snd gL t z, hz⟩ : U)).asIdeal :=
    hU.isLocalization_stalk (⟨pullback.snd gL t z, hz⟩ : U)
  refine IsLocalization.ringHom_ext
    (hU.primeIdealOf (⟨pullback.snd gL t z, hz⟩ : U)).asIdeal.primeCompl (RingHom.ext fun c => ?_)
  change quotientStalkEquivStalkPullbackSndOfSpan t hU gL hW hsurj hker hz
      (Ideal.Quotient.mk _ (X.presheaf.germ U (pullback.snd gL t z) hz c)) =
    (pullback.snd gL t).stalkMap z (X.presheaf.germ U (pullback.snd gL t z) hz c)
  rw [quotientStalkEquivStalkPullbackSndOfSpan_mk_germ,
    Scheme.Hom.germ_stalkMap_apply (pullback.snd gL t) U z hz c]

include hU hW hsurj hker in
/-- **Flatness of the local ring of a base change cut out by one section.** Let `f : X ⟶ Y'` be a
further morphism out of `X`. If the quotient of the local ring of `X` at `pr₂ z` by the germ of
the cutting section is flat over the local ring of `Y'` at the image of `pr₂ z`, then the local
ring of the base change at `z` is flat over that same ring, for the algebra structure induced by
`pr₂ ≫ f`.

This is the flatness half of the Cohen-Macaulayness of `pr₂ ≫ f` at `z`. The identification of
`quotientStalkEquivStalkPullbackSndOfSpan` is an isomorphism of algebras over the local ring of
`Y'` because `quotientStalkEquivStalkPullbackSndOfSpan_comp_mk` identifies it, after the quotient
map, with the local ring map of `pr₂`, and the local ring map of `pr₂ ≫ f` factors as the local
ring map of `f` followed by that of `pr₂`. -/
public theorem flat_stalk_pullback_snd_comp_of_flat_quotient {Y' : Scheme.{u}} (f : X ⟶ Y') :
    letI _algX : Algebra (Y'.presheaf.stalk ((pullback.snd gL t ≫ f) z))
        (X.presheaf.stalk (pullback.snd gL t z)) :=
      (f.stalkMap (pullback.snd gL t z)).hom.toAlgebra
    letI _algP : Algebra (Y'.presheaf.stalk ((pullback.snd gL t ≫ f) z))
        ((pullback gL t).presheaf.stalk z) :=
      ((pullback.snd gL t ≫ f).stalkMap z).hom.toAlgebra
    Module.Flat (Y'.presheaf.stalk ((pullback.snd gL t ≫ f) z))
        (X.presheaf.stalk (pullback.snd gL t z) ⧸
          Ideal.span {(X.presheaf.germ U (pullback.snd gL t z) hz).hom w}) →
      Module.Flat (Y'.presheaf.stalk ((pullback.snd gL t ≫ f) z))
        ((pullback gL t).presheaf.stalk z) := by
  intro hflat
  let _algX : Algebra (Y'.presheaf.stalk ((pullback.snd gL t ≫ f) z))
      (X.presheaf.stalk (pullback.snd gL t z)) :=
    (f.stalkMap (pullback.snd gL t z)).hom.toAlgebra
  let _algP : Algebra (Y'.presheaf.stalk ((pullback.snd gL t ≫ f) z))
      ((pullback gL t).presheaf.stalk z) :=
    ((pullback.snd gL t ≫ f).stalkMap z).hom.toAlgebra
  have hsq := quotientStalkEquivStalkPullbackSndOfSpan_comp_mk t hU gL hW hsurj hker hz
  -- The local ring map of `pr₂ ≫ f` factors through the local ring of `X`; this is recorded as
  -- an equality of ring homomorphisms in term mode, the fibre product's local ring being too
  -- large to rewrite inside.
  have hcomp : ((pullback.snd gL t ≫ f).stalkMap z).hom =
      ((pullback.snd gL t).stalkMap z).hom.comp (f.stalkMap (pullback.snd gL t z)).hom :=
    (congrArg CommRingCat.Hom.hom
      (Scheme.Hom.stalkMap_comp (pullback.snd gL t) f z)).trans (CommRingCat.hom_comp _ _)
  have hgoal : (quotientStalkEquivStalkPullbackSndOfSpan t hU gL hW hsurj hker hz :
        _ →+* _).comp ((Ideal.Quotient.mk (Ideal.span
          {(X.presheaf.germ U (pullback.snd gL t z) hz).hom w})).comp
            (f.stalkMap (pullback.snd gL t z)).hom) =
      ((pullback.snd gL t ≫ f).stalkMap z).hom := by
    rw [hcomp, ← RingHom.comp_assoc, hsq]
  exact flat_of_ringEquiv_comp
    (quotientStalkEquivStalkPullbackSndOfSpan t hU gL hW hsurj hker hz) hgoal hflat

end AlgebraSquare

end AlgebraicGeometry

end
