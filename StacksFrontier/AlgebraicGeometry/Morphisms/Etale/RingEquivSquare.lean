module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.IsoInvariance
public import StacksFrontier.AlgebraicGeometry.Scheme.ClosedPointSpecSurjection

/-!
# Transporting a point and étaleness across a square of ring isomorphisms

Let `φ : A → B` and `φ' : A' → B'` be ring maps and let `eA : A ≃+* A'` and `eB : B ≃+* B'` be
isomorphisms with `φ' ∘ eA = eB ∘ φ`. Then `Spec φ'` and `Spec φ` are carried onto one another by
the two isomorphisms of spectra, and this file is the two consequences of that which a transport
argument needs:

* a point of `Spec B'` above a given point of `Spec B`, which over local rings `A` and `A'` lies
  above the closed point of `Spec A'` as soon as the given point lies above the closed point of
  `Spec A`;
* étaleness of `Spec φ` at a point, from étaleness of `Spec φ'` at a point above it.

The two together replace the situation in which a ring map is only known up to a pair of
isomorphisms of its source and target — for instance a map of invariant rings of base-changed
groupoid schemes, which is the map of new base rings read through the two canonical identifications
of Tag 03BK.

## Main results

* `AlgebraicGeometry.exists_point_specMap_of_ringEquiv_square`: **the point of `Spec B'` above a
  given point of `Spec B`, above the closed point of `Spec A'`.**
* `AlgebraicGeometry.etaleAt_specMap_of_ringEquiv_square`: **étaleness at a point is carried from
  `Spec φ'` to `Spec φ`.**

## Implementation notes

Both are read off the commuting square of the four spectra, whose vertical maps are isomorphisms:
the first from injectivity of `Spec eA` together with
`AlgebraicGeometry.specMap_base_closedPoint_of_ringEquiv`, and the second from
`AlgebraicGeometry.etaleAt_of_isIso_square`.

## References

* [Stacks Project, Tag 03BK](https://stacks.math.columbia.edu/tag/03BK)
* [Stacks Project, Tag 0DT9](https://stacks.math.columbia.edu/tag/0DT9)

## Tags

spectrum, ring isomorphism, étale at a point, closed point
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry

variable {A B A' B' : Type u} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
  (φ : A →+* B) (φ' : A' →+* B') (eA : A ≃+* A') (eB : B ≃+* B')

/-- The square of the four spectra determined by a commuting square of ring maps two of whose
sides are isomorphisms. -/
theorem specMap_comp_eq_of_ringEquiv_square
    (hcomm : φ'.comp eA.toRingHom = eB.toRingHom.comp φ) :
    Spec.map (CommRingCat.ofHom φ') ≫ Spec.map (CommRingCat.ofHom eA.toRingHom) =
      Spec.map (CommRingCat.ofHom eB.toRingHom) ≫ Spec.map (CommRingCat.ofHom φ) := by
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
    hcomm]

/-- **Étaleness at a point is carried across a square of ring isomorphisms.** If `φ' ∘ eA = eB ∘ φ`
with `eA` and `eB` isomorphisms, and `Spec φ'` is étale at a point `y` whose image under `Spec eB`
is `x`, then `Spec φ` is étale at `x`.

This is `AlgebraicGeometry.etaleAt_of_isIso_square` for the square of the four spectra; unlike a
statement about the points above a closed point it says nothing about where `x` lies, so it serves
a transport at an arbitrary point. -/
theorem etaleAt_specMap_of_ringEquiv_square
    (hcomm : φ'.comp eA.toRingHom = eB.toRingHom.comp φ)
    {x : Spec (.of B)} {y : Spec (.of B')}
    (hy : (Spec.map (CommRingCat.ofHom eB.toRingHom)).base y = x)
    (h : EtaleAt (Spec.map (CommRingCat.ofHom φ')) y) :
    EtaleAt (Spec.map (CommRingCat.ofHom φ)) x := by
  have : IsIso (CommRingCat.ofHom eA.toRingHom) := eA.toCommRingCatIso.isIso_hom
  have : IsIso (CommRingCat.ofHom eB.toRingHom) := eB.toCommRingCatIso.isIso_hom
  have hmain := etaleAt_of_isIso_square (Spec.map (CommRingCat.ofHom eB.toRingHom))
    (Spec.map (CommRingCat.ofHom eA.toRingHom))
    (specMap_comp_eq_of_ringEquiv_square φ φ' eA eB hcomm) h
  rwa [hy] at hmain

/-- **The point of `Spec B'` above a given point of `Spec B`, lying above the closed point.** For
`A` and `A'` local and a commuting square `φ' ∘ eA = eB ∘ φ` with `eA` and `eB` isomorphisms, a
point of `Spec B` above the closed point of `Spec A` is the image of a point of `Spec B'` above the
closed point of `Spec A'`.

This is the forward transfer of the chosen point in the descent of [Stacks Project, Tag 0DT9]: the
point is chosen on the tensor product presentation of the new base ring and used on the invariant
ring of the base-changed groupoid, which the canonical map of Tag 03BK identifies with it. -/
theorem exists_point_specMap_of_ringEquiv_square [IsLocalRing A] [IsLocalRing A']
    (hcomm : φ'.comp eA.toRingHom = eB.toRingHom.comp φ) (x : Spec (.of B))
    (hx : (Spec.map (CommRingCat.ofHom φ)).base x =
      (IsLocalRing.closedPoint A : Spec (.of A))) :
    ∃ y : Spec (.of B'), (Spec.map (CommRingCat.ofHom eB.toRingHom)).base y = x ∧
      (Spec.map (CommRingCat.ofHom φ')).base y =
        (IsLocalRing.closedPoint A' : Spec (.of A')) := by
  have : IsIso (CommRingCat.ofHom eA.toRingHom) := eA.toCommRingCatIso.isIso_hom
  have : IsIso (CommRingCat.ofHom eB.toRingHom) := eB.toCommRingCatIso.isIso_hom
  have hvinj : Function.Injective (Spec.map (CommRingCat.ofHom eA.toRingHom)).base := by
    intro a b hab
    have h3 : (inv (Spec.map (CommRingCat.ofHom eA.toRingHom))).base
        ((Spec.map (CommRingCat.ofHom eA.toRingHom)).base a) =
        (inv (Spec.map (CommRingCat.ofHom eA.toRingHom))).base
        ((Spec.map (CommRingCat.ofHom eA.toRingHom)).base b) := by rw [hab]
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, IsIso.hom_inv_id] at h3
    simpa using h3
  have hB : (Spec.map (CommRingCat.ofHom eB.toRingHom)).base
      ((inv (Spec.map (CommRingCat.ofHom eB.toRingHom))).base x) = x := by
    rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
    rfl
  refine ⟨(inv (Spec.map (CommRingCat.ofHom eB.toRingHom))).base x, hB, hvinj ?_⟩
  rw [specMap_base_closedPoint_of_ringEquiv eA,
    ← Scheme.Hom.comp_apply (Spec.map (CommRingCat.ofHom φ'))
      (Spec.map (CommRingCat.ofHom eA.toRingHom)),
    specMap_comp_eq_of_ringEquiv_square φ φ' eA eB hcomm, Scheme.Hom.comp_apply, hB]
  exact hx

end AlgebraicGeometry

end

end
