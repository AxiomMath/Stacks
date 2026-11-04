module

public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.SupportedCounitStalkInputs
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.SupportedCounitStalkTorsion
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleFlatTopos

/-!
# The stalk rings of the points of the site at a point of `f^{-1}Z`

Let `f : Y ⟶ X` be a morphism of algebraic spaces, `ȳ` a geometric point of `Y` with image `x̄`.
The flatness of `f` at `ȳ` and the bijectivity of `𝒪_{X,x̄}/I_x̄ ⟶ 𝒪_{Y,ȳ}/I_x̄𝒪_{Y,ȳ}` are
statements about the étale local rings of Stacks 04KG and the canonical map
`AlgebraicGeometry.Space.etaleLocalRingMap` between them. The derived geometric stalks, the stalk
of a derived pullback and Stacks 0AET at the stalk ring of the point of the site are statements
over the stalk rings of the points of the small étale sites and the stalk map
`AlgebraicGeometry.Space.stalkStructureMap` between them. This file moves the two hypotheses
across `AlgebraicGeometry.Space.pointStalkRingEquiv`.

## Main results

* `IPowerTorsion.bijective_quotientMap_of_ringEquiv` and `IPowerTorsion.flat_of_ringEquiv`:
  bijectivity of `R/I ⟶ S/IS` and flatness move along ring isomorphisms of source and target
  compatible with the two ring maps.
* `AlgebraicGeometry.Space.pointStalkRingEquiv_stalkStructureMap`: the stalk map is the canonical
  map of étale local rings read through `pointStalkRingEquiv` at the two points.
* `AlgebraicGeometry.Space.flat_stalkStructureMap_of_isFlatAt` and
  `AlgebraicGeometry.Space.bijective_quotientMap_stalkStructureMap`: the two hypotheses of
  Stacks 05E9 for the stalk map at a point of `f^{-1}Z`.

## Implementation notes

The comparison of the stalk map with the canonical map of étale local rings is
`AlgebraicGeometry.Space.etaleLocalRingMapAsStalkMap_eq`. The identification of the stalk map
with the stalk ring map of the pullback of modules,
`AlgebraicGeometry.Space.stalkStructureMap_hom_eq_smallEtaleStalkPullbackRingMap`, is not
repeated here.

## References

* [Stacks Project, Tag 0AEU](https://stacks.math.columbia.edu/tag/0AEU)
* [Stacks Project, Tag 05E9](https://stacks.math.columbia.edu/tag/05E9)
* [Stacks Project, Tag 04NG](https://stacks.math.columbia.edu/tag/04NG)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

/-! ### Transport along ring isomorphisms -/

namespace IPowerTorsion

variable {A A' B B' : Type*} [CommRing A] [CommRing A'] [CommRing B] [CommRing B']

/-- **Bijectivity of `R/I ⟶ S/IS` moves along ring isomorphisms.** Let `eA : A ≅ A'`,
`eB : B ≅ B'` be ring isomorphisms carrying `c : A ⟶ B` to `c' : A' ⟶ B'`. If
`A'/I' ⟶ B'/I'B'` is bijective, so is `A/I ⟶ B/IB` for `I` the pullback of `I'`. -/
theorem bijective_quotientMap_of_ringEquiv (eA : A ≃+* A') (eB : B ≃+* B') (c : A →+* B)
    (c' : A' →+* B') (hc : ∀ a, c' (eA a) = eB (c a)) (I' : Ideal A')
    (h : Function.Bijective (Ideal.quotientMap (I'.map c') c' Ideal.le_comap_map)) :
    Function.Bijective
      (Ideal.quotientMap ((I'.comap (eA : A →+* A')).map c) c Ideal.le_comap_map) := by
  set J := I'.comap (eA : A →+* A')
  have hJ : J.map (eA : A →+* A') = I' := Ideal.map_comap_of_surjective _ eA.surjective I'
  have hL : (J.map c).map (eB : B →+* B') = I'.map c' := by
    rw [Ideal.map_map, ← hJ, Ideal.map_map]
    congr 1
    exact RingHom.ext fun a ↦ (hc a).symm
  let qA : A ⧸ J ≃+* A' ⧸ I' := Ideal.quotientEquiv J I' eA hJ.symm
  let qB : B ⧸ J.map c ≃+* B' ⧸ I'.map c' := Ideal.quotientEquiv _ _ eB hL.symm
  have hcomm : ∀ x, Ideal.quotientMap (I'.map c') c' Ideal.le_comap_map (qA x) =
      qB (Ideal.quotientMap (J.map c) c Ideal.le_comap_map x) := by
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    show Ideal.quotientMap (I'.map c') c' Ideal.le_comap_map
        (Ideal.quotientMap I' (eA : A →+* A') (Ideal.map_le_iff_le_comap.mp hJ.le)
          (Ideal.Quotient.mk J a)) =
      Ideal.quotientMap (I'.map c') (eB : B →+* B') (Ideal.map_le_iff_le_comap.mp hL.le)
        (Ideal.Quotient.mk (J.map c) (c a))
    simp only [Ideal.quotientMap_mk, RingHom.coe_coe, hc]
  have hfun : ⇑(Ideal.quotientMap (J.map c) c Ideal.le_comap_map) =
      qB.symm ∘ ⇑(Ideal.quotientMap (I'.map c') c' Ideal.le_comap_map) ∘ qA := by
    funext x
    simp [hcomm]
  rw [hfun]
  exact qB.symm.bijective.comp (h.comp qA.bijective)

/-- **Flatness moves along ring isomorphisms** of source and target compatible with the two
ring maps. -/
theorem flat_of_ringEquiv (eA : A ≃+* A') (eB : B ≃+* B') (c : A →+* B) (c' : A' →+* B')
    (hc : ∀ a, c' (eA a) = eB (c a)) (h : c'.Flat) : c.Flat := by
  have hc' : c = (eB.symm : B' →+* B).comp (c'.comp (eA : A →+* A')) :=
    RingHom.ext fun a ↦ by simp [hc]
  rw [hc', RingHom.Flat.comp_iff_of_bijective_left eB.symm.bijective,
    RingHom.Flat.comp_iff_of_bijective_right eA.bijective]
  exact h

end IPowerTorsion

/-! ### The stalk map at a point of `f^{-1}Z` -/

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y : AlgebraicSpaces B S hS}

/-- The ideal of the stalk ring of the point of the site at `x̄` corresponding to an ideal of the
étale local ring `𝒪_{X,x̄}`: its pullback along `AlgebraicGeometry.Space.pointStalkRingEquiv`. -/
def geometricStalkIdeal (x : GeometricPoint B S hS X.1)
    (I : Ideal (etaleLocalRing B S hS X.1 x)) : Ideal ↥(geometricStalkRing B S hS x) :=
  I.comap (pointStalkRingEquiv B S hS X x).toRingHom

/-- **The stalk map is the canonical map of étale local rings**, read through the comparison
`AlgebraicGeometry.Space.pointStalkRingEquiv` at the two geometric points. -/
theorem pointStalkRingEquiv_stalkStructureMap (f : Y ⟶ X) (y : GeometricPoint B S hS Y.1)
    (a : ((etaleSitePoint B S hS X.1 (geometricPointMap f.hom y) X.2).presheafFiber
      (A := CommRingCat.{u})).obj (smallEtaleRingedTopos B S hS X).O.obj) :
    etaleLocalRingMap Y.2 f.hom y (pointStalkRingEquiv B S hS X (geometricPointMap f.hom y) a) =
      pointStalkRingEquiv B S hS Y y ((stalkStructureMap B S hS f y).hom a) := by
  have h := congrArg (fun φ ↦ pointStalkRingEquiv B S hS Y y (φ.hom a))
    (etaleLocalRingMapAsStalkMap_eq (B := B) (S := S) (hS := hS) (f := f) (x := y))
  exact ((pointStalkRingEquiv B S hS Y y).apply_symm_apply _).symm.trans h

/-- **The stalk map is flat at a point where `f` is flat.** -/
theorem flat_stalkStructureMap_of_isFlatAt (f : Y ⟶ X) (y : GeometricPoint B S hS Y.1)
    (hf : IsFlatAt B S hS f.hom y.image) :
    (stalkStructureMap B S hS f y).hom.Flat :=
  IPowerTorsion.flat_of_ringEquiv (pointStalkRingEquiv B S hS X (geometricPointMap f.hom y))
    (pointStalkRingEquiv B S hS Y y) _ (etaleLocalRingMap Y.2 f.hom y)
    (pointStalkRingEquiv_stalkStructureMap f y)
    ((isFlatAt_iff_etaleLocalRingMap_flat Y.2 X.2 f.hom y).mp hf)

/-- **The stalk map is bijective modulo the ideal of `Z` at a point of `f^{-1}Z`.** If
`f^{-1}Z ⟶ Z` is an isomorphism and `f` is flat at the points of `f^{-1}Z`, then at a geometric
point `ȳ` of `f^{-1}Z` the stalk map induces a bijection modulo the stalk of the ideal of `Z`,
pulled back to the stalk ring of the point of the site
(`AlgebraicGeometry.Space.geometricStalkIdeal`). -/
theorem bijective_quotientMap_stalkStructureMap (f : Y ⟶ X) (Z : Subfunctor X.1)
    (hZ : IsClosedSubspace B S hS Z) (hfZ : IsIso (Z.fromPreimage f.hom))
    (hflat : ∀ p : points B S hS (Z.preimage f.hom).toFunctor,
      IsFlatAt B S hS f.hom
        (pointsMap B S hS (Z.preimage f.hom).toFunctor (Z.preimage f.hom).ι p))
    (y : GeometricPoint B S hS Y.1)
    (hy : y.image ∈
      Set.range (pointsMap B S hS (Z.preimage f.hom).toFunctor (Z.preimage f.hom).ι)) :
    Function.Bijective
      (Ideal.quotientMap
        ((geometricStalkIdeal (geometricPointMap f.hom y)
          (closedSubspaceStalkIdeal B S hS X ⟨Z, hZ⟩ (geometricPointMap f.hom y))).map
            (stalkStructureMap B S hS f y).hom)
        (stalkStructureMap B S hS f y).hom Ideal.le_comap_map) :=
  IPowerTorsion.bijective_quotientMap_of_ringEquiv
    (pointStalkRingEquiv B S hS X (geometricPointMap f.hom y)) (pointStalkRingEquiv B S hS Y y)
    _ (etaleLocalRingMap Y.2 f.hom y) (pointStalkRingEquiv_stalkStructureMap f y) _
    (bijective_quotientMap_closedSubspaceStalkIdeal X.2 Y.2 f.hom Z hZ hfZ hflat y hy)

end AlgebraicGeometry.Space

end
