module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.ConstructiblePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.ReducedClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.GeneralLinearTwoPowerContraction
public import StacksFrontier.AlgebraicGeometry.Spaces.InfiniteFibreContractedPiece
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty

/-!
# The contracted piece of an infinite fibre, with its two rational points

The contraction step of [Stacks, Tag 0AEM] runs on a closed subvariety `C` of `(ℙ¹_k)^n` which
the given morphism maps to a point, *together with two distinct `k`-rational points `x, y` of
`C`* — those two points are what names the subset `I = {i | x_i = y_i}` of the coordinates the
morphism is then shown to factor through.  The source obtains them by passing to the algebraic
closure of `k`, "we only do this so we may argue using rational points".

This file produces exactly that datum.  Over an algebraically closed field the closed points of
a scheme locally of finite type are its rational points
(`AlgebraicGeometry.pointEquivClosedPoint`), so the two distinct closed points that
`AlgebraicGeometry.Space.exists_isIrreducible_mapsTo_of_infinite_fibre` extracts from an
infinite fibre become two distinct morphisms from the terminal presheaf, and each factors
through the reduced closed subspace on the extracted piece because its image on points lies
there (Stacks 03JJ at the reduced closed subspace).

## Main definitions

* `AlgebraicGeometry.Space.sitePointOfClosedPoint`: the closed point of a scheme in the big
  fppf site over an algebraically closed field `K`, as a section of the structure morphism in
  the site.
* `AlgebraicGeometry.Space.rationalPointOfClosedPoint`: the same, as a morphism from the
  terminal presheaf to the functor of points.

## Main results

* `AlgebraicGeometry.Space.pointsMap_rationalPointOfClosedPoint`: that rational point lies over
  the closed point it was built from.
* `AlgebraicGeometry.Space.rationalPointOfClosedPoint_ne`: distinct closed points give distinct
  rational points.
* `Space.exists_reducedClosedSubspace_pair_ne_of_infinite_fibre_projectiveLinePower`:
  the same at `(ℙ¹_K)^n`, the source of 0AEM.
* `AlgebraicGeometry.Space.exists_reducedClosedSubspace_pair_ne_of_infinite_fibre`: **the
  contracted-curve extraction step of Stacks 0AEM.** A morphism out of an algebraic space
  isomorphic to the functor of points of an object of the site proper over `Spec K` which has
  an infinite fibre over a closed point of the target admits an irreducible closed subset of
  its source whose reduced closed subspace is carried into that one point and which contains
  two distinct `K`-rational points.

## Implementation notes

Properness of the representing object is used twice and for different reasons: with local
finite type it makes the point space of the source Jacobson, so that the extracted piece has
closed points at all, and with quasi-compactness it makes it Noetherian, so that an infinite
closed subset has an infinite irreducible piece.

## References

* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 03IQ](https://stacks.math.columbia.edu/tag/03IQ)
* [Stacks Project, Tag 03JJ](https://stacks.math.columbia.edu/tag/03JJ)
* [Stacks Project, Tag 0AEM](https://stacks.math.columbia.edu/tag/0AEM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (K : Type u) [Field K] [IsAlgClosed K]
  (hK : B.Contains (Spec (CommRingCat.of K)))

/-! ### A closed point of a scheme of the site as a rational point -/

/-- **A closed point of a scheme locally of finite type over an algebraically closed field `K`,
as a `K`-rational point of the corresponding object of the big fppf site**: a section of the
structure morphism, the site being a full subcategory of schemes so that a morphism of schemes
over `Spec K` is a morphism of the site. -/
noncomputable def sitePointOfClosedPoint
    (U : BigFppfOver B (Spec (CommRingCat.of K)) hK)
    (hft : LocallyOfFiniteType (B.inclusion.map U.hom))
    (x : (BigFppfOver.toScheme B (Spec (CommRingCat.of K)) hK).obj U) (hx : IsClosed {x}) :
    (Over.mk (𝟙 (B.obj hK)) : BigFppfOver B (Spec (CommRingCat.of K)) hK) ⟶ U :=
  letI := hft
  Over.homMk (ObjectProperty.homMk (pointOfClosedPoint (B.inclusion.map U.hom) x hx))
    (ObjectProperty.hom_ext _ (pointOfClosedPoint_comp (B.inclusion.map U.hom) x hx))

/-- The morphism of schemes underlying
`AlgebraicGeometry.Space.sitePointOfClosedPoint` is Mathlib's rational point attached to a
closed point. -/
theorem toScheme_map_sitePointOfClosedPoint
    (U : BigFppfOver B (Spec (CommRingCat.of K)) hK)
    (hft : LocallyOfFiniteType (B.inclusion.map U.hom))
    (x : (BigFppfOver.toScheme B (Spec (CommRingCat.of K)) hK).obj U) (hx : IsClosed {x}) :
    (BigFppfOver.toScheme B (Spec (CommRingCat.of K)) hK).map
        (sitePointOfClosedPoint B K hK U hft x hx) =
      (letI := hft; pointOfClosedPoint (B.inclusion.map U.hom) x hx) := rfl

/-- **A closed point of a scheme of the site, as a morphism from the terminal presheaf to the
functor of points.**  This is the `K`-rational point the contraction step of
[Stacks, Tag 0AEM] argues with. -/
noncomputable def rationalPointOfClosedPoint
    (U : BigFppfOver B (Spec (CommRingCat.of K)) hK)
    (hft : LocallyOfFiniteType (B.inclusion.map U.hom))
    (x : (BigFppfOver.toScheme B (Spec (CommRingCat.of K)) hK).obj U) (hx : IsClosed {x}) :
    yoneda.obj (Over.mk (𝟙 (B.obj hK)) : BigFppfOver B (Spec (CommRingCat.of K)) hK) ⟶
      yoneda.obj U :=
  yoneda.map (sitePointOfClosedPoint B K hK U hft x hx)

/-- **The rational point attached to a closed point lies over that closed point.**  Both sides
are read through the identification of the point space of a represented presheaf with the
representing scheme, clause (1) of Stacks 03BX. -/
theorem pointsMap_rationalPointOfClosedPoint
    (U : BigFppfOver B (Spec (CommRingCat.of K)) hK)
    (hft : LocallyOfFiniteType (B.inclusion.map U.hom))
    (x : (BigFppfOver.toScheme B (Spec (CommRingCat.of K)) hK).obj U) (hx : IsClosed {x})
    (ξ : points B (Spec (CommRingCat.of K)) hK
      (yoneda.obj (Over.mk (𝟙 (B.obj hK)) : BigFppfOver B (Spec (CommRingCat.of K)) hK))) :
    pointsMap B (Spec (CommRingCat.of K)) hK _ (rationalPointOfClosedPoint B K hK U hft x hx) ξ =
      (schemePointsHomeomorph B (Spec (CommRingCat.of K)) hK U).symm x := by
  let := hft
  obtain ⟨z, rfl⟩ :=
    (schemePointsHomeomorph B (Spec (CommRingCat.of K)) hK
      (Over.mk (𝟙 (B.obj hK)))).symm.surjective ξ
  rw [rationalPointOfClosedPoint, schemePointsHomeomorph_symm_naturality,
    toScheme_map_sitePointOfClosedPoint, pointOfClosedPoint_apply]

/-- The rational point attached to a closed point has that closed point as its whole image on
points. -/
theorem range_pointsMap_rationalPointOfClosedPoint
    (U : BigFppfOver B (Spec (CommRingCat.of K)) hK)
    (hft : LocallyOfFiniteType (B.inclusion.map U.hom))
    (x : (BigFppfOver.toScheme B (Spec (CommRingCat.of K)) hK).obj U) (hx : IsClosed {x}) :
    Set.range (pointsMap B (Spec (CommRingCat.of K)) hK _
        (rationalPointOfClosedPoint B K hK U hft x hx)) ⊆
      {(schemePointsHomeomorph B (Spec (CommRingCat.of K)) hK U).symm x} :=
  Set.range_subset_iff.2 (pointsMap_rationalPointOfClosedPoint B K hK U hft x hx)

/-- **Distinct closed points give distinct rational points.**  The functor of points is
faithful, and the underlying morphism of schemes takes every point of `Spec K` to the closed
point it was built from. -/
theorem rationalPointOfClosedPoint_ne
    (U : BigFppfOver B (Spec (CommRingCat.of K)) hK)
    (hft : LocallyOfFiniteType (B.inclusion.map U.hom))
    (x₁ x₂ : (BigFppfOver.toScheme B (Spec (CommRingCat.of K)) hK).obj U)
    (hx₁ : IsClosed {x₁}) (hx₂ : IsClosed {x₂}) (hne : x₁ ≠ x₂) :
    rationalPointOfClosedPoint B K hK U hft x₁ hx₁ ≠
      rationalPointOfClosedPoint B K hK U hft x₂ hx₂ := by
  intro h
  have h₁ := pointsMap_rationalPointOfClosedPoint B K hK U hft x₁ hx₁
    ((schemePointsHomeomorph B (Spec (CommRingCat.of K)) hK (Over.mk (𝟙 (B.obj hK)))).symm
      (IsLocalRing.closedPoint K))
  rw [h, pointsMap_rationalPointOfClosedPoint] at h₁
  exact hne ((schemePointsHomeomorph B (Spec (CommRingCat.of K)) hK U).symm.injective h₁).symm

/-! ### The extraction -/

omit [IsAlgClosed K] in
/-- The terminal presheaf on the big fppf site over `Spec K` is étale-locally reduced: it is
represented by the identity of `Spec K`, and the spectrum of a field is reduced. -/
theorem hasEtaleLocalProperty_isReduced_base :
    HasEtaleLocalProperty B (Spec (CommRingCat.of K)) hK
      (yoneda.obj (Over.mk (𝟙 (B.obj hK)) : BigFppfOver B (Spec (CommRingCat.of K)) hK))
      (fun W : Scheme.{u} => IsReduced W) :=
  hasEtaleLocalProperty_of_representable B (Spec (CommRingCat.of K)) hK _ _
    (Over.mk (𝟙 (B.obj hK))) (Iso.refl _)
    (inferInstanceAs (IsReduced (Spec (CommRingCat.of K))))

/-- **The contracted-curve extraction step of [Stacks, Tag 0AEM].**  Let `K` be an algebraically
closed field, let `X` be an algebraic space over `Spec K` isomorphic to the functor of points of
an object `U` of the big fppf site which is proper over `Spec K` — for 0AEM, `X = (ℙ¹_K)^n` and
`U` the object representing it — and let `g : X ⟶ Z`.  If the fibre of `g` over a closed point
`y` of `|Z|` is infinite, then there is an irreducible closed subset `C` of `|X|` such that

* the reduced closed subspace on `C` is carried by `g` into the single point `y`, and
* two distinct `K`-rational points of `X` factor through that subspace.

These are the data the source's contraction argument runs on: a closed subvariety mapped to a
point, and two distinct rational points of it.  Properness of `U` is used twice: with local
finite type it makes `|X|` Jacobson, so that `C` has closed points at all, and with
quasi-compactness it makes `|X|` Noetherian, so that an infinite closed subset has an infinite
irreducible piece. -/
theorem exists_reducedClosedSubspace_pair_ne_of_infinite_fibre
    (U : BigFppfOver B (Spec (CommRingCat.of K)) hK)
    (hproper : _root_.AlgebraicGeometry.IsProper (B.inclusion.map U.hom))
    {X Z : (BigFppfOver B (Spec (CommRingCat.of K)) hK)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B (Spec (CommRingCat.of K)) hK X) (e : X ≅ yoneda.obj U)
    (g : X ⟶ Z) (y : points B (Spec (CommRingCat.of K)) hK Z) (hy : IsClosed {y})
    (hinf : {x : points B (Spec (CommRingCat.of K)) hK X |
      pointsMap B (Spec (CommRingCat.of K)) hK X g x = y}.Infinite) :
    ∃ (C : Set (points B (Spec (CommRingCat.of K)) hK X)) (hC : IsClosed C)
      (xi1 xi2 : yoneda.obj (Over.mk (𝟙 (B.obj hK)) :
        BigFppfOver B (Spec (CommRingCat.of K)) hK) ⟶ X),
      IsIrreducible C ∧
        Set.range (pointsMap B (Spec (CommRingCat.of K)) hK
          (reducedClosedSubspace B (Spec (CommRingCat.of K)) hK X hX C hC).toFunctor
          ((reducedClosedSubspace B (Spec (CommRingCat.of K)) hK X hX C hC).ι ≫ g)) ⊆ {y} ∧
        (∃ l, l ≫ (reducedClosedSubspace B (Spec (CommRingCat.of K)) hK X hX C hC).ι = xi1) ∧
        (∃ l, l ≫ (reducedClosedSubspace B (Spec (CommRingCat.of K)) hK X hX C hC).ι = xi2) ∧
        xi1 ≠ xi2 := by
  let := hproper
  have hft : LocallyOfFiniteType (B.inclusion.map U.hom) := inferInstance
  -- the point space of `X` is that of the representing scheme, a Noetherian Jacobson space
  set E := (pointsHomeomorphOfIso B (Spec (CommRingCat.of K)) hK e).trans
    (schemePointsHomeomorph B (Spec (CommRingCat.of K)) hK U)
  have hnoeth := noetherianSpace_points_of_iso B (Spec (CommRingCat.of K)) hK e
    (noetherianSpace_points_yoneda B (Spec (CommRingCat.of K)) hK U
      (noetherianSpace_of_isProper_over_field (B.inclusion.map U.hom)))
  have hjac := jacobsonSpace_points_of_iso B (Spec (CommRingCat.of K)) hK e
    (jacobsonSpace_points_yoneda B (Spec (CommRingCat.of K)) hK U
      (jacobsonSpace_of_locallyOfFiniteType_over_field (B.inclusion.map U.hom)))
  obtain ⟨C, p₁, p₂, hCclosed, hCirr, hCy, hp₁, hp₂, hp₁c, hp₂c, hne⟩ :=
    exists_isIrreducible_mapsTo_of_infinite_fibre B (Spec (CommRingCat.of K)) hK hnoeth hjac g y
      hy hinf
  have hclosed : ∀ p : points B (Spec (CommRingCat.of K)) hK X, IsClosed {p} →
      IsClosed {E p} := fun p hp ↦ by
    rw [← Set.image_singleton]
    exact E.isClosedMap _ hp
  -- the rational point of `X` at a closed point of `|X|`, read on the representing scheme
  have hpoint : ∀ (p : points B (Spec (CommRingCat.of K)) hK X) (hp : IsClosed {p}),
      Set.range (pointsMap B (Spec (CommRingCat.of K)) hK _
        (rationalPointOfClosedPoint B K hK U hft (E p) (hclosed p hp) ≫ e.inv)) ⊆ {p} := by
    rintro p hp w ⟨ζ, rfl⟩
    rw [pointsMap_comp B (Spec (CommRingCat.of K)) hK _
      (rationalPointOfClosedPoint B K hK U hft (E p) (hclosed p hp)) e.inv, Function.comp_apply,
      pointsMap_rationalPointOfClosedPoint]
    change (pointsHomeomorphOfIso B (Spec (CommRingCat.of K)) hK e).symm
      ((schemePointsHomeomorph B (Spec (CommRingCat.of K)) hK U).symm (E p)) ∈ ({p} : Set _)
    exact E.symm_apply_apply p
  have hlift : ∀ (p : points B (Spec (CommRingCat.of K)) hK X) (hp : IsClosed {p}), p ∈ C →
      ∃ l, l ≫ (reducedClosedSubspace B (Spec (CommRingCat.of K)) hK X hX C hCclosed).ι =
        rationalPointOfClosedPoint B K hK U hft (E p) (hclosed p hp) ≫ e.inv :=
    fun p hp hpC ↦ (exists_lift_reducedClosedSubspace_iff_pointsMap_range_subset B
      (Spec (CommRingCat.of K)) hK X hX C hCclosed
      (isAlgebraicSpace_yoneda B (Spec (CommRingCat.of K)) hK _)
      (hasEtaleLocalProperty_isReduced_base B K hK) _).2
      ((hpoint p hp).trans (Set.singleton_subset_iff.2 hpC))
  exact ⟨C, hCclosed,
    rationalPointOfClosedPoint B K hK U hft (E p₁) (hclosed p₁ hp₁c) ≫ e.inv,
    rationalPointOfClosedPoint B K hK U hft (E p₂) (hclosed p₂ hp₂c) ≫ e.inv, hCirr,
    range_pointsMap_reducedClosedSubspace_comp_subset B (Spec (CommRingCat.of K)) hK hX g y C
      hCclosed hCy, hlift p₁ hp₁c hp₁, hlift p₂ hp₂c hp₂,
    fun h ↦ rationalPointOfClosedPoint_ne B K hK U hft (E p₁) (E p₂) (hclosed p₁ hp₁c)
      (hclosed p₂ hp₂c) (fun h' ↦ hne (E.injective h')) ((cancel_mono e.inv).1 h)⟩

/-! ### The extraction at a finite power of the projective line -/

omit [IsAlgClosed K] in
/-- The structure morphism of the object of the big fppf site representing `(ℙ¹_K)^n` is proper:
it is the structure morphism of the `n`-fold self-product of `ℙ¹_K` over `Spec K`. -/
theorem isProper_projectiveSpacePowerSiteObject (n : ℕ) :
    _root_.AlgebraicGeometry.IsProper
      (B.inclusion.map (projectiveSpacePowerSiteObject K B hK n).hom) :=
  isProper_projectiveSpacePowerOver K n

/-- **The contracted-curve extraction step of [Stacks, Tag 0AEM] at its own source.**  Let `K`
be an algebraically closed field and let `g : (ℙ¹_K)^n ⟶ Z` have an infinite fibre over a closed
point `y` of `|Z|`.  Then there is an irreducible closed subset `C` of `|(ℙ¹_K)^n|` whose
reduced closed subspace is carried by `g` into `y` alone, and two distinct `K`-rational points
of `(ℙ¹_K)^n` factor through that subspace.

This is
`AlgebraicGeometry.Space.exists_reducedClosedSubspace_pair_ne_of_infinite_fibre` at the object
of the site representing `(ℙ¹_K)^n`, which is proper over `Spec K`. -/
theorem exists_reducedClosedSubspace_pair_ne_of_infinite_fibre_projectiveLinePower (n : ℕ)
    {Z : (BigFppfOver B (Spec (CommRingCat.of K)) hK)ᵒᵖ ⥤ Type u}
    (g : projectiveLinePower K B hK (Fin n) ⟶ Z)
    (y : points B (Spec (CommRingCat.of K)) hK Z) (hy : IsClosed {y})
    (hinf : {x : points B (Spec (CommRingCat.of K)) hK (projectiveLinePower K B hK (Fin n)) |
      pointsMap B (Spec (CommRingCat.of K)) hK (projectiveLinePower K B hK (Fin n)) g x =
        y}.Infinite) :
    ∃ (C : Set (points B (Spec (CommRingCat.of K)) hK (projectiveLinePower K B hK (Fin n))))
      (hC : IsClosed C)
      (xi1 xi2 : yoneda.obj (Over.mk (𝟙 (B.obj hK)) :
        BigFppfOver B (Spec (CommRingCat.of K)) hK) ⟶ projectiveLinePower K B hK (Fin n)),
      IsIrreducible C ∧
        Set.range (pointsMap B (Spec (CommRingCat.of K)) hK
          (reducedClosedSubspace B (Spec (CommRingCat.of K)) hK
            (projectiveLinePower K B hK (Fin n))
            (isAlgebraicSpace_projectiveLinePowerFin K B hK n) C hC).toFunctor
          ((reducedClosedSubspace B (Spec (CommRingCat.of K)) hK
            (projectiveLinePower K B hK (Fin n))
            (isAlgebraicSpace_projectiveLinePowerFin K B hK n) C hC).ι ≫ g)) ⊆ {y} ∧
        (∃ l, l ≫ (reducedClosedSubspace B (Spec (CommRingCat.of K)) hK
          (projectiveLinePower K B hK (Fin n))
          (isAlgebraicSpace_projectiveLinePowerFin K B hK n) C hC).ι = xi1) ∧
        (∃ l, l ≫ (reducedClosedSubspace B (Spec (CommRingCat.of K)) hK
          (projectiveLinePower K B hK (Fin n))
          (isAlgebraicSpace_projectiveLinePowerFin K B hK n) C hC).ι = xi2) ∧
        xi1 ≠ xi2 :=
  exists_reducedClosedSubspace_pair_ne_of_infinite_fibre B K hK
    (projectiveSpacePowerSiteObject K B hK n) (isProper_projectiveSpacePowerSiteObject B K hK n)
    (isAlgebraicSpace_projectiveLinePowerFin K B hK n)
    (projectiveSpacePowerYonedaIso K B hK n).symm g y hy hinf

end AlgebraicGeometry.Space

end
