module

public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowupSeparation
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FiniteLocallyFreePushPullUnranked
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineProper
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformOffExceptional
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedPermanence

/-!
# Surjectivity of a finite strict transform onto the blowup

Let `A` be an algebraic space over a scheme `S`, let `Z ⊆ A` be a closed subspace and let
`b : A' ⟶ A` be the blowup of `A` in `Z`. Let `f : X ⟶ A` be a morphism of algebraic spaces
and let `X' ⊆ X ×_A A'` be the strict transform of `X` with respect to `b`. Suppose that
`U ⊆ A` is an open subspace whose points are dense in `|A|`, disjoint from `|Z|`, and contained
in the image of `|f|`. If the projection `X' ⟶ A'` is finite, then it is surjective.

The argument is the following. A finite morphism is universally closed, so the image of
`|X'| ⟶ |A'|` is closed. Over the complement of the exceptional divisor `b⁻¹Z` the strict
transform contains the whole base change `X ×_A A'`, so every point of `|A'|` lying over `|U|`
is hit: it lifts, together with a point of `X` over the same point of `A`, to a point of
`X ×_A A'` by Stacks 03H4. Finally the points of `A'` over `|U|` are dense in `|A'|`. Indeed
the inverse image of `A ∖ Z` is dense, being the complement of an effective Cartier divisor
(Stacks 083S), and `b` restricts to an isomorphism `b⁻¹(A ∖ Z) ≅ A ∖ Z` (Stacks 085T), in
which the points of `U` are dense. A closed set containing a dense set is everything.

## Main results

* `AlgebraicGeometry.Space.dense_preimage_subspacePointSet_of_isBlowupAlong`: the points of
  the blowup lying over a dense open subspace are dense.
* `AlgebraicGeometry.Space.isSurjective_strictTransformSpaceToBlowUp_of_isFinite`: a finite
  strict transform maps onto the blowup, under the hypotheses above.
* `AlgebraicGeometry.Space.isSurjective_strictTransformSpaceToBlowUp_of_isFiniteLocallyFree`:
  the same with the projection assumed finite locally free.

## References

* [Stacks Project, Tag 0862](https://stacks.math.columbia.edu/tag/0862)
* [Stacks Project, Tag 085T](https://stacks.math.columbia.edu/tag/085T)
* [Stacks Project, Tag 083S](https://stacks.math.columbia.edu/tag/083S)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The points of a blowup over a dense open subspace are dense.**
Let `b : A' ⟶ A` be the blowup of an algebraic space `A` in a closed subspace `Z`, and let
`U ⊆ A` be an open subspace whose points are dense in `|A|`. Then the
inverse image of `|U|` under `|b|` is dense in `|A'|`.

The inverse image of `A ∖ Z` is dense by Stacks 083S, and `b` restricts to an isomorphism
`b⁻¹(A ∖ Z) ≅ A ∖ Z` by Stacks 085T; an open set of `|A'|` meeting `b⁻¹(A ∖ Z)` is therefore
carried to a nonempty open set of `|A ∖ Z|`, hence of `|A|`, which meets `|U|`. -/
theorem dense_preimage_subspacePointSet_of_isBlowupAlong {A A' : AlgebraicSpaces B S hS}
    (U : OpenSubspaces B S hS A.1) (Z : ClosedSubspaces B S hS A.1) {b : A' ⟶ A}
    (hb : IsBlowupAlong B S hS Z b) (hU : Dense (subspacePointSet B S hS A.1 U.1)) :
    Dense (pointsMap B S hS A'.1 b.hom ⁻¹' subspacePointSet B S hS A.1 U.1) := by
  set W := openComplementOfClosedSubspace B S hS A Z
  have hW : subspacePointSet B S hS A.1 W.1 = (subspacePointSet B S hS A.1 Z.1)ᶜ :=
    subspacePointSet_openComplement B S hS A Z
  have hV : Dense (subspacePointSet B S hS A'.1 (W.1.preimage b.hom)) :=
    dense_subspacePointSet_preimage_of_isBlowupAlong W Z hb (by rw [hW, compl_compl])
  have hiso := isIso_fromPreimage_openComplement hb
  set φ := W.1.fromPreimage b.hom
  have hinv : ∀ {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ⟶ G) (e' : G ⟶ F), e ≫ e' = 𝟙 F →
      ∀ x, pointsMap B S hS G e' (pointsMap B S hS F e x) = x := fun e e' h x => by
    rw [← pointsMap_comp_apply, h, pointsMap_id]
    rfl
  have hsq : ∀ y, pointsMap B S hS _ W.1.ι (pointsMap B S hS _ φ y) =
      pointsMap B S hS A'.1 b.hom (pointsMap B S hS _ (W.1.preimage b.hom).ι y) := fun y => by
    rw [← pointsMap_comp_apply, ← pointsMap_comp_apply, Subfunctor.fromPreimage_ι]
  refine dense_iff_inter_open.2 fun O hO ⟨a, ha⟩ => ?_
  obtain ⟨_, hyO, ⟨y, rfl⟩⟩ := hV.inter_open_nonempty O hO ⟨a, ha⟩
  set Q := pointsMap B S hS _ (W.1.preimage b.hom).ι ⁻¹' O
  have hQ : IsOpen Q := hO.preimage (continuous_pointsMap B S hS _)
  have hQ' : IsOpen (pointsMap B S hS _ (inv φ) ⁻¹' Q) :=
    hQ.preimage (continuous_pointsMap B S hS _)
  obtain ⟨_, ⟨⟨w, hwQ, rfl⟩, ⟨u, hu⟩⟩⟩ := hU.inter_open_nonempty _
    (isOpenMap_pointsMap_of_isOpenImmersion B S hS W.1.ι W.2.2 _ hQ')
    ⟨_, pointsMap B S hS _ φ y, by
      change pointsMap B S hS _ (inv φ) (pointsMap B S hS _ φ y) ∈ Q
      rw [hinv _ _ (IsIso.hom_inv_id φ)]
      exact hyO, rfl⟩
  refine ⟨pointsMap B S hS _ (W.1.preimage b.hom).ι (pointsMap B S hS _ (inv φ) w), hwQ, ?_⟩
  rw [Set.mem_preimage, ← hsq, hinv _ _ (IsIso.inv_hom_id φ)]
  exact ⟨u, hu⟩

/-- **A finite strict transform maps onto the blowup.** Let `b : A' ⟶ A` be the blowup of an
algebraic space `A` in a closed subspace `Z`, let `f : X ⟶ A` be a morphism of algebraic
spaces, and let `U ⊆ A` be an open subspace whose points are dense in `|A|`, disjoint from
`|Z|`, and contained in the image of `|f|`. If the projection from the strict transform of `X`
to `A'` is finite, then it is surjective.

Its image is closed because a finite morphism is universally closed. It contains every point of
`A'` over `|U|`: such a point lifts to `X ×_A A'` by Stacks 03H4, off the exceptional divisor,
where the strict transform is everything. These points are dense by
`AlgebraicGeometry.Space.dense_preimage_subspacePointSet_of_isBlowupAlong`. -/
theorem isSurjective_strictTransformSpaceToBlowUp_of_isFinite {A X A' : AlgebraicSpaces B S hS}
    (f : X ⟶ A) (U : OpenSubspaces B S hS A.1) (Z : ClosedSubspaces B S hS A.1) {b : A' ⟶ A}
    (hb : IsBlowupAlong B S hS Z b) (hU : Dense (subspacePointSet B S hS A.1 U.1))
    (hUZ : Disjoint (subspacePointSet B S hS A.1 U.1) (subspacePointSet B S hS A.1 Z.1))
    (hUf : subspacePointSet B S hS A.1 U.1 ⊆ Set.range (pointsMap B S hS _ f.hom))
    (hfin : IsFinite B S hS (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)).hom) :
    IsSurjective B S hS (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)).hom := by
  set s := strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)
  set E : ClosedSubspaces B S hS A'.1 :=
    ⟨Z.1.preimage b.hom, isClosedSubspace_preimage B S hS b.hom Z.1 A.2 A'.2 Z.2⟩
  set P := strictTransformPullback B S hS f b
  set pr₂ := strictTransformPullbackToBlowUp B S hS f b
  -- The image of the strict transform is closed.
  have hclosed : IsClosed (Set.range (pointsMap B S hS _ s.hom)) := by
    have hproper := ((isFinite_iff_isAffineHom_and_isProper B S hS
      (strictTransformSpace B S hS f b (Z.1.preimage b.hom)).2 A'.2 s.hom).1 hfin).2
    exact (isClosed_of_universallyClosed B S hS A'.2 s.hom hproper.2.2).isClosed_range
  -- Every point of `A'` over `|U|` is in the image.
  have hsub : pointsMap B S hS A'.1 b.hom ⁻¹' subspacePointSet B S hS A.1 U.1 ⊆
      Set.range (pointsMap B S hS _ s.hom) := by
    intro a' ha'
    obtain ⟨x, hx⟩ := hUf ha'
    obtain ⟨p, -, hp⟩ := exists_point_of_isPullback B S hS
      (AlgebraicSpaces.isPullback_fiberProduct B S hS f b) x a' hx
    have hpE : p ∈ subspacePointSet B S hS P.1
        ((openComplementOfClosedSubspace B S hS A' E).1.preimage pr₂.hom) := by
      rw [subspacePointSet_preimage, Set.mem_preimage, hp,
        subspacePointSet_openComplement]
      intro haE
      rw [show subspacePointSet B S hS A'.1 E.1 =
          pointsMap B S hS A'.1 b.hom ⁻¹' subspacePointSet B S hS A.1 Z.1 from
        subspacePointSet_preimage B S hS b.hom Z.1] at haE
      exact Set.disjoint_left.1 hUZ ha' haE
    obtain ⟨q, hq⟩ := hpE
    have hle := preimage_openComplement_le_strictTransformSubfunctor B S hS f b E
      (isEffectiveCartierDivisor_exceptionalDivisor hb)
    refine ⟨pointsMap B S hS _ (Subfunctor.homOfLe hle) q, ?_⟩
    change pointsMap B S hS _ (strictTransformSpaceι B S hS f b E.1 ≫ pr₂).hom _ = a'
    rw [ObjectProperty.FullSubcategory.comp_hom, pointsMap_comp, Function.comp_apply,
      ← Function.comp_apply (f := pointsMap B S hS _ (strictTransformSpaceι B S hS f b E.1).hom),
      ← pointsMap_comp]
    change pointsMap B S hS _ pr₂.hom
      (pointsMap B S hS _ (Subfunctor.homOfLe hle ≫ (strictTransformSubfunctor B S hS f b E.1).ι)
        q) = a'
    rw [Subfunctor.homOfLe_ι, hq, hp]
  -- A closed set containing a dense set is everything.
  have hdense := dense_preimage_subspacePointSet_of_isBlowupAlong B S hS U Z hb hU
  exact Set.range_eq_univ.1 (Set.eq_univ_of_univ_subset
    (hdense.closure_eq ▸ closure_minimal hsub hclosed))

/-- **A finite locally free strict transform maps onto the blowup.** This is
`AlgebraicGeometry.Space.isSurjective_strictTransformSpaceToBlowUp_of_isFinite` for a projection
which is finite locally free, hence finite by Stacks 0416. -/
theorem isSurjective_strictTransformSpaceToBlowUp_of_isFiniteLocallyFree
    {A X A' : AlgebraicSpaces B S hS}
    (f : X ⟶ A) (U : OpenSubspaces B S hS A.1) (Z : ClosedSubspaces B S hS A.1) {b : A' ⟶ A}
    (hb : IsBlowupAlong B S hS Z b) (hU : Dense (subspacePointSet B S hS A.1 U.1))
    (hUZ : Disjoint (subspacePointSet B S hS A.1 U.1) (subspacePointSet B S hS A.1 Z.1))
    (hUf : subspacePointSet B S hS A.1 U.1 ⊆ Set.range (pointsMap B S hS _ f.hom))
    (hfin : IsFiniteLocallyFree B S hS
      (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom))) :
    IsSurjective B S hS (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)).hom :=
  isSurjective_strictTransformSpaceToBlowUp_of_isFinite B S hS f U Z hb hU hUZ hUf
    (isFinite_and_isFlat_of_isFiniteLocallyFree B S hS _ hfin).1

end AlgebraicGeometry.Space

end
