module

public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupIsomorphismOffCentre
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcOpenSubspaceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformSpaceEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalFirstOrderThickening

/-!
# The strict transform contains the part lying off the exceptional preimage

Let `S` be a scheme, let `b : A' ⟶ A` be a morphism of algebraic spaces over `S`, let
`E ⊆ A'` be a closed subspace of its source and let `f : X ⟶ A` be an algebraic space over `A`.
The strict transform of `X` with respect to `(b, E)`, Stacks 0862 part (2) in the form
`AlgebraicGeometry.Space.strictTransformSubfunctor`, is a closed subspace of `X ×_A A'` cut out
by the ideal of sections supported on the exceptional preimage `|pr_{A'}^{-1}E|`.  **Off that
set the strict transform is everything**: this file proves that the open part of `X ×_A A'`
lying over the complement of `E` is contained in the strict transform, whenever `E` is an
effective Cartier divisor on `A'` — which is what the exceptional divisor of a blowup is.

## Main results

* `AlgebraicGeometry.Space.preimage_openComplement_le_strictTransformSubfunctor`: the inverse
  image under `pr_{A'}` of the open complement of `E` is contained in the strict transform.
* `AlgebraicGeometry.Space.range_le_strictTransformSubfunctor_of_points_notMem`: a morphism to
  `X ×_A A'` no point of whose source lies in the exceptional preimage lands in the strict
  transform.
* `AlgebraicGeometry.Space.subspacePointSet_preimage_openComplement`: the points of that open
  part are exactly the points outside the exceptional preimage.
* `AlgebraicGeometry.Space.offCentreBaseChange` and
  `AlgebraicGeometry.Space.isPullback_offCentreBaseChange`,
  `AlgebraicGeometry.Space.isEtale_offCentreBaseChange`,
  `AlgebraicGeometry.Space.range_offCentreBaseChange`: the base change
  `X ×_A (A' ∖ E) ⟶ X ×_A A'` of the open immersion, the cartesian square it sits in, its
  étaleness and its image.

## Implementation notes

The proof is by étale localization.  Write `A'_0 = A' ∖ E` for the open complement and
`can : X ×_A A'_0 ⟶ X ×_A A'` for the base change of its open immersion along `pr_{A'}`, which is
étale because an open immersion is and étaleness is stable under base change (Stacks 03FU).  The
inverse image of `E` in `A'_0` has no points, so the exceptional preimage of the second situation
is empty and the ideal of sections supported on it vanishes on every chart — a section with empty
support is zero, `AlgebraicGeometry.Space.eq_zero_of_supportOfSection_eq_empty`.  Hence the strict
transform of `X` for the pair `(A'_0 ⟶ A, E|_{A'_0})` is the whole of `X ×_A A'_0`, by the
injectivity half of Stacks 03MB.

Stacks 0863, part (2) in its geometry-free form
`AlgebraicGeometry.Space.strictTransformSubfunctor_eq_preimage_of_isEffectiveCartierDivisor`
then identifies that whole space with the inverse image along `can` of the strict transform of
`X`, so the inverse image is everything, which is exactly the assertion that the image of `can`
— the part of `X ×_A A'` lying off the exceptional preimage, by
`CategoryTheory.Subfunctor.range_eq_preimage_of_isPullback` — is contained in the strict
transform.  Effective Cartierness of `E` enters only through that identification.

## References

* [Stacks Project, Tag 0862](https://stacks.math.columbia.edu/tag/0862)
* [Stacks Project, Tag 0863](https://stacks.math.columbia.edu/tag/0863)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 03FU](https://stacks.math.columbia.edu/tag/03FU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {A X A' : AlgebraicSpaces B S hS} (f : X ⟶ A) (b : A' ⟶ A)
variable (E : ClosedSubspaces B S hS A'.1)

/-- The open complement of `E` in `A'`, as an algebraic space. -/
abbrev offCentreSpace : AlgebraicSpaces B S hS :=
  ⟨(openComplementOfClosedSubspace B S hS A' E).1.toFunctor,
    (openComplementOfClosedSubspace B S hS A' E).2.1⟩

/-- The open immersion of `offCentreSpace B S hS E` into `A'`. -/
abbrev offCentreSpaceι : offCentreSpace B S hS E ⟶ A' :=
  ObjectProperty.homMk (openComplementOfClosedSubspace B S hS A' E).1.ι

/-- The open immersion `A' ∖ E ⟶ A'` is étale. -/
theorem isEtale_offCentreSpaceι : IsEtale B S hS (offCentreSpaceι B S hS E).hom :=
  isEtale_ι_of_isOpenSubspace (openComplementOfClosedSubspace B S hS A' E).2

/-- The base change `X ×_A A'_0 ⟶ X ×_A A'` of the open immersion. -/
def offCentreBaseChange :
    strictTransformPullback B S hS f (offCentreSpaceι B S hS E ≫ b) ⟶
      strictTransformPullback B S hS f b :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS f b).lift
    (strictTransformPullbackToSource B S hS f (offCentreSpaceι B S hS E ≫ b))
    (strictTransformPullbackToBlowUp B S hS f (offCentreSpaceι B S hS E ≫ b) ≫
      offCentreSpaceι B S hS E)
    (by
      have h := (AlgebraicSpaces.isPullback_fiberProduct B S hS f
        (offCentreSpaceι B S hS E ≫ b)).w
      rw [Category.assoc]
      exact h)

/-- The base change `X ×_A A'_0 ⟶ X ×_A A'` commutes with the projections to `X`. -/
@[simp]
theorem offCentreBaseChange_toSource :
    offCentreBaseChange B S hS f b E ≫ strictTransformPullbackToSource B S hS f b =
      strictTransformPullbackToSource B S hS f (offCentreSpaceι B S hS E ≫ b) :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS f b).lift_fst _ _ _

/-- The base change `X ×_A A'_0 ⟶ X ×_A A'` covers the open immersion `A'_0 ⟶ A'` on the
second projections. -/
@[simp]
theorem offCentreBaseChange_toBlowUp :
    offCentreBaseChange B S hS f b E ≫ strictTransformPullbackToBlowUp B S hS f b =
      strictTransformPullbackToBlowUp B S hS f (offCentreSpaceι B S hS E ≫ b) ≫
        offCentreSpaceι B S hS E :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS f b).lift_snd _ _ _

/-- The square formed by `X ×_A A'_0 ⟶ X ×_A A'`, the open immersion `A'_0 ⟶ A'` and the
projections to `A'_0` and `A'` is cartesian. -/
theorem isPullback_offCentreBaseChange :
    IsPullback (strictTransformPullbackToBlowUp B S hS f (offCentreSpaceι B S hS E ≫ b))
      (offCentreBaseChange B S hS f b E) (offCentreSpaceι B S hS E)
      (strictTransformPullbackToBlowUp B S hS f b) := by
  refine IsPullback.of_bot ?_ (offCentreBaseChange_toBlowUp B S hS f b E).symm
    ((AlgebraicSpaces.isPullback_fiberProduct B S hS f b).flip)
  rw [offCentreBaseChange_toSource]
  exact (AlgebraicSpaces.isPullback_fiberProduct B S hS f
    (offCentreSpaceι B S hS E ≫ b)).flip

/-- The base change `X ×_A A'_0 ⟶ X ×_A A'` is étale. -/
theorem isEtale_offCentreBaseChange :
    IsEtale B S hS (offCentreBaseChange B S hS f b E).hom :=
  isEtale_of_isPullback B S hS _ _ _ _ (isPullback_offCentreBaseChange B S hS f b E)
    (isEtale_offCentreSpaceι B S hS E)

/-- The image of the open immersion `A'_0 ⟶ A'` is the open complement of `E`. -/
theorem range_offCentreSpaceι :
    Subfunctor.range (offCentreSpaceι B S hS E).hom =
      (openComplementOfClosedSubspace B S hS A' E).1 :=
  Subfunctor.range_ι (openComplementOfClosedSubspace B S hS A' E).1

/-- The image of `X ×_A A'_0 ⟶ X ×_A A'` is the inverse image under `pr_{A'}` of the open
complement of `E`. -/
theorem range_offCentreBaseChange :
    Subfunctor.range (offCentreBaseChange B S hS f b E).hom =
      (openComplementOfClosedSubspace B S hS A' E).1.preimage
        (strictTransformPullbackToBlowUp B S hS f b).hom := by
  have h := Subfunctor.range_eq_preimage_of_isPullback
    (AlgebraicSpaces.isPullback_hom B S hS (isPullback_offCentreBaseChange B S hS f b E).flip)
  rw [h, range_offCentreSpaceι]

/-- The inverse image of `E` in `A'_0 = A' ∖ E` has no points. -/
theorem subspacePointSet_preimage_offCentre_eq_empty :
    subspacePointSet B S hS (offCentreSpace B S hS E).1
      (E.1.preimage (offCentreSpaceι B S hS E).hom) = ∅ := by
  rw [show subspacePointSet B S hS (offCentreSpace B S hS E).1
      (E.1.preimage (offCentreSpaceι B S hS E).hom) =
      Set.range (pointsMap B S hS (E.1.preimage (offCentreSpaceι B S hS E).hom).toFunctor
        (E.1.preimage (offCentreSpaceι B S hS E).hom).ι) from rfl,
    range_pointsMap_preimage_ι]
  refine Set.eq_empty_iff_forall_notMem.2 fun x hx => ?_
  have hmem : pointsMap B S hS (offCentreSpace B S hS E).1 (offCentreSpaceι B S hS E).hom x ∈
      subspacePointSet B S hS A'.1 E.1 := hx
  have hcompl : pointsMap B S hS (offCentreSpace B S hS E).1 (offCentreSpaceι B S hS E).hom x ∈
      (subspacePointSet B S hS A'.1 E.1)ᶜ := by
    rw [← subspacePointSet_openComplement B S hS A' E]
    exact ⟨x, rfl⟩
  exact hcompl hmem

/-- The exceptional preimage in `X ×_A A'_0` of the inverse image of `E` in `A'_0` is empty. -/
theorem exceptionalPreimageSet_offCentre_eq_empty :
    exceptionalPreimageSet B S hS f (offCentreSpaceι B S hS E ≫ b)
      (E.1.preimage (offCentreSpaceι B S hS E).hom) = ∅ := by
  rw [exceptionalPreimageSet_eq_preimage,
    show Set.range (pointsMap B S hS (E.1.preimage (offCentreSpaceι B S hS E).hom).toFunctor
        (E.1.preimage (offCentreSpaceι B S hS E).hom).ι) = ∅ from
      subspacePointSet_preimage_offCentre_eq_empty B S hS E]
  exact Set.preimage_empty

/-- The strict transform of `X` with respect to `A'_0 ⟶ A` and the inverse image of `E` in
`A'_0` is the whole of `X ×_A A'_0`. -/
theorem strictTransformSubfunctor_offCentre_eq_top :
    strictTransformSubfunctor B S hS f (offCentreSpaceι B S hS E ≫ b)
      (E.1.preimage (offCentreSpaceι B S hS E).hom) = ⊤ := by
  have hbot : ∀ U : SmallEtale B S hS
      (strictTransformPullback B S hS f (offCentreSpaceι B S hS E ≫ b)).1,
      IsAffine ((BigFppfOver.toScheme B S hS).obj U.1.left) →
      (strictTransformIdealSubmodule B S hS f (offCentreSpaceι B S hS E ≫ b)
        (E.1.preimage (offCentreSpaceι B S hS E).hom)).toSubmodule.obj (op U) = ⊥ := by
    intro U _
    refine Submodule.eq_bot_iff _ |>.2 fun s hs => ?_
    have h := (mem_supportedSectionsSubmodule_iff B S hS _ _ _ _ U s).1 hs
    refine eq_zero_of_supportOfSection_eq_empty
      (F := moduleAddSheaf B S hS
        (strictTransformPullback B S hS f (offCentreSpaceι B S hS E ≫ b)).1
        (strictTransformPullback B S hS f (offCentreSpaceι B S hS E ≫ b)).2
        (SheafOfModules.unit (structureRingSheaf B S hS
          (strictTransformPullback B S hS f (offCentreSpaceι B S hS E ≫ b))))) U s ?_
    rw [exceptionalPreimageSet_offCentre_eq_empty B S hS f b E] at h
    exact Set.eq_empty_iff_forall_notMem.2 fun y hy => h hy
  refine le_antisymm le_top (le_sInf ?_)
  rintro Z ⟨hZ, hZle⟩
  refine le_of_forall_definingIdealAt_le B S hS _
    ⟨⊤, isClosedSubspace_top B S hS _⟩ ⟨Z, hZ⟩ fun U hU => ?_
  exact ((hZle U hU).trans (le_of_eq (hbot U hU))).trans bot_le

/-- **The strict transform contains the part of the ambient base change lying off the
exceptional preimage**, for `E` an effective Cartier divisor on `A'`. -/
theorem preimage_openComplement_le_strictTransformSubfunctor
    (hE : IsEffectiveCartierDivisor B S hS A' E) :
    (openComplementOfClosedSubspace B S hS A' E).1.preimage
        (strictTransformPullbackToBlowUp B S hS f b).hom ≤
      strictTransformSubfunctor B S hS f b E.1 := by
  have hstep := strictTransformSubfunctor_eq_preimage_of_isEffectiveCartierDivisor B S hS f b E hE
    f (offCentreSpaceι B S hS E ≫ b) (E.1.preimage (offCentreSpaceι B S hS E).hom)
    (offCentreBaseChange B S hS f b E) (isEtale_offCentreBaseChange B S hS f b E)
    (by
      rw [exceptionalPreimageSet_offCentre_eq_empty B S hS f b E]
      refine (Set.eq_empty_iff_forall_notMem.2 fun x hx => ?_).symm
      have hx' : pointsMap B S hS _ (offCentreBaseChange B S hS f b E).hom x ∈
          exceptionalPreimageSet B S hS f b E.1 := hx
      rw [exceptionalPreimageSet_eq_preimage] at hx'
      have hco : pointsMap B S hS _
          ((offCentreBaseChange B S hS f b E).hom ≫
            (strictTransformPullbackToBlowUp B S hS f b).hom) x =
          pointsMap B S hS _ (strictTransformPullbackToBlowUp B S hS f b).hom
            (pointsMap B S hS _ (offCentreBaseChange B S hS f b E).hom x) :=
        congrFun (pointsMap_comp B S hS _ _ _) x
      have hE2 : pointsMap B S hS _
          ((strictTransformPullbackToBlowUp B S hS f
              (offCentreSpaceι B S hS E ≫ b)).hom ≫ (offCentreSpaceι B S hS E).hom) x ∈
          subspacePointSet B S hS A'.1 E.1 := by
        rw [show ((strictTransformPullbackToBlowUp B S hS f
              (offCentreSpaceι B S hS E ≫ b)).hom ≫ (offCentreSpaceι B S hS E).hom) =
            ((offCentreBaseChange B S hS f b E) ≫
              (strictTransformPullbackToBlowUp B S hS f b)).hom from
          congrArg (fun φ : strictTransformPullback B S hS f
              (offCentreSpaceι B S hS E ≫ b) ⟶ A' => φ.hom)
            (offCentreBaseChange_toBlowUp B S hS f b E).symm]
        rw [show ((offCentreBaseChange B S hS f b E) ≫
              (strictTransformPullbackToBlowUp B S hS f b)).hom =
            (offCentreBaseChange B S hS f b E).hom ≫
              (strictTransformPullbackToBlowUp B S hS f b).hom from rfl, hco]
        exact hx'
      rw [pointsMap_comp] at hE2
      have hcompl : pointsMap B S hS (offCentreSpace B S hS E).1
          (offCentreSpaceι B S hS E).hom
            (pointsMap B S hS _ (strictTransformPullbackToBlowUp B S hS f
              (offCentreSpaceι B S hS E ≫ b)).hom x) ∈
          (subspacePointSet B S hS A'.1 E.1)ᶜ := by
        rw [← subspacePointSet_openComplement B S hS A' E]
        exact ⟨_, rfl⟩
      exact hcompl hE2)
  rw [strictTransformSubfunctor_offCentre_eq_top B S hS f b E] at hstep
  rw [← range_offCentreBaseChange B S hS f b E]
  exact (Subfunctor.preimage_eq_top_iff _ _).1 hstep.symm


/-- The points of the inverse image under `pr_{A'}` of the open complement of `E` are exactly the
points of `X ×_A A'` outside the exceptional preimage. -/
theorem subspacePointSet_preimage_openComplement :
    subspacePointSet B S hS (strictTransformPullback B S hS f b).1
        ((openComplementOfClosedSubspace B S hS A' E).1.preimage
          (strictTransformPullbackToBlowUp B S hS f b).hom) =
      (exceptionalPreimageSet B S hS f b E.1)ᶜ := by
  rw [show subspacePointSet B S hS (strictTransformPullback B S hS f b).1
      ((openComplementOfClosedSubspace B S hS A' E).1.preimage
        (strictTransformPullbackToBlowUp B S hS f b).hom) =
      Set.range (pointsMap B S hS
        ((openComplementOfClosedSubspace B S hS A' E).1.preimage
          (strictTransformPullbackToBlowUp B S hS f b).hom).toFunctor
        ((openComplementOfClosedSubspace B S hS A' E).1.preimage
          (strictTransformPullbackToBlowUp B S hS f b).hom).ι) from rfl,
    range_pointsMap_preimage_ι,
    show Set.range (pointsMap B S hS (openComplementOfClosedSubspace B S hS A' E).1.toFunctor
        (openComplementOfClosedSubspace B S hS A' E).1.ι) =
      (subspacePointSet B S hS A'.1 E.1)ᶜ from subspacePointSet_openComplement B S hS A' E,
    Set.preimage_compl, exceptionalPreimageSet_eq_preimage]

/-- For `E` an effective Cartier divisor on `A'`, a morphism `g : Y ⟶ X ×_A A'` no point of whose
image lies in the exceptional preimage factors through the strict transform. -/
theorem range_le_strictTransformSubfunctor_of_points_notMem
    (hE : IsEffectiveCartierDivisor B S hS A' E) {Y : AlgebraicSpaces B S hS}
    (g : Y ⟶ strictTransformPullback B S hS f b)
    (hg : Set.range (pointsMap B S hS Y.1 g.hom) ⊆
      (exceptionalPreimageSet B S hS f b E.1)ᶜ) :
    Subfunctor.range g.hom ≤ strictTransformSubfunctor B S hS f b E.1 := by
  have hopen : IsOpenSubspace B S hS
      ((openComplementOfClosedSubspace B S hS A' E).1.preimage
        (strictTransformPullbackToBlowUp B S hS f b).hom) :=
    isOpenSubspace_preimage B S hS _ _ A'.2 (strictTransformPullback B S hS f b).2
      (openComplementOfClosedSubspace B S hS A' E).2
  obtain ⟨h, hh⟩ := (factorsThrough_openSubspace_iff_points B S hS
    (strictTransformPullback B S hS f b).2 Y.2 _ hopen g.hom).2
    (by
      rw [show Set.range (pointsMap B S hS
            ((openComplementOfClosedSubspace B S hS A' E).1.preimage
              (strictTransformPullbackToBlowUp B S hS f b).hom).toFunctor
            ((openComplementOfClosedSubspace B S hS A' E).1.preimage
              (strictTransformPullbackToBlowUp B S hS f b).hom).ι) =
          (exceptionalPreimageSet B S hS f b E.1)ᶜ from
        subspacePointSet_preimage_openComplement B S hS f b E]
      exact hg)
  refine le_trans (le_of_eq_of_le (congrArg Subfunctor.range hh.symm) ?_)
    (preimage_openComplement_le_strictTransformSubfunctor B S hS f b E hE)
  exact le_of_le_of_eq (Subfunctor.range_comp_le h _) (Subfunctor.range_ι _)

end AlgebraicGeometry.Space

end
