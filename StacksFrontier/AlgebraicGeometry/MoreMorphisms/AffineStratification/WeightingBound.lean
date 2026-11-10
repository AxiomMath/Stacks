module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.AffineStratification.LevelSetBound
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.AffineMaxLocus
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.FibreSumMaximum
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.FinitePresentationModel
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.MaximalLocus
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme

/-!
# The affine stratification number of the target of a positively weighted quasi-finite morphism

Let `f : X ⟶ Y` be a surjective quasi-finite morphism with `X` affine and `Y` separated, and let
`w` be an everywhere positive weighting of `f`. The weighted fibre sum `∫_f w` is lower
semicontinuous, takes finitely many values, and each of its level sets is affine; so the level
sets stratify `Y` and bound its affine stratification number by the number of values.

## Main results

* `AlgebraicGeometry.affineStratificationNumber_le_ncard_separableDegreeWeightedFiberSum`: the
  affine stratification number of `Y` is at most the number of values of `∫_f w`.

## Implementation notes

Quasi-finiteness is expressed by `LocallyOfFiniteType` together with `LocallyQuasiFinite`;
quasi-compactness of `f` is automatic here, `f` being a morphism from an affine scheme to a
separated one and hence affine.

## References

* [Stacks Project, Tag 0F3S](https://stacks.math.columbia.edu/tag/0F3S)
* [Stacks Project, Tag 0F3R](https://stacks.math.columbia.edu/tag/0F3R)
* [Stacks Project, Tag 0F3L](https://stacks.math.columbia.edu/tag/0F3L)
* [Stacks Project, Tag 01ZT](https://stacks.math.columbia.edu/tag/01ZT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.ZariskiAndSeparation.ReducedInducedLocallyClosed

universe u

namespace AlgebraicGeometry

/-- The weighted fibre sum of a positive weighting of a quasi-finite morphism with
quasi-compact source takes finitely many values: it is nonnegative and attains a maximum. -/
private lemma finite_range_separableDegreeWeightedFiberSum
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    [CompactSpace X] (w : X → ℤ) (hw : IsWeighting f w) (hpositive : ∀ x, 0 < w x) :
    (Set.range (separableDegreeWeightedFiberSum f w)).Finite := by
  cases isEmpty_or_nonempty Y with
  | inl _ => exact Set.finite_range _
  | inr _ =>
    obtain ⟨d, hd⟩ := exists_isGreatest_range_separableDegreeWeightedFiberSum f hw
    refine (Set.finite_Icc (0 : ℤ) d).subset ?_
    rintro z ⟨y, rfl⟩
    exact ⟨separableDegreeWeightedFiberSum_nonneg f w (fun x ↦ (hpositive x).le) y,
      hd.2 ⟨y, rfl⟩⟩

/-- The maximum locus of a positive weighting of a quasi-finite morphism of affine schemes, not
necessarily of finite presentation, is an affine open. -/
private lemma exists_isAffineOpen_maxLocus_of_isAffine
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
    [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    (w : X → ℤ) (hw : IsWeighting f w) (hpos : ∀ x, 0 < w x) (d : ℤ)
    (hd : IsGreatest (Set.range (separableDegreeWeightedFiberSum f w)) d) :
    ∃ U : Y.Opens,
      (U : Set Y) = {y | separableDegreeWeightedFiberSum f w y = d} ∧ IsAffineOpen U := by
  obtain ⟨Z, j, p, _, _, _, _, hjp⟩ :=
    exists_isClosedImmersion_locallyQuasiFinite_finitePresentation_factorization f
  have hwj : IsWeighting (j ≫ p) w := by rwa [hjp]
  obtain ⟨T, i, k, _, _, _, _, _, hik⟩ :=
    exists_surjective_isClosedImmersion_finitePresentation_of_range_compl_isCompact j
      (isCompact_compl_range_of_isWeighting j p hwj hpos)
  have hif : i ≫ (k ≫ p) = f := by rw [← Category.assoc, hik, hjp]
  have hw' : IsWeighting (k ≫ p) (Function.extend i w (0 : T → ℤ)) :=
    IsWeighting.extend_of_isClosedImmersion i (by rwa [hif])
  have hpos' : ∀ t, 0 < Function.extend i w (0 : T → ℤ) t := by
    intro t
    obtain ⟨x, rfl⟩ := i.surjective t
    simpa only [i.isEmbedding.injective.extend_apply] using hpos x
  have hsum : separableDegreeWeightedFiberSum (k ≫ p) (Function.extend i w (0 : T → ℤ)) =
      separableDegreeWeightedFiberSum f w := by
    rw [separableDegreeWeightedFiberSum_extend_of_isPreimmersion, hif]
  obtain ⟨U, hU, hUa⟩ := exists_isAffineOpen_separableDegreeWeightedFiberSum_eq_max (k ≫ p)
    ⟨inferInstance, inferInstance, inferInstance⟩ _ hw' hpos' d (by rwa [hsum])
  exact ⟨U, by simpa only [hsum] using hU, hUa⟩

/-- For a surjective quasi-finite morphism from an affine scheme to a separated scheme, the
maximum locus of a positive weighting is an affine open. -/
private lemma exists_isAffineOpen_maxLocus
    {X Y : Scheme.{u}} [IsAffine X] [Y.IsSeparated] (f : X ⟶ Y)
    [Surjective f] [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    (w : X → ℤ) (hw : IsWeighting f w) (hpositive : ∀ x, 0 < w x) (d : ℤ)
    (hd : IsGreatest (Set.range (separableDegreeWeightedFiberSum f w)) d) :
    ∃ U : Y.Opens,
      (U : Set Y) = {y | separableDegreeWeightedFiberSum f w y = d} ∧ IsAffineOpen U := by
  have : IsAffineHom f := isAffineHom_of_isAffine_of_isSeparated f
  obtain ⟨U, hU, _⟩ :=
    exists_isFinite_restrict_separableDegreeWeightedFiberSum_maxLocus f
      f.finite_preimage_singleton w hw hpositive d hd
  have hUι : IsAffineHom U.ι := by
    constructor
    intro V hV
    have : IsAffine V.toScheme := hV
    have : IsAffine (f ⁻¹ᵁ V).toScheme := hV.preimage f
    have hwV : IsWeighting (f ∣_ V) (w ∘ (f ⁻¹ᵁ V).ι) :=
      IsWeighting.comp_of_isPullback hw (isPullback_morphismRestrict f V).flip
    have hsum : separableDegreeWeightedFiberSum f w ∘ V.ι =
        separableDegreeWeightedFiberSum (f ∣_ V) (w ∘ (f ⁻¹ᵁ V).ι) :=
      separableDegreeWeightedFiberSum_comp_of_isPullback f
        (f ⁻¹ᵁ V).ι (f ∣_ V) V.ι (isPullback_morphismRestrict f V).flip
        f.finite_preimage_singleton w
    have hVmax : IsAffineOpen (V.ι ⁻¹ᵁ U) := by
      by_cases hdV : d ∈ Set.range (separableDegreeWeightedFiberSum (f ∣_ V)
          (w ∘ (f ⁻¹ᵁ V).ι))
      · have hdV' : IsGreatest (Set.range (separableDegreeWeightedFiberSum (f ∣_ V)
            (w ∘ (f ⁻¹ᵁ V).ι))) d :=
          ⟨hdV, by rintro _ ⟨v, rfl⟩; rw [← hsum]; exact hd.2 ⟨V.ι v, rfl⟩⟩
        obtain ⟨T, hT, hTaff⟩ :=
          exists_isAffineOpen_maxLocus_of_isAffine (f ∣_ V) (w ∘ (f ⁻¹ᵁ V).ι) hwV
            (fun x ↦ hpositive _) d hdV'
        have hTV : T = V.ι ⁻¹ᵁ U := by
          ext v
          change v ∈ (T : Set V.toScheme) ↔ V.ι v ∈ (U : Set Y)
          rw [hT, hU]
          change _ = d ↔ _ = d
          rw [← hsum]
          rfl
        exact hTV ▸ hTaff
      · have hempty : V.ι ⁻¹ᵁ U = ⊥ := by
          ext v
          change V.ι v ∈ (U : Set Y) ↔ False
          rw [hU]
          exact ⟨fun hv ↦ hdV ⟨v, (congrFun hsum v).symm.trans hv⟩, False.elim⟩
        exact hempty ▸ isAffineOpen_bot _
    have hinter : IsAffineOpen (V ⊓ U) := by
      simpa only [Scheme.Hom.image_preimage_eq_opensRange_inf,
        Scheme.Opens.opensRange_ι] using hVmax.image_of_isOpenImmersion V.ι
    have hpre := hinter.preimage_of_isOpenImmersion U.ι (by
      simpa only [Scheme.Opens.opensRange_ι] using (inf_le_right : V ⊓ U ≤ U))
    convert hpre using 1
    ext y
    simp only [Scheme.Hom.coe_preimage, TopologicalSpace.Opens.coe_inf, Set.mem_preimage,
      Set.mem_inter_iff, iff_self_and]
    exact fun _ ↦ y.property
  have : IsAffine (f ⁻¹ᵁ U).toScheme :=
    IsAffine.of_isPullback (isPullback_morphismRestrict f U).flip
  have : Surjective (f ∣_ U) := MorphismProperty.of_isPullback
    (isPullback_morphismRestrict f U).flip (inferInstance : Surjective f)
  exact ⟨U, hU, Stacks.AffineFromFiniteSurjective.isAffine_of_finite_surjective (f ∣_ U)⟩

/-- The subscheme cut out by an ideal sheaf on a separated scheme is separated. -/
private lemma isSeparated_subscheme {Y : Scheme.{u}} [Y.IsSeparated] (J : Y.IdealSheafData) :
    J.subscheme.IsSeparated :=
  ⟨by simpa only [terminal.comp_from] using
    (inferInstance : IsSeparated (J.subschemeι ≫ terminal.from Y))⟩

/-- A level set of a lower semicontinuous function on a separated scheme is affine as soon as
the maximum locus of the function on every closed subscheme is an affine open of that closed
subscheme. -/
private lemma isAffine_reducedInduced_levelSet_of_isAffineOpen_maxLocus
    {Y : Scheme.{u}} [Y.IsSeparated] (F : Y → ℤ) (hF : LowerSemicontinuous F)
    (hmax : ∀ (J : Y.IdealSheafData) (d : ℤ),
      IsGreatest (Set.range (F ∘ J.subschemeι)) d →
      ∃ U : J.subscheme.Opens,
        (U : Set J.subscheme) = {y | F (J.subschemeι y) = d} ∧ IsAffineOpen U)
    (d : ℤ) :
    IsAffine (reducedInducedScheme {y | F y = d}
      (isLocallyClosed_levelSet_of_lowerSemicontinuous hF d)) := by
  classical
  by_cases hd : d ∈ Set.range F
  · let C : Closeds Y := ⟨F ⁻¹' Set.Iic d, hF.isClosed_preimage d⟩
    let J := Scheme.IdealSheafData.vanishingIdeal C
    have hrange : Set.range J.subschemeι = F ⁻¹' Set.Iic d := by
      rw [Scheme.IdealSheafData.range_subschemeι]
      exact Scheme.IdealSheafData.coe_support_vanishingIdeal C
    have hsub : {y | F y = d} ⊆ Set.range J.subschemeι :=
      hrange ▸ fun y (hy : F y = d) ↦ hy.le
    have hgreatest : IsGreatest (Set.range (F ∘ J.subschemeι)) d := by
      refine ⟨?_, ?_⟩
      · obtain ⟨y, hy⟩ := hd
        obtain ⟨x, rfl⟩ := hsub hy
        exact ⟨x, hy⟩
      · rintro z ⟨x, rfl⟩
        exact hrange.subset ⟨x, rfl⟩
    obtain ⟨U, hUeq, hUaff⟩ := hmax J d hgreatest
    have : IsAffine U.toScheme := hUaff
    have := isSeparated_subscheme J
    have : IsAffineHom U.ι := isAffineHom_of_isAffine_of_isSeparated U.ι
    refine (isAffine_reducedInduced_of_range_eq {y | F y = d}
      (isLocallyClosed_levelSet_of_lowerSemicontinuous hF d) (U.ι ≫ J.subschemeι) ?_).1
    change Set.range (J.subschemeι ∘ U.ι) = {y | F y = d}
    rw [Set.range_comp, Scheme.Opens.range_ι, hUeq]
    exact Set.image_preimage_eq_of_subset hsub
  · have : IsEmpty (reducedInducedScheme {y | F y = d}
        (isLocallyClosed_levelSet_of_lowerSemicontinuous hF d)) :=
      ⟨fun x ↦ hd ⟨reducedInducedInclusion _ _ x,
        (range_reducedInducedInclusion _ _).subset ⟨x, rfl⟩⟩⟩
    infer_instance

/-- Let `f : X ⟶ Y` be a surjective quasi-finite morphism of
schemes and let `w : X → ℤ_{>0}` be a positive weighting of `f`. If `X` is affine and `Y` is
separated, then the affine stratification number of `Y` is at most the number of distinct values
of the weighted fibre integral `∫_f w`. -/
@[stacks 0F3S]
theorem affineStratificationNumber_le_ncard_separableDegreeWeightedFiberSum
    {X Y : Scheme.{u}} [IsAffine X] [Y.IsSeparated] (f : X ⟶ Y)
    [Surjective f] [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    (w : X → ℤ) (hw : IsWeighting f w) (hpositive : ∀ x, 0 < w x) :
    affineStratificationNumber Y ≤
      (Set.range (separableDegreeWeightedFiberSum f w)).ncard := by
  classical
  have : IsAffineHom f := isAffineHom_of_isAffine_of_isSeparated f
  have hF := lowerSemicontinuous_separableDegreeWeightedFiberSum f
    f.finite_preimage_singleton w hw hpositive
  refine affineStratificationNumber_le_ncard_of_isAffine_levelSet _
    (finite_range_separableDegreeWeightedFiberSum f w hw hpositive) hF ?_
  refine isAffine_reducedInduced_levelSet_of_isAffineOpen_maxLocus _ hF ?_
  intro J d hd
  have := isSeparated_subscheme J
  have hw' : IsWeighting (pullback.snd f J.subschemeι)
      (w ∘ pullback.fst f J.subschemeι) :=
    IsWeighting.comp_of_isPullback hw (.of_hasPullback f J.subschemeι)
  have hsum := separableDegreeWeightedFiberSum_comp_of_isPullback f
    (pullback.fst f J.subschemeι) (pullback.snd f J.subschemeι)
    J.subschemeι (.of_hasPullback f J.subschemeι) f.finite_preimage_singleton w
  have hd' : IsGreatest (Set.range (separableDegreeWeightedFiberSum
      (pullback.snd f J.subschemeι) (w ∘ pullback.fst f J.subschemeι))) d := hsum ▸ hd
  obtain ⟨U, hUeq, hUaff⟩ := exists_isAffineOpen_maxLocus (pullback.snd f J.subschemeι)
    (w ∘ pullback.fst f J.subschemeι) hw' (fun x ↦ hpositive _) d hd'
  refine ⟨U, ?_, hUaff⟩
  rw [hUeq, ← hsum]
  rfl

end AlgebraicGeometry

end
