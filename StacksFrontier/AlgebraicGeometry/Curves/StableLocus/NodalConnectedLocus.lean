module

public import StacksFrontier.AlgebraicGeometry.Curves.NodalLocus
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedPullback09US
public import StacksFrontier.AlgebraicGeometry.Curves.NodalFamilyCriterion
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FibreConnectedComponents.LocalConstancy
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.GeometricallyConnectedFibres
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedBaseChange
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ProperGlobalSections

/-!
# The nodal and the geometrically connected loci of a proper flat family

Let `π : Z ⟶ T` be proper, flat and of finite presentation. This file produces opens of `T` whose
membership is tested on the fibres over field-valued points:

* `U₀`: a field-valued point `Spec K ⟶ T` lands in `U₀` exactly when the fibre `Z_K` is
  at-worst-nodal of relative dimension one over `K`; the restriction of `π` to `U₀` is
  at-worst-nodal of relative dimension one. It is the complement of the image of the closed
  complement of the nodal locus `AlgebraicGeometry.nodalLocus` (Stacks 0DSC), using that the nodal
  locus commutes with base change.
* `U₁ ⊆ U₀`: a field-valued point of `U₀` lands in `U₁` exactly when the fibre is geometrically
  connected; it is the locus where the number of geometric connected components is one, which is
  locally constant because the fibres are geometrically reduced (Stacks 0E0N).

These are the first two steps of the openness of the stable locus in a family of curves
(Stacks 0E76), for a family whose total space is a scheme.

## Main results

* `AlgebraicGeometry.exists_isPullback_restrict_of_mem`: a field-valued point landing in an open
  `U` of the base presents its fibre as a fibre of the restriction of the family to `U`.
* `AlgebraicGeometry.exists_opens_isAtWorstNodal_restrict_and_forall_mem_iff`: the open `U₀`.
* `AlgebraicGeometry.exists_opens_geometricallyConnected_restrict_and_forall_mem_iff`: the open
  `U₁`.

## References

* [Stacks Project, Tag 0E76](https://stacks.math.columbia.edu/tag/0E76)
* [Stacks Project, Tag 0DSC](https://stacks.math.columbia.edu/tag/0DSC)
* [Stacks Project, Tag 0E0N](https://stacks.math.columbia.edu/tag/0E0N)
* [Stacks Project, Tag 055F](https://stacks.math.columbia.edu/tag/055F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The image of a field-valued point of a scheme is its closed point. -/
private theorem range_eq_singleton_closedPoint {T : Scheme.{u}} {K : Type u} [Field K]
    (y : Spec (CommRingCat.of K) ⟶ T) : Set.range y = {y (IsLocalRing.closedPoint K)} := by
  ext t
  refine ⟨?_, fun ht => ⟨IsLocalRing.closedPoint K, ht.symm⟩⟩
  rintro ⟨z, rfl⟩
  rw [Subsingleton.elim z (IsLocalRing.closedPoint K)]
  rfl

/-- **A field-valued point landing in an open of the base presents its fibre as a fibre of the
restriction.** If `y : Spec K ⟶ T` lands in `U` and `q ≫ π = fV ≫ y` is cartesian, then `y` and `q`
factor through `U` and `π⁻¹ U`, and the factored square is cartesian over `π ∣_ U`. -/
theorem exists_isPullback_restrict_of_mem {Z T V : Scheme.{u}} (π : Z ⟶ T) (U : T.Opens)
    {K : Type u} [Field K] {y : Spec (CommRingCat.of K) ⟶ T} {q : V ⟶ Z}
    {fV : V ⟶ Spec (CommRingCat.of K)} (sq : IsPullback q fV π y)
    (hy : y (IsLocalRing.closedPoint K) ∈ U) :
    ∃ (y' : Spec (CommRingCat.of K) ⟶ U) (q' : V ⟶ π ⁻¹ᵁ U), y' ≫ U.ι = y ∧
      q' ≫ (π ⁻¹ᵁ U).ι = q ∧ IsPullback q' fV (π ∣_ U) y' := by
  have hrange : Set.range y.base ⊆ Set.range U.ι.base := by
    rw [U.range_ι]
    exact (range_eq_singleton_closedPoint y).trans_subset (Set.singleton_subset_iff.mpr hy)
  let y' := IsOpenImmersion.lift U.ι y hrange
  have hy' : y' ≫ U.ι = y := IsOpenImmersion.lift_fac _ _ _
  have hR := (isPullback_morphismRestrict π U).flip
  let q' : V ⟶ π ⁻¹ᵁ U := hR.lift q (fV ≫ y') (by rw [Category.assoc, hy', sq.w])
  have hq' : q' ≫ (π ⁻¹ᵁ U).ι = q := hR.lift_fst _ _ _
  exact ⟨y', q', hy', hq', IsPullback.of_right (by rwa [hq', hy']) (hR.lift_snd _ _ _) hR⟩

/-- A morphism is at-worst-nodal of relative dimension one exactly when its nodal locus is
everything. -/
theorem nodalLocus_eq_top_iff {X S : Scheme.{u}} (f : X ⟶ S) :
    nodalLocus f = ⊤ ↔ IsAtWorstNodalOfRelativeDimensionOne f := by
  constructor
  · intro h
    have h1 := nodalLocus_isAtWorstNodalOfRelativeDimensionOne f
    rw [h] at h1
    exact IsZariskiLocalAtSource.of_iSup_eq_top (fun _ : Unit => (⊤ : X.Opens))
      (iSup_const) (fun _ => h1)
  · intro h
    exact top_le_iff.mp (le_nodalLocus f (IsZariskiLocalAtSource.comp h _))

/-- **The nodal locus of the base.** For `π : Z ⟶ T` proper, flat and of finite presentation there
is an open `U ⊆ T` over which `π` is at-worst-nodal of relative dimension one, and a field-valued
point `y : Spec K ⟶ T` lands in `U` exactly when the fibre `fV : Z_K ⟶ Spec K` is at-worst-nodal of
relative dimension one: `U` is the complement of the image of the closed complement of the nodal
locus of `π` (Stacks 0DSC), which commutes with base change. -/
theorem exists_opens_isAtWorstNodal_restrict_and_forall_mem_iff {Z T : Scheme.{u}} (π : Z ⟶ T)
    [IsProper π] [Flat π] [LocallyOfFinitePresentation π] :
    ∃ U : T.Opens, IsAtWorstNodalOfRelativeDimensionOne (π ∣_ U) ∧
      ∀ (K : Type u) [Field K] (V : Scheme.{u}) (y : Spec (CommRingCat.of K) ⟶ T) (q : V ⟶ Z)
        (fV : V ⟶ Spec (CommRingCat.of K)), IsPullback q fV π y →
        (y (IsLocalRing.closedPoint K) ∈ U ↔ IsAtWorstNodalOfRelativeDimensionOne fV) := by
  let N := nodalLocus π
  have hclosed : IsClosed (π '' (N : Set Z)ᶜ) :=
    π.isClosedMap _ N.isOpen.isClosed_compl
  let U : T.Opens := ⟨(π '' (N : Set Z)ᶜ)ᶜ, hclosed.isOpen_compl⟩
  have hU : ∀ t : T, t ∈ U ↔ ∀ z : Z, π z = t → z ∈ N := by
    intro t
    change t ∈ (π '' (N : Set Z)ᶜ)ᶜ ↔ _
    simp only [Set.mem_compl_iff, Set.mem_image, not_exists, not_and]
    exact ⟨fun h z hz => by_contra fun hn => h z hn hz, fun h z hn hz => hn (h z hz)⟩
  refine ⟨U, ?_, fun K _ V y q fV sq => ?_⟩
  · rw [← nodalLocus_eq_top_iff,
      nodalLocus_baseChange _ _ _ _ (isPullback_morphismRestrict π U).flip]
    exact top_le_iff.mp fun z _ => (hU _).mp z.2 _ rfl
  · rw [← nodalLocus_eq_top_iff, nodalLocus_baseChange q fV π y sq, hU]
    have hr := range_eq_preimage_range_of_isPullback sq
    have hy := range_eq_singleton_closedPoint y
    constructor
    · intro h
      refine top_le_iff.mp fun v _ => h (q v) ?_
      have hv : q v ∈ π ⁻¹' Set.range y := hr ▸ ⟨v, rfl⟩
      rwa [hy] at hv
    · intro h z hz
      obtain ⟨v, rfl⟩ : z ∈ Set.range q := by rwa [hr, hy]
      exact (h ▸ trivial : v ∈ q ⁻¹ᵁ N)

/-- **The fibre over a field-valued point is a base change of the fibre over the residue field.**
If `y : Spec K ⟶ T` hits `t` and `q ≫ π = fV ≫ y` is cartesian, then `y` factors through
`Spec κ(t)` by a field extension `φ : κ(t) ⟶ K`, and `V` is the base change of the fibre
`π⁻¹(t) ⟶ Spec κ(t)` along `Spec K ⟶ Spec κ(t)`. -/
theorem exists_isPullback_fiberToSpecResidueField {Z T V : Scheme.{u}} (π : Z ⟶ T)
    {K : Type u} [Field K] {y : Spec (CommRingCat.of K) ⟶ T} {q : V ⟶ Z}
    {fV : V ⟶ Spec (CommRingCat.of K)} (sq : IsPullback q fV π y) :
    ∃ (φ : T.residueField (y (IsLocalRing.closedPoint K)) ⟶ CommRingCat.of K)
      (a : V ⟶ π.fiber (y (IsLocalRing.closedPoint K))),
      Spec.map φ ≫ T.fromSpecResidueField (y (IsLocalRing.closedPoint K)) = y ∧
      a ≫ π.fiberι (y (IsLocalRing.closedPoint K)) = q ∧
      IsPullback a fV (π.fiberToSpecResidueField (y (IsLocalRing.closedPoint K))) (Spec.map φ) := by
  let t := y (IsLocalRing.closedPoint K)
  let φ := T.descResidueField (Scheme.stalkClosedPointTo y)
  have hy : Spec.map φ ≫ T.fromSpecResidueField t = y :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K T y
  have hF := IsPullback.of_hasPullback π (T.fromSpecResidueField t)
  let a : V ⟶ π.fiber t := hF.lift q (fV ≫ Spec.map φ) (by rw [Category.assoc, hy, sq.w])
  have ha : a ≫ π.fiberι t = q := hF.lift_fst _ _ _
  refine ⟨φ, a, hy, ha, IsPullback.of_right ?_ (hF.lift_snd _ _ _) hF⟩
  change IsPullback (a ≫ π.fiberι t) fV π (Spec.map φ ≫ T.fromSpecResidueField t)
  rwa [ha, hy]

/-- **Geometric connectedness is unchanged by extension of the ground field**, for a base change
presented by an arbitrary cartesian square over `Spec K ⟶ Spec κ`. -/
theorem geometricallyConnected_iff_of_isPullback_specMap {W V : Scheme.{u}} {κ K : Type u}
    [Field κ] [Field K] (φ : CommRingCat.of κ ⟶ CommRingCat.of K) (h : W ⟶ Spec (CommRingCat.of κ))
    {a : V ⟶ W} {fV : V ⟶ Spec (CommRingCat.of K)} (sq : IsPullback a fV h (Spec.map φ)) :
    GeometricallyConnected h ↔ GeometricallyConnected fV := by
  let : Algebra κ K := φ.hom.toAlgebra
  rw [geometricallyConnected_iff_baseChange_fieldExtension κ K h]
  have hφ : Spec.map (CommRingCat.ofHom (algebraMap κ K)) = Spec.map φ := rfl
  have : MorphismProperty.RespectsIso (@GeometricallyConnected) := by
    rw [GeometricallyConnected.eq_geometrically]; infer_instance
  rw [hφ]
  refine (MorphismProperty.arrow_mk_iso_iff (P := @GeometricallyConnected)
    (Arrow.isoMk sq.isoPullback (Iso.refl _) ?_)).symm
  simp [sq.isoPullback_hom_snd]

/-- **An at-worst-nodal morphism of relative dimension one is geometrically reduced**: every
nonempty fibre is a curve with at-worst-nodal singularities over its residue field, hence
geometrically reduced ([Stacks, Tag 0E37]), and an empty fibre is reduced after any base change. -/
theorem geometricallyReduced_of_isAtWorstNodalOfRelativeDimensionOne {X S : Scheme.{u}}
    (f : X ⟶ S) (hf : IsAtWorstNodalOfRelativeDimensionOne f) : GeometricallyReduced f := by
  obtain ⟨-, hlfp, h⟩ := (Stacks.Curves.hasAtWorstNodalFibresOfDimensionOne_iff f).mpr hf
  have : LocallyOfFinitePresentation f := hlfp
  refine ⟨geometrically_iff_forall_fiberToSpecResidueField.mpr fun s => ?_⟩
  by_cases hne : Nonempty (f.fiber s)
  · let : (f.fiber s).Over (Spec (.of (S.residueField s))) := ⟨f.fiberToSpecResidueField s⟩
    have : LocallyOfFiniteType (f.fiber s ↘ Spec (.of (S.residueField s))) :=
      inferInstanceAs (LocallyOfFiniteType (f.fiberToSpecResidueField s))
    obtain ⟨heq, hdim, hnodal⟩ := h s hne
    exact (Stacks.Curves.geometricallyReduced_of_hasAtWorstNodalSingularities _ _ heq hdim
      hnodal).geometrically_isReduced
  · intro K _ y Z fst snd _
    have : IsEmpty (f.fiber s) := not_nonempty_iff.mp hne
    have : IsEmpty Z := ⟨fun z => isEmptyElim (fst z)⟩
    exact @isReduced_of_isReduced_stalk Z fun z => isEmptyElim z

/-- **The geometrically connected locus of a nodal family.** For `π : Z ⟶ T` proper and
at-worst-nodal of relative dimension one there is an open `U ⊆ T` over which `π` is geometrically
connected, and a field-valued point `y : Spec K ⟶ T` lands in `U` exactly when the fibre
`fV : Z_K ⟶ Spec K` is geometrically connected: `U` is the locus where the number of geometric
connected components of the fibre is one, which is locally constant (Stacks 0E0N) because the
fibres are geometrically reduced. -/
theorem exists_opens_geometricallyConnected_restrict_and_forall_mem_iff {Z T : Scheme.{u}}
    (π : Z ⟶ T) [IsProper π] (hπ : IsAtWorstNodalOfRelativeDimensionOne π) :
    ∃ U : T.Opens, GeometricallyConnected (π ∣_ U) ∧
      ∀ (K : Type u) [Field K] (V : Scheme.{u}) (y : Spec (CommRingCat.of K) ⟶ T) (q : V ⟶ Z)
        (fV : V ⟶ Spec (CommRingCat.of K)), IsPullback q fV π y →
        (y (IsLocalRing.closedPoint K) ∈ U ↔ GeometricallyConnected fV) := by
  obtain ⟨hflat, hlfp, -⟩ := (Stacks.Curves.hasAtWorstNodalFibresOfDimensionOne_iff π).mpr hπ
  have : Flat π := hflat
  have : LocallyOfFinitePresentation π := hlfp
  have hred := (geometricallyReduced_iff_forall_isAlgClosed π).1
    (geometricallyReduced_of_isAtWorstNodalOfRelativeDimensionOne π hπ)
  have hlc := isLocallyConstant_numGeometricConnectedComponents π hred
  let U : T.Opens := ⟨numGeometricConnectedComponents π ⁻¹' {1}, hlc.isOpen_fiber 1⟩
  have key : ∀ (K : Type u) [Field K] (V : Scheme.{u}) (y : Spec (CommRingCat.of K) ⟶ T)
      (q : V ⟶ Z) (fV : V ⟶ Spec (CommRingCat.of K)), IsPullback q fV π y →
      (y (IsLocalRing.closedPoint K) ∈ U ↔ GeometricallyConnected fV) := by
    intro K _ V y q fV sq
    obtain ⟨φ, a, -, -, ha⟩ := exists_isPullback_fiberToSpecResidueField π sq
    change numGeometricConnectedComponents π _ = 1 ↔ _
    rw [← geometricallyConnected_iff_numGeometricConnectedComponents_eq_one]
    exact geometricallyConnected_iff_of_isPullback_specMap φ _ ha
  refine ⟨U, ⟨fun K _ y' Z' fst snd sq' => ?_⟩, key⟩
  have hpaste := sq'.paste_horiz (isPullback_morphismRestrict π U).flip
  have hgc := (key K Z' (y' ≫ U.ι) _ snd hpaste).mp (y' (IsLocalRing.closedPoint K)).2
  exact hgc.geometrically_connectedSpace (𝟙 _) (𝟙 Z') snd (IsPullback.of_horiz_isIso ⟨by simp⟩)

end AlgebraicGeometry

end
