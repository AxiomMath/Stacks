module

public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.EtaleGroupoidQuotientPieces
public import StacksFrontier.AlgebraicGeometry.Descent.GlueDataOverBase
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.InvariantModuliSpace
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.SeparatedDescent
public import StacksFrontier.AlgebraicGeometry.Size.Affine
public import StacksFrontier.AlgebraicGeometry.Size.FlatSurjective
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Gluing the invariant spectra of the invariant affine opens of an étale cartesian groupoid

Let `G'` be a groupoid scheme with finite locally free source and target, let `Q i` be invariant
affine opens of its object scheme `W`, and write `G'_i` for the restriction of `G'` to `Q i` and
`φ_i : Q i ⟶ N_i` for the invariant quotient map of `G'_i`. This file builds the gluing datum of
the `N_i`: the overlap `V_ij ⊆ N_i` is the image of `Q i ∩ Q j`, which is open with inverse image
exactly `Q i ∩ Q j` because `φ_i` is closed and its fibres are orbits (Stacks 03BL); the transition
morphisms are the factorizations of the quotient maps through the overlaps
(`AlgebraicGeometry.GroupoidScheme.existsUnique_quotientRestrict_comp`), and the cocycle condition
follows from the uniqueness of those factorizations.

## References

* [Stacks Project, Tag 0DUS](https://stacks.math.columbia.edu/tag/0DUS)
* [Stacks Project, Tag 01JA](https://stacks.math.columbia.edu/tag/01JA)
* [Stacks Project, Tag 03BL](https://stacks.math.columbia.edu/tag/03BL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids Stacks.Morphisms

universe u

namespace AlgebraicGeometry.GroupoidScheme

namespace InvariantCoverGlue

variable {S : Scheme.{u}} (G' : GroupoidScheme S)
  [IsFiniteLocallyFree G'.source.left] [IsFiniteLocallyFree G'.target.left]
  {I : Type u} (Q : I → G'.objects.left.Opens) (hQ : ∀ i, IsInvariantOpen G' (Q i))
  (hQa : ∀ i, IsAffineOpen (Q i))

/-- The restriction of `G'` to the `i`-th invariant open. -/
abbrev piece (i : I) : GroupoidScheme S := restrictInvariantOpen G' (Q i) (hQ i)

/-- The inclusion of the `i`-th invariant open into the object scheme. -/
abbrev pieceIncl (i : I) : (piece G' Q hQ i).objects.left ⟶ G'.objects.left :=
  (restrictInvariantOpenHom G' (Q i) (hQ i)).mapObjects.left

/-- The invariant spectrum `N_i` of the `i`-th piece. -/
abbrev pieceSpec (i : I) : Scheme.{u} := Spec (.of (invariantRing (piece G' Q hQ i)))

/-- The invariant quotient map `φ_i : Q i ⟶ N_i` of the `i`-th piece. -/
abbrev pieceQuot (i : I) : (piece G' Q hQ i).objects.left ⟶ pieceSpec G' Q hQ i :=
  objectsToInvariantSpectrum (piece G' Q hQ i)

include hQa in
omit [IsFiniteLocallyFree G'.source.left] [IsFiniteLocallyFree G'.target.left] in
/-- The object scheme of the `i`-th piece is affine. -/
theorem piece_isAffine_objects (i : I) : IsAffine (piece G' Q hQ i).objects.left := hQa i

omit [IsFiniteLocallyFree G'.target.left] in
/-- The source morphism of the `i`-th piece is finite locally free. -/
theorem piece_flf_source (i : I) : IsFiniteLocallyFree (piece G' Q hQ i).source.left :=
  isFiniteLocallyFree_of_isPullback (isPullback_restrictInvariantOpenHom_source G' (Q i) (hQ i))

omit [IsFiniteLocallyFree G'.source.left] in
/-- The target morphism of the `i`-th piece is finite locally free. -/
theorem piece_flf_target (i : I) : IsFiniteLocallyFree (piece G' Q hQ i).target.left :=
  isFiniteLocallyFree_of_isPullback (isPullback_restrictInvariantOpenHom_target G' (Q i) (hQ i))

include hQa in
omit [IsFiniteLocallyFree G'.target.left] in
/-- The arrow scheme of the `i`-th piece is affine. -/
theorem piece_isAffine_arrows (i : I) : IsAffine (piece G' Q hQ i).arrows.left := by
  have : IsAffine (piece G' Q hQ i).objects.left := hQa i
  have := piece_flf_source G' Q hQ i
  have : IsFinite (piece G' Q hQ i).source.left :=
    ((isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation _).1 inferInstance).1
  exact isAffine_of_isAffineHom (piece G' Q hQ i).source.left

/-- The object and arrow schemes of the `i`-th piece are affine, and its source and target are
finite locally free. -/
private theorem piece_instances (hQa : ∀ i, IsAffineOpen (Q i)) (i : I) :
    IsAffine (piece G' Q hQ i).objects.left ∧ IsAffine (piece G' Q hQ i).arrows.left ∧
      IsFiniteLocallyFree (piece G' Q hQ i).source.left ∧
      IsFiniteLocallyFree (piece G' Q hQ i).target.left :=
  ⟨piece_isAffine_objects G' Q hQ hQa i, piece_isAffine_arrows G' Q hQ hQa i,
    piece_flf_source G' Q hQ i, piece_flf_target G' Q hQ i⟩

/-- The points of `Q i` lying in `Q j`, as an open of `Q i`. -/
abbrev interOpen (i j : I) : (piece G' Q hQ i).objects.left.Opens := (pieceIncl G' Q hQ i) ⁻¹ᵁ Q j

omit [IsFiniteLocallyFree G'.source.left] [IsFiniteLocallyFree G'.target.left] in
/-- The arrow of `G'` underlying an arrow of the `i`-th piece has source the image of its
source. -/
theorem piece_source_apply (i : I) (r : (piece G' Q hQ i).arrows.left) :
    G'.source.left ((restrictInvariantOpenHom G' (Q i) (hQ i)).mapArrows.left r) =
      (pieceIncl G' Q hQ i) ((piece G' Q hQ i).source.left r) := by
  rw [← Scheme.Hom.comp_apply, (restrictInvariantOpenHom G' (Q i) (hQ i)).map_source_left,
    Scheme.Hom.comp_apply]

omit [IsFiniteLocallyFree G'.source.left] [IsFiniteLocallyFree G'.target.left] in
/-- The arrow of `G'` underlying an arrow of the `i`-th piece has target the image of its
target. -/
theorem piece_target_apply (i : I) (r : (piece G' Q hQ i).arrows.left) :
    G'.target.left ((restrictInvariantOpenHom G' (Q i) (hQ i)).mapArrows.left r) =
      (pieceIncl G' Q hQ i) ((piece G' Q hQ i).target.left r) := by
  rw [← Scheme.Hom.comp_apply, (restrictInvariantOpenHom G' (Q i) (hQ i)).map_target_left,
    Scheme.Hom.comp_apply]

include hQa in
/-- The image under `φ_i` of the complement of `Q i ∩ Q j` is closed. -/
theorem isClosed_image_compl (i j : I) :
    IsClosed (pieceQuot G' Q hQ i ''
      (interOpen G' Q hQ i j : Set (piece G' Q hQ i).objects.left)ᶜ) := by
  obtain ⟨_, _, _, _⟩ := piece_instances G' Q hQ hQa i
  have : UniversallyClosed (pieceQuot G' Q hQ i) :=
    universallyClosed_objectsToInvariantSpectrum (piece G' Q hQ i)
  exact (pieceQuot G' Q hQ i).isClosedMap _ (interOpen G' Q hQ i j).isOpen.isClosed_compl

/-- **The overlap `V_ij ⊆ N_i`**: the image of `Q i ∩ Q j`, which is open, being the complement of
the image of the complement. -/
def overlap (i j : I) : (pieceSpec G' Q hQ i).Opens :=
  ⟨(pieceQuot G' Q hQ i '' (interOpen G' Q hQ i j : Set (piece G' Q hQ i).objects.left)ᶜ)ᶜ,
    (isClosed_image_compl G' Q hQ hQa i j).isOpen_compl⟩

include hQa in
/-- **The inverse image of the overlap is `Q i ∩ Q j`.** A point of `Q i` mapping into the image
of the complement is related by an arrow to a point outside `Q j` (the fibres of `φ_i` are orbits,
Stacks 03BL), so it is itself outside `Q j` because `Q j` is invariant. -/
theorem mem_overlap_iff (i j : I) (x : (piece G' Q hQ i).objects.left) :
    pieceQuot G' Q hQ i x ∈ overlap G' Q hQ hQa i j ↔ x ∈ interOpen G' Q hQ i j := by
  obtain ⟨_, _, _, _⟩ := piece_instances G' Q hQ hQa i
  refine ⟨fun hx => not_not.mp fun hn => hx ⟨x, hn, rfl⟩, ?_⟩
  rintro hx ⟨y, hy, hyx⟩
  obtain ⟨r, hrt, hrs⟩ := (base_objectsToInvariantSpectrum_eq_iff (piece G' Q hQ i) y x).1 hyx
  apply hy
  show (pieceIncl G' Q hQ i) y ∈ Q j
  rw [← hrt, ← piece_target_apply]
  apply hQ j
  rwa [piece_source_apply, hrs]

include hQa in
/-- The inverse image of the overlap, as an open of `Q i`. -/
theorem quotientPreimage_overlap (i j : I) :
    quotientPreimage (piece G' Q hQ i) (overlap G' Q hQ hQa i j) = interOpen G' Q hQ i j :=
  TopologicalSpace.Opens.ext (Set.ext fun x => mem_overlap_iff G' Q hQ hQa i j x)

include hQa in
/-- The overlap `V_ii` is all of `N_i`. -/
theorem overlap_self (i : I) : overlap G' Q hQ hQa i i = ⊤ := by
  refine top_le_iff.mp fun m _ => ?_
  obtain ⟨_, _, _, _⟩ := piece_instances G' Q hQ hQa i
  obtain ⟨x, rfl⟩ := surjective_objectsToInvariantSpectrum (piece G' Q hQ i) m
  exact (mem_overlap_iff G' Q hQ hQa i i x).2 x.2

/-- The points of `W` over an open `X ⊆ V_ij` of `N_i` lie in the `j`-th invariant open. -/
private theorem range_preimage_subset_range_pieceIncl (hQa : ∀ i, IsAffineOpen (Q i)) (i j : I)
    (X : (pieceSpec G' Q hQ i).Opens) (hX : X ≤ overlap G' Q hQ hQa i j) :
    Set.range ((quotientPreimage (piece G' Q hQ i) X).ι ≫ pieceIncl G' Q hQ i) ⊆
      Set.range (pieceIncl G' Q hQ j) := by
  rintro _ ⟨p, rfl⟩
  have hp : (quotientPreimage (piece G' Q hQ i) X).ι p ∈ interOpen G' Q hQ i j := by
    rw [← quotientPreimage_overlap G' Q hQ hQa i j]
    exact Scheme.Hom.preimage_mono _ hX ((Scheme.Opens.range_ι _).le ⟨p, rfl⟩)
  exact (Scheme.Opens.range_ι (Q j)).ge hp

/-- The inverse image of the overlap `V_ij` in `Q i`, as an open of `Q i`. -/
abbrev overlapPreimage (i j : I) : (piece G' Q hQ i).objects.left.Opens :=
  quotientPreimage (piece G' Q hQ i) (overlap G' Q hQ hQa i j)

/-- The inverse image of `V_ij` in `Q i` lies in `Q j`. -/
theorem range_overlapPreimage_subset (i j : I) :
    Set.range ((overlapPreimage G' Q hQ hQa i j).ι ≫ pieceIncl G' Q hQ i) ⊆
      (Q j : Set G'.objects.left) := by
  rw [← Scheme.Opens.range_ι (Q j)]
  exact range_preimage_subset_range_pieceIncl G' Q hQ hQa i j _ le_rfl

/-- The inclusion of the inverse image of `V_ij` into `Q j`. -/
abbrev overlapIncl (i j : I) :
    (overlapPreimage G' Q hQ hQa i j).toScheme ⟶ (piece G' Q hQ j).objects.left :=
  IsOpenImmersion.lift (pieceIncl G' Q hQ j)
    ((overlapPreimage G' Q hQ hQa i j).ι ≫ pieceIncl G' Q hQ i)
    (by
      change _ ⊆ Set.range (Q j).ι
      rw [Scheme.Opens.range_ι]
      exact range_overlapPreimage_subset G' Q hQ hQa i j)

/-- The inclusion of the inverse image of `V_ij` into `Q j`, followed by the inclusion of `Q j`
into `W`, is the inclusion of the inverse image into `Q i` followed by that of `Q i`. -/
theorem overlapIncl_ι (i j : I) :
    overlapIncl G' Q hQ hQa i j ≫ (pieceIncl G' Q hQ j) =
      (overlapPreimage G' Q hQ hQa i j).ι ≫ (pieceIncl G' Q hQ i) :=
  IsOpenImmersion.lift_fac _ _ _

/-- The arrows of the `i`-th piece with source over `V_ij`, read as arrows of the `j`-th piece. -/
abbrev overlapArrowIncl (i j : I) :
    (quotientPreimageArrows (piece G' Q hQ i) (overlap G' Q hQ hQa i j)).toScheme ⟶
      (piece G' Q hQ j).arrows.left :=
  IsOpenImmersion.lift (restrictInvariantOpenHom G' (Q j) (hQ j)).mapArrows.left
    ((quotientPreimageArrows (piece G' Q hQ i) (overlap G' Q hQ hQa i j)).ι ≫
      (restrictInvariantOpenHom G' (Q i) (hQ i)).mapArrows.left) (by
    rintro _ ⟨r, rfl⟩
    refine ⟨⟨_, ?_⟩, rfl⟩
    have hr : (piece G' Q hQ i).source.left
        ((quotientPreimageArrows (piece G' Q hQ i) (overlap G' Q hQ hQa i j)).ι r) ∈
          overlapPreimage G' Q hQ hQa i j := r.2
    have hr2 : (piece G' Q hQ i).source.left
        ((quotientPreimageArrows (piece G' Q hQ i) (overlap G' Q hQ hQa i j)).ι r) ∈
          interOpen G' Q hQ i j := (quotientPreimage_overlap G' Q hQ hQa i j) ▸ hr
    exact (congrArg (· ∈ Q j) (piece_source_apply G' Q hQ i _)).mpr hr2)

/-- An arrow of the `i`-th piece with source over `V_ij` and its reading as an arrow of the
`j`-th piece have the same underlying arrow of `G'`. -/
theorem overlapArrowIncl_mapArrows (i j : I) :
    overlapArrowIncl G' Q hQ hQa i j ≫ (restrictInvariantOpenHom G' (Q j) (hQ j)).mapArrows.left =
      (quotientPreimageArrows (piece G' Q hQ i) (overlap G' Q hQ hQa i j)).ι ≫
        (restrictInvariantOpenHom G' (Q i) (hQ i)).mapArrows.left :=
  IsOpenImmersion.lift_fac _ _ _

/-- The target of an arrow of the `i`-th piece over `V_ij`, read in the `j`-th piece, is the
image in `Q j` of its target. -/
theorem overlapArrowIncl_target (i j : I) :
    overlapArrowIncl G' Q hQ hQa i j ≫ (piece G' Q hQ j).target.left =
      quotientPreimageTarget (piece G' Q hQ i) (overlap G' Q hQ hQa i j) ≫
        overlapIncl G' Q hQ hQa i j := by
  refine (cancel_mono (pieceIncl G' Q hQ j)).1 ?_
  have e1 : quotientPreimageTarget (piece G' Q hQ i) (overlap G' Q hQ hQa i j) ≫
      (overlapPreimage G' Q hQ hQa i j).ι =
        (quotientPreimageArrows (piece G' Q hQ i) (overlap G' Q hQ hQa i j)).ι ≫
          (piece G' Q hQ i).target.left := Scheme.Hom.resLE_comp_ι _ _
  simp only [Category.assoc, overlapIncl_ι, reassoc_of% e1,
    ← (restrictInvariantOpenHom G' (Q j) (hQ j)).map_target_left,
    ← (restrictInvariantOpenHom G' (Q i) (hQ i)).map_target_left,
    reassoc_of% overlapArrowIncl_mapArrows G' Q hQ hQa i j]

/-- The source of an arrow of the `i`-th piece over `V_ij`, read in the `j`-th piece, is the
image in `Q j` of its source. -/
theorem overlapArrowIncl_source (i j : I) :
    overlapArrowIncl G' Q hQ hQa i j ≫ (piece G' Q hQ j).source.left =
      quotientPreimageSource (piece G' Q hQ i) (overlap G' Q hQ hQa i j) ≫
        overlapIncl G' Q hQ hQa i j := by
  refine (cancel_mono (pieceIncl G' Q hQ j)).1 ?_
  have e1 : quotientPreimageSource (piece G' Q hQ i) (overlap G' Q hQ hQa i j) ≫
      (overlapPreimage G' Q hQ hQa i j).ι =
        (quotientPreimageArrows (piece G' Q hQ i) (overlap G' Q hQ hQa i j)).ι ≫
          (piece G' Q hQ i).source.left := Scheme.Hom.resLE_comp_ι _ _
  simp only [Category.assoc, overlapIncl_ι, reassoc_of% e1,
    ← (restrictInvariantOpenHom G' (Q j) (hQ j)).map_source_left,
    ← (restrictInvariantOpenHom G' (Q i) (hQ i)).map_source_left,
    reassoc_of% overlapArrowIncl_mapArrows G' Q hQ hQa i j]

/-- The quotient map of the `j`-th piece, restricted to the inverse image of `V_ij` in `Q i`, is
invariant for the `i`-th piece. -/
theorem overlapQuot_invariant (i j : I) :
    quotientPreimageTarget (piece G' Q hQ i) (overlap G' Q hQ hQa i j) ≫
        (overlapIncl G' Q hQ hQa i j ≫ pieceQuot G' Q hQ j) =
      quotientPreimageSource (piece G' Q hQ i) (overlap G' Q hQ hQa i j) ≫
        (overlapIncl G' Q hQ hQa i j ≫ pieceQuot G' Q hQ j) := by
  rw [← Category.assoc, ← overlapArrowIncl_target, Category.assoc,
    target_comp_objectsToInvariantSpectrum (piece G' Q hQ j), ← Category.assoc,
    overlapArrowIncl_source, Category.assoc]

/-- **The transition morphism `V_ij ⟶ N_j`**: the factorization through `V_ij` of the quotient
map of the `j`-th piece restricted to `Q i ∩ Q j`. -/
def transition (i j : I) : (overlap G' Q hQ hQa i j).toScheme ⟶ pieceSpec G' Q hQ j := by
  have := piece_isAffine_objects G' Q hQ hQa i
  have := piece_isAffine_arrows G' Q hQ hQa i
  have := piece_flf_source G' Q hQ i
  have := piece_flf_target G' Q hQ i
  exact (existsUnique_quotientRestrict_comp (piece G' Q hQ i) _
    (overlapQuot_invariant G' Q hQ hQa i j)).exists.choose

/-- The restricted quotient map onto `V_ij` followed by the transition `V_ij ⟶ N_j` is the
inclusion into `Q j` followed by the quotient map of the `j`-th piece. -/
theorem quotientRestrict_transition (i j : I) :
    quotientRestrict (piece G' Q hQ i) (overlap G' Q hQ hQa i j) ≫ transition G' Q hQ hQa i j =
      overlapIncl G' Q hQ hQa i j ≫ pieceQuot G' Q hQ j := by
  obtain ⟨_, _, _, _⟩ := piece_instances G' Q hQ hQa i
  exact (existsUnique_quotientRestrict_comp (piece G' Q hQ i) _
    (overlapQuot_invariant G' Q hQ hQa i j)).exists.choose_spec

include hQa in
/-- Two morphisms out of `V_ij` agreeing after the restricted quotient map agree. -/
theorem overlap_ext (i j : I) {T : Scheme.{u}} (h₁ h₂ : (overlap G' Q hQ hQa i j).toScheme ⟶ T)
    (h : quotientRestrict (piece G' Q hQ i) (overlap G' Q hQ hQa i j) ≫ h₁ =
      quotientRestrict (piece G' Q hQ i) (overlap G' Q hQ hQa i j) ≫ h₂) : h₁ = h₂ := by
  obtain ⟨_, _, _, _⟩ := piece_instances G' Q hQ hQa i
  exact quotientRestrict_ext (piece G' Q hQ i) h₁ h₂ h

/-- The transition morphism lands in `V_ji`. -/
theorem range_transition_subset (i j : I) :
    Set.range (transition G' Q hQ hQa i j) ⊆ (overlap G' Q hQ hQa j i : Set _) := by
  obtain ⟨_, _, _, _⟩ := piece_instances G' Q hQ hQa i
  rintro _ ⟨v, rfl⟩
  obtain ⟨p, rfl⟩ := quotientRestrict_surjective (piece G' Q hQ i) (overlap G' Q hQ hQa i j) v
  rw [← Scheme.Hom.comp_apply, quotientRestrict_transition, Scheme.Hom.comp_apply]
  refine (mem_overlap_iff G' Q hQ hQa j i _).2 ?_
  show (pieceIncl G' Q hQ j) (overlapIncl G' Q hQ hQa i j p) ∈ Q i
  rw [← Scheme.Hom.comp_apply, overlapIncl_ι, Scheme.Hom.comp_apply]
  exact (Scheme.Opens.range_ι (Q i)).le ⟨(overlapPreimage G' Q hQ hQa i j).ι p, rfl⟩

/-- **The transition isomorphism `t_ij : V_ij ⟶ V_ji`.** -/
def tmap (i j : I) : (overlap G' Q hQ hQa i j).toScheme ⟶ (overlap G' Q hQ hQa j i).toScheme :=
  IsOpenImmersion.lift (overlap G' Q hQ hQa j i).ι (transition G' Q hQ hQa i j)
    (by rw [Scheme.Opens.range_ι]; exact range_transition_subset G' Q hQ hQa i j)

/-- The transition `t_ij` followed by the inclusion of `V_ji` is the transition morphism
`V_ij ⟶ N_j`. -/
theorem tmap_ι (i j : I) :
    tmap G' Q hQ hQa i j ≫ (overlap G' Q hQ hQa j i).ι = transition G' Q hQ hQa i j :=
  IsOpenImmersion.lift_fac _ _ _

omit [IsFiniteLocallyFree G'.source.left] [IsFiniteLocallyFree G'.target.left] in
/-- The restricted quotient map, followed by the inclusion of the overlap, is the inclusion of
the inverse image followed by the quotient map. -/
theorem quotientRestrict_ι (i : I) (X : (pieceSpec G' Q hQ i).Opens) :
    quotientRestrict (piece G' Q hQ i) X ≫ X.ι =
      (quotientPreimage (piece G' Q hQ i) X).ι ≫ pieceQuot G' Q hQ i :=
  Scheme.Hom.resLE_comp_ι _ _

/-- **The point inclusion.** For opens `X ⊆ N_i` and `Y ⊆ N_j` such that every point of `W`
lying in the inverse image of `X` lies in that of `Y`, the inclusion of the inverse image of `X`
into the inverse image of `Y`. -/
def pointIncl (i j : I) (X : (pieceSpec G' Q hQ i).Opens) (Y : (pieceSpec G' Q hQ j).Opens)
    (h : Set.range ((quotientPreimage (piece G' Q hQ i) X).ι ≫ pieceIncl G' Q hQ i) ⊆
      Set.range ((quotientPreimage (piece G' Q hQ j) Y).ι ≫ pieceIncl G' Q hQ j)) :
    (quotientPreimage (piece G' Q hQ i) X).toScheme ⟶
      (quotientPreimage (piece G' Q hQ j) Y).toScheme :=
  IsOpenImmersion.lift ((quotientPreimage (piece G' Q hQ j) Y).ι ≫ pieceIncl G' Q hQ j)
    ((quotientPreimage (piece G' Q hQ i) X).ι ≫ pieceIncl G' Q hQ i) h

omit [IsFiniteLocallyFree G'.source.left] [IsFiniteLocallyFree G'.target.left] in
/-- The point inclusion commutes with the inclusions of the inverse images into `W`. -/
theorem pointIncl_fac (i j : I) (X : (pieceSpec G' Q hQ i).Opens)
    (Y : (pieceSpec G' Q hQ j).Opens) (h) :
    pointIncl G' Q hQ i j X Y h ≫ (quotientPreimage (piece G' Q hQ j) Y).ι ≫ pieceIncl G' Q hQ j =
      (quotientPreimage (piece G' Q hQ i) X).ι ≫ pieceIncl G' Q hQ i :=
  IsOpenImmersion.lift_fac _ _ _

include hQa in
/-- **The transition morphism on an open inside the overlap.** For `X ⊆ V_ij`, the restricted
quotient map of `X` followed by the transition is the inclusion into `Q j` followed by the
quotient map of the `j`-th piece. -/
theorem quotientRestrict_homOfLE_transition (i j : I) (X : (pieceSpec G' Q hQ i).Opens)
    (hX : X ≤ overlap G' Q hQ hQa i j) :
    quotientRestrict (piece G' Q hQ i) X ≫ (pieceSpec G' Q hQ i).homOfLE hX ≫
        transition G' Q hQ hQa i j =
      IsOpenImmersion.lift (pieceIncl G' Q hQ j)
          ((quotientPreimage (piece G' Q hQ i) X).ι ≫ pieceIncl G' Q hQ i) (by
            change _ ⊆ Set.range (Q j).ι
            rw [Scheme.Opens.range_ι]
            rintro _ ⟨p, rfl⟩
            have hp : (quotientPreimage (piece G' Q hQ i) X).ι p ∈ interOpen G' Q hQ i j := by
              rw [← quotientPreimage_overlap G' Q hQ hQa i j]
              exact Scheme.Hom.preimage_mono _ hX
                ((Scheme.Opens.range_ι _).le ⟨p, rfl⟩)
            exact hp) ≫
        pieceQuot G' Q hQ j := by
  let k : (quotientPreimage (piece G' Q hQ i) X).toScheme ⟶
      (overlapPreimage G' Q hQ hQa i j).toScheme :=
    (piece G' Q hQ i).objects.left.homOfLE (Scheme.Hom.preimage_mono _ hX)
  have hk : quotientRestrict (piece G' Q hQ i) X ≫ (pieceSpec G' Q hQ i).homOfLE hX =
      k ≫ quotientRestrict (piece G' Q hQ i) (overlap G' Q hQ hQa i j) := by
    refine (cancel_mono (overlap G' Q hQ hQa i j).ι).1 ?_
    rw [Category.assoc, Scheme.homOfLE_ι, quotientRestrict_ι, Category.assoc, quotientRestrict_ι,
      ← Category.assoc, Scheme.homOfLE_ι]
  rw [← Category.assoc, hk, Category.assoc, quotientRestrict_transition, ← Category.assoc]
  congr 1
  refine (cancel_mono (pieceIncl G' Q hQ j)).1 ?_
  rw [Category.assoc, overlapIncl_ι, ← Category.assoc, Scheme.homOfLE_ι, IsOpenImmersion.lift_fac]

include hQa in
/-- The transition `t_ii` is the identity of `V_ii`. -/
theorem tmap_self (i : I) : tmap G' Q hQ hQa i i = 𝟙 _ := by
  refine overlap_ext G' Q hQ hQa i i _ _ ((cancel_mono (overlap G' Q hQ hQa i i).ι).1 ?_)
  rw [Category.assoc, tmap_ι, quotientRestrict_transition, Category.comp_id, quotientRestrict_ι]
  congr 1
  refine (cancel_mono (pieceIncl G' Q hQ i)).1 ?_
  rw [overlapIncl_ι]

/-- The triple overlap `V_ij ∩ V_ik ⊆ N_i`. -/
abbrev tripleOverlap (i j k : I) : (pieceSpec G' Q hQ i).Opens :=
  overlap G' Q hQ hQa i j ⊓ overlap G' Q hQ hQa i k

include hQa in
/-- A point of `Q i` lies over the triple overlap exactly when it lies in `Q j` and in `Q k`. -/
theorem mem_quotientPreimage_tripleOverlap (i j k : I) (x : (piece G' Q hQ i).objects.left) :
    x ∈ quotientPreimage (piece G' Q hQ i) (tripleOverlap G' Q hQ hQa i j k) ↔
      pieceIncl G' Q hQ i x ∈ Q j ∧ pieceIncl G' Q hQ i x ∈ Q k :=
  Iff.and (mem_overlap_iff G' Q hQ hQa i j x) (mem_overlap_iff G' Q hQ hQa i k x)

include hQa in
/-- Every point of `W` over the triple overlap `V_ij ∩ V_ik` lies over `V_jk ∩ V_ji`. -/
theorem range_tripleOverlap_subset (i j k : I) :
    Set.range ((quotientPreimage (piece G' Q hQ i) (tripleOverlap G' Q hQ hQa i j k)).ι ≫
        pieceIncl G' Q hQ i) ⊆
      Set.range ((quotientPreimage (piece G' Q hQ j) (tripleOverlap G' Q hQ hQa j k i)).ι ≫
        pieceIncl G' Q hQ j) := by
  rintro _ ⟨p, rfl⟩
  have hp := (mem_quotientPreimage_tripleOverlap G' Q hQ hQa i j k _).1
    ((Scheme.Opens.range_ι _).le ⟨p, rfl⟩)
  set w := pieceIncl G' Q hQ i ((quotientPreimage (piece G' Q hQ i)
    (tripleOverlap G' Q hQ hQa i j k)).ι p)
  have hwi : w ∈ Q i := (Scheme.Opens.range_ι (Q i)).le ⟨_, rfl⟩
  let z : (piece G' Q hQ j).objects.left := ⟨w, hp.1⟩
  have hz : z ∈ quotientPreimage (piece G' Q hQ j) (tripleOverlap G' Q hQ hQa j k i) :=
    (mem_quotientPreimage_tripleOverlap G' Q hQ hQa j k i z).2 ⟨hp.2, hwi⟩
  exact ⟨⟨z, hz⟩, rfl⟩

include hQa in
/-- The transition morphism maps the triple overlap `V_ij ∩ V_ik` into `V_jk ∩ V_ji`. -/
theorem range_tprime_subset (i j k : I) :
    Set.range ((pieceSpec G' Q hQ i).homOfLE (inf_le_left : tripleOverlap G' Q hQ hQa i j k ≤ _) ≫
        transition G' Q hQ hQa i j) ⊆ (tripleOverlap G' Q hQ hQa j k i : Set _) := by
  obtain ⟨_, _, _, _⟩ := piece_instances G' Q hQ hQa i
  rintro _ ⟨v, rfl⟩
  obtain ⟨p, rfl⟩ := quotientRestrict_surjective (piece G' Q hQ i)
    (tripleOverlap G' Q hQ hQa i j k) v
  rw [← Scheme.Hom.comp_apply, quotientRestrict_homOfLE_transition G' Q hQ hQa i j
    (tripleOverlap G' Q hQ hQa i j k) inf_le_left]
  obtain ⟨⟨z, hz⟩, hzw⟩ := range_tripleOverlap_subset G' Q hQ hQa i j k ⟨p, rfl⟩
  have hzp : z = IsOpenImmersion.lift (pieceIncl G' Q hQ j)
      ((quotientPreimage (piece G' Q hQ i) (tripleOverlap G' Q hQ hQa i j k)).ι ≫
        pieceIncl G' Q hQ i) 
          (range_preimage_subset_range_pieceIncl G' Q hQ hQa i j _ inf_le_left) p := by
    apply (pieceIncl G' Q hQ j).isOpenEmbedding.injective
    rwa [← Scheme.Hom.comp_apply, IsOpenImmersion.lift_fac]
  rwa [Scheme.Hom.comp_apply, ← hzp]

/-- **The transition on triple overlaps** `t'_ijk : V_ij ∩ V_ik ⟶ V_jk ∩ V_ji`. -/
def tprime (i j k : I) : (tripleOverlap G' Q hQ hQa i j k).toScheme ⟶
    (tripleOverlap G' Q hQ hQa j k i).toScheme :=
  IsOpenImmersion.lift (tripleOverlap G' Q hQ hQa j k i).ι
    ((pieceSpec G' Q hQ i).homOfLE (inf_le_left : tripleOverlap G' Q hQ hQa i j k ≤ _) ≫
      transition G' Q hQ hQa i j)
    (by rw [Scheme.Opens.range_ι]; exact range_tprime_subset G' Q hQ hQa i j k)

/-- The triple transition `t'_ijk` followed by the inclusion of `V_jk ∩ V_ji` is the inclusion
into `V_ij` followed by the transition morphism `V_ij ⟶ N_j`. -/
theorem tprime_ι (i j k : I) :
    tprime G' Q hQ hQa i j k ≫ (tripleOverlap G' Q hQ hQa j k i).ι =
      (pieceSpec G' Q hQ i).homOfLE (inf_le_left : tripleOverlap G' Q hQ hQa i j k ≤ _) ≫
        transition G' Q hQ hQa i j :=
  IsOpenImmersion.lift_fac _ _ _

/-- The triple transition `t'_ijk` is the restriction of `t_ij` to the triple overlaps. -/
theorem tprime_fac (i j k : I) :
    tprime G' Q hQ hQa i j k ≫
        (pieceSpec G' Q hQ j).homOfLE (inf_le_right : tripleOverlap G' Q hQ hQa j k i ≤ _) =
      (pieceSpec G' Q hQ i).homOfLE (inf_le_left : tripleOverlap G' Q hQ hQa i j k ≤ _) ≫
        tmap G' Q hQ hQa i j := by
  refine (cancel_mono (overlap G' Q hQ hQa j i).ι).1 ?_
  rw [Category.assoc, Scheme.homOfLE_ι, tprime_ι, Category.assoc, tmap_ι]

include hQa in
/-- **The triple transition on points.** The restricted quotient map of the triple overlap,
followed by the triple transition, is the point inclusion followed by the restricted quotient map
of the next triple overlap. -/
theorem quotientRestrict_tprime (i j k : I) :
    quotientRestrict (piece G' Q hQ i) (tripleOverlap G' Q hQ hQa i j k) ≫
        tprime G' Q hQ hQa i j k =
      pointIncl G' Q hQ i j (tripleOverlap G' Q hQ hQa i j k) (tripleOverlap G' Q hQ hQa j k i)
          (range_tripleOverlap_subset G' Q hQ hQa i j k) ≫
        quotientRestrict (piece G' Q hQ j) (tripleOverlap G' Q hQ hQa j k i) := by
  refine (cancel_mono (tripleOverlap G' Q hQ hQa j k i).ι).1 ?_
  rw [Category.assoc, tprime_ι, quotientRestrict_homOfLE_transition G' Q hQ hQa i j _ inf_le_left,
    Category.assoc, quotientRestrict_ι, ← Category.assoc]
  congr 1
  refine (cancel_mono (pieceIncl G' Q hQ j)).1 ?_
  rw [IsOpenImmersion.lift_fac, Category.assoc, pointIncl_fac]

include hQa in
/-- **The cocycle condition.** -/
theorem tprime_cocycle (i j k : I) :
    tprime G' Q hQ hQa i j k ≫ tprime G' Q hQ hQa j k i ≫ tprime G' Q hQ hQa k i j = 𝟙 _ := by
  obtain ⟨_, _, _, _⟩ := piece_instances G' Q hQ hQa i
  refine quotientRestrict_ext (piece G' Q hQ i) _ _ ?_
  rw [← Category.assoc, quotientRestrict_tprime, Category.assoc, ← Category.assoc
    (quotientRestrict _ _), quotientRestrict_tprime, Category.assoc, quotientRestrict_tprime,
    Category.comp_id, ← Category.assoc, ← Category.assoc]
  conv_rhs => rw [← Category.id_comp (quotientRestrict (piece G' Q hQ i) _)]
  congr 1
  refine (cancel_mono ((quotientPreimage (piece G' Q hQ i)
    (tripleOverlap G' Q hQ hQa i j k)).ι ≫ pieceIncl G' Q hQ i)).1 ?_
  simp only [Category.assoc, pointIncl_fac, Category.id_comp]

section OverBase

variable {G : GroupoidScheme S} (F : GroupoidScheme.Hom G' G)
  [IsAffine G.objects.left] [IsAffine G.arrows.left]
  [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left]
  (hsource : IsPullback F.mapArrows.left G'.source.left G.source.left F.mapObjects.left)
  (htarget : IsPullback F.mapArrows.left G'.target.left G.target.left F.mapObjects.left)
  (hsrc : ∀ {T : Scheme.{u}} (r : T ⟶ G'.arrows.left),
    (r ≫ F.mapArrows.left) ≫ G.source.left = (r ≫ F.mapArrows.left) ≫ G.target.left →
      r ≫ G'.source.left = r ≫ G'.target.left)
  [Etale F.mapObjects.left]

/-- The structure morphism `N_i ⟶ M` of the `i`-th invariant spectrum. -/
abbrev pieceProj (i : I) : pieceSpec G' Q hQ i ⟶ Spec (.of (invariantRing G)) :=
  Spec.map (CommRingCat.ofHom (invariantRingMap (invariantOpenCompHom F (Q i) (hQ i))))

include hQa hsource htarget hsrc in
/-- **Stacks 0DT9 for the `i`-th piece:** `Q i = N_i ×_M U`. -/
theorem isPullback_piece (i : I) :
    IsPullback (pieceIncl G' Q hQ i ≫ F.mapObjects.left) (pieceQuot G' Q hQ i)
      (objectsToInvariantSpectrum G) (pieceProj G' Q hQ F i) := by
  obtain ⟨_, _, _, _⟩ := piece_instances G' Q hQ hQa i
  exact isPullback_restrictHom F hsource htarget hsrc (Q i) (hQ i)

include hQa hsource htarget hsrc in
/-- **Stacks 0DT9 for the `i`-th piece:** `N_i ⟶ M` is étale. -/
theorem etale_pieceProj (i : I) : Etale (pieceProj G' Q hQ F i) := by
  obtain ⟨_, _, _, _⟩ := piece_instances G' Q hQ hQa i
  exact etale_restrictHom_invariantSpectrum F hsource htarget hsrc (Q i) (hQ i)

include hQa hsource htarget hsrc in
/-- The transition `t_ij` commutes with the structure morphisms `N_i ⟶ M` and `N_j ⟶ M`. -/
theorem tmap_over (i j : I) :
    tmap G' Q hQ hQa i j ≫ (overlap G' Q hQ hQa j i).ι ≫ pieceProj G' Q hQ F j =
      (overlap G' Q hQ hQa i j).ι ≫ pieceProj G' Q hQ F i := by
  refine overlap_ext G' Q hQ hQa i j _ _ ?_
  have hj := (isPullback_piece G' Q hQ hQa F hsource htarget hsrc j).w
  have hi := (isPullback_piece G' Q hQ hQa F hsource htarget hsrc i).w
  calc quotientRestrict (piece G' Q hQ i) (overlap G' Q hQ hQa i j) ≫
        tmap G' Q hQ hQa i j ≫ (overlap G' Q hQ hQa j i).ι ≫ pieceProj G' Q hQ F j
      = (quotientRestrict (piece G' Q hQ i) (overlap G' Q hQ hQa i j) ≫
          transition G' Q hQ hQa i j) ≫ pieceProj G' Q hQ F j := by
        rw [← tmap_ι]; simp only [Category.assoc]
    _ = overlapIncl G' Q hQ hQa i j ≫ (pieceQuot G' Q hQ j ≫ pieceProj G' Q hQ F j) := by
        rw [quotientRestrict_transition, Category.assoc]
    _ = (overlapIncl G' Q hQ hQa i j ≫ pieceIncl G' Q hQ j) ≫ F.mapObjects.left ≫
          objectsToInvariantSpectrum G := by
        rw [← hj]; simp only [Category.assoc]
    _ = (overlapPreimage G' Q hQ hQa i j).ι ≫ (pieceIncl G' Q hQ i ≫ F.mapObjects.left) ≫
          objectsToInvariantSpectrum G := by
        rw [overlapIncl_ι]; simp only [Category.assoc]
    _ = (overlapPreimage G' Q hQ hQa i j).ι ≫ pieceQuot G' Q hQ i ≫ pieceProj G' Q hQ F i := by
        rw [hi]
    _ = _ := by rw [← Category.assoc, ← quotientRestrict_ι, Category.assoc]

/-- **The gluing datum** of the invariant spectra `N_i` over `M`. -/
def glueData : Scheme.GlueDataOverBase (Spec (.of (invariantRing G))) where
  J := I
  obj := pieceSpec G' Q hQ
  proj := pieceProj G' Q hQ F
  overlap := overlap G' Q hQ hQa
  overlap_self := overlap_self G' Q hQ hQa
  t := tmap G' Q hQ hQa
  t_over := tmap_over G' Q hQ hQa F hsource htarget hsrc
  t_self := tmap_self G' Q hQ hQa
  t' := tprime G' Q hQ hQa
  t'_fac := tprime_fac G' Q hQ hQa
  cocycle := tprime_cocycle G' Q hQ hQa

end OverBase

section Quotient

variable {G : GroupoidScheme S} (F : GroupoidScheme.Hom G' G)
  [IsAffine G.objects.left] [IsAffine G.arrows.left]
  [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left]
  (hsource : IsPullback F.mapArrows.left G'.source.left G.source.left F.mapObjects.left)
  (htarget : IsPullback F.mapArrows.left G'.target.left G.target.left F.mapObjects.left)
  (hsrc : ∀ {T : Scheme.{u}} (r : T ⟶ G'.arrows.left),
    (r ≫ F.mapArrows.left) ≫ G.source.left = (r ≫ F.mapArrows.left) ≫ G.target.left →
      r ≫ G'.source.left = r ≫ G'.target.left)
  [Etale F.mapObjects.left] (hcov : ∀ w, ∃ i, w ∈ Q i)

/-- The open cover of the object scheme of `G'` by the invariant opens `Q i`. -/
def pieceCover : G'.objects.left.OpenCover :=
  Scheme.Cover.mkOfCovers I (fun i => (piece G' Q hQ i).objects.left) (pieceIncl G' Q hQ)
    (fun w => (hcov w).imp fun _ hi => ⟨⟨w, hi⟩, rfl⟩)
    (fun _ => inferInstance)

/-- The glued scheme `Y`. -/
abbrev glued : Scheme.{u} :=
  (glueData G' Q hQ hQa F hsource htarget hsrc).glued

/-- The chart `N_i ⟶ Y`. -/
abbrev gluedι (i : I) : pieceSpec G' Q hQ i ⟶ glued G' Q hQ hQa F hsource htarget hsrc :=
  (glueData G' Q hQ hQa F hsource htarget hsrc).ι i

/-- The chart `N_i ⟶ Y` is an open immersion. -/
instance isOpenImmersion_gluedι (i : I) :
    IsOpenImmersion (gluedι G' Q hQ hQa F hsource htarget hsrc i) :=
  Scheme.GlueDataOverBase.isOpenImmersion_ι (glueData G' Q hQ hQa F hsource htarget hsrc) i

/-- The inverse image in `N_i` of the `j`-th chart of `Y` is the overlap `V_ij`. -/
theorem preimage_opensRange_gluedι_gluedι (i j : I) :
    gluedι G' Q hQ hQa F hsource htarget hsrc i ⁻¹ᵁ
        (gluedι G' Q hQ hQa F hsource htarget hsrc j).opensRange = overlap G' Q hQ hQa i j :=
  (glueData G' Q hQ hQa F hsource htarget hsrc).preimage_opensRange_ι i j

include hQa in
/-- The pullback of two of the invariant opens maps into the inverse image of the overlap. -/
theorem range_pullbackFst_subset (i j : I) :
    Set.range (pullback.fst (pieceIncl G' Q hQ i) (pieceIncl G' Q hQ j)) ⊆
      (overlapPreimage G' Q hQ hQa i j : Set _) := by
  rintro _ ⟨z, rfl⟩
  show _ ∈ quotientPreimage (piece G' Q hQ i) (overlap G' Q hQ hQa i j)
  rw [quotientPreimage_overlap G' Q hQ hQa i j]
  show (pieceIncl G' Q hQ i) (pullback.fst (pieceIncl G' Q hQ i) (pieceIncl G' Q hQ j) z) ∈ Q j
  rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
  exact (Scheme.Opens.range_ι (Q j)).le ⟨_, rfl⟩

include hQa in
/-- The maps `Q i ⟶ N_i ⟶ Y` and `Q j ⟶ N_j ⟶ Y` agree on `Q i ∩ Q j`. -/
theorem glue_condition (i j : I) :
    pullback.fst (pieceIncl G' Q hQ i) (pieceIncl G' Q hQ j) ≫ pieceQuot G' Q hQ i ≫
        gluedι G' Q hQ hQa F hsource htarget hsrc i =
      pullback.snd (pieceIncl G' Q hQ i) (pieceIncl G' Q hQ j) ≫ pieceQuot G' Q hQ j ≫
        gluedι G' Q hQ hQa F hsource htarget hsrc j := by
  let ℓ := IsOpenImmersion.lift (overlapPreimage G' Q hQ hQa i j).ι
    (pullback.fst (pieceIncl G' Q hQ i) (pieceIncl G' Q hQ j))
    (by rw [Scheme.Opens.range_ι]; exact range_pullbackFst_subset G' Q hQ hQa i j)
  have hℓ : ℓ ≫ (overlapPreimage G' Q hQ hQa i j).ι =
      pullback.fst (pieceIncl G' Q hQ i) (pieceIncl G' Q hQ j) := IsOpenImmersion.lift_fac _ _ _
  have hℓ' : ℓ ≫ overlapIncl G' Q hQ hQa i j =
      pullback.snd (pieceIncl G' Q hQ i) (pieceIncl G' Q hQ j) := by
    refine (cancel_mono (pieceIncl G' Q hQ j)).1 ?_
    rw [Category.assoc, overlapIncl_ι, ← Category.assoc, hℓ, pullback.condition]
  rw [← hℓ, ← hℓ', Category.assoc, Category.assoc, ← Category.assoc _ (pieceQuot G' Q hQ i),
    ← quotientRestrict_ι, ← Category.assoc (overlapIncl _ _ _ _ i j),
    ← quotientRestrict_transition, ← tmap_ι]
  simp only [Category.assoc]
  congr 2
  exact ((glueData G' Q hQ hQa F hsource htarget hsrc).t_ι i j).symm

/-- **The quotient map `q' : W ⟶ Y`**, glued from the `Q i ⟶ N_i ⟶ Y`. -/
def gluedQuot : G'.objects.left ⟶ glued G' Q hQ hQa F hsource htarget hsrc :=
  (pieceCover G' Q hQ hcov).glueMorphisms
    (fun i => pieceQuot G' Q hQ i ≫ gluedι G' Q hQ hQa F hsource htarget hsrc i)
    (glue_condition G' Q hQ hQa F hsource htarget hsrc)

/-- The quotient map `q' : W ⟶ Y` restricts on `Q i` to `Q i ⟶ N_i ⟶ Y`. -/
theorem pieceIncl_gluedQuot (i : I) :
    pieceIncl G' Q hQ i ≫ gluedQuot G' Q hQ hQa F hsource htarget hsrc hcov =
      pieceQuot G' Q hQ i ≫ gluedι G' Q hQ hQa F hsource htarget hsrc i :=
  Scheme.Cover.ι_glueMorphisms (pieceCover G' Q hQ hcov) _ _ i

/-- Pointwise form of `pieceIncl_gluedQuot`. -/
theorem gluedQuot_pieceIncl_apply (i : I) (w : (piece G' Q hQ i).objects.left) :
    gluedQuot G' Q hQ hQa F hsource htarget hsrc hcov (pieceIncl G' Q hQ i w) =
      gluedι G' Q hQ hQa F hsource htarget hsrc i (pieceQuot G' Q hQ i w) := by
  rw [← Scheme.Hom.comp_apply, pieceIncl_gluedQuot, Scheme.Hom.comp_apply]

include hQa in
/-- **The inverse image of the `i`-th chart of `Y` is `Q i`.** -/
theorem preimage_opensRange_gluedι (i : I) :
    gluedQuot G' Q hQ hQa F hsource htarget hsrc hcov ⁻¹ᵁ
        (gluedι G' Q hQ hQa F hsource htarget hsrc i).opensRange = Q i := by
  ext w
  refine ⟨fun hw => ?_, fun hw =>
    ⟨_, (gluedQuot_pieceIncl_apply G' Q hQ hQa F hsource htarget hsrc hcov i ⟨w, hw⟩).symm⟩⟩
  obtain ⟨j, hj⟩ := hcov w
  have hmem : pieceQuot G' Q hQ j ⟨w, hj⟩ ∈
      (gluedι G' Q hQ hQa F hsource htarget hsrc j) ⁻¹ᵁ
        (gluedι G' Q hQ hQa F hsource htarget hsrc i).opensRange := by
    show _ ∈ (gluedι G' Q hQ hQa F hsource htarget hsrc i).opensRange
    rwa [← gluedQuot_pieceIncl_apply G' Q hQ hQa F hsource htarget hsrc hcov j ⟨w, hj⟩]
  rw [preimage_opensRange_gluedι_gluedι] at hmem
  exact (mem_overlap_iff G' Q hQ hQa j i _).1 hmem

include hQa in
/-- **`Q i = W ×_Y N_i`.** -/
theorem isPullback_pieceIncl_gluedQuot (i : I) :
    IsPullback (pieceIncl G' Q hQ i) (pieceQuot G' Q hQ i)
      (gluedQuot G' Q hQ hQa F hsource htarget hsrc hcov)
      (gluedι G' Q hQ hQa F hsource htarget hsrc i) := by
  set ι := gluedι G' Q hQ hQa F hsource htarget hsrc i
  have e : pieceIncl G' Q hQ i = (Q i).ι := rfl
  let g : (Q i).toScheme ⟶ pieceSpec G' Q hQ i := pieceQuot G' Q hQ i
  have h := isPullback_opens_ι_of_eq_preimage (gluedQuot G' Q hQ hQa F hsource htarget hsrc hcov)
    ι.opensRange (Q i) (preimage_opensRange_gluedι G' Q hQ hQa F hsource htarget hsrc hcov i).symm
    (g ≫ ι.isoOpensRange.hom) (by
      rw [Category.assoc, Scheme.Hom.isoOpensRange_hom_ι, ← e]
      exact (pieceIncl_gluedQuot G' Q hQ hQa F hsource htarget hsrc hcov i).symm)
  rw [e]
  exact IsPullback.of_iso h (Iso.refl _) (Iso.refl _) ι.isoOpensRange.symm (Iso.refl _)
    (by simp) (by
      show (g ≫ ι.isoOpensRange.hom) ≫ ι.isoOpensRange.inv = 𝟙 _ ≫ g
      simp) (by simp) (by simp)

/-- The chart `N_i ⟶ Y` followed by the structure morphism `Y ⟶ M` is `N_i ⟶ M`. -/
@[reassoc (attr := simp)]
theorem gluedι_toBase (i : I) :
    gluedι G' Q hQ hQa F hsource htarget hsrc i ≫
        (glueData G' Q hQ hQa F hsource htarget hsrc).toBase = pieceProj G' Q hQ F i :=
  Scheme.GlueDataOverBase.ι_toBase (glueData G' Q hQ hQa F hsource htarget hsrc) i

include hQa in
omit [IsFiniteLocallyFree G'.source.left] [IsFiniteLocallyFree G'.target.left] in
/-- The invariant spectra are no larger than the object scheme: `N_i` is no larger than the affine
open `Q i`. -/
theorem size_pieceSpec_le (i : I) : (pieceSpec G' Q hQ i).size ≤ G'.objects.left.size := by
  have := piece_isAffine_objects G' Q hQ hQa i
  have : IsOpenImmersion (pieceIncl G' Q hQ i) := inferInstanceAs (IsOpenImmersion (Q i).ι)
  refine le_trans ?_ (Scheme.size_le_of_isOpenImmersion (pieceIncl G' Q hQ i))
  rw [Scheme.size_Spec, Scheme.size_of_isAffine (piece G' Q hQ i).objects.left]
  exact max_le_max le_rfl (Cardinal.mk_le_of_injective Subtype.val_injective)

include hQa in
/-- **The quotient map `q' : W ⟶ Y` is invariant**: it identifies the source and the target. -/
theorem source_comp_gluedQuot :
    G'.source.left ≫ gluedQuot G' Q hQ hQa F hsource htarget hsrc hcov =
      G'.target.left ≫ gluedQuot G' Q hQ hQa F hsource htarget hsrc hcov := by
  refine Scheme.Cover.hom_ext ((pieceCover G' Q hQ hcov).pullback₁ G'.source.left) _ _
    fun (i : I) => ?_
  obtain ⟨_, _, _, _⟩ := piece_instances G' Q hQ hQa i
  have hP := isPullback_restrictInvariantOpenHom_source G' (Q i) (hQ i)
  have hT := isPullback_restrictInvariantOpenHom_target G' (Q i) (hQ i)
  show pullback.fst G'.source.left (pieceIncl G' Q hQ i) ≫ _ =
    pullback.fst G'.source.left (pieceIncl G' Q hQ i) ≫ _
  rw [← hP.isoPullback_inv_fst, Category.assoc, Category.assoc]
  congr 1
  rw [← Category.assoc, hP.w, ← Category.assoc _ G'.target.left, hT.w, Category.assoc,
    Category.assoc, pieceIncl_gluedQuot, ← Category.assoc, ← Category.assoc]
  congr 1
  exact (target_comp_objectsToInvariantSpectrum (piece G' Q hQ i)).symm

include hQa in
/-- **`W = Y ×_M U`**: the object scheme of `G'` is the base change of the glued scheme `Y` along
the quotient map `U ⟶ M = Spec (invariantRing G)`. -/
theorem isPullback_gluedQuot :
    IsPullback (gluedQuot G' Q hQ hQa F hsource htarget hsrc hcov) F.mapObjects.left
      (glueData G' Q hQ hQa F hsource htarget hsrc).toBase (objectsToInvariantSpectrum G) := by
  refine Scheme.isPullback_of_openCover _ _ _ _
    (glueData G' Q hQ hQa F hsource htarget hsrc).toGlueData.openCover fun (i : I) => ?_
  have hp := isPullback_pieceIncl_gluedQuot G' Q hQ hQa F hsource htarget hsrc hcov i
  have hpiece := (isPullback_piece G' Q hQ hQa F hsource htarget hsrc i).flip
  show IsPullback
    (pullback.snd (gluedQuot G' Q hQ hQa F hsource htarget hsrc hcov)
      (gluedι G' Q hQ hQa F hsource htarget hsrc i))
    (pullback.fst (gluedQuot G' Q hQ hQa F hsource htarget hsrc hcov)
      (gluedι G' Q hQ hQa F hsource htarget hsrc i) ≫ F.mapObjects.left)
    (gluedι G' Q hQ hQa F hsource htarget hsrc i ≫
      (glueData G' Q hQ hQa F hsource htarget hsrc).toBase)
    (objectsToInvariantSpectrum G)
  refine IsPullback.of_iso hpiece hp.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ?_ ?_ ?_ ?_
  · rw [Iso.refl_hom, Category.comp_id]
    exact hp.isoPullback_hom_snd.symm
  · rw [Iso.refl_hom, Category.comp_id, ← Category.assoc, hp.isoPullback_hom_fst]
  · rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp, gluedι_toBase]
  · simp

include hQa in
/-- **The glued scheme is étale over `M`**: on each chart it is the étale `N_i ⟶ M`. -/
theorem etale_toBase : Etale (glueData G' Q hQ hQa F hsource htarget hsrc).toBase := by
  refine IsZariskiLocalAtSource.of_openCover
    (glueData G' Q hQ hQa F hsource htarget hsrc).toGlueData.openCover fun (i : I) => ?_
  show Etale (gluedι G' Q hQ hQa F hsource htarget hsrc i ≫
    (glueData G' Q hQ hQa F hsource htarget hsrc).toBase)
  rw [gluedι_toBase]
  exact etale_pieceProj G' Q hQ hQa F hsource htarget hsrc i

include hQa in
/-- The quotient map `q' : W ⟶ Y` is surjective and universally closed, being the base change of
the integral surjection `U ⟶ M` (**Stacks 03BJ**, **03BL**). -/
@[sga "1 V 1.1" "more general"]
theorem surjective_universallyClosed_gluedQuot :
    Surjective (gluedQuot G' Q hQ hQa F hsource htarget hsrc hcov) ∧
      UniversallyClosed (gluedQuot G' Q hQ hQa F hsource htarget hsrc hcov) := by
  have hpb := (isPullback_gluedQuot G' Q hQ hQa F hsource htarget hsrc hcov).flip
  have : IsIntegralHom (objectsToInvariantSpectrum G) := isIntegralHom_objectsToInvariantSpectrum G
  have : Surjective (objectsToInvariantSpectrum G) :=
    (surjective_iff _).2 (surjective_objectsToInvariantSpectrum G)
  exact ⟨MorphismProperty.of_isPullback (P := @Surjective) hpb inferInstance,
    MorphismProperty.of_isPullback (P := @UniversallyClosed) hpb inferInstance⟩

include hQa hcov in
/-- **The glued scheme is separated over `M`** as soon as `W ⟶ U` is (**Stacks 09MQ**): `W ⟶ M`
is separated and `W ⟶ Y` is a universally closed surjection over `M`. -/
theorem isSeparated_toBase [IsSeparated F.mapObjects.left] :
    IsSeparated (glueData G' Q hQ hQa F hsource htarget hsrc).toBase := by
  obtain ⟨h1, h2⟩ := surjective_universallyClosed_gluedQuot G' Q hQ hQa F hsource htarget hsrc hcov
  have hw := (isPullback_gluedQuot G' Q hQ hQa F hsource htarget hsrc hcov).w
  have : IsIntegralHom (objectsToInvariantSpectrum G) := isIntegralHom_objectsToInvariantSpectrum G
  have : IsSeparated (gluedQuot G' Q hQ hQa F hsource htarget hsrc hcov ≫
      (glueData G' Q hQ hQa F hsource htarget hsrc).toBase) := by
    rw [hw]; infer_instance
  exact @isSeparated_of_surjective_universallyClosed _
    (Over.mk (gluedQuot G' Q hQ hQa F hsource htarget hsrc hcov ≫
      (glueData G' Q hQ hQa F hsource htarget hsrc).toBase))
    (Over.mk (glueData G' Q hQ hQa F hsource htarget hsrc).toBase)
    (Over.homMk (gluedQuot G' Q hQ hQa F hsource htarget hsrc hcov) rfl) h1 h2 this

end Quotient

end InvariantCoverGlue

end AlgebraicGeometry.GroupoidScheme

end
