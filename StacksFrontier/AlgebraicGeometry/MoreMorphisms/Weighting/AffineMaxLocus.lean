module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ImmersionCover
public import StacksFrontier.AlgebraicGeometry.FiniteFactorization.Basic
public import StacksFrontier.AlgebraicGeometry.Limits.AffineFromFiniteSurjective
public import StacksFrontier.AlgebraicGeometry.Limits.Descending.DescentSituation
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.FibreSumLevelSetConstructible
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.LimitDescent
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.MaximalLocus
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.UniversallyOpen
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Approximation
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.FiniteCover
public import StacksFrontier.AlgebraicGeometry.Morphisms.Misc.FiniteCoproduct
public import StacksFrontier.AlgebraicGeometry.TopDegreeFiniteType.Basic
public import StacksFrontier.Topology.Spectral.BijectionHomeomorph
public import StacksFrontier.Topology.Spectral.LimitConstructible
public import StacksCore.Tactic.StacksAttribute

/-!
# Affineness of the maximum locus of a weighted fibre sum

Let `f : X ⟶ Y` be a quasi-finite morphism of finite presentation between affine schemes and let
`w` be an everywhere positive weighting of `f`.  If the weighted fibre sum of `w` attains a
greatest value `d`, then the locus in `Y` where that value is attained is an *affine* open
subscheme of `Y`.

## Main results

* `AlgebraicGeometry.exists_isAffineOpen_separableDegreeWeightedFiberSum_eq_max`: the
  maximum-value locus of the weighted fibre sum is an affine open subscheme of the target.

## Implementation notes

The proof runs in four stages, each reducing to the next.

Over an *irreducible* affine base covered by finitely many closed subschemes of the source that
are open over the base, the maximum locus `U` is squeezed between the intersection `W` of the
finitely many affine opens `Im(Z i → Y)` and itself: `U ≤ W` because the restriction of each
piece over `U` is a finite open immersion into an irreducible nonempty space, hence surjective;
and `W ≤ U` because the restriction of the morphism over `W` is finite, so its weighted fibre
sum is locally constant there, and `W` is irreducible.  Hence `U = W` is a finite intersection
of affine opens of an affine scheme.  This replaces the explicit computation of the weight sum at
the generic point in the Stacks text by local constancy of the fibre sum over the connected `W`.

Over an *integral* affine base the finitely many closed pieces come from a factorization
`X ⟶ T ⟶ Y` of the morphism through an immersion followed by finitely many sections of `T ⟶ Y`:
pulling the sections back along the immersion gives closed subschemes of `X`, those whose image
contains the generic point are open over `Y` (an immersion with dense image into a reduced scheme
is an open immersion), and they already cover the generic fibre, hence all of `X`.  Such a
factorization exists after a finite surjective base change, by Zariski's main theorem
([Stacks, Tag 05K0]) followed by the finite locally free cover of [Stacks, Tag 03HW].

Over a *Noetherian* affine base one passes to the finitely many integral components, and then
descends affineness along the finite surjective base change by [Stacks, Tag 01ZT].

In general one writes the base as the limit of the spectra of the finitely generated subalgebras
of its ring of sections over the Noetherian base of an affine finite-type model of the morphism
([Stacks, Tag 05FL], [Stacks, Tag 05FJ]).  The weighting descends to a finite stage by
[Stacks, Tag 0F3P]; at a later stage the "bad" locus — where some weight is non-positive, or
where the fibre sum exceeds the maximum — becomes empty, because it is closed for the
constructible topology and has empty preimage in the limit ([Stacks, Tag 0A2X], applied through
the descent situation of [Stacks, Tag 09RD]).  The Noetherian case then applies at that stage and
the resulting affine open is pulled back.

[Stacks, Tag 0F3H] — local constructibility of the level sets of a weighted fibre sum — is not
yet available in this library, so it enters as an explicit hypothesis of the main theorem rather
than as an import.

## References

* [Stacks Project, Tag 0F3R](https://stacks.math.columbia.edu/tag/0F3R)
* [Stacks Project, Tag 0F3L](https://stacks.math.columbia.edu/tag/0F3L)
* [Stacks Project, Tag 0F3P](https://stacks.math.columbia.edu/tag/0F3P)
* [Stacks Project, Tag 05K0](https://stacks.math.columbia.edu/tag/05K0)
* [Stacks Project, Tag 03HW](https://stacks.math.columbia.edu/tag/03HW)
* [Stacks Project, Tag 01ZT](https://stacks.math.columbia.edu/tag/01ZT)
* [Stacks Project, Tag 0A2X](https://stacks.math.columbia.edu/tag/0A2X)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Topology

universe u

namespace AlgebraicGeometry

/-! ### Open immersions from immersions with dense image -/

private lemma isOpenImmersion_of_isImmersion_of_denseRange
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsImmersion f] [QuasiCompact f]
    [IsReduced Y] (hf : DenseRange f) : IsOpenImmersion f := by
  have : IsDominant f := ⟨hf⟩
  have : IsSchemeTheoreticallyDominant f := .of_isDominant f
  have : IsIso f.imageι := by
    change IsIso f.ker.subschemeι
    rw [f.ker_eq_bot]
    infer_instance
  rw [← f.toImage_imageι]
  infer_instance

private lemma isLocallyConstant_weightedFiberSum_of_isFinite
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] (w : X → ℤ)
    (hw : IsWeighting f w) :
    IsLocallyConstant (separableDegreeWeightedFiberSum f w) := by
  have : IsIso (pullback.lift (𝟙 X) f (by simp) : X ⟶ pullback f (𝟙 Y)) := by
    have heq : pullback.lift (𝟙 X) f (by simp) = inv (pullback.fst f (𝟙 Y)) := by
      apply (cancel_mono (pullback.fst f (𝟙 Y))).mp
      rw [pullback.lift_fst, IsIso.inv_hom_id]
    rw [heq]
    infer_instance
  simpa using hw.isLocallyConstant (𝟙 X) f (𝟙 Y) (by simp)
    inferInstance inferInstance inferInstance

/-! ### Finiteness from a finite closed cover of the source -/

private lemma universallyClosed_of_finite_closed_cover
    {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Type*} [Finite ι]
    (Z : ι → Scheme.{u}) (j : ∀ index, Z index ⟶ X)
    (hfinite : ∀ index, IsFinite (j index ≫ f))
    (hcover : ∀ x : X, ∃ index, ∃ z : Z index, j index z = x) :
    UniversallyClosed f := by
  rw [universallyClosed_eq]
  intro X' Y' source target baseChange square
  let Z' (index : ι) := pullback (j index) source
  let j' (index : ι) : Z' index ⟶ X' := pullback.snd (j index) source
  have hfinite' (index : ι) : IsFinite (j' index ≫ baseChange) := by
    have smaller := IsPullback.of_hasPullback (j index) source
    have composed := smaller.paste_vert square.flip
    exact MorphismProperty.of_isPullback composed (hfinite index)
  have hcover' : ∀ x : X', ∃ index, ∃ z : Z' index, j' index z = x := by
    intro x
    obtain ⟨index, z, hz⟩ := hcover (source x)
    obtain ⟨lifted, _, hlifted⟩ := Scheme.Pullback.exists_preimage_pullback z x hz
    exact ⟨index, lifted, hlifted⟩
  intro closedSet hclosedSet
  have heq : baseChange '' closedSet =
      ⋃ index, (j' index ≫ baseChange) '' ((j' index) ⁻¹' closedSet) := by
    ext point
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨index, z, rfl⟩ := hcover' x
      exact Set.mem_iUnion.mpr ⟨index, z, hx, rfl⟩
    · intro hpoint
      obtain ⟨index, z, hz, rfl⟩ := Set.mem_iUnion.mp hpoint
      exact ⟨j' index z, hz, rfl⟩
  rw [heq]
  apply isClosed_iUnion_of_finite
  intro index
  have := hfinite' index
  exact (j' index ≫ baseChange).isClosedMap _
    (hclosedSet.preimage (j' index).continuous)

private lemma isFinite_of_finite_cover
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] [LocallyOfFiniteType f]
    {ι : Type*} [Finite ι] (Z : ι → Scheme.{u}) (j : ∀ index, Z index ⟶ X)
    (hfinite : ∀ index, IsFinite (j index ≫ f))
    (hcover : ∀ x : X, ∃ index, ∃ z : Z index, j index z = x) : IsFinite f := by
  have : UniversallyClosed f := universallyClosed_of_finite_closed_cover f Z j hfinite hcover
  have : IsIntegralHom f :=
    IsIntegralHom.iff_universallyClosed_and_isAffineHom.mpr ⟨inferInstance, inferInstance⟩
  exact (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType f).mpr
    ⟨inferInstance, inferInstance⟩

/-! ### Covers detected on the generic fibre -/

private theorem denseRange_of_genericPoint_mem_range
    {X Y : Scheme.{u}} [IrreducibleSpace Y] (f : X ⟶ Y)
    (hf : genericPoint Y ∈ Set.range f) : DenseRange f := by
  rw [denseRange_iff_closure_range]
  apply Set.eq_univ_of_univ_subset
  rw [← genericPoint_closure Y]
  exact closure_mono (Set.singleton_subset_iff.mpr hf)

private theorem covers_of_generic_fiber_cover
    {X Y : Scheme.{u}} [IrreducibleSpace Y] (f : X ⟶ Y)
    (hopen : IsOpenMap f) {ι : Type*} [Finite ι]
    (Z : ι → Scheme.{u}) (j : ∀ index, Z index ⟶ X)
    (hclosed : ∀ index, IsClosed (Set.range (j index)))
    (hcover : ∀ x : X, f x = genericPoint Y →
      ∃ index, ∃ z : Z index, j index z = x) :
    ∀ x : X, ∃ index, ∃ z : Z index, j index z = x := by
  have hdense : closure (f ⁻¹' {genericPoint Y}) = Set.univ := by
    apply Set.eq_univ_of_univ_subset
    have hdensity := hopen.preimage_closure_subset_closure_preimage
      (s := {genericPoint Y})
    simpa only [genericPoint_closure, Set.preimage_univ] using hdensity
  have hsubset : f ⁻¹' {genericPoint Y} ⊆ ⋃ index, Set.range (j index) := by
    intro x hx
    obtain ⟨index, z, hz⟩ := hcover x hx
    exact Set.mem_iUnion.mpr ⟨index, z, hz⟩
  have hclosure := closure_minimal hsubset (isClosed_iUnion_of_finite hclosed)
  rw [hdense] at hclosure
  intro x
  obtain ⟨index, z, hz⟩ := Set.mem_iUnion.mp (hclosure (Set.mem_univ x))
  exact ⟨index, z, hz⟩

/-! ### Restricting a base change over the preimage of an open -/

private theorem isFinite_pullback_restrict
    {X Y B : Scheme.{u}} (f : X ⟶ Y) (g : B ⟶ Y) (U : Y.Opens)
    (hfinite : IsFinite (f ∣_ U)) :
    IsFinite (pullback.snd f g ∣_ (g ⁻¹ᵁ U)) := by
  have := hfinite
  have hUY : (pullback.snd f g ⁻¹ᵁ g ⁻¹ᵁ U) =
      pullback.fst f g ⁻¹ᵁ (f ⁻¹ᵁ U) ⊓ pullback.snd f g ⁻¹ᵁ (g ⁻¹ᵁ U) := by
    have h : pullback.fst f g ⁻¹ᵁ (f ⁻¹ᵁ U) = pullback.snd f g ⁻¹ᵁ (g ⁻¹ᵁ U) := by
      rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, pullback.condition]
    rw [h, inf_idem]
  have h := Scheme.Hom.isPullback_resLE (IsPullback.of_hasPullback f g)
    (US := U) (UT := g ⁻¹ᵁ U) (UX := f ⁻¹ᵁ U)
    (UY := pullback.snd f g ⁻¹ᵁ g ⁻¹ᵁ U) le_rfl le_rfl hUY
  rw [Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.resLE_eq_morphismRestrict,
    Scheme.Hom.resLE_eq_morphismRestrict] at h
  exact MorphismProperty.of_isPullback h hfinite

/-! ### Affineness from a finite surjective base change and from a finite closed cover -/

private theorem isAffineOpen_of_finite_surjective_preimage
    {Y B : Scheme.{u}} (g : B ⟶ Y) [IsFinite g] [Surjective g]
    (U : Y.Opens) (hU : IsAffineOpen (g ⁻¹ᵁ U)) : IsAffineOpen U := by
  have : IsAffine (g ⁻¹ᵁ U).toScheme := hU
  have : Surjective (g ∣_ U) := MorphismProperty.of_isPullback
    (isPullback_morphismRestrict g U).flip (inferInstance : Surjective g)
  exact Stacks.AffineFromFiniteSurjective.isAffine_of_finite_surjective (g ∣_ U)

/-- A point of `X` over a point of `U` gives a point of the restriction over `U`. -/
private lemma exists_morphismRestrict_apply_eq {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    {y : Y} (hy : y ∈ U) {x : X} (hx : f x = y) : ∃ x' : f ⁻¹ᵁ U, (f ∣_ U) x' = ⟨y, hy⟩ :=
  ⟨⟨x, show f x ∈ U from hx ▸ hy⟩, Subtype.ext ((morphismRestrict_base_coe _ _ _).trans hx)⟩

private theorem isAffineOpen_of_finite_closed_cover
    {Y : Scheme.{u}} [IsAffine Y] (U : Y.Opens) {ι : Type u} [Finite ι]
    (Z : ι → Scheme.{u}) (j : ∀ index, Z index ⟶ Y)
    (hj : ∀ index, IsFinite (j index))
    (hcover : ∀ y : Y, ∃ index, ∃ z : Z index, j index z = y)
    (hU : ∀ index, IsAffineOpen (j index ⁻¹ᵁ U)) : IsAffineOpen U := by
  let Z' (index : ι) := (j index ⁻¹ᵁ U).toScheme
  let j' (index : ι) : Z' index ⟶ U.toScheme := j index ∣_ U
  have hZ' (index : ι) : IsAffine (Z' index) := hU index
  have hj' (index : ι) : IsFinite (j' index) := by
    have := hj index
    exact inferInstance
  have : IsFinite (Sigma.desc j') := isFinite_sigmaDesc
  have : Surjective (Sigma.desc j') := by
    constructor
    intro y
    obtain ⟨index, z, hz⟩ := hcover y.1
    obtain ⟨z', hz'⟩ := exists_morphismRestrict_apply_eq (j index) U y.2 hz
    refine ⟨Sigma.ι Z' index z', ?_⟩
    change (Sigma.ι Z' index ≫ Sigma.desc j') _ = y
    rw [Sigma.ι_comp_desc]
    exact hz'
  exact Stacks.AffineFromFiniteSurjective.isAffine_of_finite_surjective (Sigma.desc j')

/-! ### The maximum locus over an irreducible base covered by sections -/

private lemma isAffineOpen_maxLocus_of_finite_closed_cover
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] [IrreducibleSpace Y]
    (f : X ⟶ Y) [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    (w : X → ℤ) (hw : IsWeighting f w)
    (U : Y.Opens) (hfinite : IsFinite (f ∣_ U))
    (d : ℤ) (hU : (U : Set Y) = {y | separableDegreeWeightedFiberSum f w y = d})
    (hnonempty : (U : Set Y).Nonempty)
    {ι : Type*} [Finite ι] [Nonempty ι]
    (Z : ι → Scheme.{u}) (j : ∀ index, Z index ⟶ X)
    (hj : ∀ index, IsClosedImmersion (j index))
    (hopen : ∀ index, IsOpenImmersion (j index ≫ f))
    (hdominant : ∀ index, (Set.range (j index ≫ f)).Nonempty)
    (hcover : ∀ x : X, ∃ index, ∃ z : Z index, j index z = x) :
    IsAffineOpen U := by
  classical
  let instClosed : ∀ index, IsClosedImmersion (j index) := hj
  let instOpen : ∀ index, IsOpenImmersion (j index ≫ f) := hopen
  have : Nonempty U.toScheme := hnonempty.to_subtype
  have : IrreducibleSpace U.toScheme := U.ι.isOpenEmbedding.irreducibleSpace
  have hpiece (index : ι) : IsFinite ((j index ≫ f) ∣_ U) := by
    have hfin : IsFinite ((j index ∣_ (f ⁻¹ᵁ U)) ≫ (f ∣_ U)) := by
      have := hfinite
      infer_instance
    rw [morphismRestrict_comp]
    exact hfin
  let V (index : ι) : Y.Opens := (j index ≫ f).opensRange
  have hUle (index : ι) : U ≤ V index := by
    have := hpiece index
    have hclopen : IsClopen (Set.range ((j index ≫ f) ∣_ U)) :=
      ⟨((j index ≫ f) ∣_ U).isClosedMap.isClosed_range,
        ((j index ≫ f) ∣_ U).isOpenEmbedding.isOpen_range⟩
    have hnonempty' : (Set.range ((j index ≫ f) ∣_ U)).Nonempty := by
      obtain ⟨point, hpointU, hpointRange⟩ :=
        nonempty_preirreducible_inter U.isOpen
          (j index ≫ f).isOpenEmbedding.isOpen_range
          hnonempty (hdominant index)
      obtain ⟨z, hz⟩ := hpointRange
      exact ⟨_, exists_morphismRestrict_apply_eq _ U hpointU hz⟩
    have hrange := hclopen.eq_univ hnonempty'
    intro point hpoint
    have hmem : (⟨point, hpoint⟩ : U.toScheme) ∈ Set.range ((j index ≫ f) ∣_ U) := by
      rw [hrange]; trivial
    obtain ⟨z, hz⟩ := hmem
    exact ⟨z.1, (morphismRestrict_base_coe _ _ z).symm.trans (congrArg Subtype.val hz)⟩
  let W : Y.Opens := ⨅ index, V index
  have hW : IsAffineOpen W := by
    apply IsAffineOpen.iInf
    intro index
    have : IsAffine (Z index) := isAffine_of_isAffineHom (j index)
    exact isAffineOpen_opensRange (j index ≫ f)
  have hUW : U ≤ W := le_iInf hUle
  have hWfinite : IsFinite (f ∣_ W) := by
    have : IsAffine W.toScheme := hW
    have : IsAffineHom (f ∣_ W) := MorphismProperty.of_isPullback
      (isPullback_morphismRestrict f W).flip (inferInstance : IsAffineHom f)
    refine isFinite_of_finite_cover (f ∣_ W)
      (fun index ↦ (j index ⁻¹ᵁ f ⁻¹ᵁ W).toScheme)
      (fun index ↦ j index ∣_ (f ⁻¹ᵁ W)) ?_ ?_
    · intro index
      have hsurj : Surjective ((j index ≫ f) ∣_ W) := by
        constructor
        intro point
        obtain ⟨z, hz⟩ := (iInf_le V index : W ≤ V index) point.property
        exact exists_morphismRestrict_apply_eq _ W point.property hz
      have : IsIso ((j index ≫ f) ∣_ W) :=
        (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, hsurj⟩
      have hfin : IsFinite ((j index ≫ f) ∣_ W) := inferInstance
      rw [show (j index ∣_ (f ⁻¹ᵁ W)) ≫ (f ∣_ W) = ((j index ≫ f) ∣_ W) from
        (morphismRestrict_comp (j index) f W).symm]
      exact hfin
    · intro point
      obtain ⟨index, z, hz⟩ := hcover point.1
      exact ⟨index, exists_morphismRestrict_apply_eq _ _ point.property hz⟩
  have hwW : IsWeighting (f ∣_ W) (w ∘ (f ⁻¹ᵁ W).ι) :=
    IsWeighting.comp_of_isPullback hw (isPullback_morphismRestrict f W).flip
  have hsum := separableDegreeWeightedFiberSum_comp_of_isPullback f
    (f ⁻¹ᵁ W).ι (f ∣_ W) W.ι (isPullback_morphismRestrict f W).flip
    f.finite_preimage_singleton w
  have := hWfinite
  have hconstant := isLocallyConstant_weightedFiberSum_of_isFinite (f ∣_ W) _ hwW
  obtain ⟨point, hpoint⟩ := hnonempty
  have hpointd : separableDegreeWeightedFiberSum f w point = d := by
    rw [hU] at hpoint; exact hpoint
  have : Nonempty W.toScheme := ⟨⟨point, hUW hpoint⟩⟩
  have : IrreducibleSpace W.toScheme := W.ι.isOpenEmbedding.irreducibleSpace
  have hWU : W ≤ U := by
    intro other hother
    change other ∈ (U : Set Y)
    rw [hU]
    change separableDegreeWeightedFiberSum f w other = d
    have heq := hconstant.apply_eq_of_preconnectedSpace
      ⟨other, hother⟩ ⟨point, hUW hpoint⟩
    rw [← hsum] at heq
    exact heq.trans hpointd
  rw [le_antisymm hUW hWU]
  exact hW

/-! ### The maximum locus over an integral base covered by sections -/

private theorem isAffineOpen_maxLocus_of_section_envelope
    {X Y T : Scheme.{u}} [IsAffine X] [IsAffine Y] [IsIntegral Y]
    (f : X ⟶ Y) [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    (w : X → ℤ) (hw : IsWeighting f w)
    (hfopen : IsOpenMap f)
    (U : Y.Opens) (hfinite : IsFinite (f ∣_ U))
    (d : ℤ) (hU : (U : Set Y) = {y | separableDegreeWeightedFiberSum f w y = d})
    (e : X ⟶ T) [IsImmersion e] (p : T ⟶ Y) (hep : e ≫ p = f)
    {ι : Type*} [Finite ι] (sections : ι → (Y ⟶ T))
    (hsections : ∀ index, IsClosedImmersion (sections index) ∧
      sections index ≫ p = 𝟙 Y)
    (hcover : ∀ point : T, ∃ index, ∃ y : Y, sections index y = point) :
    IsAffineOpen U := by
  classical
  let instSections : ∀ index, IsClosedImmersion (sections index) :=
    fun index ↦ (hsections index).1
  by_cases hnonempty : (U : Set Y).Nonempty
  · let Z (index : ι) := pullback e (sections index)
    let j (index : ι) : Z index ⟶ X := pullback.fst e (sections index)
    let q (index : ι) : Z index ⟶ Y := pullback.snd e (sections index)
    have hj (index : ι) : IsClosedImmersion (j index) :=
      inferInstanceAs (IsClosedImmersion (pullback.fst e (sections index)))
    have hq (index : ι) : IsImmersion (q index) :=
      inferInstanceAs (IsImmersion (pullback.snd e (sections index)))
    have hqeq (index : ι) : j index ≫ f = q index := by
      change pullback.fst e (sections index) ≫ f = pullback.snd e (sections index)
      rw [← hep, pullback.condition_assoc, (hsections index).2, Category.comp_id]
    let selected := {index : ι // genericPoint Y ∈ Set.range (q index)}
    have hopen (index : selected) : IsOpenImmersion (j index.1 ≫ f) := by
      rw [hqeq]
      have := hq index.1
      have : IsAffine (Z index.1) := isAffine_of_isAffineHom (j index.1)
      exact isOpenImmersion_of_isImmersion_of_denseRange _
        (denseRange_of_genericPoint_mem_range _ index.2)
    have hselectedCover : ∀ x : X, ∃ index : selected,
        ∃ z : Z index.1, j index.1 z = x := by
      apply covers_of_generic_fiber_cover f hfopen
        (fun index : selected ↦ Z index.1) (fun index ↦ j index.1)
      · intro index
        have := hj index.1
        exact (j index.1).isClosedMap.isClosed_range
      · intro x hx
        obtain ⟨index, y, hy⟩ := hcover (e x)
        obtain ⟨z, hzx, _⟩ := Scheme.Pullback.exists_preimage_pullback x y hy.symm
        have hqz : q index z = genericPoint Y := by
          rw [← hqeq, Scheme.Hom.comp_apply, hzx, hx]
        exact ⟨⟨index, z, hqz⟩, z, hzx⟩
    by_cases hX : Nonempty X
    · have : Nonempty selected := by
        obtain ⟨x⟩ := hX
        obtain ⟨index, _, _⟩ := hselectedCover x
        exact ⟨index⟩
      exact isAffineOpen_maxLocus_of_finite_closed_cover f w hw U hfinite d hU hnonempty
        (fun index : selected ↦ Z index.1) (fun index ↦ j index.1)
        (fun index ↦ hj index.1) hopen
        (fun index ↦ ⟨genericPoint Y, by simpa only [hqeq] using index.2⟩)
        hselectedCover
    · have : IsEmpty X := not_nonempty_iff.mp hX
      have hzero : ∀ y : Y, separableDegreeWeightedFiberSum f w y = 0 := fun y ↦
        separableDegreeWeightedFiberSum_eq_zero_of_fiber_eq_empty f w y
          (Set.eq_empty_of_isEmpty _)
      obtain ⟨point, hpoint⟩ := hnonempty
      have hd : d = 0 := by
        rw [hU] at hpoint
        exact (hzero point).symm.trans hpoint |>.symm
      have htop : U = ⊤ := by
        apply SetLike.coe_injective
        rw [hU]
        ext y
        simp [hzero y, hd]
      rw [htop]
      exact isAffineOpen_top Y
  · have hbot : U = ⊥ := by
      apply SetLike.coe_injective
      exact Set.not_nonempty_iff_eq_empty.mp hnonempty
    rw [hbot]
    exact isAffineOpen_bot Y

/-! ### Zariski's main theorem plus the finite locally free cover of Tag 03HW -/

/-- Base change along `g` of a factorization `f = e ≫ p` is a pullback square over `e`. -/
private lemma isPullback_fst_pullback_map {X Y B T : Scheme.{u}} (f : X ⟶ Y) (g : B ⟶ Y)
    (e : X ⟶ T) (p : T ⟶ Y) (hep : e ≫ p = f) :
    IsPullback (pullback.fst f g)
      (pullback.map f g p g e (𝟙 B) (𝟙 Y) (by simpa using hep.symm) (by simp)) e
      (pullback.fst p g) := by
  apply IsPullback.flip
  apply IsPullback.of_right
    (h₁₁ := pullback.map f g p g e (𝟙 B) (𝟙 Y) (by simpa using hep.symm) (by simp))
    (h₁₂ := pullback.snd p g) (h₂₁ := e) (h₂₂ := p)
    (v₁₁ := pullback.fst f g) (v₁₂ := pullback.fst p g) (v₁₃ := g)
  · simpa only [pullback.map, pullback.lift_snd, Category.comp_id, hep]
      using (IsPullback.of_hasPullback f g).flip
  · simp only [pullback.map, pullback.lift_fst]
  · exact (IsPullback.of_hasPullback p g).flip

private theorem exists_finite_surjective_section_envelope
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) [LocallyOfFiniteType f] [LocallyQuasiFinite f] :
    ∃ (B T : Scheme.{u}) (g : B ⟶ Y)
      (e : pullback f g ⟶ T) (p : T ⟶ B),
      IsFinite g ∧ Surjective g ∧ IsImmersion e ∧ e ≫ p = pullback.snd f g ∧
        ∃ (count : ℕ) (sections : Fin count → (B ⟶ T)),
          (∀ index, IsClosedImmersion (sections index) ∧ sections index ≫ p = 𝟙 B) ∧
          (∀ point : T, ∃ index, ∃ b : B, sections index b = point) := by
  obtain ⟨A, inclusion, projection, hopen, hcompact, hfinite, hfactor⟩ :=
    Stacks.FiniteFactorization.exists_isOpenImmersion_isFinite_factorization f
  have := hopen
  have := hcompact
  have := hfinite
  obtain ⟨B, g, hsurjective, hfree, _, _, T, p, embedding,
    hembedding, hembedding_comp, _, count, sections, hsections, hcover⟩ :=
    Stacks.Morphisms.exists_finiteLocallyFree_cover_closedImmersion projection
  have hgfinite : IsFinite g :=
    ((Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
      g).mp hfree).1
  have := hembedding
  let toModel : pullback f g ⟶ pullback projection g :=
    pullback.map f g projection g inclusion (𝟙 B) (𝟙 Y)
      (by simpa using hfactor) (by simp)
  have htoModel : IsOpenImmersion toModel := by
    exact MorphismProperty.of_isPullback
      (isPullback_fst_pullback_map f g inclusion projection hfactor.symm) hopen
  have := htoModel
  refine ⟨B, T, g, toModel ≫ embedding, p, hgfinite, hsurjective,
    inferInstance, ?_, count, sections, hsections, hcover⟩
  rw [Category.assoc, hembedding_comp]
  simp only [toModel, pullback.map, pullback.lift_snd, Category.comp_id]

/-! ### Finiteness over the maximum locus -/

private theorem exists_finite_maximumLocus
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
    [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    (w : X → ℤ) (hw : IsWeighting f w)
    (hpositive : ∀ x, 0 < w x) (d : ℤ)
    (hd : IsGreatest (Set.range (separableDegreeWeightedFiberSum f w)) d) :
    ∃ U : Y.Opens,
      (U : Set Y) = {y | separableDegreeWeightedFiberSum f w y = d} ∧
        IsFinite (f ∣_ U) :=
  exists_isFinite_restrict_separableDegreeWeightedFiberSum_maxLocus f
    (fun y ↦ f.finite_preimage_singleton y) w hw hpositive d hd

/-! ### The integral components of a Noetherian affine scheme -/

private theorem exists_integral_closed_cover
    {Y : Scheme.{u}} [IsAffine Y] [IsNoetherian Y] :
    ∃ (ι : Type u) (_ : Finite ι) (Z : ι → Scheme.{u})
      (j : ∀ index, Z index ⟶ Y),
      (∀ index, IsAffine (Z index) ∧ IsIntegral (Z index) ∧ IsClosedImmersion (j index)) ∧
      (∀ y : Y, ∃ index, ∃ z : Z index, j index z = y) := by
  classical
  let ι := {C : Set Y // C ∈ irreducibleComponents Y}
  have : Finite ι := NoetherianSpace.finite_irreducibleComponents.to_subtype
  let I (index : ι) : Y.IdealSheafData :=
    Scheme.IdealSheafData.vanishingIdeal
      ⟨index.1, isClosed_of_mem_irreducibleComponents _ index.2⟩
  let Z (index : ι) := (I index).subscheme
  let j (index : ι) : Z index ⟶ Y := (I index).subschemeι
  have hrange (index : ι) : Set.range (j index) = index.1 :=
    Scheme.IdealSheafData.range_subschemeι_vanishingIdeal _
  refine ⟨ι, inferInstance, Z, j, ?_, ?_⟩
  · intro index
    have : IsReduced (Z index) :=
      Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
    have : IrreducibleSpace (Z index) :=
      Scheme.IdealSheafData.irreducibleSpace_subscheme Y (I index)
        ((hrange index).symm ▸ index.2.1)
    exact ⟨isAffine_of_isAffineHom (j index),
      isIntegral_of_irreducibleSpace_of_isReduced _, inferInstance⟩
  · intro y
    let index : ι :=
      ⟨irreducibleComponent y, irreducibleComponent_mem_irreducibleComponents y⟩
    obtain ⟨z, hz⟩ : y ∈ Set.range (j index) := (hrange index).symm ▸ mem_irreducibleComponent
    exact ⟨index, z, hz⟩

/-! ### The maximum locus over a Noetherian base -/

/-- The preimage of a level set of `F` under `g` is the level set of `F ∘ g`. -/
private lemma preimage_eq_levelSet_of_comp {Y Y' : Scheme.{u}} (g : Y' ⟶ Y) (U : Y.Opens)
    (F : Y → ℤ) (F' : Y' → ℤ) (d : ℤ) (hsum : F ∘ g = F')
    (hU : (U : Set Y) = {y | F y = d}) : ((g ⁻¹ᵁ U : Y'.Opens) : Set Y') = {y | F' y = d} := by
  subst hsum
  ext z
  change g z ∈ (U : Set Y) ↔ _
  rw [hU]
  rfl

private theorem isAffineOpen_maxLocus_of_noetherian_section_envelope
    {X Y T : Scheme.{u}} [IsAffine X] [IsAffine Y] [IsNoetherian Y]
    (f : X ⟶ Y) [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    (w : X → ℤ) (hw : IsWeighting f w) [UniversallyOpen f]
    (U : Y.Opens) (hfinite : IsFinite (f ∣_ U))
    (d : ℤ) (hU : (U : Set Y) = {y | separableDegreeWeightedFiberSum f w y = d})
    (e : X ⟶ T) [IsImmersion e] (p : T ⟶ Y) (hep : e ≫ p = f)
    {ι : Type*} [Finite ι] (sections : ι → (Y ⟶ T))
    (hsections : ∀ index, IsClosedImmersion (sections index) ∧
      sections index ≫ p = 𝟙 Y)
    (hcover : ∀ point : T, ∃ index, ∃ y : Y, sections index y = point) :
    IsAffineOpen U := by
  obtain ⟨components, hcomponents, Z, j, hj, hcoverZ⟩ := exists_integral_closed_cover (Y := Y)
  have := hcomponents
  refine isAffineOpen_of_finite_closed_cover U Z j (fun index ↦ ?_) hcoverZ ?_
  · have := (hj index).2.2
    infer_instance
  intro index
  have := (hj index).1
  have := (hj index).2.1
  have := (hj index).2.2
  let f' : (pullback f (j index) : Scheme.{u}) ⟶ Z index := pullback.snd f (j index)
  let e' : (pullback f (j index) : Scheme.{u}) ⟶ (pullback p (j index) : Scheme.{u}) :=
    pullback.map f (j index) p (j index) e (𝟙 _) (𝟙 _)
      (by simpa using hep.symm) (by simp)
  let sections' (sectionIndex : ι) : Z index ⟶ (pullback p (j index) : Scheme.{u}) :=
    pullback.lift (j index ≫ sections sectionIndex) (𝟙 _)
      (by rw [Category.assoc, (hsections sectionIndex).2, Category.comp_id, Category.id_comp])
  have he' : IsImmersion e' :=
    MorphismProperty.of_isPullback (isPullback_fst_pullback_map f (j index) e p hep)
      inferInstance
  have := he'
  have hsections' (sectionIndex : ι) : IsClosedImmersion (sections' sectionIndex) ∧
      sections' sectionIndex ≫ pullback.snd p (j index) = 𝟙 _ := by
    refine ⟨?_, by simp only [sections', pullback.lift_snd]⟩
    have hcomp : IsClosedImmersion (sections' sectionIndex ≫ pullback.fst p (j index)) := by
      simp only [sections', pullback.lift_fst]
      have := (hsections sectionIndex).1
      infer_instance
    exact IsClosedImmersion.of_comp (sections' sectionIndex) (pullback.fst p (j index))
  have hcover' : ∀ point : (pullback p (j index) : Scheme.{u}),
      ∃ sectionIndex, ∃ z : Z index, sections' sectionIndex z = point := by
    intro point
    obtain ⟨sectionIndex, y, hy⟩ := hcover (pullback.fst p (j index) point)
    have hy' : j index (pullback.snd p (j index) point) = y := by
      have h := congrArg (fun morphism : (pullback p (j index) : Scheme.{u}) ⟶ Y ↦ morphism point)
        (pullback.condition (f := p) (g := j index))
      have hs := congrArg (fun morphism ↦ morphism y) (hsections sectionIndex).2
      simp only [Scheme.Hom.comp_apply] at h hs
      exact h.symm.trans (hy.symm ▸ hs)
    refine ⟨sectionIndex, pullback.snd p (j index) point, ?_⟩
    apply (pullback.fst p (j index)).injective
    change (sections' sectionIndex ≫ pullback.fst p (j index)) _ = _
    rw [pullback.lift_fst]
    change sections sectionIndex (j index (pullback.snd p (j index) point)) = _
    rw [hy', hy]
  have hw' : IsWeighting f' (w ∘ pullback.fst f (j index)) :=
    IsWeighting.comp_of_isPullback hw (IsPullback.of_hasPullback f (j index))
  have hsum := separableDegreeWeightedFiberSum_comp_of_isPullback
    f (pullback.fst f (j index)) f' (j index) (IsPullback.of_hasPullback f (j index))
    f.finite_preimage_singleton w
  refine isAffineOpen_maxLocus_of_section_envelope f' _ hw' f'.isOpenMap
    (j index ⁻¹ᵁ U) (isFinite_pullback_restrict f (j index) U hfinite) d
    (preimage_eq_levelSet_of_comp _ U _ _ d hsum hU)
    e' (pullback.snd p (j index))
    (by simp only [e', pullback.map, pullback.lift_snd, Category.comp_id, f'])
    sections' hsections' hcover'

private theorem isAffineOpen_maxLocus_of_isNoetherian
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] [IsNoetherian Y]
    (f : X ⟶ Y) [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    (w : X → ℤ) (hw : IsWeighting f w) [UniversallyOpen f]
    (U : Y.Opens) (hfinite : IsFinite (f ∣_ U))
    (d : ℤ) (hU : (U : Set Y) = {y | separableDegreeWeightedFiberSum f w y = d}) :
    IsAffineOpen U := by
  obtain ⟨B, T, g, e, p, hg, hsurj, he, hep, count, sections, hs, hcover⟩ :=
    exists_finite_surjective_section_envelope f
  have := hg
  have := hsurj
  have := he
  have : IsAffine B := isAffine_of_isAffineHom g
  have : IsLocallyNoetherian B := LocallyOfFiniteType.isLocallyNoetherian g
  have : IsNoetherian B := (isNoetherian_iff B).mpr ⟨inferInstance, inferInstance⟩
  have hw' : IsWeighting (pullback.snd f g) (w ∘ pullback.fst f g) :=
    IsWeighting.comp_of_isPullback hw (IsPullback.of_hasPullback f g)
  have hsum := separableDegreeWeightedFiberSum_comp_of_isPullback
    f (pullback.fst f g) (pullback.snd f g) g (IsPullback.of_hasPullback f g)
    f.finite_preimage_singleton w
  refine isAffineOpen_of_finite_surjective_preimage g U
    (isAffineOpen_maxLocus_of_noetherian_section_envelope (pullback.snd f g)
      (w ∘ pullback.fst f g) hw' (g ⁻¹ᵁ U)
      (isFinite_pullback_restrict f g U hfinite) d
        (preimage_eq_levelSet_of_comp _ U _ _ d hsum hU) e p hep sections hs hcover)

/-! ### Descending an empty bad locus to a finite stage -/

private theorem isClosed_constructible_preimage_of_levelSets
    {Y : Scheme.{u}} [IsAffine Y] (weight : Y → ℤ)
    (hweight : ∀ value, Topology.IsLocallyConstructible {y | weight y = value})
    (values : Set ℤ) :
    @IsClosed Y (constructibleTopology Y) (weight ⁻¹' values) := by
  have : SpectralSpace Y := Scheme.spectralSpace_of_compactSpace_quasiSeparatedSpace Y
  have hconstant : @IsLocallyConstant Y ℤ (constructibleTopology Y) weight := by
    refine (@IsLocallyConstant.iff_isOpen_fiber Y ℤ (constructibleTopology Y) weight).mpr ?_
    intro value
    exact (hweight value).isConstructible.isOpen_constructibleTopology
  exact @IsClosed.mk Y (constructibleTopology Y) (weight ⁻¹' values) (hconstant valuesᶜ)

private theorem exists_empty_preimage_of_isClosed_constructible
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ index : I, IsAffine (D.obj (.op index))]
    (index : I) (bad : Set (D.obj (.op index)))
    (hbad : @IsClosed _ (constructibleTopology (D.obj (.op index))) bad)
    (hempty : (c.π.app (.op index)) ⁻¹' bad = ∅) :
    ∃ later : I, ∃ transition : index ≤ later,
      D.map (homOfLE transition).op ⁻¹' bad = ∅ := by
  have : Nonempty I := ⟨index⟩
  have hAffine : ∀ i : Iᵒᵖ, IsAffine (D.obj i) := fun i ↦
    ‹∀ index : I, IsAffine (D.obj (.op index))› i.unop
  let situation : DescentSituation I :=
    { system := D
      transition_affine := fun {_ _} _ ↦ inferInstance
      quasiCompact := fun _ ↦ inferInstance
      quasiSeparated := fun _ ↦ inferInstance
      limitCone := c
      isLimit := hc
      base := index }
  obtain ⟨htop⟩ := nonempty_isLimit_forgetToTop_mapCone situation
  let F := D ⋙ Scheme.forgetToTop
  have hspectral : ∀ object : Iᵒᵖ, SpectralSpace (F.obj object) := fun object ↦
    Scheme.spectralSpace_of_compactSpace_quasiSeparatedSpace (D.obj object)
  have hlimit : (limit.π F (.op index)) ⁻¹' bad = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr ?_
    intro point hbadpoint
    have hcomp := htop.conePointUniqueUpToIso_inv_comp (limit.isLimit F) (.op index)
    have hcomp' := congrArg (fun morphism ↦ morphism point) hcomp
    have hmem : (htop.conePointUniqueUpToIso (limit.isLimit F)).inv point ∈
        (c.π.app (.op index)) ⁻¹' bad := by
      change (Scheme.forgetToTop.mapCone c).π.app (.op index)
        ((htop.conePointUniqueUpToIso (limit.isLimit F)).inv point) ∈ bad
      rw [show (Scheme.forgetToTop.mapCone c).π.app (.op index)
        ((htop.conePointUniqueUpToIso (limit.isLimit F)).inv point) =
          limit.π F (.op index) point from hcomp']
      exact hbadpoint
    rw [hempty] at hmem
    exact hmem
  have hsubset : (limit.π F (.op index)) ⁻¹' bad ⊆
      (limit.π F (.op index)) ⁻¹' (∅ : Set (F.obj (.op index))) := by
    rw [hlimit]
    exact Set.empty_subset _
  obtain ⟨later, transition, htransition⟩ :=
    (SpectralLimits.preimage_limit_π_subset_iff_exists_map_preimage_subset F hspectral
      (fun {_ _} morphism ↦ (D.map morphism).isSpectralMap)
      (.op index) bad ∅ hbad (@isOpen_empty _ (constructibleTopology _))).mp hsubset
  refine ⟨later.unop, leOfHom transition.unop, ?_⟩
  refine Set.eq_empty_iff_forall_notMem.mpr ?_
  intro point hpoint
  exact htransition hpoint

/-- Tag 0F3H, the local constructibility of the level sets of a weighted fibre sum, in the
form in which the descent argument uses it.  It is not yet available in this library and is
therefore carried as a hypothesis. -/
private abbrev LevelSetsLocallyConstructible : Prop :=
  ∀ {X' Y' : Scheme.{u}} (g : X' ⟶ Y'), LocallyQuasiFinite g →
    FinitePresentation g → ∀ (v : X' → ℤ), IsWeighting g v → ∀ m : ℤ,
      Topology.IsLocallyConstructible
        {y : Y' | separableDegreeWeightedFiberSum g v y = m}

private theorem exists_empty_bad_weighting_stage
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ index : I, IsAffine (D.obj (.op index))]
    {X X₀ : Scheme.{u}} [IsAffine X] [IsAffine X₀]
    (index : I) (f : X ⟶ c.pt) (f₀ : X₀ ⟶ D.obj (.op index))
    [LocallyOfFinitePresentation f₀] [LocallyQuasiFinite f₀]
    (source : X ⟶ X₀) (square : IsPullback source f f₀ (c.π.app (.op index)))
    (w₀ : X₀ → ℤ) (hw₀ : IsWeighting f₀ w₀)
    (hpositive : ∀ x, 0 < w₀ (source x)) (d : ℤ)
    (hbound : ∀ y, separableDegreeWeightedFiberSum f (w₀ ∘ source) y ≤ d)
    (h0F3H : LevelSetsLocallyConstructible.{u}) :
    ∃ later : I, ∃ transition : index ≤ later,
      ∀ y : D.obj (.op later),
        (∀ x₀ : X₀, f₀ x₀ = D.map (homOfLE transition).op y → 0 < w₀ x₀) ∧
        separableDegreeWeightedFiberSum f₀ w₀
          (D.map (homOfLE transition).op y) ≤ d := by
  have : SpectralSpace X₀ := Scheme.spectralSpace_of_compactSpace_quasiSeparatedSpace X₀
  have : SpectralSpace (D.obj (.op index)) :=
    Scheme.spectralSpace_of_compactSpace_quasiSeparatedSpace _
  have himage : IsClosed[constructibleTopology (D.obj (.op index))]
      (f₀ '' {x₀ | w₀ x₀ ≤ 0}) :=
    f₀.isSpectralMap.isClosedMap_constructibleTopology _
      (isClosed_constructible_preimage_of_levelSets w₀
        (isLocallyConstructible_weighting_levelSet hw₀) {value | value ≤ 0})
  have hlevel : IsClosed[constructibleTopology (D.obj (.op index))]
      {y₀ | d < separableDegreeWeightedFiberSum f₀ w₀ y₀} := by
    have hfp₀ : FinitePresentation f₀ := ⟨inferInstance, inferInstance, inferInstance⟩
    exact isClosed_constructible_preimage_of_levelSets
      (separableDegreeWeightedFiberSum f₀ w₀)
      (h0F3H f₀ inferInstance hfp₀ w₀ hw₀) {value | d < value}
  have hempty : c.π.app (.op index) ⁻¹' (f₀ '' {x₀ | w₀ x₀ ≤ 0} ∪
      {y₀ | d < separableDegreeWeightedFiberSum f₀ w₀ y₀}) = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr ?_
    intro y hy
    rcases hy with ⟨x₀, hx₀, hequal⟩ | hy
    · obtain ⟨x, hx, _⟩ := Scheme.exists_preimage_of_isPullback square x₀ y hequal
      exact (not_le_of_gt (hpositive x)) (hx ▸ hx₀)
    · have hsum := separableDegreeWeightedFiberSum_comp_of_isPullback
        f₀ source f (c.π.app (.op index)) square f₀.finite_preimage_singleton w₀
      exact (not_lt_of_ge (hbound y)) (congrFun hsum y ▸ hy)
  obtain ⟨later, transition, hlater⟩ :=
    exists_empty_preimage_of_isClosed_constructible D c hc index _
      (@IsClosed.union _ _ _ (constructibleTopology (D.obj (.op index))) himage hlevel) hempty
  refine ⟨later, transition, fun y ↦ ⟨?_, ?_⟩⟩
  · intro x₀ hequal
    by_contra hpos
    have hmem : y ∈ D.map (homOfLE transition).op ⁻¹' (f₀ '' {x₀ | w₀ x₀ ≤ 0} ∪
        {y₀ | d < separableDegreeWeightedFiberSum f₀ w₀ y₀}) :=
      Or.inl ⟨x₀, le_of_not_gt hpos, hequal⟩
    rw [hlater] at hmem
    exact hmem
  · by_contra hle
    have hmem : y ∈ D.map (homOfLE transition).op ⁻¹' (f₀ '' {x₀ | w₀ x₀ ≤ 0} ∪
        {y₀ | d < separableDegreeWeightedFiberSum f₀ w₀ y₀}) := Or.inr (lt_of_not_ge hle)
    rw [hlater] at hmem
    exact hmem

/-! ### Descending the weighting itself to a finite stage -/

/-- Factoring the base change of `f₀` along `a ≫ b` through the base change along `b`. -/
private lemma isPullback_lift_pullback_snd {X X₀ S S' C : Scheme.{u}} {f₀ : X₀ ⟶ S} (b : S' ⟶ S)
    {a : C ⟶ S'} {source : X ⟶ X₀} {f : X ⟶ C} (h : IsPullback source f f₀ (a ≫ b)) :
    IsPullback (pullback.lift source (f ≫ a) (by rw [Category.assoc]; exact h.w)) f
      (pullback.snd f₀ b) a := by
  apply IsPullback.of_right (h₁₂ := pullback.fst f₀ b) (h₂₂ := b)
  · simpa only [pullback.lift_fst] using h
  · simp only [pullback.lift_snd]
  · exact IsPullback.of_hasPullback f₀ b

private theorem exists_weighting_stage
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ index : I, IsAffine (D.obj (.op index))]
    {X X₀ : Scheme.{u}} [IsAffine X₀]
    (index : I) (f : X ⟶ c.pt) (f₀ : X₀ ⟶ D.obj (.op index))
    [LocallyOfFinitePresentation f₀] [LocallyQuasiFinite f₀]
    (source : X ⟶ X₀) (square : IsPullback source f f₀ (c.π.app (.op index)))
    (w : X → ℤ) (hw : IsWeighting f w) :
    ∃ later : I, ∃ transition : index ≤ later,
      ∃ wᵢ : (pullback f₀ (D.map (homOfLE transition).op) : Scheme.{u}) → ℤ,
        IsWeighting (pullback.snd f₀ (D.map (homOfLE transition).op)) wᵢ ∧
        ∃ sourceᵢ : X ⟶ pullback f₀ (D.map (homOfLE transition).op),
          IsPullback sourceᵢ f (pullback.snd f₀ (D.map (homOfLE transition).op))
            (c.π.app (.op later)) ∧ w = wᵢ ∘ sourceᵢ := by
  have : Nonempty I := ⟨index⟩
  have : LocallyOfFiniteType f := MorphismProperty.of_isPullback square inferInstance
  have : LocallyQuasiFinite f := MorphismProperty.of_isPullback square inferInstance
  have hcomm : CommSq square.isoPullback.inv (pullback.snd f₀ (c.π.app (.op index)))
      f (𝟙 (c.pt : Scheme.{u})) :=
    ⟨square.isoPullback_inv_snd.trans (Category.comp_id _).symm⟩
  have hinv : IsIso square.isoPullback.inv := square.isoPullback.isIso_inv
  have hone : IsIso (𝟙 (c.pt : Scheme.{u})) := IsIso.id _
  have sqiso : IsPullback square.isoPullback.inv (pullback.snd f₀ (c.π.app (.op index)))
      f (𝟙 (c.pt : Scheme.{u})) := IsPullback.of_horiz_isIso hcomm
  have hw' : IsWeighting (pullback.snd f₀ (c.π.app (.op index)))
      (w ∘ square.isoPullback.inv) := IsWeighting.comp_of_isPullback hw sqiso
  have hfp₀ : FinitePresentation f₀ := ⟨inferInstance, inferInstance, inferInstance⟩
  obtain ⟨bound, hbound⟩ := (eventually_exists_weighting_baseChange
    D c hc index X₀ f₀ hfp₀ (w ∘ square.isoPullback.inv) hw').exists_forall_of_atTop
  obtain ⟨later, hindex, hboundlater⟩ := exists_ge_ge index bound
  obtain ⟨wᵢ, hwᵢ, hwi⟩ := hbound later hboundlater hindex
  let sourceᵢ : X ⟶ pullback f₀ (D.map (homOfLE hindex).op) :=
    pullback.lift source (f ≫ c.π.app (.op later)) (by
      rw [Category.assoc, c.w (homOfLE hindex).op]
      exact square.w)
  have squareᵢ : IsPullback sourceᵢ f
      (pullback.snd f₀ (D.map (homOfLE hindex).op)) (c.π.app (.op later)) := by
    exact isPullback_lift_pullback_snd (D.map (homOfLE hindex).op)
      (by simpa only [c.w] using square)
  refine ⟨later, hindex, wᵢ, hwᵢ, sourceᵢ, squareᵢ, ?_⟩
  have hcomp : square.isoPullback.hom ≫
      pullback.lift (pullback.fst f₀ (c.π.app (.op index)))
        (pullback.snd f₀ (c.π.app (.op index)) ≫ c.π.app (.op later))
        (by rw [Category.assoc, c.w (homOfLE hindex).op]; exact pullback.condition)
          = sourceᵢ := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, sourceᵢ, square.isoPullback_hom_fst]
    · simp only [Category.assoc, pullback.lift_snd, sourceᵢ,
        square.isoPullback_hom_snd_assoc]
  funext x
  have hx := congrArg (fun weight ↦ weight (square.isoPullback.hom x)) hwi
  simpa [Function.comp_apply, ← Scheme.Hom.comp_apply,
    square.isoPullback.hom_inv_id, hcomp] using hx

/-! ### The maximum locus over a limit of Noetherian affine schemes -/

private theorem exists_isAffineOpen_maxLocus_of_noetherian_approximation
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ index : I, IsAffine (D.obj (.op index))]
    [∀ index : I, IsLocallyNoetherian (D.obj (.op index))]
    {X X₀ : Scheme.{u}} [IsAffine X] [IsAffine c.pt] [IsAffine X₀]
    (index : I) (f : X ⟶ c.pt) (f₀ : X₀ ⟶ D.obj (.op index))
    [LocallyOfFinitePresentation f₀] [LocallyQuasiFinite f₀]
    (source : X ⟶ X₀) (square : IsPullback source f f₀ (c.π.app (.op index)))
    (w : X → ℤ) (hw : IsWeighting f w)
    (hpositive : ∀ x, 0 < w x) (d : ℤ)
    (hd : IsGreatest (Set.range (separableDegreeWeightedFiberSum f w)) d)
    (h0F3H : LevelSetsLocallyConstructible.{u}) :
    ∃ U : c.pt.Opens,
      (U : Set c.pt) = {y | separableDegreeWeightedFiberSum f w y = d} ∧
        IsAffineOpen U := by
  obtain ⟨stage, transition, wᵢ, hwᵢ, sourceᵢ, squareᵢ, hwi⟩ :=
    exists_weighting_stage D c hc index f f₀ source square w hw
  have : LocallyOfFiniteType f := MorphismProperty.of_isPullback square inferInstance
  have : LocallyQuasiFinite f := MorphismProperty.of_isPullback square inferInstance
  set fᵢ : (pullback f₀ (D.map (homOfLE transition).op) : Scheme.{u}) ⟶ D.obj (.op stage) :=
    pullback.snd f₀ (D.map (homOfLE transition).op) with hfᵢ
  have hpositiveᵢ : ∀ x, 0 < wᵢ (sourceᵢ x) := by
    intro x
    change 0 < (wᵢ ∘ sourceᵢ) x
    rw [← hwi]
    exact hpositive x
  obtain ⟨later, laterTransition, hgood⟩ :=
    exists_empty_bad_weighting_stage D c hc stage f fᵢ sourceᵢ squareᵢ wᵢ hwᵢ
      hpositiveᵢ d
      (by
        intro y
        rw [← hwi]
        exact hd.2 (Set.mem_range_self y))
      h0F3H
  set base : D.obj (.op later) ⟶ D.obj (.op stage) := D.map (homOfLE laterTransition).op
    with hbase
  set fₗ : (pullback fᵢ base : Scheme.{u}) ⟶ D.obj (.op later) := pullback.snd fᵢ base
    with hfₗ
  set wₗ : ↥(pullback fᵢ base) → ℤ := wᵢ ∘ pullback.fst fᵢ base with hwₗdef
  have hwₗ : IsWeighting fₗ wₗ :=
    IsWeighting.comp_of_isPullback hwᵢ (IsPullback.of_hasPullback fᵢ base)
  have hpositiveₗ : ∀ x, 0 < wₗ x := by
    intro x
    refine (hgood (fₗ x)).1 (pullback.fst fᵢ base x) ?_
    exact congrArg (fun morphism ↦ morphism x) (pullback.condition (f := fᵢ) (g := base))
  have hsumₗ := separableDegreeWeightedFiberSum_comp_of_isPullback
    fᵢ (pullback.fst fᵢ base) fₗ base (IsPullback.of_hasPullback fᵢ base)
    fᵢ.finite_preimage_singleton wᵢ
  have hboundₗ : ∀ y, separableDegreeWeightedFiberSum fₗ wₗ y ≤ d := fun y ↦
    congrFun hsumₗ y ▸ (hgood y).2
  set sourceₗ : X ⟶ (pullback fᵢ base : Scheme.{u}) :=
    pullback.lift sourceᵢ (f ≫ c.π.app (.op later)) (by
      rw [Category.assoc, c.w (homOfLE laterTransition).op]
      exact squareᵢ.w) with hsourceₗ
  have squareₗ : IsPullback sourceₗ f fₗ (c.π.app (.op later)) :=
    isPullback_lift_pullback_snd base (by simpa only [hbase, c.w] using squareᵢ)
  have hwcomp : w = wₗ ∘ sourceₗ := by
    rw [hwi]
    funext x
    change wᵢ (sourceᵢ x) = wᵢ ((sourceₗ ≫ pullback.fst fᵢ base) x)
    rw [hsourceₗ, pullback.lift_fst]
  have hsum := separableDegreeWeightedFiberSum_comp_of_isPullback
    fₗ sourceₗ f (c.π.app (.op later)) squareₗ fₗ.finite_preimage_singleton wₗ
  have hdₗ : IsGreatest (Set.range (separableDegreeWeightedFiberSum fₗ wₗ)) d := by
    refine ⟨?_, ?_⟩
    · obtain ⟨y, hy⟩ := hd.1
      refine ⟨c.π.app (.op later) y, ?_⟩
      have heq := congrFun hsum y
      rw [← hwcomp] at heq
      exact heq.trans hy
    · rintro value ⟨y, rfl⟩
      exact hboundₗ y
  obtain ⟨Uₗ, hUₗ, hfiniteₗ⟩ := exists_finite_maximumLocus fₗ wₗ hwₗ hpositiveₗ d hdₗ
  have : UniversallyOpen fₗ := universallyOpen_of_positive_weighting hwₗ hpositiveₗ
  have : IsNoetherian (D.obj (.op later)) :=
    (isNoetherian_iff _).mpr ⟨inferInstance, inferInstance⟩
  have hAffineₗ := isAffineOpen_maxLocus_of_isNoetherian fₗ wₗ hwₗ Uₗ hfiniteₗ d hUₗ
  refine ⟨c.π.app (.op later) ⁻¹ᵁ Uₗ, ?_, hAffineₗ.preimage _⟩
  exact preimage_eq_levelSet_of_comp _ Uₗ _ _ d (by rw [hwcomp]; exact hsum) hUₗ

/-! ### A Noetherian affine model -/

private theorem exists_noetherianModel
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
    [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    (hfp : FinitePresentation f) :
    Nonempty {model : FiniteTypeAffineModel ⊤ f //
      IsNoetherian model.S₀ ∧ LocallyQuasiFinite model.f₀} := by
  have hdiscrete (y : Y) : DiscreteTopology (f.fiber y) :=
    (f.fiberHomeo y).discreteTopology_iff.mpr
      (isDiscrete_iff_discreteTopology.mp
        (locallyQuasiFinite_iff_isDiscrete_preimage_singleton.mp inferInstance y))
  obtain ⟨model, hdim⟩ :=
    exists_finiteTypeAffineModel_fiberDimension_le f hfp 0 (fun y ↦ by
      have := hdiscrete y
      change topologicalKrullDim (f.fiber y) ≤ ((0 : ℕ) : WithBot ℕ∞)
      simpa using topologicalKrullDim_zero_of_discreteTopology (f.fiber y))
  have := model.base_affine
  have := model.locallyOfFiniteType
  have := model.base_locallyOfFiniteType
  have := model.base_quasiCompact
  let terminalIso := (terminalIsTerminal : IsTerminal (⊤_ Scheme.{u})).uniqueUpToIso
    specULiftZIsTerminal
  have : IsNoetherianRing (ULift.{u} ℤ) :=
    isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  have : IsLocallyNoetherian (Spec (.of (ULift.{u} ℤ))) := inferInstance
  have : IsLocallyNoetherian (⊤_ Scheme.{u}) :=
    isLocallyNoetherian_of_isOpenImmersion terminalIso.hom
  have : CompactSpace (⊤_ Scheme.{u}) :=
    terminalIso.symm.hom.homeomorph.compactSpace
  have : IsLocallyNoetherian model.S₀ :=
    LocallyOfFiniteType.isLocallyNoetherian (terminal.from _)
  have : CompactSpace model.S₀ :=
    QuasiCompact.compactSpace_of_compactSpace (terminal.from model.S₀)
  have : IsNoetherian model.S₀ := (isNoetherian_iff _).mpr ⟨inferInstance, inferInstance⟩
  exact ⟨model, inferInstance,
    locallyQuasiFinite_of_forall_topologicalKrullDim_fiber_le_zero model.f₀ hdim⟩

/-! ### An affine scheme as the limit of the spectra of its finitely generated subalgebras -/

private noncomputable def subalgebraDiagram (R A : CommRingCat.{u}) [Algebra R A] :
    Finset A ⥤ CommRingCat.{u} where
  obj generators := .of (Algebra.adjoin R (generators : Set A))
  map inclusion := CommRingCat.ofHom (Subalgebra.inclusion
    (Algebra.adjoin_mono (Finset.coe_subset.mpr (leOfHom inclusion)))).toRingHom

private noncomputable def subalgebraCocone (R A : CommRingCat.{u}) [Algebra R A] :
    Cocone (subalgebraDiagram R A) where
  pt := A
  ι :=
    { app := fun generators ↦
        CommRingCat.ofHom ((Algebra.adjoin R (generators : Set A)).val.toRingHom) }

private noncomputable def subalgebraIsColimit (R A : CommRingCat.{u}) [Algebra R A] :
    IsColimit (subalgebraCocone R A) := by
  have := reflectsColimit_of_reflectsIsomorphisms (subalgebraDiagram R A) (forget CommRingCat)
  apply isColimitOfReflects (forget CommRingCat)
  apply Types.FilteredColimit.isColimitOf'
  · intro element
    exact ⟨{element}, ⟨element, Algebra.subset_adjoin (Finset.mem_singleton_self _)⟩, rfl⟩
  · intro generators first second equal
    refine ⟨generators, 𝟙 _, ?_⟩
    change first = second
    exact Subtype.ext equal

private noncomputable def affineSystem (R A : CommRingCat.{u}) [Algebra R A] :
    (Finset A)ᵒᵖ ⥤ Scheme.{u} := (subalgebraDiagram R A).op ⋙ Scheme.Spec

private noncomputable def affineCone (R A : CommRingCat.{u}) [Algebra R A] :
    Cone (affineSystem R A) := Scheme.Spec.mapCone (subalgebraCocone R A).op

private noncomputable def affineIsLimit (R A : CommRingCat.{u}) [Algebra R A] :
    IsLimit (affineCone R A) :=
  isLimitOfPreserves Scheme.Spec (subalgebraIsColimit R A).op

private theorem isAffine_affineSystem (R A : CommRingCat.{u}) [Algebra R A]
    (generators : Finset A) : IsAffine ((affineSystem R A).obj (.op generators)) :=
  inferInstanceAs (IsAffine (Spec (.of (Algebra.adjoin R (generators : Set A)))))

private theorem isLocallyNoetherian_affineSystem (R A : CommRingCat.{u}) [Algebra R A]
    [IsNoetherianRing R] (generators : Finset A) :
    IsLocallyNoetherian ((affineSystem R A).obj (.op generators)) := by
  have : IsNoetherianRing (Algebra.adjoin R (generators : Set A)) :=
    isNoetherianRing_of_fg (Subalgebra.fg_adjoin_finset generators)
  exact inferInstanceAs
    (IsLocallyNoetherian (Spec (.of (Algebra.adjoin R (generators : Set A)))))

private theorem isoSpec_comp_subalgebraVal_eq
    {S Y : Scheme.{u}} [IsAffine S] [IsAffine Y] (t : Y ⟶ S)
    [Algebra Γ(S, ⊤) Γ(Y, ⊤)]
    (halg : ∀ r : Γ(S, ⊤), algebraMap Γ(S, ⊤) Γ(Y, ⊤) r = t.appTop.hom r)
    (B : Subalgebra Γ(S, ⊤) Γ(Y, ⊤)) :
    (Y.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom B.val.toRingHom)) ≫
        (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) B)) ≫ S.isoSpec.inv) = t := by
  rw [Category.assoc]
  have heq : CommRingCat.ofHom (algebraMap Γ(S, ⊤) B) ≫
      CommRingCat.ofHom B.val.toRingHom = t.appTop := by
    ext r
    exact halg r
  rw [← Spec.map_comp_assoc, heq, Scheme.isoSpec_inv_naturality,
    ← Category.assoc, Y.isoSpec.hom_inv_id, Category.id_comp]

private theorem exists_isPullback_of_model
    {X Y T : Scheme.{u}} {f : X ⟶ Y} (model : FiniteTypeAffineModel ⊤ f)
    (base : T ⟶ model.S₀) (g : Y ⟶ T) (hbase : g ≫ base = model.toBase) :
    ∃ source : X ⟶ (pullback model.f₀ base : Scheme.{u}),
      IsPullback source f (pullback.snd model.f₀ base) g := by
  exact ⟨_, isPullback_lift_pullback_snd base (by rw [hbase]; exact model.isPullback)⟩

private noncomputable def subalgebraSchemeCone {Y : Scheme.{u}} [IsAffine Y]
    (R : CommRingCat.{u}) [Algebra R Γ(Y, ⊤)] :
    Cone (affineSystem R Γ(Y, ⊤)) :=
  (affineCone R Γ(Y, ⊤)).extend Y.isoSpec.hom

private theorem affineCone_π_app (R A : CommRingCat.{u}) [Algebra R A]
    (generators : Finset A) :
    (affineCone R A).π.app (.op generators) =
      Spec.map (CommRingCat.ofHom
        (Algebra.adjoin R (generators : Set A)).val.toRingHom) := rfl

private theorem subalgebraSchemeCone_π_app {Y : Scheme.{u}} [IsAffine Y]
    (R : CommRingCat.{u}) [Algebra R Γ(Y, ⊤)] (generators : Finset Γ(Y, ⊤)) :
    (subalgebraSchemeCone (Y := Y) R).π.app (.op generators) =
      Y.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
        (Algebra.adjoin R (generators : Set Γ(Y, ⊤))).val.toRingHom) := by
  rw [← affineCone_π_app]
  rfl

private noncomputable def subalgebraSchemeConeIsLimit {Y : Scheme.{u}} [IsAffine Y]
    (R : CommRingCat.{u}) [Algebra R Γ(Y, ⊤)] :
    IsLimit (subalgebraSchemeCone (Y := Y) R) :=
  (affineIsLimit R Γ(Y, ⊤)).ofIsoLimit
    (Cone.extendIso (affineCone R Γ(Y, ⊤)) Y.isoSpec.symm)

/-- An affine scheme over a Noetherian affine base is the limit of a directed inverse system of
affine locally Noetherian schemes, compatibly with a chosen map to the base: take the spectra of
the finitely generated subalgebras of its ring of sections over the base's. -/
private theorem exists_affine_noetherian_limit_over
    {S Y : Scheme.{u}} [IsAffine S] [IsAffine Y] [IsNoetherian S] (t : Y ⟶ S) :
    ∃ (I : Type u) (_ : Preorder I) (_ : IsDirected I (· ≤ ·))
      (D : Iᵒᵖ ⥤ Scheme.{u}) (π : (Functor.const Iᵒᵖ).obj Y ⟶ D)
      (_ : IsLimit (Cone.mk Y π))
      (_ : ∀ i : I, IsAffine (D.obj (.op i)))
      (_ : ∀ i : I, IsLocallyNoetherian (D.obj (.op i)))
      (i₀ : I) (base : D.obj (.op i₀) ⟶ S),
      (Cone.mk Y π).π.app (.op i₀) ≫ base = t := by
  let : Algebra Γ(S, ⊤) Γ(Y, ⊤) := t.appTop.hom.toAlgebra
  have hR : IsNoetherianRing Γ(S, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  have hlim : IsLimit (Cone.mk Y (subalgebraSchemeCone (Y := Y) Γ(S, ⊤)).π) :=
    subalgebraSchemeConeIsLimit Γ(S, ⊤)
  refine ⟨Finset Γ(Y, ⊤), inferInstance, inferInstance,
    affineSystem Γ(S, ⊤) Γ(Y, ⊤), (subalgebraSchemeCone (Y := Y) Γ(S, ⊤)).π, hlim,
    isAffine_affineSystem Γ(S, ⊤) Γ(Y, ⊤),
    isLocallyNoetherian_affineSystem Γ(S, ⊤) Γ(Y, ⊤), ∅,
    Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤)
      (Algebra.adjoin Γ(S, ⊤) ((∅ : Finset Γ(Y, ⊤)) : Set Γ(Y, ⊤))))) ≫ S.isoSpec.inv, ?_⟩
  change (subalgebraSchemeCone (Y := Y) Γ(S, ⊤)).π.app (.op (∅ : Finset Γ(Y, ⊤))) ≫ _ = t
  rw [subalgebraSchemeCone_π_app]
  exact isoSpec_comp_subalgebraVal_eq t (fun _ ↦ rfl)
    (Algebra.adjoin Γ(S, ⊤) ((∅ : Finset Γ(Y, ⊤)) : Set Γ(Y, ⊤)))

/-! ### The maximum locus of a positive weighting is affine -/

private theorem exists_isAffineOpen_weightedFiberSum_eq_max_of_affine
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
    [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    (hfp : FinitePresentation f)
    (w : X → ℤ) (hw : IsWeighting f w)
    (hpositive : ∀ x, 0 < w x) (d : ℤ)
    (hd : IsGreatest (Set.range (separableDegreeWeightedFiberSum f w)) d)
    (h0F3H : LevelSetsLocallyConstructible.{u}) :
    ∃ U : Y.Opens,
      (U : Set Y) = {y | separableDegreeWeightedFiberSum f w y = d} ∧
        IsAffineOpen U := by
  obtain ⟨model, hnoetherian, hquasiFinite⟩ := exists_noetherianModel f hfp
  have := model.source_affine
  have := model.base_affine
  have := model.locallyOfFiniteType
  have := model.quasiCompact
  have := hnoetherian
  have := hquasiFinite
  obtain ⟨I, _, _, D, π, hc, hAffine, hNoetherian, index, base, hbase⟩ :=
    exists_affine_noetherian_limit_over model.toBase
  have := hAffine
  have := hNoetherian
  have hpt : IsAffine (Cone.mk Y π).pt := inferInstanceAs (IsAffine Y)
  obtain ⟨source, square⟩ :=
    exists_isPullback_of_model model base ((Cone.mk Y π).π.app (.op index)) hbase
  exact exists_isAffineOpen_maxLocus_of_noetherian_approximation D (Cone.mk Y π) hc index f
    (pullback.snd model.f₀ base) source square w hw hpositive d hd h0F3H

/-- Tag 0F3H, in the form in which the descent argument uses it. -/
private theorem levelSetsLocallyConstructible : LevelSetsLocallyConstructible.{u} := by
  intro X' Y' g hqf hfp v hv m
  have := hqf
  exact isLocallyConstructible_separableDegreeWeightedFiberSum_levelSet g hfp v hv m

/-- **Stacks Project, Tag 0F3R.** Let `f : X ⟶ Y` be a quasi-finite morphism of finite
presentation between affine schemes and let `w` be an everywhere positive weighting of `f`.
If the weighted fibre sum of `w` attains a greatest value `d`, then the locus in `Y` where
that value is attained is an affine open subscheme of `Y`.

Quasi-finiteness is expressed, as in Tag 01TD, by `AlgebraicGeometry.LocallyOfFiniteType`
together with `AlgebraicGeometry.LocallyQuasiFinite`; the maximum value exists by Tag 0F3K, and
the locus is produced together with its openness rather than assumed open. -/
@[stacks 0F3R]
theorem exists_isAffineOpen_separableDegreeWeightedFiberSum_eq_max
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
    [LocallyOfFiniteType f] [LocallyQuasiFinite f] (hfp : FinitePresentation f)
    (w : X → ℤ) (hw : IsWeighting f w) (hpositive : ∀ x, 0 < w x) (d : ℤ)
    (hd : IsGreatest (Set.range (separableDegreeWeightedFiberSum f w)) d) :
    ∃ U : Y.Opens,
      (U : Set Y) = {y | separableDegreeWeightedFiberSum f w y = d} ∧ IsAffineOpen U :=
  exists_isAffineOpen_weightedFiberSum_eq_max_of_affine f hfp w hw hpositive d hd
    levelSetsLocallyConstructible

end AlgebraicGeometry

end
