module

public import Mathlib.AlgebraicGeometry.Morphisms.Descent
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.Restrict
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.MorphismProperty.FaithfullyFlatRing

/-!
# Descent of local finiteness along an fppf morphism

Consider morphisms of schemes `X ⟶ Y ⟶ S`. If the first morphism is surjective, flat and
locally of finite presentation, then both local finite presentation and local finite type
descend from the composite `X ⟶ S` to `Y ⟶ S`.

## Main results

* `AlgebraicGeometry.locallyOfFinitePresentation_of_comp_of_fppf`: the locally finitely
  presented case.
* `AlgebraicGeometry.locallyOfFiniteType_of_comp_of_fppf`: the locally finite type case.

## Implementation notes

The commutative triangle is represented by taking the morphism `X ⟶ S` to be the composite
`f ≫ q`. Both statements are reduced to the affine case by restricting along affine opens
with `Scheme.Hom.resLE`, where they become the corresponding descent statements for ring
maps along a faithfully flat map of finite presentation.

## References

* [Stacks Project, Tag 02KL](https://stacks.math.columbia.edu/tag/02KL)
* [EGA IV, 17.7.5 (i) and (ii)]
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- An affine scheme mapping onto `X` by a morphism which is, like `f`, surjective, flat and
locally of finite presentation over the affine target of `f`. -/
private theorem exists_affine_fppf_cover
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsAffine Y] [Surjective f] [Flat f] [LocallyOfFinitePresentation f] :
    ∃ (T : Scheme.{u}) (h : T ⟶ X), IsAffine T ∧
      LocallyOfFinitePresentation h ∧ Surjective (h ≫ f) ∧
      Flat (h ≫ f) ∧ LocallyOfFinitePresentation (h ≫ f) := by
  obtain ⟨W, hW, hWsurj⟩ :=
    IsOpenMap.exists_opens_image_eq_of_prespectralSpace f.continuous
      (Scheme.Hom.isOpenMap f) (U := (Set.univ : Set Y)) (by simp) isOpen_univ isCompact_univ
  have : CompactSpace (Scheme.Opens.toScheme W) := isCompact_iff_compactSpace.mp hW
  have : IsZariskiLocalAtSource @Flat.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Flat)
  have : IsZariskiLocalAtSource @LocallyOfFinitePresentation.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFinitePresentation)
  have : MorphismProperty.ContainsIdentities (@Flat.{u}) :=
    HasRingHomProperty.containsIdentities RingHom.Flat.containsIdentities
  have : MorphismProperty.ContainsIdentities (@LocallyOfFinitePresentation.{u}) :=
    HasRingHomProperty.containsIdentities
      RingHom.finitePresentation_holdsForLocalizationAway.containsIdentities
  have : IsZariskiLocalAtSource (@Flat.{u} ⊓ @LocallyOfFinitePresentation.{u}) :=
    MorphismProperty.IsLocalAtSource.inf @Flat.{u} @LocallyOfFinitePresentation.{u}
  have : MorphismProperty.ContainsIdentities
      (@Flat.{u} ⊓ @LocallyOfFinitePresentation.{u}) :=
    MorphismProperty.ContainsIdentities.inf
  obtain ⟨T, hT, hTsurj, ⟨_, _⟩, hTaff⟩ :=
    AlgebraicGeometry.Scheme.exists_hom_isAffine_of_isZariskiLocalAtSource
      (@Flat.{u} ⊓ @LocallyOfFinitePresentation.{u}) (Scheme.Opens.toScheme W)
  have : Surjective (Scheme.Opens.ι W ≫ f) := ⟨fun y ↦ by
    obtain ⟨x, hxW, hxy⟩ : y ∈ f.base '' W := by
      rw [hWsurj]
      trivial
    exact ⟨⟨x, hxW⟩, hxy⟩⟩
  refine ⟨T, hT ≫ Scheme.Opens.ι W, hTaff, ?_, ?_, ?_, ?_⟩
  · infer_instance
  · simpa only [Category.assoc] using
      (show Surjective (hT ≫ (Scheme.Opens.ι W ≫ f)) from inferInstance)
  · infer_instance
  · infer_instance

/-- The affine case of descent of local finite presentation along an fppf morphism. -/
@[sga "4 IV 8.5.5" "special case"]
private theorem locallyOfFinitePresentation_of_comp_of_fppf_affine
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (q : Y ⟶ S)
    [IsAffine Y] [IsAffine S] [Surjective f] [Flat f]
    [LocallyOfFinitePresentation f]
    [LocallyOfFinitePresentation (f ≫ q)] :
    LocallyOfFinitePresentation q := by
  obtain ⟨T, h, _, _, hs, hf, hp⟩ := exists_affine_fppf_cover f
  let g := h ≫ f
  have : Surjective g := hs
  have : Flat g := hf
  have : LocallyOfFinitePresentation g := hp
  have : LocallyOfFinitePresentation (g ≫ q) := by
    show LocallyOfFinitePresentation (h ≫ (f ≫ q))
    infer_instance
  rw [HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)]
  exact RingHom.finitePresentation_of_comp_of_faithfullyFlat
    q.appTop.hom g.appTop.hom
    (by simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] using
      (g ≫ q).finitePresentation_appTop)
    ((Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine g).mp ⟨inferInstance, hs⟩)
    g.finitePresentation_appTop

/-- The affine case of descent of local finite type along an fppf morphism. -/
@[sga "4 IV 8.5.5" "special case"]
private theorem locallyOfFiniteType_of_comp_of_fppf_affine
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (q : Y ⟶ S)
    [IsAffine Y] [IsAffine S] [Surjective f] [Flat f]
    [LocallyOfFinitePresentation f]
    [LocallyOfFiniteType (f ≫ q)] :
    LocallyOfFiniteType q := by
  obtain ⟨T, h, _, _, hs, hf, hp⟩ := exists_affine_fppf_cover f
  let g := h ≫ f
  have : Surjective g := hs
  have : Flat g := hf
  have : LocallyOfFinitePresentation g := hp
  have : LocallyOfFiniteType (g ≫ q) := by
    show LocallyOfFiniteType (h ≫ (f ≫ q))
    infer_instance
  rw [HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)]
  exact RingHom.finiteType_of_comp_of_faithfullyFlat_of_finitePresentation
    (by simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] using
      (HasRingHomProperty.appTop (P := @LocallyOfFiniteType) (g ≫ q) inferInstance))
    ((Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine g).mp ⟨inferInstance, hs⟩)
    g.finitePresentation_appTop

/-- The restriction of a surjective morphism over an open of its target is surjective. -/
theorem surjective_resLE {X Y : Scheme.{u}} (f : X ⟶ Y) [Surjective f]
    (U : Y.Opens) : Surjective (f.resLE U (f ⁻¹ᵁ U) le_rfl) := by
  refine ⟨fun y ↦ ?_⟩
  obtain ⟨x, hx⟩ := f.surjective y.1
  refine ⟨⟨x, ?_⟩, ?_⟩
  · show f x ∈ U
    rw [hx]
    exact y.2
  · apply Subtype.ext
    simpa using hx

/-- Descent of a ring-hom-local property along a surjective flat morphism which is locally of
finite presentation reduces to the case where `Y` and `S` are affine. -/
private theorem comp_of_fppf_of_affine_case
    {P : MorphismProperty Scheme.{u}} {Q : ∀ {R S : Type u} [CommRing R] [CommRing S],
      (R →+* S) → Prop} [HasRingHomProperty P Q]
    (affine : ∀ {X Y S : Scheme.{u}} (f : X ⟶ Y) (q : Y ⟶ S) [IsAffine Y] [IsAffine S]
      [Surjective f] [Flat f] [LocallyOfFinitePresentation f], P (f ≫ q) → P q)
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (q : Y ⟶ S)
    [Surjective f] [Flat f] [LocallyOfFinitePresentation f] (hfq : P (f ≫ q)) : P q := by
  refine (HasRingHomProperty.iff_appLE (P := P) (Q := Q)).mpr ?_
  rintro ⟨V, hV⟩ ⟨U, hU⟩ e
  let f' := f.resLE U (f ⁻¹ᵁ U) le_rfl
  let q' := q.resLE V U e
  have : IsAffine U.toScheme := hU
  have : IsAffine V.toScheme := hV
  have : Surjective f' := surjective_resLE f U
  have : Flat f' := by
    dsimp only [f']
    infer_instance
  have : LocallyOfFinitePresentation f' := by
    dsimp only [f']
    infer_instance
  have hf'q' : P (f' ≫ q') := by
    dsimp only [f', q']
    rw [Scheme.Hom.resLE_comp_resLE]
    exact IsZariskiLocalAtSource.resLE _ hfq
  have hq'app := HasRingHomProperty.appLE (Q := Q) P q' (affine f' q' hf'q')
    ⟨⊤, isAffineOpen_top _⟩ ⟨⊤, isAffineOpen_top _⟩ (by simp)
  dsimp [q'] at hq'app
  rw [Scheme.Hom.resLE_appLE q e ⊤ ⊤ (by simp)] at hq'app
  exact (q.appLE_congr e (by simp) (by simp) (fun φ ↦ Q φ.hom)).mpr hq'app

/-- **Stacks Project, Tag 02KL (finite-presentation case).** Local finite presentation
descends through a surjective flat morphism which is locally of finite presentation. -/
@[stacks 02KL "locally of finite presentation",
  ega "IV 17.7.5" "(ii)",
  ega "IV 11.3.16" "loc. fin. presentation"]
theorem locallyOfFinitePresentation_of_comp_of_fppf
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (q : Y ⟶ S)
    [Surjective f] [Flat f] [LocallyOfFinitePresentation f]
    [LocallyOfFinitePresentation (f ≫ q)] :
    LocallyOfFinitePresentation q :=
  comp_of_fppf_of_affine_case (P := @LocallyOfFinitePresentation)
    (fun f q _ _ _ _ _ _ ↦ locallyOfFinitePresentation_of_comp_of_fppf_affine f q) f q inferInstance

/-- **Stacks Project, Tag 02KL (finite-type case).** Local finite type descends through a
surjective flat morphism which is locally of finite presentation. -/
@[stacks 02KL "locally of finite type",
  ega "IV 17.7.5" "(i)",
  ega "IV 11.3.16" "locally of finite type"]
theorem locallyOfFiniteType_of_comp_of_fppf
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (q : Y ⟶ S)
    [Surjective f] [Flat f] [LocallyOfFinitePresentation f]
    [LocallyOfFiniteType (f ≫ q)] :
    LocallyOfFiniteType q :=
  comp_of_fppf_of_affine_case (P := @LocallyOfFiniteType)
    (fun f q _ _ _ _ _ _ ↦ locallyOfFiniteType_of_comp_of_fppf_affine f q) f q inferInstance

end AlgebraicGeometry
