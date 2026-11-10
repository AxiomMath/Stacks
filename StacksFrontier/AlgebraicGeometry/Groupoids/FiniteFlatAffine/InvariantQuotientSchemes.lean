module

public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Cover.MorphismProperty
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.AffineQuotientPoints
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.InvariantBaseChange
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.InvariantModuliSpace
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The invariant spectrum is a categorical quotient in all schemes

Let `G = (U, R, s, t, c)` be a groupoid scheme with `U` and `R` affine and `s, t` finite locally
free, and let `C` be its ring of invariant functions. The canonical morphism
`φ : U ⟶ M = Spec C` is a categorical quotient in the category of affine schemes by the
`Γ`-`Spec` adjunction
(`AlgebraicGeometry.GroupoidScheme.existsUnique_comp_objectsToInvariantSpectrum`). This file shows
that it is a categorical quotient in the category of *all* schemes: every morphism `g : U ⟶ T` to
a scheme with `g ∘ t = g ∘ s` factors uniquely through `φ`.

In particular the structure morphism `U ⟶ S` descends to `M`, which makes `M` a scheme over the
base of the groupoid. Stacks 0DUP takes `M` as its moduli space without comment on this point;
`AlgebraicGeometry.GroupoidScheme.invariantSpectrumBaseMap` supplies the descent when `(t, s)` is
an equivalence relation, by effective descent along the finite locally free `φ`, and no such
argument is available for a general groupoid, where `φ` need not be flat.

## Main results

* `AlgebraicGeometry.GroupoidScheme.ext_of_comp_objectsToInvariantSpectrum`: `φ` is an
  epimorphism of schemes.
* `AlgebraicGeometry.GroupoidScheme.existsUnique_comp_objectsToInvariantSpectrum_scheme`: `φ` is a
  categorical quotient in the category of schemes.
* `AlgebraicGeometry.GroupoidScheme.invariantSpectrumDescentMap`: the descent of the structure
  morphism of the object scheme along `φ`.

## Implementation notes

The argument is local on `M` for the principal open cover. For `c ∈ C` the base change of `G`
along the flat localization `C ⟶ C_c` (**Stacks 03BK**,
`AlgebraicGeometry.GroupoidScheme.exists_affineInvariantBaseChange`) has object scheme the inverse
image of `D(c)`, and its structure morphism to `Spec C_c` is a categorical quotient in the
category of affine schemes because the invariant functions of the base change are `C_c`
(`AlgebraicGeometry.GroupoidScheme.existsUnique_comp_objects_hom_of_flat`). Given `g`, every
fibre of `φ` is a single orbit (**Stacks 03BL**), so `g` is constant on it; since `φ` is closed,
each point of `M` has a principal open neighbourhood whose inverse image is carried by `g` into a
single affine open of `T`, and there the affine universal property applies. The local
factorizations agree on overlaps by the same uniqueness, and glue.

## References

* [Stacks Project, Tag 03BK](https://stacks.math.columbia.edu/tag/03BK)
* [Stacks Project, Tag 03BL](https://stacks.math.columbia.edu/tag/03BL)
* [Stacks Project, Tag 0DUP](https://stacks.math.columbia.edu/tag/0DUP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids Stacks.Morphisms

universe u

namespace AlgebraicGeometry.GroupoidScheme

variable {S : Scheme.{u}} (G : GroupoidScheme S)

/-! ### The affine universal property after a flat extension of the invariant ring -/

/-- **After a flat extension `C ⟶ C'` of the invariant ring, the structure morphism of the object
scheme of the base change is a categorical quotient in the category of affine schemes.** This is
`AlgebraicGeometry.GroupoidScheme.existsUnique_comp_objects_hom_of_flat` with an arbitrary affine
scheme as target rather than a spectrum. -/
@[sga "1 V 1.9" "affine case with Z = Y"]
theorem existsUnique_comp_objects_hom_of_flat_of_isAffine {C' : Type u} [CommRing C']
    [Algebra (invariantRing G) C'] [Module.Flat (invariantRing G) C']
    (G' : AffineInvariantBaseChange G C') {V : Scheme.{u}} [IsAffine V]
    (ψ : G'.groupoid.objects.left ⟶ V)
    (hψ : G'.groupoid.target.left ≫ ψ = G'.groupoid.source.left ≫ ψ) :
    ∃! χ : Spec (.of C') ⟶ V, G'.groupoid.objects.hom ≫ χ = ψ := by
  obtain ⟨χ₀, hχ₀, hu⟩ := existsUnique_comp_objects_hom_of_flat G G' Γ(V, ⊤)
    (ψ ≫ V.isoSpec.hom) (by rw [reassoc_of% hψ])
  refine ⟨χ₀ ≫ V.isoSpec.inv, ?_, fun χ hχ => ?_⟩
  · change G'.groupoid.objects.hom ≫ χ₀ ≫ V.isoSpec.inv = ψ
    rw [← Category.assoc, hχ₀, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · have h := hu (χ ≫ V.isoSpec.hom) (by
      change G'.groupoid.objects.hom ≫ χ ≫ V.isoSpec.hom = ψ ≫ V.isoSpec.hom
      rw [← Category.assoc, hχ])
    rw [← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The structure morphism of the object scheme of a base change coequalizes its target and
source maps. -/
theorem target_comp_objects_hom {C' : Type u} [CommRing C'] [Algebra (invariantRing G) C']
    (G' : AffineInvariantBaseChange G C') :
    G'.groupoid.target.left ≫ G'.groupoid.objects.hom =
      G'.groupoid.source.left ≫ G'.groupoid.objects.hom := by
  rw [Over.w G'.groupoid.target, Over.w G'.groupoid.source]

/-- Over a flat extension of the invariant ring, a morphism from the base-changed object scheme
into an affine open `V` of `T` which coequalizes the target and source has a unique factorization
through `Spec C'` landing in `V`. -/
private theorem existsUnique_objects_hom_comp_eq_of_range_subset {C' : Type u} [CommRing C']
    [Algebra (invariantRing G) C'] [Module.Flat (invariantRing G) C']
    (G' : AffineInvariantBaseChange G C') {T : Scheme.{u}} (V : T.Opens) (hV : IsAffineOpen V)
    (ψ : G'.groupoid.objects.left ⟶ T) (hψV : Set.range ψ.base ⊆ V)
    (hψ : G'.groupoid.target.left ≫ ψ = G'.groupoid.source.left ≫ ψ) :
    ∃! f : Spec (.of C') ⟶ T, Set.range f.base ⊆ V ∧ G'.groupoid.objects.hom ≫ f = ψ := by
  have : IsAffine V := hV
  have hlift : ∀ {Y : Scheme.{u}} (k : Y ⟶ T), Set.range k.base ⊆ V → ∃ k' : Y ⟶ V, k' ≫ V.ι = k :=
    fun k hk => ⟨IsOpenImmersion.lift V.ι k (by rwa [Scheme.Opens.range_ι]),
      IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨ψ', rfl⟩ := hlift ψ hψV
  obtain ⟨χ, hχ, hu⟩ := existsUnique_comp_objects_hom_of_flat_of_isAffine G G' ψ'
    ((cancel_mono V.ι).1 (by simpa only [Category.assoc] using hψ))
  refine ⟨χ ≫ V.ι, ⟨fun _ ⟨z, hz⟩ => hz ▸ (χ.base z).2, by rw [← Category.assoc, hχ]⟩, ?_⟩
  rintro _ ⟨hk, hk'⟩
  obtain ⟨k', rfl⟩ := hlift _ hk
  rw [hu k' ((cancel_mono V.ι).1 (by simpa only [Category.assoc] using hk'))]

/-- **Uniqueness into an affine open.** After a flat extension `C ⟶ C'` of the invariant ring,
two morphisms `Spec C' ⟶ T` landing in one affine open of `T` agree as soon as their composites
with the structure morphism of the base-changed object scheme agree. -/
theorem eq_of_objects_hom_comp_eq {C' : Type u} [CommRing C'] [Algebra (invariantRing G) C']
    [Module.Flat (invariantRing G) C'] (G' : AffineInvariantBaseChange G C') {T : Scheme.{u}}
    (V : T.Opens) (hV : IsAffineOpen V) (k₁ k₂ : Spec (.of C') ⟶ T)
    (h₁ : Set.range k₁.base ⊆ V) (h₂ : Set.range k₂.base ⊆ V)
    (h : G'.groupoid.objects.hom ≫ k₁ = G'.groupoid.objects.hom ≫ k₂) : k₁ = k₂ :=
  (existsUnique_objects_hom_comp_eq_of_range_subset G G' V hV _ (fun _ ⟨z, hz⟩ => hz ▸ h₁ ⟨_, rfl⟩)
    (by rw [← Category.assoc, target_comp_objects_hom, Category.assoc])).unique ⟨h₁, rfl⟩
    ⟨h₂, h.symm⟩

/-- **Existence into an affine open.** After a flat extension `C ⟶ C'` of the invariant ring, a
morphism from the base-changed object scheme to `T` which lands in one affine open of `T` and
coequalizes the target and the source factors through `Spec C'`. -/
theorem exists_objects_hom_comp_eq {C' : Type u} [CommRing C'] [Algebra (invariantRing G) C']
    [Module.Flat (invariantRing G) C'] (G' : AffineInvariantBaseChange G C') {T : Scheme.{u}}
    (V : T.Opens) (hV : IsAffineOpen V) (ψ : G'.groupoid.objects.left ⟶ T)
    (hψV : Set.range ψ.base ⊆ V)
    (hψ : G'.groupoid.target.left ≫ ψ = G'.groupoid.source.left ≫ ψ) :
    ∃ f : Spec (.of C') ⟶ T, G'.groupoid.objects.hom ≫ f = ψ :=
  let ⟨f, ⟨_, hf⟩, _⟩ := existsUnique_objects_hom_comp_eq_of_range_subset G G' V hV ψ hψV hψ
  ⟨f, hf⟩

section Quotient

variable [IsAffine G.objects.left] [IsAffine G.arrows.left]
  [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left]

/-- The base change of `G` along the localization of its invariant ring at one element. -/
noncomputable def localizedBaseChange (c : invariantRing G) :
    AffineInvariantBaseChange G (Localization.Away c) :=
  (exists_affineInvariantBaseChange G (Localization.Away c)).some

omit [IsAffine G.objects.left] [IsAffine G.arrows.left] [IsFiniteLocallyFree G.source.left]
  [IsFiniteLocallyFree G.target.left] in
/-- The localization of the invariant ring at one element is flat over it. -/
instance flat_localization_away (c : invariantRing G) :
    Module.Flat (invariantRing G) (Localization.Away c) :=
  IsLocalization.flat _ (Submonoid.powers c)

omit [IsAffine G.objects.left] [IsAffine G.arrows.left] [IsFiniteLocallyFree G.source.left]
  [IsFiniteLocallyFree G.target.left] in
/-- The spectrum of a principal localization of the invariant ring is an open subscheme of `M`. -/
instance isOpenImmersion_invariantSpectrumMap_away (c : invariantRing G) :
    IsOpenImmersion (invariantSpectrumMap G (Localization.Away c)) := by
  unfold invariantSpectrumMap
  infer_instance

/-- The structure morphism of the object scheme of a base change is surjective, being a base
change of the surjective `φ`. -/
theorem surjective_objects_hom {C' : Type u} [CommRing C'] [Algebra (invariantRing G) C']
    (G' : AffineInvariantBaseChange G C') :
    Function.Surjective G'.groupoid.objects.hom.base := by
  have : Surjective (objectsToInvariantSpectrum G) :=
    ⟨surjective_objectsToInvariantSpectrum G⟩
  have h : Surjective G'.groupoid.objects.hom :=
    MorphismProperty.of_isPullback G'.objects_isPullback inferInstance
  exact h.surj

omit [IsAffine G.objects.left] [IsAffine G.arrows.left] [IsFiniteLocallyFree G.source.left]
  [IsFiniteLocallyFree G.target.left] in
/-- A point of `U` and a point of `Spec C'` with the same image in `M` come from a point of the
object scheme of the base change. -/
theorem exists_objects_point {C' : Type u} [CommRing C'] [Algebra (invariantRing G) C']
    (G' : AffineInvariantBaseChange G C') (x : G.objects.left) (y : Spec (.of C'))
    (h : (objectsToInvariantSpectrum G).base x = (invariantSpectrumMap G C').base y) :
    ∃ z : G'.groupoid.objects.left,
      G'.objectsProjection.base z = x ∧ G'.groupoid.objects.hom.base z = y := by
  obtain ⟨w, hw₁, hw₂⟩ := Scheme.Pullback.exists_preimage_pullback x y h
  refine ⟨G'.objects_isPullback.isoPullback.inv.base w, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst, hw₁]
  · rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_snd, hw₂]

/-- Two morphisms out of an open subscheme of `M` which agree after every principal localization
of `G` agree on points. -/
theorem base_eq_of_forall_localizedBaseChange {X T : Scheme.{u}}
    (j : X ⟶ Spec (.of (invariantRing G))) [IsOpenImmersion j] (k₁ k₂ : X ⟶ T)
    (h : ∀ (c : invariantRing G) (e : Spec (.of (Localization.Away c)) ⟶ X),
      e ≫ j = invariantSpectrumMap G (Localization.Away c) →
        (localizedBaseChange G c).groupoid.objects.hom ≫ e ≫ k₁ =
          (localizedBaseChange G c).groupoid.objects.hom ≫ e ≫ k₂) (p : X) :
    k₁.base p = k₂.base p := by
  obtain ⟨_, ⟨c, rfl⟩, hpc, hcj⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (show j.base p ∈ Set.range j.base from ⟨p, rfl⟩) j.isOpenEmbedding.isOpen_range
  have hrange : Set.range (invariantSpectrumMap G (Localization.Away c)).base =
      (PrimeSpectrum.basicOpen c : Set (PrimeSpectrum (invariantRing G))) :=
    PrimeSpectrum.localization_away_comap_range (Localization.Away c) c
  obtain ⟨e, he⟩ : ∃ e : Spec (.of (Localization.Away c)) ⟶ X,
      e ≫ j = invariantSpectrumMap G (Localization.Away c) :=
    ⟨IsOpenImmersion.lift j _ (by rwa [hrange]), IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨z, hz⟩ : j.base p ∈ Set.range (invariantSpectrumMap G (Localization.Away c)).base := by
    rwa [hrange]
  obtain ⟨w, rfl⟩ := surjective_objects_hom G (localizedBaseChange G c) z
  have hez : e.base ((localizedBaseChange G c).groupoid.objects.hom.base w) = p := by
    apply j.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, he, hz]
  have := congrArg (fun k => k.base w) (h c e he)
  simp only [Scheme.Hom.comp_base, TopCat.comp_app] at this
  rwa [hez] at this

omit [IsAffine G.objects.left] [IsAffine G.arrows.left] [IsFiniteLocallyFree G.source.left]
  [IsFiniteLocallyFree G.target.left] in
/-- For an open subscheme `j : X ⟶ M` and `k : X ⟶ T`, every point of `X` has a principal open
neighbourhood in `M` contained in the image of the inverse image of one affine open of `T`. -/
theorem exists_basicOpen_subset_image_preimage_affineOpen {X T : Scheme.{u}}
    (j : X ⟶ Spec (.of (invariantRing G))) [IsOpenImmersion j] (k : X ⟶ T) (p : X) :
    ∃ (c : invariantRing G) (V : T.Opens), IsAffineOpen V ∧
      j.base p ∈ PrimeSpectrum.basicOpen c ∧
      (PrimeSpectrum.basicOpen c : Set (PrimeSpectrum (invariantRing G))) ⊆
        j.base '' (k.base ⁻¹' V) := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hpV, -⟩ :=
    T.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (k.base p)) isOpen_univ
  obtain ⟨_, ⟨c, rfl⟩, hpc, hcO⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (show j.base p ∈ j.base '' (k.base ⁻¹' V) from ⟨p, hpV, rfl⟩)
      (j.isOpenEmbedding.isOpenMap _ (V.isOpen.preimage k.base.hom.continuous))
  exact ⟨c, V, hV, hpc, hcO⟩

/-- **Two morphisms out of an open subscheme of `M` agree as soon as they agree after every
principal localization of `G`.** For an open immersion `j : X ⟶ M` and `k₁ k₂ : X ⟶ T`, it is
enough that for every `c ∈ C` and every `e : Spec C_c ⟶ X` over `M` the two composites
`U_c ⟶ Spec C_c ⟶ X ⟶ T` from the object scheme of the localized groupoid agree. -/
theorem ext_of_forall_localizedBaseChange {X T : Scheme.{u}}
    (j : X ⟶ Spec (.of (invariantRing G))) [IsOpenImmersion j] (k₁ k₂ : X ⟶ T)
    (h : ∀ (c : invariantRing G) (e : Spec (.of (Localization.Away c)) ⟶ X),
      e ≫ j = invariantSpectrumMap G (Localization.Away c) →
        (localizedBaseChange G c).groupoid.objects.hom ≫ e ≫ k₁ =
          (localizedBaseChange G c).groupoid.objects.hom ≫ e ≫ k₂) :
    k₁ = k₂ := by
  classical
  have hrange : ∀ c : invariantRing G, Set.range (invariantSpectrumMap G (Localization.Away c)) =
      (PrimeSpectrum.basicOpen c : Set (PrimeSpectrum (invariantRing G))) := fun c =>
    PrimeSpectrum.localization_away_comap_range (Localization.Away c) c
  -- the lift of a principal open contained in the image of `j`
  have hlift : ∀ c : invariantRing G,
      (PrimeSpectrum.basicOpen c : Set (PrimeSpectrum (invariantRing G))) ⊆ Set.range j →
      ∃ e : Spec (.of (Localization.Away c)) ⟶ X,
        e ≫ j = invariantSpectrumMap G (Localization.Away c) := fun c hc =>
    ⟨IsOpenImmersion.lift j _ (by rwa [hrange c]), IsOpenImmersion.lift_fac _ _ _⟩
  choose c V hV hpc hcO using exists_basicOpen_subset_image_preimage_affineOpen G j k₁
  have hcj : ∀ p, (PrimeSpectrum.basicOpen (c p) : Set (PrimeSpectrum (invariantRing G))) ⊆
      Set.range j := fun p => (hcO p).trans (Set.image_subset_range _ _)
  choose e he using fun p => hlift (c p) (hcj p)
  have : ∀ p, IsOpenImmersion (e p) := fun p => by
    have : IsOpenImmersion (e p ≫ j) := by rw [he p]; infer_instance
    exact IsOpenImmersion.of_comp (e p) j
  let 𝒰 : X.OpenCover := Scheme.Cover.mkOfCovers X (fun p => Spec (.of (Localization.Away (c p))))
    e (fun p => by
      obtain ⟨z, hz⟩ : j.base p ∈
          Set.range (invariantSpectrumMap G (Localization.Away (c p))).base :=
        (hrange (c p)).ge (hpc p)
      refine ⟨p, z, j.isOpenEmbedding.injective ?_⟩
      rw [← Scheme.Hom.comp_apply, he p, hz])
  refine Scheme.Cover.hom_ext 𝒰 k₁ k₂ fun p => ?_
  change e p ≫ k₁ = e p ≫ k₂
  -- both composites land in the affine open `V p`
  have hV₁ : Set.range (e p ≫ k₁).base ⊆ V p := by
    rintro _ ⟨z, rfl⟩
    obtain ⟨q, hq, hqz⟩ : j.base ((e p).base z) ∈ j.base '' (k₁.base ⁻¹' (V p)) := hcO p (by
      rw [← Scheme.Hom.comp_apply, he p]
      exact (hrange (c p)).le ⟨z, rfl⟩)
    rwa [j.isOpenEmbedding.injective hqz] at hq
  have hV₂ : Set.range (e p ≫ k₂).base ⊆ V p := by
    rintro _ ⟨z, rfl⟩
    have := hV₁ ⟨z, rfl⟩
    rwa [Scheme.Hom.comp_apply, base_eq_of_forall_localizedBaseChange G j k₁ k₂ h] at this
  exact eq_of_objects_hom_comp_eq G (localizedBaseChange G (c p)) (V p) (hV p) _ _ hV₁ hV₂
    (by simpa only [Category.assoc] using h (c p) (e p) (he p))

/-- **The quotient map `φ : U ⟶ M` is an epimorphism of schemes.** -/
theorem ext_of_comp_objectsToInvariantSpectrum {T : Scheme.{u}}
    (h₁ h₂ : Spec (.of (invariantRing G)) ⟶ T)
    (h : objectsToInvariantSpectrum G ≫ h₁ = objectsToInvariantSpectrum G ≫ h₂) : h₁ = h₂ := by
  refine ext_of_forall_localizedBaseChange G (𝟙 _) h₁ h₂ fun c e he => ?_
  rw [Category.comp_id] at he
  rw [he, ← Category.assoc, ← (localizedBaseChange G c).objects_isPullback.w, Category.assoc, h,
    ← Category.assoc, (localizedBaseChange G c).objects_isPullback.w, Category.assoc]

omit [IsAffine G.objects.left] [IsAffine G.arrows.left] [IsFiniteLocallyFree G.source.left]
  [IsFiniteLocallyFree G.target.left] in
/-- The range of the inclusion of a principal open of `M`. -/
theorem range_invariantSpectrumMap_away (c : invariantRing G) :
    Set.range (invariantSpectrumMap G (Localization.Away c)).base =
      (PrimeSpectrum.basicOpen c : Set (PrimeSpectrum (invariantRing G))) :=
  PrimeSpectrum.localization_away_comap_range (Localization.Away c) c

/-- The object schemes of the principal localizations at a family of elements whose principal
opens cover `M` cover `U`. -/
noncomputable def localizedObjectsCover (c : Spec (.of (invariantRing G)) → invariantRing G)
    (hmc : ∀ m, m ∈ PrimeSpectrum.basicOpen (c m)) : G.objects.left.OpenCover :=
  Scheme.Cover.mkOfCovers _ (fun m => (localizedBaseChange G (c m)).groupoid.objects.left)
    (fun m => (localizedBaseChange G (c m)).objectsProjection) (fun x => by
      obtain ⟨z, hz⟩ : (objectsToInvariantSpectrum G).base x ∈ Set.range
          (invariantSpectrumMap G
            (Localization.Away (c ((objectsToInvariantSpectrum G).base x)))).base :=
        (range_invariantSpectrumMap_away G _).ge (hmc _)
      obtain ⟨w, hw, -⟩ := exists_objects_point G
        (localizedBaseChange G (c ((objectsToInvariantSpectrum G).base x))) x z hz.symm
      exact ⟨_, w, hw⟩)
    (fun m => MorphismProperty.of_isPullback
      (localizedBaseChange G (c m)).objects_isPullback.flip inferInstance)

/-- The principal opens of a family of elements whose principal opens cover `M`, as an open cover
of `M`. -/
noncomputable def principalCover (c : Spec (.of (invariantRing G)) → invariantRing G)
    (hmc : ∀ m, m ∈ PrimeSpectrum.basicOpen (c m)) : (Spec (.of (invariantRing G))).OpenCover :=
  Scheme.Cover.mkOfCovers _ (fun m => Spec (.of (Localization.Away (c m))))
    (fun m => invariantSpectrumMap G (Localization.Away (c m))) (fun m => by
      obtain ⟨z, hz⟩ : m ∈ Set.range
          (invariantSpectrumMap G (Localization.Away (c m))).base :=
        (range_invariantSpectrumMap_away G _).ge (hmc m)
      exact ⟨m, z, hz⟩)

/-- A factorization of `g` over the principal open `D(c)` is compatible with any morphism from
another principal open `D(c')` over `M`. -/
theorem objects_hom_comp_comp_eq_of_localizedBaseChange {T : Scheme.{u}}
    (g : G.objects.left ⟶ T) {c c' : invariantRing G} (f : Spec (.of (Localization.Away c)) ⟶ T)
    (hf : (localizedBaseChange G c).groupoid.objects.hom ≫ f =
      (localizedBaseChange G c).objectsProjection ≫ g)
    (a : Spec (.of (Localization.Away c')) ⟶ Spec (.of (Localization.Away c)))
    (ha : a ≫ invariantSpectrumMap G (Localization.Away c) =
      invariantSpectrumMap G (Localization.Away c')) :
    (localizedBaseChange G c').groupoid.objects.hom ≫ a ≫ f =
      (localizedBaseChange G c').objectsProjection ≫ g := by
  have hw : (localizedBaseChange G c').objectsProjection ≫ objectsToInvariantSpectrum G =
      ((localizedBaseChange G c').groupoid.objects.hom ≫ a) ≫
        invariantSpectrumMap G (Localization.Away c) := by
    rw [Category.assoc, ha]
    exact (localizedBaseChange G c').objects_isPullback.w
  obtain ⟨l, hl₁, hl₂⟩ : ∃ l, l ≫ (localizedBaseChange G c).objectsProjection =
        (localizedBaseChange G c').objectsProjection ∧
      l ≫ (localizedBaseChange G c).groupoid.objects.hom =
        (localizedBaseChange G c').groupoid.objects.hom ≫ a :=
    ⟨_, IsPullback.lift_fst (localizedBaseChange G c).objects_isPullback _ _ hw,
      IsPullback.lift_snd (localizedBaseChange G c).objects_isPullback _ _ hw⟩
  rw [← Category.assoc, ← hl₂, Category.assoc, hf, ← Category.assoc, hl₁]

/-- **Gluing the local factorizations.** Given principal opens `D(c_m)` covering `M` and, on each
of them, a factorization of `g` restricted to the object scheme of the localized groupoid, `g`
factors through `φ`. -/
theorem exists_comp_objectsToInvariantSpectrum_eq_of_local {T : Scheme.{u}}
    (g : G.objects.left ⟶ T)
    (c : Spec (.of (invariantRing G)) → invariantRing G)
    (hmc : ∀ m, m ∈ PrimeSpectrum.basicOpen (c m))
    (f : ∀ m, Spec (.of (Localization.Away (c m))) ⟶ T)
    (hf : ∀ m, (localizedBaseChange G (c m)).groupoid.objects.hom ≫ f m =
        (localizedBaseChange G (c m)).objectsProjection ≫ g) :
    ∃ h : Spec (.of (invariantRing G)) ⟶ T, objectsToInvariantSpectrum G ≫ h = g := by
  let 𝒰 := principalCover G c hmc
  have hglue : ∀ m m', pullback.fst (𝒰.f m) (𝒰.f m') ≫ f m = pullback.snd _ _ ≫ f m' := by
    intro m m'
    have : IsOpenImmersion (𝒰.f m) :=
      inferInstanceAs (IsOpenImmersion (invariantSpectrumMap G (Localization.Away (c m))))
    have : IsOpenImmersion (𝒰.f m') :=
      inferInstanceAs (IsOpenImmersion (invariantSpectrumMap G (Localization.Away (c m'))))
    refine ext_of_forall_localizedBaseChange G (pullback.fst (𝒰.f m) (𝒰.f m') ≫ 𝒰.f m) _ _
      fun c' e he => ?_
    have h₁ := objects_hom_comp_comp_eq_of_localizedBaseChange G g (f m) (hf m) (c' := c')
      (e ≫ pullback.fst _ _) ((Category.assoc _ _ _).trans he)
    have h₂ := objects_hom_comp_comp_eq_of_localizedBaseChange G g (f m') (hf m') (c' := c')
      (e ≫ pullback.snd _ _) ((Category.assoc _ _ _).trans
        ((congrArg (fun k => e ≫ k) pullback.condition.symm).trans he))
    erw [Category.assoc] at h₁ h₂
    exact h₁.trans h₂.symm
  refine ⟨𝒰.glueMorphisms f hglue, ?_⟩
  refine Scheme.Cover.hom_ext (localizedObjectsCover G c hmc) _ _ fun m => ?_
  change (localizedBaseChange G (c m)).objectsProjection ≫ objectsToInvariantSpectrum G ≫
      𝒰.glueMorphisms f hglue = (localizedBaseChange G (c m)).objectsProjection ≫ g
  rw [← Category.assoc, (localizedBaseChange G (c m)).objects_isPullback.w, Category.assoc]
  change (localizedBaseChange G (c m)).groupoid.objects.hom ≫ 𝒰.f m ≫
    𝒰.glueMorphisms f hglue = _
  exact (congrArg (fun k => (localizedBaseChange G (c m)).groupoid.objects.hom ≫ k)
    (Scheme.Cover.ι_glueMorphisms 𝒰 f hglue m)).trans (hf m)

/-- **`φ : U ⟶ M` is a categorical quotient in the category of schemes.** Every morphism from the
object scheme to a scheme which coequalizes the target and the source maps factors uniquely
through the canonical morphism to the spectrum of the invariant ring. -/
theorem existsUnique_comp_objectsToInvariantSpectrum_scheme {T : Scheme.{u}}
    (g : G.objects.left ⟶ T) (hg : G.target.left ≫ g = G.source.left ≫ g) :
    ∃! h : Spec (.of (invariantRing G)) ⟶ T, objectsToInvariantSpectrum G ≫ h = g := by
  classical
  have : UniversallyClosed (objectsToInvariantSpectrum G) :=
    universallyClosed_objectsToInvariantSpectrum G
  -- each point of `M` has a principal neighbourhood carried by `g` into one affine open
  have key : ∀ m : Spec (.of (invariantRing G)), ∃ (c : invariantRing G) (V : T.Opens),
      IsAffineOpen V ∧ m ∈ PrimeSpectrum.basicOpen c ∧
      ∀ x : G.objects.left, (objectsToInvariantSpectrum G).base x ∈ PrimeSpectrum.basicOpen c →
        g.base x ∈ V := by
    intro m
    obtain ⟨x₀, hx₀⟩ := surjective_objectsToInvariantSpectrum G m
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
      T.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (g.base x₀)) isOpen_univ
    have hZ : IsClosed ((objectsToInvariantSpectrum G).base '' (g.base ⁻¹' V)ᶜ) :=
      (objectsToInvariantSpectrum G).isClosedMap _
        (V.isOpen.preimage g.base.hom.continuous).isClosed_compl
    have hm : m ∉ (objectsToInvariantSpectrum G).base '' (g.base ⁻¹' V)ᶜ := by
      rintro ⟨z, hz, hzm⟩
      obtain ⟨r, hrt, hrs⟩ :=
        (base_objectsToInvariantSpectrum_eq_iff G z x₀).1 (hzm.trans hx₀.symm)
      apply hz
      change g.base z ∈ V
      rw [← hrt, ← Scheme.Hom.comp_apply, hg, Scheme.Hom.comp_apply, hrs]
      exact hxV
    obtain ⟨_, ⟨c, rfl⟩, hmc, hcZ⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hm hZ.isOpen_compl
    refine ⟨c, V, hV, hmc, fun x hx => ?_⟩
    by_contra hxV'
    exact hcZ hx ⟨x, hxV', rfl⟩
  choose c V hV hmc hcV using key
  -- the local factorizations
  have hloc : ∀ m, ∃ f : Spec (.of (Localization.Away (c m))) ⟶ T,
      (localizedBaseChange G (c m)).groupoid.objects.hom ≫ f =
        (localizedBaseChange G (c m)).objectsProjection ≫ g := by
    intro m
    refine exists_objects_hom_comp_eq G (localizedBaseChange G (c m)) (V m) (hV m) _ ?_ ?_
    · rintro _ ⟨z, rfl⟩
      rw [Scheme.Hom.comp_apply]
      apply hcV m
      rw [← Scheme.Hom.comp_apply, (localizedBaseChange G (c m)).objects_isPullback.w,
        Scheme.Hom.comp_apply]
      exact (range_invariantSpectrumMap_away G (c m)).le ⟨_, rfl⟩
    · rw [← Category.assoc, ← (localizedBaseChange G (c m)).projection_target, Category.assoc,
        hg, ← Category.assoc, (localizedBaseChange G (c m)).projection_source, Category.assoc]
  choose f hf using hloc
  obtain ⟨h, hh⟩ := exists_comp_objectsToInvariantSpectrum_eq_of_local G g c hmc f hf
  exact ⟨h, hh, fun h' hh' => ext_of_comp_objectsToInvariantSpectrum G _ _ (hh'.trans hh.symm)⟩

/-- **The descent of a morphism coequalizing the target and the source along `φ`**: the unique
morphism `M ⟶ T` through which it factors. -/
noncomputable def invariantSpectrumDescentMap {T : Scheme.{u}} (g : G.objects.left ⟶ T)
    (hg : G.target.left ≫ g = G.source.left ≫ g) : Spec (.of (invariantRing G)) ⟶ T :=
  (existsUnique_comp_objectsToInvariantSpectrum_scheme G g hg).exists.choose

/-- The composite of `φ` with `invariantSpectrumDescentMap G g hg` is `g`. -/
@[reassoc (attr := simp)]
theorem objectsToInvariantSpectrum_comp_invariantSpectrumDescentMap {T : Scheme.{u}}
    (g : G.objects.left ⟶ T) (hg : G.target.left ≫ g = G.source.left ≫ g) :
    objectsToInvariantSpectrum G ≫ invariantSpectrumDescentMap G g hg = g :=
  (existsUnique_comp_objectsToInvariantSpectrum_scheme G g hg).exists.choose_spec

omit [IsAffine G.objects.left] [IsAffine G.arrows.left] [IsFiniteLocallyFree G.source.left]
  [IsFiniteLocallyFree G.target.left] in
/-- The structure morphism of the object scheme coequalizes the target and the source. -/
theorem target_comp_objects_hom_eq_source_comp :
    G.target.left ≫ G.objects.hom = G.source.left ≫ G.objects.hom := by
  rw [Over.w G.target, Over.w G.source]

/-- **The spectrum of the invariant ring is a scheme over the base**: the structure morphism of
the object scheme descends along `φ`. -/
noncomputable def invariantSpectrumToBase : Spec (.of (invariantRing G)) ⟶ S :=
  invariantSpectrumDescentMap G G.objects.hom (target_comp_objects_hom_eq_source_comp G)

/-- The composite of `φ` with `invariantSpectrumToBase G` is the structure morphism of the object
scheme. -/
@[reassoc (attr := simp)]
theorem objectsToInvariantSpectrum_comp_invariantSpectrumToBase :
    objectsToInvariantSpectrum G ≫ invariantSpectrumToBase G = G.objects.hom :=
  objectsToInvariantSpectrum_comp_invariantSpectrumDescentMap G _ _

end Quotient

end AlgebraicGeometry.GroupoidScheme

end
