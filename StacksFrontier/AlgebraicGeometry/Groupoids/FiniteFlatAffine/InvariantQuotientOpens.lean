module

public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.InvariantQuotientSchemes

/-!
# The invariant quotient over an open of the invariant spectrum

Let `G = (U, R, s, t, c)` be a groupoid scheme with `U` and `R` affine and `s, t` finite locally
free, with ring of invariants `C` and quotient map `φ : U ⟶ M = Spec C`. For an open `X ⊆ M` with
inverse image `P = φ⁻¹(X) ⊆ U`, the restriction `φ_X : P ⟶ X` is a categorical quotient in the
category of schemes: every morphism `g : P ⟶ T` to a scheme which is invariant — it coequalizes
the source and target maps on the arrows with source in `P` — factors uniquely through `φ_X`.

For `X = M` this is
`AlgebraicGeometry.GroupoidScheme.existsUnique_comp_objectsToInvariantSpectrum_scheme`.

## Main results

* `AlgebraicGeometry.GroupoidScheme.existsUnique_quotientRestrict_comp`: `φ_X` is a categorical
  quotient in the category of schemes.
* `AlgebraicGeometry.GroupoidScheme.quotientRestrict_ext`: `φ_X` is an epimorphism of schemes.
* `AlgebraicGeometry.GroupoidScheme.quotientRestrict_surjective`: `φ_X` is surjective.

## References

* [Stacks Project, Tag 0DUS](https://stacks.math.columbia.edu/tag/0DUS)
* [Stacks Project, Tag 03BK](https://stacks.math.columbia.edu/tag/03BK)
* [Stacks Project, Tag 03BL](https://stacks.math.columbia.edu/tag/03BL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids Stacks.Morphisms

universe u

namespace AlgebraicGeometry.GroupoidScheme

section Definitions

variable {S : Scheme.{u}} (G : GroupoidScheme S) (X : (Spec (.of (invariantRing G))).Opens)

/-- The inverse image `φ⁻¹(X)` in the object scheme. -/
abbrev quotientPreimage : G.objects.left.Opens := objectsToInvariantSpectrum G ⁻¹ᵁ X

/-- The arrows whose source lies in `φ⁻¹(X)`. -/
abbrev quotientPreimageArrows : G.arrows.left.Opens := G.source.left ⁻¹ᵁ quotientPreimage G X

/-- The target of an arrow with source in `φ⁻¹(X)` also lies in `φ⁻¹(X)`. -/
theorem quotientPreimageArrows_le_target :
    quotientPreimageArrows G X ≤ G.target.left ⁻¹ᵁ quotientPreimage G X := by
  intro r hr
  change (objectsToInvariantSpectrum G) (G.target.left r) ∈ X
  rw [← Scheme.Hom.comp_apply, target_comp_objectsToInvariantSpectrum, Scheme.Hom.comp_apply]
  exact hr

/-- The source map on the arrows with source in `φ⁻¹(X)`. -/
abbrev quotientPreimageSource :
    (quotientPreimageArrows G X).toScheme ⟶ (quotientPreimage G X).toScheme :=
  G.source.left.resLE _ _ le_rfl

/-- The target map on the arrows with source in `φ⁻¹(X)`. -/
abbrev quotientPreimageTarget :
    (quotientPreimageArrows G X).toScheme ⟶ (quotientPreimage G X).toScheme :=
  G.target.left.resLE _ _ (quotientPreimageArrows_le_target G X)

/-- The restriction `φ_X : φ⁻¹(X) ⟶ X` of the quotient map. -/
abbrev quotientRestrict :
    (quotientPreimage G X).toScheme ⟶ X.toScheme :=
  (objectsToInvariantSpectrum G).resLE X _ le_rfl

end Definitions

variable {S : Scheme.{u}} (G : GroupoidScheme S)
  [IsAffine G.objects.left] [IsAffine G.arrows.left]
  [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left]
  (X : (Spec (.of (invariantRing G))).Opens)

/-- For a principal open `D(c)` contained in `X`, the object scheme of the localization of `G` at
`c` lands in `φ⁻¹(X)`. -/
theorem range_objectsProjection_subset (c : invariantRing G)
    (hc : Set.range (invariantSpectrumMap G (Localization.Away c)) ⊆ (X : Set _)) :
    Set.range (localizedBaseChange G c).objectsProjection ⊆ (quotientPreimage G X : Set _) := by
  rintro _ ⟨y, rfl⟩
  change objectsToInvariantSpectrum G ((localizedBaseChange G c).objectsProjection y) ∈ X
  rw [← Scheme.Hom.comp_apply, (localizedBaseChange G c).objects_isPullback.w,
    Scheme.Hom.comp_apply]
  exact hc ⟨_, rfl⟩

/-- The projection of the object scheme of the localization at `c` into `φ⁻¹(X)`, for
`D(c) ⊆ X`. -/
abbrev localizedLift (c : invariantRing G)
    (hc : Set.range (invariantSpectrumMap G (Localization.Away c)) ⊆ (X : Set _)) :
    (localizedBaseChange G c).groupoid.objects.left ⟶ (quotientPreimage G X).toScheme :=
  IsOpenImmersion.lift (quotientPreimage G X).ι (localizedBaseChange G c).objectsProjection
    (by rw [Scheme.Opens.range_ι]; exact range_objectsProjection_subset G X c hc)

/-- The localized lift followed by the inclusion of `φ⁻¹(X)` is the projection of the localized
object scheme to `U`. -/
theorem localizedLift_ι (c : invariantRing G)
    (hc : Set.range (invariantSpectrumMap G (Localization.Away c)) ⊆ (X : Set _)) :
    localizedLift G X c hc ≫ (quotientPreimage G X).ι =
      (localizedBaseChange G c).objectsProjection :=
  IsOpenImmersion.lift_fac _ _ _

/-- The arrow scheme of the localization at `c` lands in the arrows with source in `φ⁻¹(X)`. -/
theorem range_arrowsProjection_subset (c : invariantRing G)
    (hc : Set.range (invariantSpectrumMap G (Localization.Away c)) ⊆ (X : Set _)) :
    Set.range (localizedBaseChange G c).arrowsProjection ⊆
      (quotientPreimageArrows G X : Set _) := by
  rintro _ ⟨y, rfl⟩
  change G.source.left ((localizedBaseChange G c).arrowsProjection y) ∈ quotientPreimage G X
  rw [← Scheme.Hom.comp_apply, (localizedBaseChange G c).projection_source, Scheme.Hom.comp_apply]
  exact range_objectsProjection_subset G X c hc ⟨_, rfl⟩

variable {X} in
/-- **The localized lifts of an invariant morphism are invariant.** -/
theorem localizedLift_comp_invariant {T : Scheme.{u}} (g : (quotientPreimage G X).toScheme ⟶ T)
    (hg : quotientPreimageTarget G X ≫ g = quotientPreimageSource G X ≫ g) (c : invariantRing G)
    (hc : Set.range (invariantSpectrumMap G (Localization.Away c)) ⊆ (X : Set _)) :
    (localizedBaseChange G c).groupoid.target.left ≫ localizedLift G X c hc ≫ g =
      (localizedBaseChange G c).groupoid.source.left ≫ localizedLift G X c hc ≫ g := by
  let a : (localizedBaseChange G c).groupoid.arrows.left ⟶
      (quotientPreimageArrows G X).toScheme :=
    IsOpenImmersion.lift (quotientPreimageArrows G X).ι (localizedBaseChange G c).arrowsProjection
      (by rw [Scheme.Opens.range_ι]; exact range_arrowsProjection_subset G X c hc)
  have ha : a ≫ (quotientPreimageArrows G X).ι = (localizedBaseChange G c).arrowsProjection :=
    IsOpenImmersion.lift_fac _ _ _
  clear_value a
  have ht : (localizedBaseChange G c).groupoid.target.left ≫ localizedLift G X c hc =
      a ≫ quotientPreimageTarget G X := by
    refine (cancel_mono (quotientPreimage G X).ι).1 ?_
    have e1 : quotientPreimageTarget G X ≫ (quotientPreimage G X).ι =
        (quotientPreimageArrows G X).ι ≫ G.target.left := Scheme.Hom.resLE_comp_ι _ _
    rw [Category.assoc, localizedLift_ι, Category.assoc, e1, ← Category.assoc, ha]
    exact (localizedBaseChange G c).projection_target.symm
  have hs : (localizedBaseChange G c).groupoid.source.left ≫ localizedLift G X c hc =
      a ≫ quotientPreimageSource G X := by
    refine (cancel_mono (quotientPreimage G X).ι).1 ?_
    have e1 : quotientPreimageSource G X ≫ (quotientPreimage G X).ι =
        (quotientPreimageArrows G X).ι ≫ G.source.left := Scheme.Hom.resLE_comp_ι _ _
    rw [Category.assoc, localizedLift_ι, Category.assoc, e1, ← Category.assoc]
    exact ((congrArg (· ≫ G.source.left) ha).trans
      (localizedBaseChange G c).projection_source).symm
  calc (localizedBaseChange G c).groupoid.target.left ≫ localizedLift G X c hc ≫ g
      = ((localizedBaseChange G c).groupoid.target.left ≫ localizedLift G X c hc) ≫ g :=
        (Category.assoc _ _ _).symm
    _ = (a ≫ quotientPreimageTarget G X) ≫ g := congrArg (· ≫ g) ht
    _ = a ≫ (quotientPreimageTarget G X ≫ g) := Category.assoc _ _ _
    _ = a ≫ (quotientPreimageSource G X ≫ g) := congrArg (a ≫ ·) hg
    _ = (a ≫ quotientPreimageSource G X) ≫ g := (Category.assoc _ _ _).symm
    _ = ((localizedBaseChange G c).groupoid.source.left ≫ localizedLift G X c hc) ≫ g :=
        congrArg (· ≫ g) hs.symm
    _ = _ := Category.assoc _ _ _

variable {X} in
/-- **Local factorization.** Every point of `X` lies in a principal open `D(c) ⊆ X` over which an
invariant morphism `g : φ⁻¹(X) ⟶ T` factors through `Spec C_c`. -/
theorem exists_localized_factorization {T : Scheme.{u}} (g : (quotientPreimage G X).toScheme ⟶ T)
    (hg : quotientPreimageTarget G X ≫ g = quotientPreimageSource G X ≫ g) (m : X.toScheme) :
    ∃ (c : invariantRing G)
      (hc : Set.range (invariantSpectrumMap G (Localization.Away c)) ⊆ (X : Set _)),
      X.ι m ∈ Set.range (invariantSpectrumMap G (Localization.Away c)) ∧
      ∃ f : Spec (.of (Localization.Away c)) ⟶ T,
        (localizedBaseChange G c).groupoid.objects.hom ≫ f = localizedLift G X c hc ≫ g := by
  classical
  have : UniversallyClosed (objectsToInvariantSpectrum G) :=
    universallyClosed_objectsToInvariantSpectrum G
  obtain ⟨x₀, hx₀⟩ := surjective_objectsToInvariantSpectrum G (X.ι m)
  have hx₀P : x₀ ∈ quotientPreimage G X := by
    change objectsToInvariantSpectrum G x₀ ∈ X
    rw [hx₀]
    exact (Scheme.Opens.range_ι X).le ⟨m, rfl⟩
  let x₀' : (quotientPreimage G X).toScheme := ⟨x₀, hx₀P⟩
  have hx₀' : (quotientPreimage G X).ι x₀' = x₀ := rfl
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    T.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (g x₀')) isOpen_univ
  let Z : Set G.objects.left := (quotientPreimage G X).ι '' (g ⁻¹' (V : Set T))
  have hZ : IsOpen Z :=
    (quotientPreimage G X).ι.isOpenEmbedding.isOpenMap _ (V.isOpen.preimage g.continuous)
  have hW : IsClosed ((objectsToInvariantSpectrum G) '' Zᶜ) :=
    (objectsToInvariantSpectrum G).isClosedMap _ hZ.isClosed_compl
  have hm : X.ι m ∉ (objectsToInvariantSpectrum G) '' Zᶜ := by
    rintro ⟨z, hz, hzm⟩
    obtain ⟨r, hrt, hrs⟩ := (base_objectsToInvariantSpectrum_eq_iff G z x₀).1 (hzm.trans hx₀.symm)
    have hrA : r ∈ quotientPreimageArrows G X := by
      change G.source.left r ∈ quotientPreimage G X
      rw [hrs]
      exact hx₀P
    let r' : (quotientPreimageArrows G X).toScheme := ⟨r, hrA⟩
    have h1 : (quotientPreimageTarget G X ≫ g) r' = (quotientPreimageSource G X ≫ g) r' := by
      rw [hg]
    have hsr : quotientPreimageSource G X r' = x₀' := by
      apply (quotientPreimage G X).ι.isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, Scheme.Hom.resLE_comp_ι, Scheme.Hom.comp_apply]
      exact hrs
    have htr : (quotientPreimage G X).ι (quotientPreimageTarget G X r') = z := by
      rw [← Scheme.Hom.comp_apply, Scheme.Hom.resLE_comp_ι, Scheme.Hom.comp_apply]
      exact hrt
    apply hz
    refine ⟨quotientPreimageTarget G X r', ?_, htr⟩
    change g (quotientPreimageTarget G X r') ∈ V
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hsr] at h1
    rw [h1]
    exact hxV
  have hopen : IsOpen ((X : Set (Spec (.of (invariantRing G)))) ∩
      ((objectsToInvariantSpectrum G) '' Zᶜ)ᶜ) :=
    X.isOpen.inter hW.isOpen_compl
  have hmem : X.ι m ∈ (X : Set (Spec (.of (invariantRing G)))) ∩
      ((objectsToInvariantSpectrum G) '' Zᶜ)ᶜ := ⟨(Scheme.Opens.range_ι X).le ⟨m, rfl⟩, hm⟩
  obtain ⟨_, ⟨c, rfl⟩, hmc, hcO⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hmem hopen
  have hrange := range_invariantSpectrumMap_away G c
  have hc : Set.range (invariantSpectrumMap G (Localization.Away c)) ⊆ (X : Set _) := by
    rw [hrange]
    exact fun y hy => (hcO hy).1
  refine ⟨c, hc, by rw [hrange]; exact hmc, ?_⟩
  refine exists_objects_hom_comp_eq G (localizedBaseChange G c) V hV _ ?_
    (localizedLift_comp_invariant G g hg c hc)
  rintro _ ⟨y, rfl⟩
  rw [Scheme.Hom.comp_apply]
  have hy : objectsToInvariantSpectrum G ((quotientPreimage G X).ι (localizedLift G X c hc y)) ∈
      ((objectsToInvariantSpectrum G) '' Zᶜ)ᶜ := by
    have key : localizedLift G X c hc ≫ (quotientPreimage G X).ι ≫ objectsToInvariantSpectrum G =
        (localizedBaseChange G c).groupoid.objects.hom ≫
          invariantSpectrumMap G (Localization.Away c) := by
      rw [← Category.assoc, localizedLift_ι, (localizedBaseChange G c).objects_isPullback.w]
    have := congrArg (fun k => k y) key
    simp only [Scheme.Hom.comp_apply] at this
    rw [this]
    have hmemc : (invariantSpectrumMap G (Localization.Away c))
        ((localizedBaseChange G c).groupoid.objects.hom y) ∈
          Set.range (invariantSpectrumMap G (Localization.Away c)) := ⟨_, rfl⟩
    rw [hrange] at hmemc
    exact (hcO hmemc).2
  have hyZ : (quotientPreimage G X).ι (localizedLift G X c hc y) ∈ Z := by
    by_contra hn
    exact hy ⟨_, hn, rfl⟩
  obtain ⟨p, hp, hpe⟩ := hyZ
  rw [← (quotientPreimage G X).ι.isOpenEmbedding.injective hpe]
  exact hp

/-- Over `M`, the localized lift followed by the restricted quotient map is the structure map of
the localized object scheme followed by the inclusion of `D(c)` into `X`. -/
theorem localizedLift_comp_quotientRestrict (c : invariantRing G)
    (hc : Set.range (invariantSpectrumMap G (Localization.Away c)) ⊆ (X : Set _))
    (e : Spec (.of (Localization.Away c)) ⟶ X.toScheme)
    (he : e ≫ X.ι = invariantSpectrumMap G (Localization.Away c)) :
    localizedLift G X c hc ≫ quotientRestrict G X =
      (localizedBaseChange G c).groupoid.objects.hom ≫ e := by
  refine (cancel_mono X.ι).1 ?_
  rw [Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc, localizedLift_ι,
    Category.assoc, he, (localizedBaseChange G c).objects_isPullback.w]

variable {X} in
/-- **Compatibility of local factorizations.** A factorization over `D(c) ⊆ X` of an invariant
morphism on `φ⁻¹(X)`, composed with a morphism `Spec C_{c'} ⟶ Spec C_c` over `M`, is a
factorization over `D(c')`. -/
theorem localized_factorization_compat {T : Scheme.{u}} (g : (quotientPreimage G X).toScheme ⟶ T)
    (c c' : invariantRing G)
    (hc : Set.range (invariantSpectrumMap G (Localization.Away c)) ⊆ (X : Set _))
    (hc' : Set.range (invariantSpectrumMap G (Localization.Away c')) ⊆ (X : Set _))
    (f : Spec (.of (Localization.Away c)) ⟶ T)
    (hf : (localizedBaseChange G c).groupoid.objects.hom ≫ f = localizedLift G X c hc ≫ g)
    (a : Spec (.of (Localization.Away c')) ⟶ Spec (.of (Localization.Away c)))
    (ha : a ≫ invariantSpectrumMap G (Localization.Away c) =
      invariantSpectrumMap G (Localization.Away c')) :
    (localizedBaseChange G c').groupoid.objects.hom ≫ a ≫ f = localizedLift G X c' hc' ≫ g := by
  have hw : (localizedBaseChange G c').objectsProjection ≫ objectsToInvariantSpectrum G =
      ((localizedBaseChange G c').groupoid.objects.hom ≫ a) ≫
        invariantSpectrumMap G (Localization.Away c) := by
    rw [Category.assoc, ha]
    exact (localizedBaseChange G c').objects_isPullback.w
  obtain ⟨l, hl₁, hl₂⟩ : ∃ l, l ≫ (localizedBaseChange G c).objectsProjection =
        (localizedBaseChange G c').objectsProjection ∧
      l ≫ (localizedBaseChange G c).groupoid.objects.hom =
        (localizedBaseChange G c').groupoid.objects.hom ≫ a :=
    ⟨_, (localizedBaseChange G c).objects_isPullback.lift_fst _ _ hw,
      (localizedBaseChange G c).objects_isPullback.lift_snd _ _ hw⟩
  have hll : l ≫ localizedLift G X c hc = localizedLift G X c' hc' := by
    refine (cancel_mono (quotientPreimage G X).ι).1 ?_
    rw [Category.assoc, localizedLift_ι, localizedLift_ι, hl₁]
  rw [← Category.assoc, ← hl₂, Category.assoc, hf, ← Category.assoc, hll]

variable {X} in
/-- **Uniqueness of factorizations through an open of `M` inside `X`.** Two morphisms out of an
open subscheme of `X` agree as soon as, for every principal open `D(c) ⊆ X` mapping into it over
`M`, their composites with the localized object scheme are both the localized lift followed by
`g`. -/
theorem eq_of_localized_factorizations {T : Scheme.{u}} (g : (quotientPreimage G X).toScheme ⟶ T)
    {Y : Scheme.{u}} (j : Y ⟶ Spec (.of (invariantRing G))) [IsOpenImmersion j]
    (hj : Set.range j ⊆ (X : Set _)) (k₁ k₂ : Y ⟶ T)
    (h : ∀ (c : invariantRing G) (e : Spec (.of (Localization.Away c)) ⟶ Y)
      (hc : Set.range (invariantSpectrumMap G (Localization.Away c)) ⊆ (X : Set _)),
      e ≫ j = invariantSpectrumMap G (Localization.Away c) →
        (localizedBaseChange G c).groupoid.objects.hom ≫ e ≫ k₁ = localizedLift G X c hc ≫ g ∧
        (localizedBaseChange G c).groupoid.objects.hom ≫ e ≫ k₂ = localizedLift G X c hc ≫ g) :
    k₁ = k₂ := by
  refine ext_of_forall_localizedBaseChange G j k₁ k₂ fun c e he => ?_
  have hc : Set.range (invariantSpectrumMap G (Localization.Away c)) ⊆ (X : Set _) := by
    rw [← he]
    rintro _ ⟨y, rfl⟩
    exact hj ⟨e y, rfl⟩
  obtain ⟨h₁, h₂⟩ := h c e hc he
  exact h₁.trans h₂.symm

variable {X} in
/-- **The restricted quotient map is a categorical quotient in the category of schemes.** For an
open `X` of `M = Spec C`, every morphism `g : φ⁻¹(X) ⟶ T` to a scheme which coequalizes the
target and the source maps on the arrows with source in `φ⁻¹(X)` factors uniquely through
`φ_X : φ⁻¹(X) ⟶ X`. -/
theorem existsUnique_quotientRestrict_comp {T : Scheme.{u}}
    (g : (quotientPreimage G X).toScheme ⟶ T)
    (hg : quotientPreimageTarget G X ≫ g = quotientPreimageSource G X ≫ g) :
    ∃! h : X.toScheme ⟶ T, quotientRestrict G X ≫ h = g := by
  classical
  choose c hc hmc f hf using exists_localized_factorization G g hg
  have hlift : ∀ m, ∃ e : Spec (.of (Localization.Away (c m))) ⟶ X.toScheme,
      e ≫ X.ι = invariantSpectrumMap G (Localization.Away (c m)) := fun m =>
    ⟨IsOpenImmersion.lift X.ι _ (by rw [Scheme.Opens.range_ι]; exact hc m),
      IsOpenImmersion.lift_fac _ _ _⟩
  choose e he using hlift
  have heo : ∀ m, IsOpenImmersion (e m) := fun m => by
    have : IsOpenImmersion (e m ≫ X.ι) := by rw [he m]; infer_instance
    exact IsOpenImmersion.of_comp (e m) X.ι
  have hcov : ∀ x : X.toScheme, ∃ m y, e m y = x := by
    intro x
    obtain ⟨y, hy⟩ := hmc x
    refine ⟨x, y, X.ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, he x]
    exact hy
  let 𝒱 : X.toScheme.OpenCover :=
    Scheme.Cover.mkOfCovers X.toScheme (fun m => Spec (.of (Localization.Away (c m)))) e
      hcov heo
  have hglue : ∀ m m' : X.toScheme,
      pullback.fst (e m) (e m') ≫ f m = pullback.snd (e m) (e m') ≫ f m' := by
    intro m m'
    have := heo m
    have := heo m'
    refine eq_of_localized_factorizations G g (pullback.fst (e m) (e m') ≫ e m ≫ X.ι) ?_ _ _
      fun c' e' hc' he' => ⟨?_, ?_⟩
    · rintro _ ⟨y, rfl⟩
      exact (Scheme.Opens.range_ι X).le ⟨_, rfl⟩
    · have := localized_factorization_compat G g (c m) c' (hc m) hc' (f m) (hf m)
        (e' ≫ pullback.fst (e m) (e m')) (by rw [Category.assoc, ← he m, ← he'])
      simpa only [Category.assoc] using this
    · have := localized_factorization_compat G g (c m') c' (hc m') hc' (f m') (hf m')
        (e' ≫ pullback.snd (e m) (e m')) (by
          rw [Category.assoc, ← he m', ← he', ← pullback.condition_assoc])
      simpa only [Category.assoc] using this
  obtain ⟨H, hι⟩ : ∃ H : X.toScheme ⟶ T, ∀ m, e m ≫ H = f m :=
    ⟨𝒱.glueMorphisms f hglue, fun m => Scheme.Cover.ι_glueMorphisms 𝒱 f hglue m⟩
  clear_value 𝒱
  have hcovP : ∀ p : (quotientPreimage G X).toScheme,
      ∃ m y, localizedLift G X (c m) (hc m) y = p := by
    intro p
    let m := quotientRestrict G X p
    obtain ⟨z, hz⟩ := hmc m
    have hp := congrArg (fun k => k p)
      (Scheme.Hom.resLE_comp_ι (objectsToInvariantSpectrum G) (le_rfl :
        quotientPreimage G X ≤ objectsToInvariantSpectrum G ⁻¹ᵁ X))
    simp only [Scheme.Hom.comp_apply] at hp
    have hzp : (objectsToInvariantSpectrum G) ((quotientPreimage G X).ι p) =
        (invariantSpectrumMap G (Localization.Away (c m))) z := hp.symm.trans hz.symm
    obtain ⟨w, hw, -⟩ := exists_objects_point G (localizedBaseChange G (c m)) _ z hzp
    refine ⟨m, w, (quotientPreimage G X).ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, localizedLift_ι]
    exact hw
  have hℓo : ∀ m, IsOpenImmersion (localizedLift G X (c m) (hc m)) := fun m => by
    have : IsOpenImmersion (localizedBaseChange G (c m)).objectsProjection :=
      MorphismProperty.of_isPullback (localizedBaseChange G (c m)).objects_isPullback.flip
        inferInstance
    have : IsOpenImmersion (localizedLift G X (c m) (hc m) ≫ (quotientPreimage G X).ι) := by
      rw [localizedLift_ι]; infer_instance
    exact IsOpenImmersion.of_comp _ (quotientPreimage G X).ι
  let 𝒲 : (quotientPreimage G X).toScheme.OpenCover :=
    Scheme.Cover.mkOfCovers _ (fun m => (localizedBaseChange G (c m)).groupoid.objects.left)
      (fun m => localizedLift G X (c m) (hc m)) hcovP hℓo
  have hex : quotientRestrict G X ≫ H = g := by
    refine Scheme.Cover.hom_ext 𝒲 _ _ fun m => ?_
    change localizedLift G X (c m) (hc m) ≫ quotientRestrict G X ≫ H =
      localizedLift G X (c m) (hc m) ≫ g
    rw [← Category.assoc, localizedLift_comp_quotientRestrict G X (c m) (hc m) (e m) (he m),
      Category.assoc, hι m, hf m]
  refine ⟨H, hex, fun h hh => ?_⟩
  refine eq_of_localized_factorizations G g X.ι (Scheme.Opens.range_ι X).le h _
    fun c' e' hc' he' => ⟨?_, ?_⟩
  · calc _ = ((localizedBaseChange G c').groupoid.objects.hom ≫ e') ≫ h :=
          (Category.assoc _ _ _).symm
      _ = (localizedLift G X c' hc' ≫ quotientRestrict G X) ≫ h :=
          congrArg (· ≫ h) (localizedLift_comp_quotientRestrict G X c' hc' e' he').symm
      _ = _ := (Category.assoc _ _ _).trans (congrArg (localizedLift G X c' hc' ≫ ·) hh)
  · calc _ = ((localizedBaseChange G c').groupoid.objects.hom ≫ e') ≫ H :=
          (Category.assoc _ _ _).symm
      _ = (localizedLift G X c' hc' ≫ quotientRestrict G X) ≫ H :=
          congrArg (· ≫ H) (localizedLift_comp_quotientRestrict G X c' hc' e' he').symm
      _ = _ := (Category.assoc _ _ _).trans (congrArg (localizedLift G X c' hc' ≫ ·) hex)

omit [IsAffine G.objects.left] [IsAffine G.arrows.left]
  [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left] in
/-- The restricted quotient map coequalizes the restricted target and source maps. -/
theorem quotientPreimageTarget_comp_quotientRestrict :
    quotientPreimageTarget G X ≫ quotientRestrict G X =
      quotientPreimageSource G X ≫ quotientRestrict G X := by
  refine (cancel_mono X.ι).1 ?_
  have e1 : quotientRestrict G X ≫ X.ι = (quotientPreimage G X).ι ≫ objectsToInvariantSpectrum G :=
    Scheme.Hom.resLE_comp_ι _ _
  have e2 : quotientPreimageTarget G X ≫ (quotientPreimage G X).ι =
      (quotientPreimageArrows G X).ι ≫ G.target.left := Scheme.Hom.resLE_comp_ι _ _
  have e3 : quotientPreimageSource G X ≫ (quotientPreimage G X).ι =
      (quotientPreimageArrows G X).ι ≫ G.source.left := Scheme.Hom.resLE_comp_ι _ _
  rw [Category.assoc, Category.assoc, e1, ← Category.assoc, e2, ← Category.assoc, e3,
    Category.assoc, Category.assoc, target_comp_objectsToInvariantSpectrum]

variable {X} in
/-- **The restricted quotient map is an epimorphism of schemes.** -/
theorem quotientRestrict_ext {T : Scheme.{u}} (h₁ h₂ : X.toScheme ⟶ T)
    (h : quotientRestrict G X ≫ h₁ = quotientRestrict G X ≫ h₂) : h₁ = h₂ := by
  have hg : quotientPreimageTarget G X ≫ quotientRestrict G X ≫ h₁ =
      quotientPreimageSource G X ≫ quotientRestrict G X ≫ h₁ := by
    rw [← Category.assoc, quotientPreimageTarget_comp_quotientRestrict, Category.assoc]
  exact (existsUnique_quotientRestrict_comp G _ hg).unique rfl h.symm

/-- The restricted quotient map is surjective. -/
theorem quotientRestrict_surjective : Function.Surjective (quotientRestrict G X) := by
  intro m
  obtain ⟨x, hx⟩ := surjective_objectsToInvariantSpectrum G (X.ι m)
  have hxP : x ∈ quotientPreimage G X := by
    change objectsToInvariantSpectrum G x ∈ X
    rw [hx]
    exact (Scheme.Opens.range_ι X).le ⟨m, rfl⟩
  let p : (quotientPreimage G X).toScheme := ⟨x, hxP⟩
  refine ⟨p, X.ι.isOpenEmbedding.injective ?_⟩
  have e := congrArg (fun k => k p) (Scheme.Hom.resLE_comp_ι (objectsToInvariantSpectrum G)
    (le_rfl : quotientPreimage G X ≤ objectsToInvariantSpectrum G ⁻¹ᵁ X))
  simp only [Scheme.Hom.comp_apply] at e
  exact e.trans hx

end AlgebraicGeometry.GroupoidScheme

end
