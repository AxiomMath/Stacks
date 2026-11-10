module

public import StacksFrontier.AlgebraicGeometry.Thickenings.Existence.Affine

/-!
# Existence of the universal first-order thickening: charts and overlaps

This file continues the construction of the universal first-order thickening of a formally
unramified morphism `h : Z ⟶ X`: lifts against arbitrary first-order thickenings for the affine
construction, the affine charts of `Z` over affine opens of `X` and their thickenings, the
canonical isomorphism between two universal first-order thickenings, and the restrictions of the
chosen thickenings of the charts to the double and triple overlaps of an open cover.

## References

* [Stacks Project, Tag 04F3](https://stacks.math.columbia.edu/tag/04F3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Thickenings

/-- Unique lifting of `affineThickeningSkeleton` against the base change of a first-order
thickening along an open immersion from an affine scheme. -/
private lemma affineThickeningSkeleton_existsUnique_lift_pullback
    {Z X T T' Y : Scheme.{u}} [IsAffine Z] [IsAffine X] [IsAffine Y]
    (h : Z ⟶ X) [FormallyUnramified h]
    (j : T ⟶ T') (hj : IsFirstOrderThickening j)
    (a : T ⟶ Z) (b : T' ⟶ X) (hab : j ≫ b = a ≫ h) (g : Y ⟶ T') [IsOpenImmersion g] :
    ∃! f : Y ⟶ (affineThickeningSkeleton h).ambient,
      pullback.fst g j ≫ f = pullback.snd g j ≫ a ≫ (affineThickeningSkeleton h).inclusion ∧
        f ≫ (affineThickeningSkeleton h).toBase = g ≫ b := by
  have : IsClosedImmersion j := hj.1
  have : IsAffine (pullback g j) := isAffine_of_isAffineHom (pullback.fst g j)
  have hq : IsFirstOrderThickening (pullback.fst g j) := by
    refine ⟨inferInstance, ?_⟩
    rw [Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
    exact comap_sq_eq_bot_of_isOpenImmersion j.ker g hj.2
  refine affineThickeningSkeleton_existsUnique_lift_of_isAffine h (pullback.fst g j) hq
    (pullback.snd g j ≫ a) (g ≫ b) ?_
  rw [pullback.condition_assoc, hab, Category.assoc]

/-- `affineThickeningSkeleton` has the unique lifting property against *arbitrary* first-order
thickenings, not just affine ones: the lift is built on an affine open cover of the test
thickening and glued, using uniqueness on overlaps. -/
private lemma affineThickeningSkeleton_existsUnique_lift
    {Z X T T' : Scheme.{u}} [IsAffine Z] [IsAffine X]
    (h : Z ⟶ X) [FormallyUnramified h]
    (j : T ⟶ T') (hj : IsFirstOrderThickening j)
    (a : T ⟶ Z) (b : T' ⟶ X) (hab : j ≫ b = a ≫ h) :
    ∃! f : T' ⟶ (affineThickeningSkeleton h).ambient,
      (j ≫ f = a ≫ (affineThickeningSkeleton h).inclusion) ∧
      (f ≫ (affineThickeningSkeleton h).toBase = b) := by
  classical
  let H := affineThickeningSkeleton h
  let 𝒰 := T'.affineCover
  have localLift (k : 𝒰.I₀) : ∃! f : 𝒰.X k ⟶ H.ambient,
      pullback.fst (𝒰.f k) j ≫ f = pullback.snd (𝒰.f k) j ≫ a ≫ H.inclusion ∧
        f ≫ H.toBase = 𝒰.f k ≫ b :=
    affineThickeningSkeleton_existsUnique_lift_pullback h j hj a b hab (𝒰.f k)
  let lift (k : 𝒰.I₀) : 𝒰.X k ⟶ H.ambient :=
    Classical.choose (localLift k).exists
  have lift_spec (k : 𝒰.I₀) :
      pullback.fst (𝒰.f k) j ≫ lift k = pullback.snd (𝒰.f k) j ≫ a ≫ H.inclusion ∧
        lift k ≫ H.toBase = 𝒰.f k ≫ b := Classical.choose_spec (localLift k).exists
  -- `lift k` restricted along any `c : Y ⟶ 𝒰.X k` is a solution of the lifting problem for `b₀`
  have restrict_lift (k : 𝒰.I₀) {Y : Scheme.{u}} (c : Y ⟶ 𝒰.X k) (b₀ : Y ⟶ T')
      (hc : c ≫ 𝒰.f k = b₀) :
      pullback.fst b₀ j ≫ c ≫ lift k = pullback.snd b₀ j ≫ a ≫ H.inclusion ∧
        (c ≫ lift k) ≫ H.toBase = b₀ ≫ b := by
    subst hc
    refine ⟨?_, by rw [Category.assoc, (lift_spec k).2, Category.assoc]⟩
    let α : pullback (c ≫ 𝒰.f k) j ⟶ pullback (𝒰.f k) j :=
      pullback.lift (pullback.fst _ j ≫ c) (pullback.snd _ j) (by simp [pullback.condition])
    simpa only [α, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.assoc] using
      α ≫= (lift_spec k).1
  have compatible (k l : 𝒰.I₀) :
      pullback.fst (𝒰.f k) (𝒰.f l) ≫ lift k =
        pullback.snd (𝒰.f k) (𝒰.f l) ≫ lift l := by
    apply (pullback (𝒰.f k) (𝒰.f l)).affineCover.hom_ext
    intro m
    let w := (pullback (𝒰.f k) (𝒰.f l)).affineCover.f m
    obtain ⟨_, _, hu⟩ := affineThickeningSkeleton_existsUnique_lift_pullback h j hj a b hab
      (w ≫ pullback.fst (𝒰.f k) (𝒰.f l) ≫ 𝒰.f k)
    have h₁ := hu _ (restrict_lift k (w ≫ pullback.fst (𝒰.f k) (𝒰.f l)) _ (by simp))
    have h₂ := hu _ (restrict_lift l (w ≫ pullback.snd (𝒰.f k) (𝒰.f l)) _
      (by simp [pullback.condition]))
    simpa only [Category.assoc] using h₁.trans h₂.symm
  let f := 𝒰.glueMorphisms lift compatible
  have hf : j ≫ f = a ≫ H.inclusion := by
    let 𝒯 : T.OpenCover := Scheme.Cover.mkOfCovers 𝒰.I₀
      (fun k => pullback j (𝒰.f k)) (fun k => pullback.fst j (𝒰.f k)) (by
        intro t
        obtain ⟨k, y, hy⟩ := 𝒰.exists_eq (j t)
        obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback t y hy.symm
        exact ⟨k, z, hz₁⟩)
    have h𝒯f (k : 𝒰.I₀) : 𝒯.f k = pullback.fst j (𝒰.f k) := rfl
    apply 𝒯.hom_ext
    intro k
    change pullback.fst j (𝒰.f k) ≫ j ≫ f =
      pullback.fst j (𝒰.f k) ≫ a ≫ H.inclusion
    calc
      pullback.fst j (𝒰.f k) ≫ j ≫ f =
          pullback.snd j (𝒰.f k) ≫ 𝒰.f k ≫ f :=
        congrArg (fun g => g ≫ f) pullback.condition
      _ = (pullbackSymmetry j (𝒰.f k)).hom ≫
          pullback.fst (𝒰.f k) j ≫ 𝒰.f k ≫ f := by simp
      _ = (pullbackSymmetry j (𝒰.f k)).hom ≫
          pullback.fst (𝒰.f k) j ≫ lift k :=
        congrArg (fun g => (pullbackSymmetry j (𝒰.f k)).hom ≫
          pullback.fst (𝒰.f k) j ≫ g) (𝒰.ι_glueMorphisms lift compatible k)
      _ = (pullbackSymmetry j (𝒰.f k)).hom ≫
          pullback.snd (𝒰.f k) j ≫ a ≫ H.inclusion := by
        simpa [Category.assoc] using congrArg
          (fun g => (pullbackSymmetry j (𝒰.f k)).hom ≫ g) (lift_spec k).1
      _ = pullback.fst j (𝒰.f k) ≫ a ≫ H.inclusion := by simp
  have hbase : f ≫ H.toBase = b := by
    apply 𝒰.hom_ext
    intro k
    rw [𝒰.ι_glueMorphisms_assoc lift compatible k]
    exact (lift_spec k).2
  refine ⟨f, ⟨hf, hbase⟩, ?_⟩
  intro g hg
  apply 𝒰.hom_ext
  intro k
  obtain ⟨w, hw, hu⟩ := localLift k
  have hwchoose : Classical.choose (localLift k).exists = w :=
    hu _ (Classical.choose_spec (localLift k).exists)
  calc
    𝒰.f k ≫ g = w := hu (𝒰.f k ≫ g) ⟨by
      calc
        pullback.fst (𝒰.f k) j ≫ (𝒰.f k ≫ g) =
            pullback.snd (𝒰.f k) j ≫ j ≫ g := by rw [← pullback.condition_assoc]
        _ = pullback.snd (𝒰.f k) j ≫ a ≫ H.inclusion := by rw [hg.1], by
      rw [Category.assoc, hg.2]⟩
    _ = Classical.choose (localLift k).exists := hwchoose.symm
    _ = lift k := rfl
    _ = 𝒰.f k ≫ f := (𝒰.ι_glueMorphisms lift compatible k).symm

/-- A universal first-order thickening over an open subscheme `U ⊆ X` is also one over `X`,
because a map out of a first-order thickening over `X` whose closed subscheme lands in `U`
lands in `U` entirely. This is the second of the "general remarks" of Tag 04F3. -/
private lemma isUniversalFirstOrderThickening_affineThickeningSkeleton
    {Z X : Scheme.{u}} [IsAffine Z] (U : X.Opens) [IsAffine U.toScheme]
    (h : Z ⟶ U.toScheme) [FormallyUnramified h] :
    IsUniversalFirstOrderThickening (h ≫ U.ι)
      (affineThickeningSkeleton h).inclusion
      ((affineThickeningSkeleton h).toBase ≫ U.ι) := by
  let H := affineThickeningSkeleton h
  refine ⟨H.isFirstOrderThickening, ?_, ?_⟩
  · simpa [H, Category.assoc] using congrArg (fun f => f ≫ U.ι) H.inclusion_toBase
  · intro T T' j hj a b hab
    obtain ⟨bU, hbU⟩ := exists_factorization_of_isFirstOrderThickening j hj U (a ≫ h) b (by
      simpa [Category.assoc] using hab.symm)
    have hcomm : j ≫ bU = a ≫ h := by
      apply (cancel_mono U.ι).mp
      calc
        (j ≫ bU) ≫ U.ι = j ≫ (bU ≫ U.ι) := by simp [Category.assoc]
        _ = j ≫ b := by rw [hbU]
        _ = (a ≫ h) ≫ U.ι := hab
    obtain ⟨f, hf, hu⟩ := affineThickeningSkeleton_existsUnique_lift h j hj a bU hcomm
    refine ⟨f, ⟨hf.1, ?_⟩, ?_⟩
    · calc
        f ≫ (H.toBase ≫ U.ι) = (f ≫ H.toBase) ≫ U.ι := by simp [Category.assoc]
        _ = bU ≫ U.ι := by rw [hf.2]
        _ = b := hbU
    · intro g hg
      have hbaseU : g ≫ H.toBase = bU := by
        apply (cancel_mono U.ι).mp
        calc
          (g ≫ H.toBase) ≫ U.ι = b := hg.2
          _ = bU ≫ U.ι := hbU.symm
      exact hu g ⟨hg.1, hbaseU⟩

/-- The open cover of `Z` by the preimages of the charts of the affine cover of `X`. -/
noncomputable def affinePreimageCover {Z X : Scheme.{u}} (h : Z ⟶ X) :
    Z.OpenCover := by
  let 𝒰 := X.affineCover
  refine Scheme.Cover.mkOfCovers (P := @IsOpenImmersion) 𝒰.I₀
    (fun i => (h ⁻¹ᵁ (𝒰.f i).opensRange).toScheme)
    (fun i => (h ⁻¹ᵁ (𝒰.f i).opensRange).ι) ?_
  intro z
  obtain ⟨i, y, hy⟩ := 𝒰.exists_eq (h z)
  exact ⟨i, ⟨z, y, hy⟩, rfl⟩

/-- An affine open cover of `Z` each of whose charts maps into an affine open of `X`. -/
noncomputable abbrev affineSourceCover {Z X : Scheme.{u}} (h : Z ⟶ X) :
    Z.OpenCover := (affinePreimageCover h).affineRefinement.openCover

/-- The charts of `affineSourceCover` are affine. -/
private instance isAffine_affineSourceCover {Z X : Scheme.{u}} (h : Z ⟶ X)
    (i : (affinePreimageCover h).affineRefinement.I₀) :
    IsAffine ((affineSourceCover h).X i) :=
  Scheme.isAffine_affineOpenCover Z (affinePreimageCover h).affineRefinement i

/-- The image of a chart of the affine cover of `X` is an affine open subscheme. -/
private instance isAffine_opensRange_affineCover {X : Scheme.{u}} (i : X.affineCover.I₀) :
    IsAffine ((X.affineCover.f i).opensRange.toScheme) := by
  have : IsOpenImmersion (X.affineCover.f i) := X.affineCover.map_prop i
  exact isAffineOpen_opensRange (X.affineCover.f i)

/-- The map from a chart of `affineSourceCover` to the preimage open subscheme containing it. -/
noncomputable def affineSourceChartMap {Z X : Scheme.{u}} (h : Z ⟶ X)
    (i : (affinePreimageCover h).affineRefinement.I₀) :
    (affineSourceCover h).X i ⟶ (affinePreimageCover h).X i.1 :=
  ((affinePreimageCover h).X i.1).affineCover.f i.2

/-- The structure morphism of a chart of `affineSourceCover` to the affine open of `X` it maps
into. -/
noncomputable def affineChartToBase {Z X : Scheme.{u}} (h : Z ⟶ X)
    (i : (affinePreimageCover h).affineRefinement.I₀)
    [IsOpenImmersion (X.affineCover.f i.1)] :
    (affineSourceCover h).X i ⟶ (X.affineCover.f i.1).opensRange.toScheme :=
  affineSourceChartMap h i ≫ (h ∣_ (X.affineCover.f i.1).opensRange)

/-- `affineChartToBase` is a factorization of the chart's composite to `X`. -/
private lemma affineChartToBase_comp_ι {Z X : Scheme.{u}} (h : Z ⟶ X)
    (i : (affinePreimageCover h).affineRefinement.I₀)
    [IsOpenImmersion (X.affineCover.f i.1)] :
    affineChartToBase h i ≫ (X.affineCover.f i.1).opensRange.ι =
      (affineSourceCover h).f i ≫ h := by
  let U := (X.affineCover.f i.1).opensRange
  have hres : (h ∣_ U) ≫ U.ι = (h ⁻¹ᵁ U).ι ≫ h := by
    rw [← Scheme.Hom.resLE_eq_morphismRestrict]
    exact Scheme.Hom.resLE_comp_ι h (U := U) (V := h ⁻¹ᵁ U) le_rfl
  have href : affineSourceChartMap h i ≫ (h ⁻¹ᵁ U).ι =
      (affineSourceCover h).f i := by
    change ((affinePreimageCover h).X i.1).affineCover.f i.2 ≫ (h ⁻¹ᵁ U).ι =
      (affinePreimageCover h).affineRefinement.openCover.f i
    exact (affinePreimageCover h).fromAffineRefinement.w₀ i
  calc
    affineChartToBase h i ≫ U.ι =
        affineSourceChartMap h i ≫ ((h ∣_ U) ≫ U.ι) := by
          change (affineSourceChartMap h i ≫ (h ∣_ U)) ≫ U.ι =
            affineSourceChartMap h i ≫ ((h ∣_ U) ≫ U.ι)
          exact Category.assoc _ _ _
    _ = affineSourceChartMap h i ≫ ((h ⁻¹ᵁ U).ι ≫ h) :=
      congrArg (fun f => affineSourceChartMap h i ≫ f) hres
    _ = (affineSourceChartMap h i ≫ (h ⁻¹ᵁ U).ι) ≫ h :=
      (Category.assoc _ _ _).symm
    _ = (affineSourceCover h).f i ≫ h := by
      simpa only [Category.assoc] using congrArg (fun f => f ≫ h) href

/-- `affineChartToBase` is formally unramified. This is Tag 02HC: formal unramifiedness is local
on the source and stable under base change to an open subscheme. -/
instance formallyUnramified_affineChartToBase {Z X : Scheme.{u}} (h : Z ⟶ X)
    [FormallyUnramified h] (i : (affinePreimageCover h).affineRefinement.I₀)
    [IsOpenImmersion (X.affineCover.f i.1)] :
    FormallyUnramified (affineChartToBase h i) := by
  let U := (X.affineCover.f i.1).opensRange
  have hres : FormallyUnramified (h ∣_ U) :=
    CategoryTheory.MorphismProperty.of_isPullback
      (isPullback_morphismRestrict h U).flip ‹FormallyUnramified h›
  have : IsOpenImmersion (affineSourceChartMap h i) := by
    dsimp [affineSourceChartMap]
    exact ((affinePreimageCover h).X i.1).affineCover.map_prop i.2
  exact CategoryTheory.MorphismProperty.comp_mem @FormallyUnramified
    (affineSourceChartMap h i) (h ∣_ U) inferInstance hres

/-- The affine construction applied to `affineChartToBase` is a universal first-order thickening
over `X`, not merely over the affine open of `X` it was built over. -/
private lemma affineChartToBase_isUniversal {Z X : Scheme.{u}} (h : Z ⟶ X)
    [FormallyUnramified h] (i : (affinePreimageCover h).affineRefinement.I₀)
    [IsOpenImmersion (X.affineCover.f i.1)]
    [IsAffine ((X.affineCover.f i.1).opensRange.toScheme)] :
    IsUniversalFirstOrderThickening
      (affineChartToBase h i ≫ (X.affineCover.f i.1).opensRange.ι)
      (affineThickeningSkeleton (affineChartToBase h i)).inclusion
      ((affineThickeningSkeleton (affineChartToBase h i)).toBase ≫
        (X.affineCover.f i.1).opensRange.ι) := by
  have : IsOpenImmersion (X.affineCover.f i.1) := X.affineCover.map_prop i.1
  have : IsAffine ((affineSourceCover h).X i) :=
    Scheme.isAffine_affineOpenCover _ (affinePreimageCover h).affineRefinement i
  have : IsAffine (X.affineCover.X i.1) := Scheme.isAffine_affineCover X i.1
  exact isUniversalFirstOrderThickening_affineThickeningSkeleton (X.affineCover.f i.1).opensRange
    (affineChartToBase h i)

/-- `affineChartToBase_isUniversal` rewritten so that the base morphism is the chart's composite
to `X`. -/
lemma affineChart_isUniversal {Z X : Scheme.{u}} (h : Z ⟶ X)
    [FormallyUnramified h] (i : (affinePreimageCover h).affineRefinement.I₀)
    [IsOpenImmersion (X.affineCover.f i.1)]
    [IsAffine ((X.affineCover.f i.1).opensRange.toScheme)] :
    IsUniversalFirstOrderThickening
      ((affineSourceCover h).f i ≫ h)
      (affineThickeningSkeleton (affineChartToBase h i)).inclusion
      ((affineThickeningSkeleton (affineChartToBase h i)).toBase ≫
        (X.affineCover.f i.1).opensRange.ι) := by
  rw [← affineChartToBase_comp_ι]
  exact affineChartToBase_isUniversal h i

/-- The chosen universal first-order thickening of a chart of `affineSourceCover` over `X`. -/
noncomputable def affineChartThickening {Z X : Scheme.{u}}
    (h : Z ⟶ X) [FormallyUnramified h]
    (i : (affinePreimageCover h).affineRefinement.I₀) :
    UniversalFirstOrderThickening ((affineSourceCover h).f i ≫ h) := by
  let F := X.affineCover
  haveI : IsOpenImmersion (F.f i.1) := F.map_prop i.1
  haveI : IsAffine (F.X i.1) := Scheme.isAffine_affineCover X i.1
  haveI : IsAffine ((F.f i.1).opensRange.toScheme) := isAffineOpen_opensRange (F.f i.1)
  letI : FormallyUnramified (affineChartToBase h i) := formallyUnramified_affineChartToBase h i
  let H := affineThickeningSkeleton (affineChartToBase h i)
  haveI : FormallyUnramified H.toBase := H.formallyUnramified_toBase
  haveI : FormallyUnramified (F.f i.1).opensRange.ι := inferInstance
  exact ⟨H.ambient, H.inclusion, H.toBase ≫ (F.f i.1).opensRange.ι,
    affineChart_isUniversal h i⟩

/-- The structure morphism of `affineChartThickening` is formally unramified; this is Tag 04F6 in
the affine case, and it is what makes the uniqueness half of the universal property available
when the charts are glued. -/
lemma formallyUnramified_affineChartThickening_toBase
    {Z X : Scheme.{u}} (h : Z ⟶ X) [FormallyUnramified h]
    (i : (affinePreimageCover h).affineRefinement.I₀) :
    FormallyUnramified (affineChartThickening h i).toBase := by
  dsimp [affineChartThickening]
  let F := X.affineCover
  have : IsOpenImmersion (F.f i.1) := F.map_prop i.1
  have : IsAffine (F.X i.1) := Scheme.isAffine_affineCover X i.1
  have : IsAffine ((F.f i.1).opensRange.toScheme) := isAffineOpen_opensRange (F.f i.1)
  let : FormallyUnramified (affineChartToBase h i) := formallyUnramified_affineChartToBase h i
  let H := affineThickeningSkeleton (affineChartToBase h i)
  have : FormallyUnramified H.toBase := H.formallyUnramified_toBase
  have : FormallyUnramified (F.f i.1).opensRange.ι := inferInstance
  exact MorphismProperty.comp_mem (@FormallyUnramified) H.toBase
    (F.f i.1).opensRange.ι inferInstance inferInstance

/-- Being a universal first-order thickening is invariant under precomposing with an isomorphism
of the closed subscheme. -/
lemma isUniversalFirstOrderThickening_comp_iso
    {Z Z' X A : Scheme.{u}} (e : Z ≅ Z') (h : Z' ⟶ X)
    (i : Z' ⟶ A) (p : A ⟶ X)
    (hi : IsUniversalFirstOrderThickening h i p) :
    IsUniversalFirstOrderThickening (e.hom ≫ h) (e.hom ≫ i) p := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · have eArrow : Arrow.mk i ≅ Arrow.mk (e.hom ≫ i) :=
        Arrow.isoMk e.symm (Iso.refl A) (by simp)
      exact (CategoryTheory.MorphismProperty.arrow_mk_iso_iff @IsClosedImmersion eArrow).1
        hi.isFirstOrderThickening.1
    · rw [Scheme.Hom.ker_comp_of_isIso]
      exact hi.isFirstOrderThickening.2
  · simpa only [Category.assoc] using congrArg (fun f => e.hom ≫ f) hi.inclusion_toBase
  · intro T T' j hj a b hab
    obtain ⟨f, hf, hu⟩ := hi.existsUnique_lift j hj (a ≫ e.hom) b (by
      simpa only [Category.assoc] using hab)
    refine ⟨f, ?_, ?_⟩
    · constructor
      · simpa only [Category.assoc] using hf.1
      · exact hf.2
    · intro g hg
      exact hu g ⟨by simpa only [Category.assoc] using hg.1, hg.2⟩

/-- Two universal first-order thickenings of the same morphism are canonically isomorphic, by the
two mutually inverse lifts of the identity. -/
noncomputable def isoOfIsUniversal
    {Z X A B : Scheme.{u}} (h : Z ⟶ X)
    (iA : Z ⟶ A) (hA : A ⟶ X)
    (iB : Z ⟶ B) (hB : B ⟶ X)
    (hAuniv : IsUniversalFirstOrderThickening h iA hA)
    (hBuniv : IsUniversalFirstOrderThickening h iB hB) : A ≅ B := by
  let ef := hBuniv.existsUnique_lift iA hAuniv.isFirstOrderThickening
    (𝟙 Z) hA hAuniv.inclusion_toBase
  let eg := hAuniv.existsUnique_lift iB hBuniv.isFirstOrderThickening
    (𝟙 Z) hB hBuniv.inclusion_toBase
  let f := Classical.choose ef.exists
  let g := Classical.choose eg.exists
  have hf := Classical.choose_spec ef.exists
  have hg := Classical.choose_spec eg.exists
  have hgf : iA ≫ (f ≫ g) = iA ≫ 𝟙 A := by
    calc
      iA ≫ (f ≫ g) = (iA ≫ f) ≫ g := (Category.assoc _ _ _).symm
      _ = (𝟙 Z ≫ iB) ≫ g := by rw [hf.1]
      _ = iA ≫ 𝟙 A := by rw [Category.assoc, hg.1]; simp
  have hbase : (f ≫ g) ≫ hA = hA := by
    rw [Category.assoc, hg.2, hf.2]
  have hfg : iB ≫ (g ≫ f) = iB ≫ 𝟙 B := by
    calc
      iB ≫ (g ≫ f) = (iB ≫ g) ≫ f := (Category.assoc _ _ _).symm
      _ = (𝟙 Z ≫ iA) ≫ f := by rw [hg.1]
      _ = iB ≫ 𝟙 B := by rw [Category.assoc, hf.1]; simp
  have hbase' : (g ≫ f) ≫ hB = hB := by
    rw [Category.assoc, hf.2, hg.2]
  have hgf' : f ≫ g = 𝟙 A :=
    ((hAuniv.existsUnique_lift iA hAuniv.isFirstOrderThickening (𝟙 Z) hA
      hAuniv.inclusion_toBase).unique ⟨Category.comp_id _, Category.id_comp _⟩
      ⟨hgf, hbase⟩).symm
  have hfg' : g ≫ f = 𝟙 B :=
    ((hBuniv.existsUnique_lift iB hBuniv.isFirstOrderThickening (𝟙 Z) hB
      hBuniv.inclusion_toBase).unique ⟨Category.comp_id _, Category.id_comp _⟩
      ⟨hfg, hbase'⟩).symm
  exact ⟨f, g, hgf', hfg'⟩

/-- `isoOfIsUniversal` is compatible with the two inclusions. -/
lemma isoOfIsUniversal_hom_fac
    {Z X A B : Scheme.{u}} (h : Z ⟶ X)
    (iA : Z ⟶ A) (hA : A ⟶ X)
    (iB : Z ⟶ B) (hB : B ⟶ X)
    (hAuniv : IsUniversalFirstOrderThickening h iA hA)
    (hBuniv : IsUniversalFirstOrderThickening h iB hB) :
    iA ≫ (isoOfIsUniversal h iA hA iB hB hAuniv hBuniv).hom = iB := by
  let ef := hBuniv.existsUnique_lift iA hAuniv.isFirstOrderThickening
    (𝟙 Z) hA hAuniv.inclusion_toBase
  have hf := Classical.choose_spec ef.exists
  change iA ≫ Classical.choose ef.exists = iB
  simpa [ef] using hf.1

/-- `isoOfIsUniversal` is a morphism over the base. -/
lemma isoOfIsUniversal_hom_toBase
    {Z X A B : Scheme.{u}} (h : Z ⟶ X)
    (iA : Z ⟶ A) (hA : A ⟶ X)
    (iB : Z ⟶ B) (hB : B ⟶ X)
    (hAuniv : IsUniversalFirstOrderThickening h iA hA)
    (hBuniv : IsUniversalFirstOrderThickening h iB hB) :
    (isoOfIsUniversal h iA hA iB hB hAuniv hBuniv).hom ≫ hB = hA := by
  let ef := hBuniv.existsUnique_lift iA hAuniv.isFirstOrderThickening
    (𝟙 Z) hA hAuniv.inclusion_toBase
  have hf := Classical.choose_spec ef.exists
  change Classical.choose ef.exists ≫ hB = hA
  exact hf.2

/-- The charts of an open cover are open immersions. -/
private instance isOpenImmersion_cover_f {Z : Scheme.{u}} (𝒰 : Z.OpenCover)
    (i : 𝒰.I₀) : IsOpenImmersion (𝒰.f i) := 𝒰.map_prop i

/-- The overlap of two charts of an open cover, as an open subscheme of the first chart. -/
noncomputable def sourceOverlap {Z : Scheme.{u}} (𝒰 : Z.OpenCover)
    (i j : 𝒰.I₀) : (𝒰.X i).Opens := (𝒰.f i) ⁻¹ᵁ (𝒰.f j).opensRange

/-- The restriction of a universal first-order thickening to an open subscheme of its closed
subscheme. -/
noncomputable def restrictUniversalThickening
    {Z X : Scheme.{u}} {h : Z ⟶ X}
    (H : UniversalFirstOrderThickening h) (V : Z.Opens) :
    UniversalFirstOrderThickening (V.ι ≫ h) := by
  let W := thickeningOpenImage H.inclusion H.isUniversal.isFirstOrderThickening.isThickening V
  have hpre : H.inclusion ⁻¹ᵁ W = V :=
    preimage_thickeningOpenImage H.inclusion H.isUniversal.isFirstOrderThickening.isThickening V
  exact ⟨W.toScheme,
    H.inclusion.resLE W V hpre.ge,
    W.ι ≫ H.toBase,
    isUniversalFirstOrderThickening_resLE_top H.isUniversal hpre⟩

/-- The two descriptions of the overlap of two charts have the same image in `Z`. -/
lemma sourceOverlap_range {Z : Scheme.{u}} (𝒰 : Z.OpenCover)
    (i j : 𝒰.I₀) :
    Set.range ((sourceOverlap 𝒰 i j).ι ≫ 𝒰.f i).base =
      Set.range ((sourceOverlap 𝒰 j i).ι ≫ 𝒰.f j).base := by
  have hrange (i j : 𝒰.I₀) : Scheme.Hom.opensRange ((sourceOverlap 𝒰 i j).ι ≫ 𝒰.f i) =
      (𝒰.f i).opensRange ⊓ (𝒰.f j).opensRange := by
    rw [Scheme.Hom.opensRange_comp, Scheme.Opens.opensRange_ι]
    simpa [sourceOverlap] using
      (Scheme.Hom.image_preimage_eq_opensRange_inf (𝒰.f i) (𝒰.f j).opensRange)
  have heq : Scheme.Hom.opensRange ((sourceOverlap 𝒰 i j).ι ≫ 𝒰.f i) =
      Scheme.Hom.opensRange ((sourceOverlap 𝒰 j i).ι ≫ 𝒰.f j) := by
    rw [hrange, hrange, inf_comm]
  simpa only [Scheme.Hom.coe_opensRange] using
    congrArg (fun V : Z.Opens => (V : Set Z)) heq

/-- The triple overlap of three charts of an open cover, as an open subscheme of the first
chart. -/
noncomputable def sourceTriple {Z : Scheme.{u}} (𝒰 : Z.OpenCover)
    (i j k : 𝒰.I₀) : (𝒰.X i).Opens := sourceOverlap 𝒰 i j ⊓ sourceOverlap 𝒰 i k

/-- A triple overlap is contained in the corresponding double overlap. -/
lemma sourceTriple_le_sourceOverlap {Z : Scheme.{u}} (𝒰 : Z.OpenCover)
    (i j k : 𝒰.I₀) : sourceTriple 𝒰 i j k ≤ sourceOverlap 𝒰 i j :=
  inf_le_left

/-- The triple overlap is symmetric in its last two indices. -/
lemma sourceTriple_swap {Z : Scheme.{u}} (𝒰 : Z.OpenCover)
    (i j k : 𝒰.I₀) : sourceTriple 𝒰 i j k = sourceTriple 𝒰 i k j :=
  inf_comm _ _

/-- The image of a triple overlap in `Z` is the intersection of the three charts. -/
private lemma sourceTriple_opensRange {Z : Scheme.{u}} (𝒰 : Z.OpenCover)
    (i j k : 𝒰.I₀) :
    Scheme.Hom.opensRange ((sourceTriple 𝒰 i j k).ι ≫ 𝒰.f i) =
      (𝒰.f i).opensRange ⊓ (𝒰.f j).opensRange ⊓ (𝒰.f k).opensRange := by
  rw [Scheme.Hom.opensRange_comp, Scheme.Opens.opensRange_ι]
  have hpre : sourceTriple 𝒰 i j k =
      (𝒰.f i) ⁻¹ᵁ ((𝒰.f j).opensRange ⊓ (𝒰.f k).opensRange) := by
    ext z
    simp [sourceTriple, sourceOverlap]
  rw [hpre]
  simpa [inf_assoc] using Scheme.Hom.image_preimage_eq_opensRange_inf (𝒰.f i)
    ((𝒰.f j).opensRange ⊓ (𝒰.f k).opensRange)

/-- The two descriptions of a triple overlap have the same image in `Z`. -/
lemma sourceTriple_range_eq {Z : Scheme.{u}} (𝒰 : Z.OpenCover)
    (i j k : 𝒰.I₀) :
    Set.range ((sourceTriple 𝒰 i j k).ι ≫ 𝒰.f i).base =
      Set.range ((sourceTriple 𝒰 j i k).ι ≫ 𝒰.f j).base := by
  have heq : Scheme.Hom.opensRange ((sourceTriple 𝒰 i j k).ι ≫ 𝒰.f i) =
      Scheme.Hom.opensRange ((sourceTriple 𝒰 j i k).ι ≫ 𝒰.f j) := by
    rw [sourceTriple_opensRange, sourceTriple_opensRange]
    ac_rfl
  simpa only [Scheme.Hom.coe_opensRange] using
    congrArg (fun V : Z.Opens => (V : Set Z)) heq

/-- The isomorphism between the two descriptions of a triple overlap. -/
noncomputable def sourceTripleIso {Z : Scheme.{u}} (𝒰 : Z.OpenCover)
    (i j k : 𝒰.I₀) : (sourceTriple 𝒰 i j k).toScheme ≅
      (sourceTriple 𝒰 j i k).toScheme :=
  IsOpenImmersion.isoOfRangeEq
    ((sourceTriple 𝒰 i j k).ι ≫ 𝒰.f i)
    ((sourceTriple 𝒰 j i k).ι ≫ 𝒰.f j)
    (sourceTriple_range_eq 𝒰 i j k)

/-- `sourceTripleIso` is compatible with the maps to `Z`. -/
lemma sourceTripleIso_hom_fac {Z : Scheme.{u}} (𝒰 : Z.OpenCover)
    (i j k : 𝒰.I₀) :
    (sourceTripleIso 𝒰 i j k).hom ≫
        ((sourceTriple 𝒰 j i k).ι ≫ 𝒰.f j) =
      (sourceTriple 𝒰 i j k).ι ≫ 𝒰.f i :=
  IsOpenImmersion.isoOfRangeEq_hom_fac
    ((sourceTriple 𝒰 i j k).ι ≫ 𝒰.f i)
    ((sourceTriple 𝒰 j i k).ι ≫ 𝒰.f j)
    (sourceTriple_range_eq 𝒰 i j k)

/-- The universal first-order thickening of a triple overlap, obtained by restricting the chosen
thickening of the first chart. -/
noncomputable def tripleRestriction {Z X : Scheme.{u}}
    (𝒰 : Z.OpenCover) (h : Z ⟶ X)
    (A : ∀ i, UniversalFirstOrderThickening (𝒰.f i ≫ h)) (i j k : 𝒰.I₀) :
    UniversalFirstOrderThickening ((sourceTriple 𝒰 i j k).ι ≫ 𝒰.f i ≫ h) :=
  restrictUniversalThickening (A i) (sourceTriple 𝒰 i j k)

/-- The open immersion of the ambient scheme of `tripleRestriction` into the ambient scheme of
the chart's thickening. -/
noncomputable def tripleRestrictionMap {Z X : Scheme.{u}}
    (𝒰 : Z.OpenCover) (h : Z ⟶ X)
    (A : ∀ i, UniversalFirstOrderThickening (𝒰.f i ≫ h)) (i j k : 𝒰.I₀) :
    (tripleRestriction 𝒰 h A i j k).ambient ⟶ (A i).ambient :=
  (thickeningOpenImage (A i).inclusion (A i).isUniversal.isFirstOrderThickening.isThickening
    (sourceTriple 𝒰 i j k)).ι

/-- `tripleRestrictionMap` is an open immersion. -/
instance isOpenImmersion_tripleRestrictionMap {Z X : Scheme.{u}}
    (𝒰 : Z.OpenCover) (h : Z ⟶ X)
    (A : ∀ i, UniversalFirstOrderThickening (𝒰.f i ≫ h)) (i j k : 𝒰.I₀) :
    IsOpenImmersion (tripleRestrictionMap 𝒰 h A i j k) :=
  (thickeningOpenImage (A i).inclusion
    (A i).isUniversal.isFirstOrderThickening.isThickening
      (sourceTriple 𝒰 i j k)).instIsOpenImmersionι

/-- The canonical isomorphism between the thickenings of a triple overlap computed from its two
first charts. -/
noncomputable def tripleTransition {Z X : Scheme.{u}}
    (𝒰 : Z.OpenCover) (h : Z ⟶ X)
    (A : ∀ i, UniversalFirstOrderThickening (𝒰.f i ≫ h)) (i j k : 𝒰.I₀) :
    (tripleRestriction 𝒰 h A i j k).ambient ≅
      (tripleRestriction 𝒰 h A j i k).ambient := by
  let e := sourceTripleIso 𝒰 i j k
  have heqZ : e.hom ≫ ((sourceTriple 𝒰 j i k).ι ≫ 𝒰.f j) =
      (sourceTriple 𝒰 i j k).ι ≫ 𝒰.f i :=
    sourceTripleIso_hom_fac 𝒰 i j k
  have heq : e.hom ≫ ((sourceTriple 𝒰 j i k).ι ≫ 𝒰.f j ≫ h) =
      (sourceTriple 𝒰 i j k).ι ≫ 𝒰.f i ≫ h := by
    simpa only [Category.assoc] using congrArg (fun f => f ≫ h) heqZ
  have hright := isUniversalFirstOrderThickening_comp_iso e
    ((sourceTriple 𝒰 j i k).ι ≫ 𝒰.f j ≫ h)
    (tripleRestriction 𝒰 h A j i k).inclusion
    (tripleRestriction 𝒰 h A j i k).toBase
    (tripleRestriction 𝒰 h A j i k).isUniversal
  have hright' : IsUniversalFirstOrderThickening
      ((sourceTriple 𝒰 i j k).ι ≫ 𝒰.f i ≫ h)
      (e.hom ≫ (tripleRestriction 𝒰 h A j i k).inclusion)
      ((tripleRestriction 𝒰 h A j i k).toBase) :=
    heq ▸ hright
  exact isoOfIsUniversal
    ((sourceTriple 𝒰 i j k).ι ≫ 𝒰.f i ≫ h)
    (tripleRestriction 𝒰 h A i j k).inclusion
    (tripleRestriction 𝒰 h A i j k).toBase
    (e.hom ≫ (tripleRestriction 𝒰 h A j i k).inclusion)
    (tripleRestriction 𝒰 h A j i k).toBase
    (tripleRestriction 𝒰 h A i j k).isUniversal hright'

/-- The isomorphism between the two descriptions of the overlap of two charts. -/
noncomputable def sourceOverlapIso {Z : Scheme.{u}} (𝒰 : Z.OpenCover)
    (i j : 𝒰.I₀) : (sourceOverlap 𝒰 i j).toScheme ≅ (sourceOverlap 𝒰 j i).toScheme :=
  IsOpenImmersion.isoOfRangeEq ((sourceOverlap 𝒰 i j).ι ≫ 𝒰.f i)
    ((sourceOverlap 𝒰 j i).ι ≫ 𝒰.f j) (sourceOverlap_range 𝒰 i j)

/-- `sourceOverlapIso` at a repeated index is the identity. -/
lemma sourceOverlapIso_self {Z : Scheme.{u}} (𝒰 : Z.OpenCover) (i : 𝒰.I₀) :
    (sourceOverlapIso 𝒰 i i).hom = 𝟙 _ := by
  apply (cancel_mono ((sourceOverlap 𝒰 i i).ι ≫ 𝒰.f i)).mp
  change (IsOpenImmersion.isoOfRangeEq _ _ _).hom ≫ _ = _
  exact IsOpenImmersion.isoOfRangeEq_hom_fac
    ((sourceOverlap 𝒰 i i).ι ≫ 𝒰.f i)
    ((sourceOverlap 𝒰 i i).ι ≫ 𝒰.f i) (sourceOverlap_range 𝒰 i i)

/-- The universal first-order thickening of a double overlap, obtained by restricting the chosen
thickening of the first chart. -/
noncomputable def overlapRestriction {Z X : Scheme.{u}}
    (𝒰 : Z.OpenCover) (h : Z ⟶ X)
    (A : ∀ i, UniversalFirstOrderThickening (𝒰.f i ≫ h)) (i j : 𝒰.I₀) :
    UniversalFirstOrderThickening
      ((sourceOverlap 𝒰 i j).ι ≫ 𝒰.f i ≫ h) := by
  let V := sourceOverlap 𝒰 i j
  let H := A i
  let W := thickeningOpenImage H.inclusion H.isUniversal.isFirstOrderThickening.isThickening V
  have hpre : H.inclusion ⁻¹ᵁ W = V :=
    preimage_thickeningOpenImage H.inclusion H.isUniversal.isFirstOrderThickening.isThickening V
  exact ⟨W.toScheme,
    H.inclusion.resLE W V hpre.ge,
    W.ι ≫ H.toBase,
    isUniversalFirstOrderThickening_resLE_top H.isUniversal hpre⟩

/-- The open immersion of the ambient scheme of `overlapRestriction` into the ambient scheme of
the chart's thickening. -/
noncomputable def overlapRestrictionMap {Z X : Scheme.{u}}
    (𝒰 : Z.OpenCover) (h : Z ⟶ X)
    (A : ∀ i, UniversalFirstOrderThickening (𝒰.f i ≫ h)) (i j : 𝒰.I₀) :
    (overlapRestriction 𝒰 h A i j).ambient ⟶ (A i).ambient :=
  (thickeningOpenImage (A i).inclusion (A i).isUniversal.isFirstOrderThickening.isThickening
    (sourceOverlap 𝒰 i j)).ι

/-- `overlapRestrictionMap` is an open immersion. -/
instance isOpenImmersion_overlapRestrictionMap {Z X : Scheme.{u}}
    (𝒰 : Z.OpenCover) (h : Z ⟶ X)
    (A : ∀ i, UniversalFirstOrderThickening (𝒰.f i ≫ h)) (i j : 𝒰.I₀) :
    IsOpenImmersion (overlapRestrictionMap 𝒰 h A i j) :=
  (thickeningOpenImage (A i).inclusion
    (A i).isUniversal.isFirstOrderThickening.isThickening
      (sourceOverlap 𝒰 i j)).instIsOpenImmersionι

/-- The image of a triple overlap thickening is the intersection of the two double overlap
thickenings. -/
lemma tripleRestrictionMap_opensRange {Z X : Scheme.{u}}
    (𝒰 : Z.OpenCover) (h : Z ⟶ X)
    (A : ∀ i, UniversalFirstOrderThickening (𝒰.f i ≫ h)) (i j k : 𝒰.I₀) :
    (tripleRestrictionMap 𝒰 h A i j k).opensRange =
      (overlapRestrictionMap 𝒰 h A i j).opensRange ⊓
        (overlapRestrictionMap 𝒰 h A i k).opensRange := by
  dsimp only [tripleRestrictionMap, overlapRestrictionMap,
    tripleRestriction, restrictUniversalThickening,
    overlapRestriction]
  rw [Scheme.Opens.opensRange_ι, Scheme.Opens.opensRange_ι,
    Scheme.Opens.opensRange_ι]
  apply SetLike.coe_injective
  change (thickeningHomeomorph (A i).inclusion
      (A i).isUniversal.isFirstOrderThickening.isThickening) ''
      (sourceOverlap 𝒰 i j ⊓ sourceOverlap 𝒰 i k : Set (𝒰.X i)) =
    ((thickeningHomeomorph (A i).inclusion
        (A i).isUniversal.isFirstOrderThickening.isThickening) ''
        (sourceOverlap 𝒰 i j : Set (𝒰.X i))) ∩
      ((thickeningHomeomorph (A i).inclusion
        (A i).isUniversal.isFirstOrderThickening.isThickening) ''
        (sourceOverlap 𝒰 i k : Set (𝒰.X i)))
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy.1, rfl⟩, ⟨y, hy.2, rfl⟩⟩
  · rintro ⟨⟨y, hy, rfl⟩, ⟨z, hz, heq⟩⟩
    have hEq : y = z := (thickeningHomeomorph (A i).inclusion
      (A i).isUniversal.isFirstOrderThickening.isThickening).injective heq.symm
    subst z
    exact ⟨y, ⟨hy, hz⟩, rfl⟩

end Stacks.Thickenings

end
