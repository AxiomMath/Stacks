module

public import StacksFrontier.AlgebraicGeometry.Picard.HilbertAffineLine
public import StacksFrontier.Examples.GroupSchemes.DoubleGlue
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.AffineSpaceSmooth
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorSupportedInOpenRepresentable

/-!
# The affine line with doubled points over a base

Let `S` be a scheme and `W ⊆ S` an open subscheme. Glue two copies of the affine line `𝔸¹_S`
along the open `𝔸¹_W`; the result is a scheme `X` over `S` covered by two charts `𝔸¹_S ⟶ X`,
which agree over `W` and are disjoint over the complement of `W`. It is smooth of relative
dimension one over `S`, and it is not separated when `W` is not closed.

This file sets up `X` and the behaviour of its charts after base change along an `S`-scheme
`T`: they are open immersions covering `X ×_S T`, they agree over the inverse image of `W`, a
point in the image of both lies over `W`, over a base landing in `W` either chart is an
isomorphism, and over a base landing outside `W` the two charts have complementary images.

## Main definitions

* `Stacks.Hilbert.DoubledLine.doubledLine` — the scheme `X` over `S`.
* `Stacks.Hilbert.DoubledLine.chartHom`, `Stacks.Hilbert.DoubledLine.foldHom` — its two charts
  and the morphism `X ⟶ 𝔸¹_S` restricting to the identity on each.
* `Stacks.Hilbert.DoubledLine.chartT` — the charts after base change along `T`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Hilbert

/-- The comparison map of ambient schemes induced by the identity is the identity. -/
theorem familyAmbientMap_id {S : Scheme.{u}} (X : Over S) (T : Over S) :
    familyAmbientMap (𝟙 X) T = 𝟙 _ := by
  refine pullback.hom_ext ?_ ?_ <;> simp [familyAmbientMap, pullback.map]

/-- The comparison maps of ambient schemes compose. -/
theorem familyAmbientMap_comp {S : Scheme.{u}} {X Y Z : Over S} (i : X ⟶ Y) (j : Y ⟶ Z)
    (T : Over S) : familyAmbientMap (i ≫ j) T = familyAmbientMap i T ≫ familyAmbientMap j T := by
  refine pullback.hom_ext ?_ ?_ <;>
    simp only [familyAmbientMap, pullback.map, Category.assoc, Category.comp_id,
      pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, Over.comp_left]

/-- The comparison map `X ×_S T ⟶ Y ×_S T` is a morphism over `T`. -/
alias familyAmbientMap_comp_hom := familyAmbientMap_hom

/-- The comparison map `X ×_S T ⟶ Y ×_S T` lies over the morphism `X ⟶ Y`. -/
theorem familyAmbientMap_comp_fst {S : Scheme.{u}} {X Y : Over S} (i : X ⟶ Y) (T : Over S) :
    familyAmbientMap i T ≫ pullback.fst Y.hom T.hom = pullback.fst X.hom T.hom ≫ i.left :=
  pullback.lift_fst _ _ _

/-- The comparison map `X ×_S T ⟶ Y ×_S T` is the base change of `X ⟶ Y` along `T ⟶ S`. -/
theorem familyAmbientMap_eq_left {S : Scheme.{u}} {X Y : Over S} (i : X ⟶ Y) (T : Over S) :
    familyAmbientMap i T = ((Over.pullback T.hom).map i).left := by
  refine pullback.hom_ext ?_ ?_ <;> simp [familyAmbientMap, pullback.map]

/-- The base change of an open immersion `X ⟶ Y` along `T ⟶ S` is an open immersion. -/
instance {S : Scheme.{u}} {X Y : Over S} (i : X ⟶ Y) [IsOpenImmersion i.left] (T : Over S) :
    IsOpenImmersion (familyAmbientMap i T) := by
  rw [familyAmbientMap_eq_left]
  exact MorphismProperty.overPullbackMap (P := @IsOpenImmersion) T.hom i ‹_›

/-- The image of `X ×_S T ⟶ Y ×_S T` is the inverse image of the image of `X ⟶ Y`. -/
theorem range_familyAmbientMap {S : Scheme.{u}} {X Y : Over S} (i : X ⟶ Y) (T : Over S) :
    Set.range (familyAmbientMap i T) =
      pullback.fst Y.hom T.hom ⁻¹' Set.range i.left := by
  rw [familyAmbientMap, Scheme.Pullback.range_map]
  simp

namespace DoubledLine

open AffineLine

variable {S : Scheme.{u}} (W : S.Opens)

/-- The inverse image of `W` in the affine line `𝔸¹_S`. -/
abbrev lineOver : (𝔸(PUnit.{u + 1}; S)).Opens := (𝔸(PUnit.{u + 1}; S) ↘ S) ⁻¹ᵁ W

/-- Two copies of `𝔸¹_S` glued along `𝔸¹_W`, with its two charts. -/
abbrev cover : Stacks.Examples.SectionCoverData 𝔸(PUnit.{u + 1}; S) :=
  Stacks.Examples.doubleSectionCover _ (lineOver W)

/-- **The affine line with doubled points.** Two copies of `𝔸¹_S` glued along `𝔸¹_W`, as a
scheme over `S`. -/
abbrev doubledLine : Over S := Over.mk ((cover W).proj ≫ (𝔸(PUnit.{u + 1}; S) ↘ S))

/-- The two charts `𝔸¹_S ⟶ X` of the doubled line. -/
def chartHom (b : Bool) : line S ⟶ doubledLine W :=
  Over.homMk ((cover W).chart b) (by
    change (cover W).chart b ≫ (cover W).proj ≫ _ = _
    rw [← Category.assoc, (cover W).chart_comp_proj, Category.id_comp]
    rfl)

/-- The morphism `X ⟶ 𝔸¹_S` which is the identity on each chart. -/
def foldHom : doubledLine W ⟶ line S := Over.homMk (cover W).proj rfl

/-- The fold map restricts to the identity on each chart. -/
theorem chartHom_foldHom (b : Bool) : chartHom W b ≫ foldHom W = 𝟙 _ :=
  Over.OverMorphism.ext ((cover W).chart_comp_proj b)

/-- Each chart of the doubled line is an open immersion. -/
instance (b : Bool) : IsOpenImmersion (chartHom W b).left := (cover W).isOpenImmersion_chart b

/-- The two charts agree on `𝔸¹_W`. -/
theorem chart_agree :
    (lineOver W).ι ≫ (cover W).chart true = (lineOver W).ι ≫ (cover W).chart false :=
  Stacks.Examples.doubleSectionCover_chart_agree _ _

/-- A point in the image of both charts comes from `𝔸¹_W`. -/
theorem mem_lineOver_of_chart_eq {b b' : Bool} (hbb' : b ≠ b') {y y' : 𝔸(PUnit.{u + 1}; S)}
    (h : (cover W).chart b y = (cover W).chart b' y') : y ∈ lineOver W := by
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback y y' h
  have hp := Stacks.Examples.doubleSectionCover_isPullback_chart _ (lineOver W) hbb'
  rw [← hp.isoPullback_inv_fst, Scheme.Hom.comp_apply] at hz
  rw [← hz]
  exact (Scheme.Opens.range_ι (lineOver W)).subset ⟨_, rfl⟩

/-! ### Smoothness -/

/-- The affine line over any base is smooth of relative dimension one. -/
theorem smoothOfRelativeDimension_line (S : Scheme.{u}) :
    SmoothOfRelativeDimension 1 (𝔸(PUnit.{u + 1}; S) ↘ S) := by
  have h0 : SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom
      (MvPolynomial.C : ULift.{u} ℤ →+* MvPolynomial PUnit.{u + 1} (ULift.{u} ℤ)))) := by
    rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)]
    refine RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ ?_
    change (algebraMap (ULift.{u} ℤ)
      (MvPolynomial PUnit.{u + 1} (ULift.{u} ℤ))).IsStandardSmoothOfRelativeDimension 1
    rw [RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
    exact Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv 1
      (MvPolynomial.renameEquiv (ULift.{u} ℤ) (Equiv.equivPUnit.{1, u + 1} (Fin 1)))
  have h1 : SmoothOfRelativeDimension 1 (terminal.from
      (Spec (CommRingCat.of (MvPolynomial PUnit.{u + 1} (ULift.{u} ℤ))))) := by
    rw [show terminal.from (Spec (CommRingCat.of (MvPolynomial PUnit.{u + 1} (ULift.{u} ℤ)))) =
        Spec.map (CommRingCat.ofHom MvPolynomial.C) ≫
          (specULiftZIsTerminal.{u}.uniqueUpToIso terminalIsTerminal).hom from
      terminal.hom_ext _ _]
    exact SmoothOfRelativeDimension.comp_relativeDimension_zero 1 _ _
  exact (smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)).of_isPullback
    (IsPullback.of_hasPullback (terminal.from S)
      (terminal.from (Spec (CommRingCat.of (MvPolynomial PUnit.{u + 1} (ULift.{u} ℤ)))))).flip h1

/-- **The doubled line is smooth of relative dimension one**: each chart is a copy of `𝔸¹_S`. -/
instance smoothOfRelativeDimension_doubledLine :
    SmoothOfRelativeDimension 1 (doubledLine W).hom := by
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @SmoothOfRelativeDimension 1)
  have key (b : Bool) : SmoothOfRelativeDimension 1
      ((cover W).chart b ≫ (cover W).proj ≫ (𝔸(PUnit.{u + 1}; S) ↘ S)) := by
    rw [← Category.assoc, (cover W).chart_comp_proj, Category.id_comp]
    exact smoothOfRelativeDimension_line S
  exact IsZariskiLocalAtSource.of_openCover (cover W).cover key

/-! ### The charts after base change -/

variable (T : Over S)

/-- The doubled line over `T`. -/
abbrev total : Scheme.{u} := ((Over.pullback T.hom).obj (doubledLine W)).left

/-- The two charts `𝔸¹_S ×_S T ⟶ X ×_S T`. -/
def chartT (b : Bool) : ambient T ⟶ total W T := familyAmbientMap (chartHom W b) T

/-- The fold map `X ×_S T ⟶ 𝔸¹_S ×_S T`. -/
def foldT : total W T ⟶ ambient T := familyAmbientMap (foldHom W) T

/-- Each chart of the doubled line over `T` is an open immersion. -/
instance (b : Bool) : IsOpenImmersion (chartT W T b) := by
  unfold chartT
  infer_instance

/-- The fold map over `T` restricts to the identity on each chart. -/
theorem chartT_foldT (b : Bool) : chartT W T b ≫ foldT W T = 𝟙 _ := by
  rw [chartT, foldT, ← familyAmbientMap_comp, chartHom_foldHom, familyAmbientMap_id]

/-- Each chart `𝔸¹_S ×_S T ⟶ X ×_S T` is a morphism over `T`. -/
theorem chartT_hom (b : Bool) :
    chartT W T b ≫ ((Over.pullback T.hom).obj (doubledLine W)).hom = proj T :=
  familyAmbientMap_comp_hom _ T

/-- The charts over `T` are natural in `T`. -/
theorem chartT_naturality (b : Bool) {T' : Over S} (g : T' ⟶ T) :
    chartT W T' b ≫ familyBaseChangeMap (doubledLine W) g =
      familyBaseChangeMap (line S) g ≫ chartT W T b :=
  familyAmbientMap_familyBaseChangeMap _ g

/-- The point of `X` under a point of `X ×_S T`. -/
abbrev toTotal : total W T ⟶ (doubledLine W).left := pullback.fst _ _

/-- The point of `𝔸¹_S` under a point of `𝔸¹_S ×_S T`. -/
abbrev toLine : ambient T ⟶ 𝔸(PUnit.{u + 1}; S) := pullback.fst _ _

/-- The square formed by `𝔸¹_S ×_S T`, `𝔸¹_S`, `T` and `S` commutes. -/
theorem toLine_comp : toLine T ≫ (𝔸(PUnit.{u + 1}; S) ↘ S) = proj T ≫ T.hom :=
  pullback.condition

/-- Each chart over `T` lies over the corresponding chart `𝔸¹_S ⟶ X`. -/
theorem chartT_toTotal (b : Bool) :
    chartT W T b ≫ toTotal W T = toLine T ≫ (chartHom W b).left :=
  familyAmbientMap_comp_fst _ T

/-- The two charts agree on `𝔸¹_W`, in the form of morphisms of `S`-schemes. -/
theorem chartHom_agree :
    (lineOver W).ι ≫ (chartHom W true).left = (lineOver W).ι ≫ (chartHom W false).left :=
  chart_agree W

/-- **The charts cover `X ×_S T`.** -/
theorem exists_chartT_eq (p : total W T) : ∃ (b : Bool) (a : ambient T), chartT W T b a = p := by
  obtain ⟨b, y, hy⟩ := (cover W).exists_chart_eq (toTotal W T p)
  refine ⟨b, ?_⟩
  rw [← Set.mem_range, chartT, range_familyAmbientMap]
  exact ⟨y, hy⟩

/-- **A point in the image of both charts lies over `W`.** -/
theorem mem_of_chartT_eq {b b' : Bool} (hbb' : b ≠ b') {a a' : ambient T}
    (h : chartT W T b a = chartT W T b' a') : T.hom (proj T a) ∈ W := by
  have h' : (chartT W T b ≫ toTotal W T) a = (chartT W T b' ≫ toTotal W T) a' := by
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, h]
  rw [chartT_toTotal, chartT_toTotal, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at h'
  rw [← Scheme.Hom.comp_apply, ← toLine_comp, Scheme.Hom.comp_apply]
  exact mem_lineOver_of_chart_eq W hbb' h'

/-- **The charts agree over `W`.** If a morphism into `𝔸¹_S ×_S T` lands over `W`, its
composites with the two charts agree. -/
theorem comp_chartT_eq {V : Scheme.{u}} (h : V ⟶ ambient T)
    (hW : ∀ v, T.hom (proj T (h v)) ∈ W) : h ≫ chartT W T true = h ≫ chartT W T false := by
  have hrange : Set.range (h ≫ toLine T) ⊆ ((lineOver W).ι).opensRange := by
    rintro _ ⟨v, rfl⟩
    rw [Scheme.Opens.opensRange_ι]
    change (𝔸(PUnit.{u + 1}; S) ↘ S) ((h ≫ toLine T) v) ∈ W
    rw [← Scheme.Hom.comp_apply, Category.assoc, toLine_comp, ← Category.assoc,
      Scheme.Hom.comp_apply]
    exact hW v
  let l := IsOpenImmersion.lift (lineOver W).ι _ hrange
  have hl : l ≫ (lineOver W).ι = h ≫ toLine T := IsOpenImmersion.lift_fac _ _ _
  refine pullback.hom_ext ?_ ?_
  · change h ≫ chartT W T true ≫ toTotal W T = h ≫ chartT W T false ≫ toTotal W T
    rw [chartT_toTotal, chartT_toTotal, ← Category.assoc, ← hl, Category.assoc,
      chartHom_agree, ← Category.assoc, hl, Category.assoc]
  · change h ≫ chartT W T true ≫ ((Over.pullback T.hom).obj (doubledLine W)).hom =
      h ≫ chartT W T false ≫ ((Over.pullback T.hom).obj (doubledLine W)).hom
    rw [chartT_hom, chartT_hom]

/-- **Over a base landing in `W` the two charts are the same isomorphism.** -/
theorem chartT_true_eq_false (hW : ∀ t, T.hom t ∈ W) : chartT W T true = chartT W T false := by
  simpa using comp_chartT_eq W T (𝟙 _) fun v ↦ hW _

/-- Over a base landing in `W`, every chart equals the chart indexed by `true`. -/
theorem chartT_true_eq_false' (hW : ∀ t, T.hom t ∈ W) (b : Bool) :
    chartT W T true = chartT W T b := by
  cases b <;> [exact chartT_true_eq_false W T hW; rfl]

/-- Over a base landing in `W`, each chart is an isomorphism. -/
theorem isIso_chartT (hW : ∀ t, T.hom t ∈ W) (b : Bool) : IsIso (chartT W T b) := by
  have hsurj : Function.Surjective (chartT W T b) := by
    intro p
    obtain ⟨b', a, ha⟩ := exists_chartT_eq W T p
    refine ⟨a, ?_⟩
    cases b <;> cases b' <;> simp_all [chartT_true_eq_false W T hW]
  have : Epi (chartT W T b).base := (TopCat.epi_iff_surjective _).mpr hsurj
  exact IsOpenImmersion.isIso _

/-- **Over a base landing outside `W` the two charts have complementary images.** -/
theorem isCompl_opensRange_chartT (hW : ∀ t, T.hom t ∉ W) :
    IsCompl (chartT W T true).opensRange (chartT W T false).opensRange := by
  constructor
  · rw [disjoint_iff, eq_bot_iff]
    rintro p ⟨⟨a, rfl⟩, ⟨a', ha'⟩⟩
    exact hW _ (mem_of_chartT_eq W T (by decide) ha'.symm)
  · rw [codisjoint_iff, eq_top_iff]
    intro p _
    obtain ⟨b, a, rfl⟩ := exists_chartT_eq W T p
    cases b <;> [exact Or.inr ⟨a, rfl⟩; exact Or.inl ⟨a, rfl⟩]

end DoubledLine

end Stacks.Hilbert

end
