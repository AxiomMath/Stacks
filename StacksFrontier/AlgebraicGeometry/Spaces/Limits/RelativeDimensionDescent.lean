module

public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.BaseChange
public import StacksFrontier.AlgebraicGeometry.Limits.FibreDimensionBound
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionChart
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Descending a bound on the relative dimension along a limit

The relative dimension of a morphism of algebraic spaces at a point of its source is read off
an étale scheme chart, so a bound on it at every point is a bound on the local dimension of the
fibres of the morphism of charts. This file proves the two directions of that translation, and
that a bound on the local dimension of the fibres of the base change of a morphism of schemes to
the limit of a cofiltered inverse system holds already for its base change to some stage.

## Main definitions

* `AlgebraicGeometry.fiberDimensionLE` is the bound `≤ d` on the local dimension of the fibre
  through each point of the source, as a property of morphisms of schemes. For a morphism
  locally of finite type it is the relative dimension `≤ d`.

## Main results

* `AlgebraicGeometry.fiberDimensionLE_iff_forall_topologicalKrullDim_fiber_le`: the pointwise
  bound is the bound on the dimension of each whole fibre.
* `AlgebraicGeometry.exists_fiberDimensionLE_baseChange_of_limitBaseChange`: if the base change
  of `f₀ : X₀ ⟶ Y₀` to the limit of a cofiltered inverse system of schemes with affine
  transition morphisms satisfies the bound, then so does its base change to some stage.
* `AlgebraicGeometry.Space.fiberDimensionLE_chartMap_of_hasRelativeDimensionLE` and
  `AlgebraicGeometry.Space.hasRelativeDimensionLE_of_holdsOnSurjectiveEtaleChart`: a
  relative-dimension bound for a morphism of algebraic spaces gives the fibre-dimension bound on
  the morphism of charts of every square of étale charts, and conversely one square whose chart
  of the source is surjective suffices.

## References

* [Stacks Project, Tag 02NJ](https://stacks.math.columbia.edu/tag/02NJ)
* [Stacks Project, Tag 04NL](https://stacks.math.columbia.edu/tag/04NL)
* [Stacks Project, Tag 04NM](https://stacks.math.columbia.edu/tag/04NM)
* [Stacks Project, Tag 05M5](https://stacks.math.columbia.edu/tag/05M5)
* [Stacks Project, Tag 06LR](https://stacks.math.columbia.edu/tag/06LR)
* [Stacks Project, Tag 0D4K](https://stacks.math.columbia.edu/tag/0D4K)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe w v u

namespace AlgebraicGeometry

/-! ### The fibre-dimension bound as a property of morphisms of schemes -/

/-- The bound `≤ d` on the local dimension of the fibre through each point of the source, as a
property of morphisms of schemes. For a morphism locally of finite type this is the relative
dimension `≤ d`. -/
@[ega "IV 9.3.1" "special case"]
def fiberDimensionLE (d : ℕ) : MorphismProperty Scheme.{u} :=
  fun _ _ f ↦ ∀ x, topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) ≤ (d : WithBot ℕ∞)

/-- On a morphism locally of finite type the fibre-dimension bound is the relative dimension
`≤ d`. -/
theorem fiberDimensionLE_iff_relativeDimensionLE {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (d : ℕ) :
    fiberDimensionLE d f ↔ RelativeDimensionLE f d :=
  Iff.rfl

/-- The fibre-dimension bound respects isomorphisms. -/
instance fiberDimensionLE_respectsIso (d : ℕ) :
    (fiberDimensionLE.{u} d).RespectsIso := by
  refine MorphismProperty.RespectsIso.mk _ (fun {X Y Z} e f hf x ↦ ?_) (fun {X Y Z} e f hf x ↦ ?_)
  · rw [topologicalKrullDimAt_fiber_eq_of_etale_square (e.hom ≫ f) e.hom (𝟙 Z) f (by simp) x]
    exact hf (e.hom x)
  · rw [topologicalKrullDimAt_fiber_eq_of_etale_square (f ≫ e.hom) (𝟙 X) e.inv f (by simp) x]
    exact hf ((𝟙 X) x)

/-- The pointwise bound on the local dimension of the fibres is the bound on the dimension of
each whole fibre. -/
theorem fiberDimensionLE_iff_forall_topologicalKrullDim_fiber_le {X Y : Scheme.{u}} (f : X ⟶ Y)
    (d : ℕ) :
    fiberDimensionLE d f ↔ ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (d : WithBot ℕ∞) := by
  refine ⟨fun h y ↦ ?_, fun h x ↦ (topologicalKrullDimAt_le_topologicalKrullDim _).trans (h (f x))⟩
  rw [topologicalKrullDim_eq_iSup_localKrullDim]
  refine iSup_le fun z ↦ ?_
  rw [← topologicalKrullDimAt_eq_localKrullDim, ← Scheme.Hom.topologicalKrullDimAt_fiber_fiberι]
  exact h _

/-! ### Descending the bound along a limit of schemes -/

/-- Let `D` be a cofiltered inverse system of
quasi-compact quasi-separated schemes with affine transition morphisms and limit `c`, and let
`f₀ : X₀ ⟶ Y₀` be a morphism of quasi-compact quasi-separated schemes over a stage `D.obj i₀`,
locally of finite type. If the base change of `f₀` to the limit has all fibres of local
dimension at most `d`, then so does its base change to some later stage. -/
theorem exists_fiberDimensionLE_baseChange_of_limitBaseChange
    {I : Type v} [Category.{w} I] [IsCofiltered I] [EssentiallySmall.{u} I]
    (D : I ⥤ Scheme.{u}) {c : Cone D} (hc : IsLimit c) (i₀ : I)
    (X₀ Y₀ : Over (D.obj i₀)) (f₀ : X₀ ⟶ Y₀) (d : ℕ)
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    [CompactSpace X₀.left] [QuasiSeparatedSpace X₀.left]
    [CompactSpace Y₀.left] [QuasiSeparatedSpace Y₀.left]
    [LocallyOfFiniteType f₀.left]
    (hlim : fiberDimensionLE d ((Over.pullback (c.π.app i₀)).map f₀).left) :
    ∃ (i : I) (g : i ⟶ i₀), fiberDimensionLE d ((Over.pullback (D.map g)).map f₀).left := by
  classical
  let X : Over i₀ ⥤ Scheme.{u} := baseChangeDiagram D i₀ X₀
  let Y : Over i₀ ⥤ Scheme.{u} := baseChangeDiagram D i₀ Y₀
  let f : X ⟶ Y := baseChangeDiagramMap D i₀ f₀
  let cX : Cone X := baseChangeCone D c i₀ X₀
  let cY : Cone Y := baseChangeCone D c i₀ Y₀
  have hcX : IsLimit cX := baseChangeConeIsLimit D hc i₀ X₀
  have hcY : IsLimit cY := baseChangeConeIsLimit D hc i₀ Y₀
  let : ∀ {a b : Over i₀} (g : a ⟶ b), IsAffineHom (Y.map g) := fun g ↦
    isAffineHom_baseChangeDiagram_map D i₀ Y₀ g
  let : ∀ a : Over i₀, CompactSpace (X.obj a) := fun a ↦
    compactSpace_baseChangeDiagram_obj D i₀ X₀ a
  let : ∀ a : Over i₀, QuasiSeparatedSpace (X.obj a) := fun a ↦
    quasiSeparatedSpace_baseChangeDiagram_obj D i₀ X₀ a
  let : ∀ a : Over i₀, CompactSpace (Y.obj a) := fun a ↦
    compactSpace_baseChangeDiagram_obj D i₀ Y₀ a
  let : ∀ a : Over i₀, QuasiSeparatedSpace (Y.obj a) := fun a ↦
    quasiSeparatedSpace_baseChangeDiagram_obj D i₀ Y₀ a
  let : ∀ a : Over i₀, LocallyOfFiniteType (f.app a) := fun a ↦
    show LocallyOfFiniteType (baseChangeMap (D.map a.hom) X₀ Y₀ f₀) from
      MorphismProperty.of_isPullback (baseChangeMap_isPullback (D.map a.hom) X₀ Y₀ f₀).flip
        inferInstance
  let : ∀ a : Over i₀, QuasiCompact (f.app a) := fun a ↦ inferInstance
  let : ∀ {a b : Over i₀} (g : a ⟶ b),
      IsClosedImmersion (pullback.lift (X.map g) (f.app a) (f.naturality g)) := by
    intro a b g
    have hsq := baseChangeDiagramMap_isPullback D i₀ f₀ g
    rw [show pullback.lift (X.map g) (f.app a) (f.naturality g) = hsq.isoPullback.hom from
      pullback.hom_ext (by rw [pullback.lift_fst, hsq.isoPullback_hom_fst])
        (by rw [pullback.lift_snd, hsq.isoPullback_hom_snd])]
    infer_instance
  have hlift : hcY.lift ((Cone.postcompose f).obj cX) = baseChangeMap (c.π.app i₀) X₀ Y₀ f₀ := by
    refine hcY.hom_ext fun a ↦ ?_
    rw [hcY.fac]
    exact (baseChangeCone_π_isPullback D i₀ f₀ c a).w
  have hdim : ∀ s : cY.pt,
      topologicalKrullDim ((hcY.lift ((Cone.postcompose f).obj cX)).fiber s) ≤
        (d : WithBot ℕ∞) := by
    rw [hlift]
    exact (fiberDimensionLE_iff_forall_topologicalKrullDim_fiber_le _ d).mp
      ((baseChangeMap_prop_iff (fiberDimensionLE d) (c.π.app i₀) X₀ Y₀ f₀).mpr hlim)
  obtain ⟨a, ha⟩ :=
    AlgebraicGeometry.exists_forall_topologicalKrullDim_fiber_le_of_isLimit_of_essentiallySmall
      X Y f cX hcX cY hcY d hdim
  exact ⟨a.left, a.hom, (baseChangeMap_prop_iff (fiberDimensionLE d) (D.map a.hom) X₀ Y₀ f₀).mp
    ((fiberDimensionLE_iff_forall_topologicalKrullDim_fiber_le _ d).mpr ha)⟩

/-! ### Reading the bound off a square of étale charts -/

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A local dimension bounded by a natural number `d` is the image of a natural number
`e ≤ d`. -/
private theorem exists_nat_topologicalKrullDimAt_eq {Z : Type u} [TopologicalSpace Z] (z : Z)
    (d : ℕ) (h : topologicalKrullDimAt Z z ≤ (d : WithBot ℕ∞)) :
    ∃ e : ℕ, e ≤ d ∧ topologicalKrullDimAt Z z = ((e : ℕ∞) : WithBot ℕ∞) := by
  obtain ⟨⟨U, hzU, _, hval⟩, -⟩ := topologicalKrullDimAt_isLeast Z z
  have hbot : topologicalKrullDimAt Z z ≠ ⊥ := by
    rw [hval, Ne, topologicalKrullDim_eq_bot_iff_isEmpty]
    exact fun hempty ↦ hempty.elim ⟨z, hzU⟩
  cases hdimval : topologicalKrullDimAt Z z with
  | bot => exact absurd hdimval hbot
  | coe r =>
    cases r with
    | top =>
      rw [hdimval] at h
      exact absurd (WithBot.coe_le_coe.mp h) (by simp)
    | coe m =>
      refine ⟨m, ?_, rfl⟩
      rw [hdimval] at h
      exact_mod_cast WithBot.coe_le_coe.mp h

/-- A relative-dimension bound for a morphism of algebraic spaces bounds the local dimension of
the fibres of the morphism of charts of every commuting square of étale charts. -/
theorem fiberDimensionLE_chartMap_of_hasRelativeDimensionLE (f : F ⟶ G) (d : ℕ)
    (hf : HasRelativeDimensionLE d B S hS f) :
    HoldsOnEveryEtaleChart B S hS (fiberDimensionLE d) f := by
  intro U V a b h ha hb hcomm u
  obtain ⟨e, hed, he⟩ :=
    hf (pointsMap B S hS (yoneda.obj U) a ((pointsEquivScheme B S hS U).symm u))
  rw [(hasRelativeDimensionAt_pointsMap_iff B S hS (e : ℕ∞) f U V a b h ha hb hcomm u).mp he]
  exact WithBot.coe_le_coe.mpr (by exact_mod_cast hed)

/-- Conversely, a bound on the local dimension of the fibres of the morphism of charts of one
commuting square of étale charts whose chart of the source is surjective bounds the relative
dimension of the morphism of algebraic spaces. -/
theorem hasRelativeDimensionLE_of_holdsOnSurjectiveEtaleChart
    (hF : IsAlgebraicSpace B S hS F) (f : F ⟶ G) (d : ℕ)
    (hf : HoldsOnSurjectiveEtaleChart B S hS (fiberDimensionLE d) f) :
    HasRelativeDimensionLE d B S hS f := by
  obtain ⟨U, V, a, b, h, ha, hb, hs, hcomm, hP⟩ := hf
  intro x
  obtain ⟨q, rfl⟩ := (presheafSurjective_iff_isSurjective_yoneda B S hS F hF U a).mp hs x
  obtain ⟨e, hed, hee⟩ := exists_nat_topologicalKrullDimAt_eq _ d
    (hP (pointsEquivScheme B S hS U q))
  refine ⟨e, hed, ?_⟩
  have := (hasRelativeDimensionAt_pointsMap_iff B S hS (e : ℕ∞) f U V a b h ha hb hcomm
    (pointsEquivScheme B S hS U q)).mpr hee
  rwa [Equiv.symm_apply_apply] at this

end Space

end AlgebraicGeometry

end
