module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ConnectedComponentSection.BaseChange
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ConnectedComponentSection.FibreConnectedness
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.ConditionalStatements
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The sectioned locus of a base change

Tag 057I is proved by descending the locus `X⁰` of fibrewise connected components along the
first projection of a multisection pullback. This file sets up the sectioned morphisms that
occur, records what Tags 055P and 055R say about their loci, and proves the two facts about
them which the descent needs: that the locus contains every fibre which is geometrically
connected, and that the loci attached to two sections agree wherever the two sections select
the same connected component.

## Main definitions

* `AlgebraicGeometry.ConnectedComponentSection.ofSection` packages a morphism with a section as a
  `AlgebraicGeometry.ConnectedAlongSection`.
* `AlgebraicGeometry.ConnectedComponentSection.sectionedPullback` is the base change of a morphism
  along a map which factors through it, sectioned by the chosen factorization.

## Main results

* `AlgebraicGeometry.ConnectedComponentSection.isLocallyConstructible_locus` and
  `AlgebraicGeometry.ConnectedComponentSection.isOpen_locus` are Tags 055P and 055R, taken as
  hypotheses in the shape of `AlgebraicGeometry.Statement055P` and
  `AlgebraicGeometry.Statement055R`.
* `AlgebraicGeometry.ConnectedComponentSection.mem_locus_of_geometricallyConnected_fiber`: a
  geometrically connected fibre lies entirely in `X⁰`.
* `AlgebraicGeometry.ConnectedComponentSection.sectionedPullback_locus_eq_preimage` is Tag 055M
  for the sectioned base changes occurring here.
* `AlgebraicGeometry.ConnectedComponentSection.locus_congr_of_cross_component` compares the loci
  of two sections of one morphism.
* `AlgebraicGeometry.ConnectedComponentSection.exists_nhd_cross_section` produces the
  neighbourhood of the base point on which the two tautological sections of the double
  multisection pullback select the same fibrewise connected component.

## Implementation notes

`AlgebraicGeometry.ConnectedComponentSection.ofSection` and
`AlgebraicGeometry.ConnectedComponentSection.sectionedPullback` are reducible, so that the
instances attached to the morphism being base changed are found for the
field `AlgebraicGeometry.ConnectedAlongSection.f` of the resulting structure. The two
conditional statements are applied with their instance arguments made explicit, so that no
instance has to be found for a projection of a structure built in a proof.

## References

* [Stacks Project, Tag 055M](https://stacks.math.columbia.edu/tag/055M)
* [Stacks Project, Tag 055P](https://stacks.math.columbia.edu/tag/055P)
* [Stacks Project, Tag 055R](https://stacks.math.columbia.edu/tag/055R)
* [Stacks Project, Tag 057I](https://stacks.math.columbia.edu/tag/057I)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Morphisms Topology

universe u

namespace AlgebraicGeometry.ConnectedComponentSection

/-- A morphism together with a section, as a `AlgebraicGeometry.ConnectedAlongSection`. -/
abbrev ofSection {X Y : Scheme.{u}} (F : X ⟶ Y) (s : Y ⟶ X) (hs : s ≫ F = 𝟙 Y) :
    ConnectedAlongSection.{u} := ⟨X, Y, F, s, hs⟩

/-- The base change of `f : X ⟶ Y` along `k : P ⟶ Y`, sectioned by a factorization `t` of `k`
through `f`. -/
noncomputable abbrev sectionedPullback {X Y P : Scheme.{u}} (f : X ⟶ Y) (k : P ⟶ Y)
    (t : P ⟶ X) (ht : t ≫ f = k) : ConnectedAlongSection.{u} :=
  ofSection (pullback.snd f k)
    (pullback.lift t (𝟙 P) (ht.trans (Category.id_comp k).symm)) (pullback.lift_snd _ _ _)

/-- The fibrewise connected component selected by the section is the connected component of the
point the section selects. -/
theorem fiberComponent_eq_connectedComponent (D : ConnectedAlongSection.{u}) (z : D.Y) :
    D.fiberComponent z = connectedComponent (D.sectionPoint z) := rfl

/-- **Stacks Project, Tag 055P**, in the shape of `AlgebraicGeometry.Statement055P`. -/
theorem isLocallyConstructible_locus (h055P : Statement055P.{u})
    (D : ConnectedAlongSection.{u}) (hlfp : LocallyOfFinitePresentation D.f)
    (hqc : QuasiCompact D.f) (hqs : QuasiSeparated D.f) :
    IsLocallyConstructible D.locus := @h055P D hlfp hqc hqs

/-- **Stacks Project, Tag 055R**, in the shape of `AlgebraicGeometry.Statement055R`. -/
theorem isOpen_locus (h055R : Statement055R.{u}) (D : ConnectedAlongSection.{u})
    (hfp : FinitePresentation D.f) (hflat : Flat D.f)
    (hred : GeometricallyReduced D.f) : IsOpen D.locus := @h055R D hfp hflat hred

/-- Granted Tag 055R, the locus of a sectioned base change of a flat, finitely presented
morphism with geometrically reduced fibres is open. -/
theorem sectionedPullback_locus_isOpen (h055R : Statement055R.{u})
    {X Y P : Scheme.{u}} (f : X ⟶ Y) (k : P ⟶ Y) (t : P ⟶ X) (ht : t ≫ f = k)
    (hfp : FinitePresentation f) (hflat : Flat f)
    (hreduced : ∀ y : Y, GeometricallyReduced (f.fiberToSpecResidueField y)) :
    IsOpen (sectionedPullback f k t ht).locus := by
  let : LocallyOfFinitePresentation f := hfp.locallyOfFinitePresentation
  let : QuasiCompact f := hfp.quasiCompact
  let : QuasiSeparated f := hfp.quasiSeparated
  let : Flat f := hflat
  let : GeometricallyReduced f := geometricallyReduced_of_fibers f hreduced
  exact isOpen_locus h055R _
    (FinitePresentation.mk inferInstance inferInstance inferInstance)
    inferInstance inferInstance

/-- A point in the image of the fibre inclusion over `y` lies over `y`. -/
private theorem apply_eq_of_fiberι_eq {X Y : Scheme.{u}} (F : X ⟶ Y) {y : Y} {x : F.fiber y}
    {a : X} (h : F.fiberι y x = a) : F a = y := by
  have : a ∈ Set.range (F.fiberι y) := ⟨x, h⟩
  rw [F.range_fiberι] at this
  simpa using this

/-- A section of `F` sends each point of the base to a point lying over it. -/
private theorem apply_section {X Y : Scheme.{u}} {F : X ⟶ Y} {s : Y ⟶ X} (hs : s ≫ F = 𝟙 Y)
    (y : Y) : F (s y) = y := by
  simpa using congrArg (fun m : Y ⟶ Y => m y) hs

/-- The two projections of a pullback agree on points after composing with the structure maps. -/
private theorem pullback_condition_apply {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    (e : ↥(pullback f g)) : f (pullback.fst f g e) = g (pullback.snd f g e) := by
  simpa using congrArg (fun φ : pullback f g ⟶ Z => φ e) (pullback.condition (f := f) (g := g))

/-- A point whose fibre is geometrically connected lies in the sectioned locus `X⁰`. -/
theorem mem_locus_of_geometricallyConnected_fiber (D : ConnectedAlongSection.{u}) (z : D.Y)
    (hconn : GeometricallyConnected (D.f.fiberToSpecResidueField z)) (e : D.X)
    (he : D.f e = z) : e ∈ D.locus := by
  subst he
  let : GeometricallyConnected (D.f.fiberToSpecResidueField (D.f e)) := hconn
  have : ConnectedSpace (D.f.fiber (D.f e)) :=
    GeometricallyConnected.connectedSpace_of_subsingleton
      (f := D.f.fiberToSpecResidueField (D.f e))
  refine (D.mem_locus e).mpr ⟨D.f e, D.f.asFiber e, ?_, D.f.fiberι_asFiber e⟩
  rw [fiberComponent_eq_connectedComponent, PreconnectedSpace.connectedComponent_eq_univ]
  trivial

/-- Every point of a geometrically connected fibre of `f` lies in the locus of the sectioned
base change of `f` along a map through which the section factors. -/
theorem mem_sectionedPullback_locus_of_fiber {X Y P : Scheme.{u}} (f : X ⟶ Y) (k : P ⟶ Y)
    (t : P ⟶ X) (ht : t ≫ f = k) (y : Y)
    (hconn : GeometricallyConnected (f.fiberToSpecResidueField y))
    (e : ↥(pullback f k)) (he : (pullback.fst f k ≫ f) e = y) :
    e ∈ (sectionedPullback f k t ht).locus := by
  have hy : k ((pullback.snd f k) e) = y := (pullback_condition_apply f k e).symm.trans he
  refine mem_locus_of_geometricallyConnected_fiber (sectionedPullback f k t ht)
    ((pullback.snd f k) e) ?_ e rfl
  exact pullback_fiber_geometricallyConnected f k ((pullback.snd f k) e) (by rw [hy]; exact hconn)

/-- **Stacks Project, Tag 055M** for a sectioned base change: the locus of the base change of
`f` along `k` is the preimage, under a cartesian comparison map over `π`, of the locus of the
base change along `g`. -/
@[sga "3 VIB 4.2" "more general"]
theorem sectionedPullback_locus_eq_preimage {X Y Z P : Scheme.{u}} (f : X ⟶ Y) (g : Z ⟶ Y)
    (σ : Z ⟶ X) (hσ : σ ≫ f = g) (π : P ⟶ Z) (k : P ⟶ Y)
    (ht : (π ≫ σ) ≫ f = k) (m : pullback f k ⟶ pullback f g)
    (hm : IsPullback m (pullback.snd f k) (pullback.snd f g) π)
    (hmfst : m ≫ pullback.fst f g = pullback.fst f k) :
    (sectionedPullback f k (π ≫ σ) ht).locus =
      m ⁻¹' (sectionedPullback f g σ hσ).locus := by
  refine ConnectedAlongSection.locus_eq_preimage_of_isPullback (sectionedPullback f g σ hσ)
    (sectionedPullback f k (π ≫ σ) ht) m π hm ?_
  have e₁ : (sectionedPullback f k (π ≫ σ) ht).s ≫ pullback.fst f k = π ≫ σ :=
    pullback.lift_fst _ _ _
  have e₂ : (sectionedPullback f k (π ≫ σ) ht).s ≫ pullback.snd f k = 𝟙 P :=
    pullback.lift_snd _ _ _
  have e₃ : (sectionedPullback f g σ hσ).s ≫ pullback.fst f g = σ := pullback.lift_fst _ _ _
  have e₄ : (sectionedPullback f g σ hσ).s ≫ pullback.snd f g = 𝟙 Z := pullback.lift_snd _ _ _
  apply pullback.hom_ext
  · rw [Category.assoc, hmfst, e₁, Category.assoc, e₃]
  · rw [Category.assoc, hm.w, ← Category.assoc, e₂, Category.id_comp, Category.assoc, e₄,
      Category.comp_id]

/-- The loci attached to two sections of one morphism agree over any set of base points at
which the two sections select the same fibrewise connected component. -/
theorem locus_congr_of_cross_component {X Y : Scheme.{u}} (F : X ⟶ Y) (s₀ s₁ : Y ⟶ X)
    (hs₀ : s₀ ≫ F = 𝟙 Y) (hs₁ : s₁ ≫ F = 𝟙 Y) (S : Set Y)
    (hcross₀₁ : ∀ y ∈ S, (ofSection F s₀ hs₀).sectionPoint y ∈
      connectedComponent ((ofSection F s₁ hs₁).sectionPoint y))
    (hcross₁₀ : ∀ y ∈ S, (ofSection F s₁ hs₁).sectionPoint y ∈
      connectedComponent ((ofSection F s₀ hs₀).sectionPoint y))
    (a : X) (ha : F a ∈ S) :
    a ∈ (ofSection F s₀ hs₀).locus ↔ a ∈ (ofSection F s₁ hs₁).locus := by
  have key : ∀ (t₀ t₁ : Y ⟶ X) (ht₀ : t₀ ≫ F = 𝟙 Y) (ht₁ : t₁ ≫ F = 𝟙 Y),
      (∀ y ∈ S, (ofSection F t₀ ht₀).sectionPoint y ∈
        connectedComponent ((ofSection F t₁ ht₁).sectionPoint y)) →
      a ∈ (ofSection F t₀ ht₀).locus → a ∈ (ofSection F t₁ ht₁).locus := by
    intro t₀ t₁ ht₀ ht₁ hcross hmem
    obtain ⟨y, x, hxcomp, hxa⟩ := ((ofSection F t₀ ht₀).mem_locus a).mp hmem
    have hy : y ∈ S := apply_eq_of_fiberι_eq F hxa ▸ ha
    refine ((ofSection F t₁ ht₁).mem_locus a).mpr ⟨y, x, ?_, hxa⟩
    rw [fiberComponent_eq_connectedComponent] at hxcomp ⊢
    rw [← connectedComponent_eq_iff_mem.mpr (hcross y hy)]
    exact hxcomp
  exact ⟨key s₀ s₁ hs₀ hs₁ hcross₀₁, key s₁ s₀ hs₁ hs₀ hcross₁₀⟩

/-- If the value of one section lies in the locus attached to another section, then the two
sections select the same fibrewise connected component there. -/
theorem sectionPoint_mem_connectedComponent_of_mem_locus {X Y : Scheme.{u}} (F : X ⟶ Y)
    (s₀ s₁ : Y ⟶ X) (hs₀ : s₀ ≫ F = 𝟙 Y) (hs₁ : s₁ ≫ F = 𝟙 Y) (y : Y)
    (h : s₀ y ∈ (ofSection F s₁ hs₁).locus) :
    (ofSection F s₀ hs₀).sectionPoint y ∈
      connectedComponent ((ofSection F s₁ hs₁).sectionPoint y) := by
  obtain ⟨y', x, hxcomp, hx⟩ := ((ofSection F s₁ hs₁).mem_locus (s₀ y)).mp h
  have hy' : y' = y := (apply_eq_of_fiberι_eq F hx).symm.trans (apply_section hs₀ y)
  subst y'
  have hfi : F.fiberι y ((ofSection F s₀ hs₀).sectionPoint y) = s₀ y :=
    (ofSection F s₀ hs₀).fiberι_sectionPoint y
  have hxpoint : x = (ofSection F s₀ hs₀).sectionPoint y :=
    (F.fiberι y).isEmbedding.injective (by rw [hfi, ← hx])
  rw [← hxpoint]
  rw [fiberComponent_eq_connectedComponent] at hxcomp
  exact hxcomp

/-- Granted Tag 055R, the two tautological sections of the base change of `f` along
`Z ×_Y Z ⟶ Y` select the same fibrewise connected component over a neighbourhood of `y`. -/
theorem exists_nhd_cross_section (h055R : Statement055R.{u})
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Z ⟶ Y) (y : Y)
    (hfp : FinitePresentation f) (hflat : Flat f) [IsFiniteLocallyFree g]
    (hreduced : ∀ y' : Y, GeometricallyReduced (f.fiberToSpecResidueField y'))
    (hconnected : GeometricallyConnected (f.fiberToSpecResidueField y))
    {σ : Z ⟶ X} (hk₀ : (pullback.fst g g ≫ σ) ≫ f = pullback.fst g g ≫ g)
    (hk₁ : (pullback.snd g g ≫ σ) ≫ f = pullback.fst g g ≫ g) :
    ∃ V : Set Y, IsOpen V ∧ y ∈ V ∧ ∀ w : ↥(pullback g g),
      (pullback.fst g g ≫ g) w ∈ V →
        (sectionedPullback f (pullback.fst g g ≫ g) (pullback.fst g g ≫ σ) hk₀).sectionPoint w ∈
            connectedComponent ((sectionedPullback f (pullback.fst g g ≫ g)
              (pullback.snd g g ≫ σ) hk₁).sectionPoint w) ∧
          (sectionedPullback f (pullback.fst g g ≫ g)
              (pullback.snd g g ≫ σ) hk₁).sectionPoint w ∈
            connectedComponent ((sectionedPullback f (pullback.fst g g ≫ g)
              (pullback.fst g g ≫ σ) hk₀).sectionPoint w) := by
  have hflf :=
    (isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation g).mp inferInstance
  let : IsFinite g := hflf.1
  let : IsFinite (pullback.fst g g ≫ g) := inferInstance
  have hO : IsOpen ((sectionedPullback f (pullback.fst g g ≫ g)
      (pullback.fst g g ≫ σ) hk₀).s ⁻¹'
      (sectionedPullback f (pullback.fst g g ≫ g) (pullback.snd g g ≫ σ) hk₁).locus) :=
    (sectionedPullback_locus_isOpen h055R f (pullback.fst g g ≫ g) (pullback.snd g g ≫ σ)
      hk₁ hfp hflat hreduced).preimage
      (sectionedPullback f (pullback.fst g g ≫ g) (pullback.fst g g ≫ σ) hk₀).s.continuous
  have hfiber : ∀ w : ↥(pullback g g), (pullback.fst g g ≫ g) w = y →
      w ∈ (sectionedPullback f (pullback.fst g g ≫ g) (pullback.fst g g ≫ σ) hk₀).s ⁻¹'
        (sectionedPullback f (pullback.fst g g ≫ g) (pullback.snd g g ≫ σ) hk₁).locus := by
    intro w hwy
    refine mem_sectionedPullback_locus_of_fiber f (pullback.fst g g ≫ g)
      (pullback.snd g g ≫ σ) hk₁ y hconnected _ ?_
    have hsnd := apply_section (F := pullback.snd f (pullback.fst g g ≫ g))
      (s := (sectionedPullback f (pullback.fst g g ≫ g) (pullback.fst g g ≫ σ) hk₀).s)
      (pullback.lift_snd _ _ _) w
    exact (pullback_condition_apply f _ _).trans ((congrArg _ hsnd).trans hwy)
  obtain ⟨V, hVopen, hyV, hVk⟩ := exists_open_neighborhood_preimage_subset
    (pullback.fst g g ≫ g) (pullback.fst g g ≫ g).isClosedMap y _ hO hfiber
  refine ⟨V, hVopen, hyV, fun w hw => ?_⟩
  have hcross := sectionPoint_mem_connectedComponent_of_mem_locus
    (pullback.snd f (pullback.fst g g ≫ g))
    (sectionedPullback f (pullback.fst g g ≫ g) (pullback.fst g g ≫ σ) hk₀).s
    (sectionedPullback f (pullback.fst g g ≫ g) (pullback.snd g g ≫ σ) hk₁).s
    (pullback.lift_snd _ _ _) (pullback.lift_snd _ _ _) w (hVk hw)
  refine ⟨hcross, ?_⟩
  rw [connectedComponent_eq_iff_mem.mpr hcross]
  exact mem_connectedComponent

end AlgebraicGeometry.ConnectedComponentSection

end
