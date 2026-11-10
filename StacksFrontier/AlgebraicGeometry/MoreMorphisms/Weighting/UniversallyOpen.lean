module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import StacksFrontier.AlgebraicGeometry.Flatness.FiniteNeighborhood
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.BaseChange
public import StacksCore.Tactic.StacksAttribute

/-!
# Positive weightings and universal openness

A locally quasi-finite morphism carrying an everywhere positive weighting is universally open.

## Main results

* `AlgebraicGeometry.universallyOpen_of_positive_weighting`: a locally quasi-finite morphism with
  an everywhere positive weighting is universally open.

## Implementation notes

Local quasi-finiteness is `AlgebraicGeometry.LocallyOfFiniteType` together with
`AlgebraicGeometry.LocallyQuasiFinite`, and universal openness is Mathlib's
`AlgebraicGeometry.UniversallyOpen`.

Openness of the image is checked at a point `x` by passing to an elementary étale neighbourhood
of `f x` over which an open piece of the base change is finite with a single point over the
distinguished point. The weighted fibre sum of that piece is locally constant, and it is
positive at the distinguished point because the fibre there is nonempty and the weight is
positive; so the locus where it keeps that value is an open subset of the neighbourhood
contained in the image, whose image in the target is an open neighbourhood of `f x` inside the
image of `f`. Openness of an arbitrary open subset follows by restricting the weighting, and
universal openness follows because a weighting pulls back along any base change.

## References

* [Stacks Project, Tag 0F3C](https://stacks.math.columbia.edu/tag/0F3C)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The image of a locally quasi-finite morphism with an everywhere positive weighting is
open. -/
private theorem isOpen_range_of_positive_weighting {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [LocallyQuasiFinite f] {w : X → ℤ}
    (hw : IsWeighting f w) (hpositive : ∀ x, 0 < w x) :
    IsOpen (Set.range f) := by
  rw [isOpen_iff_forall_mem_open]
  rintro _ ⟨x, rfl⟩
  have hxiso : IsIsolatedPoint (f.asFiber x) :=
    (quasiFiniteAt_tfae f x).out 1 2 rfl rfl (by decide) (by decide) |>.mp
      ((forall_quasiFiniteAt_iff f).mpr ⟨inferInstance, inferInstance⟩ x)
  let Nbh : Stacks.Flatness.FiniteNeighborhoodAt f x :=
    Classical.choice (Stacks.Flatness.exists_etaleNeighborhood_finiteAt f x hxiso)
  let U := Nbh.neighborhood
  let V := Nbh.openSubscheme
  let π : ↑V ⟶ U.scheme := V.ι ≫ pullback.snd f U.toBase
  let h : ↑V ⟶ X := V.ι ≫ pullback.fst f U.toBase
  have hcomm : h ≫ f = π ≫ U.toBase := by
    dsimp [h, π]
    simp only [Category.assoc, pullback.condition]
  have hlift : pullback.lift h π hcomm = V.ι := by
    apply pullback.hom_ext
    · simp [h]
    · simp [π]
  have hopen : IsOpenImmersion (pullback.lift h π hcomm) := by
    rw [hlift]
    infer_instance
  have hfinite : IsFinite π := Nbh.spec.1
  obtain ⟨v, hv, -⟩ := Nbh.spec.2.1
  have hsumpos : 0 < separableDegreeWeightedFiberSum π (w ∘ h) U.point :=
    separableDegreeWeightedFiberSum_pos π (fun t ↦ π.finite_preimage_singleton t) (w ∘ h)
      (fun z ↦ hpositive (h z)) U.point ⟨v, by simpa [π] using hv⟩
  let s : U.scheme → ℤ := separableDegreeWeightedFiberSum π (w ∘ h)
  let N : Set U.scheme := {z | s z = s U.point}
  have hNopen : IsOpen N :=
    (hw.isLocallyConstant h π U.toBase hcomm inferInstance hopen hfinite).isOpen_fiber (s U.point)
  have hNrange : N ⊆ Set.range π := by
    intro z hz
    by_contra hznot
    have hzπ : ∀ a : ↑V, π a ≠ z := fun a hπa ↦ hznot ⟨a, hπa⟩
    have hzero : s z = 0 := by
      classical
      dsimp [s, separableDegreeWeightedFiberSum]
      rw [finsum_eq_zero_of_forall_eq_zero]
      intro a
      simp [hzπ a]
    change s z = s U.point at hz
    change 0 < s U.point at hsumpos
    rw [← hz, hzero] at hsumpos
    omega
  have himage : U.toBase '' N ⊆ Set.range f := by
    rintro y' ⟨z, hzN, hy'z⟩
    obtain ⟨a, ha⟩ := hNrange hzN
    refine ⟨h a, ?_⟩
    have hcompapp : f (h a) = U.toBase (π a) := by
      simpa only [Scheme.Hom.comp_apply] using congrArg (fun q : ↑V ⟶ Y => q a) hcomm
    rwa [hcompapp, ha]
  exact ⟨U.toBase '' N, himage, U.toBase.isOpenMap N hNopen, ⟨U.point, rfl, U.map_point⟩⟩

/-- A locally quasi-finite morphism with an everywhere positive weighting is an open map. -/
private theorem isOpenMap_of_positive_weighting {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [LocallyQuasiFinite f] {w : X → ℤ}
    (hw : IsWeighting f w) (hpositive : ∀ x, 0 < w x) : IsOpenMap f := by
  intro s hs
  let O : X.Opens := ⟨s, hs⟩
  let g : ↑O ⟶ Y := O.ι ≫ f
  have hrange : IsOpen (Set.range g) := isOpen_range_of_positive_weighting g
    (IsWeighting.comp_isOpenImmersion O.ι hw) fun x ↦ hpositive (O.ι x)
  have hrange_eq : Set.range g = f '' s := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨O.ι x, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  exact hrange_eq ▸ hrange

/-- **Stacks Project, Tag 0F3C.** A locally quasi-finite morphism carrying an everywhere
positive weighting is universally open. -/
@[stacks 0F3C]
theorem universallyOpen_of_positive_weighting {X Y : Scheme.{u}}
    {f : X ⟶ Y} [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    {w : X → ℤ} (hw : IsWeighting f w) (hpositive : ∀ x : X, 0 < w x) :
    UniversallyOpen f := by
  rw [universallyOpen_iff]
  refine MorphismProperty.universally_mk' _ f ?_
  intro T g _
  have hw' : IsWeighting (pullback.fst g f) (w ∘ pullback.snd g f) :=
    IsWeighting.comp_of_isPullback hw (IsPullback.of_hasPullback g f).flip
  exact isOpenMap_of_positive_weighting (pullback.fst g f) hw'
    fun x ↦ hpositive (pullback.snd g f x)

end AlgebraicGeometry
