module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ConnectedComponentSection.DescentTopology
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Pullback bookkeeping for Stacks Tag 057I

The proof of Tag 057I works on the pullback `X ×_Y Z` of a family `f : X ⟶ Y` along a finite
locally free multisection `g : Z ⟶ Y`, descends a subset of it along the first projection
`X ×_Y Z ⟶ X`, and compares the fibres of an open subscheme with the fibres of the ambient
scheme. The cartesian squares and the lifts that this needs are assembled here.

## Main results

* `AlgebraicGeometry.ConnectedComponentSection.finiteLocallyFree_isOpenMap_and_isClosedMap`: a
finite locally
  free morphism is both open and closed on underlying spaces.
* `AlgebraicGeometry.ConnectedComponentSection.compact_open_image_of_pullback_compatible_open`
descends a
  compact open which is invariant under the canonical equivalence relation of a morphism.
* `AlgebraicGeometry.ConnectedComponentSection.open_fiber_comparison_isPullback`,
  `AlgebraicGeometry.ConnectedComponentSection.open_fiber_comparison_isOpenEmbedding` and
  `AlgebraicGeometry.ConnectedComponentSection.open_fiber_comparison_range` identify the fibre of
  `U.ι ≫ f` with
  an open subset of the fibre of `f`.
* `AlgebraicGeometry.ConnectedComponentSection.pullback_map_isPullback_over_base` exhibits the
comparison map of
  a pullback base change as cartesian.
* `AlgebraicGeometry.ConnectedComponentSection.exists_relation_factorization` factors the canonical
relation of
  the first projection through the double multisection `Z ×_Y Z`.

## Implementation notes

The relation used for descent along `p : X ×_Y Z ⟶ X` is `p ×_X p`, and the factorization in
`AlgebraicGeometry.ConnectedComponentSection.exists_relation_factorization` is obtained by lifting
into the
pullback of `f` along `Z ×_Y Z ⟶ Y`. The two legs are then the two base changes of `p` along
the two projections of `Z ×_Y Z`, which is exactly the shape the base-change statement for the
sectioned locus expects.

## References

* [Stacks Project, Tag 057I](https://stacks.math.columbia.edu/tag/057I)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Morphisms Topology

universe u

namespace AlgebraicGeometry.ConnectedComponentSection

/-- A finite locally free morphism of schemes is open and closed on underlying spaces. -/
@[sga "3 VIA 2.4.1" "more general"]
theorem finiteLocallyFree_isOpenMap_and_isClosedMap
    {T S : Scheme.{u}} (h : T ⟶ S) [IsFiniteLocallyFree h] :
    IsOpenMap h ∧ IsClosedMap h := by
  obtain ⟨_, _, _⟩ :=
    (isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation h).mp inferInstance
  exact ⟨h.isOpenMap, h.isClosedMap⟩

/-- A compact open subset of the source of an open morphism which is invariant under the
canonical equivalence relation of that morphism descends to a compact open of the target, of
which it is the full preimage. -/
theorem compact_open_image_of_pullback_compatible_open
    {E B : Scheme.{u}} (p : E ⟶ B) (A : Set E)
    (hp : IsOpenMap p) (hopen : IsOpen A) (hcompact : IsCompact A)
    (hcompat : ∀ r : (pullback p p : Scheme),
      (pullback.fst p p) r ∈ A ↔ (pullback.snd p p) r ∈ A) :
    IsOpen (p '' A) ∧ IsCompact (p '' A) ∧ p ⁻¹' (p '' A) = A := by
  obtain ⟨himage, hpreimage⟩ :=
    open_image_eq_of_descent_relation p (pullback.fst p p) (pullback.snd p p)
      A hp hopen hcompat Scheme.Pullback.exists_preimage_pullback
  exact ⟨himage, hcompact.image p.continuous, hpreimage⟩

/-- The comparison map from the fibre of `U.ι ≫ f` to the fibre of `f` sits in a cartesian
square over the open immersion `U.ι`. -/
theorem open_fiber_comparison_isPullback
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : X.Opens) (y : Y) :
    IsPullback
      (pullback.map (U.ι ≫ f) (Y.fromSpecResidueField y)
        f (Y.fromSpecResidueField y) U.ι (𝟙 _) (𝟙 Y) (by simp) (by simp))
      (pullback.fst (U.ι ≫ f) (Y.fromSpecResidueField y))
      (pullback.fst f (Y.fromSpecResidueField y)) U.ι := by
  let g := Y.fromSpecResidueField y
  let j := pullback.map (U.ι ≫ f) g f g U.ι (𝟙 _) (𝟙 Y) (by simp) (by simp)
  have hp : j ≫ pullback.fst f g = pullback.fst (U.ι ≫ f) g ≫ U.ι := by
    dsimp [j, pullback.map]
    exact pullback.lift_fst _ _ _
  have houter : IsPullback (j ≫ pullback.snd f g)
      (pullback.fst (U.ι ≫ f) g) g (U.ι ≫ f) := by
    convert (IsPullback.of_hasPullback (U.ι ≫ f) g).flip using 1
    dsimp [j, pullback.map]
    simp
  exact houter.of_right hp (IsPullback.of_hasPullback f g).flip

/-- The comparison map from the fibre of `U.ι ≫ f` to the fibre of `f` is an open embedding. -/
theorem open_fiber_comparison_isOpenEmbedding
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : X.Opens) (y : Y) :
    IsOpenEmbedding
      (pullback.map (U.ι ≫ f) (Y.fromSpecResidueField y)
        f (Y.fromSpecResidueField y) U.ι (𝟙 _) (𝟙 Y) (by simp) (by simp)) := by
  have := MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    (open_fiber_comparison_isPullback f U y).flip (inferInstance : IsOpenImmersion U.ι)
  exact Scheme.Hom.isOpenEmbedding _

/-- The image of the comparison map from the fibre of `U.ι ≫ f` to the fibre of `f` is the
preimage of `U` under the fibre inclusion. -/
theorem open_fiber_comparison_range
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : X.Opens) (y : Y) :
    Set.range (pullback.map (U.ι ≫ f) (Y.fromSpecResidueField y)
      f (Y.fromSpecResidueField y) U.ι (𝟙 _) (𝟙 Y) (by simp) (by simp)) =
      (f.fiberι y) ⁻¹' (U : Set X) := by
  let j := pullback.map (U.ι ≫ f) (Y.fromSpecResidueField y)
    f (Y.fromSpecResidueField y) U.ι (𝟙 _) (𝟙 Y) (by simp) (by simp)
  have h := open_fiber_comparison_isPullback f U y
  ext x
  refine ⟨?_, fun hx => ?_⟩
  · rintro ⟨a, rfl⟩
    have hw := congrArg (fun φ : (U.ι ≫ f).fiber y ⟶ X => φ a) h.w
    change f.fiberι y (j a) = U.ι ((pullback.fst (U.ι ≫ f) (Y.fromSpecResidueField y)) a) at hw
    rw [← U.range_ι]
    exact ⟨_, hw.symm⟩
  · obtain ⟨u, hu⟩ : f.fiberι y x ∈ Set.range U.ι := by rwa [U.range_ι]
    obtain ⟨w, hw₀, -⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := f.fiberι y) (g := U.ι) x u hu.symm
    refine ⟨h.isoPullback.inv w, ?_⟩
    have hw := congrArg (fun φ : pullback (f.fiberι y) U.ι ⟶ f.fiber y => φ w)
      h.isoPullback_inv_fst
    change (h.isoPullback.inv ≫ j) w = x
    exact hw.trans hw₀

/-- Base changing `f` along `π ≫ g` rather than along `g` is cartesian over `π`. -/
theorem pullback_map_isPullback_over_base
    {X Y Z P : Scheme.{u}} (f : X ⟶ Y) (g : Z ⟶ Y) (π : P ⟶ Z) :
    IsPullback
      (pullback.map f (π ≫ g) f g (𝟙 X) π (𝟙 Y) (by simp) (by simp))
      (pullback.snd f (π ≫ g)) (pullback.snd f g) π := by
  let m := pullback.map f (π ≫ g) f g (𝟙 X) π (𝟙 Y) (by simp) (by simp)
  have hp : m ≫ pullback.snd f g = pullback.snd f (π ≫ g) ≫ π := by
    dsimp [m, pullback.map]
    exact pullback.lift_snd _ _ _
  have houter : IsPullback (m ≫ pullback.fst f g)
      (pullback.snd f (π ≫ g)) f (π ≫ g) := by
    convert (IsPullback.of_hasPullback f (π ≫ g)) using 1
    dsimp [m, pullback.map]
    simp
  exact houter.of_right hp (IsPullback.of_hasPullback f g)

/-- The comparison map of a pullback base change is compatible with the first projections. -/
theorem pullback_map_fst
    {X Y Z P : Scheme.{u}} (f : X ⟶ Y) (g : Z ⟶ Y) (π : P ⟶ Z) :
    (pullback.map f (π ≫ g) f g (𝟙 X) π (𝟙 Y) (by simp) (by simp)) ≫ pullback.fst f g =
      pullback.fst f (π ≫ g) := by
  dsimp [pullback.map]
  simp

/-- `AlgebraicGeometry.ConnectedComponentSection.pullback_map_isPullback_over_base` and
`AlgebraicGeometry.ConnectedComponentSection.pullback_map_fst` for a base map presented as any
morphism equal to
`π ≫ g`, which is how the two projections of a double multisection occur. -/
theorem pullback_map_isPullback_over_base_of_eq
    {X Y Z P : Scheme.{u}} (f : X ⟶ Y) (g : Z ⟶ Y) (π : P ⟶ Z) (k : P ⟶ Y) (hk : k = π ≫ g)
    (w₁ : 𝟙 X ≫ f = f ≫ 𝟙 Y) (w₂ : k ≫ 𝟙 Y = π ≫ g) :
    IsPullback (pullback.map f k f g (𝟙 X) π (𝟙 Y) w₁ w₂) (pullback.snd f k)
        (pullback.snd f g) π ∧
      (pullback.map f k f g (𝟙 X) π (𝟙 Y) w₁ w₂) ≫ pullback.fst f g = pullback.fst f k := by
  subst hk
  exact ⟨pullback_map_isPullback_over_base f g π, pullback_map_fst f g π⟩

/-- The canonical relation of the first projection `X ×_Y Z ⟶ X` maps to the double
multisection `Z ×_Y Z`, compatibly with the two projections. -/
theorem exists_double_base_map
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Z ⟶ Y) :
    ∃ q : pullback (pullback.fst f g) (pullback.fst f g) ⟶ pullback g g,
      q ≫ pullback.fst g g =
        pullback.fst (pullback.fst f g) (pullback.fst f g) ≫ pullback.snd f g ∧
      q ≫ pullback.snd g g =
        pullback.snd (pullback.fst f g) (pullback.fst f g) ≫ pullback.snd f g :=
  ⟨pullback.map _ _ _ _ (pullback.snd f g) (pullback.snd f g) f
    pullback.condition pullback.condition, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

/-- A pair of maps into `X ×_Y Z` agreeing on `X` and covered over `Z ×_Y Z` factors through
the base change of `f` along `Z ×_Y Z ⟶ Y`, as the two base changes of that factorization. -/
theorem double_base_lift
    {X Y Z P R : Scheme.{u}} (f : X ⟶ Y) (g : Z ⟶ Y)
    (r₀ r₁ : R ⟶ pullback f g) (q : R ⟶ P) (π₀ π₁ : P ⟶ Z)
    (hr : r₀ ≫ pullback.fst f g = r₁ ≫ pullback.fst f g)
    (hq₀ : q ≫ π₀ = r₀ ≫ pullback.snd f g)
    (hq₁ : q ≫ π₁ = r₁ ≫ pullback.snd f g)
    (hk : π₀ ≫ g = π₁ ≫ g) :
    ∃ h : R ⟶ pullback f (π₀ ≫ g),
      h ≫ (pullback.map f (π₀ ≫ g) f g (𝟙 X) π₀ (𝟙 Y) (by simp) (by simp)) = r₀ ∧
      h ≫ (pullback.map f (π₀ ≫ g) f g (𝟙 X) π₁ (𝟙 Y)
        (by simp) (by simpa using hk)) = r₁ := by
  have hc : (r₀ ≫ pullback.fst f g) ≫ f = q ≫ (π₀ ≫ g) := by
    simp [pullback.condition, reassoc_of% hq₀]
  let h := pullback.lift (r₀ ≫ pullback.fst f g) q hc
  refine ⟨h, ?_, ?_⟩
  · apply pullback.hom_ext
    · dsimp [h, pullback.map]
      simp only [Category.assoc, pullback.lift_fst, Category.comp_id]
    · dsimp [h, pullback.map]
      rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd, hq₀]
  · apply pullback.hom_ext
    · dsimp [h, pullback.map]
      simpa only [Category.assoc, pullback.lift_fst, Category.comp_id] using hr
    · dsimp [h, pullback.map]
      rwa [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd]

/-- The two legs of the canonical relation of the first projection `X ×_Y Z ⟶ X` are the two
base changes, along the two projections of `Z ×_Y Z`, of a single map into the base change of
`f` along `Z ×_Y Z ⟶ Y`. -/
theorem exists_relation_factorization
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Z ⟶ Y) :
    ∃ h : pullback (pullback.fst f g) (pullback.fst f g) ⟶
        pullback f (pullback.fst g g ≫ g),
      h ≫ (pullback.map f (pullback.fst g g ≫ g) f g
        (𝟙 X) (pullback.fst g g) (𝟙 Y) (by simp) (by simp)) =
          pullback.fst (pullback.fst f g) (pullback.fst f g) ∧
      h ≫ (pullback.map f (pullback.fst g g ≫ g) f g
        (𝟙 X) (pullback.snd g g) (𝟙 Y)
        (by simp) (by simpa using (pullback.condition (f := g) (g := g)))) =
          pullback.snd (pullback.fst f g) (pullback.fst f g) := by
  let p := pullback.fst f g
  obtain ⟨q, hq₀, hq₁⟩ := exists_double_base_map f g
  exact double_base_lift f g (pullback.fst p p) (pullback.snd p p) q
    (pullback.fst g g) (pullback.snd g g)
    (pullback.condition (f := p) (g := p)) hq₀ hq₁
    (pullback.condition (f := g) (g := g))

/-- The data the descent of the sectioned locus along `X ×_Y Z ⟶ X` runs on: the two base
changes of `X ×_Y Z` along the two projections of `Z ×_Y Z`, each presented by its universal
property, together with the factorization of the canonical relation through them. -/
theorem exists_base_change_maps {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Z ⟶ Y) :
    ∃ m₀ m₁ : pullback f (pullback.fst g g ≫ g) ⟶ pullback f g,
      IsPullback m₀ (pullback.snd f (pullback.fst g g ≫ g)) (pullback.snd f g)
          (pullback.fst g g) ∧
        m₀ ≫ pullback.fst f g = pullback.fst f (pullback.fst g g ≫ g) ∧
        IsPullback m₁ (pullback.snd f (pullback.fst g g ≫ g)) (pullback.snd f g)
          (pullback.snd g g) ∧
        m₁ ≫ pullback.fst f g = pullback.fst f (pullback.fst g g ≫ g) ∧
        ∃ t : pullback (pullback.fst f g) (pullback.fst f g) ⟶
            pullback f (pullback.fst g g ≫ g),
          t ≫ m₀ = pullback.fst (pullback.fst f g) (pullback.fst f g) ∧
            t ≫ m₁ = pullback.snd (pullback.fst f g) (pullback.fst f g) := by
  obtain ⟨hm₀, hm₀'⟩ := pullback_map_isPullback_over_base_of_eq f g (pullback.fst g g)
    (pullback.fst g g ≫ g) rfl (by simp) (by simp)
  obtain ⟨hm₁, hm₁'⟩ := pullback_map_isPullback_over_base_of_eq f g (pullback.snd g g)
    (pullback.fst g g ≫ g) (pullback.condition (f := g) (g := g)) (by simp)
    (by simpa using (pullback.condition (f := g) (g := g)))
  obtain ⟨t, ht₀, ht₁⟩ := exists_relation_factorization f g
  exact ⟨_, _, hm₀, hm₀', hm₁, hm₁', t, ht₀, ht₁⟩

end AlgebraicGeometry.ConnectedComponentSection

end
