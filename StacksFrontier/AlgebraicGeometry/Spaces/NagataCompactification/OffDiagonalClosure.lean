module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ProperCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationCancellation
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosed

/-!
# The off-diagonal part of a self-intersection near the boundary

Let `X` be an algebraic space over `Y`, separated, and let `ψ : V ⟶ U` be a proper morphism from
an open subspace `V ⊆ X` to an algebraic space `U` over `Y`. The graph `V ⟶ U ×_Y X` of `ψ` is
proper, so its image is closed. This is the valuative content of the repaired proof of
Stacks 0F4B in the form used there: a point of `X ×_Y X` in the closure of the off-diagonal part
`O` of `U₁ ×_U U₁` whose first coordinate lies in `V` has its second coordinate in `V` as well,
and lies over the same point of `U`.

The two point-set lemmas at the end are the bookkeeping of the repair: the first is Step 1 of
the proof of the condition `(H)`, the second turns the closedness of `O` near the chosen
neighbourhood `N` of the closure of `f⁻¹ Z₁` into the hypothesis of
`AlgebraicGeometry.Space.isSeparated_of_isPullback_of_isClosedMap_offDiagonal`.

## Main results

* `AlgebraicGeometry.Space.isProper_pullbackLift_of_isProper`: the graph of a proper morphism
  to a space over `Y`, into a separated space over `Y`, is proper.
* `AlgebraicGeometry.Space.isClosed_range_pointsMap_of_isProper`: its image is closed.
* `notMem_of_mem_closure_of_mem_closure`: Step 1, as a statement about sets.
* `closure_image_inter_subset_of_closure_inter_subset`: the transfer to images — for `ι`
  injective and closed onto an open set, the closure of the image of a closed subset meets `N`
  only inside that image.

## References

* [Stacks Project, Tag 0F4B](https://stacks.math.columbia.edu/tag/0F4B)
* [Stacks Project, Tag 04NX](https://stacks.math.columbia.edu/tag/04NX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

/-- **Step 1 of the separation argument, for sets.** Let `pr₁, pr₂ : P → X` be maps from a
topological space, `V ⊆ X`, `T ⊆ X` with `closure T ∩ V ⊆ T`, and `O ⊆ P`. Suppose that the part
of the closure of `O` over `V` (in either coordinate) lies in a set `K` whose points have both
coordinates in `V`, that a point of `K` with both coordinates in `T` lies in `Δ`, and that `Δ` does
not meet the closure of `O`. Then a point of the closure of `O` with both coordinates in the
closure of `T` has both coordinates outside `V`. -/
theorem notMem_of_mem_closure_of_mem_closure {P X : Type*} [TopologicalSpace P]
    [TopologicalSpace X] (pr₁ pr₂ : P → X) {V T : Set X} (hTV : closure T ∩ V ⊆ T)
    {O K Δ : Set P} (hK₁ : closure O ∩ pr₁ ⁻¹' V ⊆ K) (hK₂ : closure O ∩ pr₂ ⁻¹' V ⊆ K)
    (hKV : K ⊆ pr₁ ⁻¹' V ∩ pr₂ ⁻¹' V) (hKΔ : ∀ w ∈ K, pr₁ w ∈ T → pr₂ w ∈ T → w ∈ Δ)
    (hΔ : Disjoint (closure O) Δ) {w : P} (hw : w ∈ closure O) (h₁ : pr₁ w ∈ closure T)
    (h₂ : pr₂ w ∈ closure T) : pr₁ w ∉ V ∧ pr₂ w ∉ V := by
  have key : w ∉ K := fun hwK =>
    Set.disjoint_left.1 hΔ hw (hKΔ w hwK (hTV ⟨h₁, (hKV hwK).1⟩) (hTV ⟨h₂, (hKV hwK).2⟩))
  exact ⟨fun hv => key (hK₁ ⟨hw, hv⟩), fun hv => key (hK₂ ⟨hw, hv⟩)⟩

/-- **Closed images from a closure condition.** Let `ι : R → P` be closed onto a set `A ⊆ P`
(it maps closed sets to sets closed in `A`). Let `O' ⊆ R` be
closed and `N ⊆ P` with `closure (ι '' O') ∩ N ⊆ A`. Then `ι` maps closed subsets of `O'` to sets
whose closure meets `N` only inside them. -/
theorem closure_image_inter_subset_of_closure_inter_subset {R P : Type*} [TopologicalSpace R]
    [TopologicalSpace P] (ι : R → P) {A N : Set P}
    (hι : ∀ K, IsClosed K → closure (ι '' K) ∩ A ⊆ ι '' K) {O' : Set R}
    (hN : closure (ι '' O') ∩ N ⊆ A) {K : Set R} (hK : IsClosed K) (hKO : K ⊆ O') :
    closure (ι '' K) ∩ N ⊆ ι '' K := by
  intro x ⟨hx, hxN⟩
  have hxA : x ∈ A := hN ⟨closure_mono (Set.image_mono hKO) hx, hxN⟩
  exact hι K hK ⟨hx, hxA⟩

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out without
this shortcut). -/
local instance (priority := high) hasPullback_presheaf_OffDiagonalClosure
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- **The graph of a proper morphism is proper.** Let `π : X ⟶ Y` be separated and let
`ψ : V ⟶ U` be proper, with `q : U ⟶ Y` and `ι : V ⟶ X` such that `ψ ≫ q = ι ≫ π`. Then the
graph `(ψ, ι) : V ⟶ U ×_Y X` is proper: its composite with the first projection is `ψ`, and the
first projection is separated, being a base change of `π` (Stacks 04NX). -/
theorem isProper_pullbackLift_of_isProper {V U X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hV : IsAlgebraicSpace B S hS V) (hU : IsAlgebraicSpace B S hS U)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    {ψ : V ⟶ U} {ι : V ⟶ X} {q : U ⟶ Y} {π : X ⟶ Y} (hψ : IsProper B S hS ψ)
    (hπ : IsSeparated B S hS π) (h : ψ ≫ q = ι ≫ π) :
    IsProper B S hS (pullback.lift ψ ι h) := by
  have hfst : IsSeparated B S hS (pullback.fst q π) :=
    isSeparated_pullback_fst_of_snd B S hS π q (isSeparated_pullback B S hS π q hπ)
  refine isProper_of_comp_of_isSeparated B S hS hV
    (isAlgebraicSpace_pullback B S hS q π hU hX hY) hU _ _ ?_ hfst
  rw [pullback.lift_fst]
  exact hψ

/-- The image of a proper morphism of algebraic spaces is closed. -/
theorem isClosed_range_pointsMap_of_isProper {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hG : IsAlgebraicSpace B S hS G) {f : F ⟶ G} (hf : IsProper B S hS f) :
    @IsClosed _ (pointTopology B S hS G) (Set.range (pointsMap B S hS F f)) := by
  let := pointTopology B S hS F
  let := pointTopology B S hS G
  have := isClosedMap_pointsMap_of_pullback_fst_id B S hS f (hf.2.2 G hG (𝟙 G))
  simpa using this _ isClosed_univ

end AlgebraicGeometry.Space

end
