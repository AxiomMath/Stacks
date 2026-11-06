module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.EqualityLocus
public import StacksCore.Tactic.StacksAttribute

/-!
# Relative cycles over a limit of a system of bases

Let `S = lim_{i ∈ I} S_i` be the limit of a directed inverse system of Noetherian schemes with
affine transition morphisms, let `0 ∈ I`, let `X_0 ⟶ S_0` be of finite type, and for `i ≥ 0` put
`X_i = S_i ×_{S_0} X_0` and `X = S ×_{S_0} X_0`. If `S` is Noetherian too, Lemma 0H5D asserts that
the canonical map

  `colim_{i ≥ 0} z(X_i/S_i, r) ⟶ z(X/S, r)`

whose transition maps are base change of relative `r`-cycles, is an isomorphism. This file proves
that this map is injective.

## Main results

* `Stacks.Chow.baseChangeFamily_eq_iff` — two families of `r`-cycles on the fibres of `X/S` have
  the same base change along `g : S' ⟶ S` exactly when their members agree over every point in
  the image of `g`.
* `Stacks.Chow.exists_map_baseChangeFamily_eq_of_isLimit` — for a morphism `Y ⟶ S_i` locally of
  finite type to a Noetherian stage of the system: if two relative `r`-cycles over `S_i` have the
  same base change to `S`, then they already have the same base change to `S_j` for some `j ≥ i`.
* `Stacks.Chow.exists_map_baseChangeFamily_pullback_eq_of_isLimit` — the same for
  `X_i = S_i ×_{S_0} X_0`: the canonical map of Lemma 0H5D is injective.

## References

* [Stacks Project, Lemma 0H5D](https://stacks.math.columbia.edu/tag/0H5D)
* [Stacks Project, Lemma 0H5C](https://stacks.math.columbia.edu/tag/0H5C)
* [Stacks Project, Lemma 01YX](https://stacks.math.columbia.edu/tag/01YX)
* [Stacks Project, Lemma 05F4](https://stacks.math.columbia.edu/tag/05F4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Equality of two base changes is a condition on the base -/

/-- Two families of `r`-cycles on the fibres of `X/S` have the same base change along
`g : S' ⟶ S` exactly when their members over the image of every point of `S'` agree. -/
theorem baseChangeFamily_eq_iff {X S S' : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (g : S' ⟶ S) (r : ℕ) (α β : FamilyOfCycles f r) :
    baseChangeFamily f g r α = baseChangeFamily f g r β ↔ ∀ t : S', α (g t) = β (g t) := by
  have hsub : baseChangeFamily f g r (α - β) =
      baseChangeFamily f g r α - baseChangeFamily f g r β := by
    simpa only [baseChangeFamilyHom_apply] using map_sub (baseChangeFamilyHom f g r) α β
  rw [← sub_eq_zero, ← hsub, funext_iff]
  refine forall_congr' fun t => ?_
  rw [Pi.zero_apply, baseChangeFamily_apply_eq_zero_iff, Pi.sub_apply, sub_eq_zero]

/-! ### Injectivity of the comparison map -/

/-- **The injectivity in Lemma 0H5D, general form.** Let `S = lim_{i ∈ I} S_i` be a
limit of a cofiltered system of schemes with affine transition morphisms, let `i ∈ I` with `S_i`
Noetherian, let `f : Y ⟶ S_i` be locally of finite type and let `α, β ∈ z(Y/S_i, r)`. If the base
changes of `α` and of `β` along the projection `S ⟶ S_i` agree, then their base changes along
some transition morphism `S_j ⟶ S_i` already agree. -/
theorem exists_map_baseChangeFamily_eq_of_isLimit {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ {i j : I} (u : i ⟶ j), IsAffineHom (D.map u)] (c : Cone D)
    (hc : IsLimit c) {i : I} [IsNoetherian (D.obj i)] {Y : Scheme.{u}} (f : Y ⟶ D.obj i)
    [LocallyOfFiniteType f] (r : ℕ) (α β : relativeCycles f r)
    (h : baseChangeFamily f (c.π.app i) r (α : FamilyOfCycles f r) =
      baseChangeFamily f (c.π.app i) r (β : FamilyOfCycles f r)) :
    ∃ (j : I) (v : j ⟶ i), baseChangeFamily f (D.map v) r (α : FamilyOfCycles f r) =
      baseChangeFamily f (D.map v) r (β : FamilyOfCycles f r) := by
  have hall : ∀ s : c.pt, (α : FamilyOfCycles f r) (c.π.app i s) =
      (β : FamilyOfCycles f r) (c.π.app i s) :=
    (baseChangeFamily_eq_iff f (c.π.app i) r _ _).mp h
  obtain ⟨j, v, hv⟩ := AlgebraicGeometry.exists_map_preimage_le_map_preimage D c hc
    (U := ⟨{s : D.obj i | (α : FamilyOfCycles f r) s = (β : FamilyOfCycles f r) s}ᶜ,
      (isClosed_setOf_fiberCycle_eq f α β).isOpen_compl⟩)
    (V := ⊥) (NoetherianSpace.isCompact _) (fun s hs => absurd (hall s) hs)
  refine ⟨j, v, (baseChangeFamily_eq_iff f (D.map v) r _ _).mpr fun s => ?_⟩
  by_contra hne
  exact hv hne

/-- **The injectivity in Lemma 0H5D.** Let `S = lim_{i ∈ I} S_i` be the limit of a
cofiltered system of Noetherian schemes with affine transition morphisms, let `0 ∈ I`, let
`X_0 ⟶ S_0` be locally of finite type, and for `i ≥ 0` put `X_i = S_i ×_{S_0} X_0`. Let
`α, β ∈ z(X_i/S_i, r)`. If `α` and `β` have the same image in `z(X/S, r)`, realized as the base
change along the projection `S ⟶ S_i`, then they have the same image in `z(X_j/S_j, r)` for some
`j ≥ i`: the canonical map `colim_{i ≥ 0} z(X_i/S_i, r) ⟶ z(X/S, r)` is injective. -/
theorem exists_map_baseChangeFamily_pullback_eq_of_isLimit {I : Type u} [Category.{u} I]
    [IsCofiltered I] (D : I ⥤ Scheme.{u}) [∀ {i j : I} (u : i ⟶ j), IsAffineHom (D.map u)]
    [∀ i, IsNoetherian (D.obj i)] (c : Cone D) (hc : IsLimit c) [IsNoetherian c.pt] {i₀ : I}
    {X₀ : Scheme.{u}} (f₀ : X₀ ⟶ D.obj i₀) [LocallyOfFiniteType f₀] (r : ℕ) {i : I} (u : i ⟶ i₀)
    (α β : relativeCycles (pullback.snd f₀ (D.map u)) r)
    (h : baseChangeFamily (pullback.snd f₀ (D.map u)) (c.π.app i) r
          (α : FamilyOfCycles (pullback.snd f₀ (D.map u)) r) =
        baseChangeFamily (pullback.snd f₀ (D.map u)) (c.π.app i) r
          (β : FamilyOfCycles (pullback.snd f₀ (D.map u)) r)) :
    ∃ (j : I) (v : j ⟶ i),
      baseChangeFamily (pullback.snd f₀ (D.map u)) (D.map v) r
          (α : FamilyOfCycles (pullback.snd f₀ (D.map u)) r) =
        baseChangeFamily (pullback.snd f₀ (D.map u)) (D.map v) r
          (β : FamilyOfCycles (pullback.snd f₀ (D.map u)) r) :=
  exists_map_baseChangeFamily_eq_of_isLimit D c hc (pullback.snd f₀ (D.map u)) r α β h

end Stacks.Chow

end
