module

public import StacksFrontier.AlgebraicGeometry.Chow.DiagonalGysin
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.LciGysinFlat
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.LciGysinMapComposition
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.RegularImmersionSelfIntersection
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.RegularImmersion
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.Syntomic
public import StacksFrontier.AlgebraicGeometry.Morphisms.SmoothMorphisms.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# `Δ^! ∘ pr_i^! = 1` for the Gysin map of the diagonal of a smooth morphism

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `f : X ⟶ Y` be a
smooth morphism of schemes locally of finite type over `S`. The diagonal `Δ : X ⟶ X ×_Y X` is a
regular immersion (Stacks 0FBR), so it has a Gysin map `Δ^! ∈ A^*(X ⟶ X ×_Y X)^∧`
(Stacks 0FF3), and so do the smooth projections `pr_1, pr_2 : X ×_Y X ⟶ X`. **Stacks 0FBS**
asserts

  `Δ^! ∘ pr_i^! = 1`   in `A^0(X)`,

no constancy of the relative dimension of `f` being assumed: the classes live in the completed
bivariant groups of Stacks 0FE0, and `A^0(X)` is read inside `A^*(X)^∧`.

The proof is the source's: the identity is the special case `g ∘ f = 𝟙` of Stacks 0FF5,
`(g ∘ f)^! = f^! ∘ g^!` (`Stacks.Chow.lciGysinMap_comp`), together with `𝟙^! = 1`. The Gysin map
of the identity is its flat pullback (Stacks 0FF4,
`Stacks.Chow.lciGysinMap_eq_completedFlatPullbackOfFlatLCI`), and the flat pullback along the
identity is the unit
(`Stacks.Chow.completedFlatPullbackOfSmooth_id`).

## Main results

* `Stacks.Chow.lciGysinMap_id` — `𝟙^! = 1` in `A^*(X)^∧`.
* `Stacks.Chow.lciGysinMap_copy` — the Gysin maps of two equal morphisms agree.
* `Stacks.Chow.lciGysinMap_comp_eq_completedIdentityClass` — `i^! ∘ q^! = 1` for local complete
  intersection morphisms `i : X ⟶ P`, `q : P ⟶ X` with `i ≫ q = 𝟙 X` and Gysin maps.
* `Stacks.Chow.diagonalGysinMap_comp_eq_completedIdentityClass` — **Stacks 0FBS**.

## References

* [Stacks Project, Tag 0FBS](https://stacks.math.columbia.edu/tag/0FBS)
* [Stacks Project, Tag 0FBR](https://stacks.math.columbia.edu/tag/0FBR)
* [Stacks Project, Tag 0FF3](https://stacks.math.columbia.edu/tag/0FF3)
* [Stacks Project, Tag 0FF4](https://stacks.math.columbia.edu/tag/0FF4)
* [Stacks Project, Tag 0FF5](https://stacks.math.columbia.edu/tag/0FF5)
* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

section Lci

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- **`𝟙^! = 1`.** The Gysin map (Stacks 0FF3) of the identity of `X` is the unit
`1 ∈ A^*(X)^∧`: it is the flat pullback along the identity (Stacks 0FF4), which is the unit. -/
theorem lciGysinMap_id (hlci : IsLocalCompleteIntersectionMorphism (𝟙 X))
    (h : GysinMapExists (𝟙 X)) :
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    lciGysinMap C sX sX (Category.id_comp sX) hlci h = completedIdentityClass C sX := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  rw [lciGysinMap_eq_completedFlatPullbackOfFlatLCI, completedFlatPullbackOfFlatLCI,
    ← completedFlatPullbackOfSmooth_eq_completedFlatPullback, completedFlatPullbackOfSmooth_id]

/-- The Gysin maps (Stacks 0FF3) of two equal morphisms agree, read through
`Stacks.Chow.completedBivariantGroup.copy`. -/
theorem lciGysinMap_copy {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    {f f' : X ⟶ Y} [LocallyOfFiniteType f] [LocallyOfFiniteType f'] (e : f = f')
    (hf : f ≫ sY = sX) (hf' : f' ≫ sY = sX) (hlci : IsLocalCompleteIntersectionMorphism f)
    (hlci' : IsLocalCompleteIntersectionMorphism f') (h : GysinMapExists f)
    (h' : GysinMapExists f') :
    completedBivariantGroup.copy C e hf hf' (lciGysinMap C sX sY hf hlci h) =
      lciGysinMap C sX sY hf' hlci' h' := by
  subst e
  rfl

/-- **`i^! ∘ q^! = 1` for a retraction.** Let `i : X ⟶ P` and `q : P ⟶ X` be local complete
intersection morphisms of schemes locally of finite type over the base whose Gysin maps exist
(Stacks 0FF3), with `i ≫ q = 𝟙 X`. Then the composite `i^! ∘ q^! ∈ A^*(X ⟶ X)^∧`, read as a
class for `𝟙 X`, is the unit `1 ∈ A^*(X)^∧`. This is Stacks 0FF5 for `q ∘ i = 𝟙 X` together with
`𝟙^! = 1`. -/
theorem lciGysinMap_comp_eq_completedIdentityClass {P : Scheme.{u}} (sP : P ⟶ C.S)
    [LocallyOfFiniteType sP] (i : X ⟶ P) (q : P ⟶ X) [LocallyOfFiniteType i]
    [LocallyOfFiniteType q] (hi : i ≫ sP = sX) (hq : q ≫ sX = sP) (hiq : i ≫ q = 𝟙 X)
    (hli : IsLocalCompleteIntersectionMorphism i) (hlq : IsLocalCompleteIntersectionMorphism q)
    (hGi : GysinMapExists i) (hGq : GysinMapExists q) :
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    haveI : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian sP
    completedBivariantGroup.copy C hiq (comp_comp_structureMorphism_eq hi hq)
        (Category.id_comp sX)
        (completedBivariantCompositeOfInvertible C sX sP sX i q hi hq
          (lciGysinMap C sX sP hi hli hGi) (lciGysinMap C sP sX hq hlq hGq)) =
      completedIdentityClass C sX := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian sP
  have hGiq : GysinMapExists (i ≫ q) := by
    rw [hiq]
    exact GysinMapExists.of_smooth _
  obtain ⟨_, hcomp⟩ := lciGysinMap_comp C sX sP sX hi hq hli hlq hGiq hGq
  rw [← hcomp, lciGysinMap_copy C sX sX hiq _ (Category.id_comp sX) _
    (isLocalCompleteIntersectionMorphism_of_syntomic (syntomic_of_smooth (𝟙 X))) hGiq
    (GysinMapExists.of_smooth _)]
  exact lciGysinMap_id C sX _ _

end Lci

section Diagonal

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y) [Smooth f] (hf : f ≫ sY = sX)

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] [Smooth f] in
include hf in
/-- The second projection `X ×_Y X ⟶ X` is a morphism over the base, for the structure morphism
`pr_1 ≫ s_X` of `X ×_Y X`. -/
theorem pullback_snd_comp_structureMorphism_of_comp_eq :
    pullback.snd f f ≫ sX = pullback.fst f f ≫ sX := by
  rw [← hf, pullback.condition_assoc]

omit [LocallyOfFiniteType sY] in
/-- **Stacks 0FBS: `Δ^! ∘ pr_i^! = 1` in `A^0(X)`, for `i = 1, 2`.** Let `f : X ⟶ Y` be a smooth
morphism of schemes locally of finite type over the base, let `Δ : X ⟶ X ×_Y X` be its diagonal
and `pr_1, pr_2 : X ×_Y X ⟶ X` the projections. Write `Δ^! ∈ A^*(X ⟶ X ×_Y X)^∧` and
`pr_i^! ∈ A^*(X ×_Y X ⟶ X)^∧` for their Gysin maps (Stacks 0FF3), which exist since `Δ` is a
regular immersion (Stacks 0FBR) and the projections are smooth. Then for both projections the
composite `Δ^! ∘ pr_i^!` (Stacks 0FE0), read as a class for `𝟙 X` through `Δ ≫ pr_i = 𝟙 X`, is
the unit `1 ∈ A^0(X) ⊆ A^*(X)^∧`. No constancy of the relative dimension of `f` is assumed. -/
@[stacks 0FBS "Δ^! ∘ pr_i^! = 1 for both projections i = 1, 2, Δ^! and pr_i^! the Gysin maps of \
Stacks 0FF3, in the completed ring A^*(X)^∧, for any smooth X → Y"]
theorem diagonalGysinMap_comp_eq_completedIdentityClass :
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    haveI : IsLocallyNoetherian (pullback f f) :=
      LocallyOfFiniteType.isLocallyNoetherian (pullback.fst f f ≫ sX)
    completedBivariantGroup.copy C (pullback.diagonal_fst f)
        (comp_comp_structureMorphism_eq (by simp) rfl) (Category.id_comp sX)
        (completedBivariantCompositeOfInvertible C sX (pullback.fst f f ≫ sX) sX
          (pullback.diagonal f) (pullback.fst f f) (by simp) rfl
          (lciGysinMap C sX (pullback.fst f f ≫ sX) (by simp)
            (isLocalCompleteIntersectionMorphism_of_isRegularImmersion _
              (isRegularImmersion_diagonal_of_smooth f))
            (gysinMapExists_diagonal_of_smooth f))
          (lciGysinMap C (pullback.fst f f ≫ sX) sX rfl
            (isLocalCompleteIntersectionMorphism_of_syntomic (syntomic_of_smooth _))
            (GysinMapExists.of_smooth _))) =
        completedIdentityClass C sX ∧
      completedBivariantGroup.copy C (pullback.diagonal_snd f)
        (comp_comp_structureMorphism_eq (by simp)
          (pullback_snd_comp_structureMorphism_of_comp_eq C sX sY f hf)) (Category.id_comp sX)
        (completedBivariantCompositeOfInvertible C sX (pullback.fst f f ≫ sX) sX
          (pullback.diagonal f) (pullback.snd f f) (by simp)
          (pullback_snd_comp_structureMorphism_of_comp_eq C sX sY f hf)
          (lciGysinMap C sX (pullback.fst f f ≫ sX) (by simp)
            (isLocalCompleteIntersectionMorphism_of_isRegularImmersion _
              (isRegularImmersion_diagonal_of_smooth f))
            (gysinMapExists_diagonal_of_smooth f))
          (lciGysinMap C (pullback.fst f f ≫ sX) sX
            (pullback_snd_comp_structureMorphism_of_comp_eq C sX sY f hf)
            (isLocalCompleteIntersectionMorphism_of_syntomic (syntomic_of_smooth _))
            (GysinMapExists.of_smooth _))) =
        completedIdentityClass C sX :=
  ⟨lciGysinMap_comp_eq_completedIdentityClass C sX _ _ _ _ _ (pullback.diagonal_fst f) _ _ _ _,
    lciGysinMap_comp_eq_completedIdentityClass C sX _ _ _ _ _ (pullback.diagonal_snd f) _ _ _ _⟩

end Diagonal

end Stacks.Chow

end
