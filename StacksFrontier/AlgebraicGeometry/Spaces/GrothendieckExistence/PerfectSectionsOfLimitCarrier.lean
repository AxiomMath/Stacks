module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.LimitSheafHomSectionsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.StageTransitionCounitCompatibility
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.StageTensorSectionsTransitionCompatibility

/-!
# `RΓ(X, E ⊗^𝐋 K)` and `RHom_X(E, K)` are perfect and commute with base change, for every `K`

In Situation [Stacks, Tag 0CX4] let `K = DQ_X(L)` for a coherator `DQ_X` and a derived limit
`L = R lim_{D(𝒪_X)} Fₙ` given by a triangle `L ⟶ ∏ Fₙ ⟶ ∏ Fₙ ⟶ L[1]` (the object of
[Stacks, Tag 0CX5], `AlgebraicGeometry.Space.FlatSheafExistenceSituation.derivedLimit_bounded`,
which also proves that such `DQ_X` and `L` exist). For every perfect `E` on `X`:

1. `M = RΓ(X, E ⊗^𝐋 K)` is perfect in `D(A)` and the canonical map
   `M ⊗^𝐋_A Aₙ ⟶ RΓ(Xₙ, E|_{Xₙ} ⊗^𝐋 Fₙ)` is an isomorphism;
2. `N = RHom_X(E, K)` is perfect in `D(A)` and the canonical map
   `N ⊗^𝐋_A Aₙ ⟶ RHom_{Xₙ}(E|_{Xₙ}, Fₙ)` is an isomorphism.

The proof is
`AlgebraicGeometry.Space.FlatSheafExistenceSituation.isPerfect_limitTensorSections_and_isIso_of`
(part (1)) and
`AlgebraicGeometry.Space.FlatSheafExistenceSituation.isPerfect_limitSheafHomSections_and_isIso_of`
(part (2), from (1) at `E^∨` through Cohomology on Sites, Lemma 21.48.4 = Stacks 08JJ), with their
two compatibilities of the transitions supplied by
`AlgebraicGeometry.Space.FlatSheafExistenceSituation.stageTransitionCounitCompatible` and
`AlgebraicGeometry.Space.FlatSheafExistenceSituation.stageTensorSectionsTransitionCompatible`.
[Stacks, Tag 0CX6] itself, for the coherator and derived limit chosen from [Stacks, Tag 0CX5], is
`FlatSheafExistenceSituation.ringIsPerfect_limitSections_and_isIso_baseChangeMap` in
`StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.PerfectSectionsOfLimitTheorem`.

## Main results

* `AlgebraicGeometry.Space.FlatSheafExistenceSituation.perfectSections_of_derivedLimit`.

## References

* [Stacks Project, Tag 0CX6](https://stacks.math.columbia.edu/tag/0CX6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

universe u

namespace AlgebraicGeometry.Space

namespace FlatSheafExistenceSituation

variable (D : FlatSheafExistenceSituation.{u})
  {DQ : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left ⥤
    (spaceQuasicoherentProp D.B D.S D.containsLimitBase D.X.left).FullSubcategory}
  (adj : (spaceQuasicoherentProp D.B D.S D.containsLimitBase D.X.left).ι ⊣ DQ)
  (L : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left)

/-- **[Stacks, Tag 0CX6] for every choice of `K`.** In Situation [Stacks, Tag 0CX4] let
`K = DQ_X(L)` be as in [Stacks, Tag 0CX5]
(`AlgebraicGeometry.Space.FlatSheafExistenceSituation.derivedLimit_bounded`):
`DQ_X` is a coherator (`adj : ι ⊣ DQ_X`) and `p : L ⟶ ∏ (iₙ,* Fₙ)[0]` is the first map of a
distinguished triangle `L ⟶ ∏ Fₙ ⟶ ∏ Fₙ ⟶ L[1]` whose middle map is `1 - transition`
(`hp` is exactly the triangle of `CategoryTheory.Pretriangulated.IsDerivedLimit` with `p` bound),
so `L = R lim Fₙ`. Then for every perfect `E` on `X` and every `n`:

1. `RΓ(X, E ⊗^𝐋 K)` is a perfect object of `D(A)` and the canonical map
   `RΓ(X, E ⊗^𝐋 K) ⊗^𝐋_A Aₙ ⟶ RΓ(Xₙ, E|_{Xₙ} ⊗^𝐋 Fₙ)` is an isomorphism in `D(Aₙ)`;
2. `RHom_X(E, K)` is a perfect object of `D(A)` and the canonical map
   `RHom_X(E, K) ⊗^𝐋_A Aₙ ⟶ RHom_{Xₙ}(E|_{Xₙ}, Fₙ)` is an isomorphism in `D(Aₙ)`; this map is
   the one induced from (1) at `E^∨` by Cohomology on Sites, Lemma 21.48.4 (Stacks 08JJ).

Here `E|_{Xₙ}` is the derived pullback of `E` along `iₙ : Xₙ ⟶ X`. -/
theorem perfectSections_of_derivedLimit
    (p : L ⟶ ∏ᶜ fun n : ℕ => D.derivedSystem.obj ⟨n⟩)
    (hp : ∃ δ : (∏ᶜ fun n : ℕ => D.derivedSystem.obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧,
      Triangle.mk p (Pi.lift fun n : ℕ => Pi.π (fun n : ℕ => D.derivedSystem.obj ⟨n⟩) n -
        Pi.π (fun n : ℕ => D.derivedSystem.obj ⟨n⟩) (n + 1) ≫
          D.derivedSystem.map (homOfLE (Nat.le_succ n)).op) δ ∈
        distTriang (spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left))
    (E : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left)
    (hE : spaceIsPerfect D.B D.S D.containsLimitBase D.X.left E) (n : ℕ) :
    (StacksDraft.ringIsPerfect (D.limitTensorSections DQ L E) ∧
      IsIso (D.limitTensorSectionsBaseChangeMap adj L E p n)) ∧
    (StacksDraft.ringIsPerfect (D.limitSheafHomSections DQ L E) ∧
      IsIso (D.limitSheafHomSectionsBaseChangeMap adj L E hE p n)) :=
  by
  have h₁ := D.isPerfect_limitTensorSections_and_isIso_of adj L E hE p hp
    D.stageTransitionCounitCompatible (D.stageTensorSectionsTransitionCompatible · E)
  have h₂ := D.isPerfect_limitSheafHomSections_and_isIso_of adj L E hE p hp
    D.stageTransitionCounitCompatible (D.stageTensorSectionsTransitionCompatible · _)
  exact ⟨⟨h₁.1, h₁.2 n⟩, h₂.1, h₂.2 n⟩

end FlatSheafExistenceSituation

end AlgebraicGeometry.Space
