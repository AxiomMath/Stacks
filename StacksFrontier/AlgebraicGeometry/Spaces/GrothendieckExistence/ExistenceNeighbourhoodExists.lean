module

public import StacksCore.Tactic.StacksAttribute
public import
  StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.ExistenceNeighbourhoodOfPerfect
public import
  StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.LimitTensorSectionsBaseChange
public import
  StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.RelativePseudoCoherenceOfPerfect
public import
  StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.StageTransitionCounitCompatibility
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.StageTensorSectionsTransitionCompatibility

/-!
# The open neighbourhood of `X₀` on which `K` is a finitely presented module

In Situation [Stacks, Tag 0CX4] let `K = DQ_X(L)` be the object of [Stacks, Tag 0CX5], for a
coherator `DQ_X` and a presentation `L ⟶ ∏ Fₙ ⟶ ∏ Fₙ ⟶ L[1]` of `L = R lim_{D(𝒪_X)} Fₙ`. There is
an open subspace `W ⊂ X` containing `X₀` such that `Hⁱ(K)|_W = 0` for `i ≠ 0`,
`F = H⁰(K)|_W` is of finite presentation, and `Fₙ = F ⊗_{𝒪_X} 𝒪_{Xₙ}` through the canonical maps
`K ⟶ Fₙ`.

## Main results

* `AlgebraicGeometry.Space.FlatSheafExistenceSituation.exists_isExistenceNeighbourhood`: `K` has
  such an open neighbourhood `W` of `X₀`.

## References

* [Stacks Project, Tag 0CX9](https://stacks.math.columbia.edu/tag/0CX9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

universe u

namespace AlgebraicGeometry.Space

namespace FlatSheafExistenceSituation

variable (D : FlatSheafExistenceSituation.{u})

/-- In Situation [Stacks, Tag 0CX4] let `K = DQ_X(L)` be as in [Stacks, Tag 0CX5]: `DQ_X` is a
coherator (`adj : ι ⊣ DQ_X`) and `L ⟶ ∏ Fₙ ⟶ ∏ Fₙ ⟶ L[1]` (first map `p`) presents `L` as
`R lim_{D(𝒪_X)} Fₙ`, with canonical maps `K ⟶ Fₙ` the counit followed by the projections. Then
there is an open subspace `W ⊂ X` containing the points `X₀` lying over `Spec(A₁)` such that
`Hⁱ(K)|_W = 0` for `i ≠ 0`, `H⁰(K)|_W` is of finite presentation, and
`H⁰(K)|_W ⊗_{𝒪_X} 𝒪_{Xₙ} ⟶ Fₙ` induced by `K ⟶ Fₙ` is an isomorphism on `W ×_X Xₙ` for every `n`.
-/
@[stacks 0CX9 "the full statement: for every coherator DQ_X and every presentation of \
L = R lim F_n in D(O_X), K = DQ_X(L) has an open subspace W containing X_0 with H^i(K)|_W = 0 \
for i ≠ 0, H^0(K)|_W of finite presentation, and F_n = H^0(K)|_W ⊗ O_{X_n} through the \
canonical maps K → F_n; nothing is granted or assumed"]
theorem exists_isExistenceNeighbourhood
    {DQ : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left ⥤
      (spaceQuasicoherentProp D.B D.S D.containsLimitBase D.X.left).FullSubcategory}
    (adj : (spaceQuasicoherentProp D.B D.S D.containsLimitBase D.X.left).ι ⊣ DQ)
    {L : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left}
    (p : L ⟶ ∏ᶜ fun n : ℕ => D.derivedSystem.obj ⟨n⟩)
    (hp : ∃ δ : (∏ᶜ fun n : ℕ => D.derivedSystem.obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧,
      Triangle.mk p (Pi.lift fun n : ℕ => Pi.π (fun n : ℕ => D.derivedSystem.obj ⟨n⟩) n -
        Pi.π (fun n : ℕ => D.derivedSystem.obj ⟨n⟩) (n + 1) ≫
          D.derivedSystem.map (homOfLE (Nat.le_succ n)).op) δ ∈
        distTriang (spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left)) :
    ∃ (W : Subfunctor D.X.left.1) (hW : IsOpenSubspace D.B D.S D.containsLimitBase W),
      D.IsExistenceNeighbourhood
        ((spaceQuasicoherentProp D.B D.S D.containsLimitBase D.X.left).ι.obj (DQ.obj L))
        (D.derivedLimitProjection adj p) W hW :=
  D.exists_isExistenceNeighbourhood_of_isIso_of_isRelativelyPseudoCoherent adj p hp
    (fun n => D.isIso_limitTensorSectionsBaseChangeMap_of adj L p hp
      (fun m => D.stageTransitionCounitCompatible m)
      (fun E m => D.stageTensorSectionsTransitionCompatible m E) n)
    (D.isRelativelyPseudoCoherent_coheratorObj_of_transitionCompatible adj L ⟨p, hp⟩
      (fun m => D.stageTransitionCounitCompatible m)
      (fun E m => D.stageTensorSectionsTransitionCompatible m E))

end FlatSheafExistenceSituation

end AlgebraicGeometry.Space

end
