module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EtaleStageSectionsMap
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.LimitTensorSectionsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.StageTransitionCounitCompatibility
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.StageTensorSectionsTransitionCompatibility

/-!
# [Stacks, Tag 0CX8]: `RΓ(U, K) ⊗^𝐋_A Aₙ = RΓ(Uₙ, Fₙ)` for `U` étale over `X`

In Situation [Stacks, Tag 0CX4] let `K = DQ_X(L)` be the object of [Stacks, Tag 0CX5], for a
coherator `DQ_X` and a presentation `L ⟶ ∏ Fₙ ⟶ ∏ Fₙ ⟶ L[1]` of `L = R lim_{D(𝒪_X)} Fₙ`. For
every étale `j : U ⟶ X` with `U` quasi-compact and quasi-separated and every `n`, the canonical
map `RΓ(U, K) ⊗^𝐋_A Aₙ ⟶ RΓ(Uₙ, Fₙ)` of `D(Aₙ)` induced by `K ⟶ Fₙ`
(`AlgebraicGeometry.Space.FlatSheafExistenceSituation.etaleStageBaseChangeMap`) is an
isomorphism, where `Uₙ = U ×_X Xₙ`.

The proof is
`AlgebraicGeometry.Space.FlatSheafExistenceSituation.isIso_etaleStageBaseChangeMap_of_isIso` (the
source's argument: `Rj_*𝒪_U = hocolim Eₘ` with `Eₘ` perfect, [Stacks, Tag 0CRW], and `- ⊗^𝐋_A Aₙ`
commutes with homotopy colimits) with its input, [Stacks, Tag 0CX6] (1), supplied by
`AlgebraicGeometry.Space.FlatSheafExistenceSituation.isIso_limitTensorSectionsBaseChangeMap_of`,
whose compatibilities of the transitions are
`AlgebraicGeometry.Space.FlatSheafExistenceSituation.stageTransitionCounitCompatible` and
`AlgebraicGeometry.Space.FlatSheafExistenceSituation.stageTensorSectionsTransitionCompatible`.

## Main results

* `AlgebraicGeometry.Space.FlatSheafExistenceSituation.isIso_etaleStageBaseChangeMap`.

## References

* [Stacks Project, Tag 0CX8](https://stacks.math.columbia.edu/tag/0CX8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

universe u

namespace AlgebraicGeometry.Space

namespace FlatSheafExistenceSituation

variable (D : FlatSheafExistenceSituation.{u})

/-- **[Stacks, Tag 0CX8].** In Situation [Stacks, Tag 0CX4] let `K = DQ_X(L)` be as in
[Stacks, Tag 0CX5]: `DQ_X` is a coherator (`adj : ι ⊣ DQ_X`) and
`L ⟶ ∏ Fₙ ⟶ ∏ Fₙ ⟶ L[1]` (first map `p`) presents `L` as `R lim_{D(𝒪_X)} Fₙ`, with
canonical maps `φₙ : K ⟶ Fₙ` the counit followed by the projections. For every `n` and every
étale morphism `j : U ⟶ X` with `U` quasi-compact and quasi-separated, the canonical map
`RΓ(U, K) ⊗^𝐋_A Aₙ ⟶ RΓ(Uₙ, Fₙ)` of `D(Aₙ)` induced by `φₙ`, `Uₙ = U ×_X Xₙ`, is an
isomorphism. -/
@[stacks 0CX8 "the full statement: for every coherator DQ_X and every presentation of \
L = R lim F_n in D(O_X), every n and every etale U → X with U quasi-compact and \
quasi-separated, the canonical map RΓ(U, K) ⊗^L_A A_n → RΓ(U_n, F_n) in D(A_n) induced by \
K = DQ_X(L) → F_n is an isomorphism, U_n = U ×_X X_n, under exactly the source's hypotheses"]
theorem isIso_etaleStageBaseChangeMap
    {DQ : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left ⥤
      (spaceQuasicoherentProp D.B D.S D.containsLimitBase D.X.left).FullSubcategory}
    (adj : (spaceQuasicoherentProp D.B D.S D.containsLimitBase D.X.left).ι ⊣ DQ)
    {L : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left}
    (p : L ⟶ ∏ᶜ fun n : ℕ => D.derivedSystem.obj ⟨n⟩)
    (hp : ∃ δ : (∏ᶜ fun n : ℕ => D.derivedSystem.obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧,
      Triangle.mk p (Pi.lift fun n : ℕ => Pi.π (fun n : ℕ => D.derivedSystem.obj ⟨n⟩) n -
        Pi.π (fun n : ℕ => D.derivedSystem.obj ⟨n⟩) (n + 1) ≫
          D.derivedSystem.map (homOfLE (Nat.le_succ n)).op) δ ∈
        distTriang (spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left))
    (n : ℕ) {U : AlgebraicSpaces D.B D.S D.containsLimitBase} (j : U ⟶ D.X.left)
    (hj : IsEtale D.B D.S D.containsLimitBase j.hom)
    (hUqc : IsQuasiCompactSpace D.B D.S D.containsLimitBase U.1)
    (hUqs : IsAbsolutelyQuasiSeparated D.B D.S D.containsLimitBase D.B.contains_terminal U.1) :
    IsIso (D.etaleStageBaseChangeMap n j
      (D.isQuasiCompact_isQuasiSeparated_of_isEtale j hj hUqc hUqs).1
      (D.isQuasiCompact_isQuasiSeparated_of_isEtale j hj hUqc hUqs).2 adj p) :=
  D.isIso_etaleStageBaseChangeMap_of_isIso n j hj hUqc hUqs
    (D.isQuasiCompact_isQuasiSeparated_of_isEtale j hj hUqc hUqs).1
    (D.isQuasiCompact_isQuasiSeparated_of_isEtale j hj hUqc hUqs).2 adj p
    (D.isIso_limitTensorSectionsBaseChangeMap_of adj L p hp
      (fun m => D.stageTransitionCounitCompatible m)
      (fun E m => D.stageTensorSectionsTransitionCompatible m E) n)

end FlatSheafExistenceSituation

end AlgebraicGeometry.Space

end
