module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.FlatAlgebraization
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.ExistenceNeighbourhoodExists
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.FlatSheafDerivedLimit
public import StacksCore.Tactic.StacksAttribute

/-!
# Grothendieck's existence theorem for algebraic spaces

In Situation [Stacks, Tag 0CX4] there exists a finitely presented `𝒪_X`-module `F`, flat over
`A`, with support proper over `A`, such that `Fₙ = F ⊗_{𝒪_X} 𝒪_{Xₙ}` for all `n` compatibly with
the maps `φₙ` ([Stacks, Tag 0CXB]).

The proof follows the source: Lemma 0CX5 gives a coherator `DQ_X` and a derived limit
`L = R lim_{D(𝒪_X)} Fₙ`, whose object `K = DQ_X(L)` comes with compatible maps `K ⟶ Fₙ`
(`FlatSheafExistenceSituation.derivedLimitProjection_comp_map`); Lemma 0CX9 gives an open
subspace `W ⊂ X` containing `X₀` with its three conclusions; and
`FlatSheafExistenceSituation.exists_algebraization_of_isExistenceNeighbourhood` carries out the
rest of the source's argument (0CXA, the direct image along `W ⟶ X`, and flatness over `A` from
the proper support).

## Main results

* `AlgebraicGeometry.Space.FlatSheafExistenceSituation.exists_algebraization`: **Stacks 0CXB**.

## References

* [Stacks Project, Tag 0CXB](https://stacks.math.columbia.edu/tag/0CXB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open AlgebraicGeometry.GrothendieckExistence (limitBase baseAt)

universe u

namespace AlgebraicGeometry.Space.FlatSheafExistenceSituation

attribute [local instance] pointTopology

variable (D : FlatSheafExistenceSituation.{u})

/-- **Grothendieck's existence theorem, [Stacks, Tag 0CXB].** In Situation [Stacks, Tag 0CX4]
there exists a finitely presented `𝒪_X`-module `F`, flat over `A`, whose support is closed and
proper over `A`, with identifications `αₙ : F ⊗_{𝒪_X} 𝒪_{Xₙ} = iₙ^* F ≅ Fₙ` for all `n`,
compatible with the maps `φₙ : Fₙ₊₁ ⊗ 𝒪_{Xₙ} ≅ Fₙ` through `tₙ^* iₙ₊₁^* = iₙ^*`. -/
@[stacks 0CXB]
theorem exists_algebraization :
    ∃ F : Modules.{u, u} D.B D.S D.containsLimitBase D.X.left.1 D.X.left.2,
      F.IsFinitePresentationOnSite ∧
        IsFlatOver D.B D.S D.containsLimitBase D.X.left.2 D.X.hom.hom F ∧
        ∃ hcl : IsClosed (supportOfSheaf D.B D.S D.containsLimitBase D.X.left.1
            ((SheafOfModules.toSheaf _).obj F)),
          IsProperOver D.B D.S D.containsLimitBase D.X.left.2
            (schemeSpace (limitBaseObject D.system D.B D.containsLimitBase)).2 D.X.hom.hom
            (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation D.B D.S
              D.containsLimitBase D.finitePresentation.1)
            (supportOfSheaf D.B D.S D.containsLimitBase D.X.left.1
              ((SheafOfModules.toSheaf _).obj F)) hcl ∧
          ∃ α : ∀ n : ℕ, (modulePullback D.B D.S D.containsLimitBase
              (D.closedImmersion n)).obj F ≅ D.F n,
            ∀ n : ℕ,
              (modulePullback D.B D.S D.containsLimitBase (D.transition n)).map
                  (α (n + 1)).hom ≫ (D.φ n).hom =
                (modulePullbackCompIso D.B D.S D.containsLimitBase (D.transition n)
                    (D.closedImmersion (n + 1))).hom.app F ≫
                  eqToHom (congrArg (fun g => (modulePullback D.B D.S
                    D.containsLimitBase g).obj F) (D.transition_closedImmersion n)) ≫
                  (α n).hom := by
  obtain ⟨hadj, ⟨L, hL⟩, -⟩ := D.derivedLimit_bounded
  obtain ⟨DQ, ⟨adj⟩⟩ := hadj.exists_rightAdjoint
  obtain ⟨p, δ, hT⟩ := hL
  obtain ⟨W, hW, hN⟩ := D.exists_isExistenceNeighbourhood adj p ⟨δ, hT⟩
  obtain ⟨G, hGfp, hflat, ⟨hcl, hprop⟩, α, hα⟩ :=
    D.exists_algebraization_of_isExistenceNeighbourhood (D.derivedLimitProjection_comp_map adj p hT)
      hN
  exact ⟨G, hGfp, hflat, hcl, hprop, α, fun n => (hα n).eq⟩

end AlgebraicGeometry.Space.FlatSheafExistenceSituation

end
