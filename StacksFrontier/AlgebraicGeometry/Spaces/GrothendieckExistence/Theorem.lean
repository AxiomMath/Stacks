module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.FlatAlgebraization
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.InverseSystemExistence

public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowSerreImage
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDerivedCoheratorGlobalSections
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentWeakSerreUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.SpaceDerivedCategory
/-!
# Grothendieck's existence theorem for algebraic spaces

[Stacks, Tag 0CXB]: in Situation [Stacks, Tag 0CX4] there is a finitely presented `𝒪_X`-module
`F`, flat over `A`, with support proper over `A`, such that `Fₙ = F ⊗_{𝒪_X} 𝒪_{Xₙ}` for all `n`
compatibly with the maps `φₙ`.

## Main results

* `InverseSystemExistenceSituation.exists_flat_algebraization_of_isExistenceNeighbourhood`: the
  conclusion of Stacks 0CXB, for the situation in the form
  `AlgebraicGeometry.Space.InverseSystemExistenceSituation`, from an existence neighbourhood in the
  sense of Stacks 0CX9. It is in the namespace `AlgebraicGeometry.Space`.

## References

* [Stacks Project, Tag 0CXB](https://stacks.math.columbia.edu/tag/0CXB)
* [Stacks Project, Tag 0CX9](https://stacks.math.columbia.edu/tag/0CX9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.GrothendieckExistence (limitBase baseAt)

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

namespace InverseSystemExistenceSituation

/-- **The conclusion of Stacks 0CXB from an existence neighbourhood**, in the form of the situation
`AlgebraicGeometry.Space.InverseSystemExistenceSituation`. -/
theorem exists_flat_algebraization_of_isExistenceNeighbourhood
    (D : FlatSheafExistenceSituation.{u})
    {K : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left}
    {π : ∀ n : ℕ, K ⟶ D.derivedSystem.obj (op n)}
    (hπ : ∀ n : ℕ, π (n + 1) ≫ D.derivedSystem.map (homOfLE (Nat.le_succ n)).op = π n)
    {W : Subfunctor D.X.left.1} {hW : IsOpenSubspace D.B D.S D.containsLimitBase W}
    (hN : D.IsExistenceNeighbourhood K π W hW) :
    ∃ F : Modules.{u, u} D.toInverseSystemExistenceSituation.B
      (limitBase D.toInverseSystemExistenceSituation.system)
      D.toInverseSystemExistenceSituation.containsLimitBase
      D.toInverseSystemExistenceSituation.X.left.1 D.toInverseSystemExistenceSituation.X.left.2,
        F.IsFinitePresentationOnSite ∧
          IsFlatOver D.toInverseSystemExistenceSituation.B
            (limitBase D.toInverseSystemExistenceSituation.system)
            D.toInverseSystemExistenceSituation.containsLimitBase
            D.toInverseSystemExistenceSituation.X.left.2
            D.toInverseSystemExistenceSituation.X.hom.hom F ∧
          ∃ hcl : IsClosed (supportOfSheaf D.toInverseSystemExistenceSituation.B
            (limitBase D.toInverseSystemExistenceSituation.system)
            D.toInverseSystemExistenceSituation.containsLimitBase
            D.toInverseSystemExistenceSituation.X.left.1
              ((SheafOfModules.toSheaf _).obj F)),
            IsProperOver D.toInverseSystemExistenceSituation.B
              (limitBase D.toInverseSystemExistenceSituation.system)
              D.toInverseSystemExistenceSituation.containsLimitBase
              D.toInverseSystemExistenceSituation.X.left.2
              (schemeSpace (limitBaseObject D.toInverseSystemExistenceSituation.system
                D.toInverseSystemExistenceSituation.B
                D.toInverseSystemExistenceSituation.containsLimitBase)).2
                D.toInverseSystemExistenceSituation.X.hom.hom
              (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation
                D.toInverseSystemExistenceSituation.B
                (limitBase D.toInverseSystemExistenceSituation.system)
                D.toInverseSystemExistenceSituation.containsLimitBase
                  D.toInverseSystemExistenceSituation.finitePresentation.1)
              (supportOfSheaf D.toInverseSystemExistenceSituation.B
                (limitBase D.toInverseSystemExistenceSituation.system)
                D.toInverseSystemExistenceSituation.containsLimitBase
                D.toInverseSystemExistenceSituation.X.left.1
                ((SheafOfModules.toSheaf _).obj F)) hcl ∧
            ∃ α : ∀ n : ℕ, (modulePullback D.toInverseSystemExistenceSituation.B
              (limitBase D.toInverseSystemExistenceSituation.system)
              D.toInverseSystemExistenceSituation.containsLimitBase
                (spaceProjection D.toInverseSystemExistenceSituation.system
                  D.toInverseSystemExistenceSituation.B
                  D.toInverseSystemExistenceSituation.containsLimitBase
                  D.toInverseSystemExistenceSituation.containsBaseAt
                  D.toInverseSystemExistenceSituation.X n)).obj F ≅
                  (D.toInverseSystemExistenceSituation.sheaf n).obj,
              ∀ n : ℕ,
                (modulePullback D.toInverseSystemExistenceSituation.B
                  (limitBase D.toInverseSystemExistenceSituation.system)
                  D.toInverseSystemExistenceSituation.containsLimitBase
                    (transitionSpace D.toInverseSystemExistenceSituation.system
                      D.toInverseSystemExistenceSituation.B
                      D.toInverseSystemExistenceSituation.containsLimitBase
                      D.toInverseSystemExistenceSituation.containsBaseAt
                      D.toInverseSystemExistenceSituation.X n)).map
                      (α (n + 1)).hom ≫ (D.toInverseSystemExistenceSituation.φ n).hom =
                  (modulePullbackCompIso D.toInverseSystemExistenceSituation.B
                    (limitBase D.toInverseSystemExistenceSituation.system)
                    D.toInverseSystemExistenceSituation.containsLimitBase
                      (transitionSpace D.toInverseSystemExistenceSituation.system
                        D.toInverseSystemExistenceSituation.B
                        D.toInverseSystemExistenceSituation.containsLimitBase
                        D.toInverseSystemExistenceSituation.containsBaseAt
                        D.toInverseSystemExistenceSituation.X n)
                      (spaceProjection D.toInverseSystemExistenceSituation.system
                        D.toInverseSystemExistenceSituation.B
                        D.toInverseSystemExistenceSituation.containsLimitBase
                        D.toInverseSystemExistenceSituation.containsBaseAt
                        D.toInverseSystemExistenceSituation.X
                        (n + 1))).hom.app F ≫
                    eqToHom (congrArg (fun g => (modulePullback
                      D.toInverseSystemExistenceSituation.B
                      (limitBase D.toInverseSystemExistenceSituation.system)
                      D.toInverseSystemExistenceSituation.containsLimitBase g).obj F)
                      (transitionSpace_spaceProjection D.toInverseSystemExistenceSituation.system
                        D.toInverseSystemExistenceSituation.B
                        D.toInverseSystemExistenceSituation.containsLimitBase
                        D.toInverseSystemExistenceSituation.containsBaseAt
                          D.toInverseSystemExistenceSituation.X n)) ≫
                    (α n).hom := by
  obtain ⟨G, hGfp, hflat, ⟨hcl, hprop⟩, α, hα⟩ :=
    D.exists_algebraization_of_isExistenceNeighbourhood hπ hN
  have hα' : ∀ n : ℕ, ModulePullbackCompatible
      (transitionSpace D.toInverseSystemExistenceSituation.system
        D.toInverseSystemExistenceSituation.B D.toInverseSystemExistenceSituation.containsLimitBase
        D.toInverseSystemExistenceSituation.containsBaseAt D.toInverseSystemExistenceSituation.X n)
      (spaceProjection D.toInverseSystemExistenceSituation.system
        D.toInverseSystemExistenceSituation.B D.toInverseSystemExistenceSituation.containsLimitBase
        D.toInverseSystemExistenceSituation.containsBaseAt D.toInverseSystemExistenceSituation.X
        (n + 1))
      (spaceProjection D.toInverseSystemExistenceSituation.system
        D.toInverseSystemExistenceSituation.B D.toInverseSystemExistenceSituation.containsLimitBase
        D.toInverseSystemExistenceSituation.containsBaseAt D.toInverseSystemExistenceSituation.X n)
      (transitionSpace_spaceProjection D.toInverseSystemExistenceSituation.system
        D.toInverseSystemExistenceSituation.B D.toInverseSystemExistenceSituation.containsLimitBase
        D.toInverseSystemExistenceSituation.containsBaseAt D.toInverseSystemExistenceSituation.X n)
      G (D.toInverseSystemExistenceSituation.φ n) (α (n + 1)).hom (α n).hom := fun n => hα n
  exact ⟨G, hGfp, hflat, hcl, hprop, α, fun n => (hα' n).eq⟩

end InverseSystemExistenceSituation

end AlgebraicGeometry.Space

end
