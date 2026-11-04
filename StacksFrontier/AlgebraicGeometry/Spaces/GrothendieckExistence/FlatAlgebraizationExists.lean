module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.ExistenceNeighbourhoodExists
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.FlatSheafDerivedLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.Theorem

public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowSerreImage
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDerivedCoheratorGlobalSections
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentWeakSerreUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.SpaceDerivedCategory
/-!
# Grothendieck's existence theorem for algebraic spaces, with nothing assumed

In Situation [Stacks, Tag 0CX4] there is a finitely presented `𝒪_X`-module `F`, flat over `A`,
with support proper over `A`, such that `Fₙ = F ⊗_{𝒪_X} 𝒪_{Xₙ}` for all `n` compatibly with the
maps `φₙ` ([Stacks, Tag 0CXB]).

The source's proof starts from `K = DQ_X(R lim Fₙ)` and the open subspace `W ⊆ X` of
[Stacks, Tag 0CX9] on which `K` is a finitely presented module restricting to the `Fₙ`. Here the
coherator `DQ_X` exists by the first part of [Stacks, Tag 0CX5]
(`AlgebraicGeometry.Space.FlatSheafExistenceSituation.derivedLimit_bounded`), the derived limit
`R lim Fₙ` exists by its second part, [Stacks, Tag 0CX9] is
`AlgebraicGeometry.Space.FlatSheafExistenceSituation.exists_isExistenceNeighbourhood`, and the
rest of the proof is `exists_flat_algebraization_of_isExistenceNeighbourhood` in the namespace
`AlgebraicGeometry.Space.InverseSystemExistenceSituation`.

## Main results

* `AlgebraicGeometry.Space.InverseSystemExistenceSituation.exists_flat_algebraization`: the
  conclusion of Stacks 0CXB for every situation in the form
  `AlgebraicGeometry.Space.InverseSystemExistenceSituation`, with no hypothesis. It is stated in
  the form the proof of Stacks 09DS consumes and carries no `@[stacks]` attribute.

## References

* [Stacks Project, Tag 0CXB](https://stacks.math.columbia.edu/tag/0CXB)
* [Stacks Project, Tag 0CX9](https://stacks.math.columbia.edu/tag/0CX9)
* [Stacks Project, Tag 0CX5](https://stacks.math.columbia.edu/tag/0CX5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open AlgebraicGeometry.GrothendieckExistence (limitBase baseAt)

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

namespace InverseSystemExistenceSituation

/-- **Grothendieck's existence theorem for algebraic spaces** (the conclusion of Stacks 0CXB, with
nothing assumed). In Situation 0CX4 there is a finitely presented module `F` on `X`, flat over `A`,
whose support is closed and proper over `A`, with isomorphisms `αₙ : F|_{Xₙ} ≅ Fₙ` compatible with
the `φₙ`. -/
theorem exists_flat_algebraization (s : InverseSystemExistenceSituation.{u}) :
    ∃ F : Modules.{u, u} s.B (limitBase s.system) s.containsLimitBase s.X.left.1 s.X.left.2,
      F.IsFinitePresentationOnSite ∧
        IsFlatOver s.B (limitBase s.system) s.containsLimitBase s.X.left.2 s.X.hom.hom F ∧
        ∃ hcl : IsClosed (supportOfSheaf s.B (limitBase s.system) s.containsLimitBase s.X.left.1
            ((SheafOfModules.toSheaf _).obj F)),
          IsProperOver s.B (limitBase s.system) s.containsLimitBase s.X.left.2
            (schemeSpace (limitBaseObject s.system s.B s.containsLimitBase)).2 s.X.hom.hom
            (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation s.B (limitBase s.system)
              s.containsLimitBase s.finitePresentation.1)
            (supportOfSheaf s.B (limitBase s.system) s.containsLimitBase s.X.left.1
              ((SheafOfModules.toSheaf _).obj F)) hcl ∧
          ∃ α : ∀ n : ℕ, (modulePullback s.B (limitBase s.system) s.containsLimitBase
              (spaceProjection s.system s.B s.containsLimitBase s.containsBaseAt s.X n)).obj F ≅
                (s.sheaf n).obj,
            ∀ n : ℕ,
              (modulePullback s.B (limitBase s.system) s.containsLimitBase
                  (transitionSpace s.system s.B s.containsLimitBase s.containsBaseAt s.X n)).map
                    (α (n + 1)).hom ≫ (s.φ n).hom =
                (modulePullbackCompIso s.B (limitBase s.system) s.containsLimitBase
                    (transitionSpace s.system s.B s.containsLimitBase s.containsBaseAt s.X n)
                    (spaceProjection s.system s.B s.containsLimitBase s.containsBaseAt s.X
                      (n + 1))).hom.app F ≫
                  eqToHom (congrArg (fun g => (modulePullback s.B (limitBase s.system)
                    s.containsLimitBase g).obj F)
                    (transitionSpace_spaceProjection s.system s.B s.containsLimitBase
                      s.containsBaseAt s.X n)) ≫
                  (α n).hom := by
  obtain ⟨D, rfl⟩ := exists_eq_toInverseSystemExistenceSituation s
  obtain ⟨hDQ, ⟨L, p, δ, hT⟩, -, -⟩ := D.derivedLimit_bounded
  let adj := Adjunction.ofIsLeftAdjoint
    (spaceQuasicoherentProp D.B D.S D.containsLimitBase D.X.left).ι
  obtain ⟨W, hW, hN⟩ := D.exists_isExistenceNeighbourhood adj p ⟨δ, hT⟩
  exact exists_flat_algebraization_of_isExistenceNeighbourhood D
    (fun n => D.derivedLimitProjection_comp_map adj p hT n) hN

end InverseSystemExistenceSituation

end AlgebraicGeometry.Space

end
