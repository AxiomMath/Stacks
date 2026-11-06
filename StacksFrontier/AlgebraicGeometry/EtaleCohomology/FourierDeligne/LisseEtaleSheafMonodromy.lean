module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.LevelDichotomyBasePoint
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.ContinuousModuleLevelDichotomyMatrix
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.ArtinSchreierKernel

/-!
# The monodromy of the lisse sheaf of a representation

Let `X` be a connected scheme with a geometric point `x̄`, `Λ` a finite commutative ring and `P` a
finite `Λ`-module with a continuous action of `π₁(X, x̄)`. The lisse sheaf `ℱ_P` (the inverse of
the equivalence of Tag 0DV5 (3), read on Mathlib's small étale site) is locally constant of finite
type, and its monodromy module at `x̄` is `P` again
(`Stacks.EtaleCohomology.nonempty_monodromy_lisseEtaleSheaf_iso`: the counit of the equivalence).
Hence the level dichotomy of `P` is the level dichotomy of the monodromy modules of `ℱ_P` at every
geometric point of `X` (`Stacks.EtaleCohomology.continuousModuleLevelDichotomy_lisseEtaleSheaf`,
through the independence of the base point), and, when `P` is free with the action given by
matrices over a ring `O` up to units, it follows from the matrix form of the dichotomy
(`Stacks.EtaleCohomology.continuousModuleLevelDichotomy_lisseEtaleSheaf_of_matrix`).

## Main results

* `Stacks.EtaleCohomology.isFiniteTypeLocallyConstant_lisseEtaleSheaf`: `ℱ_P` is locally constant
  of finite type.
* `Stacks.EtaleCohomology.nonempty_monodromy_lisseEtaleSheaf_iso`: the monodromy module of `ℱ_P` at
  `x̄` is isomorphic to `P`.
* `Stacks.EtaleCohomology.continuousModuleLevelDichotomy_lisseEtaleSheaf`: the level dichotomy of
  `P` holds for the monodromy modules of `ℱ_P` at every geometric point.
* `Stacks.EtaleCohomology.continuousModuleLevelDichotomy_lisseEtaleSheaf_of_matrix`: the same,
  from the dichotomy for a set of matrices acting on `Λ^ι` up to units.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.GroupCohomology Matrix

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  {Λ : Type} [CommRing Λ] [Finite Λ]

/-- **The lisse sheaf `ℱ_P` is locally constant of finite type.** -/
theorem isFiniteTypeLocallyConstant_lisseEtaleSheaf
    (P : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x)) :
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ X.1.smallEtaleTopology
      ((lisseEtaleSheaf B X x Λ).obj P) :=
  ((finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B X x Λ).inverse.obj P).property

/-- **The monodromy of `ℱ_P` at `x̄` is `P`**: the counit of the equivalence of Tag 0DV5 (3). -/
theorem nonempty_monodromy_lisseEtaleSheaf_iso
    (P : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x))
    (h : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ X.1.smallEtaleTopology
      ((lisseEtaleSheaf B X x Λ).obj P)) :
    Nonempty ((finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B X x Λ).functor.obj
      ⟨(lisseEtaleSheaf B X x Λ).obj P, h⟩ ≅ P) :=
  ⟨(finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B X x Λ).counitIso.app P⟩

/-- **The level dichotomy of `P` holds for the monodromy of `ℱ_P` at every geometric point.** -/
theorem continuousModuleLevelDichotomy_lisseEtaleSheaf
    (P : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x))
    {ℓ N c₀ : ℕ} (hP : ContinuousModuleLevelDichotomy P ℓ N c₀) (x' : GeometricPoint X.1)
    (h : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ X.1.smallEtaleTopology
      ((lisseEtaleSheaf B X x Λ).obj P)) :
    ContinuousModuleLevelDichotomy
      ((finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B X x' Λ).functor.obj
        ⟨(lisseEtaleSheaf B X x Λ).obj P, h⟩) ℓ N c₀ := by
  obtain ⟨e⟩ := nonempty_monodromy_lisseEtaleSheaf_iso B X x P h
  exact continuousModuleLevelDichotomy_of_basePoint B X x x' h (hP.of_iso e.symm)

/-- **The level dichotomy for the monodromy of `ℱ_P`, from matrices**: if `P` is identified with
`Λ^ι` so that a set `S₀` of matrices over `O` acts through `π₁(X, x̄)` up to units, and the
`S₀`-stable submodules of `Λ^ι` satisfy the dichotomy at `ℓ, N, c₀`, then the monodromy modules
of `ℱ_P` satisfy it at every geometric point. -/
theorem continuousModuleLevelDichotomy_lisseEtaleSheaf_of_matrix {O : Type*} [CommRing O]
    [Algebra O Λ] {ι : Type*} [Fintype ι] [DecidableEq ι] (S₀ : Set (Matrix ι ι O))
    (P : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x))
    (e : P.obj.obj.obj.V ≃ₗ[Λ] (ι → Λ))
    (hS₀ : ∀ a ∈ S₀, ∃ g : EtaleFundamentalGroup X.1 x, ∃ c : Λˣ, ∀ v,
      e ((P.obj.obj.obj.ρ g).asHom.hom v) = c • (a.map (algebraMap O Λ) *ᵥ e v))
    (ℓ : O) (ℓₙ : ℕ) (hℓ : algebraMap O Λ ℓ = ℓₙ) (N c₀ : ℕ)
    (hD : ∀ S : Submodule Λ (ι → Λ), (∀ a ∈ S₀, ∀ v ∈ S, a.map (algebraMap O Λ) *ᵥ v ∈ S) →
      (∃ v ∈ S, ℓ ^ N • v ≠ 0) → ∀ w : ι → Λ, ℓ ^ c₀ • w ∈ S) (x' : GeometricPoint X.1)
    (h : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ X.1.smallEtaleTopology
      ((lisseEtaleSheaf B X x Λ).obj P)) :
    ContinuousModuleLevelDichotomy
      ((finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B X x' Λ).functor.obj
        ⟨(lisseEtaleSheaf B X x Λ).obj P, h⟩) ℓₙ N c₀ :=
  continuousModuleLevelDichotomy_lisseEtaleSheaf B X x P
    (continuousModuleLevelDichotomy_of_matrix S₀ e hS₀ ℓ ℓₙ hℓ N c₀ hD) x' h

end Stacks.EtaleCohomology

end
