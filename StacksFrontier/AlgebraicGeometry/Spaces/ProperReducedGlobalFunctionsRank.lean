module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProperGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperReducedGlobalFunctionsFinite

/-!
# Dimension of the global functions of a reduced proper space over an algebraically closed field

Let `k` be an algebraically closed field and let `X` be a reduced algebraic space proper over
`Spec k`. Then `dim_k Γ(X, 𝒪_X)` is the number of connected components of `|X|`.

## Main results

* `AlgebraicGeometry.Space.finrank_globalFunctions_eq_card_connectedComponents`: for `X` reduced
  and proper over an algebraically closed field `k`, `dim_k Γ(X, 𝒪_X) = #π₀(|X|)`.

## Implementation notes

`Γ(X, 𝒪_X)` is a finite `k`-module
(`AlgebraicGeometry.Space.module_finite_globalFunctions_of_isProper`, by Chow's lemma), hence an
Artinian ring, so the componentwise factorization of Stacks 0DMY
(`AlgebraicGeometry.Space.nonempty_componentwiseArtinianFactorization_of_isQuasiCompactSpace`)
applies: `Γ(X, 𝒪_X)` is the product over the finitely many connected components of `|X|` of
rings which are fields because `X` is reduced
(`AlgebraicGeometry.Space.isField_componentFunctions`). Each factor is finite over `k`, hence
equal to `k`, `k` being algebraically closed.

## References

* [Stacks Project, Tag 0DMY](https://stacks.math.columbia.edu/tag/0DMY)
* [Stacks Project, Tag 0E1E](https://stacks.math.columbia.edu/tag/0E1E)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (k : Type u) [Field k] (B : BigFppfSite.{u}) (hS : B.Contains (Spec (.of k)))
    (X : (BigFppfOver B (Spec (.of k)) hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of k)) hS X)
    (f : X ⟶ yoneda.obj (baseObject k B hS))

/-- A field finite over an algebraically closed field `k` is linearly equivalent to `k`. -/
private theorem nonempty_linearEquiv_of_isField_of_isAlgClosed {F : Type*} [CommRing F]
    [Algebra k F] [IsAlgClosed k] [Module.Finite k F] (hF : IsField F) :
    Nonempty (k ≃ₗ[k] F) := by
  have : IsDomain F := hF.isDomain
  have : Algebra.IsIntegral k F := Algebra.IsIntegral.of_finite k F
  exact ⟨LinearEquiv.ofBijective (Algebra.linearMap k F)
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k))⟩

/-- A ring which is a field and finite over an algebraically closed field `k` is
one-dimensional over `k`. -/
theorem finrank_eq_one_of_isField_of_isAlgClosed {F : Type*} [CommRing F] [Algebra k F]
    [IsAlgClosed k] [Module.Finite k F] (hF : IsField F) : Module.finrank k F = 1 := by
  obtain ⟨e⟩ := nonempty_linearEquiv_of_isField_of_isAlgClosed k hF
  rw [← e.finrank_eq, Module.finrank_self]

include hX in
/-- **The global functions of a reduced proper algebraic space over an algebraically closed
field count its connected components.** For `X` reduced and proper over `Spec k` with `k`
algebraically closed, `dim_k Γ(X, 𝒪_X)` is the number of connected components of `|X|`. -/
theorem finrank_globalFunctions_eq_card_connectedComponents [IsAlgClosed k]
    (hf : IsProper B (Spec (.of k)) hS f)
    (hred : HasEtaleLocalProperty B (Spec (.of k)) hS X
      (fun T : Scheme.{u} => _root_.AlgebraicGeometry.IsReduced T)) :
    Module.finrank k (globalFunctions B (Spec (.of k)) hS X) =
      Nat.card (ConnectedComponents (points B (Spec (.of k)) hS X)) := by
  classical
  have hfin : Module.Finite k (globalFunctions B (Spec (.of k)) hS X) :=
    module_finite_globalFunctions_of_isProper B k hS ⟨X, hX⟩ f hf hred
  obtain ⟨fac⟩ := nonempty_componentwiseArtinianFactorization_of_isQuasiCompactSpace k B hS X hX
    (isQuasiCompactSpace_of_isProper_baseObject k B hS X hX f hf)
    (hasEtaleLocalProperty_isLocallyNoetherian_of_isProper k B hS X hX f hf)
    (IsArtinianRing.of_finite k _)
  have := finite_connectedComponents_points_of_isProper k B hS X hX f hf
  let _ := Fintype.ofFinite (ConnectedComponents (points B (Spec (.of k)) hS X))
  let (c : ConnectedComponents (points B (Spec (.of k)) hS X)) :
      Algebra k (componentFunctions B (Spec (.of k)) hS X c) := fac.factorAlgebra c
  have hprod : Module.Finite k
      (∀ c : ConnectedComponents (points B (Spec (.of k)) hS X),
        componentFunctions B (Spec (.of k)) hS X c) :=
    Module.Finite.equiv fac.equivalence.toLinearEquiv
  have hfc (c : ConnectedComponents (points B (Spec (.of k)) hS X)) :
      Module.Finite k (componentFunctions B (Spec (.of k)) hS X c) :=
    Module.Finite.of_surjective (LinearMap.proj c) (LinearMap.proj_surjective c)
  have hone (c : ConnectedComponents (points B (Spec (.of k)) hS X)) :
      Module.finrank k (componentFunctions B (Spec (.of k)) hS X c) = 1 := by
    have := hfc c
    exact finrank_eq_one_of_isField_of_isAlgClosed k
      (isField_componentFunctions k B hS X hX hred fac c)
  have (c : ConnectedComponents (points B (Spec (.of k)) hS X)) :
      Module.Free k (componentFunctions B (Spec (.of k)) hS X c) := by
    have := hfc c
    obtain ⟨e⟩ := nonempty_linearEquiv_of_isField_of_isAlgClosed k
      (isField_componentFunctions k B hS X hX hred fac c)
    exact Module.Free.of_equiv e
  rw [fac.equivalence.toLinearEquiv.finrank_eq, Module.finrank_pi_fintype]
  simp [hone, Nat.card_eq_fintype_card]

end AlgebraicGeometry.Space

end
