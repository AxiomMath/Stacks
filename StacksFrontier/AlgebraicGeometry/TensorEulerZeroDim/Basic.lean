module

public import StacksFrontier.AlgebraicGeometry.CurveTensorEulerUnit.Symmetry
public import StacksFrontier.AlgebraicGeometry.EulerCharDirectSum.Basic
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.ZeroDimensionalTensor
public import StacksCore.Tactic.StacksAttribute

/-!
# Clause (5) of Tag 0AYT: the Euler characteristic after tensoring, in dimension zero

[Stacks, Tag 0AYT] (5) says that for `X` proper over a field `k`, `𝒢` coherent with
`dim Supp 𝒢 ≤ 0` and `ℰ` locally free of rank `n`,

  `χ(X, ℰ ⊗ 𝒢) = n · χ(X, 𝒢)`.

This file proves the clause for an invertible `ℰ` and for `ℰ` finite locally free of rank one, and
proves the formula at rank `n` given a sheaf isomorphism `ℰ ⊗ 𝒢 ≅ 𝒢^{⊞ n}`. No finiteness of the
cohomology is assumed: the Euler characteristic is an isomorphism invariant
(`AlgebraicGeometry.eulerCharacteristic_eq_of_iso`), and the dimension of a finite power of a
vector space is a multiple of the dimension of that space whether or not the space is
finite-dimensional (`Module.finrank_fun_fin`).

## Main results

* `AlgebraicGeometry.exists_eulerCharacteristic_tensorSheaf_eq_mul_of_isInvertible`:
  `χ(X, ℳ ⊗ 𝒢) = 1 · χ(X, 𝒢)` for `ℳ` invertible.
* `exists_eulerCharacteristic_tensorSheaf_eq_mul_of_isFiniteLocallyFreeOfRank_one`:
  `χ(X, ℰ ⊗ 𝒢) = 1 · χ(X, 𝒢)` for `ℰ` finite locally free of rank one.
* `AlgebraicGeometry.exists_eulerCharacteristic_tensorSheaf_eq_mul_of_iso_biprodPow`:
  `χ(X, ℰ ⊗ 𝒢) = n · χ(X, 𝒢)` given an isomorphism `ℰ ⊗ 𝒢 ≅ 𝒢^{⊞ n}`.

## Implementation notes

The tensor product is written with the locally free factor first, whereas [Stacks, Tag 0AYT] (5)
writes the coherent factor first; the two orders are compared by
`Stacks.SheafOfModules.TensorPresentations.tensorSheafSwap`. On a scheme, finite local freeness of
rank one and invertibility agree by [Stacks, Tag 0B8M]
(`Stacks.SheafOfModules.Scheme.isInvertible_iff_isFiniteLocallyFreeOfRank_one`).

## References

* [Stacks Project, Tag 0AYT](https://stacks.math.columbia.edu/tag/0AYT)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **Clause (5) of [Stacks, Tag 0AYT] for an invertible factor.** For `X` proper over a field, `𝒢`
coherent with support of dimension at most zero and `ℳ` invertible, `ℳ ⊗ 𝒢` is coherent and
`χ(X, ℳ ⊗ 𝒢) = 1 · χ(X, 𝒢)`. -/
theorem exists_eulerCharacteristic_tensorSheaf_eq_mul_of_isInvertible [IsProper f]
    (M G : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M]
    [hG : SheafOfModules.IsCoherent G]
    (hdim : topologicalKrullDim (_root_.SheafOfModules.supp G) ≤ 0) :
    ∃ hT : ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (M)).obj (G))).IsCoherent,
      @eulerCharacteristic k _ X f _ ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (M)).obj (G))) hT =
        (1 : ℤ) * eulerCharacteristic k f G := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨e₀⟩ := nonempty_tensorModulesIso_of_topologicalKrullDim_supp_le_zero G hdim M
  have e : (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj M).obj G : X.Modules) ≅ G :=
    (Stacks.SheafOfModules.TensorPresentations.tensorSheafSwap X.toRingedSpace M G).trans e₀
  have hT : (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj M).obj G).IsCoherent := by
    let P : ObjectProperty X.Modules := fun N => N.IsCoherent
    let : P.IsWeakSerreClass := _root_.SheafOfModules.coherentModules_isWeakSerreClass
    exact P.prop_of_iso e.symm hG
  refine ⟨hT, ?_⟩
  rw [@eulerCharacteristic_eq_of_iso k _ X f _ _ _ hT hG e, one_mul]

/-- **Clause (5) of [Stacks, Tag 0AYT] at rank one.** For `X` proper over a field, `𝒢` coherent
with support of dimension at most zero and `ℰ` finite locally free of rank one, `ℰ ⊗ 𝒢` is coherent
and `χ(X, ℰ ⊗ 𝒢) = 1 · χ(X, 𝒢)`. -/
theorem exists_eulerCharacteristic_tensorSheaf_eq_mul_of_isFiniteLocallyFreeOfRank_one
    [IsProper f] (E G : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E 1]
    [SheafOfModules.IsCoherent G]
    (hdim : topologicalKrullDim (_root_.SheafOfModules.supp G) ≤ 0) :
    ∃ hT : ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (G))).IsCoherent,
      @eulerCharacteristic k _ X f _ ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (G))) hT =
        (1 : ℤ) * eulerCharacteristic k f G :=
  have : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 E :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ E).1
      ((Stacks.SheafOfModules.Scheme.isInvertible_iff_isFiniteLocallyFreeOfRank_one X E).2 ‹_›)
  exists_eulerCharacteristic_tensorSheaf_eq_mul_of_isInvertible k f E G hdim

/-- **Clause (5) of [Stacks, Tag 0AYT] at rank `n`, from a sheaf isomorphism.** For `X` proper over
a field and `𝒢` coherent, an isomorphism `ℰ ⊗ 𝒢 ≅ 𝒢^{⊞ n}` makes `ℰ ⊗ 𝒢` coherent, with
`χ(X, ℰ ⊗ 𝒢) = n · χ(X, 𝒢)`. -/
theorem exists_eulerCharacteristic_tensorSheaf_eq_mul_of_iso_biprodPow [IsProper f]
    (E G : X.Modules) [SheafOfModules.IsCoherent G] (n : ℕ)
    (e : ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (G)) : X.Modules)
      ≅
      Scheme.Modules.biprodPow G n) :
    ∃ hT : ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (G))).IsCoherent,
      @eulerCharacteristic k _ X f _ ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (G))) hT =
        (n : ℤ) * eulerCharacteristic k f G :=
  exists_eulerCharacteristic_eq_mul_of_iso_biprodPow k f G _ n e

end AlgebraicGeometry

end
