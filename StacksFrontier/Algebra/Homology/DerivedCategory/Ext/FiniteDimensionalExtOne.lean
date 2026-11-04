module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! # Finiteness of `Ext¹` from a projective presentation

Let `𝒜` be an abelian category which is linear over a field `k`, and let

`0 ⟶ K ⟶ P ⟶ M ⟶ 0`

be a short exact sequence in `𝒜` with `P` projective — a *projective presentation* of `M`, with
`K` its module of relations. Then for every object `Y` the first extension group `Ext¹(M, Y)` is
a quotient of the space of maps `K ⟶ Y`; in particular it is finite dimensional over `k` as soon
as `K ⟶ Y` is.

This is the elementary half of the computation of `Ext¹` by a presentation: the connecting map
of the contravariant long exact sequence, which is composition with the class of the sequence in
`Ext¹(M, K)`, lands in `Ext¹(M, Y)` and is surjective there because `Ext¹(P, Y)` vanishes for
projective `P`. No resolution of `K` is needed and no finiteness or Noetherian hypothesis on `𝒜`
enters: only a single projective presentation whose relation object has a finite-dimensional
space of maps into `Y`.

## Main results

* `CategoryTheory.Abelian.Ext.extClassComp`: composition with the class of a short exact
  sequence, as a `k`-linear map `(S.X₁ ⟶ Y) →ₗ[k] Ext¹(S.X₃, Y)`.
* `CategoryTheory.Abelian.Ext.surjective_extClassComp`: it is surjective when `S.X₂` is
  projective.
* `CategoryTheory.Abelian.Ext.finite_extOne_of_shortExact_of_projective`: hence `Ext¹(S.X₃, Y)`
  is finite dimensional over `k` whenever `S.X₁ ⟶ Y` is.
-/

@[expose] public noncomputable section

universe t w v u

namespace CategoryTheory.Abelian.Ext

variable {k : Type t} [Field k] {C : Type u} [Category.{v} C] [Abelian C] [Linear k C]
  [HasExt.{w} C] {S : ShortComplex C} (hS : S.ShortExact) (Y : C)

/-- Composition with the class in `Ext¹(S.X₃, S.X₁)` of a short exact sequence `S`, read as a
`k`-linear map from the maps `S.X₁ ⟶ Y` to `Ext¹(S.X₃, Y)`.

This is the connecting map of the contravariant long exact sequence of `S` in degree zero,
transported along the identification of `Ext⁰` with the space of maps. -/
def extClassComp : (S.X₁ ⟶ Y) →ₗ[k] Ext.{w} S.X₃ Y 1 :=
  (bilinearCompOfLinear k S.X₃ S.X₁ Y 1 0 1 (add_zero 1) hS.extClass).comp
    (linearEquiv₀ (R := k)).symm.toLinearMap

/-- The map `extClassComp` sends `f : S.X₁ ⟶ Y` to the composition of the class of `S` with
`mk₀ f`. -/
theorem extClassComp_apply (f : S.X₁ ⟶ Y) :
    extClassComp (k := k) hS Y f = hS.extClass.comp (mk₀ f) (add_zero 1) := rfl

/-- If the middle object of a short exact sequence is projective, then composition with the
class of the sequence is surjective onto `Ext¹` of its right-hand object. -/
theorem surjective_extClassComp [Projective S.X₂] :
    Function.Surjective (extClassComp (k := k) hS Y) := by
  have : Subsingleton (Ext.{w} S.X₂ Y 1) := subsingleton_of_projective _ _ 0
  intro x
  obtain ⟨y, hy⟩ :=
    contravariant_sequence_exact₃ hS Y x (by subsingleton) (n₀ := 0) (add_zero 1)
  exact ⟨linearEquiv₀ (R := k) y, by simpa [extClassComp] using hy⟩

include hS in
/-- **The first extension group of a projective presentation is finite dimensional.** If `M` has
a projective presentation `0 ⟶ K ⟶ P ⟶ M ⟶ 0` in a `k`-linear abelian category and the space of
maps `K ⟶ Y` is finite dimensional over `k`, then so is `Ext¹(M, Y)`. -/
theorem finite_extOne_of_shortExact_of_projective [Projective S.X₂]
    [Module.Finite k (S.X₁ ⟶ Y)] :
    Module.Finite k (Ext.{w} S.X₃ Y 1) :=
  Module.Finite.of_surjective _ (surjective_extClassComp (k := k) hS Y)

end CategoryTheory.Abelian.Ext

end
