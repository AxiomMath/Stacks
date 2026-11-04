module

public import StacksFrontier.AlgebraicGeometry.CurveTensorEulerUnit.Devissage
public import StacksFrontier.AlgebraicGeometry.CohomologyFinitenessDevissage.Basic
public import StacksFrontier.AlgebraicGeometry.TensorEulerZeroDim.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# The Euler characteristic of `ℰ ⊗ ℱ` on a proper curve, with finiteness at two base cases

Let `X` be a proper curve over a field `k`, let `ℰ` be a finite locally free `𝒪_X`-module of rank
`n` and let `ℱ` be a coherent `𝒪_X`-module. The formula `χ(X, ℰ ⊗ ℱ) = r · deg(ℰ) + n · χ(X, ℱ)`,
with `r` the fibre rank of `ℱ` at the generic point, follows from the dévissage principle for
coherent modules on `X`, the formula `χ(X, ℰ ⊗ 𝒢) = n · χ(X, 𝒢)` for coherent `𝒢` with
zero-dimensional support, and finite dimensionality of the cohomology over `k` of

* the structure sheaf `𝒪_X`, and
* the coherent modules whose support is a proper closed subset.

At rank one the formula for zero-dimensional support holds unconditionally and is not assumed.

## Main results

* `exists_eulerCharacteristic_tensorSheaf_eq_fiberRank_mul_curveDegree_add_of_devissage`: the
  formula from the dévissage, the zero-dimensional case and the two finiteness base cases.
* `exists_eulerCharacteristic_tensorSheaf_eq_fiberRank_mul_curveDegree_add_of_devissage_one`: the
  formula at rank one from the dévissage and the two finiteness base cases.

## References

* [Stacks Project, Tag 0AYV](https://stacks.math.columbia.edu/tag/0AYV)
* [Stacks Project, Tag 0AYT](https://stacks.math.columbia.edu/tag/0AYT)
* [Stacks Project, Tag 01YH](https://stacks.math.columbia.edu/tag/01YH)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open _root_.AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- Let `ℰ` be finite locally free of rank `n` and `ℱ` coherent on a proper curve over a field.
Assume the dévissage principle `hdev` for coherent modules, finite dimensionality of the cohomology
over `k` of `𝒪_X` (`hunit`) and of every coherent module supported in a proper closed subset
(`hclosed`), and `χ(X, ℰ ⊗ 𝒢) = n · χ(X, 𝒢)` for every coherent `𝒢` with zero-dimensional support
(`h0AYT`). Then `χ(X, ℰ ⊗ ℱ) = r · deg(ℰ) + n · χ(X, ℱ)`, with `r` the fibre rank of `ℱ` at the
generic point. -/
theorem exists_eulerCharacteristic_tensorSheaf_eq_fiberRank_mul_curveDegree_add_of_devissage
    [IsCurve k f] [IsProper f] (E : X.Modules) (n : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E n]
    (hdev : ∀ P : X.Modules → Prop,
      (∀ T : ShortComplex X.Modules, T.ShortExact → SheafOfModules.IsCoherent T.X₁ →
        SheafOfModules.IsCoherent T.X₂ → SheafOfModules.IsCoherent T.X₃ →
        ((P T.X₁ ∧ P T.X₂ → P T.X₃) ∧ (P T.X₁ ∧ P T.X₃ → P T.X₂) ∧
          (P T.X₂ ∧ P T.X₃ → P T.X₁))) →
      (∀ (G : X.Modules) (Z : Set X), IsClosed Z → Z ≠ Set.univ →
        _root_.SheafOfModules.supp G ⊆ Z → P G) →
      P (SheafOfModules.unit X.ringCatSheaf) →
      ∀ G : X.Modules, SheafOfModules.IsCoherent G → P G)
    (hclosed : ∀ (G : X.Modules) (Z : Set X), IsClosed Z → Z ≠ Set.univ →
      _root_.SheafOfModules.supp G ⊆ Z → SheafOfModules.IsCoherent G →
        ∀ m, FiniteDimensional k (cohomologyOverField k f G m))
    (hunit : ∀ m,
      FiniteDimensional k (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) m))
    (h0AYT : ∀ (G : X.Modules) (hG : SheafOfModules.IsCoherent G),
      topologicalKrullDim (_root_.SheafOfModules.supp G) ≤ 0 →
      ∃ hT : ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj
            (G))).IsCoherent,
        @eulerCharacteristic k _ X f _
          ((((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (G)))
            hT =
          (n : ℤ) * @eulerCharacteristic k _ X f _ G hG)
    (F : X.Modules) [SheafOfModules.IsCoherent F] :
    ∃ h : ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj
          (F))).IsCoherent,
      @eulerCharacteristic k _ X f _
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (F)))
          h =
        (Scheme.Modules.fiberRank F (genericPoint X) : ℤ) *
            curveDegree k f (le_of_eq (IsCurve.topologicalKrullDim_eq_one (f := f))) E n +
          (n : ℤ) * eulerCharacteristic k f F :=
  exists_eulerCharacteristic_tensorSheaf_eq_fiberRank_mul_curveDegree_add k f E n
    (forall_finiteDimensional_cohomologyOverField_of_devissage k f hdev hclosed hunit)
    hdev h0AYT F

/-- Let `ℰ` be finite locally free of rank one and `ℱ` coherent on a proper curve over a field.
Assume the dévissage principle `hdev` for coherent modules and finite dimensionality of the
cohomology over `k` of `𝒪_X` (`hunit`) and of every coherent module supported in a proper closed
subset (`hclosed`). Then `χ(X, ℰ ⊗ ℱ) = r · deg(ℰ) + χ(X, ℱ)`, with `r` the fibre rank of `ℱ` at
the generic point. -/
theorem exists_eulerCharacteristic_tensorSheaf_eq_fiberRank_mul_curveDegree_add_of_devissage_one
    [IsCurve k f] [IsProper f] (E : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E 1]
    (hdev : ∀ P : X.Modules → Prop,
      (∀ T : ShortComplex X.Modules, T.ShortExact → SheafOfModules.IsCoherent T.X₁ →
        SheafOfModules.IsCoherent T.X₂ → SheafOfModules.IsCoherent T.X₃ →
        ((P T.X₁ ∧ P T.X₂ → P T.X₃) ∧ (P T.X₁ ∧ P T.X₃ → P T.X₂) ∧
          (P T.X₂ ∧ P T.X₃ → P T.X₁))) →
      (∀ (G : X.Modules) (Z : Set X), IsClosed Z → Z ≠ Set.univ →
        _root_.SheafOfModules.supp G ⊆ Z → P G) →
      P (SheafOfModules.unit X.ringCatSheaf) →
      ∀ G : X.Modules, SheafOfModules.IsCoherent G → P G)
    (hclosed : ∀ (G : X.Modules) (Z : Set X), IsClosed Z → Z ≠ Set.univ →
      _root_.SheafOfModules.supp G ⊆ Z → SheafOfModules.IsCoherent G →
        ∀ m, FiniteDimensional k (cohomologyOverField k f G m))
    (hunit : ∀ m,
      FiniteDimensional k (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) m))
    (F : X.Modules) [SheafOfModules.IsCoherent F] :
    ∃ h : ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj
          (F))).IsCoherent,
      @eulerCharacteristic k _ X f _
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (F)))
          h =
        (Scheme.Modules.fiberRank F (genericPoint X) : ℤ) *
            curveDegree k f (le_of_eq (IsCurve.topologicalKrullDim_eq_one (f := f))) E 1 +
          (1 : ℤ) * eulerCharacteristic k f F :=
  exists_eulerCharacteristic_tensorSheaf_eq_fiberRank_mul_curveDegree_add_of_devissage
    k f E 1 hdev hclosed hunit
    (fun G hG hdim =>
      have : SheafOfModules.IsCoherent G := hG
      exists_eulerCharacteristic_tensorSheaf_eq_mul_of_isFiniteLocallyFreeOfRank_one k f E G hdim)
    F

end AlgebraicGeometry

end
