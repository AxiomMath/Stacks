module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.Basic
public import StacksFrontier.AlgebraicGeometry.TensorCoherence.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorStalkRingedSpace
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorUnitSections
public import StacksCore.Tactic.StacksAttribute

/-!
# Tensoring with the structure sheaf, and the Euler characteristic of a tensor product

Tag 0AYV computes the Euler characteristic of `ℰ ⊗ ℱ` on a proper curve over a field, for `ℰ`
finite locally free of rank `n` and `ℱ` coherent, as `r · deg(ℰ) + n · χ(X, ℱ)` where `r` is the
rank of `ℱ` at the generic point. Its proof runs the dévissage of Tag 01YH over the property
"the formula holds for `ℱ`", and the dévissage has two base cases: the structure sheaf, where the
formula is the *definition* of the degree, and a sheaf supported at a closed point, where it is
Tag 0AYT (5).

This file proves the first of those two base cases, unconditionally: the formula for
`ℱ = 𝒪_X`, where the rank at the generic point is `1`. The isomorphism
`ℰ ⊗_{𝒪_X} 𝒪_X ≅ ℰ` on an arbitrary ringed space that the computation rests on is
`AlgebraicGeometry.SheafOfModules.tensorSheafUnitRightIso`, imported from
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorUnitSections`, where it is accompanied by
its description on local sections.

## Main results

* `AlgebraicGeometry.eulerCharacteristic_tensor_unit`: `χ(X, ℰ ⊗ 𝒪_X) = χ(X, ℰ)`.
* `AlgebraicGeometry.eulerCharacteristic_tensor_unit_eq_curveDegree_add`: the formula of Tag
  0AYV at `ℱ = 𝒪_X`, namely `χ(X, ℰ ⊗ 𝒪_X) = 1 · deg(ℰ) + n · χ(X, 𝒪_X)`.
* `AlgebraicGeometry.exists_eulerCharacteristic_tensor_unit_eq_curveDegree_add`: the same, in
  the existential shape that also supplies coherence of the tensor product.

## Implementation notes

**Coherence is carried as instance arguments rather than derived.** On a proper curve both
coherence hypotheses follow from Tag 01XZ, through
`AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian`, but that is a theorem in the
structure morphism rather than an instance, so a statement whose *type* mentions
`AlgebraicGeometry.eulerCharacteristic` of the structure sheaf cannot discharge it. The
hypotheses here are exactly those of `AlgebraicGeometry.curveDegree_eq_eulerCharacteristic_sub`,
which this file consumes.

**What is not proved here.** Tag 0AYV itself is not proved and no attribute for it is attached.
What it still owes beyond this base case is the dévissage of Tag 01YH, the second base case
(Tag 0AYT (5)), and unconditional additivity of `χ` (Tag 08AA, which is reduced to Tag 02O6
alone by `AlgebraicGeometry.eulerCharacteristic_add_of_shortExact_of_finiteDimensional`). Those
three are exactly the hypotheses of
`AlgebraicGeometry.exists_eulerCharacteristic_tensorSheaf_eq_fiberRank_mul_curveDegree_add` in
`StacksFrontier/AlgebraicGeometry/CurveTensorEulerUnit/Devissage.lean`, which assembles the tag's
conclusion from them. Two further inputs are **available**: the generic
rank of a coherent sheaf is `AlgebraicGeometry.Scheme.Modules.fiberRank`, and flatness of a
finite locally free sheaf — the exactness half of Tag 05P2 (4) ⟹ (1) — is
`AlgebraicGeometry.Scheme.Modules.isFlat_of_isFiniteLocallyFree`, both in
`StacksFrontier/AlgebraicGeometry/FiberRank/Basic.lean`.

## References

* [Stacks Project, Tag 0AYV](https://stacks.math.columbia.edu/tag/0AYV)
* [Stacks Project, Tag 0AYR](https://stacks.math.columbia.edu/tag/0AYR)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **Tensoring with the structure sheaf does not change the Euler characteristic.** -/
theorem eulerCharacteristic_tensor_unit [IsProper f] (E : X.Modules)
    [hE : SheafOfModules.IsCoherent E]
    [hO : SheafOfModules.IsCoherent (SheafOfModules.unit X.ringCatSheaf)] :
    @eulerCharacteristic k _ X f _
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj
            ((SheafOfModules.unit X.ringCatSheaf))))
        (@AlgebraicGeometry.SheafOfModules.tensorSheaf_isCoherent X.toRingedSpace E _ hE hO) =
      eulerCharacteristic k f E :=
  @eulerCharacteristic_eq_of_iso k _ X f _ _ _
    (@AlgebraicGeometry.SheafOfModules.tensorSheaf_isCoherent X.toRingedSpace E _ hE hO) hE
    (SheafOfModules.tensorSheafUnitRightIso X.toRingedSpace E)

/-- **The formula of Tag 0AYV at `ℱ = 𝒪_X`**: the rank of the structure sheaf at the generic
point is `1`, and the formula is then the definition of the degree. This is the first base case
of the dévissage by which Tag 0AYV is proved. -/
theorem eulerCharacteristic_tensor_unit_eq_curveDegree_add [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (E : X.Modules) (n : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E n]
    [hE : SheafOfModules.IsCoherent E]
    [hO : SheafOfModules.IsCoherent (SheafOfModules.unit X.ringCatSheaf)] :
    @eulerCharacteristic k _ X f _
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj
            ((SheafOfModules.unit X.ringCatSheaf))))
        (@AlgebraicGeometry.SheafOfModules.tensorSheaf_isCoherent X.toRingedSpace E _ hE hO) =
      1 * curveDegree k f hdim E n +
        (n : ℤ) * eulerCharacteristic k f (SheafOfModules.unit X.ringCatSheaf) := by
  rw [eulerCharacteristic_tensor_unit k f E, curveDegree_eq_eulerCharacteristic_sub k f hdim E n]
  ring

/-- The formula of Tag 0AYV at `ℱ = 𝒪_X`, in the existential shape of that tag, which also
supplies coherence of the tensor product. -/
theorem exists_eulerCharacteristic_tensor_unit_eq_curveDegree_add [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (E : X.Modules) (n : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E n]
    [SheafOfModules.IsCoherent E]
    [SheafOfModules.IsCoherent (SheafOfModules.unit X.ringCatSheaf)] :
    ∃ h : ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj
        ((SheafOfModules.unit X.ringCatSheaf)))).IsCoherent,
      @eulerCharacteristic k _ X f _
          ((((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj
              ((SheafOfModules.unit X.ringCatSheaf)))) h =
        1 * curveDegree k f hdim E n +
          (n : ℤ) * eulerCharacteristic k f (SheafOfModules.unit X.ringCatSheaf) :=
  ⟨_, eulerCharacteristic_tensor_unit_eq_curveDegree_add k f hdim E n⟩

end AlgebraicGeometry

end
