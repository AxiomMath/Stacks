module

public import StacksFrontier.Deformation.ToposThickening.CoefficientExtUnit
public import StacksFrontier.Deformation.ToposThickening.DerivedLiftShift

/-!
# The groups `Ext¹(K₀, K₀)` and `Ext⁰(K₀, K₀)` at `V = k` do not change under the shift

For a coefficient map `θ : \underline{k} ⟶ O₀`, the obstruction group
`Hom(K₀, (K₀ ⊗^L (O₀ ⊗_k k))⟦1⟧)` and the group `Hom(K₀, K₀ ⊗^L (O₀ ⊗_k k))` at `V = k` are
finite dimensional for `K₀⟦m⟧` as soon as they are for `K₀`
(`Deformation.ComplexLift.finiteDimensional_coefficientExt_unit_shift`,
`Deformation.ComplexLift.finiteDimensional_coefficientHom_unit_shift`): both are `k`-linearly
`Hom(K₀, K₀⟦n⟧)` for the structure of multiplication by `θ(c)`
(`Deformation.ComplexLift.coefficientExtUnitLinearEquiv`), and the shift is a `k`-linear
equivalence. In the proof of Stacks 0DLL this moves the finiteness of Stacks 0D0T from the
complex `E₀` of a field point to its normalization `E₀⟦m⟧ ∈ D^{≤ 0}`.

Nothing here is registered.

## References

* [Stacks Project, Tag 0DLL](https://stacks.math.columbia.edu/tag/0DLL)
* [Stacks Project, Tag 0D0T](https://stacks.math.columbia.edu/tag/0D0T)
-/

@[expose] public noncomputable section

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

open CategoryTheory

universe d₀ u

namespace Deformation.ComplexLift

variable {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {k : Type u} [Field k] {O₀ : Sheaf J CommRingCat.{u}}
  [HasDerivedCategory.{d₀} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))]
  (θ : Stacks.TensorByBaseModule.constantRingPresheaf (C := C) k ⟶ O₀.obj)
  (K₀ : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)))

/-- **The obstruction group at `V = k` of `K₀⟦m⟧` is finite dimensional when that of `K₀` is.** -/
theorem finiteDimensional_coefficientExt_unit_shift (m : ℤ)
    [FiniteDimensional k ((coefficientExtLinearFunctor.{d₀} θ K₀).obj (FGModuleCat.of k k))] :
    FiniteDimensional k
      ((coefficientExtLinearFunctor.{d₀} θ (K₀⟦m⟧)).obj (FGModuleCat.of k k)) := by
  let : Linear k (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)) :=
    Stacks.TensorByBaseModule.linearOfHom k J O₀ θ
  have hθ := isCoefficientScalar_linearOfHom θ
  have : FiniteDimensional k (K₀ ⟶ K₀⟦(1 : ℤ)⟧) :=
    (coefficientExtUnitLinearEquiv K₀ hθ).symm.finiteDimensional
  have := finiteDimensional_shift_hom_shift k K₀ m 1
  exact (coefficientExtUnitLinearEquiv (K₀⟦m⟧) hθ).finiteDimensional

/-- **The group `Hom(K₀, K₀ ⊗^L (O₀ ⊗_k k))` of `K₀⟦m⟧` is finite dimensional when that of `K₀`
is.** -/
theorem finiteDimensional_coefficientHom_unit_shift (m : ℤ)
    [FiniteDimensional k ((coefficientHomLinearFunctor.{d₀} θ K₀).obj (FGModuleCat.of k k))] :
    FiniteDimensional k
      ((coefficientHomLinearFunctor.{d₀} θ (K₀⟦m⟧)).obj (FGModuleCat.of k k)) := by
  let : Linear k (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)) :=
    Stacks.TensorByBaseModule.linearOfHom k J O₀ θ
  have hθ := isCoefficientScalar_linearOfHom θ
  have : FiniteDimensional k (K₀ ⟶ K₀) :=
    (coefficientHomUnitLinearEquiv K₀ hθ).symm.finiteDimensional
  have := finiteDimensional_shift_hom_self k K₀ m
  exact (coefficientHomUnitLinearEquiv (K₀⟦m⟧) hθ).finiteDimensional

end Deformation.ComplexLift

end
