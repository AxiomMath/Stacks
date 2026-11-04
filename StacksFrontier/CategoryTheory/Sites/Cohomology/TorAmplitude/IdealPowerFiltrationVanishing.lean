module

public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerModule
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.IdealFiltrationVanishing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The adic filtration as a filtration absorbing the product with the ideal

Let `(C, O)` be a ringed site, `I ⊆ O` a sheaf of ideals and `M` a sheaf of `O`-modules. The
submodules `Iᵏ M` form a decreasing filtration of `M` with `I · (Iᵏ M) ⊆ Iᵏ⁺¹ M` and with
`I⁰ M = M`, so they are an instance of the filtration
`Stacks.Sites.isZero_homologyTensorSingle_of_idealSmul_filtration_top_sections` runs its
dévissage along. This file performs that instantiation, leaving only the vanishing of the last
stage to be supplied.

## Main results

* `Stacks.Sites.isZero_homologyTensorSingle_of_isZero_idealPowSmul`: if the cohomology of
  `K ⊗^L_O G[0]` in the degree `i` vanishes for every sheaf of modules `G` whose sections are
  killed by the sections of `I`, and if `Iⁿ M` is zero, then the cohomology of `K ⊗^L_O M[0]` in
  the degree `i` vanishes.

## Implementation notes

All three structural hypotheses of the dévissage are discharged from the lattice theory of
`Stacks.Sites.idealPowSmul` already in place: `I⁰ M = M` is
`Stacks.Sites.idealPowSmul_zero`, the filtration decreases by
`Stacks.Sites.idealPowSmul_succ_le`, and `I · (Iᵏ M) ⊆ Iᵏ⁺¹ M` is the Artin–Rees inclusion
`Stacks.Sites.idealPowSmul_idealPowSmul_le` at the first exponent `1`, read through
`Stacks.Sites.idealPowSmul_one`. Only the vanishing of `Iⁿ M` is left as a hypothesis: it is the
one assertion about `M` rather than about the filtration, and in the application of Stacks 0942
part (2) — where `M` is a sheaf of `O/Iⁿ`-modules — it is where that hypothesis on `M` enters.

## References

* [Stacks Project, Tag 0942](https://stacks.math.columbia.edu/tag/0942)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v w d

namespace Stacks.Sites

variable {X : RingedSite.{u, v, w}}

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

variable [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasDerivedCategory.{d} (RingedSite.Modules.{u, v, w} X)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules.{u, v, w} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O) (ComplexShape.up ℤ)]
  (I : IdealSubsheaf.{v, u, w} X.O)
  (T : Stacks.SheafOfModules.DerivedTensorProduct.{u, v, w, d} X)
  (K : RingedSite.DerivedModules.{u, v, w, d} X)

omit [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasDerivedCategory.{d} (RingedSite.Modules.{u, v, w} X)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules.{u, v, w} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O) (ComplexShape.up ℤ)] in
/-- **The product with `I` carries each stage of the adic filtration into the next.**  This is
the Artin–Rees inclusion `Iᵏ · (Iⁿ · N) ⊆ Iᵏ⁺ⁿ · N` at `k = 1`. -/
theorem idealSmul_idealPowSmul_le_succ {M : RingedSite.Modules.{u, v, w} X}
    (N : M.Submodule) (n : ℕ) :
    idealSmul I (idealPowSmul.{w, v, u, w} I n N : M.Submodule) ≤
      (idealPowSmul.{w, v, u, w} I (n + 1) N : M.Submodule) := by
  simpa only [idealPowSmul_one, Nat.add_comm 1 n] using
    idealPowSmul_idealPowSmul_le.{w, v, u, w} I 1 n N

/-- **A module whose adic filtration reaches zero inherits a vanishing from the modules
annihilated by `I`.**  If the cohomology of `K ⊗^L_O G[0]` in the degree `i` vanishes for every
sheaf of modules `G` whose sections are killed by the sections of `I`, and if `Iⁿ M` is zero,
then so does that of `K ⊗^L_O M[0]`.

The submodules `Iᵏ M` are the filtration of
`Stacks.Sites.isZero_homologyTensorSingle_of_idealSmul_filtration_top_sections`: they start at
`M`, they decrease, and the product with `I` carries each into the next. -/
@[sga "1 IV 5.3" "more general"]
theorem isZero_homologyTensorSingle_of_isZero_idealPowSmul (i : ℤ) (n : ℕ)
    {M : RingedSite.Modules.{u, v, w} X}
    (hm : IsZero ((idealPowSmul.{w, v, u, w} I n (⊤ : M.Submodule)).toSheafOfModules))
    (hG : ∀ G : RingedSite.Modules.{u, v, w} X,
      (∀ (U : X.Cᵒᵖ) (a : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U),
        a ∈ I.obj U → ∀ g : G.val.obj U, a • g = 0) →
      IsZero (Stacks.SheafOfModules.DerivedTensorProduct.homologyTensorSingle T K i G)) :
    IsZero (Stacks.SheafOfModules.DerivedTensorProduct.homologyTensorSingle T K i M) :=
  isZero_homologyTensorSingle_of_idealSmul_filtration_top_sections I T K i n
    (N := fun k => idealPowSmul.{w, v, u, w} I k (⊤ : M.Submodule))
    (idealPowSmul_zero.{w, v, u, w} I ⊤)
    (fun k => idealPowSmul_succ_le.{w, v, u, w} I k ⊤)
    (fun k => idealSmul_idealPowSmul_le_succ I ⊤ k) hm hG

end Stacks.Sites

end
