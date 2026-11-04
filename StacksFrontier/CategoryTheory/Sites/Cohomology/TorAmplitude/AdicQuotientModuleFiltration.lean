module

public import StacksFrontier.CategoryTheory.Sites.Modules.AdicQuotientKernelIdeal
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.IdealPowerFiltrationVanishing
import StacksCore.Tactic.StacksAttribute

/-!
# The adic filtration of a sheaf of modules over an adic quotient reaches zero

Let `(C, O)` be a ringed site and `I ⊆ O` a sheaf of ideals. A sheaf of `O/Iⁿ`-modules, read as
a sheaf of `O`-modules along `O ⟶ O/Iⁿ`, is annihilated by `Iⁿ`, so the `n`-th stage `Iⁿ M` of
its adic filtration is the zero subsheaf. That is the one hypothesis
`Stacks.Sites.isZero_homologyTensorSingle_of_isZero_idealPowSmul` leaves open, and discharging
it turns that dévissage into an unconditional statement about a module over the quotient.

## Main results

* `Stacks.Sites.idealPowSmul_top_restrictScalars_adicQuotient_eq_bot`: `Iⁿ M = 0` for a sheaf
  `M` of `O/Iⁿ`-modules read over `O`.
* `Stacks.Sites.isZero_idealPowSmul_top_restrictScalars_adicQuotient`: the same, as the
  vanishing of the associated sheaf of modules, which is the shape the dévissage consumes.
* `Stacks.Sites.isZero_homologyTensorSingle_restrictScalars_adicQuotient`: **the dévissage of
  Stacks 0942 part (2) at a sheaf of `O/Iⁿ`-modules.** If the cohomology of `K ⊗^L_O G[0]` in
  the degree `i` vanishes for every sheaf of `O`-modules `G` whose sections are killed by the
  sections of `I`, then it vanishes at every sheaf of `O/Iⁿ`-modules read over `O`.

## Implementation notes

The product `Iⁿ · M` is the smallest subsheaf with local membership containing every product of
a section of `Iⁿ` with a section of `M`, so `Stacks.Sites.idealPowSmul_le` reduces its vanishing
to the sectionwise statement `Stacks.Sites.smul_eq_zero_of_mem_idealPow`, which is where the
identification of `Iⁿ` as the kernel ideal of `O ⟶ O/Iⁿ` enters. No local description of the
sections of `Iⁿ` is needed: the universal property is applied at the bottom subsheaf, and that
one has local membership.

`restrictScalarsAdicQuotient` is an abbreviation with its type written out rather than an
inlined `SheafOfModules.restrictScalars`: the module universe of restriction of scalars is not
determined by the morphism of ring sheaves, so inlining it leaves that universe open and the
derived instances over `(C, O)` fail to apply.

## References

* [Stacks Project, Tag 0942](https://stacks.math.columbia.edu/tag/0942)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u d

namespace Stacks.Sites

variable {X : RingedSite.{u, u, u}} [HasWeakSheafify X.J CommRingCat.{u}]

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

variable (I : IdealSubsheaf.{u, u, u} X.O) (n : ℕ)
  (M : _root_.SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u}
      (adicQuotient.{u, u, u} I n)))

/-- A sheaf of `O/Iⁿ`-modules read as a sheaf of `O`-modules along `O ⟶ O/Iⁿ`. -/
abbrev restrictScalarsAdicQuotient : RingedSite.Modules.{u, u, u} X :=
  (_root_.SheafOfModules.restrictScalars.{u} (adicQuotientRingHom.{u} I n)).obj M

/-- **The `n`-th stage of the adic filtration of a sheaf of `O/Iⁿ`-modules is zero.** Every
product of a section of `Iⁿ` with a section of the module vanishes, by
`Stacks.Sites.smul_eq_zero_of_mem_idealPow`, and `Iⁿ · M` is the smallest subsheaf with local
membership containing those products. -/
theorem idealPowSmul_top_restrictScalars_adicQuotient_eq_bot :
    idealPowSmul.{u, u, u, u} I n
      (⊤ : (restrictScalarsAdicQuotient I n M).Submodule) = ⊥ :=
  le_antisymm
    (idealPowSmul_le I n fun U a ha z _ => by
      rw [smul_eq_zero_of_mem_idealPow I n M U ha z]
      exact Submodule.zero_mem _)
    bot_le

/-- **The `n`-th stage of the adic filtration of a sheaf of `O/Iⁿ`-modules is a zero object**,
which is the form in which the dévissage of
`Stacks.Sites.isZero_homologyTensorSingle_of_isZero_idealPowSmul` consumes it. -/
theorem isZero_idealPowSmul_top_restrictScalars_adicQuotient :
    IsZero ((idealPowSmul.{u, u, u, u} I n
      (⊤ : (restrictScalarsAdicQuotient I n M).Submodule)).toSheafOfModules) :=
  _root_.SheafOfModules.Submodule.isZero_toSheafOfModules_of_eq_bot
    (idealPowSmul_top_restrictScalars_adicQuotient_eq_bot I n M)

section Derived

variable [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{d} (RingedSite.Modules.{u, u, u} X)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ N, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj N).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules.{u, u, u} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  (T : Stacks.SheafOfModules.DerivedTensorProduct.{u, u, u, d} X)
  (K : RingedSite.DerivedModules.{u, u, u, d} X)

/-- **The dévissage of Stacks 0942 part (2) at a sheaf of `O/Iⁿ`-modules.** If the cohomology of
`K ⊗^L_O G[0]` in the degree `i` vanishes for every sheaf of `O`-modules `G` whose sections are
killed by the sections of `I`, then it vanishes at every sheaf of `O/Iⁿ`-modules read over `O`.

The source's "`F` has a finite filtration whose successive quotients are sheaves of
`O/I`-modules": the filtration is by the powers `Iᵏ F`, and it reaches zero at the stage `n`
because `Iⁿ` is the kernel ideal of `O ⟶ O/Iⁿ`. -/
theorem isZero_homologyTensorSingle_restrictScalars_adicQuotient (i : ℤ)
    (hG : ∀ G : RingedSite.Modules.{u, u, u} X,
      (∀ (U : X.Cᵒᵖ) (a : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U),
        a ∈ I.obj U → ∀ g : G.val.obj U, a • g = 0) →
      IsZero (Stacks.SheafOfModules.DerivedTensorProduct.homologyTensorSingle T K i G)) :
    IsZero (Stacks.SheafOfModules.DerivedTensorProduct.homologyTensorSingle T K i
      (restrictScalarsAdicQuotient I n M)) :=
  isZero_homologyTensorSingle_of_isZero_idealPowSmul I T K i n
    (isZero_idealPowSmul_top_restrictScalars_adicQuotient I n M) hG

end Derived

end Stacks.Sites

end
