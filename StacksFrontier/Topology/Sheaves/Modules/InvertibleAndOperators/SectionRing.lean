module

public import Mathlib.Algebra.DirectSum.Decomposition
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerCoherence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Graded sections of the twists of an invertible sheaf of modules

Let `𝒪` be a sheaf of commutative rings on a site `(C, J)` with a terminal object, and let `L`
be an invertible sheaf of `𝒪`-modules. The global sections of the nonnegative tensor powers
`L^{⊗ n}` assemble into a single additive group, the *section ring* of `L`, and the global
sections of all the twists `F ⊗ L^{⊗ n}` of a sheaf of modules `F` assemble into the *section
module* of `F`. Both are taken as direct sums over the degree, so a section of one twist is
literally a homogeneous element and the homogeneous components are the ranges of the
inclusions of the summands.

This file constructs those two graded objects, their homogeneous components, and the pairing
of two global sections through the sheaf tensor product.

## Main definitions

* `Stacks.SheafOfModules.sectionRing` is `⨁ n : ℕ, Γ(L^{⊗ n})`.
* `Stacks.SheafOfModules.sectionModule` is `⨁ n : ℤ, Γ(F ⊗ L^{⊗ n})`.
* `Stacks.SheafOfModules.tensorGlobalSection` is the global section of `F ⊗ G` determined by a
  global section of `F` and one of `G`.
* `Stacks.SheafOfModules.sectionRingGrading` and `Stacks.SheafOfModules.sectionModuleGrading`
  are the homogeneous components, as additive subgroups of the two direct sums.
* `Stacks.SheafOfModules.directSumComponentDecomposition` decomposes an arbitrary direct sum
  into the ranges of the inclusions of its summands.

## Main results

* `Stacks.SheafOfModules.tensorGlobalSection_add_left`,
  `Stacks.SheafOfModules.tensorGlobalSection_add_right`,
  `Stacks.SheafOfModules.tensorGlobalSection_zero_left` and
  `Stacks.SheafOfModules.tensorGlobalSection_zero_right`: the pairing of global sections is
  biadditive.
* `Stacks.SheafOfModules.sectionModuleDecomposition`: an element of the section module
  decomposes uniquely into its homogeneous components.

## Implementation notes

A section over the terminal object of the site is the general-site form of a global section;
for `C = Opens X` it is a section over all of `X`. The pairing `tensorGlobalSection` is the
sheafification unit applied to a tensor of sections of the underlying presheaves, so its
biadditivity is biadditivity of the presheaf tensor product followed by additivity of that
unit.

The grading is by the ranges of the summand inclusions rather than by a separately chosen
family of subgroups, so `directSumComponentDecomposition` applies verbatim and no
completeness or independence argument is needed.

The graded *ring* structure on `sectionRing` and the graded *module* structure on
`sectionModule` are not here. They are determined by the coherent multiplication
`L^{⊗ n} ⊗ L^{⊗ m} ≅ L^{⊗ (n + m)}` of Tag 01CU, and are built from it in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TwistSectionRing`, which imports this file.
Everything here is independent of that step: the two direct sums and their homogeneous
components are additive data only.

## References

* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite MonoidalCategory
open scoped DirectSum TensorProduct

universe v u w

namespace Stacks.SheafOfModules

attribute [local instance] monoidalCategoryPresheafOfModules

/-- A direct sum decomposes into the ranges of the inclusions of its summands: the component
map sends each summand into the corresponding range. -/
@[instance_reducible]
noncomputable def directSumComponentDecomposition
    {ι : Type*} [DecidableEq ι] (A : ι → Type*) [∀ i, AddCommGroup (A i)] :
    DirectSum.Decomposition (fun i => (DirectSum.of A i).range) := by
  let d : (⨁ i, A i) →+ ⨁ i, (DirectSum.of A i).range :=
    DirectSum.toAddMonoid fun i =>
      (DirectSum.of (fun i => (DirectSum.of A i).range) i).comp
        (DirectSum.of A i).rangeRestrict
  refine DirectSum.Decomposition.ofAddHom _ d ?_ ?_
  · apply DirectSum.addHom_ext
    intro i x
    simp [d]
  · apply DirectSum.addHom_ext
    intro i ⟨x, hx⟩
    obtain ⟨a, rfl⟩ := hx
    simp [d]
    rfl

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasTerminal C]
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

/-- The degree action of the `ℕ`-graded section ring on the `ℤ`-graded section module. -/
scoped instance sectionDegreeVAdd : VAdd ℕ ℤ where
  vadd n j := (n : ℤ) + j

/-- **Stacks Project, Tag 01CV.** The section ring of an invertible sheaf `L`: the direct sum of
the global sections of the nonnegative tensor powers of `L`. -/
@[stacks 01CV "underlying graded ring", ega "II 4.5.1" "partial"]
abbrev sectionRing (L : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] : Type _ :=
  (⨁ n : ℕ, (TensorPower.tensorPower O hO L (n : ℤ)).val.obj (op (⊤_ C)))

/-- **Stacks Project, Tag 01CV.** The section module of a sheaf of modules `F`: the direct sum of
the global sections of all the twists of `F` by integer tensor powers of an invertible sheaf
`L`. -/
@[stacks 01CV "underlying graded module"]
abbrev sectionModule (L F : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] : Type _ :=
  (⨁ n : ℤ, ((((Stacks.SheafOfModules.Tensor.sheafTensor
    ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj (F)).obj
      ((TensorPower.tensorPower O hO L n)))).val.obj (op (⊤_ C)))

/-- The global section of the sheaf tensor product determined by a global section of each
factor: tensor them as sections of the underlying presheaves, then apply the sheafification
unit.

This is the general-site form, where a global section is a section over the terminal object of
`C`. The ringed-space form, phrased with `PresheafOfModules.sections` and
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf`, is
`Stacks.SheafOfModules.tensorSections`; neither is an instance of the other, because the two
sheaf tensor products are different constructions. -/
noncomputable def tensorGlobalSection
    (F G : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    (s : F.val.obj (op (⊤_ C))) (t : G.val.obj (op (⊤_ C))) :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
        (F)).obj (G))).val.obj (op (⊤_ C)) :=
  (TensorSheafification.toSheafify O hO (F.val ⊗ G.val)).app (op (⊤_ C))
    (s ⊗ₜ[(O.obj (op (⊤_ C)))] t)

/-- The pairing of global sections is additive in its left argument. -/
theorem tensorGlobalSection_add_left
    (F G : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    (s₁ s₂ : F.val.obj (op (⊤_ C))) (t : G.val.obj (op (⊤_ C))) :
    tensorGlobalSection O hO F G (s₁ + s₂) t =
      tensorGlobalSection O hO F G s₁ t + tensorGlobalSection O hO F G s₂ t := by
  simp only [tensorGlobalSection, TensorProduct.add_tmul]
  exact map_add _ _ _

/-- The pairing of global sections is additive in its right argument. -/
theorem tensorGlobalSection_add_right
    (F G : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    (s : F.val.obj (op (⊤_ C))) (t₁ t₂ : G.val.obj (op (⊤_ C))) :
    tensorGlobalSection O hO F G s (t₁ + t₂) =
      tensorGlobalSection O hO F G s t₁ + tensorGlobalSection O hO F G s t₂ := by
  simp only [tensorGlobalSection, TensorProduct.tmul_add]
  exact map_add _ _ _

/-- Pairing with the zero section on the left gives the zero section. -/
theorem tensorGlobalSection_zero_left
    (F G : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    (t : G.val.obj (op (⊤_ C))) :
    tensorGlobalSection O hO F G 0 t = 0 := by
  simp only [tensorGlobalSection, TensorProduct.zero_tmul]
  exact map_zero _

/-- Pairing with the zero section on the right gives the zero section. -/
theorem tensorGlobalSection_zero_right
    (F G : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    (s : F.val.obj (op (⊤_ C))) :
    tensorGlobalSection O hO F G s 0 = 0 := by
  simp only [tensorGlobalSection, TensorProduct.tmul_zero]
  exact map_zero _

/-- The degree-`n` homogeneous component of the section ring: the global sections of the `n`th
tensor power, as an additive subgroup of the direct sum. -/
noncomputable def sectionRingGrading
    (L : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] (n : ℕ) : AddSubgroup (sectionRing O hO L) :=
  (DirectSum.of _ n).range

/-- The degree-`j` homogeneous component of the section module: the global sections of the
`j`th twist, as an additive subgroup of the direct sum. -/
@[ega "II 2.6.1" "more general"]
noncomputable def sectionModuleGrading
    (L F : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] (j : ℤ) :
    AddSubgroup (sectionModule O hO L F) :=
  (DirectSum.of _ j).range

/-- Every element of the section module decomposes uniquely into its homogeneous
components. -/
noncomputable instance sectionModuleDecomposition
    (L F : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] :
    DirectSum.Decomposition (sectionModuleGrading O hO L F) :=
  directSumComponentDecomposition _

end Stacks.SheafOfModules

end
