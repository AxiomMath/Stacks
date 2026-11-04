module

public import StacksFrontier.AlgebraicGeometry.Divisors.InvertibleSections.ModuleSystem
public import StacksCore.Tactic.StacksAttribute

/-!
# The graded ring and graded module of sections of an invertible sheaf

Let `𝒪` be a sheaf of commutative rings on a site, `L` an invertible sheaf of `𝒪`-modules and
`F` an arbitrary sheaf of `𝒪`-modules. The *`n`-th twist* of `F` is `F ⊗ L^{⊗ n}`, realised
here as the image of `F` under the `n`-th integer power of the right-tensor autoequivalence, so
that it is defined for every integer `n` and is `F` itself for `n = 0`. Tag 01CV then forms

  `Γ_*(X, L) = ⨁_{n ≥ 0} Γ(X, L^{⊗ n})` and `Γ_*(X, L, F) = ⨁_{n ∈ ℤ} Γ(X, F ⊗ L^{⊗ n})`,

the first a graded ring and the second a graded module over it. The multiplication of the ring
is the one built in `StacksFrontier/AlgebraicGeometry/GradedSectionRing/`; the action of the ring
on the module is built here, from the module system of the twists.

## Main definitions

* `Stacks.SheafOfModules.Invertible.twist`: the twist `F ⊗ L^{⊗ n}`, for `n` any integer.
* `Stacks.SheafOfModules.Invertible.twistLeftSuccIso`: the comparison
  `L ⊗ (F ⊗ L^{⊗ n}) ≅ F ⊗ L^{⊗ (n + 1)}`.
* `Stacks.SheafOfModules.Invertible.twistModuleSystem`: the twists of `F`, as a module system
  over the power system of the tensor powers of `L`.
* `Stacks.SheafOfModules.Invertible.sectionRing`: `Γ_*(X, L)`, the direct sum of the global
  sections of the non-negative tensor powers.
* `Stacks.SheafOfModules.Invertible.twistedSections`: `Γ_*(X, L, F)`, the direct sum of the
  global sections of all the twists.
* `Stacks.SheafOfModules.Invertible.twistedSectionsSMul`: the action of a global section of
  `L^{⊗ a}` on a global section of `F ⊗ L^{⊗ b}`.

## Main results

* `Stacks.SheafOfModules.Invertible.twistedSectionsGmodule` and
  `Stacks.SheafOfModules.Invertible.twistedSectionsModule`: **`Γ_*(X, L, F)` is a graded module
  over `Γ_*(X, L)`**, which is the second half of Tag 01CV. The graded ring itself is
  `Stacks.SheafOfModules.Invertible.homGradedRing`, the first half.
The homogeneous action of that structure is `twistedSectionsSMul` by construction, so
`DirectSum.Gmodule.of_smul_of` computes the action of a homogeneous section of `Γ_*(X, L)` on a
homogeneous section of `Γ_*(X, L, F)`.

## Implementation notes

**Why the twists, and not the tensor product sheaf.** `F ⊗ L^{⊗ n}` could be spelled as the
tensor product sheaf of Tag 05NA applied to `F` and `L^{⊗ n}`. It is spelled instead as
`(tensorPowerEquivalence 𝒪 h𝒪 L n).functor.obj F`, the `n`-th iterate of `· ⊗ L` applied to
`F`, because that is the spelling for which `Stacks.SheafOfModules.Invertible.powSuccIso`
already provides the successor comparison, for an arbitrary object and for every integer
exponent. For `F` the structure sheaf it is `Stacks.SheafOfModules.Invertible.tensorPower` on
the nose, so the module `Γ_*(X, L, 𝒪_X)` has the ring `Γ_*(X, L)` in its non-negative part.

**The action is a left action from the start.** The comparison used to build it is
`twistLeftSuccIso`, with the extra tensor factor of `L` on the *left*, obtained from the
successor comparison by the braiding. Building the action from the right-hand comparison
instead would produce a right action, and a left module structure could then only be recovered
from commutativity of `Γ_*(X, L)` — the commutativity constraint of Tag 01CU. That constraint
*is* proved for an invertible `L`, unconditionally:
`Stacks.SheafOfModules.Invertible.tensorPowerMulIso_comm`, with
`Stacks.SheafOfModules.Invertible.homGradedCommRingOfInvertible` the resulting commutative
graded ring, in `StacksFrontier/AlgebraicGeometry/GradedSectionRing/Commutativity.lean` — but that
module is not in this one's import closure (only `GradedSectionRing/Ring.lean` is), so using it
would need a new import. The braiding, by contrast, is unconditional and needs none. An earlier
version of this
paragraph said the constraint is not available in this development; that is false.

**The grading is by morphisms out of the tensor unit.** As in
`StacksFrontier/AlgebraicGeometry/GradedSectionRing/Ring.lean`, a summand is
`𝟙_ ⟶ F ⊗ L^{⊗ n}` rather than `(F ⊗ L^{⊗ n}).sections`: the graded-module interface needs an
`AddCommGroup` on every summand, a morphism group of a preadditive category has one for free,
and `SheafOfModules.unitHomEquiv` identifies the two.

## References

* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public section

open CategoryTheory MonoidalCategory
open scoped DirectSum
open AlgebraicGeometry.SheafOfModules (IsInvertible)

universe v u w

namespace Stacks.SheafOfModules.Invertible

attribute [local instance] Stacks.SheafOfModules.monoidalCategory
  Stacks.SheafOfModules.monoidalPreadditive Stacks.SheafOfModules.braidedCategory

open scoped Stacks.Monoidal

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]
  (L : _root_.SheafOfModules.{w}
    (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) [IsInvertible O hO L]

/-- The `n`-th twist `F ⊗ L^{⊗ n}` of a sheaf of modules by an invertible sheaf of modules, for
`n` an arbitrary integer: the image of `F` under the `n`-th power of the right-tensor
autoequivalence. -/
@[implicit_reducible]
noncomputable def twist
    (F : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) (n : ℤ) :
    _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) :=
  (tensorPowerEquivalence O hO L n).functor.obj F

/-- The zeroth twist is the sheaf itself. -/
@[simp]
theorem twist_zero (F : _root_.SheafOfModules.{w}
    (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    twist O hO L F 0 = F := rfl

/-- The twists of the structure sheaf are the tensor powers of `L`. -/
theorem twist_unit (n : ℤ) :
    twist O hO L
        (_root_.SheafOfModules.unit
          (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) n
      = tensorPower O hO L n := rfl

/-- One more tensor factor of `L` on the right of a twist: `(F ⊗ L^{⊗ n}) ⊗ L ≅
F ⊗ L^{⊗ (n + 1)}`, written with the tensor product sheaf of Tag 05NA. In negative degree the
step is the counit of the right-tensor autoequivalence. -/
noncomputable def twistSuccIso
    (F : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) (n : ℤ) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
        ((twist O hO L F n))).obj (L))
      ≅ twist O hO L F (n + 1) :=
  powSuccIso ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
    ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
      L).asEquivalence n F

/-- One more tensor factor of `L` on the *left* of a twist:
`L ⊗ (F ⊗ L^{⊗ n}) ≅ F ⊗ L^{⊗ (n + 1)}`. This is `twistSuccIso` read through the braiding of
the tensor product of sheaves of modules and the identification of the monoidal tensor product
with the tensor product sheaf of Tag 05NA. -/
noncomputable def twistLeftSuccIso
    (F : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) (n : ℤ) :
    L ⊗ twist O hO L F n ≅ twist O hO L F (n + 1) :=
  β_ L (twist O hO L F n) ≪≫ Stacks.SheafOfModules.tensorObjIso O hO _ _
    ≪≫ twistSuccIso O hO L F n

/-- The twists of a sheaf of modules, as a module system over the power system
`Stacks.SheafOfModules.Invertible.tensorPowerSystem` of the tensor powers of `L`. -/
@[implicit_reducible]
noncomputable def twistModuleSystem
    (F : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    Stacks.Monoidal.ModuleSystem (tensorPowerSystem O hO L) where
  obj n := twist O hO L F n
  succIso n := twistLeftSuccIso O hO L F n

/-- **Stacks Project, Tag 01CV.** The *associated graded ring* `Γ_*(X, L)` of an invertible
sheaf of modules: the direct sum of the global sections of its non-negative tensor powers. Its
graded ring structure is `Stacks.SheafOfModules.Invertible.homGradedRing`. -/
@[stacks 01CV "underlying graded ring",
  ega "II 4.5.1" "S = ⊕Γ(X,L^⊗n)",
  ega "III 2.1.1" "(2.1.1.1)", ega "II 2.6.1" "Γ_•(O_X) definition", ega "0 5.4.6" "Γ•(L) carrier"]
abbrev sectionRing :=
  ⨁ n : ℕ, (𝟙_ (_root_.SheafOfModules.{w}
    (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
      ⟶ tensorPower O hO L (n : ℤ))

/-- **Stacks Project, Tag 01CV.** The graded module `Γ_*(X, L, F)` of a sheaf of modules `F`:
the direct sum, over all integers `n`, of the global sections of the twists `F ⊗ L^{⊗ n}`. Its
module structure over `Γ_*(X, L)` is
`Stacks.SheafOfModules.Invertible.twistedSectionsModule`. -/
@[stacks 01CV "underlying graded module",
  ega "0 5.4.6" "partial",
  ega "II 2.6.1",
  ega "III 2.1.2" "partial"]
abbrev twistedSections
    (F : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :=
  ⨁ n : ℤ, (𝟙_ (_root_.SheafOfModules.{w}
    (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
      ⟶ twist O hO L F n)

/-- The action of a global section of `L^{⊗ a}` on a global section of `F ⊗ L^{⊗ b}`, as a
global section of `F ⊗ L^{⊗ (a + b)}`: tensor the two sections and contract by the action
isomorphism of the module system of twists. -/
noncomputable def twistedSectionsSMul
    (F : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) {a : ℕ} {b : ℤ}
    (s : 𝟙_ (_root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
        ⟶ tensorPower O hO L (a : ℤ))
    (t : 𝟙_ (_root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) ⟶ twist O hO L F b) :
    𝟙_ (_root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
        ⟶ twist O hO L F (a +ᵥ b) :=
  (twistModuleSystem O hO L F).sectionSMul s t

/-- **Stacks Project, Tag 01CV.** `Γ_*(X, L, F)` is a `ℤ`-graded module over the `ℕ`-graded
ring `Γ_*(X, L)`, with the action `twistedSectionsSMul` on homogeneous sections. No
commutativity of `Γ_*(X, L)` is used. -/
@[stacks 01CV "graded module action", instance_reducible]
noncomputable def twistedSectionsGmodule
    (F : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    letI : GradedMonoid.GMonoid (fun n : ℕ =>
        𝟙_ (_root_.SheafOfModules.{w}
          (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
            ⟶ tensorPower O hO L (n : ℤ)) := (tensorPowerSystem O hO L).gradedMonoid
    DirectSum.Gmodule
      (fun n : ℕ => 𝟙_ (_root_.SheafOfModules.{w}
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
          ⟶ tensorPower O hO L (n : ℤ))
      (fun n : ℤ => 𝟙_ (_root_.SheafOfModules.{w}
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
          ⟶ twist O hO L F n) :=
  (twistModuleSystem O hO L F).gmodule

/-- `Γ_*(X, L, F)` is a module over `Γ_*(X, L)`: the graded module structure
`Stacks.SheafOfModules.Invertible.twistedSectionsGmodule` read on the direct sums. -/
@[instance_reducible]
noncomputable def twistedSectionsModule
    (F : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    letI : DirectSum.GRing (fun n : ℕ =>
        𝟙_ (_root_.SheafOfModules.{w}
          (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
            ⟶ tensorPower O hO L (n : ℤ)) := homGradedRing O hO L
    Module (sectionRing O hO L) (twistedSections O hO L F) :=
  (twistModuleSystem O hO L F).module

end Stacks.SheafOfModules.Invertible

-- Tag 01CV: the multiplication of the graded ring `Γ_*(X, L)`, which is the graded ring
-- structure already built on the global sections of the tensor powers.
add_to_stacks 01CV "graded ring multiplication" Stacks.SheafOfModules.Invertible.homGradedRing
