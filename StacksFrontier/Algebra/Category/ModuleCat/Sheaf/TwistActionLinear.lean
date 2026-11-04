module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalSectionSmul
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TwistActionMorphism
import all StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TwistSectionRing

/-!
# Multiplication by a global section of a tensor power is linear in that section

`Stacks.SheafOfModules.TwistAction.actionOf` multiplies the twist `F ⊗ L^{⊗ j}` by a global
section `s` of `L^{⊗ n}`.  It is already known to be additive in `s`
(`Stacks.SheafOfModules.TwistAction.actionOf_add`).  This file adds the missing homogeneity:
rescaling `s` by a global section `r` of the structure sheaf rescales the morphism, in the sense
that multiplying by `r • s` is multiplying by `r` and then by `s`.  Together with additivity this
makes `s ↦ actionOf … s` a map of modules over the ring of global sections of the structure
sheaf, which is what a codimension count in the space of sections needs.

The scalar `r` acts on a sheaf of modules through
`Stacks.SheafOfModules.terminalSectionToEnd`, multiplication by a section over the terminal
object; `Stacks.TwistActionLinear.sectionSmul` is that endomorphism at a fixed module, and the
four ring laws and the naturality it satisfies are recorded here as well.

One further commutation law is proved: multiplying by two sections of tensor powers in either
order agrees, up to the reindexing comparisons that bring the two orders of the degrees to a
common total degree.

## Main results

* `Stacks.TwistActionLinear.actionOf_smul`: **multiplication by `r • s` is multiplication by `r`
  followed by multiplication by `s`.**
* `Stacks.TwistActionLinear.actionOf_comm`: **multiplication by two sections of tensor powers
  commutes**, up to reindexing.
* `Stacks.TwistActionLinear.sectionSmul` with `sectionSmul_one`, `sectionSmul_mul`,
  `sectionSmul_add`, `sectionSmul_zero` and `comp_sectionSmul`.

## Implementation notes

The proof of `actionOf_smul` is the proof of
`Stacks.SheafOfModules.TwistAction.actionOf_add` with the additivity of the three layers
replaced by their homogeneity.  Morphisms of sheaves of modules are compared on sections of the
form `tensorSectionsAt … x y` by `Stacks.SheafOfModules.tensorSheaf_hom_ext`, which is private to
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TwistSectionRing` and reached by `import all`, as
in `TwistActionMorphism.lean` itself.  On such a section the value of `actionOf … a` is
`tensorSectionsAt … x (tensorPowerMulSectionAt … (a|_U) y)` (`twistActionHom_pure` together with
`globalSectionHom_app`), so the scalar has to be moved out of three maps in turn: the restriction
`a ↦ a|_U` (`PresheafOfModules.map_smul`), the product of sections of tensor powers
(`tensorPowerMulSectionAt_smul_left` below) and the pairing of sections
(`tensorSectionsAt_smul_right` below).  The last two are proved from `TensorProduct.smul_tmul'`
and the linearity of the sheafification unit and of the coherence comparison.

The declarations sit in `Stacks.TwistActionLinear` rather than in
`Stacks.SheafOfModules.TwistAction`, and the scalars are spelled `O.obj U` rather than
`(TensorSheafification.structureSheaf O hO).obj.obj U`: that pair of choices is what lets
instance search find `Module ↑(O.obj U) ↑(F.val.obj U)` on a section of a sheaf of modules over
the sheafified structure sheaf.  Inside `Stacks.SheafOfModules.TwistAction`, or with the scalars
written at the structure-sheaf spelling, it does not.

`sectionSmul_mul` needs the rings of sections to be commutative, which they are: the structure
sheaf of the site is the sheafification of a `CommRingCat`-valued presheaf.  The
`IsMulCommutative` instance that `Stacks.SheafOfModules.terminalSectionToEnd` requires is
supplied below for that reason.

## References

* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

universe v u w

namespace Stacks.TwistActionLinear

open Stacks.SheafOfModules Stacks.SheafOfModules.TwistAction

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
attribute [local implicit_reducible] TensorSheafification.structureSheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasTerminal C]
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

/-- The rings of sections of the structure sheaf are commutative. -/
instance structureSheafIsMulCommutative (U : Cᵒᵖ) :
    IsMulCommutative ((TensorSheafification.structureSheaf O hO).obj.obj U) :=
  inferInstanceAs (IsMulCommutative ↥(O.obj U))

section
omit [HasTerminal C]

/-- A linear map sends `r • x` to `r • f x`, in the form `congrArg f` leaves behind. -/
private theorem linearMap_congr_smul {R M N : Type*} [Semiring R] [AddCommMonoid M]
    [AddCommMonoid N] [Module R M] [Module R N] (f : M →ₗ[R] N) (r : R) (x : M) {y : M}
    (h : y = r • x) : f y = r • f x :=
  h ▸ f.map_smul r x

/-- The pairing of sections over an object is linear in its right argument. -/
theorem tensorSectionsAt_smul_right (U : Cᵒᵖ)
    (F G : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    (r : O.obj U) (s : F.val.obj U)
    (t : G.val.obj U) :
    tensorSectionsAt O hO U F G s (r • t) =
      (show (Stacks.SheafOfModules.Tensor.ringSheaf ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O)
        (forget₂ CommRingCat RingCat) (hO)⟩).obj.obj U from r) •
        tensorSectionsAt O hO U F G s t := by
  unfold tensorSectionsAt
  refine linearMap_congr_smul ((TensorSheafification.toSheafify O hO (F.val ⊗ G.val)).app U).hom
    r _ ?_
  exact (TensorProduct.smul_tmul r s t).symm.trans (TensorProduct.smul_tmul' r s t)

/-- The product of sections of tensor powers is linear in its left argument. -/
theorem tensorPowerMulSectionAt_smul_left (U : Cᵒᵖ)
    (L : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] (n m : ℤ)
    (r : O.obj U)
    (s : (TensorPower.tensorPower O hO L n).val.obj U)
    (t : (TensorPower.tensorPower O hO L m).val.obj U) :
    tensorPowerMulSectionAt O hO U L n m (r • s) t =
      r • tensorPowerMulSectionAt O hO U L n m s t := by
  unfold tensorPowerMulSectionAt tensorSectionsAt
  exact linearMap_congr_smul ((TensorPower.coherentMulIso O hO L n m).hom.val.app U).hom r _
    (linearMap_congr_smul ((TensorSheafification.toSheafify O hO
      ((TensorPower.tensorPower O hO L n).val ⊗ (TensorPower.tensorPower O hO L m).val)).app U).hom
      r _ (TensorProduct.smul_tmul' r s t))

end

/-- Multiplication by a global section of the structure sheaf. -/
def sectionSmul (r : O.obj (op (⊤_ C)))
    (M : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO)) : M ⟶ M :=
  (terminalSectionToEnd (TensorSheafification.structureSheaf O hO) (⊤_ C) terminalIsTerminal
    r).app M

omit [J.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify J AddCommGrpCat] in
/-- On sections over `U`, multiplication by a global section is multiplication by its
restriction. -/
theorem sectionSmul_app (r : O.obj (op (⊤_ C)))
    (M : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO)) (U : Cᵒᵖ)
    (x : M.val.obj U) :
    (sectionSmul O hO r M).val.app U x = O.map (terminal.from U.unop).op r • x := rfl

/-- **Multiplication by a global section of the structure sheaf is linear in the section.** -/
theorem actionOf_smul
    (L F : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] (n j : ℤ) (r : O.obj (op (⊤_ C)))
    (s : (TensorPower.tensorPower O hO L n).val.obj (op (⊤_ C))) :
    actionOf O hO L F n j (r • s) =
      sectionSmul O hO r
          ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O,
            Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
              (F)).obj ((TensorPower.tensorPower O hO L j)))) ≫
        actionOf O hO L F n j s := by
  apply tensorSheaf_hom_ext O hO
  intro U x y
  have e : ∀ a : (TensorPower.tensorPower O hO L n).val.obj (op (⊤_ C)),
      (actionOf O hO L F n j a).val.app U
          (tensorSectionsAt O hO U F (TensorPower.tensorPower O hO L j) x y) =
        tensorSectionsAt O hO U F (TensorPower.tensorPower O hO L (n + j)) x
          (tensorPowerMulSectionAt O hO U L n j
            ((TensorPower.tensorPower O hO L n).val.map (terminal.from U.unop).op a) y) := by
    intro a
    show (twistActionHom O hO L F n j (globalSectionHom O hO _ a)).val.app U _ = _
    rw [twistActionHom_pure, globalSectionHom_app]
  let r' : (Stacks.SheafOfModules.Tensor.ringSheaf ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O)
      (forget₂ CommRingCat RingCat) (hO)⟩).obj.obj U := O.map (terminal.from U.unop).op r
  have hRHS : (sectionSmul O hO r
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O,
          Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
            (F)).obj ((TensorPower.tensorPower O hO L j)))) ≫
          actionOf O hO L F n j s).val.app U
        (tensorSectionsAt O hO U F (TensorPower.tensorPower O hO L j) x y) =
      r' • tensorSectionsAt O hO U F (TensorPower.tensorPower O hO L (n + j)) x
          (tensorPowerMulSectionAt O hO U L n j
            ((TensorPower.tensorPower O hO L n).val.map (terminal.from U.unop).op s) y) :=
    (LinearMap.map_smul ((actionOf O hO L F n j s).val.app U).hom
      (O.map (terminal.from U.unop).op r) _).trans
      (congrArg (fun z => r' • z) (e s))
  have hmap : (((TensorPower.tensorPower O hO L n).val.map (terminal.from U.unop).op) (r • s)
        : (TensorPower.tensorPower O hO L n).val.obj U) =
      (O.map (terminal.from U.unop).op r : O.obj U) •
        (((TensorPower.tensorPower O hO L n).val.map (terminal.from U.unop).op) s
          : (TensorPower.tensorPower O hO L n).val.obj U) :=
    PresheafOfModules.map_smul (TensorPower.tensorPower O hO L n).val
      (terminal.from U.unop).op r s
  have hLHS : (actionOf O hO L F n j (r • s)).val.app U
        (tensorSectionsAt O hO U F (TensorPower.tensorPower O hO L j) x y) =
      r' • tensorSectionsAt O hO U F (TensorPower.tensorPower O hO L (n + j)) x
          (tensorPowerMulSectionAt O hO U L n j
            ((TensorPower.tensorPower O hO L n).val.map (terminal.from U.unop).op s) y) := by
    refine Eq.trans (e (r • s)) ?_
    refine Eq.trans (congrArg (fun z : (TensorPower.tensorPower O hO L n).val.obj U =>
      tensorSectionsAt O hO U F (TensorPower.tensorPower O hO L (n + j)) x
        (tensorPowerMulSectionAt O hO U L n j z y)) hmap) ?_
    exact Eq.trans
      (congrArg (tensorSectionsAt O hO U F (TensorPower.tensorPower O hO L (n + j)) x)
        (tensorPowerMulSectionAt_smul_left O hO U L n j (O.map (terminal.from U.unop).op r) _ y))
      (tensorSectionsAt_smul_right O hO U F (TensorPower.tensorPower O hO L (n + j))
        (O.map (terminal.from U.unop).op r) x _)
  exact hLHS.trans hRHS.symm

/-- **Multiplication by two global sections of tensor powers commutes**, up to the reindexing
comparisons that bring the two orders of the degrees to a common total degree. -/
theorem actionOf_comm
    (L F : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] (n m j : ℤ)
    (s : (TensorPower.tensorPower O hO L n).val.obj (op (⊤_ C)))
    (t : (TensorPower.tensorPower O hO L m).val.obj (op (⊤_ C)))
    (h₁ : n + (m + j) = m + n + j) (h₂ : m + (n + j) = m + n + j) :
    actionOf O hO L F m j t ≫ actionOf O hO L F n (m + j) s ≫
        (Invertible.tensorProductIso O hO (Iso.refl F)
          (TensorPower.tensorPowerReindex O hO L h₁)).hom =
      actionOf O hO L F n j s ≫ actionOf O hO L F m (n + j) t ≫
        (Invertible.tensorProductIso O hO (Iso.refl F)
          (TensorPower.tensorPowerReindex O hO L h₂)).hom := by
  have hj : n + m + j = m + n + j := by ring
  have hsplit : (Invertible.tensorProductIso O hO (Iso.refl F)
        (TensorPower.tensorPowerReindex O hO L (Int.add_assoc n m j).symm)).hom ≫
      (Invertible.tensorProductIso O hO (Iso.refl F)
        (TensorPower.tensorPowerReindex O hO L hj)).hom =
      (Invertible.tensorProductIso O hO (Iso.refl F)
        (TensorPower.tensorPowerReindex O hO L h₁)).hom :=
    reindexTwist_comp O hO F L (Int.add_assoc n m j).symm hj
  have hfin : actionOf O hO L F (m + n) j
        (tensorPowerMulSectionAt O hO (op (⊤_ C)) L m n t s) =
      actionOf O hO L F (n + m) j (tensorPowerMulSectionAt O hO (op (⊤_ C)) L n m s t) ≫
        (Invertible.tensorProductIso O hO (Iso.refl F)
          (TensorPower.tensorPowerReindex O hO L hj)).hom := by
    rw [tensorPowerMulSectionAt_comm O hO (op (⊤_ C)) L m n t s]
    exact actionOf_reindex O hO L F (Int.add_comm n m) j hj
      (tensorPowerMulSectionAt O hO (op (⊤_ C)) L n m s t)
  calc actionOf O hO L F m j t ≫ actionOf O hO L F n (m + j) s ≫
          (Invertible.tensorProductIso O hO (Iso.refl F)
            (TensorPower.tensorPowerReindex O hO L h₁)).hom
      = (actionOf O hO L F m j t ≫ actionOf O hO L F n (m + j) s ≫
          (Invertible.tensorProductIso O hO (Iso.refl F)
            (TensorPower.tensorPowerReindex O hO L (Int.add_assoc n m j).symm)).hom) ≫
          (Invertible.tensorProductIso O hO (Iso.refl F)
            (TensorPower.tensorPowerReindex O hO L hj)).hom := by
          rw [Category.assoc, Category.assoc, hsplit]
    _ = actionOf O hO L F (n + m) j
          (tensorPowerMulSectionAt O hO (op (⊤_ C)) L n m s t) ≫
          (Invertible.tensorProductIso O hO (Iso.refl F)
            (TensorPower.tensorPowerReindex O hO L hj)).hom := by
          rw [← actionOf_assoc O hO L F n m j s t]
    _ = actionOf O hO L F (m + n) j
          (tensorPowerMulSectionAt O hO (op (⊤_ C)) L m n t s) := hfin.symm
    _ = actionOf O hO L F n j s ≫ actionOf O hO L F m (n + j) t ≫
          (Invertible.tensorProductIso O hO (Iso.refl F)
            (TensorPower.tensorPowerReindex O hO L h₂)).hom :=
          actionOf_assoc O hO L F m n j t s

omit [J.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify J AddCommGrpCat] in
/-- Multiplication by the unit global section is the identity. -/
theorem sectionSmul_one (M : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO)) :
    sectionSmul O hO (1 : O.obj (op (⊤_ C))) M = 𝟙 M := by
  ext U x
  rw [sectionSmul_app, map_one, one_smul]
  rfl

omit [J.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify J AddCommGrpCat] in
/-- Multiplication by a product of global sections is multiplication by each in turn. -/
theorem sectionSmul_mul (r r' : O.obj (op (⊤_ C)))
    (M : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO)) :
    sectionSmul O hO (r * r') M = sectionSmul O hO r M ≫ sectionSmul O hO r' M := by
  ext U x
  show _ = (sectionSmul O hO r' M).val.app U ((sectionSmul O hO r M).val.app U x)
  rw [sectionSmul_app, sectionSmul_app, sectionSmul_app, map_mul, mul_comm, mul_smul]

omit [J.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify J AddCommGrpCat] in
/-- Multiplication by a global section is additive in the section. -/
theorem sectionSmul_add (r r' : O.obj (op (⊤_ C)))
    (M : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO)) :
    sectionSmul O hO (r + r') M = sectionSmul O hO r M + sectionSmul O hO r' M := by
  ext U x
  rw [sectionSmul_app, map_add, add_smul]
  rfl

omit [J.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify J AddCommGrpCat] in
/-- Multiplication by the zero global section is the zero morphism. -/
theorem sectionSmul_zero (M : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO)) :
    sectionSmul O hO (0 : O.obj (op (⊤_ C))) M = 0 := by
  ext U x
  rw [sectionSmul_app, map_zero, zero_smul]
  rfl

omit [J.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify J AddCommGrpCat] in
/-- Multiplication by a global section is natural in the module. -/
theorem comp_sectionSmul (r : O.obj (op (⊤_ C)))
    {M N : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO)} (φ : M ⟶ N) :
    φ ≫ sectionSmul O hO r N = sectionSmul O hO r M ≫ φ :=
  (terminalSectionToEnd (TensorSheafification.structureSheaf O hO) (⊤_ C) terminalIsTerminal
    r).naturality φ

end Stacks.TwistActionLinear

end
