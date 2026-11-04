module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-!
# Sections of a fibre product of sheaves of modules

The sections over `W` of the fibre product `A ×_Z B` of two morphisms `φ : A ⟶ Z`, `ψ : B ⟶ Z`
of sheaves of modules are the pairs of sections of `A` and `B` over `W` with the same image in
`Z`: evaluation at `W` preserves limits.

## Main definitions

* `SheafOfModules.pullbackMk`: the section of `A ×_Z B` with prescribed components.

## Main results

* `SheafOfModules.pullback_fst_pullbackMk`, `SheafOfModules.pullback_snd_pullbackMk`: its
  components.
* `SheafOfModules.pullback_section_ext`: a section of `A ×_Z B` is determined by its two
  components.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v v₁ u₁

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{v}} [HasSheafify J AddCommGrpCat.{v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
  {A B Z : SheafOfModules.{v} R} (φ : A ⟶ Z) (ψ : B ⟶ Z) (W : Cᵒᵖ)

/-- Evaluation at `W` preserves the fibre product of `φ` and `ψ`. -/
def pullbackSectionsIsLimit :
    IsLimit (PullbackCone.mk
      (f := (evaluation R W ⋙ CategoryTheory.forget (ModuleCat.{v} (R.obj.obj W))).map φ)
      (g := (evaluation R W ⋙ CategoryTheory.forget (ModuleCat.{v} (R.obj.obj W))).map ψ)
      ((evaluation R W ⋙ CategoryTheory.forget (ModuleCat.{v} (R.obj.obj W))).map
        (pullback.fst φ ψ))
      ((evaluation R W ⋙ CategoryTheory.forget (ModuleCat.{v} (R.obj.obj W))).map
        (pullback.snd φ ψ))
      (by rw [← Functor.map_comp, ← Functor.map_comp, pullback.condition])) :=
  isLimitPullbackConeMapOfIsLimit
    (evaluation R W ⋙ CategoryTheory.forget (ModuleCat.{v} (R.obj.obj W))) pullback.condition
    (pullbackIsPullback φ ψ)

/-- The section of `A ×_Z B` over `W` with components `a` and `b`. -/
def pullbackMk (a : A.val.obj W) (b : B.val.obj W) (h : φ.val.app W a = ψ.val.app W b) :
    (pullback φ ψ).val.obj W :=
  (PullbackCone.IsLimit.equivPullbackObj (pullbackSectionsIsLimit φ ψ W)).symm ⟨(a, b), h⟩

omit [HasSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat] in
/-- The first component of `pullbackMk φ ψ W a b h` is `a`. -/
@[simp]
theorem pullback_fst_pullbackMk (a : A.val.obj W) (b : B.val.obj W)
    (h : φ.val.app W a = ψ.val.app W b) :
    (pullback.fst φ ψ).val.app W (pullbackMk φ ψ W a b h) = a :=
  PullbackCone.IsLimit.equivPullbackObj_symm_apply_fst (pullbackSectionsIsLimit φ ψ W)
    ⟨(a, b), h⟩

omit [HasSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat] in
/-- The second component of `pullbackMk φ ψ W a b h` is `b`. -/
@[simp]
theorem pullback_snd_pullbackMk (a : A.val.obj W) (b : B.val.obj W)
    (h : φ.val.app W a = ψ.val.app W b) :
    (pullback.snd φ ψ).val.app W (pullbackMk φ ψ W a b h) = b :=
  PullbackCone.IsLimit.equivPullbackObj_symm_apply_snd (pullbackSectionsIsLimit φ ψ W)
    ⟨(a, b), h⟩

omit [HasSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat] in
/-- A section of `A ×_Z B` is determined by its two components. -/
theorem pullback_section_ext {x y : (pullback φ ψ).val.obj W}
    (h₁ : (pullback.fst φ ψ).val.app W x = (pullback.fst φ ψ).val.app W y)
    (h₂ : (pullback.snd φ ψ).val.app W x = (pullback.snd φ ψ).val.app W y) : x = y :=
  (PullbackCone.IsLimit.equivPullbackObj (pullbackSectionsIsLimit φ ψ W)).injective
    (Subtype.ext (Prod.ext h₁ h₂))

end SheafOfModules

end
