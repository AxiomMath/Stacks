module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import StacksFrontier.CategoryTheory.Sites.Modules.DifferentialOperatorsOrder

/-!
# Differential operators as morphisms of modules over the base sheaf of rings

Let `φ : O₁ ⟶ O₂` be a morphism of sheaves of rings on a site. A differential operator of
finite order relative to `φ` between sheaves of `O₂`-modules is by definition `O₁`-linear on
local sections and compatible with restriction, so it is a morphism of the sheaves of
`O₁`-modules obtained by restriction of scalars along `φ`.

## Main definitions

* `DiffOp.GlobalOp.restrictScalarsHomOfFiniteOrder` and `DiffOp.GlobalOp.restrictScalarsHom`:
  a differential operator of some finite order, respectively of a given order, regarded as a
  morphism of sheaves of `O₁`-modules.

## Main results

* `DiffOp.GlobalOp.map_of_isGlobalDiffOpOfOrder` and
  `DiffOp.GlobalOp.map_smul_of_isGlobalDiffOpOfOrder`: a differential operator of finite order
  commutes with restriction of local sections and with multiplication by sections of `O₁`.
* `DiffOp.GlobalOp.restrictScalarsHom_app_apply`: the morphism of sheaves of `O₁`-modules acts
  on local sections by the differential operator.

## References

* [Stacks Project, Tag 09CR](https://stacks.math.columbia.edu/tag/09CR)
-/

@[expose] public section

open CategoryTheory Opposite

namespace DiffOp

universe v u w m

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {O₁ O₂ : Sheaf J RingCat.{w}}

section

variable {F G : SheafOfModules.{m} O₂}

variable (φ : O₁ ⟶ O₂) {k : ℕ} (D : GlobalOp F G) (hD : IsGlobalDiffOpOfOrder φ k D)

include hD

/-- A differential operator of finite order is compatible with restriction of local
sections. -/
lemma GlobalOp.map_of_isGlobalDiffOpOfOrder {X Y : Cᵒᵖ} (f : X ⟶ Y) (s : F.val.obj X) :
    D Y (F.val.map f s) = G.val.map f (D X s) :=
  RawOp.isNatural_of_isDiffOpOfOrder φ k _ (hD X.unop) (Over.mk f.unop) (Over.mk (𝟙 X.unop))
    (Over.homMk f.unop (by simp)) s

/-- A differential operator of finite order relative to `φ : O₁ ⟶ O₂` is `O₁`-linear on local
sections. -/
lemma GlobalOp.map_smul_of_isGlobalDiffOpOfOrder (X : Cᵒᵖ) (a : O₁.obj.obj X)
    (s : F.val.obj X) :
    D X (sectionRingHom φ X a • s) = sectionRingHom φ X a • D X s :=
  RawOp.isO1Linear_of_isDiffOpOfOrder φ k _ (hD X.unop) (Over.mk (𝟙 X.unop)) a s

end

section

variable {F G : SheafOfModules.{m} O₂} (φ : O₁ ⟶ O₂) (D : GlobalOp F G)
  (hD : ∃ k, IsGlobalDiffOpOfOrder φ k D)

include hD

/-- A differential operator of some finite order relative to `φ : O₁ ⟶ O₂`, regarded as a
morphism of the sheaves of `O₁`-modules obtained by restriction of scalars along `φ`. -/
noncomputable def GlobalOp.restrictScalarsHomOfFiniteOrder :
    (SheafOfModules.restrictScalars φ).obj F ⟶ (SheafOfModules.restrictScalars φ).obj G where
  val :=
    { app := fun X => ModuleCat.ofHom
        (X := ((PresheafOfModules.restrictScalars φ.hom).obj F.val).obj X)
        (Y := ((PresheafOfModules.restrictScalars φ.hom).obj G.val).obj X)
        { toFun := D X
          map_add' := (D X).map_add
          map_smul' := fun a s => hD.elim fun _ hk =>
            GlobalOp.map_smul_of_isGlobalDiffOpOfOrder φ D hk X a s }
      naturality := fun {X Y} f => by
        apply ModuleCat.hom_ext
        refine LinearMap.ext fun s => ?_
        exact hD.elim fun _ hk => GlobalOp.map_of_isGlobalDiffOpOfOrder φ D hk f s }

/-- On local sections over `X`, `GlobalOp.restrictScalarsHomOfFiniteOrder φ D hD` acts by
`D X`. -/
@[simp]
lemma GlobalOp.restrictScalarsHomOfFiniteOrder_app_apply (X : Cᵒᵖ) (s : F.val.obj X) :
    (GlobalOp.restrictScalarsHomOfFiniteOrder φ D hD).val.app X s = D X s := rfl

end

section

variable (φ : O₁ ⟶ O₂) {k : ℕ} {F G : SheafOfModules.{m} O₂} (D : GlobalOp F G)
  (hD : IsGlobalDiffOpOfOrder φ k D)

include hD

/-- A differential operator of order at most `k` relative to `φ : O₁ ⟶ O₂`, regarded as a
morphism of the sheaves of `O₁`-modules obtained by restriction of scalars along `φ`. -/
noncomputable def GlobalOp.restrictScalarsHom :
    (SheafOfModules.restrictScalars φ).obj F ⟶ (SheafOfModules.restrictScalars φ).obj G :=
  GlobalOp.restrictScalarsHomOfFiniteOrder φ D ⟨k, hD⟩

/-- On local sections over `X`, `GlobalOp.restrictScalarsHom φ D hD` acts by `D X`. -/
@[simp]
lemma GlobalOp.restrictScalarsHom_app_apply (X : Cᵒᵖ) (s : F.val.obj X) :
    (GlobalOp.restrictScalarsHom φ D hD).val.app X s = D X s := rfl

end

end DiffOp
