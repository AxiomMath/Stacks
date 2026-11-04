module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Center.Linear
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalSectionSmul

/-!
# Sheaves of modules as a linear category over a base ring

Let `O` be a sheaf of rings on a site with a terminal object `T`, whose rings of sections are
commutative. Multiplication by a section `a ∈ O(T)` is an endomorphism of every sheaf of
`O`-modules, natural in the module (`Stacks.SheafOfModules.terminalSectionToEnd`); this file
records that `a ↦` that endomorphism is a *ring homomorphism* into the centre
`CatCenter (SheafOfModules O) = End (𝟭 (SheafOfModules O))`, and therefore that a ring map
`A →+* O(T)` makes `SheafOfModules O` an `A`-linear category.

For a scheme `X` over `Spec A` the ring map is `Stacks.LocalCohomology.baseScalars`, and the
resulting `A`-linear structure is what lets a complex of sheaves of `O_X`-modules carry
differentials given by matrices with entries in `A` — a Koszul complex of a sequence in `A`, for
instance, whose entries have to act on the objects and not merely on the sections.

## Main definitions

* `Stacks.SheafOfModules.terminalSectionRingHom` — multiplication by a section over a terminal
  object, as a ring map into the centre of the category of sheaves of modules.
* `Stacks.SheafOfModules.linearOfTerminalSection` — the `A`-linear structure attached to a ring
  map `A →+* O(T)`.
* `AlgebraicGeometry.Scheme.linearOfRingHom` — the same for a scheme and a ring map into its
  global sections.

## Main results

* `Stacks.SheafOfModules.smul_val_app` — a scalar acts on local sections by the restriction of
  its image, and `Stacks.SheafOfModules.smul_val_app_terminal` is the same over `T`, where the
  restriction is trivial.

## Implementation notes

`Stacks.Cohomology.SiteModules.linearSheafOfModules` already makes
`SheafOfModules O` linear over the ring `Stacks.Cohomology.SiteModules.GlobalSectionRing O` of
compatible families of local sections, by the same action
`Stacks.SheafOfModules.globalSectionToEnd`. The two structures agree wherever they are both
defined, since each is `f ↦ (multiplication by the scalar) ≫ f`; what is new here is the base
ring, which is not a ring of sections of `O` and reaches the category only through a ring map.

Commutativity of the rings of sections is assumed in the unbundled form
`∀ U, IsMulCommutative (O.obj.obj U)`, as for `Stacks.SheafOfModules.terminalSectionToEnd`. For
a scheme that instance is not found by synthesis through `forget₂ CommRingCat RingCat`, so
`AlgebraicGeometry.Scheme.isMulCommutative_ringCatSheaf` supplies it. The same proposition is
also the instance `Stacks.AlgebraicGeometry.PrincipalIdealExtension.isMulCommutative_ringCatSheaf`,
declared in a file that this one does not import, so it is repeated here.

The `A`-linear structures are `def`s rather than instances: the ring `A` is not determined by
the sheaf of rings, so they are introduced with `letI` at the point of use.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u w m

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{w}) [∀ U, IsMulCommutative (R.obj.obj U)]

/-- **Multiplication by a section over a terminal object, as a ring map into the centre of the
category of sheaves of modules.** -/
def terminalSectionRingHom (T : C) (hT : IsTerminal T) :
    R.obj.obj (op T) →+* CatCenter (_root_.SheafOfModules.{m} R) where
  toFun f := terminalSectionToEnd R T hT f
  map_one' := by
    ext M U x
    change R.obj.map (hT.from U.unop).op (1 : R.obj.obj (op T)) • x = x
    rw [map_one, one_smul]
  map_mul' a b := by
    ext M U x
    rw [CatCenter.mul_app]
    change R.obj.map (hT.from U.unop).op (a * b) • x =
      R.obj.map (hT.from U.unop).op b • R.obj.map (hT.from U.unop).op a • x
    rw [map_mul, mul_comm', mul_smul]
  map_zero' := by
    ext M U x
    change R.obj.map (hT.from U.unop).op (0 : R.obj.obj (op T)) • x = 0
    rw [map_zero, zero_smul]
  map_add' a b := by
    ext M U x
    change R.obj.map (hT.from U.unop).op (a + b) • x =
      R.obj.map (hT.from U.unop).op a • x + R.obj.map (hT.from U.unop).op b • x
    rw [map_add, add_smul]

/-- `Stacks.SheafOfModules.terminalSectionRingHom` is multiplication by the section. -/
@[simp] theorem terminalSectionRingHom_apply (T : C) (hT : IsTerminal T)
    (f : R.obj.obj (op T)) :
    terminalSectionRingHom.{v, u, w, m} R T hT f = terminalSectionToEnd R T hT f := rfl

variable (A : Type*) [Ring A]

/-- **Sheaves of `O`-modules form an `A`-linear category**, for a ring map from `A` to the
sections of `O` over a terminal object. -/
@[instance_reducible]
def linearOfTerminalSection (T : C) (hT : IsTerminal T) (φ : A →+* R.obj.obj (op T)) :
    Linear A (_root_.SheafOfModules.{m} R) :=
  Linear.ofRingMorphism ((terminalSectionRingHom R T hT).comp φ)

/-- **A scalar acts on local sections by the restriction of its image.** -/
theorem smul_val_app (T : C) (hT : IsTerminal T) (φ : A →+* R.obj.obj (op T))
    {M N : _root_.SheafOfModules.{m} R} (a : A) (g : M ⟶ N) (U : Cᵒᵖ) (x : M.val.obj U) :
    letI := linearOfTerminalSection R A T hT φ
    (a • g).val.app U x = R.obj.map (hT.from U.unop).op (φ a) • g.val.app U x :=
  (g.val.app U).hom.map_smul _ x

/-- **Over the terminal object a scalar acts by its image itself**, the restriction being
trivial there. -/
theorem smul_val_app_terminal (T : C) (hT : IsTerminal T) (φ : A →+* R.obj.obj (op T))
    {M N : _root_.SheafOfModules.{m} R} (a : A) (g : M ⟶ N) (x : M.val.obj (op T)) :
    letI := linearOfTerminalSection R A T hT φ
    (a • g).val.app (op T) x = φ a • g.val.app (op T) x := by
  refine (smul_val_app R A T hT φ a g (op T) x).trans ?_
  rw [show hT.from (op T).unop = 𝟙 T from hT.hom_ext _ _, op_id, R.obj.map_id]
  rfl

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Scheme

open TopologicalSpace

/-- The rings of sections of the structure sheaf of a scheme are commutative, in the unbundled
form that `Stacks.SheafOfModules.globalSectionToEnd` asks for. -/
instance isMulCommutative_ringCatSheaf (X : Scheme.{u}) (U : (Opens X)ᵒᵖ) :
    IsMulCommutative (X.ringCatSheaf.obj.obj U) :=
  inferInstanceAs (IsMulCommutative (X.presheaf.obj U))

/-- **Sheaves of modules on a scheme form an `A`-linear category**, for a ring map from `A` to
the global sections of the structure sheaf. -/
@[instance_reducible]
def linearOfRingHom (X : Scheme.{u}) (A : Type u) [Ring A] (φ : A →+* Γ(X, ⊤)) :
    Linear A (SheafOfModules.{m} X.ringCatSheaf) :=
  Stacks.SheafOfModules.linearOfTerminalSection X.ringCatSheaf A ⊤ isTerminalTop φ

/-- **A scalar acts on global sections by its image.** -/
theorem smul_val_app_top (X : Scheme.{u}) (A : Type u) [Ring A] (φ : A →+* Γ(X, ⊤))
    {M N : SheafOfModules.{m} X.ringCatSheaf} (a : A) (g : M ⟶ N) (x : M.val.obj (op ⊤)) :
    letI := linearOfRingHom.{u, m} X A φ
    (a • g).val.app (op ⊤) x =
      (show X.ringCatSheaf.obj.obj (op ⊤) from φ a) • g.val.app (op ⊤) x :=
  Stacks.SheafOfModules.smul_val_app_terminal X.ringCatSheaf A ⊤ isTerminalTop φ a g x

end AlgebraicGeometry.Scheme

end
