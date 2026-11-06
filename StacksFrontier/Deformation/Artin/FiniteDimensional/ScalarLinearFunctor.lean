module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EndActionLift

/-!
# An additive functor of a vector space is a linear functor

Let `k` be a commutative ring and `P` an additive functor from finitely generated `k`-modules to
abelian groups. Multiplication by `c : k` on `V` is an endomorphism of `V`, and `P` carries it to
an endomorphism of `P(V)`; this makes `P(V)` a `k`-module, and `P` a `k`-linear functor to
`k`-modules.

## Main definitions

* `Deformation.Artin.scalarEndAction`: the action of `k` on `P` through the scalar
  endomorphisms.
* `Deformation.Artin.scalarLinearFunctor`: `P` as a `k`-linear functor to `k`-modules.

## Main results

* `Deformation.Artin.scalarLinearFunctor_smul`: the scalars of `scalarLinearFunctor P` at `V`
  are the images under `P` of the scalar endomorphisms of `V`.
* `Deformation.Artin.scalarLinearFunctor_additive`, `Deformation.Artin.scalarLinearFunctor_linear`:
  `scalarLinearFunctor P` is additive and `k`-linear.

## References

* [Stacks Project, Tag 06I7](https://stacks.math.columbia.edu/tag/06I7)
* [Stacks Project, Tag 0DLL](https://stacks.math.columbia.edu/tag/0DLL)
-/

open CategoryTheory

universe w u

@[expose] public noncomputable section

namespace Deformation.Artin

variable {k : Type u} [CommRing k] (P : FGModuleCat.{u} k ⥤ AddCommGrpCat.{w}) [P.Additive]

/-- **The action of `k` on an additive functor of `k`-modules**: `c` acts on `P(V)` by the
image under `P` of multiplication by `c` on `V`. -/
def scalarEndAction : k →+* End P where
  toFun c := .of
    { app V := P.map (c • 𝟙 V)
      naturality V W f := by
        rw [← P.map_comp, ← P.map_comp, Linear.comp_smul, Linear.smul_comp, Category.comp_id,
          Category.id_comp] }
  map_one' := End.ext <| NatTrans.ext (funext fun V ↦ by
    change P.map ((1 : k) • 𝟙 V) = 𝟙 _
    rw [one_smul, P.map_id])
  map_mul' a b := End.ext <| NatTrans.ext (funext fun V ↦ by
    change P.map ((a * b) • 𝟙 V) = P.map (b • 𝟙 V) ≫ P.map (a • 𝟙 V)
    rw [← P.map_comp, Linear.smul_comp, Category.id_comp, smul_smul, mul_comm])
  map_zero' := End.ext <| NatTrans.ext (funext fun V ↦ by
    change P.map ((0 : k) • 𝟙 V) = 0
    rw [zero_smul, P.map_zero])
  map_add' a b := End.ext <| NatTrans.ext (funext fun V ↦ by
    change P.map ((a + b) • 𝟙 V) = P.map (a • 𝟙 V) + P.map (b • 𝟙 V)
    rw [add_smul, P.map_add])

/-- The component of `scalarEndAction P c` at `V` is the image under `P` of multiplication by `c`
on `V`. -/
@[simp]
theorem scalarEndAction_app (c : k) (V : FGModuleCat.{u} k) :
    (scalarEndAction P c).asHom.app V = P.map (c • 𝟙 V) := rfl

/-- **An additive functor of `k`-modules as a `k`-linear functor**: `P(V)` with `c` acting as
`P(c · 𝟙_V)`. -/
def scalarLinearFunctor : FGModuleCat.{u} k ⥤ ModuleCat.{w} k :=
  Stacks.ModuleCatLift.ofEndAction k P (scalarEndAction P)

/-- The underlying abelian group functor of `scalarLinearFunctor P` is `P`. -/
theorem scalarLinearFunctor_comp_forget₂ :
    scalarLinearFunctor P ⋙ forget₂ (ModuleCat.{w} k) AddCommGrpCat.{w} = P := rfl

/-- In `scalarLinearFunctor P`, `c : k` acts on the value at `V` as `P.map (c • 𝟙 V)`. -/
theorem scalarLinearFunctor_smul (V : FGModuleCat.{u} k) (c : k)
    (x : (scalarLinearFunctor P).obj V) :
    c • x = (P.map (c • 𝟙 V)) (show P.obj V from x) := rfl

/-- The morphisms of `scalarLinearFunctor P` are those of `P`. -/
theorem scalarLinearFunctor_map_apply {V W : FGModuleCat.{u} k} (f : V ⟶ W)
    (x : (scalarLinearFunctor P).obj V) :
    (scalarLinearFunctor P).map f x = (P.map f) (show P.obj V from x) := rfl

/-- `scalarLinearFunctor P` is additive. -/
instance scalarLinearFunctor_additive : (scalarLinearFunctor P).Additive where
  map_add {V W f g} := by
    ext x
    change (P.map (f + g)) x = (P.map f) x + (P.map g) x
    rw [P.map_add]
    rfl

/-- `scalarLinearFunctor P` is `k`-linear. -/
instance scalarLinearFunctor_linear : (scalarLinearFunctor P).Linear k where
  map_smul {V W} f c := by
    ext x
    change (P.map (c • f)) x = (P.map (c • 𝟙 W)) ((P.map f) x)
    rw [show c • f = f ≫ (c • 𝟙 W) by rw [Linear.comp_smul, Category.comp_id], P.map_comp]
    rfl

end Deformation.Artin

end
