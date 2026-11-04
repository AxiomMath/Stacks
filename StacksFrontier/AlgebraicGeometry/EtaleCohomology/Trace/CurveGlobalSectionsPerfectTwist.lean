module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveGlobalSectionsPerfectAlgebra
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Point.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors

/-!
# Twisting a sheaf of modules by a finite free right module

Let `(C, J)` be a site and `Λ` a ring, not necessarily commutative. For a finite free right
`Λ`-module `N` and a sheaf `M` of left `Λ`-modules, the presheaf of abelian groups
`U ↦ N ⊗[Λ] M(U)` is a sheaf: tensoring with `N` is a finite power, which commutes with limits.
This file packages these twists as a bifunctor from finite free right `Λ`-modules and sheaves of
`Λ`-modules to abelian sheaves, whose global sections are, on the nose, the twists of the global
sections. They are the sheaves `N ⊗[Λ] K` of the projection formula in the proof of
[Stacks, Tag 03TV], restricted to the finite free modules `N` which is all that proof uses.

## Main definitions

* `Stacks.SheafTwist.FiniteFree`: the full subcategory of finite free right `Λ`-modules.
* `Stacks.SheafTwist.tensorAb`: the functor `M ↦ N ⊗[Λ] M` from left `Λ`-modules to abelian
  groups.
* `Stacks.SheafTwist.twist`: the bifunctor `(N, M) ↦ N ⊗[Λ] M` on finite free right modules and
  sheaves of left modules.

## Main results

* `Stacks.SheafTwist.preservesLimits_tensorAb`: tensoring with a finite free module preserves
  limits.

## References

* [Stacks Project, Tag 03TV](https://stacks.math.columbia.edu/tag/03TV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite StacksDraft.Perfect StacksDraft.Perfect.TorTotal

universe w v u r

namespace Stacks.SheafTwist

variable (Λ : Type r) [Ring Λ]

/-- Finite free right `Λ`-modules. -/
def finiteFree : ObjectProperty (ModuleCat.{v} (MulOpposite Λ)) :=
  fun N => Module.Finite (MulOpposite Λ) N ∧ Module.Free (MulOpposite Λ) N

/-- The full subcategory of finite free right `Λ`-modules. -/
abbrev FiniteFree := (finiteFree.{v} Λ).FullSubcategory

variable {Λ}

/-- An object of `FiniteFree Λ` is a finite right `Λ`-module. -/
instance (N : FiniteFree.{v} Λ) : Module.Finite (MulOpposite Λ) N.obj := N.property.1

/-- An object of `FiniteFree Λ` is a free right `Λ`-module. -/
instance (N : FiniteFree.{v} Λ) : Module.Free (MulOpposite Λ) N.obj := N.property.2

/-- The `ι`-th power functor on left modules, read in abelian groups, preserves limits. -/
instance preservesLimits_powFunctor_forget₂ (ι : Type v) :
    PreservesLimits (powFunctor (Λ := Λ) ι ⋙ forget₂ (ModuleCat.{v} ℤ) AddCommGrpCat.{v}) := by
  have e : (powFunctor (Λ := Λ) ι ⋙ forget₂ (ModuleCat.{v} ℤ) AddCommGrpCat.{v}) ⋙
      forget AddCommGrpCat.{v} ≅ forget (ModuleCat.{v} Λ) ⋙ coyoneda.obj (op ι) :=
    NatIso.ofComponents (fun M => (TypeCat.homEquiv (X := ι) (Y := M)).symm.toIso) (fun f => by
      ext x
      rfl)
  have : PreservesLimits ((powFunctor (Λ := Λ) ι ⋙ forget₂ (ModuleCat.{v} ℤ)
      AddCommGrpCat.{v}) ⋙ forget AddCommGrpCat.{v}) := preservesLimits_of_natIso e.symm
  exact preservesLimits_of_reflects_of_preserves _ (forget AddCommGrpCat.{v})

variable (D : BalancedDerivedTensoring.{r, v} Λ)

/-- **`M ↦ N ⊗[Λ] M`**, from left `Λ`-modules to abelian groups. -/
abbrev tensorAb (N : ModuleCat.{v} (MulOpposite Λ)) : ModuleCat.{v} Λ ⥤ AddCommGrpCat.{v} :=
  D.ordinary.obj N ⋙ forget₂ (ModuleCat.{v} ℤ) AddCommGrpCat.{v}

/-- **Tensoring with a finite free right module preserves limits**. -/
instance preservesLimits_tensorAb (N : FiniteFree.{v} Λ) : PreservesLimits (tensorAb D N.obj) :=
  preservesLimits_of_natIso (Functor.isoWhiskerRight
    (tensorBasisRightIso D (Module.Free.chooseBasis (MulOpposite Λ) N.obj)).symm
    (forget₂ (ModuleCat.{v} ℤ) AddCommGrpCat.{v}))

/-- Tensoring with a finite free right module is additive. -/
instance tensorAb_additive (N : ModuleCat.{v} (MulOpposite Λ)) : (tensorAb D N).Additive :=
  inferInstance

/-! ### The twist bifunctor on sheaves on a small étale site -/

section Twist

variable {Λ' : Type r} [Ring Λ'] (D' : BalancedDerivedTensoring.{r, max (u + 1) r} Λ')
  (Y : AlgebraicGeometry.Scheme.{u})

/-- Tensoring with a finite free right module carries sheaves on the small étale site to
sheaves. -/
instance hasSheafCompose_tensorAb (N : FiniteFree.{max (u + 1) r} Λ') :
    Y.smallEtaleTopology.HasSheafCompose (tensorAb D' N.obj) := by
  have : PreservesLimitsOfSize.{u, u + 1} (tensorAb D' N.obj) :=
    preservesLimitsOfSize_shrink.{u + 1, max (u + 1) r, u, max (u + 1) r} _
  infer_instance

/-- **The twist bifunctor** `(N, M) ↦ N ⊗[Λ] M`, from finite free right `Λ`-modules and sheaves of
left `Λ`-modules on the small étale site of `Y` to abelian sheaves: sectionwise tensor product,
which is already a sheaf. -/
def twist : FiniteFree.{max (u + 1) r} Λ' ⥤ Stacks.EtaleCohomology.EtaleModules.{u, r} Λ' Y ⥤
    Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) r} where
  obj N := sheafCompose Y.smallEtaleTopology (tensorAb D' N.obj)
  map f := sheafCompose_map Y.smallEtaleTopology
    (Functor.whiskerRight (D'.ordinary.map f.hom) (forget₂ (ModuleCat ℤ) AddCommGrpCat))
  map_id N := by
    rw [ObjectProperty.FullSubcategory.id_hom, CategoryTheory.Functor.map_id,
      Functor.whiskerRight_id']
    rfl
  map_comp f g := by
    rw [ObjectProperty.FullSubcategory.comp_hom, CategoryTheory.Functor.map_comp,
      Functor.whiskerRight_comp]
    rfl

/-- Each twist is additive. -/
instance twist_obj_additive (N : FiniteFree.{max (u + 1) r} Λ') :
    ((twist D' Y).obj N).Additive where
  map_add := by
    intro M M' f g
    ext U : 3
    exact (tensorAb D' N.obj).map_add

/-- The twist is additive in the module. -/
instance twist_additive : (twist D' Y).Additive where
  map_add := by
    intro N N' f g
    ext M : 3
    refine NatTrans.ext (funext fun U => ?_)
    change (forget₂ (ModuleCat ℤ) AddCommGrpCat).map ((D'.ordinary.map (f.hom + g.hom)).app _) =
      (forget₂ (ModuleCat ℤ) AddCommGrpCat).map ((D'.ordinary.map f.hom).app _) +
        (forget₂ (ModuleCat ℤ) AddCommGrpCat).map ((D'.ordinary.map g.hom).app _)
    rw [D'.ordinary.map_add, NatTrans.app_add, Functor.map_add]
    rfl

end Twist

end Stacks.SheafTwist

end
