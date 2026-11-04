module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.CategoryTheory.Preadditive.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.DifferentialOperators
public import StacksFrontier.CategoryTheory.Sites.Modules.DifferentialOperators
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The category of finite-order differential operators

Let `a : X ⟶ S` be a morphism of schemes. The quasi-coherent `𝒪_X`-modules are the objects of
a category whose morphisms are the differential operators on `X/S` of some finite order, taken
relative to the structural map `Scheme.Hom.relativeStructureSheafMap a`. An order bound is
recorded existentially, so the order of a morphism is not part of its data; the operators of
finite order between two fixed modules form an additive subgroup of the group of all global
operators, and composition adds orders, so the category is preadditive.

## Main definitions

* `AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory` is the type of quasi-coherent
  `𝒪_X`-modules, regarded as the objects of this category.
* `AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory.homAddSubgroup` is the additive
  subgroup of the global operators between two such modules consisting of those which have
  some finite order.
* `AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory.Hom` is the resulting type of
  morphisms.
* `AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory.homOrderZero` regards a morphism
  of the underlying sheaves of modules as such a morphism.

## Main results

* `AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory.instCategory`: composition of
  finite-order differential operators makes the quasi-coherent `𝒪_X`-modules a category.
* `AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory.instPreadditive`: pointwise
  addition of finite-order differential operators is compatible with that composition.

## Implementation notes

The group structure on the global operators between two sheaves of modules is the pointwise
one, obtained by unfolding `DiffOp.GlobalOp` to the product of the groups of additive maps on
local sections.

## References

* [Stacks Project, Tag 0G46](https://stacks.math.columbia.edu/tag/0G46)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- The global operators between two sheaves of modules on a scheme form an additive group
under pointwise addition of the additive maps on local sections. -/
local instance globalOpAddCommGroup {F G : X.Modules} :
    AddCommGroup (DiffOp.GlobalOp F G) := by
  unfold DiffOp.GlobalOp
  infer_instance

/-- A quasi-coherent module, regarded as an object of the category of finite-order
differential operators on `X/S`. -/
@[stacks 0G46 "category_of_finite_order_differential_operators"]
structure FiniteOrderDifferentialOperatorCategory (a : X ⟶ S) where
  /-- The underlying sheaf of modules. -/
  module : X.Modules
  [isQuasicoherent : module.IsQuasicoherent]

namespace FiniteOrderDifferentialOperatorCategory

variable {a : X ⟶ S}

attribute [instance] isQuasicoherent

/-- The additive subgroup of global operators which have some finite order. -/
noncomputable def homAddSubgroup
    (F G : FiniteOrderDifferentialOperatorCategory a) :
    AddSubgroup (DiffOp.GlobalOp F.module G.module) where
  carrier D := ∃ k, DiffOp.IsGlobalDiffOpOfOrder a.relativeStructureSheafMap k D
  zero_mem' := by
    refine ⟨0, fun U => ⟨?_, ?_⟩⟩
    · intro Y Y' h s
      change (0 : G.module.val.obj (Opposite.op Y.left)) =
        G.module.val.presheaf.map h.left.op 0
      exact (map_zero _).symm
    · intro Y r s
      change (0 : G.module.val.obj (Opposite.op Y.left)) = r • 0
      simp
  add_mem' := by
    rintro D E ⟨k, hD⟩ ⟨l, hE⟩
    have promote (n m : ℕ) (h : n ≤ m) {A B : X.Modules}
        (T : DiffOp.GlobalOp A B)
        (hT : DiffOp.IsGlobalDiffOpOfOrder a.relativeStructureSheafMap n T) :
        DiffOp.IsGlobalDiffOpOfOrder a.relativeStructureSheafMap m T := by
      induction m, h using Nat.le_induction with
      | base => exact hT
      | succ m hnm ih =>
          exact fun U => DiffOp.RawOp.isDiffOpOfOrder_succ_of_isDiffOpOfOrder
            a.relativeStructureSheafMap m (T.restrict U) (ih U)
    exact ⟨max k l, fun U => DiffOp.RawOp.isDiffOpOfOrder_add a.relativeStructureSheafMap _ _ _
      (promote k _ (Nat.le_max_left _ _) D hD U) (promote l _ (Nat.le_max_right _ _) E hE U)⟩
  neg_mem' := by
    rintro D ⟨k, hD⟩
    let negId : DiffOp.GlobalOp G.module G.module := fun _ => -AddMonoidHom.id _
    have hnegId :
        DiffOp.IsGlobalDiffOpOfOrder a.relativeStructureSheafMap 0 negId := by
      intro U
      refine ⟨?_, ?_⟩
      · intro Y Y' h s
        change -G.module.val.presheaf.map h.left.op s =
          G.module.val.presheaf.map h.left.op (-s)
        exact (map_neg _ _).symm
      · intro Y r s
        change -(r • s) = r • (-s)
        simp
    refine ⟨k, ?_⟩
    have heq : DiffOp.GlobalOp.comp negId D = -D := by
      funext U
      ext s
      rfl
    rw [← heq]
    exact DiffOp.isGlobalDiffOpOfOrder_comp a.relativeStructureSheafMap D negId hD hnegId

/-- Morphisms in the category of finite-order differential operators. -/
@[stacks 0G46 "category_of_finite_order_differential_operators"]
noncomputable abbrev Hom (F G : FiniteOrderDifferentialOperatorCategory a) :=
  homAddSubgroup F G

/-- The identity morphism: the identity on local sections, a differential operator of
order zero. -/
noncomputable def identity (F : FiniteOrderDifferentialOperatorCategory a) : Hom F F :=
  ⟨fun _ => AddMonoidHom.id _, 0, fun _ => ⟨fun _ _ _ _ => rfl, fun _ _ _ => rfl⟩⟩

/-- Composition of morphisms: the composite of two differential operators of finite orders
has finite order, bounded by the sum of the two orders. -/
@[sga "3 VIIA 1.2" "special case", sga "3 VIIA 1.4" "partial"]
noncomputable def comp {F G H : FiniteOrderDifferentialOperatorCategory a}
    (f : Hom F G) (g : Hom G H) : Hom F H := by
  refine ⟨DiffOp.GlobalOp.comp g.1 f.1, ?_⟩
  obtain ⟨k, hf⟩ := f.property
  obtain ⟨l, hg⟩ := g.property
  exact ⟨k + l, DiffOp.isGlobalDiffOpOfOrder_comp a.relativeStructureSheafMap f.1 g.1 hf hg⟩

/-- A morphism of the underlying sheaves of modules, regarded as a morphism of the category of
finite-order differential operators: it is a differential operator of order zero. -/
noncomputable def homOrderZero {F G : FiniteOrderDifferentialOperatorCategory a}
    (f : F.module ⟶ G.module) : Hom F G :=
  ⟨AlgebraicGeometry.SheafOfModules.homGlobalOp f,
    0, AlgebraicGeometry.SheafOfModules.homGlobalOp_isOrderZero a.relativeStructureSheafMap f⟩

/-- Composition of finite-order differential operators makes quasi-coherent modules
into a category. -/
@[stacks 0G46 "category_of_finite_order_differential_operators"]
noncomputable instance instCategory :
    Category (FiniteOrderDifferentialOperatorCategory a) where
  Hom := fun F G => homAddSubgroup F G
  id := fun F => identity F
  comp := fun f g => comp f g
  id_comp := by
    intro F G f
    apply Subtype.ext
    funext U
    ext s
    rfl
  comp_id := by
    intro F G f
    apply Subtype.ext
    funext U
    ext s
    rfl
  assoc := by
    intro F G H K f g h
    apply Subtype.ext
    funext U
    ext s
    rfl

/-- The pointwise addition of finite-order differential operators is compatible with
composition. -/
@[stacks 0G46 "category_of_finite_order_differential_operators"]
noncomputable instance instPreadditive :
    Preadditive (FiniteOrderDifferentialOperatorCategory a) where
  homGroup := fun F G => show AddCommGroup (homAddSubgroup F G) from inferInstance
  comp_add := by
    intro F G H f g h
    apply Subtype.ext
    funext U
    ext s
    rfl
  add_comp := by
    intro F G H f g h
    apply Subtype.ext
    funext U
    ext s
    exact (h.1 U).map_add _ _

end FiniteOrderDifferentialOperatorCategory

end AlgebraicGeometry
