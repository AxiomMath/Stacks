module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorAlgebraPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedModuleAbelian
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Restriction of scalars for graded modules along a homomorphism of graded algebra sheaves

Let `R` be a sheaf of rings on a site, let `A` and `B` be sheaves of `ℤ`-graded `R`-algebras
(`SheafOfModules.GradedAlgebra`, [Stacks, Tag 0FQW]) and let `φ : A ⟶ B` be a *unital*
homomorphism (`SheafOfModules.GradedAlgebra.UnitalHom`). Every right graded `B`-module
(`SheafOfModules.GradedModule`, [Stacks, Tag 0FQZ]) is then a right graded `A`-module, by letting
a homogeneous local section `a` of `A` act as `φ a` does.

This is the module-level counterpart of `SheafOfModules.GradedAlgebra.UnitalHom`; the library
already carries restriction along a change of the base *ring* sheaf, but nothing that changes the
graded algebra while keeping the ring sheaf fixed.

## Main definitions

* `SheafOfModules.GradedModule.restrictScalars` — the graded `A`-module underlying a graded
  `B`-module. Its homogeneous pieces are *the same sheaves of modules*: only the action changes,
  so no transport is needed to compare cohomology of the pieces before and after restriction.
* `SheafOfModules.GradedModule.restrictScalarsMap` and
  `SheafOfModules.GradedModule.restrictScalarsFunctor` — the construction on morphisms, and the
  resulting functor `Mod(B) ⥤ Mod(A)`. It is the identity on the underlying degreewise
  morphisms, hence faithful (`restrictScalarsFunctor_faithful`).

## Main results

* `SheafOfModules.GradedModule.restrictScalars_piece` and `restrictScalars_smul` — the two
  computation rules. Both hold by `rfl`; they are stated so that proofs can rewrite rather than
  unfold.
* `SheafOfModules.GradedModule.restrictScalarsFunctor_additive` — the functor is additive, so it
  carries a short exact sequence of graded `B`-modules to one of graded `A`-modules once the
  degreewise maps are unchanged.

## Implementation notes

**Why unital homomorphisms.** The `smul_one` law of a graded module says that the degree-zero
unit of the algebra acts as the identity. Transporting it needs `φ` to carry the unit of `A` to
the unit of `B`, which is exactly the extra field of `UnitalHom` over `GradedAlgebra.Hom`. The
other six laws use only multiplicativity and the fact that `φ` is degreewise a morphism of
sheaves of modules, so they would go through for a bare `Hom`.

**The dependent laws.** `smul_mul` and `smul_one` are stated with `HEq` upstream, because the
degrees `(n + i) + j` and `n + (i + j)` are only propositionally equal. Neither needs
`Stacks.degCast` here: the restricted action is literally the old action precomposed with `φ`, so
after rewriting by `φ.map_mul` respectively `φ.map_one` — both equalities between sections of a
*fixed* sheaf, hence non-dependent — the goal is the corresponding law of the original module on
the nose.

## References

* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
* [Stacks Project, Tag 0FQZ](https://stacks.math.columbia.edu/tag/0FQZ)
-/

@[expose] public section

open CategoryTheory

universe t a m v u

namespace SheafOfModules.GradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A B : GradedAlgebra.{t, a} R}

/-! ### The degreewise components of a homomorphism, as additive maps -/

/-- The degree-`i` component of a unital homomorphism of graded algebra sheaves, read as an
additive map on the sections over `U`. -/
def unitalHomAdd (φ : GradedAlgebra.UnitalHom A B) (i : ℤ) (U : Cᵒᵖ) :
    (A.piece i).val.obj U →+ (B.piece i).val.obj U :=
  ((φ.app i).val.app U).hom.toAddMonoidHom

/-- `unitalHomAdd φ i U` sends a section `y` to `(φ.app i).val.app U y`. -/
@[simp] theorem unitalHomAdd_apply (φ : GradedAlgebra.UnitalHom A B) (i : ℤ) (U : Cᵒᵖ)
    (y : (A.piece i).val.obj U) : unitalHomAdd φ i U y = (φ.app i).val.app U y := rfl

/-! ### Restriction of scalars on objects -/

/-- **Restriction of scalars for graded modules.** A right graded `B`-module becomes a right
graded `A`-module along a unital homomorphism `φ : A ⟶ B` of graded algebra sheaves: a
homogeneous local section `a` of `A` acts the way `φ a` acts.

The homogeneous pieces are unchanged — they are the very same sheaves of modules — so every
statement about the pieces of `M`, cohomological or otherwise, is a statement about the pieces of
`M.restrictScalars φ`. -/
@[ega "II 2.8.6" "more general"]
def restrictScalars (φ : GradedAlgebra.UnitalHom A B) (M : GradedModule.{t, a, m} B) :
    GradedModule.{t, a, m} A where
  piece := M.piece
  smul n i U :=
    { toFun := fun x => (M.smul n i U x).comp (unitalHomAdd φ i U)
      map_zero' := by rw [map_zero]; exact AddMonoidHom.zero_comp _
      map_add' := fun x x' => by rw [map_add]; exact AddMonoidHom.add_comp _ _ _ }
  smul_smul_left n i U r x y := by
    change M.smul n i U (r • x) _ = r • M.smul n i U x _
    rw [M.smul_smul_left]
  smul_smul_right n i U r x y := by
    change M.smul n i U x ((φ.app i).val.app U (r • y)) = r • M.smul n i U x _
    rw [map_smul, M.smul_smul_right]
    rfl
  smul_naturality n i U V f x y := by
    change (M.piece (n + i)).val.map f (M.smul n i U x ((φ.app i).val.app U y)) =
      M.smul n i V ((M.piece n).val.map f x) ((φ.app i).val.app V ((A.piece i).val.map f y))
    rw [M.smul_naturality, PresheafOfModules.naturality_apply (φ.app i).val f y]
  smul_mul n i j U x y z := by
    change HEq (M.smul (n + i) j U (M.smul n i U x ((φ.app i).val.app U y))
        ((φ.app j).val.app U z))
      (M.smul n (i + j) U x ((φ.app (i + j)).val.app U ((A.mul i j).app U y z)))
    rw [φ.map_mul]
    exact M.smul_mul n i j U x _ _
  smul_one n U x := by
    change HEq (M.smul n 0 U x ((φ.app 0).val.app U (A.one.eval U))) x
    rw [φ.map_one]
    exact M.smul_one n U x

/-- The degree-`n` piece of `M.restrictScalars φ` is the degree-`n` piece of `M`. -/
@[simp] theorem restrictScalars_piece (φ : GradedAlgebra.UnitalHom A B)
    (M : GradedModule.{t, a, m} B) (n : ℤ) : (M.restrictScalars φ).piece n = M.piece n := rfl

/-- A section `y` of `A` acts on `M.restrictScalars φ` as `φ y` acts on `M`. -/
@[simp] theorem restrictScalars_smul (φ : GradedAlgebra.UnitalHom A B)
    (M : GradedModule.{t, a, m} B) (n i : ℤ) (U : Cᵒᵖ) (x : (M.piece n).val.obj U)
    (y : (A.piece i).val.obj U) :
    (M.restrictScalars φ).smul n i U x y = M.smul n i U x ((φ.app i).val.app U y) := rfl

/-! ### Restriction of scalars on morphisms -/

/-- A homomorphism of graded `B`-modules is a homomorphism of the restricted graded
`A`-modules, with the same degreewise components. -/
def restrictScalarsMap (φ : GradedAlgebra.UnitalHom A B) {M N : GradedModule.{t, a, m} B}
    (f : M ⟶ N) : M.restrictScalars φ ⟶ N.restrictScalars φ where
  app n := f.app n
  map_smul n i U x y := f.map_smul n i U x ((φ.app i).val.app U y)

/-- The degree-`n` component of `restrictScalarsMap φ f` is the degree-`n` component of `f`. -/
@[simp] theorem restrictScalarsMap_app (φ : GradedAlgebra.UnitalHom A B)
    {M N : GradedModule.{t, a, m} B} (f : M ⟶ N) (n : ℤ) :
    (restrictScalarsMap φ f).app n = f.app n := rfl

/-- **Restriction of scalars as a functor** `Mod(B) ⥤ Mod(A)`. -/
@[ega "II 2.8.6" "more general"]
def restrictScalarsFunctor (φ : GradedAlgebra.UnitalHom A B) :
    GradedModule.{t, a, m} B ⥤ GradedModule.{t, a, m} A where
  obj M := M.restrictScalars φ
  map f := restrictScalarsMap φ f
  map_id _ := Hom.ext fun _ => rfl
  map_comp _ _ := Hom.ext fun _ => rfl

/-- The functor `restrictScalarsFunctor φ` sends `M` to `M.restrictScalars φ`. -/
@[simp] theorem restrictScalarsFunctor_obj (φ : GradedAlgebra.UnitalHom A B)
    (M : GradedModule.{t, a, m} B) :
    (restrictScalarsFunctor φ).obj M = M.restrictScalars φ := rfl

/-- The degree-`n` component of the image of `f` under `restrictScalarsFunctor φ` is the degree-`n`
component of `f`. -/
@[simp] theorem restrictScalarsFunctor_map_app (φ : GradedAlgebra.UnitalHom A B)
    {M N : GradedModule.{t, a, m} B} (f : M ⟶ N) (n : ℤ) :
    ((restrictScalarsFunctor φ).map f).app n = f.app n := rfl

/-- Restriction of scalars does not change the degreewise morphisms, so it is faithful. -/
theorem restrictScalarsFunctor_faithful (φ : GradedAlgebra.UnitalHom A B) :
    (restrictScalarsFunctor.{t, a, m} φ).Faithful :=
  ⟨fun {_ _ _ _} h => Hom.ext fun n =>
    congrArg (fun g : _ ⟶ _ => Hom.app g n) h⟩

/-- Restriction of scalars is additive on homomorphisms. -/
theorem restrictScalarsFunctor_additive (φ : GradedAlgebra.UnitalHom A B) :
    (restrictScalarsFunctor.{t, a, m} φ).Additive :=
  ⟨Hom.ext fun _ => rfl⟩

end SheafOfModules.GradedModule

end
