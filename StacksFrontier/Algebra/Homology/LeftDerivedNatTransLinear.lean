module

public import Mathlib.CategoryTheory.Abelian.LeftDerived
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.Algebra.Homology.Linear
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DerivedFunctorAdditive

/-!
# Passing to left derived functors is linear in the natural transformation

Mathlib's `CategoryTheory.NatTrans.leftDerived` turns a natural transformation `α : F ⟶ G`
between additive functors into one `F.leftDerived n ⟶ G.leftDerived n`, and records that this
assignment preserves identities (`CategoryTheory.NatTrans.leftDerived_id`) and composition
(`CategoryTheory.NatTrans.leftDerived_comp`). It records nothing about the *additive* structure
of the hom-groups it connects. This file supplies that: the assignment is additive, and
`R`-linear as soon as the target category is `R`-linear.

The consequence that is actually used is
`CategoryTheory.NatTrans.leftDerived_smul_id`: a scalar multiple of an identity is sent to the
same scalar multiple of an identity, so a scalar acting on `LⁿF(X)` through the derived functor
construction is the scalar acting through the ambient `R`-linear structure of the target. For
`Tor` that is the comparison between functoriality of `Tor_n^R(·, M)` at multiplication by a
scalar and the module structure the group carries anyway.

## Main results

* `CategoryTheory.NatTrans.mapHomologicalComplex_add`,
  `CategoryTheory.NatTrans.mapHomologicalComplex_smul`,
  `CategoryTheory.NatTrans.mapHomotopyCategory_add` and
  `CategoryTheory.NatTrans.mapHomotopyCategory_smul`: the degreewise and the
  homotopy-category versions of a natural transformation are additive, and `R`-linear, in it.
* `CategoryTheory.NatTrans.leftDerived_add` and `CategoryTheory.NatTrans.leftDerived_smul`:
  **passing to left derived functors is additive, and `R`-linear, in the natural
  transformation.**
* `CategoryTheory.NatTrans.leftDerived_smul_id`: **`NatTrans.leftDerived (r • 𝟙 F) n`
  is `r • 𝟙 (F.leftDerived n)`.**
* `CategoryTheory.NatTrans.leftDerivedLinearMap`: the same statement bundled as an `R`-linear
  map `(F ⟶ G) →ₗ[R] (F.leftDerived n ⟶ G.leftDerived n)`.

## Implementation notes

`CategoryTheory.Functor.leftDerived` is the composite of the projective-resolution functor into
the homotopy category, the degreewise image under the functor, and the degree-`n` homology of a
complex in the homotopy category. A natural transformation enters that composite only in the
middle factor, so no property of taking projective resolutions is needed — which is why the
source category is not required to be `R`-linear here. Only the last factor has to be linear,
and that is `HomotopyCategory.linear_homologyFunctor`.

Note the contrast with `CategoryTheory.Functor.linear_rightDerived`, which is linearity of a
*fixed* derived functor in the *morphism* of the source category; that statement does need the
resolution functor to be linear, hence an `R`-linear source category. The two are independent.
-/

@[expose] public noncomputable section

universe v u

namespace CategoryTheory

/-! ### A scalar multiple of an identity under a functor -/

section MapSmulId

variable {R : Type*} [Semiring R] {C D : Type*} [Category* C] [Category* D] [Preadditive C]
  [CategoryTheory.Linear R C]

/-- **A scalar multiple of an identity commutes with every morphism, and its image under any
functor still does.** Both sides are the image of `r • f`. -/
theorem Functor.map_smul_id_comp (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) (r : R) :
    F.map (r • 𝟙 X) ≫ F.map f = F.map f ≫ F.map (r • 𝟙 Y) := by
  rw [← F.map_comp, ← F.map_comp, CategoryTheory.Linear.smul_comp,
    CategoryTheory.Linear.comp_smul, Category.id_comp, Category.comp_id]

end MapSmulId

/-! ### The degreewise version of a natural transformation -/

section MapHomologicalComplex

variable {W₁ W₂ : Type*} [Category* W₁] [Category* W₂] [Preadditive W₁] [Preadditive W₂]
  {ι : Type*} (c : ComplexShape ι) {F G : W₁ ⥤ W₂}
  [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]

/-- **Applying a natural transformation degreewise to complexes is additive in it.** Both sides
act in each degree as the sum of the components. -/
@[simp]
theorem NatTrans.mapHomologicalComplex_add (α β : F ⟶ G) :
    NatTrans.mapHomologicalComplex (α + β) c =
      NatTrans.mapHomologicalComplex α c + NatTrans.mapHomologicalComplex β c := by
  ext K n
  rfl

/-- **Applying a natural transformation degreewise to complexes is `R`-linear in it.** Both
sides act in each degree as the scalar multiple of a component. -/
@[simp]
theorem NatTrans.mapHomologicalComplex_smul {R : Type*} [Semiring R] [Linear R W₂]
    (α : F ⟶ G) (r : R) :
    NatTrans.mapHomologicalComplex (r • α) c = r • NatTrans.mapHomologicalComplex α c := by
  ext K n
  rfl

end MapHomologicalComplex

/-! ### The homotopy-category version of a natural transformation -/

section MapHomotopyCategory

variable {V W : Type*} [Category* V] [Category* W] [Preadditive V] [Preadditive W]
  {ι : Type*} (c : ComplexShape ι) {F G : V ⥤ W} [F.Additive] [G.Additive]

/-- **The homotopy-category version of a natural transformation is additive in it.** The
quotient functor to the homotopy category is additive, so the sum passes through it. -/
@[simp]
theorem NatTrans.mapHomotopyCategory_add (α β : F ⟶ G) :
    NatTrans.mapHomotopyCategory (α + β) c =
      NatTrans.mapHomotopyCategory α c + NatTrans.mapHomotopyCategory β c := by
  ext K
  simp [NatTrans.mapHomotopyCategory]
  rfl

/-- **The homotopy-category version of a natural transformation is `R`-linear in it.** The
quotient functor to the homotopy category is `R`-linear, so the scalar passes through it. -/
@[simp]
theorem NatTrans.mapHomotopyCategory_smul {R : Type*} [Semiring R] [Linear R W]
    (α : F ⟶ G) (r : R) :
    NatTrans.mapHomotopyCategory (r • α) c = r • NatTrans.mapHomotopyCategory α c := by
  ext K
  simp [NatTrans.mapHomotopyCategory]
  rfl

end MapHomotopyCategory

/-! ### The left derived functor construction -/

section LeftDerived

variable {C : Type u} [Category.{v} C] {D : Type*} [Category* D]
  [Abelian C] [HasProjectiveResolutions C] [Abelian D]
  {F G : C ⥤ D} [F.Additive] [G.Additive]

/-- The homotopy-category-valued left derived functor of a natural transformation is
additive in it. -/
@[simp]
theorem NatTrans.leftDerivedToHomotopyCategory_add (α β : F ⟶ G) :
    NatTrans.leftDerivedToHomotopyCategory (α + β) =
      NatTrans.leftDerivedToHomotopyCategory α + NatTrans.leftDerivedToHomotopyCategory β := by
  ext X
  simp [NatTrans.leftDerivedToHomotopyCategory]
  rfl

/-- **Passing to left derived functors is additive in the natural transformation.** -/
@[simp]
theorem NatTrans.leftDerived_add (α β : F ⟶ G) (n : ℕ) :
    NatTrans.leftDerived (α + β) n =
      NatTrans.leftDerived α n + NatTrans.leftDerived β n := by
  ext X
  simp [NatTrans.leftDerived]
  rfl

variable {R : Type*} [Semiring R] [Linear R D]

/-- The homotopy-category-valued left derived functor of a natural transformation is
`R`-linear in it. -/
@[simp]
theorem NatTrans.leftDerivedToHomotopyCategory_smul (α : F ⟶ G) (r : R) :
    NatTrans.leftDerivedToHomotopyCategory (r • α) =
      r • NatTrans.leftDerivedToHomotopyCategory α := by
  ext X
  simp [NatTrans.leftDerivedToHomotopyCategory]
  rfl

/-- **Passing to left derived functors is `R`-linear in the natural transformation.** -/
@[simp]
theorem NatTrans.leftDerived_smul (α : F ⟶ G) (r : R) (n : ℕ) :
    NatTrans.leftDerived (r • α) n = r • NatTrans.leftDerived α n := by
  ext X
  simp [NatTrans.leftDerived]
  rfl

/-- **A scalar multiple of an identity derives to the same scalar multiple of an identity.**
This is the statement that the scalar action obtained through the left derived functor
construction agrees with the ambient `R`-linear structure of the target category. -/
@[simp]
theorem NatTrans.leftDerived_smul_id (F : C ⥤ D) [F.Additive] (r : R) (n : ℕ) :
    NatTrans.leftDerived (r • 𝟙 F) n = r • 𝟙 (F.leftDerived n) := by
  rw [NatTrans.leftDerived_smul, NatTrans.leftDerived_id]

/-- Passing to left derived functors, bundled as an `R`-linear map on hom-modules. -/
def NatTrans.leftDerivedLinearMap (F G : C ⥤ D) [F.Additive] [G.Additive] (n : ℕ) :
    (F ⟶ G) →ₗ[R] (F.leftDerived n ⟶ G.leftDerived n) where
  toFun α := NatTrans.leftDerived α n
  map_add' α β := NatTrans.leftDerived_add α β n
  map_smul' r α := NatTrans.leftDerived_smul α r n

/-- The linear map `NatTrans.leftDerivedLinearMap F G n` sends `α` to
`NatTrans.leftDerived α n`. -/
@[simp]
theorem NatTrans.leftDerivedLinearMap_apply (n : ℕ) (α : F ⟶ G) :
    NatTrans.leftDerivedLinearMap (R := R) F G n α = NatTrans.leftDerived α n :=
  rfl

end LeftDerived

end CategoryTheory

end
