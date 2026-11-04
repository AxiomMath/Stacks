module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LeftDifferentialGradedModule
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import StacksCore.Tactic.StacksAttribute

/-!
# Left graded modules over a sheaf of graded algebras

Let `R` be a sheaf of rings on a site and let `A` be a sheaf of `ℤ`-graded `R`-algebras. A left
graded `A`-module is a family of sheaves of `R`-modules indexed by `ℤ` together with a unital,
associative left action of the homogeneous local sections of `A`.

## Main definitions

* `SheafOfModules.LeftGradedModule` is a left graded module over a sheaf of graded algebras, and
  `SheafOfModules.LeftGradedModule.Hom` is a homomorphism of such; these form a category.
* `SheafOfModules.LeftGradedModule.ofDifferentialGraded` is the left graded module underlying a
  left differential graded module.
* `SheafOfModules.GradedModule.ofDifferentialGraded` is the right graded module underlying a
  right differential graded module, and `SheafOfModules.GradedModule.ofDifferentialGradedMap` the
  homomorphism underlying a morphism of such.
* `SheafOfModules.LeftGradedModule.ShortExact` is degreewise short exactness of a short complex
  of left graded modules.

## Implementation notes

The right-handed half of Tag 0FQZ — `SheafOfModules.GradedModule` — is in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedDegreeColimits.lean`. This file adds the
left-handed half, which the source defines in the same way with the algebra acting on the left.

Short exactness of a short complex of left graded modules is imposed degreewise. Kernels and
cokernels of graded modules are computed degreewise, so this is short exactness in the category
of left graded modules; stating it degreewise avoids presupposing an abelian structure on left
graded modules, which Tag 0FR0 supplies only for right graded modules.

The base is an arbitrary sheaf of rings on an arbitrary site, and the universes of the site, the
ring, the algebra components and the module components are independent.

## References

* [Stacks Project, Tag 0FQZ](https://stacks.math.columbia.edu/tag/0FQZ)
* [Stacks Project, Tag 0FRI](https://stacks.math.columbia.edu/tag/0FRI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe t a m v u

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

/-- A left graded module over a sheaf of graded algebras. -/
@[stacks 0FQZ "left graded modules, over a sheaf of rings on an arbitrary site"]
structure LeftGradedModule (A : GradedAlgebra.{t, a} R) where
  /-- The sheaf of modules in each degree. -/
  piece : ℤ → SheafOfModules.{m} R
  /-- Multiplication of a homogeneous module section by a homogeneous algebra section, with the
  algebra acting on the left. -/
  smul (i n : ℤ) (U : Cᵒᵖ) :
    (A.piece i).val.obj U →+ (piece n).val.obj U →+ (piece (i + n)).val.obj U
  /-- The action is linear over the sheaf of rings in the algebra variable. -/
  smul_smul_left (i n : ℤ) (U : Cᵒᵖ) (r : R.obj.obj U) (a : (A.piece i).val.obj U)
      (x : (piece n).val.obj U) :
    smul i n U (r • a) x = r • smul i n U a x
  /-- The action is linear over the sheaf of rings in the module variable. -/
  smul_smul_right (i n : ℤ) (U : Cᵒᵖ) (r : R.obj.obj U) (a : (A.piece i).val.obj U)
      (x : (piece n).val.obj U) :
    smul i n U a (r • x) = r • smul i n U a x
  /-- The action commutes with restriction. -/
  smul_naturality (i n : ℤ) {U V : Cᵒᵖ} (f : U ⟶ V) (a : (A.piece i).val.obj U)
      (x : (piece n).val.obj U) :
    (piece (i + n)).val.map f (smul i n U a x) =
      smul i n V ((A.piece i).val.map f a) ((piece n).val.map f x)
  /-- The module action is associative. -/
  mul_smul (i j n : ℤ) (U : Cᵒᵖ) (a : (A.piece i).val.obj U) (b : (A.piece j).val.obj U)
      (x : (piece n).val.obj U) :
    HEq (smul (i + j) n U ((A.mul i j).app U a b) x)
      (smul i (j + n) U a (smul j n U b x))
  /-- The degree-zero unit of the algebra acts as the identity. -/
  one_smul (n : ℤ) (U : Cᵒᵖ) (x : (piece n).val.obj U) :
    HEq (smul 0 n U (A.one.eval U) x) x

namespace LeftGradedModule

variable {A : GradedAlgebra.{t, a} R}

/-- A homomorphism of left graded modules over a sheaf of graded algebras. -/
@[stacks 0FQZ "homomorphisms of left graded modules"]
structure Hom (M N : LeftGradedModule.{t, a, m} A) where
  /-- The morphism of sheaves of modules in each degree. -/
  app (n : ℤ) : M.piece n ⟶ N.piece n
  /-- The degreewise maps commute with the left action. -/
  map_smul (i n : ℤ) (U : Cᵒᵖ) (a : (A.piece i).val.obj U) (x : (M.piece n).val.obj U) :
    (app (i + n)).val.app U (M.smul i n U a x) = N.smul i n U a ((app n).val.app U x)

/-- Two homomorphisms of left graded modules are equal if all their homogeneous components
are. -/
@[ext]
theorem Hom.ext {M N : LeftGradedModule.{t, a, m} A} {f g : Hom M N}
    (h : ∀ n, f.app n = g.app n) : f = g := by
  cases f
  cases g
  congr
  funext n
  exact h n

/-- The identity homomorphism of a left graded module. -/
def Hom.id (M : LeftGradedModule.{t, a, m} A) : Hom M M where
  app _ := 𝟙 _
  map_smul _ _ _ _ _ := rfl

/-- Composition of homomorphisms of left graded modules. -/
def Hom.comp {M N P : LeftGradedModule.{t, a, m} A} (f : Hom M N) (g : Hom N P) : Hom M P where
  app n := f.app n ≫ g.app n
  map_smul i n U a x := by
    change (g.app (i + n)).val.app U ((f.app (i + n)).val.app U (M.smul i n U a x)) = _
    rw [f.map_smul, g.map_smul]
    rfl

/-- Each homogeneous component of the identity homomorphism is the identity. -/
@[simp]
theorem Hom.id_app (M : LeftGradedModule.{t, a, m} A) (n : ℤ) : (Hom.id M).app n = 𝟙 _ := rfl

/-- Each homogeneous component of a composite is the composite of the components. -/
@[simp]
theorem Hom.comp_app {M N P : LeftGradedModule.{t, a, m} A} (f : Hom M N) (g : Hom N P)
    (n : ℤ) : (f.comp g).app n = f.app n ≫ g.app n := rfl

/-- The category of left graded modules over a fixed sheaf of graded algebras. -/
@[stacks 0FQZ "the category of left graded modules"]
instance instCategory : Category (LeftGradedModule.{t, a, m} A) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp f := by ext n; simp
  comp_id f := by ext n; simp
  assoc f g h := by ext n; simp

/-- Each homogeneous component of the identity morphism is the identity. -/
@[simp]
theorem id_app (M : LeftGradedModule.{t, a, m} A) (n : ℤ) : (𝟙 M : M ⟶ M).app n = 𝟙 _ := rfl

/-- Each homogeneous component of a composite morphism is the composite of the components. -/
@[simp]
theorem comp_app {M N P : LeftGradedModule.{t, a, m} A} (f : M ⟶ N) (g : N ⟶ P) (n : ℤ) :
    (f ≫ g).app n = f.app n ≫ g.app n := rfl

/-- The left graded module underlying a left differential graded module. -/
def ofDifferentialGraded {A : DifferentialGradedAlgebra.{t, a} R}
    (N : LeftDifferentialGradedModule.{t, a, m} A) :
    LeftGradedModule.{t, a, m} A.toGradedAlgebra where
  piece := N.complex.X
  smul i n U := (N.mul i n).app U
  smul_smul_left i n U r a x := (N.mul i n).map_smul_left U r a x
  smul_smul_right i n U r a x := (N.mul i n).map_smul_right U r a x
  smul_naturality i n _U _V f a x := (N.mul i n).naturality f a x
  mul_smul i j n U a b x := N.mul_assoc i j n U a b x
  one_smul n U x := N.one_mul n U x

/-- The piece of degree `n` of `ofDifferentialGraded N` is the term of degree `n` of the
underlying complex. -/
@[simp]
theorem ofDifferentialGraded_piece {A : DifferentialGradedAlgebra.{t, a} R}
    (N : LeftDifferentialGradedModule.{t, a, m} A) (n : ℤ) :
    (ofDifferentialGraded N).piece n = N.complex.X n := rfl

/-- The action on `ofDifferentialGraded N` is the multiplication of `N`. -/
@[simp]
theorem ofDifferentialGraded_smul {A : DifferentialGradedAlgebra.{t, a} R}
    (N : LeftDifferentialGradedModule.{t, a, m} A) (i n : ℤ) (U : Cᵒᵖ) :
    (ofDifferentialGraded N).smul i n U = (N.mul i n).app U := rfl

/-- The homomorphism of left graded modules underlying a morphism of left differential graded
modules. -/
def ofDifferentialGradedMap {A : DifferentialGradedAlgebra.{t, a} R}
    {N N' : LeftDifferentialGradedModule.{t, a, m} A} (f : N ⟶ N') :
    ofDifferentialGraded N ⟶ ofDifferentialGraded N' where
  app n := f.toHomologicalComplex.f n
  map_smul i n U a x := f.map_mul i n U a x

/-- A short complex of left graded modules is short exact when each of its homogeneous pieces is
a short exact sequence of sheaves of modules. -/
def ShortExact {N₁ N₂ N₃ : LeftGradedModule.{t, a, m} A} (f : N₁ ⟶ N₂) (g : N₂ ⟶ N₃)
    (hfg : ∀ n : ℤ, f.app n ≫ g.app n = 0) : Prop :=
  ∀ n : ℤ, (ShortComplex.mk (f.app n) (g.app n) (hfg n)).ShortExact

end LeftGradedModule

namespace GradedModule

/-- The right graded module underlying a right differential graded module. -/
def ofDifferentialGraded {A : DifferentialGradedAlgebra.{t, a} R}
    (M : DifferentialGradedModule.{t, a, m} A) :
    GradedModule.{t, a, m} A.toGradedAlgebra where
  piece := M.complex.X
  smul n i U := (M.mul n i).app U
  smul_smul_left n i U r x a := (M.mul n i).map_smul_left U r x a
  smul_smul_right n i U r x a := (M.mul n i).map_smul_right U r x a
  smul_naturality n i _U _V f x a := (M.mul n i).naturality f x a
  smul_mul n i j U x a b := M.mul_assoc n i j U x a b
  smul_one n U x := M.mul_one n U x

/-- The piece of degree `n` of `ofDifferentialGraded M` is the term of degree `n` of the
underlying complex. -/
@[simp]
theorem ofDifferentialGraded_piece {A : DifferentialGradedAlgebra.{t, a} R}
    (M : DifferentialGradedModule.{t, a, m} A) (n : ℤ) :
    (ofDifferentialGraded M).piece n = M.complex.X n := rfl

/-- The action on `ofDifferentialGraded M` is the multiplication of `M`. -/
@[simp]
theorem ofDifferentialGraded_smul {A : DifferentialGradedAlgebra.{t, a} R}
    (M : DifferentialGradedModule.{t, a, m} A) (n i : ℤ) (U : Cᵒᵖ) :
    (ofDifferentialGraded M).smul n i U = (M.mul n i).app U := rfl

/-- The homomorphism of right graded modules underlying a morphism of right differential graded
modules. -/
def ofDifferentialGradedMap {A : DifferentialGradedAlgebra.{t, a} R}
    {M M' : DifferentialGradedModule.{t, a, m} A} (f : M ⟶ M') :
    ofDifferentialGraded M ⟶ ofDifferentialGraded M' where
  app n := f.toHomologicalComplex.f n
  map_smul n i U x y := f.map_mul n i U x y

/-- The component of degree `n` of `ofDifferentialGradedMap f` is the component of degree `n`
of the underlying map of complexes. -/
@[simp]
theorem ofDifferentialGradedMap_app {A : DifferentialGradedAlgebra.{t, a} R}
    {M M' : DifferentialGradedModule.{t, a, m} A} (f : M ⟶ M') (n : ℤ) :
    (ofDifferentialGradedMap f).app n = f.toHomologicalComplex.f n := rfl

/-- `ofDifferentialGradedMap` sends the identity to the identity. -/
theorem ofDifferentialGradedMap_id {A : DifferentialGradedAlgebra.{t, a} R}
    (M : DifferentialGradedModule.{t, a, m} A) :
    ofDifferentialGradedMap (𝟙 M) = 𝟙 (ofDifferentialGraded M) :=
  Hom.ext fun _ ↦ rfl

/-- `ofDifferentialGradedMap` sends a composite to the composite. -/
theorem ofDifferentialGradedMap_comp {A : DifferentialGradedAlgebra.{t, a} R}
    {M M' M'' : DifferentialGradedModule.{t, a, m} A} (f : M ⟶ M') (g : M' ⟶ M'') :
    ofDifferentialGradedMap (f ≫ g) =
      ofDifferentialGradedMap f ≫ ofDifferentialGradedMap g :=
  Hom.ext fun _ ↦ rfl

end GradedModule

end SheafOfModules
