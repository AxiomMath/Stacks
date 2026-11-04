module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Algebras
public import StacksCore.Tactic.StacksAttribute

/-!
# Homogeneous components of graded modules, and colimits

Let `R` be a sheaf of rings on a site and let `A` be a sheaf of `ℤ`-graded `R`-algebras,
i.e. a family `A.piece : ℤ → SheafOfModules R` with an `R`-bilinear, restriction-compatible
multiplication `A.piece i × A.piece j → A.piece (i + j)` and a global unit in degree `0`.
A right graded `A`-module is a family `M.piece : ℤ → SheafOfModules R` with a compatible
right action, and taking the component in a fixed degree `n` is a functor
`pieceFunctor A n : GradedModule A ⥤ SheafOfModules R`.

This file provides the graded-module category, its preadditive structure, the functor
`pieceFunctor`, and the reduction of "`pieceFunctor` preserves all colimits" to the two
degreewise statements it is assembled from: that direct sums of graded modules are formed
degreewise, and that cokernels of graded modules are formed degreewise.

## Main definitions

* `SheafOfModules.BilinearMap` is an `R`-bilinear map of sheaves of modules, presented on
  sections and compatible with restriction. It is an abbreviation for `Stacks.BilinearMap`
  applied to the underlying presheaves of modules, not a second notion.
* `SheafOfModules.GradedAlgebra` is a sheaf of `ℤ`-graded algebras over a sheaf of rings.
* `SheafOfModules.GradedModule` is a right graded module over such an algebra, and
  `SheafOfModules.GradedModule.Hom` is a homomorphism of such; these form a category.
* `SheafOfModules.GradedModule.pieceFunctor A n` takes a graded module to its degree-`n`
  component.

## Main results

* `SheafOfModules.GradedModule.pieceFunctor_preservesColimitsOfSize`: if graded modules have
  coproducts and cokernels, and `pieceFunctor A n` preserves coproducts and cokernels, then
  `pieceFunctor A n` preserves all colimits of the corresponding size. This is the reduction
  of Tag 0FR0's statement that `M ↦ Mⁿ` commutes with colimits to the two degreewise facts
  that the tag's own proof uses.
* `SheafOfModules.GradedModule.pieceFunctor_preservesCoequalizers` is its coequalizer half,
  and `SheafOfModules.GradedModule.hasBinaryCoproducts` shrinks direct sums indexed by any
  one universe to binary ones.

## Implementation notes

The base is an arbitrary sheaf of rings `R` on an arbitrary site rather than the structure
sheaf of a ringed site, and the universes of the site, the ring, the algebra components and
the module components are independent.

The site and universe generality is genuine. The `RingCat` generality is **not**, and should
not be described as "the ringed-site case with commutativity forgotten". A ringed site carries
a structure sheaf of *commutative* rings — Tag 0FQW's `O` is a `Sheaf J CommRingCat` — and
dropping commutativity here buys nothing, because `BilinearMap`'s two separate scalar laws
already force the image of `app` to be annihilated by every commutator of `R`: computing
`app U (r • x) (s • y)` in the two orders yields both `(r * s) • app U x y` and
`(s * r) • app U x y`. So the notion below is the standard commutative one, stated over an `R`
whose commutators are additionally required to act trivially on the targets; it is faithful
exactly in the commutative case, which is the only case used. See the `Implementation notes`
of `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/Algebras.lean` for the full argument.

The action on a graded module is specified on sections, as an additive map in each variable
together with `R`-linearity in each variable and compatibility with restriction, because the
target `M.piece (n + m)` varies with the degrees. For the same reason associativity and the
unit law are stated with `HEq`: the indices of their two sides, `(n + i) + j` and `n + (i + j)`,
are propositionally but not definitionally equal.

`pieceFunctor_preservesColimitsOfSize` is stated with the degreewise coproduct and cokernel
facts as hypotheses, and with a free size universe. It is **not** tagged `@[stacks 0FR0]`:
the tag's own claim is unconditional, and discharging the cokernel hypothesis is a separate
piece of work — it needs the degreewise cokernel of a graded module to carry a graded-module
structure, which in a sheaf setting is not a sectionwise quotient. The coproduct hypothesis
is the content of the direct-sums part of the same tag.

## References

* [Stacks Project, Tag 0FR0](https://stacks.math.columbia.edu/tag/0FR0)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
* [Stacks Project, Tag 0FQZ](https://stacks.math.columbia.edu/tag/0FQZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w t a m p v u

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

/-- An `R`-bilinear map of sheaves of modules, presented on sections.

This is not a separate notion: it is `Stacks.BilinearMap` applied to the underlying presheaves
of modules. Bilinearity of a map of sheaves constrains only sections and restriction maps, so
the sheaf conditions on `M`, `N` and `P` play no part in it and the presheaf structure is
field-for-field the right one. The abbreviation is kept because the graded-algebra and
graded-module structures below are indexed by sheaves of modules, and writing `.val` at every
use would be noise. -/
abbrev BilinearMap (M : SheafOfModules.{m} R) (N : SheafOfModules.{a} R)
    (P : SheafOfModules.{p} R) :=
  Stacks.BilinearMap M.val N.val P.val

/-- The zero bilinear map of sheaves of modules: the zero map on sections over every object of
the site. It is the multiplication a graded algebra carries in a degree where one of the two
factors is a zero object, so it is stated here, at an arbitrary sheaf of rings on an arbitrary
site, rather than at any one of its uses. -/
def zeroBilinear (M : SheafOfModules.{m} R) (N : SheafOfModules.{a} R)
    (P : SheafOfModules.{p} R) : BilinearMap M N P where
  app _ := 0
  map_smul_left _ r _ _ := (smul_zero r).symm
  map_smul_right _ r _ _ := (smul_zero r).symm
  naturality _ _ _ := map_zero _

/-- The zero bilinear map vanishes on every pair of sections. -/
@[simp] theorem zeroBilinear_app (M : SheafOfModules.{m} R) (N : SheafOfModules.{a} R)
    (P : SheafOfModules.{p} R) (U : Cᵒᵖ) (x : M.val.obj U) (y : N.val.obj U) :
    (zeroBilinear M N P).app U x y = 0 := rfl

/-- A sheaf of `ℤ`-graded algebras over a sheaf of rings. -/
@[stacks 0FQW "sheaves of graded algebras, over a sheaf of rings on an arbitrary site"]
structure GradedAlgebra (R : Sheaf J RingCat.{t}) where
  /-- The sheaf of modules in each degree. -/
  piece : ℤ → SheafOfModules.{a} R
  /-- Multiplication of homogeneous local sections. -/
  mul (i j : ℤ) : BilinearMap (piece i) (piece j) (piece (i + j))
  /-- The global unit in degree zero. -/
  one : (piece 0).sections
  /-- Associativity of multiplication. -/
  mul_assoc (i j k : ℤ) (U : Cᵒᵖ) (x : (piece i).val.obj U) (y : (piece j).val.obj U)
      (z : (piece k).val.obj U) :
    HEq ((mul (i + j) k).app U ((mul i j).app U x y) z)
      ((mul i (j + k)).app U x ((mul j k).app U y z))
  /-- The global unit is a left identity. -/
  one_mul (i : ℤ) (U : Cᵒᵖ) (x : (piece i).val.obj U) :
    HEq ((mul 0 i).app U (one.eval U) x) x
  /-- The global unit is a right identity. -/
  mul_one (i : ℤ) (U : Cᵒᵖ) (x : (piece i).val.obj U) :
    HEq ((mul i 0).app U x (one.eval U)) x

/-- A right graded module over a sheaf of graded algebras. -/
@[stacks 0FQZ "right graded modules, over a sheaf of rings on an arbitrary site"]
structure GradedModule (A : GradedAlgebra.{t, a} R) where
  /-- The sheaf of modules in each degree. -/
  piece : ℤ → SheafOfModules.{m} R
  /-- Multiplication of a homogeneous module section by a homogeneous algebra section. -/
  smul (n i : ℤ) (U : Cᵒᵖ) :
    (piece n).val.obj U →+ (A.piece i).val.obj U →+ (piece (n + i)).val.obj U
  /-- The action is linear over the sheaf of rings in the module variable. -/
  smul_smul_left (n i : ℤ) (U : Cᵒᵖ) (r : R.obj.obj U) (x : (piece n).val.obj U)
      (y : (A.piece i).val.obj U) :
    smul n i U (r • x) y = r • smul n i U x y
  /-- The action is linear over the sheaf of rings in the algebra variable. -/
  smul_smul_right (n i : ℤ) (U : Cᵒᵖ) (r : R.obj.obj U) (x : (piece n).val.obj U)
      (y : (A.piece i).val.obj U) :
    smul n i U x (r • y) = r • smul n i U x y
  /-- The action commutes with restriction. -/
  smul_naturality (n i : ℤ) {U V : Cᵒᵖ} (f : U ⟶ V) (x : (piece n).val.obj U)
      (y : (A.piece i).val.obj U) :
    (piece (n + i)).val.map f (smul n i U x y) =
      smul n i V ((piece n).val.map f x) ((A.piece i).val.map f y)
  /-- The module action is associative. -/
  smul_mul (n i j : ℤ) (U : Cᵒᵖ) (x : (piece n).val.obj U) (y : (A.piece i).val.obj U)
      (z : (A.piece j).val.obj U) :
    HEq (smul (n + i) j U (smul n i U x y) z)
      (smul n (i + j) U x ((A.mul i j).app U y z))
  /-- The degree-zero unit of the algebra acts as the identity. -/
  smul_one (n : ℤ) (U : Cᵒᵖ) (x : (piece n).val.obj U) :
    HEq (smul n 0 U x (A.one.eval U)) x

namespace GradedModule

variable {A : GradedAlgebra.{t, a} R}

/-- A homomorphism of right graded modules over a sheaf of graded algebras. -/
@[stacks 0FQZ "homomorphisms of right graded modules"]
structure Hom (M N : GradedModule.{t, a, m} A) where
  /-- The morphism of sheaves of modules in each degree. -/
  app (n : ℤ) : M.piece n ⟶ N.piece n
  /-- The degreewise maps commute with the right action. -/
  map_smul (n i : ℤ) (U : Cᵒᵖ) (x : (M.piece n).val.obj U) (y : (A.piece i).val.obj U) :
    (app (n + i)).val.app U (M.smul n i U x y) = N.smul n i U ((app n).val.app U x) y

/-- Two graded-module homomorphisms are equal if all their homogeneous components are. -/
@[ext]
theorem Hom.ext {M N : GradedModule.{t, a, m} A} {f g : Hom M N} (h : ∀ n, f.app n = g.app n) :
    f = g := by
  cases f
  cases g
  congr
  funext n
  exact h n

/-- The identity homomorphism of a graded module. -/
def Hom.id (M : GradedModule.{t, a, m} A) : Hom M M where
  app _ := 𝟙 _
  map_smul _ _ _ _ _ := rfl

/-- Composition of homomorphisms of graded modules. -/
def Hom.comp {M N P : GradedModule.{t, a, m} A} (f : Hom M N) (g : Hom N P) : Hom M P where
  app n := f.app n ≫ g.app n
  map_smul n i U x y := by
    change (g.app (n + i)).val.app U ((f.app (n + i)).val.app U (M.smul n i U x y)) = _
    rw [f.map_smul, g.map_smul]
    rfl

/-- Each component of the identity homomorphism is the identity. -/
@[simp]
theorem Hom.id_app (M : GradedModule.{t, a, m} A) (n : ℤ) : (Hom.id M).app n = 𝟙 _ := rfl

/-- Each component of a composite is the composite of the components. -/
@[simp]
theorem Hom.comp_app {M N P : GradedModule.{t, a, m} A} (f : Hom M N) (g : Hom N P) (n : ℤ) :
    (f.comp g).app n = f.app n ≫ g.app n := rfl

/-- The category of right graded modules over a fixed sheaf of graded algebras. -/
@[stacks 0FQZ "the category of right graded modules"]
instance : Category (GradedModule.{t, a, m} A) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp f := by ext n; simp
  comp_id f := by ext n; simp
  assoc f g h := by ext n; simp

section Preadditive

/-- The zero homomorphism of graded modules, zero in every degree. -/
instance homZero (M N : GradedModule.{t, a, m} A) : Zero (Hom M N) :=
  ⟨{ app := fun _ => 0
     map_smul := by
       intro n i U x y
       change 0 = (N.smul n i U 0) y
       rw [AddMonoidHom.map_zero, AddMonoidHom.zero_apply] }⟩

/-- The sum of two graded-module homomorphisms, taken degreewise. -/
instance homAdd (M N : GradedModule.{t, a, m} A) : Add (Hom M N) :=
  ⟨fun f g =>
    { app := fun n => f.app n + g.app n
      map_smul := by
        intro n i U x y
        change ((f.app (n + i)).val.app U (M.smul n i U x y) +
          (g.app (n + i)).val.app U (M.smul n i U x y)) = _
        rw [f.map_smul, g.map_smul]
        change _ = (N.smul n i U) ((f.app n).val.app U x + (g.app n).val.app U x) y
        exact (congrArg (fun q : _ →+ _ => q y)
          ((N.smul n i U).map_add ((f.app n).val.app U x) ((g.app n).val.app U x))).symm }⟩

/-- The negation of a graded-module homomorphism, taken degreewise. -/
instance homNeg (M N : GradedModule.{t, a, m} A) : Neg (Hom M N) :=
  ⟨fun f =>
    { app := fun n => -f.app n
      map_smul := by
        intro n i U x y
        change -((f.app (n + i)).val.app U (M.smul n i U x y)) = _
        rw [f.map_smul]
        change -((N.smul n i U) ((f.app n).val.app U x) y) =
          (N.smul n i U) (-((f.app n).val.app U x)) y
        exact (congrArg (fun q : _ →+ _ => q y)
          ((N.smul n i U).map_neg ((f.app n).val.app U x))).symm }⟩

/-- Homomorphisms between two graded modules form an abelian group under degreewise addition. -/
instance homAddCommGroup (M N : GradedModule.{t, a, m} A) : AddCommGroup (Hom M N) where
  add := (· + ·)
  zero := 0
  neg := Neg.neg
  sub f g := f + -g
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc f g h := Hom.ext fun _ => add_assoc _ _ _
  zero_add f := Hom.ext fun _ => zero_add _
  add_zero f := Hom.ext fun _ => add_zero _
  add_comm f g := Hom.ext fun _ => add_comm _ _
  neg_add_cancel f := Hom.ext fun _ => neg_add_cancel _
  sub_eq_add_neg f g := rfl

/-- The category of right graded modules is preadditive. -/
instance : Preadditive (GradedModule.{t, a, m} A) where
  homGroup M N := homAddCommGroup M N
  add_comp _ _ _ _ _ _ := Hom.ext fun _ => Preadditive.add_comp _ _ _ _ _ _
  comp_add _ _ _ _ _ _ := Hom.ext fun _ => Preadditive.comp_add _ _ _ _ _ _

end Preadditive

/-- Evaluation of a graded module at one homogeneous degree. -/
def pieceFunctor (A : GradedAlgebra.{t, a} R) (n : ℤ) :
    GradedModule.{t, a, m} A ⥤ SheafOfModules.{m} R where
  obj M := M.piece n
  map f := f.app n
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The degree-`n` component functor sends a graded module to its degree-`n` piece. -/
@[simp]
theorem pieceFunctor_obj (A : GradedAlgebra.{t, a} R) (n : ℤ) (M : GradedModule.{t, a, m} A) :
    (pieceFunctor A n).obj M = M.piece n := rfl

/-- The degree-`n` component functor sends a homomorphism to its degree-`n` component. -/
@[simp]
theorem pieceFunctor_map (A : GradedAlgebra.{t, a} R) (n : ℤ)
    {M N : GradedModule.{t, a, m} A} (f : M ⟶ N) : (pieceFunctor A n).map f = f.app n := rfl

/-- Taking a fixed homogeneous component preserves zero morphisms. -/
instance pieceFunctor_preservesZeroMorphisms (A : GradedAlgebra.{t, a} R) (n : ℤ) :
    (pieceFunctor.{t, a, m} A n).PreservesZeroMorphisms where
  map_zero M N := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    ext x
    rfl

/-- Graded modules have binary coproducts as soon as they have coproducts indexed by any one
universe, since `WalkingPair` is small. -/
theorem hasBinaryCoproducts (A : GradedAlgebra.{t, a} R)
    [HasCoproducts.{w} (GradedModule.{t, a, m} A)] :
    HasBinaryCoproducts (GradedModule.{t, a, m} A) :=
  hasColimitsOfShape_of_equivalence
    (Discrete.equivalence (Equiv.ulift.{w, 0} (α := WalkingPair)))

/-- Taking a fixed homogeneous component preserves coequalizers as soon as it preserves
cokernels. Graded modules are preadditive, so a coequalizer there is a cokernel. -/
theorem pieceFunctor_preservesCoequalizers (A : GradedAlgebra.{t, a} R) (n : ℤ)
    [HasCoproducts.{w} (GradedModule.{t, a, m} A)] [HasCokernels (GradedModule.{t, a, m} A)]
    [∀ {M N : GradedModule.{t, a, m} A} (f : M ⟶ N),
      PreservesColimit (parallelPair f 0) (pieceFunctor.{t, a, m} A n)] :
    PreservesColimitsOfShape WalkingParallelPair (pieceFunctor.{t, a, m} A n) := by
  have := hasBinaryCoproducts.{w} A
  have : HasBinaryBiproducts (GradedModule.{t, a, m} A) :=
    HasBinaryBiproducts.of_hasBinaryCoproducts
  exact (pieceFunctor.{t, a, m} A n).preservesCoequalizers_of_preservesCokernels

/-- Taking a fixed homogeneous component commutes with all colimits, given the two degreewise
facts Tag 0FR0's own proof is assembled from: that graded modules have direct sums and
cokernels, and that taking the component preserves both.

This is the reduction of the tag's claim that `M ↦ Mⁿ` commutes with colimits. It is stated
with those facts as hypotheses, so it is not the tag's unconditional claim. -/
theorem pieceFunctor_preservesColimitsOfSize (A : GradedAlgebra.{t, a} R) (n : ℤ)
    [HasCoproducts.{w} (GradedModule.{t, a, m} A)] [HasCokernels (GradedModule.{t, a, m} A)]
    [∀ ι : Type w, PreservesColimitsOfShape (Discrete ι) (pieceFunctor.{t, a, m} A n)]
    [∀ {M N : GradedModule.{t, a, m} A} (f : M ⟶ N),
      PreservesColimit (parallelPair f 0) (pieceFunctor.{t, a, m} A n)] :
    PreservesColimitsOfSize.{w, w} (pieceFunctor.{t, a, m} A n) := by
  have : HasCoequalizers (GradedModule.{t, a, m} A) :=
    Preadditive.hasCoequalizers_of_hasCokernels
  have := pieceFunctor_preservesCoequalizers.{w} A n
  exact preservesColimits_of_preservesCoequalizers_and_coproducts (pieceFunctor.{t, a, m} A n)

end GradedModule

end SheafOfModules
