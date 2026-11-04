module

public import Mathlib.CategoryTheory.Abelian.Transfer
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedModuleAbelian
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedModuleDegreeLimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LeftGradedModule
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Left graded modules over a sheaf of graded algebras form an abelian category

Let `R` be a sheaf of rings on a site and let `A` be a sheaf of `ℤ`-graded `R`-algebras. The
left graded `A`-modules form an abelian category, with kernels, cokernels and finite direct sums
formed degreewise, and taking the homogeneous component of a fixed degree is exact.

A left graded `A`-module is the same thing as a right graded module over the opposite graded
algebra `Aᵒᵖ`, whose product of `a` and `b` is the product `b a` of `A`. This file constructs
`Aᵒᵖ` and that identification, as an equivalence of categories, and transports the abelian
structure of right graded modules (Tag 0FR0) along it. The preadditive structure is defined
directly, degreewise, so that the sum of two homomorphisms is the degreewise sum.

## Main definitions

* `SheafOfModules.GradedAlgebra.op`: the opposite of a sheaf of graded algebras.
* `SheafOfModules.LeftGradedModule.opRightEquivalence`: **left graded `A`-modules are right
  graded `Aᵒᵖ`-modules**, an equivalence of categories which is the identity on homogeneous
  pieces and on degreewise maps.
* `SheafOfModules.LeftGradedModule.pieceFunctor`: the homogeneous component of a fixed degree.

## Main results

* `SheafOfModules.LeftGradedModule.abelian`: **the category of left graded modules is
  abelian.**
* `SheafOfModules.LeftGradedModule.pieceFunctor_preservesFiniteLimits` and
  `SheafOfModules.LeftGradedModule.pieceFunctor_preservesFiniteColimits`: taking a homogeneous
  component is exact; kernels, cokernels and finite direct sums are formed degreewise.

## Implementation notes

The opposite algebra and the passage between left and right actions move a product from degree
`j + i` to degree `i + j`. That move is `SheafOfModules.LeftGradedModule.degTransport`, the
`eqToHom` between the two homogeneous pieces; being a morphism of sheaves of modules it is linear
and commutes with restriction for free, and it is heterogeneously equal to the identity, which is
how every associativity and unit law is checked.

## References

* [Stacks Project, Tag 0FQZ](https://stacks.math.columbia.edu/tag/0FQZ)
* [Stacks Project, Tag 0FR0](https://stacks.math.columbia.edu/tag/0FR0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe t a m v u

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

namespace LeftGradedModule

/-! ### Transport between homogeneous pieces of equal degree -/

/-- The identification of the homogeneous pieces of a family of sheaves of modules in two equal
degrees. -/
def degTransport {w : Type*} (X : w → SheafOfModules.{m} R) {i j : w} (h : i = j) :
    X i ⟶ X j :=
  eqToHom (congrArg X h)

/-- The transport between pieces of equal degree, on sections, as an additive map. -/
abbrev degTransportAdd {w : Type*} (X : w → SheafOfModules.{m} R) {i j : w} (h : i = j)
    (U : Cᵒᵖ) : (X i).val.obj U →+ (X j).val.obj U :=
  ((degTransport X h).val.app U).hom.toAddMonoidHom

/-- The transport between pieces of equal degree is heterogeneously equal to the identity on
sections. -/
theorem degTransport_heq {w : Type*} (X : w → SheafOfModules.{m} R) {i j : w} (h : i = j)
    (U : Cᵒᵖ) (x : (X i).val.obj U) : HEq ((degTransport X h).val.app U x) x := by
  subst h
  rfl

/-- A degreewise family of morphisms commutes with the transport between pieces of equal
degree. -/
theorem app_degTransport {w : Type*} {X Y : w → SheafOfModules.{m} R} (φ : ∀ k, X k ⟶ Y k)
    {i j : w} (h : i = j) (U : Cᵒᵖ) (x : (X i).val.obj U) :
    (φ j).val.app U ((degTransport X h).val.app U x)
      = (degTransport Y h).val.app U ((φ i).val.app U x) := by
  subst h
  rfl

/-- The transport between pieces of equal degree commutes with the action of `R`. -/
theorem degTransport_smul {w : Type*} (X : w → SheafOfModules.{m} R) {i j : w} (h : i = j)
    (U : Cᵒᵖ) (r : R.obj.obj U) (x : (X i).val.obj U) :
    (degTransport X h).val.app U (r • x) = r • (degTransport X h).val.app U x := by
  subst h
  rfl

/-- Transporting from degree `i` to degree `j` and back to degree `i` is the identity. -/
theorem degTransport_degTransport {w : Type*} (X : w → SheafOfModules.{m} R) {i j : w}
    (h : i = j) (h' : j = i) (U : Cᵒᵖ) (x : (X i).val.obj U) :
    (degTransport X h').val.app U ((degTransport X h).val.app U x) = x := by
  subst h
  rfl

end LeftGradedModule

open LeftGradedModule

/-! ### The opposite graded algebra -/

namespace GradedAlgebra

variable (A : GradedAlgebra.{t, a} R)

/-- A product of `A` is a congruence for heterogeneous equality in its second argument along an
equality of its degree. -/
theorem mul_heq_right (i : ℤ) {j j' : ℤ} (h : j = j') (U : Cᵒᵖ) (x : (A.piece i).val.obj U)
    {y : (A.piece j).val.obj U} {y' : (A.piece j').val.obj U} (hy : HEq y y') :
    HEq ((A.mul i j).app U x y) ((A.mul i j').app U x y') := by
  subst h
  cases eq_of_heq hy
  rfl

/-- A product of `A` is a congruence for heterogeneous equality in its first argument along an
equality of its degree. -/
theorem mul_heq_left {i i' : ℤ} (h : i = i') (j : ℤ) (U : Cᵒᵖ) {x : (A.piece i).val.obj U}
    {x' : (A.piece i').val.obj U} (hx : HEq x x') (y : (A.piece j).val.obj U) :
    HEq ((A.mul i j).app U x y) ((A.mul i' j).app U x' y) := by
  subst h
  cases eq_of_heq hx
  rfl

/-- The multiplication of the opposite algebra: the product of `x` and `y` is the product `y x`
of `A`, moved from degree `j + i` to degree `i + j`. -/
def opMul (i j : ℤ) : BilinearMap (A.piece i) (A.piece j) (A.piece (i + j)) where
  app U := (AddMonoidHom.compHom (degTransportAdd A.piece (add_comm j i) U)).comp
    ((A.mul j i).app U).flip
  map_smul_left U r x y :=
    (congrArg (fun z => (degTransport A.piece (add_comm j i)).val.app U z)
      ((A.mul j i).map_smul_right U r y x)).trans (degTransport_smul _ _ _ r _)
  map_smul_right U r x y :=
    (congrArg (fun z => (degTransport A.piece (add_comm j i)).val.app U z)
      ((A.mul j i).map_smul_left U r y x)).trans (degTransport_smul _ _ _ r _)
  naturality {_ V} f x y :=
    (PresheafOfModules.naturality_apply (degTransport A.piece (add_comm j i)).val f _).symm.trans
      (congrArg (fun z => (degTransport A.piece (add_comm j i)).val.app V z)
        ((A.mul j i).naturality f y x))

/-- The product of `x` and `y` in the opposite algebra is the product `y x` of `A`, moved from
degree `j + i` to degree `i + j`. -/
theorem opMul_app (i j : ℤ) (U : Cᵒᵖ) (x : (A.piece i).val.obj U) (y : (A.piece j).val.obj U) :
    (A.opMul i j).app U x y =
      (degTransport A.piece (add_comm j i)).val.app U ((A.mul j i).app U y x) := rfl

/-- The product of `x` and `y` in the opposite algebra is heterogeneously equal to the product
`y x` of `A`. -/
theorem opMul_app_heq (i j : ℤ) (U : Cᵒᵖ) (x : (A.piece i).val.obj U)
    (y : (A.piece j).val.obj U) : HEq ((A.opMul i j).app U x y) ((A.mul j i).app U y x) :=
  degTransport_heq _ _ _ _

/-- **The opposite of a sheaf of graded algebras**: the same homogeneous pieces and unit, with
the product of homogeneous sections taken in the other order. -/
def op : GradedAlgebra.{t, a} R where
  piece := A.piece
  mul := A.opMul
  one := A.one
  mul_assoc i j k U x y z := by
    refine (A.opMul_app_heq (i + j) k U _ z).trans ?_
    refine (A.mul_heq_right k (add_comm i j) U z (A.opMul_app_heq i j U x y)).trans ?_
    refine (A.mul_assoc k j i U z y x).symm.trans ?_
    refine HEq.trans ?_ (A.opMul_app_heq i (j + k) U x _).symm
    exact A.mul_heq_left (add_comm k j) i U (A.opMul_app_heq j k U y z).symm x
  one_mul i U x := (A.opMul_app_heq 0 i U _ x).trans (A.mul_one i U x)
  mul_one i U x := (A.opMul_app_heq i 0 U x _).trans (A.one_mul i U x)

/-- The homogeneous pieces of the opposite algebra are those of `A`. -/
@[simp]
theorem op_piece : A.op.piece = A.piece := rfl

/-- The product of `x` and `y` in `A.op` is the product `y x` of `A`, moved from degree `j + i`
to degree `i + j`. -/
theorem op_mul_app (i j : ℤ) (U : Cᵒᵖ) (x : (A.piece i).val.obj U)
    (y : (A.piece j).val.obj U) :
    (A.op.mul i j).app U x y =
      (degTransport A.piece (add_comm j i)).val.app U ((A.mul j i).app U y x) := rfl

end GradedAlgebra

namespace GradedModule

variable {A : GradedAlgebra.{t, a} R} (N : GradedModule.{t, a, m} A)

/-- The right action of a right graded module is a congruence for heterogeneous equality of its
algebra argument along an equality of degrees. -/
theorem smul_heq_algebra' (n : ℤ) {i i' : ℤ} (h : i = i') (U : Cᵒᵖ) (x : (N.piece n).val.obj U)
    {a : (A.piece i).val.obj U} {a' : (A.piece i').val.obj U} (ha : HEq a a') :
    HEq (N.smul n i U x a) (N.smul n i' U x a') := by
  subst h
  cases eq_of_heq ha
  rfl

/-- The right action of a right graded module is a congruence for heterogeneous equality of its
module argument along an equality of degrees. -/
theorem smul_heq_module' {n n' : ℤ} (h : n = n') (i : ℤ) (U : Cᵒᵖ) {x : (N.piece n).val.obj U}
    {x' : (N.piece n').val.obj U} (hx : HEq x x') (a : (A.piece i).val.obj U) :
    HEq (N.smul n i U x a) (N.smul n' i U x' a) := by
  subst h
  cases eq_of_heq hx
  rfl

end GradedModule

namespace LeftGradedModule

variable {A : GradedAlgebra.{t, a} R}

/-! ### The preadditive structure -/

section Preadditive

/-- The zero homomorphism of left graded modules, zero in every degree. -/
instance homZero (M N : LeftGradedModule.{t, a, m} A) : Zero (M ⟶ N) :=
  ⟨{ app := fun _ => 0
     map_smul := by
       intro i n U a x
       change 0 = (N.smul i n U a) 0
       rw [AddMonoidHom.map_zero] }⟩

/-- The sum of two homomorphisms of left graded modules, taken degreewise. -/
instance homAdd (M N : LeftGradedModule.{t, a, m} A) : Add (M ⟶ N) :=
  ⟨fun f g =>
    { app := fun n => f.app n + g.app n
      map_smul := by
        intro i n U a x
        change ((f.app (i + n)).val.app U (M.smul i n U a x) +
          (g.app (i + n)).val.app U (M.smul i n U a x)) = _
        rw [f.map_smul, g.map_smul]
        change _ = (N.smul i n U a) ((f.app n).val.app U x + (g.app n).val.app U x)
        exact ((N.smul i n U a).map_add ((f.app n).val.app U x) ((g.app n).val.app U x)).symm }⟩

/-- The negative of a homomorphism of left graded modules, taken degreewise. -/
instance homNeg (M N : LeftGradedModule.{t, a, m} A) : Neg (M ⟶ N) :=
  ⟨fun f =>
    { app := fun n => -f.app n
      map_smul := by
        intro i n U a x
        change -((f.app (i + n)).val.app U (M.smul i n U a x)) = _
        rw [f.map_smul]
        change -((N.smul i n U a) ((f.app n).val.app U x)) =
          (N.smul i n U a) (-((f.app n).val.app U x))
        exact ((N.smul i n U a).map_neg ((f.app n).val.app U x)).symm }⟩

/-- The zero homomorphism is zero in every degree. -/
@[simp]
theorem zero_app' (M N : LeftGradedModule.{t, a, m} A) (n : ℤ) : (0 : M ⟶ N).app n = 0 := rfl

/-- The sum of two homomorphisms is their sum in every degree. -/
@[simp]
theorem add_app {M N : LeftGradedModule.{t, a, m} A} (f g : M ⟶ N) (n : ℤ) :
    (f + g).app n = f.app n + g.app n := rfl

/-- The negative of a homomorphism is its negative in every degree. -/
@[simp]
theorem neg_app {M N : LeftGradedModule.{t, a, m} A} (f : M ⟶ N) (n : ℤ) :
    (-f).app n = -f.app n := rfl

/-- The homomorphisms between two left graded modules form an abelian group under degreewise
addition. -/
instance homAddCommGroup (M N : LeftGradedModule.{t, a, m} A) : AddCommGroup (M ⟶ N) where
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

/-- **Left graded modules form a preadditive category**, homomorphisms being added degreewise. -/
instance preadditive : Preadditive (LeftGradedModule.{t, a, m} A) where
  homGroup M N := homAddCommGroup M N
  add_comp _ _ _ _ _ _ := Hom.ext fun _ => Preadditive.add_comp _ _ _ _ _ _
  comp_add _ _ _ _ _ _ := Hom.ext fun _ => Preadditive.comp_add _ _ _ _ _ _

end Preadditive

/-! ### Left graded modules are right graded modules over the opposite algebra -/

section OpRight

variable (M : LeftGradedModule.{t, a, m} A)

/-- The left action of a left graded module is a congruence for heterogeneous equality of its
algebra argument along an equality of degrees. -/
theorem smul_heq_left {i i' : ℤ} (h : i = i') (n : ℤ) (U : Cᵒᵖ) {a : (A.piece i).val.obj U}
    {a' : (A.piece i').val.obj U} (ha : HEq a a') (x : (M.piece n).val.obj U) :
    HEq (M.smul i n U a x) (M.smul i' n U a' x) := by
  subst h
  cases eq_of_heq ha
  rfl

/-- The left action of a left graded module is a congruence for heterogeneous equality of its
module argument along an equality of degrees. -/
theorem smul_heq_right (i : ℤ) {n n' : ℤ} (h : n = n') (U : Cᵒᵖ) (a : (A.piece i).val.obj U)
    {x : (M.piece n).val.obj U} {x' : (M.piece n').val.obj U} (hx : HEq x x') :
    HEq (M.smul i n U a x) (M.smul i n' U a x') := by
  subst h
  cases eq_of_heq hx
  rfl

/-- **A left graded `A`-module, read as a right graded `Aᵒᵖ`-module**: the right action of `a`
on `x` is the left action of `a` on `x`, moved from degree `i + n` to degree `n + i`. -/
def toOpRight : GradedModule.{t, a, m} A.op where
  piece := M.piece
  smul n i U := (AddMonoidHom.compHom (degTransportAdd M.piece (add_comm i n) U)).comp
    (M.smul i n U).flip
  smul_smul_left n i U r x y :=
    (congrArg (fun z => (degTransport M.piece (add_comm i n)).val.app U z)
      (M.smul_smul_right i n U r y x)).trans (degTransport_smul _ _ _ r _)
  smul_smul_right n i U r x y :=
    (congrArg (fun z => (degTransport M.piece (add_comm i n)).val.app U z)
      (M.smul_smul_left i n U r y x)).trans (degTransport_smul _ _ _ r _)
  smul_naturality n i {U V} f x y :=
    (PresheafOfModules.naturality_apply (degTransport M.piece (add_comm i n)).val f _).symm.trans
      (congrArg (fun z => (degTransport M.piece (add_comm i n)).val.app V z)
        (M.smul_naturality i n f y x))
  smul_mul n i j U x y z := by
    refine (degTransport_heq _ _ _ _).trans ?_
    refine (M.smul_heq_right j (add_comm n i) U z (degTransport_heq _ _ _ _)).trans ?_
    refine (M.mul_smul j i n U z y x).symm.trans ?_
    refine HEq.trans ?_ (degTransport_heq _ _ _ _).symm
    exact M.smul_heq_left (add_comm j i) n U (A.opMul_app_heq i j U y z).symm x
  smul_one n U x := (degTransport_heq _ _ _ _).trans (M.one_smul n U x)

/-- The right action of `y` on `x` in `M.toOpRight` is the left action of `y` on `x` in `M`,
moved from degree `i + n` to degree `n + i`. -/
theorem toOpRight_smul (n i : ℤ) (U : Cᵒᵖ) (x : (M.piece n).val.obj U)
    (y : (A.piece i).val.obj U) :
    M.toOpRight.smul n i U x y =
      (degTransport M.piece (add_comm i n)).val.app U (M.smul i n U y x) := rfl

variable {M} in
/-- A homomorphism of left graded modules, as a homomorphism of right graded modules over the
opposite algebra. -/
def toOpRightMap {N : LeftGradedModule.{t, a, m} A} (f : M ⟶ N) :
    M.toOpRight ⟶ N.toOpRight where
  app := f.app
  map_smul n i U x y :=
    (app_degTransport f.app (add_comm i n) U _).trans
      (congrArg (fun z => (degTransport N.piece (add_comm i n)).val.app U z) (f.map_smul i n U y x))

/-- **A right graded `Aᵒᵖ`-module, read as a left graded `A`-module**: the left action of `a` on
`x` is the right action of `a` on `x`, moved from degree `n + i` to degree `i + n`. -/
def ofOpRight (N : GradedModule.{t, a, m} A.op) : LeftGradedModule.{t, a, m} A where
  piece := N.piece
  smul i n U := (AddMonoidHom.compHom (degTransportAdd N.piece (add_comm n i) U)).comp
    (N.smul n i U).flip
  smul_smul_left i n U r a x :=
    (congrArg (fun z => (degTransport N.piece (add_comm n i)).val.app U z)
      (N.smul_smul_right n i U r x a)).trans (degTransport_smul _ _ _ r _)
  smul_smul_right i n U r a x :=
    (congrArg (fun z => (degTransport N.piece (add_comm n i)).val.app U z)
      (N.smul_smul_left n i U r x a)).trans (degTransport_smul _ _ _ r _)
  smul_naturality i n {U V} f a x :=
    (PresheafOfModules.naturality_apply (degTransport N.piece (add_comm n i)).val f _).symm.trans
      (congrArg (fun z => (degTransport N.piece (add_comm n i)).val.app V z)
        (N.smul_naturality n i f x a))
  mul_smul i j n U a b x := by
    refine (degTransport_heq _ _ _ _).trans ?_
    refine (GradedModule.smul_heq_algebra' N n (add_comm i j) U x
      (A.opMul_app_heq j i U b a).symm).trans ?_
    refine (N.smul_mul n j i U x b a).symm.trans ?_
    refine HEq.trans ?_ (degTransport_heq _ _ _ _).symm
    exact GradedModule.smul_heq_module' N (add_comm n j) i U (degTransport_heq _ _ _ _).symm a
  one_smul n U x := (degTransport_heq _ _ _ _).trans (N.smul_one n U x)


/-- The left action of `y` on `x` in `ofOpRight N` is the right action of `y` on `x` in `N`,
moved from degree `n + i` to degree `i + n`. -/
theorem ofOpRight_smul (N : GradedModule.{t, a, m} A.op) (i n : ℤ) (U : Cᵒᵖ)
    (y : (A.piece i).val.obj U) (x : (N.piece n).val.obj U) :
    (ofOpRight N).smul i n U y x =
      (degTransport N.piece (add_comm n i)).val.app U (N.smul n i U x y) := rfl

/-- A homomorphism of right graded modules over the opposite algebra, as a homomorphism of left
graded modules. -/
def ofOpRightMap {N N' : GradedModule.{t, a, m} A.op} (f : N ⟶ N') :
    ofOpRight N ⟶ ofOpRight N' where
  app := f.app
  map_smul i n U y x :=
    (app_degTransport f.app (add_comm n i) U _).trans
      (congrArg (fun z => (degTransport N'.piece (add_comm n i)).val.app U z)
        (f.map_smul n i U x y))

variable (A)

/-- Reading a left graded `A`-module as a right graded `Aᵒᵖ`-module, as a functor. -/
def toOpRightFunctor : LeftGradedModule.{t, a, m} A ⥤ GradedModule.{t, a, m} A.op where
  obj M := M.toOpRight
  map f := toOpRightMap f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Reading a right graded `Aᵒᵖ`-module as a left graded `A`-module, as a functor. -/
def ofOpRightFunctor : GradedModule.{t, a, m} A.op ⥤ LeftGradedModule.{t, a, m} A where
  obj N := ofOpRight N
  map f := ofOpRightMap f
  map_id _ := rfl
  map_comp _ _ := rfl

variable {A}

/-- A left graded module is isomorphic, by the identity in each degree, to the left graded
module read back from its right graded `Aᵒᵖ`-module. -/
def unitIsoApp (M : LeftGradedModule.{t, a, m} A) : M ≅ ofOpRight M.toOpRight where
  hom :=
    { app := fun _ => 𝟙 _
      map_smul := fun i n U _ _ =>
        (degTransport_degTransport M.piece (add_comm i n) (add_comm n i) U _).symm }
  inv :=
    { app := fun _ => 𝟙 _
      map_smul := fun i n U _ _ =>
        degTransport_degTransport M.piece (add_comm i n) (add_comm n i) U _ }
  hom_inv_id := Hom.ext fun _ => Category.comp_id _
  inv_hom_id := Hom.ext fun _ => Category.comp_id _

/-- A right graded `Aᵒᵖ`-module is isomorphic, by the identity in each degree, to the right
graded module read back from its left graded `A`-module. -/
def counitIsoApp (N : GradedModule.{t, a, m} A.op) : (ofOpRight N).toOpRight ≅ N where
  hom :=
    { app := fun _ => 𝟙 _
      map_smul := fun n i U _ _ =>
        degTransport_degTransport N.piece (add_comm n i) (add_comm i n) U _ }
  inv :=
    { app := fun _ => 𝟙 _
      map_smul := fun n i U _ _ =>
        (degTransport_degTransport N.piece (add_comm n i) (add_comm i n) U _).symm }
  hom_inv_id := GradedModule.Hom.ext fun _ => Category.comp_id _
  inv_hom_id := GradedModule.Hom.ext fun _ => Category.comp_id _

variable (A)

/-- **Left graded `A`-modules are right graded `Aᵒᵖ`-modules.** The equivalence is the identity on
homogeneous pieces and on the degreewise maps of homomorphisms. -/
def opRightEquivalence : LeftGradedModule.{t, a, m} A ≌ GradedModule.{t, a, m} A.op :=
  CategoryTheory.Equivalence.mk (toOpRightFunctor A) (ofOpRightFunctor A)
    (NatIso.ofComponents unitIsoApp fun _ =>
      Hom.ext fun _ => (Category.comp_id _).trans (Category.id_comp _).symm)
    (NatIso.ofComponents counitIsoApp fun _ =>
      GradedModule.Hom.ext fun _ => (Category.comp_id _).trans (Category.id_comp _).symm)

/-- The equivalence `opRightEquivalence` does not change the homogeneous pieces of a module. -/
@[simp]
theorem opRightEquivalence_functor_obj_piece (M : LeftGradedModule.{t, a, m} A) :
    ((opRightEquivalence A).functor.obj M).piece = M.piece := rfl

/-- The equivalence `opRightEquivalence` does not change the degreewise maps of homomorphisms. -/
@[simp]
theorem opRightEquivalence_functor_map_app {M N : LeftGradedModule.{t, a, m} A} (f : M ⟶ N)
    (n : ℤ) : ((opRightEquivalence A).functor.map f).app n = f.app n := rfl

/-- The functor of `opRightEquivalence` preserves zero morphisms. -/
instance opRightEquivalence_functor_preservesZeroMorphisms :
    (opRightEquivalence.{t, a, m} A).functor.PreservesZeroMorphisms where
  map_zero _ _ := rfl

/-! ### Taking a homogeneous component -/

/-- **Taking the homogeneous component of a fixed degree** of a left graded module. -/
@[sga "6 VI 2.7" "partial"]
def pieceFunctor (n : ℤ) : LeftGradedModule.{t, a, m} A ⥤ SheafOfModules.{m} R where
  obj M := M.piece n
  map f := f.app n
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The image of a left graded module under `pieceFunctor A n` is its piece of degree `n`. -/
@[simp]
theorem pieceFunctor_obj (n : ℤ) (M : LeftGradedModule.{t, a, m} A) :
    (pieceFunctor A n).obj M = M.piece n := rfl

/-- The image of a homomorphism under `pieceFunctor A n` is its component in degree `n`. -/
@[simp]
theorem pieceFunctor_map (n : ℤ) {M N : LeftGradedModule.{t, a, m} A} (f : M ⟶ N) :
    (pieceFunctor A n).map f = f.app n := rfl

/-- Taking a homogeneous component of a left graded module is taking it of the corresponding
right graded `Aᵒᵖ`-module. -/
def pieceFunctorIso (n : ℤ) :
    (opRightEquivalence A).functor ⋙ GradedModule.pieceFunctor.{t, a, m} A.op n ≅
      pieceFunctor A n :=
  Iso.refl _

/-- Taking a homogeneous component is an additive functor. -/
instance pieceFunctor_additive (n : ℤ) : (pieceFunctor.{t, a, m} A n).Additive where
  map_add := rfl

/-! ### The abelian structure -/

variable [HasSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]

/-- Left graded modules have finite products, formed degreewise. -/
instance hasFiniteProducts : HasFiniteProducts (LeftGradedModule.{t, a, m} A) :=
  ⟨fun _ => Adjunction.hasLimitsOfShape_of_equivalence (opRightEquivalence.{t, a, m} A).functor⟩

/-- **The category of left graded modules over a sheaf of graded algebras is abelian.** It is
equivalent, by `opRightEquivalence`, to the right graded modules over the opposite algebra, which
form an abelian category by Tag 0FR0. -/
noncomputable instance abelian : Abelian (LeftGradedModule.{t, a, m} A) :=
  abelianOfEquivalence (opRightEquivalence.{t, a, m} A).functor

/-- **Taking a homogeneous component of a left graded module preserves finite limits**: kernels
and finite products are formed degreewise. -/
@[sga "6 VI 2.7" "partial"]
instance pieceFunctor_preservesFiniteLimits (n : ℤ) :
    PreservesFiniteLimits (pieceFunctor.{t, a, m} A n) := by
  have hlim : PreservesLimitsOfSize.{m, m} (GradedModule.pieceFunctor.{t, a, m} A.op n) :=
    GradedModule.pieceFunctor_preservesLimitsOfSize (A := A.op) n
  have : PreservesFiniteLimits (GradedModule.pieceFunctor.{t, a, m} A.op n) :=
    PreservesLimitsOfSize.preservesFiniteLimits.{m, m} _
  have : PreservesFiniteLimits
      ((opRightEquivalence.{t, a, m} A).functor ⋙ GradedModule.pieceFunctor.{t, a, m} A.op n) :=
    comp_preservesFiniteLimits _ _
  exact preservesFiniteLimits_of_natIso (pieceFunctorIso A n)

/-- **Taking a homogeneous component of a left graded module preserves finite colimits**:
cokernels and finite direct sums are formed degreewise. -/
instance pieceFunctor_preservesFiniteColimits (n : ℤ) :
    PreservesFiniteColimits (pieceFunctor.{t, a, m} A n) := by
  have hcol : PreservesColimitsOfSize.{m, m} (GradedModule.pieceFunctor.{t, a, m} A.op n) :=
    GradedModule.pieceFunctor_preservesColimitsOfSize' (A := A.op) n
  have : PreservesFiniteColimits (GradedModule.pieceFunctor.{t, a, m} A.op n) :=
    PreservesColimitsOfSize.preservesFiniteColimits.{m, m} _
  have : PreservesFiniteColimits
      ((opRightEquivalence.{t, a, m} A).functor ⋙ GradedModule.pieceFunctor.{t, a, m} A.op n) :=
    comp_preservesFiniteColimits _ _
  exact preservesFiniteColimits_of_natIso (pieceFunctorIso A n)

end OpRight

end LeftGradedModule


end SheafOfModules

end
