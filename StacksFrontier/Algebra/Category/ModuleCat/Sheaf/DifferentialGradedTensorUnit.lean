module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedTensor

/-!
# The tensor product of a differential graded module with the diagonal bimodule

Let `R` be a sheaf of rings on a site and let `A` be a sheaf of differential graded
`R`-algebras. Then `A` is a differential graded `(A, A)`-bimodule `{}_A A_A` over itself, both
actions being its own graded multiplication, and for a right differential graded `A`-module `M`
the tensor product `M ⊗_A {}_A A_A` is `M` itself: the universal `A`-balanced bilinear map is
the right action `(x, a) ↦ x a` of `A` on `M`, which is `R`-bilinear, `A`-balanced by
associativity and obeys the signed Leibniz rule; and an `A`-balanced bilinear family `β` of
degree `n` out of `M` and `A` is recovered from the degree-`n` local homomorphism
`x ↦ β (x, 1)`, because `β (x, a) = β (x, 1) a`.

Consequently the identity functor of `Mod^dg(A, d)` is a tensor product functor
`- ⊗_A {}_A A_A`.

## Main definitions

* `SheafOfModules.DifferentialGradedAlgebra.diagonalBimodule` is `{}_A A_A`, a sheaf of
  differential graded algebras read as a differential graded bimodule over itself.
* `SheafOfModules.DifferentialGradedModule.diagonalBalanced` is the `A`-balanced bilinear
  family `(x, a) ↦ f (x a)` attached to a local homomorphism `f` out of `M`, and
  `SheafOfModules.DifferentialGradedModule.diagonalDescend` is the local homomorphism
  `x ↦ β (x, 1)` attached to an `A`-balanced bilinear family `β`.
* `SheafOfModules.DifferentialGradedModule.diagonalUniversal` is the bijection between the two
  that these constructions make.

## Main results

* `SheafOfModules.DifferentialGradedModule.isTensorProductDiagonal`: **a right differential
  graded `A`-module `M` is the tensor product `M ⊗_A {}_A A_A`**, with multiplication map the
  right action of `A` on `M`.
* `SheafOfModules.DifferentialGradedModule.tensorFunctorDataDiagonal`: **the identity functor
  of `Mod^dg(A, d)`, together with that multiplication map, is a tensor product functor
  `- ⊗_A {}_A A_A`.**

## Implementation notes

`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedTensor.lean` pins the tensor
product `M ⊗_A N` of a right differential graded `A`-module with a differential graded
`(A, B)`-bimodule by a universal property, `SheafOfModules.IsTensorProduct`, rather than by a
formula: sheaves of modules over a sheaf of rings which is not assumed commutative carry no
monoidal structure to build the underlying graded object from. For `N = {}_A A_A` no such
construction is needed, since the tensor product is the module itself, so the universal
property and the functor datum `SheafOfModules.TensorFunctorData` built on it are inhabited
here.

The bimodule `{}_A A_A` is the case `φ = 𝟙` of
`SheafOfModules.DifferentialGradedAlgebra.asBimodule` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedBimoduleStructures.lean`,
but it is spelled out rather than obtained from it, because its complex and its two actions
have to be *reducibly* those of `A`: the local sections of the bimodule in the universal
property are then the local sections of `A` for the elaborator as well, which is what lets the
laws of the action be used on them directly.

The two degree bookkeeping devices of the universal property reappear in the proofs. A
balanced bilinear family carries its target degree `k` together with a proof of
`i + j + n = k`, so the degrees `i + 0` and `i`, resp. `j + 0` and `j`, which the unit of `A`
produces must be identified by transport: `SheafOfModules.LocalGradedHom.app_heq_arg` and
`SheafOfModules.LocalBalancedBilinear.app_heq_right` do this, and they are what turns the
`HEq`-valued associativity and unit laws of the action into the equalities the fields of
`SheafOfModules.IsTensorProduct` and `SheafOfModules.LocalBalancedBilinear` ask for.

## References

* [Stacks Project, Tag 0FRP](https://stacks.math.columbia.edu/tag/0FRP)
* [Stacks Project, Tag 0FRM](https://stacks.math.columbia.edu/tag/0FRM)
* [Stacks Project, Tag 0FRI](https://stacks.math.columbia.edu/tag/0FRI)
-/

@[expose] public section

open CategoryTheory

universe t a w z s v u

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A B : DifferentialGradedAlgebra.{t, a} R}

/-- The degree bookkeeping of evaluating a degree-`n` family at a degree-zero section: a
degree-`n` map from degree `i` to degree `j` is a family of degree `n` from the degrees `i` and
`0` to the degree `j`. -/
theorem degree_zero_right {i n j : ℤ} (hij : i + n = j) : i + 0 + n = j := by
  rwa [add_zero]

/-- The values of a degree-`n` map of the underlying graded modules on heterogeneously equal
local sections in propositionally equal degrees agree. -/
theorem LocalGradedHom.app_heq_arg {M : DifferentialGradedModule.{t, a, w} A}
    {L : DifferentialGradedModule.{t, a, z} A} {n : ℤ} {U : C} (f : LocalGradedHom M L n U)
    {i i' j : ℤ} (hij : i + n = j) (hij' : i' + n = j) (V : Over U)
    {x : (M.complex.X i).val.obj (Opposite.op V.left)}
    {x' : (M.complex.X i').val.obj (Opposite.op V.left)} (hi : i = i') (hx : HEq x x') :
    f.app i j hij V x = f.app i' j hij' V x' := by
  subst hi
  obtain rfl := eq_of_heq hx
  rfl

/-- The values of an `A`-balanced bilinear family on heterogeneously equal local sections of
the bimodule in propositionally equal degrees agree. -/
theorem LocalBalancedBilinear.app_heq_right {M : DifferentialGradedModule.{t, a, w} A}
    {N : DifferentialGradedBimodule.{t, a, z} A B} {L : DifferentialGradedModule.{t, a, s} B}
    {n : ℤ} {U : C} (β : LocalBalancedBilinear M N L n U) {i j j' k : ℤ}
    (hijk : i + j + n = k) (hijk' : i + j' + n = k) (V : Over U)
    (x : (M.complex.X i).val.obj (Opposite.op V.left))
    {y : (N.complex.X j).val.obj (Opposite.op V.left)}
    {y' : (N.complex.X j').val.obj (Opposite.op V.left)} (hj : j = j') (hy : HEq y y') :
    β.app i j k hijk V x y = β.app i j' k hijk' V x y' := by
  subst hj
  obtain rfl := eq_of_heq hy
  rfl

namespace DifferentialGradedAlgebra

/-- **`{}_A A_A`: a sheaf of differential graded algebras is a differential graded
`(A, A)`-bimodule over itself**, acting on both sides by its own graded multiplication. -/
@[implicit_reducible]
def diagonalBimodule (A : DifferentialGradedAlgebra.{t, a} R) :
    DifferentialGradedBimodule.{t, a, a} A A where
  complex := A.complex
  rightMul := A.mul
  leftMul := A.mul
  left_assoc i j n U x y z := (A.mul_assoc i j n U x y z).symm
  right_assoc := A.mul_assoc
  left_right_assoc i n j U x y z := A.mul_assoc i n j U x y z
  one_left := A.one_mul
  one_right := A.mul_one
  leibniz_left := A.leibniz
  leibniz_right := A.leibniz

/-- The underlying complex of the diagonal bimodule `{}_A A_A` is that of `A`. -/
@[simp]
theorem diagonalBimodule_complex (A : DifferentialGradedAlgebra.{t, a} R) :
    A.diagonalBimodule.complex = A.complex :=
  rfl

/-- The left action of `A` on the diagonal bimodule `{}_A A_A` is the multiplication of `A`. -/
@[simp]
theorem diagonalBimodule_leftMul (A : DifferentialGradedAlgebra.{t, a} R) (n i : ℤ) :
    A.diagonalBimodule.leftMul n i = A.mul n i :=
  rfl

/-- The right action of `A` on the diagonal bimodule `{}_A A_A` is the multiplication of `A`. -/
@[simp]
theorem diagonalBimodule_rightMul (A : DifferentialGradedAlgebra.{t, a} R) (n i : ℤ) :
    A.diagonalBimodule.rightMul n i = A.mul n i :=
  rfl

end DifferentialGradedAlgebra

namespace DifferentialGradedModule

variable {M L : DifferentialGradedModule.{t, a, w} A}

/-- The biadditive map `(x, y) ↦ f (x y)` on local sections, from degrees `i` and `j` to
degree `k`, attached to a degree-`n` local homomorphism `f` out of `M`. -/
def diagonalBalancedApp {n : ℤ} {U : C} (f : LocalHom M L n U) (i j k : ℤ)
    (hijk : i + j + n = k) (V : Over U) :
    (M.complex.X i).val.obj (Opposite.op V.left) →+
      (A.diagonalBimodule.complex.X j).val.obj (Opposite.op V.left) →+
        (L.complex.X k).val.obj (Opposite.op V.left) :=
  (AddMonoidHom.compHom (f.app (i + j) k hijk V)).comp
    ((M.mul i j).app (Opposite.op V.left))

/-- The value of `diagonalBalancedApp f` at `(x, y)` is `f (x y)`. -/
@[simp]
theorem diagonalBalancedApp_apply {n : ℤ} {U : C} (f : LocalHom M L n U) (i j k : ℤ)
    (hijk : i + j + n = k) (V : Over U)
    (x : (M.complex.X i).val.obj (Opposite.op V.left))
    (y : (A.diagonalBimodule.complex.X j).val.obj (Opposite.op V.left)) :
    diagonalBalancedApp f i j k hijk V x y =
      f.app (i + j) k hijk V ((M.mul i j).app (Opposite.op V.left) x y) :=
  rfl

/-- The `A`-balanced bilinear family `(x, a) ↦ f (x a)` of degree `n` for the diagonal
bimodule, attached to a degree-`n` local homomorphism `f` out of `M`. -/
def diagonalBalanced {n : ℤ} {U : C} (f : LocalHom M L n U) :
    LocalBalancedBilinear M A.diagonalBimodule L n U where
  app i j k hijk V := diagonalBalancedApp f i j k hijk V
  map_smul_left i j k hijk V r x y := by
    simp only [diagonalBalancedApp_apply]
    rw [(M.mul i j).map_smul_left, f.map_smul]
  map_smul_right i j k hijk V r x y := by
    simp only [diagonalBalancedApp_apply]
    rw [(M.mul i j).map_smul_right, f.map_smul]
  naturality i j k hijk {V W} g x y :=
    (f.naturality (i + j) k hijk g ((M.mul i j).app (Opposite.op V.left) x y)).trans
      (congrArg (fun u => f.app (i + j) k hijk W u) ((M.mul i j).naturality g.left.op x y))
  balanced i p j k hijk V x a y := by
    simp only [diagonalBalancedApp_apply,
      DifferentialGradedAlgebra.diagonalBimodule_leftMul]
    exact LocalGradedHom.app_heq_arg f.toLocalGradedHom hijk (by omega) V (add_assoc i p j)
      (M.mul_assoc i p j (Opposite.op V.left) x a y)
  map_rightMul i j p k hijk V x y b := by
    simp only [diagonalBalancedApp_apply, DifferentialGradedAlgebra.diagonalBimodule_rightMul]
    rw [← f.isLinear (i + j) k hijk p V ((M.mul i j).app (Opposite.op V.left) x y) b]
    exact LocalGradedHom.app_heq_arg f.toLocalGradedHom (by omega) (by omega) V
      (add_assoc i j p).symm (M.mul_assoc i j p (Opposite.op V.left) x y b).symm

/-- The value of `diagonalBalanced f` at `(x, y)` is `f (x y)`. -/
@[simp]
theorem diagonalBalanced_app {n : ℤ} {U : C} (f : LocalHom M L n U) (i j k : ℤ)
    (hijk : i + j + n = k) (V : Over U)
    (x : (M.complex.X i).val.obj (Opposite.op V.left))
    (y : (A.diagonalBimodule.complex.X j).val.obj (Opposite.op V.left)) :
    (diagonalBalanced f).app i j k hijk V x y =
      f.app (i + j) k hijk V ((M.mul i j).app (Opposite.op V.left) x y) :=
  rfl

/-- The additive map `x ↦ β (x, 1)` on local sections, from degree `i` to degree `j`, attached
to an `A`-balanced bilinear family `β` of degree `n` for the diagonal bimodule. -/
def diagonalDescendApp {n : ℤ} {U : C}
    (β : LocalBalancedBilinear M A.diagonalBimodule L n U) (i j : ℤ) (hij : i + 0 + n = j)
    (V : Over U) :
    (M.complex.X i).val.obj (Opposite.op V.left) →+
      (L.complex.X j).val.obj (Opposite.op V.left) :=
  (β.app i 0 j hij V).flip (A.one.eval (Opposite.op V.left))

/-- The value of `diagonalDescendApp β` at `x` is `β (x, 1)`. -/
@[simp]
theorem diagonalDescendApp_apply {n : ℤ} {U : C}
    (β : LocalBalancedBilinear M A.diagonalBimodule L n U) (i j : ℤ) (hij : i + 0 + n = j)
    (V : Over U) (x : (M.complex.X i).val.obj (Opposite.op V.left)) :
    diagonalDescendApp β i j hij V x =
      β.app i 0 j hij V x (A.one.eval (Opposite.op V.left)) :=
  rfl

/-- The degree-`n` local homomorphism `x ↦ β (x, 1)` out of `M`, attached to an `A`-balanced
bilinear family `β` of degree `n` for the diagonal bimodule. -/
def diagonalDescend {n : ℤ} {U : C}
    (β : LocalBalancedBilinear M A.diagonalBimodule L n U) : LocalHom M L n U where
  app i j hij V := diagonalDescendApp β i j (degree_zero_right hij) V
  map_smul i j hij V r x := by
    simp only [diagonalDescendApp_apply]
    exact β.map_smul_left i 0 j (degree_zero_right hij) V r x
      (A.one.eval (Opposite.op V.left))
  naturality i j hij {V W} g x :=
    (β.naturality i 0 j (degree_zero_right hij) g x
        (A.one.eval (Opposite.op V.left))).trans
      (congrArg
        (fun z => β.app i 0 j (degree_zero_right hij) W
          ((M.complex.X i).val.map g.left.op x) z)
        (PresheafOfModules.sections_property A.one g.left.op))
  isLinear i j hij p V x b := by
    have h2 : i + (p + 0) + n = j + p := by omega
    have h3 : i + p + n = j + p := by omega
    have h4 : i + (0 + p) + n = j + p := by omega
    have e2 : β.app i (p + 0) (j + p) h2 V x
          ((A.diagonalBimodule.leftMul p 0).app (Opposite.op V.left) b
            (A.one.eval (Opposite.op V.left))) =
        β.app i p (j + p) h3 V x b :=
      LocalBalancedBilinear.app_heq_right β h2 h3 V x (add_zero p)
        (A.mul_one p (Opposite.op V.left) b)
    have e4 : β.app i (0 + p) (j + p) h4 V x
          ((A.diagonalBimodule.rightMul 0 p).app (Opposite.op V.left)
            (A.one.eval (Opposite.op V.left)) b) =
        β.app i p (j + p) h3 V x b :=
      LocalBalancedBilinear.app_heq_right β h4 h3 V x (zero_add p)
        (A.one_mul p (Opposite.op V.left) b)
    simp only [diagonalDescendApp_apply]
    exact (β.balanced i p 0 (j + p) (by omega) V x b (A.one.eval (Opposite.op V.left))).trans
      (e2.trans (e4.symm.trans (β.map_rightMul i 0 p j (degree_zero_right hij) V x
        (A.one.eval (Opposite.op V.left)) b)))

/-- The value of `diagonalDescend β` at `x` is `β (x, 1)`. -/
@[simp]
theorem diagonalDescend_app {n : ℤ} {U : C}
    (β : LocalBalancedBilinear M A.diagonalBimodule L n U) (i j : ℤ) (hij : i + n = j)
    (V : Over U) (x : (M.complex.X i).val.obj (Opposite.op V.left)) :
    (diagonalDescend β).app i j hij V x =
      β.app i 0 j (degree_zero_right hij) V x (A.one.eval (Opposite.op V.left)) :=
  rfl

/-- A degree-`n` local homomorphism out of `M` is recovered from the `A`-balanced bilinear
family it induces, by evaluating at the unit of `A`. -/
theorem diagonalDescend_diagonalBalanced {n : ℤ} {U : C} (f : LocalHom M L n U) :
    diagonalDescend (diagonalBalanced f) = f :=
  LocalHom.ext fun i j hij V x => by
    rw [diagonalDescend_app, diagonalBalanced_app]
    exact LocalGradedHom.app_heq_arg f.toLocalGradedHom (degree_zero_right hij) hij V
      (add_zero i) (M.mul_one i (Opposite.op V.left) x)

/-- An `A`-balanced bilinear family of degree `n` for the diagonal bimodule is recovered from
the local homomorphism `x ↦ β (x, 1)` it induces. -/
theorem diagonalBalanced_diagonalDescend {n : ℤ} {U : C}
    (β : LocalBalancedBilinear M A.diagonalBimodule L n U) :
    diagonalBalanced (diagonalDescend β) = β :=
  LocalBalancedBilinear.ext fun i j k hijk V x y => by
    have h2 : i + (j + 0) + n = k := by omega
    rw [diagonalBalanced_app, diagonalDescend_app]
    refine (β.balanced i j 0 k (by omega) V x y (A.one.eval (Opposite.op V.left))).trans ?_
    exact LocalBalancedBilinear.app_heq_right β h2 hijk V x (add_zero j)
      (A.mul_one j (Opposite.op V.left) y)

/-- **The universal property of `M ⊗_A {}_A A_A = M`**: composing a degree-`n` local
homomorphism out of `M` with the right action of `A` is a bijection onto the `A`-balanced
bilinear families of degree `n` for the diagonal bimodule, with inverse `β ↦ (x ↦ β (x, 1))`. -/
def diagonalUniversal (M L : DifferentialGradedModule.{t, a, w} A) (n : ℤ) (U : C) :
    LocalHom M L n U ≃ LocalBalancedBilinear M A.diagonalBimodule L n U where
  toFun f := diagonalBalanced f
  invFun β := diagonalDescend β
  left_inv f := diagonalDescend_diagonalBalanced f
  right_inv β := diagonalBalanced_diagonalDescend β

/-- **A right differential graded `A`-module `M` is the tensor product `M ⊗_A {}_A A_A`** of
itself with the diagonal bimodule: the universal `A`-balanced bilinear map is the right action
`(x, a) ↦ x a` of `A` on `M`. -/
def isTensorProductDiagonal (M : DifferentialGradedModule.{t, a, w} A) :
    IsTensorProduct M A.diagonalBimodule M where
  tmul i j U := (M.mul i j).app U
  tmul_smul_left i j U r x y := (M.mul i j).map_smul_left U r x y
  tmul_smul_right i j U r x y := (M.mul i j).map_smul_right U r x y
  tmul_naturality i j {_ _} g x y := (M.mul i j).naturality g x y
  tmul_balanced i p j U x a y := M.mul_assoc i p j U x a y
  tmul_rightMul i j p U x y b := M.mul_assoc i j p U x y b
  tmul_d i j U x y := M.leibniz i j U x y
  universal L n U := diagonalUniversal M L n U
  universal_app _ _ _ _ _ _ _ _ _ _ _ := rfl

/-- **The identity functor of `Mod^dg(A, d)` is a tensor product functor
`- ⊗_A {}_A A_A`**: its value at `M` is the tensor product of `M` with the diagonal bimodule,
and a homomorphism `f` acts on local sections by `x ⊗ a ↦ f x ⊗ a`. -/
def tensorFunctorDataDiagonal (A : DifferentialGradedAlgebra.{t, a} R) :
    TensorFunctorData A A A.diagonalBimodule where
  functor := 𝟭 (DifferentialGradedModule.{t, a, w} A)
  isTensorProduct M := isTensorProductDiagonal M
  map_spec {_ _} f i j U x y := f.map_mul i j U x y

end DifferentialGradedModule

end SheafOfModules

end
