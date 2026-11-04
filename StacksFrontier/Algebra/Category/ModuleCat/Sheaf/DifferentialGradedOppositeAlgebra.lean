module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LeftDifferentialGradedModule
public import StacksCore.Tactic.StacksAttribute

/-!
# The opposite of a sheaf of differential graded algebras

Let `R` be a sheaf of rings on a site and let `A` be a sheaf of differential graded
`R`-algebras. The **opposite** `A.op` has the same underlying cochain complex and the same unit,
and its multiplication is that of `A` with its two variables interchanged and twisted by the
Koszul sign: on homogeneous local sections of degrees `n` and `i`,

`x ⬝ y = (-1)^{n i} y x`.

The sign is what makes the signed Leibniz rule survive the interchange, and with it `A.op` is
again a sheaf of differential graded `R`-algebras. Left differential graded `A`-modules are then
the right differential graded `A.op`-modules, which is the use this file is put to in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedOppositeModule.lean`.

## Main definitions

* `SheafOfModules.DifferentialGradedAlgebra.op` is the opposite sheaf of differential graded
  algebras, and `SheafOfModules.DifferentialGradedAlgebra.opMul_app` computes its
  multiplication on local sections.
* `Stacks.BilinearMap.intSmul` is an integer multiple of a bilinear map of presheaves of
  modules.

## Main results

* `SheafOfModules.DifferentialGradedAlgebra.opMul_leibniz` is the signed Leibniz rule for the
  interchanged multiplication, the one law of a sheaf of differential graded algebras which the
  Koszul sign is there for.
* `SheafOfModules.gradedCast_bilinearMap_app`, `SheafOfModules.gradedCast_d_app` and
  `SheafOfModules.heq_zsmul` are the transport lemmas the degree bookkeeping needs: `n + i`
  and `i + n` are propositionally and not definitionally equal, so every value of the opposite
  multiplication is a transported value of the multiplication of `A`.

## Implementation notes

The multiplication of `A.op` is defined by transporting the whole bilinear map
`SheafOfModules.BilinearMap (A.complex.X n) (A.complex.X i) (A.complex.X (i + n))` along
`i + n = n + i`, rather than by writing its value on sections and reproving bilinearity: the
three laws of a bilinear map are then inherited, and `opMul_app` is the only computation rule a
consumer needs.

Associativity and the two unit laws are stated with `HEq` in the structure, so they are proved
by chaining heterogeneous equalities and the transports never have to be compared with one
another. The Leibniz rule is an equality in a single degree, so there the transports are pushed
through the sums and the integer multiples and merged with `SheafOfModules.gradedCast_trans`;
two transports with the same source and target degrees are definitionally equal, the equality
of degrees being a proposition, so no proof-irrelevance step appears. Where two transports with
heterogeneously equal sources do have to be identified, that is
`SheafOfModules.gradedCast_eq_gradedCast`.

## References

* [Stacks Project, Tag 0FRF](https://stacks.math.columbia.edu/tag/0FRF)
* [Stacks Project, Tag 0FRI](https://stacks.math.columbia.edu/tag/0FRI)
-/

@[expose] public section

open CategoryTheory

universe t a b c m v u

namespace Stacks

namespace BilinearMap

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{t}}
  {M : PresheafOfModules.{a} R} {N : PresheafOfModules.{b} R} {P : PresheafOfModules.{c} R}

/-- An integer multiple of a bilinear map of presheaves of modules. -/
def intSmul (β : BilinearMap M N P) (ε : ℤ) : BilinearMap M N P where
  app X :=
    AddMonoidHom.mk'
      (fun x ↦ AddMonoidHom.mk' (fun y ↦ ε • β.app X x y)
        (fun y y' ↦ by rw [map_add, smul_add]))
      (fun x x' ↦ AddMonoidHom.ext fun y ↦ by
        change ε • β.app X (x + x') y = ε • β.app X x y + ε • β.app X x' y
        rw [β.map_add_left, smul_add])
  map_smul_left X r x y := by
    change ε • β.app X (r • x) y = r • (ε • β.app X x y)
    rw [β.map_smul_left, smul_comm]
  map_smul_right X r x y := by
    change ε • β.app X x (r • y) = r • (ε • β.app X x y)
    rw [β.map_smul_right, smul_comm]
  naturality {X Y} f x y := by
    change P.map f (ε • β.app X x y) = ε • β.app Y (M.map f x) (N.map f y)
    rw [map_zsmul (ConcreteCategory.hom (P.map f)) ε (β.app X x y), β.naturality f]
    rfl

/-- The value of an integer multiple of a bilinear map is the integer multiple of its value. -/
@[simp]
theorem intSmul_app (β : BilinearMap M N P) (ε : ℤ) (X : Cᵒᵖ) (x : M.obj X) (y : N.obj X) :
    (β.intSmul ε).app X x y = ε • β.app X x y := rfl

/-- A bilinear map takes an integer multiple in its first variable to the integer multiple of
its value. -/
theorem app_zsmul_left (β : BilinearMap M N P) (ε : ℤ) (X : Cᵒᵖ) (x : M.obj X) (y : N.obj X) :
    β.app X (ε • x) y = ε • β.app X x y :=
  map_zsmul (AddMonoidHom.mk' (fun u ↦ β.app X u y) fun u u' ↦ β.map_add_left X u u' y) ε x

/-- A bilinear map takes an integer multiple in its second variable to the integer multiple of
its value. -/
theorem app_zsmul_right (β : BilinearMap M N P) (ε : ℤ) (X : Cᵒᵖ) (x : M.obj X) (y : N.obj X) :
    β.app X x (ε • y) = ε • β.app X x y :=
  map_zsmul (β.app X x) ε y

end BilinearMap

end Stacks

namespace SheafOfModules

/-! ### Transport along an equality of degrees -/

/-- Transport along an equality of degrees commutes with an integer multiple, read as a
heterogeneous equality. -/
theorem heq_zsmul {ι : Type*} (T : ι → Type*) [∀ i, SMul ℤ (T i)] {i j : ι} (h : i = j)
    (ε : ℤ) {x : T i} {y : T j} (hxy : x ≍ y) : (ε • x) ≍ (ε • y) :=
  heq_dependent_apply (fun i (x : T i) ↦ ε • x) h hxy

/-- Applying a map commuting with integer multiples to both sides of `x ≍ ε • y` gives
`f x ≍ ε • f y`. -/
private theorem heq_apply_zsmul {ι : Type*} {T S : ι → Type*} [∀ i, SMul ℤ (T i)]
    [∀ i, SMul ℤ (S i)] {i j : ι} (h : i = j) (f : ∀ k, T k → S k)
    (hf : ∀ k (ε : ℤ) (x : T k), f k (ε • x) = ε • f k x) {ε : ℤ} {x : T i} {y : T j}
    (hxy : x ≍ ε • y) : f i x ≍ ε • f j y :=
  (heq_dependent_apply f h hxy).trans (heq_of_eq (hf j ε y))

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

/-- The value of a bilinear map whose target has been transported along an equality of degrees
is the transported value. -/
theorem gradedCast_bilinearMap_app {E : ℤ → SheafOfModules.{c} R} {M : SheafOfModules.{a} R}
    {N : SheafOfModules.{b} R} {j k : ℤ} (h : j = k) (β : BilinearMap M N (E j)) (X : Cᵒᵖ)
    (x : M.val.obj X) (y : N.val.obj X) :
    (gradedCast (fun l ↦ BilinearMap M N (E l)) h β).app X x y =
      gradedCast (fun l ↦ (E l).val.obj X) h (β.app X x y) := by
  cases h
  rfl

/-- The differential of a cochain complex of sheaves of modules commutes with transport along
an equality of degrees. -/
theorem gradedCast_d_app (M : CochainComplex (SheafOfModules.{m} R) ℤ) {j k : ℤ} (h : j = k)
    (U : Cᵒᵖ) (x : (M.X j).val.obj U) :
    (M.d k (k + 1)).val.app U (gradedCast (fun q ↦ (M.X q).val.obj U) h x) =
      gradedCast (fun q ↦ (M.X q).val.obj U) (congrArg (· + (1 : ℤ)) h)
        ((M.d j (j + 1)).val.app U x) := by
  cases h
  rfl

/-- A differential of a cochain complex of sheaves of modules commutes with integer
multiples. -/
theorem d_app_zsmul (M : CochainComplex (SheafOfModules.{m} R) ℤ) (j k : ℤ) (U : Cᵒᵖ) (ε : ℤ)
    (x : (M.X j).val.obj U) :
    (M.d j k).val.app U (ε • x) = ε • (M.d j k).val.app U x :=
  map_zsmul (ConcreteCategory.hom ((M.d j k).val.app U)) ε x

namespace DifferentialGradedAlgebra

variable (A : DifferentialGradedAlgebra.{t, a} R)

/-- The multiplication of the opposite sheaf of differential graded algebras: the
multiplication of `A` with its variables interchanged, twisted by the Koszul sign and
transported from degree `i + n` to degree `n + i`. -/
noncomputable def opMul (n i : ℤ) :
    BilinearMap (A.complex.X n) (A.complex.X i) (A.complex.X (n + i)) :=
  gradedCast (fun k ↦ BilinearMap (A.complex.X n) (A.complex.X i) (A.complex.X k))
    (Int.add_comm i n) ((A.mul i n).flip.intSmul (Int.negOnePow (n * i)))

/-- The value of the opposite multiplication on homogeneous local sections. -/
theorem opMul_app (n i : ℤ) (U : Cᵒᵖ) (x : (A.complex.X n).val.obj U)
    (y : (A.complex.X i).val.obj U) :
    (A.opMul n i).app U x y =
      gradedCast (fun k ↦ (A.complex.X k).val.obj U) (Int.add_comm i n)
        ((Int.negOnePow (n * i) : ℤ) • (A.mul i n).app U y x) :=
  gradedCast_bilinearMap_app (E := A.complex.X) _ _ _ _ _

/-- The value of the opposite multiplication, read as a heterogeneous equality with the
untransported local section. -/
theorem opMul_app_heq (n i : ℤ) (U : Cᵒᵖ) (x : (A.complex.X n).val.obj U)
    (y : (A.complex.X i).val.obj U) :
    (A.opMul n i).app U x y ≍ (Int.negOnePow (n * i) : ℤ) • (A.mul i n).app U y x := by
  rw [A.opMul_app]
  exact gradedCast_heq _ _ _

/-- The interchanged multiplication is associative. -/
theorem opMul_assoc (n i j : ℤ) (U : Cᵒᵖ) (x : (A.complex.X n).val.obj U)
    (y : (A.complex.X i).val.obj U) (z : (A.complex.X j).val.obj U) :
    (A.opMul (n + i) j).app U ((A.opMul n i).app U x y) z ≍
      (A.opMul n (i + j)).app U x ((A.opMul i j).app U y z) := by
  refine HEq.trans (A.opMul_app_heq (n + i) j U ((A.opMul n i).app U x y) z) ?_
  refine HEq.trans ?_ (A.opMul_app_heq n (i + j) U x ((A.opMul i j).app U y z)).symm
  have hz {k l : ℤ} (h : k = l) (ε : ℤ) {u : (A.complex.X k).val.obj U}
      {v : (A.complex.X l).val.obj U} (huv : u ≍ v) : ε • u ≍ ε • v :=
    heq_zsmul (fun q ↦ (A.complex.X q).val.obj U) h ε huv
  refine HEq.trans (hz (congrArg (fun k ↦ j + k) (Int.add_comm n i)) _
    (heq_apply_zsmul (Int.add_comm n i) (fun k w ↦ (A.mul j k).app U z w)
      (fun _ _ _ ↦ (A.mul j _).app_zsmul_right _ _ _ _) (A.opMul_app_heq n i U x y))) ?_
  refine HEq.trans ?_ (hz (congrArg (fun k ↦ k + n) (Int.add_comm i j)) _
    (heq_apply_zsmul (Int.add_comm i j) (fun k w ↦ (A.mul k n).app U w x)
      (fun _ _ _ ↦ (A.mul _ n).app_zsmul_left _ _ _ _) (A.opMul_app_heq i j U y z))).symm
  refine HEq.trans (hz (add_assoc j i n).symm _
    (hz (add_assoc j i n).symm _ (A.mul_assoc j i n U z y x).symm)) ?_
  refine heq_of_eq ?_
  rw [smul_smul, smul_smul, ← Units.val_mul, ← Units.val_mul, ← Int.negOnePow_add,
    ← Int.negOnePow_add]
  congr 2
  ring_nf

/-- The unit of `A` is a left identity for the interchanged multiplication. -/
theorem opMul_one_mul (n : ℤ) (U : Cᵒᵖ) (x : (A.complex.X n).val.obj U) :
    (A.opMul 0 n).app U (A.one.eval U) x ≍ x := by
  refine HEq.trans (A.opMul_app_heq 0 n U (A.one.eval U) x) ?_
  rw [Int.zero_mul, Int.negOnePow_zero, Units.val_one, one_zsmul]
  exact A.mul_one n U x

/-- The unit of `A` is a right identity for the interchanged multiplication. -/
theorem opMul_mul_one (n : ℤ) (U : Cᵒᵖ) (x : (A.complex.X n).val.obj U) :
    (A.opMul n 0).app U x (A.one.eval U) ≍ x := by
  refine HEq.trans (A.opMul_app_heq n 0 U x (A.one.eval U)) ?_
  rw [Int.mul_zero, Int.negOnePow_zero, Units.val_one, one_zsmul]
  exact A.one_mul n U x

/-- **The signed Leibniz rule for the interchanged multiplication.** This is the law the Koszul
sign is there for: the two terms of the Leibniz rule of `A` are interchanged with it, and the
signs match because `(-1)^{n i}(-1)^{i} = (-1)^{(n + 1) i}` and
`(-1)^{n}(-1)^{n (i + 1)} = (-1)^{n i}`. -/
theorem opMul_leibniz (n i : ℤ) (U : Cᵒᵖ) (x : (A.complex.X n).val.obj U)
    (y : (A.complex.X i).val.obj U) :
    (A.complex.d (n + i) (n + i + 1)).val.app U ((A.opMul n i).app U x y) =
      gradedCast (fun q ↦ (A.complex.X q).val.obj U) (add_right_comm n 1 i)
          ((A.opMul (n + 1) i).app U ((A.complex.d n (n + 1)).val.app U x) y) +
        (Int.negOnePow n : ℤ) •
          gradedCast (fun q ↦ (A.complex.X q).val.obj U) (add_assoc n i 1).symm
            ((A.opMul n (i + 1)).app U x ((A.complex.d i (i + 1)).val.app U y)) := by
  have hsign₁ : (Int.negOnePow ((n + 1) * i) : ℤ) =
      (Int.negOnePow (n * i) : ℤ) * (Int.negOnePow i : ℤ) := by
    rw [← Units.val_mul, ← Int.negOnePow_add]
    congr 2
    ring
  have hsign₂ : (Int.negOnePow n : ℤ) * (Int.negOnePow (n * (i + 1)) : ℤ) =
      (Int.negOnePow (n * i) : ℤ) := by
    rw [← Units.val_mul, ← Int.negOnePow_add,
      show n + n * (i + 1) = n * i + 2 * n by ring, Int.negOnePow_add, Int.negOnePow_two_mul,
      _root_.mul_one]
  simp only [A.opMul_app, gradedCast_d_app, d_app_zsmul, A.leibniz i n U y x,
    gradedCast_smul, gradedCast_add, gradedCast_trans, smul_add, smul_smul]
  rw [hsign₁, hsign₂]
  abel

/-- **The opposite sheaf of differential graded algebras.** The underlying complex and the unit
are those of `A`, and the multiplication interchanges its variables and twists by the Koszul
sign. -/
@[stacks 0FRF "the opposite of a sheaf of differential graded algebras"]
noncomputable def op : DifferentialGradedAlgebra.{t, a} R where
  complex := A.complex
  mul := A.opMul
  one := A.one
  mul_assoc := A.opMul_assoc
  one_mul := A.opMul_one_mul
  mul_one := A.opMul_mul_one
  leibniz := A.opMul_leibniz

/-- The underlying complex of `A.op` is that of `A`. -/
@[simp] theorem op_complex : A.op.complex = A.complex := rfl

/-- The multiplication of `A.op` is the interchanged multiplication `A.opMul`. -/
@[simp] theorem op_mul (n i : ℤ) : A.op.mul n i = A.opMul n i := rfl

/-- The unit of `A.op` is that of `A`. -/
@[simp] theorem op_one : A.op.one = A.one := rfl

end DifferentialGradedAlgebra

end SheafOfModules

end
