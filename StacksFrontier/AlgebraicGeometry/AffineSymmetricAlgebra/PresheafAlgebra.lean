module

public import StacksFrontier.AlgebraicGeometry.AffineSymmetricAlgebra.BaseChange
public import StacksFrontier.AlgebraicGeometry.AffineSymmetricAlgebra.GradedPieces
public import StacksFrontier.AlgebraicGeometry.AffineSymmetricAlgebra.Transport

/-!
# The base change of the symmetric algebra of a module, as a graded algebra of presheaves

Let `R` be a commutative ring and `M` an `R`-module. The family of presheaves of
`𝒪_{Spec R}`-modules

`U ↦ 𝒪(U) ⊗_R Sym^n_R(M)`, `n : ℤ`

is a graded algebra of presheaves of modules (`Stacks.GradedAlgebra`), with multiplication the
base change of the multiplication `Sym^i(M) × Sym^j(M) ⟶ Sym^{i+j}(M)` of the symmetric algebra
and unit `1 ⊗ 1`.

## Main definitions

* `Stacks.SymGraded.piecePresheaf`: the presheaf `U ↦ 𝒪(U) ⊗_R Sym^n_R(M)`.
* `Stacks.SymGraded.mulSec`: the multiplication on sections, the base change of the graded
  multiplication of the symmetric algebra.
* `Stacks.SymGraded.mulPresheaf` and `onePresheaf`: that multiplication as a bilinear map of
  presheaves of modules, and the unit as a global section of the degree-zero piece.
* `Stacks.SymGraded.presheafAlgebra`: the graded algebra of presheaves of modules.

## Main results

* `Stacks.SymGraded.mulSec_tmul`: the multiplication on pure tensors.
* `Stacks.SymGraded.mulSec_naturality`: it commutes with the restriction maps.

## Implementation notes

The associativity and unit laws are heterogeneous equalities, because `(i + j) + k` and
`i + (j + k)` are not definitionally equal in `ℤ` and so the two sides of each law live in the
base changes of two different graded pieces. They are discharged by
`Stacks.SymGraded.heq_tensor_of_eq`, which takes the equality of graded pieces as a hypothesis and
substitutes it internally; what is left is an equality of base changes of a single graded piece,
which is additive in each argument and so is checked on pure tensors, where it is associativity
in `𝒪(U)` and in the symmetric algebra.

## References

* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open scoped TensorProduct

universe u

namespace Stacks.SymGraded

variable {R : CommRingCat.{u}} (M : ModuleCat.{u} R)

/-- The degree-`n` graded piece of the symmetric algebra of `M`, as an `R`-module. -/
abbrev pieceModule (n : ℤ) : ModuleCat.{u} R := ModuleCat.of R (gradedPiece (R := R) M n)

/-- **The degree-`n` piece of the base change of the symmetric algebra**: the presheaf of
`𝒪_{Spec R}`-modules `U ↦ 𝒪(U) ⊗_R Sym^n_R(M)`. -/
abbrev piecePresheaf (n : ℤ) : PresheafOfModules.{u} (Spec R).ringCatSheaf.obj :=
  AffineBaseChange.presheaf (pieceModule M n)

/-- The graded multiplication on sections over `U`: the base change to `𝒪(U)` of the
multiplication `Sym^i(M) × Sym^j(M) → Sym^{i+j}(M)`. -/
def mulSec (U : ((Spec R).Opens)ᵒᵖ) (i j : ℤ) :
    (Γ(Spec R, U.unop) ⊗[R] gradedPiece (R := R) M i) →ₗ[Γ(Spec R, U.unop)]
      ((Γ(Spec R, U.unop) ⊗[R] gradedPiece (R := R) M j) →ₗ[Γ(Spec R, U.unop)]
        (Γ(Spec R, U.unop) ⊗[R] gradedPiece (R := R) M (i + j))) :=
  baseChangeBil Γ(Spec R, U.unop) (symMulₗ (R := R) M i j)

/-- The multiplication on sections sends `(a ⊗ x, b ⊗ y)` to `(a * b) ⊗ (x * y)`. -/
@[simp]
theorem mulSec_tmul (U : ((Spec R).Opens)ᵒᵖ) (i j : ℤ) (a b : Γ(Spec R, U.unop))
    (x : gradedPiece (R := R) M i) (y : gradedPiece (R := R) M j) :
    mulSec M U i j (a ⊗ₜ[R] x) (b ⊗ₜ[R] y) = (a * b) ⊗ₜ[R] symMulₗ (R := R) M i j x y :=
  baseChangeBil_tmul _ _ a b x y

/-- A restriction map of the base-changed graded piece, as an `R`-linear map. -/
def pieceRestrict {U V : ((Spec R).Opens)ᵒᵖ} (f : U ⟶ V) (n : ℤ) :
    (Γ(Spec R, U.unop) ⊗[R] gradedPiece (R := R) M n) →ₗ[R]
      (Γ(Spec R, V.unop) ⊗[R] gradedPiece (R := R) M n) :=
  LinearMap.rTensor _ (AffineBaseChange.specRestrictₗ (R := R) f.unop)

/-- The restriction map of `piecePresheaf M n` along `f` is `pieceRestrict M f n`. -/
theorem pieceRestrict_eq {U V : ((Spec R).Opens)ᵒᵖ} (f : U ⟶ V) (n : ℤ)
    (x : (piecePresheaf M n).obj U) :
    (piecePresheaf M n).map f x = pieceRestrict M f n x := rfl

/-- The restriction map `pieceRestrict M f n` sends `a ⊗ x` to `a|_V ⊗ x`. -/
@[simp]
theorem pieceRestrict_tmul {U V : ((Spec R).Opens)ᵒᵖ} (f : U ⟶ V) (n : ℤ)
    (a : Γ(Spec R, U.unop)) (x : gradedPiece (R := R) M n) :
    pieceRestrict M f n (a ⊗ₜ[R] x) = AffineBaseChange.specRestrictₗ (R := R) f.unop a ⊗ₜ[R] x :=
  rfl

/-- The multiplication on sections commutes with the restriction maps. -/
theorem mulSec_naturality {U V : ((Spec R).Opens)ᵒᵖ} (f : U ⟶ V) (i j : ℤ)
    (x : Γ(Spec R, U.unop) ⊗[R] gradedPiece (R := R) M i)
    (y : Γ(Spec R, U.unop) ⊗[R] gradedPiece (R := R) M j) :
    pieceRestrict M f (i + j) (mulSec M U i j x y) =
      mulSec M V i j (pieceRestrict M f i x) (pieceRestrict M f j y) := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
      induction y using TensorProduct.inductionOn with
      | tmul b y =>
          rw [mulSec_tmul, pieceRestrict_tmul, pieceRestrict_tmul, pieceRestrict_tmul,
            mulSec_tmul]
          exact congrArg (fun c => c ⊗ₜ[R] symMulₗ (R := R) M i j x y)
            (AffineBaseChange.specRestrictₗ_mul f.unop a b)
      | add y y' hy hy' => rw [map_add, map_add, map_add, map_add, hy, hy']
  | add x x' hx hx' =>
      rw [map_add (mulSec M U i j), LinearMap.add_apply, map_add (pieceRestrict M f (i + j)),
        hx, hx', map_add (pieceRestrict M f i), map_add (mulSec M V i j), LinearMap.add_apply]

/-- **The graded multiplication**, as a bilinear map of presheaves of modules. -/
def mulPresheaf (i j : ℤ) :
    BilinearMap (piecePresheaf M i) (piecePresheaf M j) (piecePresheaf M (i + j)) where
  app U := AddMonoidHom.mk' (fun x => (mulSec M U i j x).toAddMonoidHom)
    fun x x' => AddMonoidHom.ext fun y =>
      congrArg (fun g : (Γ(Spec R, U.unop) ⊗[R] gradedPiece (R := R) M j) →ₗ[Γ(Spec R, U.unop)]
          (Γ(Spec R, U.unop) ⊗[R] gradedPiece (R := R) M (i + j)) => g y)
        (map_add (mulSec M U i j) x x')
  map_smul_left U r x y :=
    congrArg (fun g : (Γ(Spec R, U.unop) ⊗[R] gradedPiece (R := R) M j) →ₗ[Γ(Spec R, U.unop)]
        (Γ(Spec R, U.unop) ⊗[R] gradedPiece (R := R) M (i + j)) => g y)
      ((mulSec M U i j).map_smul r x)
  map_smul_right U r x y := (mulSec M U i j x).map_smul r y
  naturality f x y := mulSec_naturality M f i j x y

/-- On sections over `U`, `mulPresheaf M i j` is the multiplication `mulSec M U i j`. -/
@[simp]
theorem mulPresheaf_app (i j : ℤ) (U : ((Spec R).Opens)ᵒᵖ)
    (x : (piecePresheaf M i).obj U) (y : (piecePresheaf M j).obj U) :
    (mulPresheaf M i j).app U x y = mulSec M U i j x y := rfl

/-- **The unit**, as a global section of the degree-zero piece. -/
def onePresheaf : (piecePresheaf M 0).sections :=
  PresheafOfModules.sectionsMk (fun U => (1 : Γ(Spec R, U.unop)) ⊗ₜ[R] oneG (R := R) M)
    fun {U _} f => by
      change pieceRestrict M f 0 ((1 : Γ(Spec R, U.unop)) ⊗ₜ[R] oneG (R := R) M) = _
      rw [pieceRestrict_tmul]
      exact congrArg (fun c => c ⊗ₜ[R] oneG (R := R) M)
        (AffineBaseChange.specRestrictₗ_one f.unop)

/-- The section `onePresheaf M` over `U` is `1 ⊗ 1`. -/
@[simp]
theorem onePresheaf_eval (U : ((Spec R).Opens)ᵒᵖ) :
    (onePresheaf M).eval U = (1 : Γ(Spec R, U.unop)) ⊗ₜ[R] oneG (R := R) M := rfl

/-! ### The graded-algebra laws on sections -/

/-- Pure tensors in one graded piece are equal if their coefficients and the underlying
elements of the symmetric algebra are. -/
private theorem tmul_eq_tmul_of_coe_eq {A : Type u} [CommRing A] [Algebra R A] {n : ℤ}
    {a b : A} {x y : gradedPiece (R := R) M n} (ha : a = b)
    (hxy : (x : SymmetricAlgebra R M) = y) : a ⊗ₜ[R] x = b ⊗ₜ[R] y :=
  congrArg₂ (fun (d : A) (w : gradedPiece (R := R) M n) => d ⊗ₜ[R] w) ha (Subtype.ext hxy)

/-- **Associativity on sections**, across the degree identification. -/
theorem mulSec_assoc (U : ((Spec R).Opens)ᵒᵖ) (i j k : ℤ)
    (x : Γ(Spec R, U.unop) ⊗[R] gradedPiece (R := R) M i)
    (y : Γ(Spec R, U.unop) ⊗[R] gradedPiece (R := R) M j)
    (z : Γ(Spec R, U.unop) ⊗[R] gradedPiece (R := R) M k) :
    tensorCongr (A := Γ(Spec R, U.unop)) (congrArg (gradedPiece (R := R) M) (add_assoc i j k))
        (mulSec M U (i + j) k (mulSec M U i j x y) z) =
      mulSec M U i (j + k) x (mulSec M U j k y z) := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
      induction y using TensorProduct.inductionOn with
      | tmul b y =>
          induction z using TensorProduct.inductionOn with
          | tmul c z =>
              rw [mulSec_tmul, mulSec_tmul, mulSec_tmul, mulSec_tmul, tensorCongr_tmul]
              exact tmul_eq_tmul_of_coe_eq M (_root_.mul_assoc a b c)
                (_root_.mul_assoc (x : SymmetricAlgebra R M) y z)
          | add z z' hz hz' =>
              simp only [map_add]
              exact congrArg₂ (· + ·) hz hz'
      | add y y' hy hy' =>
          simp only [map_add, LinearMap.add_apply]
          exact congrArg₂ (· + ·) hy hy'
  | add x x' hx hx' =>
      simp only [map_add, LinearMap.add_apply]
      exact congrArg₂ (· + ·) hx hx'

/-- **The left unit law on sections**, across the degree identification. -/
theorem mulSec_one_mul (U : ((Spec R).Opens)ᵒᵖ) (i : ℤ)
    (x : Γ(Spec R, U.unop) ⊗[R] gradedPiece (R := R) M i) :
    tensorCongr (A := Γ(Spec R, U.unop)) (congrArg (gradedPiece (R := R) M) (zero_add i))
        (mulSec M U 0 i ((1 : Γ(Spec R, U.unop)) ⊗ₜ[R] oneG (R := R) M) x) = x := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
      rw [mulSec_tmul, tensorCongr_tmul]
      exact tmul_eq_tmul_of_coe_eq M (_root_.one_mul a) (_root_.one_mul (x : SymmetricAlgebra R M))
  | add x x' hx hx' =>
      simp only [map_add]
      exact congrArg₂ (· + ·) hx hx'

/-- **The right unit law on sections**, across the degree identification. -/
theorem mulSec_mul_one (U : ((Spec R).Opens)ᵒᵖ) (i : ℤ)
    (x : Γ(Spec R, U.unop) ⊗[R] gradedPiece (R := R) M i) :
    tensorCongr (A := Γ(Spec R, U.unop)) (congrArg (gradedPiece (R := R) M) (add_zero i))
        (mulSec M U i 0 x ((1 : Γ(Spec R, U.unop)) ⊗ₜ[R] oneG (R := R) M)) = x := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
      rw [mulSec_tmul, tensorCongr_tmul]
      exact tmul_eq_tmul_of_coe_eq M (_root_.mul_one a) (_root_.mul_one (x : SymmetricAlgebra R M))
  | add x x' hx hx' =>
      simp only [map_add, LinearMap.add_apply]
      exact congrArg₂ (· + ·) hx hx'

/-- **The base change of the symmetric algebra of `M`, as a graded algebra of presheaves of
`𝒪_{Spec R}`-modules.** -/
def presheafAlgebra : Stacks.GradedAlgebra (piecePresheaf M) where
  mul := mulPresheaf M
  one := onePresheaf M
  mul_assoc i j k U x y z :=
    heq_tensor_of_eq (congrArg (gradedPiece (R := R) M) (add_assoc i j k))
      (mulSec_assoc M U i j k x y z)
  one_mul i U x :=
    heq_tensor_of_eq (congrArg (gradedPiece (R := R) M) (zero_add i)) (mulSec_one_mul M U i x)
  mul_one i U x :=
    heq_tensor_of_eq (congrArg (gradedPiece (R := R) M) (add_zero i)) (mulSec_mul_one M U i x)

/-- The multiplication of two degree-one sections is symmetric. -/
theorem mulSec_comm_one (U : ((Spec R).Opens)ᵒᵖ)
    (p q : Γ(Spec R, U.unop) ⊗[R] gradedPiece (R := R) M 1) :
    mulSec M U 1 1 p q = mulSec M U 1 1 q p := by
  induction p using TensorProduct.inductionOn with
  | tmul a x =>
      induction q using TensorProduct.inductionOn with
      | tmul b y =>
          rw [mulSec_tmul, mulSec_tmul, mul_comm a b, symMulₗ_comm_one]
      | add q q' hq hq' =>
          simp only [map_add, LinearMap.add_apply]
          exact congrArg₂ (· + ·) hq hq'
  | add p p' hp hp' =>
      simp only [map_add, LinearMap.add_apply]
      exact congrArg₂ (· + ·) hp hp'

end Stacks.SymGraded
