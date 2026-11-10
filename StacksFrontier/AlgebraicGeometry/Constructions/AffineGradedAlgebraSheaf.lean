module

public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits
public import StacksFrontier.AlgebraicGeometry.AffineSymmetricAlgebra.BaseChange
public import StacksFrontier.AlgebraicGeometry.AffineSymmetricAlgebra.GradedPieces
public import StacksFrontier.AlgebraicGeometry.AffineSymmetricAlgebra.Transport

/-!
# The sheaf of graded algebras on `Spec A` attached to a graded `A`-algebra

Let `A` be a commutative ring and `B` an `A`-algebra graded by `A`-submodules. **This file
constructs the sheaf of graded `𝒪_{Spec A}`-algebras `B̃` whose degree-`n` homogeneous piece is
the associated sheaf `(𝒜 n)~` of the degree-`n` piece of `B`**, with the multiplication induced
by that of `B`, and records its quasi-coherence, its commutativity and the vanishing of its
negative-degree pieces.

This is the sheaf written `B̃` in [Stacks, Tag 0897], where the graded algebra `𝓑` of the
statement is *defined* as its pullback `f^* B̃` along `f : X ⟶ Spec A`; the pullback is
`Stacks.Conormal.gradedPullback`.

The pieces are the associated sheaves **on the nose**: `gradedTilde_piece_natCast` is an
equality, not an isomorphism, so a statement about `(𝒜 n)~` is a statement about the degree-`n`
piece of `B̃` with no comparison map interposed.

## Main definitions

* `Stacks.AffineGradedAlgebra.algebraSheaf`: the sheaf of graded algebras attached to a family
  `𝒞 : ℤ → Submodule A B` of `A`-submodules of `B` which is multiplicative and contains `1` in
  degree `0`.
* `Stacks.AffineGradedAlgebra.gradedTilde`: **`B̃`**, the case of an `ℕ`-graded algebra, its
  grading extended to `ℤ` by zero.

## Main results

* `Stacks.AffineGradedAlgebra.gradedTilde_piece_natCast`: the degree-`n` piece of `B̃` is
  `(𝒜 n)~`.
* `Stacks.AffineGradedAlgebra.algebraSheaf_mul_toTilde`: the multiplication on the comparison
  images of two base-changed sections is the comparison image of their product. Together with
  local bijectivity of `Stacks.AffineBaseChange.toTilde` this pins the multiplication down.
* `Stacks.AffineGradedAlgebra.algebraSheaf_mul_comm`: homogeneous multiplication commutes, in
  every pair of degrees.
* `Stacks.AffineGradedAlgebra.isZero_gradedTilde_piece`: the negative-degree pieces of `B̃`
  vanish, because `𝒜` is `ℕ`-graded.
* `Stacks.AffineGradedAlgebra.gradedTilde_piece_isQuasicoherent` and
  `isQuasicoherent_coprod_gradedTilde_piece`: every piece of `B̃` is quasi-coherent, and so is
  the coproduct of the nonnegative-degree pieces: a piece is an associated sheaf, and
  quasi-coherence on a scheme is stable under colimits.

## Implementation notes

The construction is `Stacks.GradedAlgebra.ofComparison` applied to the graded algebra of
presheaves `U ↦ 𝒪(U) ⊗_A 𝒞 n` along the comparison `Stacks.AffineBaseChange.toTilde`, which is
locally bijective. Nothing is sheafified: the homogeneous pieces are given, and the only thing
extended is the multiplication, which is a *sectionwise* bilinear family.

`Stacks.SymGraded.baseChangeBil` base-changes an `A`-bilinear map of `A`-modules to the sections
of the structure sheaf, and `Stacks.SymGraded.tensorCongr` and `heq_tensor_of_eq` discharge the
heterogeneous associativity, unit and commutativity laws, whose two sides live in the base
changes of two different — but equal — submodules because `(i + j) + k = i + (j + k)`,
`0 + i = i`, `i + 0 = i` and `i + j = j + i` are not definitional in `ℤ`.

## References

* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open scoped TensorProduct

universe u

namespace Stacks.AffineGradedAlgebra

variable {R : CommRingCat.{u}} {B : Type u} [CommRing B] [Algebra R B]
  (𝒞 : ℤ → Submodule R B)
  (hmul : ∀ (i j : ℤ) ⦃x y : B⦄, x ∈ 𝒞 i → y ∈ 𝒞 j → x * y ∈ 𝒞 (i + j))
  (hone : (1 : B) ∈ 𝒞 0)

/-! ### The graded multiplication, as a bilinear map of graded pieces -/

/-- **The graded multiplication of `B`**, as an `A`-bilinear map of graded pieces. -/
def mulₗ (i j : ℤ) : ↥(𝒞 i) →ₗ[R] ↥(𝒞 j) →ₗ[R] ↥(𝒞 (i + j)) :=
  LinearMap.mk₂ R
    (fun x y => ⟨(x : B) * (y : B), hmul i j x.2 y.2⟩)
    (fun _ _ _ => Subtype.ext (add_mul _ _ _))
    (fun c x y => Subtype.ext (smul_mul_assoc c (x : B) (y : B)))
    (fun _ _ _ => Subtype.ext (mul_add _ _ _))
    (fun c x y => Subtype.ext (mul_smul_comm c (x : B) (y : B)))

/-- The product of two homogeneous elements under `mulₗ` is their product in `B`. -/
@[simp]
theorem mulₗ_coe (i j : ℤ) (x : ↥(𝒞 i)) (y : ↥(𝒞 j)) :
    ((mulₗ 𝒞 hmul i j x y : ↥(𝒞 (i + j))) : B) = (x : B) * (y : B) := rfl

/-- The unit of `B`, as an element of the degree-zero piece. -/
def oneEl : ↥(𝒞 0) := ⟨1, hone⟩

/-- The underlying element of `oneEl` is `1`. -/
@[simp]
theorem oneEl_coe : ((oneEl 𝒞 hone : ↥(𝒞 0)) : B) = 1 := rfl

/-! ### The base change to the sections of the structure sheaf -/

/-- The degree-`n` graded piece of `B`, as an `A`-module. -/
abbrev pieceModule (n : ℤ) : ModuleCat.{u} R := ModuleCat.of R ↥(𝒞 n)

/-- **The degree-`n` piece of the base change of `B`**: the presheaf of `𝒪_{Spec A}`-modules
`U ↦ 𝒪(U) ⊗_A 𝒞 n`. -/
abbrev piecePresheaf (n : ℤ) : PresheafOfModules.{u} (Spec R).ringCatSheaf.obj :=
  AffineBaseChange.presheaf (pieceModule 𝒞 n)

/-- **The graded multiplication on sections.** -/
def mulSec (U : ((Spec R).Opens)ᵒᵖ) (i j : ℤ) :
    (Γ(Spec R, U.unop) ⊗[R] ↥(𝒞 i)) →ₗ[Γ(Spec R, U.unop)]
      ((Γ(Spec R, U.unop) ⊗[R] ↥(𝒞 j)) →ₗ[Γ(Spec R, U.unop)]
        (Γ(Spec R, U.unop) ⊗[R] ↥(𝒞 (i + j)))) :=
  SymGraded.baseChangeBil Γ(Spec R, U.unop) (mulₗ 𝒞 hmul i j)

/-- On pure tensors, `mulSec` multiplies the sections and the homogeneous elements:
`(a ⊗ x) * (b ⊗ y) = (a * b) ⊗ (x * y)`. -/
@[simp]
theorem mulSec_tmul (U : ((Spec R).Opens)ᵒᵖ) (i j : ℤ) (a b : Γ(Spec R, U.unop))
    (x : ↥(𝒞 i)) (y : ↥(𝒞 j)) :
    mulSec 𝒞 hmul U i j (a ⊗ₜ[R] x) (b ⊗ₜ[R] y) = (a * b) ⊗ₜ[R] mulₗ 𝒞 hmul i j x y :=
  SymGraded.baseChangeBil_tmul _ _ a b x y

/-- A restriction map of the base-changed graded piece, as an `A`-linear map. -/
def pieceRestrict {U V : ((Spec R).Opens)ᵒᵖ} (f : U ⟶ V) (n : ℤ) :
    (Γ(Spec R, U.unop) ⊗[R] ↥(𝒞 n)) →ₗ[R] (Γ(Spec R, V.unop) ⊗[R] ↥(𝒞 n)) :=
  LinearMap.rTensor _ (AffineBaseChange.specRestrictₗ (R := R) f.unop)

/-- On a pure tensor `a ⊗ x`, `pieceRestrict` restricts the section `a` and fixes `x`. -/
@[simp]
theorem pieceRestrict_tmul {U V : ((Spec R).Opens)ᵒᵖ} (f : U ⟶ V) (n : ℤ)
    (a : Γ(Spec R, U.unop)) (x : ↥(𝒞 n)) :
    pieceRestrict 𝒞 f n (a ⊗ₜ[R] x) =
      AffineBaseChange.specRestrictₗ (R := R) f.unop a ⊗ₜ[R] x := rfl

/-- The restriction maps of `piecePresheaf 𝒞 n` are given by `pieceRestrict`. -/
theorem pieceRestrict_eq {U V : ((Spec R).Opens)ᵒᵖ} (f : U ⟶ V) (n : ℤ)
    (x : (piecePresheaf 𝒞 n).obj U) :
    (piecePresheaf 𝒞 n).map f x = pieceRestrict 𝒞 f n x := rfl

/-- The multiplication on sections commutes with the restriction maps. -/
theorem mulSec_naturality {U V : ((Spec R).Opens)ᵒᵖ} (f : U ⟶ V) (i j : ℤ)
    (x : Γ(Spec R, U.unop) ⊗[R] ↥(𝒞 i)) (y : Γ(Spec R, U.unop) ⊗[R] ↥(𝒞 j)) :
    pieceRestrict 𝒞 f (i + j) (mulSec 𝒞 hmul U i j x y) =
      mulSec 𝒞 hmul V i j (pieceRestrict 𝒞 f i x) (pieceRestrict 𝒞 f j y) := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
      induction y using TensorProduct.inductionOn with
      | tmul b y =>
          rw [mulSec_tmul, pieceRestrict_tmul, pieceRestrict_tmul, pieceRestrict_tmul,
            mulSec_tmul]
          exact congrArg (fun c => c ⊗ₜ[R] mulₗ 𝒞 hmul i j x y)
            (AffineBaseChange.specRestrictₗ_mul f.unop a b)
      | add y y' hy hy' => rw [map_add, map_add, map_add, map_add, hy, hy']
  | add x x' hx hx' =>
      rw [map_add (mulSec 𝒞 hmul U i j), LinearMap.add_apply,
        map_add (pieceRestrict 𝒞 f (i + j)), hx, hx', map_add (pieceRestrict 𝒞 f i),
        map_add (mulSec 𝒞 hmul V i j), LinearMap.add_apply]

/-- **The graded multiplication**, as a bilinear map of presheaves of modules. -/
def mulPresheaf (i j : ℤ) :
    BilinearMap (piecePresheaf 𝒞 i) (piecePresheaf 𝒞 j) (piecePresheaf 𝒞 (i + j)) where
  app U := AddMonoidHom.mk' (fun x => (mulSec 𝒞 hmul U i j x).toAddMonoidHom)
    fun x x' => AddMonoidHom.ext fun y =>
      congrArg (fun g : (Γ(Spec R, U.unop) ⊗[R] ↥(𝒞 j)) →ₗ[Γ(Spec R, U.unop)]
          (Γ(Spec R, U.unop) ⊗[R] ↥(𝒞 (i + j))) => g y)
        (map_add (mulSec 𝒞 hmul U i j) x x')
  map_smul_left U r x y :=
    congrArg (fun g : (Γ(Spec R, U.unop) ⊗[R] ↥(𝒞 j)) →ₗ[Γ(Spec R, U.unop)]
        (Γ(Spec R, U.unop) ⊗[R] ↥(𝒞 (i + j))) => g y)
      ((mulSec 𝒞 hmul U i j).map_smul r x)
  map_smul_right U r x y := (mulSec 𝒞 hmul U i j x).map_smul r y
  naturality f x y := mulSec_naturality 𝒞 hmul f i j x y

/-- On sections over `U`, `mulPresheaf` is `mulSec`. -/
@[simp]
theorem mulPresheaf_app (i j : ℤ) (U : ((Spec R).Opens)ᵒᵖ)
    (x : (piecePresheaf 𝒞 i).obj U) (y : (piecePresheaf 𝒞 j).obj U) :
    (mulPresheaf 𝒞 hmul i j).app U x y = mulSec 𝒞 hmul U i j x y := rfl

/-- **The unit**, as a global section of the degree-zero piece. -/
def onePresheaf : (piecePresheaf 𝒞 0).sections :=
  PresheafOfModules.sectionsMk
    (fun U => (1 : Γ(Spec R, U.unop)) ⊗ₜ[R] oneEl 𝒞 hone)
    fun {U _} f => by
      change pieceRestrict 𝒞 f 0 ((1 : Γ(Spec R, U.unop)) ⊗ₜ[R] oneEl 𝒞 hone) = _
      rw [pieceRestrict_tmul]
      exact congrArg (fun c => c ⊗ₜ[R] oneEl 𝒞 hone)
        (AffineBaseChange.specRestrictₗ_one f.unop)

/-- The section of `onePresheaf` over `U` is `1 ⊗ 1`. -/
@[simp]
theorem onePresheaf_eval (U : ((Spec R).Opens)ᵒᵖ) :
    (onePresheaf 𝒞 hone).eval U = (1 : Γ(Spec R, U.unop)) ⊗ₜ[R] oneEl 𝒞 hone := rfl

/-! ### The graded-algebra laws on sections -/

/-- `tensorCongr` sends a pure tensor `a ⊗ x` to `a' ⊗ w` when `a = a'` and `x = w` in `B`. -/
private theorem tensorCongr_tmul_eq {U : ((Spec R).Opens)ᵒᵖ} {p q : Submodule R B} (h : p = q)
    {a a' : Γ(Spec R, U.unop)} {x : ↥p} {w : ↥q} (ha : a = a') (hx : (x : B) = w) :
    SymGraded.tensorCongr (A := Γ(Spec R, U.unop)) h (a ⊗ₜ[R] x) = a' ⊗ₜ[R] w := by
  rw [SymGraded.tensorCongr_tmul]
  exact congrArg₂ (fun (d : Γ(Spec R, U.unop)) (v : ↥q) => d ⊗ₜ[R] v) ha (Subtype.ext hx)

/-- **Associativity on sections**, across the degree identification. -/
theorem mulSec_assoc (U : ((Spec R).Opens)ᵒᵖ) (i j k : ℤ)
    (x : Γ(Spec R, U.unop) ⊗[R] ↥(𝒞 i)) (y : Γ(Spec R, U.unop) ⊗[R] ↥(𝒞 j))
    (z : Γ(Spec R, U.unop) ⊗[R] ↥(𝒞 k)) :
    SymGraded.tensorCongr (A := Γ(Spec R, U.unop)) (congrArg 𝒞 (add_assoc i j k))
        (mulSec 𝒞 hmul U (i + j) k (mulSec 𝒞 hmul U i j x y) z) =
      mulSec 𝒞 hmul U i (j + k) x (mulSec 𝒞 hmul U j k y z) := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
      induction y using TensorProduct.inductionOn with
      | tmul b y =>
          induction z using TensorProduct.inductionOn with
          | tmul c z =>
              rw [mulSec_tmul, mulSec_tmul, mulSec_tmul, mulSec_tmul]
              exact tensorCongr_tmul_eq _ (_root_.mul_assoc a b c)
                (_root_.mul_assoc (x : B) (y : B) (z : B))
          | add z z' hz hz' =>
              simp only [map_add, hz, hz']
      | add y y' hy hy' =>
          simp only [map_add, LinearMap.add_apply, hy, hy']
  | add x x' hx hx' =>
      simp only [map_add, LinearMap.add_apply, hx, hx']

/-- **The left unit law on sections**, across the degree identification. -/
theorem mulSec_one_mul (U : ((Spec R).Opens)ᵒᵖ) (i : ℤ)
    (x : Γ(Spec R, U.unop) ⊗[R] ↥(𝒞 i)) :
    SymGraded.tensorCongr (A := Γ(Spec R, U.unop)) (congrArg 𝒞 (zero_add i))
        (mulSec 𝒞 hmul U 0 i ((1 : Γ(Spec R, U.unop)) ⊗ₜ[R] oneEl 𝒞 hone) x) = x := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
      rw [mulSec_tmul]
      exact tensorCongr_tmul_eq _ (_root_.one_mul a) (_root_.one_mul (x : B))
  | add x x' hx hx' =>
      simp only [map_add, hx, hx']

/-- **The right unit law on sections**, across the degree identification. -/
theorem mulSec_mul_one (U : ((Spec R).Opens)ᵒᵖ) (i : ℤ)
    (x : Γ(Spec R, U.unop) ⊗[R] ↥(𝒞 i)) :
    SymGraded.tensorCongr (A := Γ(Spec R, U.unop)) (congrArg 𝒞 (add_zero i))
        (mulSec 𝒞 hmul U i 0 x ((1 : Γ(Spec R, U.unop)) ⊗ₜ[R] oneEl 𝒞 hone)) = x := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
      rw [mulSec_tmul]
      exact tensorCongr_tmul_eq _ (_root_.mul_one a) (_root_.mul_one (x : B))
  | add x x' hx hx' =>
      simp only [map_add, LinearMap.add_apply, hx, hx']

/-- **Commutativity on sections**, across the degree identification. -/
theorem mulSec_comm (U : ((Spec R).Opens)ᵒᵖ) (i j : ℤ)
    (x : Γ(Spec R, U.unop) ⊗[R] ↥(𝒞 i)) (y : Γ(Spec R, U.unop) ⊗[R] ↥(𝒞 j)) :
    SymGraded.tensorCongr (A := Γ(Spec R, U.unop)) (congrArg 𝒞 (add_comm i j))
        (mulSec 𝒞 hmul U i j x y) = mulSec 𝒞 hmul U j i y x := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
      induction y using TensorProduct.inductionOn with
      | tmul b y =>
          rw [mulSec_tmul, mulSec_tmul]
          exact tensorCongr_tmul_eq _ (mul_comm a b) (mul_comm (x : B) (y : B))
      | add y y' hy hy' =>
          simp only [map_add, LinearMap.add_apply, hy, hy']
  | add x x' hx hx' =>
      simp only [map_add, LinearMap.add_apply, hx, hx']

/-- **The base change of `B` to the structure sheaf, as a graded algebra of presheaves of
`𝒪_{Spec A}`-modules.** -/
def presheafAlgebra : Stacks.GradedAlgebra (piecePresheaf 𝒞) where
  mul := mulPresheaf 𝒞 hmul
  one := onePresheaf 𝒞 hone
  mul_assoc i j k U x y z :=
    SymGraded.heq_tensor_of_eq (congrArg 𝒞 (add_assoc i j k))
      (mulSec_assoc 𝒞 hmul U i j k x y z)
  one_mul i U x :=
    SymGraded.heq_tensor_of_eq (congrArg 𝒞 (zero_add i)) (mulSec_one_mul 𝒞 hmul hone U i x)
  mul_one i U x :=
    SymGraded.heq_tensor_of_eq (congrArg 𝒞 (add_zero i)) (mulSec_mul_one 𝒞 hmul hone U i x)

/-! ### The sheaf of graded algebras -/

/-- The associated sheaf of the degree-`n` graded piece of `B`. -/
abbrev pieceSheaf (n : ℤ) : SheafOfModules.{u} (Spec R).ringCatSheaf :=
  tilde (pieceModule 𝒞 n)

/-- The comparison from the base-change presheaf of the degree-`n` graded piece to its
associated sheaf. -/
abbrev pieceCmp (n : ℤ) : piecePresheaf 𝒞 n ⟶ (pieceSheaf 𝒞 n).val :=
  AffineBaseChange.toTilde (pieceModule 𝒞 n)

/-- **The sheaf of graded `𝒪_{Spec A}`-algebras attached to a graded `A`-algebra**, whose
degree-`n` piece is the associated sheaf of the degree-`n` piece of `B`. -/
def algebraSheaf : SheafOfModules.GradedAlgebra.{u, u} (Spec R).ringCatSheaf :=
  (presheafAlgebra 𝒞 hmul hone).ofComparison (pieceSheaf 𝒞) (pieceCmp 𝒞)

/-- The degree-`n` piece of `algebraSheaf` is `pieceSheaf 𝒞 n`. -/
theorem algebraSheaf_piece (n : ℤ) :
    (algebraSheaf 𝒞 hmul hone).piece n = pieceSheaf 𝒞 n := rfl

/-- The multiplication of `algebraSheaf` on the comparison images of two base-changed local
sections. -/
theorem algebraSheaf_mul_toTilde (i j : ℤ) (U : ((Spec R).Opens)ᵒᵖ)
    (x : (piecePresheaf 𝒞 i).obj U) (y : (piecePresheaf 𝒞 j).obj U) :
    ((algebraSheaf 𝒞 hmul hone).mul i j).app U
        (PresheafOfModules.Hom.app (pieceCmp 𝒞 i) U x)
        (PresheafOfModules.Hom.app (pieceCmp 𝒞 j) U y) =
      PresheafOfModules.Hom.app (pieceCmp 𝒞 (i + j)) U (mulSec 𝒞 hmul U i j x y) :=
  (presheafAlgebra 𝒞 hmul hone).ofComparison_mul_comparison (pieceSheaf 𝒞) (pieceCmp 𝒞) i j U x y

/-- The unit of `algebraSheaf` over `U` is the comparison image of `1 ⊗ 1`. -/
theorem algebraSheaf_one_eval (U : ((Spec R).Opens)ᵒᵖ) :
    (algebraSheaf 𝒞 hmul hone).one.eval U =
      PresheafOfModules.Hom.app (pieceCmp 𝒞 0) U
        ((1 : Γ(Spec R, U.unop)) ⊗ₜ[R] oneEl 𝒞 hone) :=
  rfl

/-- **Homogeneous multiplication in `algebraSheaf` commutes**, in every pair of degrees. -/
theorem algebraSheaf_mul_comm (i j : ℤ) (W : ((Spec R).Opens)ᵒᵖ)
    (a : ((algebraSheaf 𝒞 hmul hone).piece i).val.obj W)
    (b : ((algebraSheaf 𝒞 hmul hone).piece j).val.obj W) :
    HEq (((algebraSheaf 𝒞 hmul hone).mul i j).app W a b)
      (((algebraSheaf 𝒞 hmul hone).mul j i).app W b a) :=
  (presheafAlgebra 𝒞 hmul hone).ofComparison_mul_comm (pieceSheaf 𝒞) (pieceCmp 𝒞)
    (fun i j U x y => SymGraded.heq_tensor_of_eq (congrArg 𝒞 (add_comm i j))
      (mulSec_comm 𝒞 hmul U i j x y)) i j W a b

/-! ### Quasi-coherence, and the vanishing of a piece -/

/-- **Every homogeneous piece of `algebraSheaf` is quasi-coherent**: it is an associated
sheaf. -/
instance pieceSheaf_isQuasicoherent (n : ℤ) : (pieceSheaf 𝒞 n).IsQuasicoherent :=
  inferInstanceAs (tilde (pieceModule 𝒞 n)).IsQuasicoherent

/-- Every homogeneous piece of `algebraSheaf` is quasi-coherent. -/
theorem algebraSheaf_piece_isQuasicoherent (n : ℤ) :
    ((algebraSheaf 𝒞 hmul hone).piece n).IsQuasicoherent :=
  pieceSheaf_isQuasicoherent 𝒞 n

/-- **The coproduct of the nonnegative-degree pieces of `algebraSheaf` is quasi-coherent.**
Quasi-coherence on a scheme is stable under colimits of any shape, so this needs nothing of the
grading. -/
theorem isQuasicoherent_coprod_pieceSheaf
    [HasCoproduct fun n : ℕ => pieceSheaf 𝒞 (n : ℤ)] :
    (∐ fun n : ℕ => pieceSheaf 𝒞 (n : ℤ)).IsQuasicoherent :=
  Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_colimit
    (Discrete.functor fun n : ℕ => pieceSheaf 𝒞 (n : ℤ))
    fun n => pieceSheaf_isQuasicoherent 𝒞 (n.as : ℤ)

/-- A homogeneous piece of `algebraSheaf` whose graded piece in `B` is zero vanishes. -/
theorem isZero_pieceSheaf_of_eq_bot {n : ℤ} (h : 𝒞 n = ⊥) : IsZero (pieceSheaf 𝒞 n) := by
  have hsub : Subsingleton ↥(𝒞 n) := by rw [h]; infer_instance
  exact (tilde.functor R).map_isZero (ModuleCat.isZero_of_subsingleton (pieceModule 𝒞 n))

/-! ### An `ℕ`-graded algebra -/

section Nat

variable {R : CommRingCat.{u}} {B : Type u} [CommRing B] [Algebra R B]
  (𝒜 : ℕ → Submodule R B)

/-- **The grading of an `ℕ`-graded algebra, extended to `ℤ` by zero.** The definition is by a
match on `Int`, so that its value at a natural number is the given piece by `rfl`. -/
def intPiece : ℤ → Submodule R B
  | .ofNat n => 𝒜 n
  | .negSucc _ => ⊥

/-- At a natural number `n`, `intPiece 𝒜` is `𝒜 n`. -/
theorem intPiece_natCast (n : ℕ) : intPiece 𝒜 (n : ℤ) = 𝒜 n := rfl

/-- At `-(n + 1)`, `intPiece 𝒜` is zero. -/
theorem intPiece_negSucc (n : ℕ) : intPiece 𝒜 (Int.negSucc n) = ⊥ := rfl

/-- At a negative integer, `intPiece 𝒜` is zero. -/
theorem intPiece_eq_bot_of_neg {n : ℤ} (hn : n < 0) : intPiece 𝒜 n = ⊥ := by
  match n with
  | .ofNat k => exact absurd hn (not_lt.mpr (Int.natCast_nonneg k))
  | .negSucc k => rfl

variable [SetLike.GradedMonoid 𝒜]

/-- The unit lies in degree zero. -/
theorem one_mem_intPiece : (1 : B) ∈ intPiece 𝒜 0 := SetLike.one_mem_graded 𝒜

/-- **The extended grading is multiplicative.** -/
theorem mul_mem_intPiece (i j : ℤ) ⦃x y : B⦄ (hx : x ∈ intPiece 𝒜 i)
    (hy : y ∈ intPiece 𝒜 j) : x * y ∈ intPiece 𝒜 (i + j) := by
  match i, j with
  | .ofNat a, .ofNat b =>
      change x * y ∈ 𝒜 (a + b)
      exact SetLike.mul_mem_graded hx hy
  | .ofNat _, .negSucc _ =>
      rw [show y = 0 from hy, mul_zero]
      exact Submodule.zero_mem _
  | .negSucc _, _ =>
      rw [show x = 0 from hx, zero_mul]
      exact Submodule.zero_mem _

/-- **`B̃`, the sheaf of graded `𝒪_{Spec A}`-algebras attached to an `ℕ`-graded `A`-algebra
`B`**: its degree-`n` piece is the associated sheaf `(𝒜 n)~` for `n ≥ 0`, and zero otherwise.

This is the sheaf written `B̃` in [Stacks, Tag 0897], whose pullback `f^* B̃` along
`f : X ⟶ Spec A` is the graded algebra `𝓑` of that statement. -/
def gradedTilde : SheafOfModules.GradedAlgebra.{u, u} (Spec R).ringCatSheaf :=
  algebraSheaf (intPiece 𝒜) (mul_mem_intPiece 𝒜) (one_mem_intPiece 𝒜)

/-- The degree-`n` piece of `gradedTilde 𝒜` is the associated sheaf of `intPiece 𝒜 n`. -/
theorem gradedTilde_piece (n : ℤ) :
    (gradedTilde 𝒜).piece n = tilde (ModuleCat.of R ↥(intPiece 𝒜 n)) := rfl

/-- **The degree-`n` piece of `B̃` is the associated sheaf of the degree-`n` piece of `B`**, on
the nose. -/
theorem gradedTilde_piece_natCast (n : ℕ) :
    (gradedTilde 𝒜).piece (n : ℤ) = tilde (ModuleCat.of R ↥(𝒜 n)) := rfl

/-- **Every homogeneous piece of `B̃` is quasi-coherent.** -/
theorem gradedTilde_piece_isQuasicoherent (n : ℤ) : ((gradedTilde 𝒜).piece n).IsQuasicoherent :=
  algebraSheaf_piece_isQuasicoherent (intPiece 𝒜) (mul_mem_intPiece 𝒜) (one_mem_intPiece 𝒜) n

/-- **Homogeneous multiplication in `B̃` commutes**, in every pair of degrees, because `B` is
commutative. -/
theorem gradedTilde_mul_comm (i j : ℤ) (W : ((Spec R).Opens)ᵒᵖ)
    (a : ((gradedTilde 𝒜).piece i).val.obj W) (b : ((gradedTilde 𝒜).piece j).val.obj W) :
    HEq (((gradedTilde 𝒜).mul i j).app W a b) (((gradedTilde 𝒜).mul j i).app W b a) :=
  algebraSheaf_mul_comm (intPiece 𝒜) (mul_mem_intPiece 𝒜) (one_mem_intPiece 𝒜) i j W a b

/-- **The negative-degree pieces of `B̃` vanish**, because `𝒜` is `ℕ`-graded. -/
theorem isZero_gradedTilde_piece (n : ℤ) (hn : n < 0) : IsZero ((gradedTilde 𝒜).piece n) :=
  isZero_pieceSheaf_of_eq_bot (intPiece 𝒜) (intPiece_eq_bot_of_neg 𝒜 hn)

/-- **The coproduct of the nonnegative-degree pieces of `B̃` is quasi-coherent.** -/
theorem isQuasicoherent_coprod_gradedTilde_piece
    [HasCoproduct fun n : ℕ => (gradedTilde 𝒜).piece (n : ℤ)] :
    (∐ fun n : ℕ => (gradedTilde 𝒜).piece (n : ℤ)).IsQuasicoherent :=
  isQuasicoherent_coprod_pieceSheaf (intPiece 𝒜)

end Nat

/-- **`B̃` for a graded algebra over a bare commutative ring.** This is
`Stacks.AffineGradedAlgebra.gradedTilde` with the base presented as `A` rather than as an object
of `CommRingCat`. -/
abbrev gradedTildeOf (A : Type u) [CommRing A] {B : Type u} [CommRing B] [Algebra A B]
    (𝒜 : ℕ → Submodule A B) [SetLike.GradedMonoid 𝒜] :
    SheafOfModules.GradedAlgebra.{u, u} (Spec (CommRingCat.of A)).ringCatSheaf :=
  gradedTilde (R := CommRingCat.of A) 𝒜

end Stacks.AffineGradedAlgebra

end
