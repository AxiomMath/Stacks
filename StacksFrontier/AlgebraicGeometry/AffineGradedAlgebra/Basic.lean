module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedForgetColimits
public import StacksFrontier.AlgebraicGeometry.AffineSymmetricAlgebra.BaseChange
public import StacksFrontier.AlgebraicGeometry.AffineSymmetricAlgebra.GradedPieces
public import StacksFrontier.AlgebraicGeometry.AffineSymmetricAlgebra.Transport

/-!
# The sheaf of graded algebras on `Spec R` attached to a graded `R`-algebra

Let `R` be a commutative ring, `S` a commutative `R`-algebra and `𝒢 : ℤ → Submodule R S` a
`ℤ`-indexed family of `R`-submodules containing `1` in degree `0` and satisfying
`𝒢 i · 𝒢 j ⊆ 𝒢 (i + j)`, i.e. a `SetLike.GradedMonoid`. **This file builds the sheaf of graded
`𝒪_{Spec R}`-algebras whose degree-`n` homogeneous piece is the associated sheaf `(𝒢 n)~.**

The pieces are the associated sheaves **on the nose**, so a statement about `(𝒢 n)~` is a
statement about the degree-`n` piece with no comparison map interposed.

The construction is `Stacks.GradedAlgebra.ofComparison` applied to the graded algebra of
base-change presheaves `U ↦ 𝒪(U) ⊗_R 𝒢 n` along `Stacks.AffineBaseChange.toTilde`, which is
locally bijective; nothing is sheafified. It is the same route by which
`Stacks.SymGraded.symAlgebra` is built for the symmetric algebra of a module, run for an
arbitrary graded algebra, and it reuses that development's two algebraic tools — the base change
`Stacks.SymGraded.baseChangeBil` of a bilinear map, and the heterogeneous equality
`Stacks.SymGraded.heq_tensor_of_eq` across an equality of submodules.

## Main definitions

* `Stacks.SpecGraded.mulₗ` and `Stacks.SpecGraded.gOne`: the graded multiplication of `𝒢` as an
  `R`-bilinear map of pieces, and its unit.
* `Stacks.SpecGraded.presheafAlgebra`: the base change of `𝒢` to sections, as a graded algebra
  of presheaves of `𝒪_{Spec R}`-modules.
* `Stacks.SpecGraded.specGradedAlgebra`: **the sheaf of graded algebras.**

## Main results

* `Stacks.SpecGraded.specGradedAlgebra_mul_toTilde`: the multiplication on the comparison images
  of two base-changed sections is the comparison image of their product. Together with local
  bijectivity of `Stacks.AffineBaseChange.toTilde` this pins the multiplication down.
* `Stacks.SpecGraded.homogeneousSection_gOne` and
  `Stacks.SpecGraded.castHom_homogeneousSection_mul`: **the global section named by a homogeneous
  element of `S`** is unital and multiplicative. The second is stated with the product's degree
  and its image in `S` as separate data, so that the two factors may be read in either order.
* `Stacks.SpecGraded.specGradedAlgebra_mul_comm`: **the homogeneous multiplication is
  commutative**, in the heterogeneous form that
  `Stacks.RelativeSpec.gradedAlgebraSheaf` asks for before it will read a sheaf of graded
  algebras as a sheaf of commutative algebras. This is what lets the relative spectrum be
  formed.
* `Stacks.SpecGraded.isQuasicoherent_specGradedAlgebra_piece` and
  `Stacks.SpecGraded.isZero_specGradedAlgebra_piece`: the pieces are quasi-coherent, and the
  pieces of vanishing degrees vanish.

## References

* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite PresheafOfModules
open Stacks.SymGraded (baseChangeBil baseChangeBil_tmul tensorCongr tensorCongr_tmul
  tensorCongr_self heq_tensor_of_eq)
open scoped TensorProduct

universe u

namespace Stacks.SpecGraded

variable {R : CommRingCat.{u}} {S : Type u} [CommRing S] [Algebra R S]
  (𝒢 : ℤ → Submodule R S) [SetLike.GradedMonoid 𝒢]

/-! ### The graded multiplication of a graded algebra -/

/-- The degree-`n` piece of `𝒢`, as an `R`-module. -/
abbrev pieceModule (n : ℤ) : ModuleCat.{u} R := ModuleCat.of R (𝒢 n)

/-- **The graded multiplication**, as an `R`-bilinear map of homogeneous pieces. -/
def mulₗ (i j : ℤ) : 𝒢 i →ₗ[R] 𝒢 j →ₗ[R] 𝒢 (i + j) :=
  LinearMap.mk₂ R
    (fun x y => ⟨(x : S) * (y : S), SetLike.mul_mem_graded x.2 y.2⟩)
    (fun _ _ _ => Subtype.ext (add_mul _ _ _))
    (fun c x y => Subtype.ext (smul_mul_assoc c (x : S) (y : S)))
    (fun _ _ _ => Subtype.ext (mul_add _ _ _))
    (fun c x y => Subtype.ext (mul_smul_comm c (x : S) (y : S)))

/-- The unit of `S`, as a degree-zero element. -/
def gOne : 𝒢 0 := ⟨1, SetLike.one_mem_graded 𝒢⟩

/-! ### The base change to sections -/

/-- **The degree-`n` piece of the base change of `𝒢`**: the presheaf of `𝒪_{Spec R}`-modules
`U ↦ 𝒪(U) ⊗_R 𝒢 n`. -/
abbrev piecePresheaf (n : ℤ) : PresheafOfModules.{u} (Spec R).ringCatSheaf.obj :=
  AffineBaseChange.presheaf (pieceModule 𝒢 n)

/-- **The graded multiplication on sections.** -/
def mulSec (U : ((Spec R).Opens)ᵒᵖ) (i j : ℤ) :
    (Γ(Spec R, U.unop) ⊗[R] 𝒢 i) →ₗ[Γ(Spec R, U.unop)]
      ((Γ(Spec R, U.unop) ⊗[R] 𝒢 j) →ₗ[Γ(Spec R, U.unop)]
        (Γ(Spec R, U.unop) ⊗[R] 𝒢 (i + j))) :=
  baseChangeBil Γ(Spec R, U.unop) (mulₗ 𝒢 i j)

/-- The multiplication on sections of two pure tensors `a ⊗ x` and `b ⊗ y` is
`(a * b) ⊗ (x * y)`. -/
@[simp]
theorem mulSec_tmul (U : ((Spec R).Opens)ᵒᵖ) (i j : ℤ) (a b : Γ(Spec R, U.unop))
    (x : 𝒢 i) (y : 𝒢 j) :
    mulSec 𝒢 U i j (a ⊗ₜ[R] x) (b ⊗ₜ[R] y) = (a * b) ⊗ₜ[R] mulₗ 𝒢 i j x y :=
  baseChangeBil_tmul _ _ a b x y

/-- A restriction map of the base-changed piece, as an `R`-linear map. -/
def pieceRestrict {U V : ((Spec R).Opens)ᵒᵖ} (f : U ⟶ V) (n : ℤ) :
    (Γ(Spec R, U.unop) ⊗[R] 𝒢 n) →ₗ[R] (Γ(Spec R, V.unop) ⊗[R] 𝒢 n) :=
  LinearMap.rTensor _ (AffineBaseChange.specRestrictₗ (R := R) f.unop)

omit [SetLike.GradedMonoid 𝒢] in
/-- The restriction of a pure tensor `a ⊗ x` is the restriction of `a` tensored with `x`. -/
@[simp]
theorem pieceRestrict_tmul {U V : ((Spec R).Opens)ᵒᵖ} (f : U ⟶ V) (n : ℤ)
    (a : Γ(Spec R, U.unop)) (x : 𝒢 n) :
    pieceRestrict 𝒢 f n (a ⊗ₜ[R] x) =
      AffineBaseChange.specRestrictₗ (R := R) f.unop a ⊗ₜ[R] x := rfl

/-- The multiplication on sections commutes with the restriction maps. -/
theorem mulSec_naturality {U V : ((Spec R).Opens)ᵒᵖ} (f : U ⟶ V) (i j : ℤ)
    (x : Γ(Spec R, U.unop) ⊗[R] 𝒢 i) (y : Γ(Spec R, U.unop) ⊗[R] 𝒢 j) :
    pieceRestrict 𝒢 f (i + j) (mulSec 𝒢 U i j x y) =
      mulSec 𝒢 V i j (pieceRestrict 𝒢 f i x) (pieceRestrict 𝒢 f j y) := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
      induction y using TensorProduct.inductionOn with
      | tmul b y =>
          rw [mulSec_tmul, pieceRestrict_tmul, pieceRestrict_tmul, pieceRestrict_tmul,
            mulSec_tmul]
          exact congrArg (fun c => c ⊗ₜ[R] mulₗ 𝒢 i j x y)
            (AffineBaseChange.specRestrictₗ_mul f.unop a b)
      | add y y' hy hy' => rw [map_add, map_add, map_add, map_add, hy, hy']
  | add x x' hx hx' =>
      rw [map_add (mulSec 𝒢 U i j), LinearMap.add_apply, map_add (pieceRestrict 𝒢 f (i + j)),
        hx, hx', map_add (pieceRestrict 𝒢 f i), map_add (mulSec 𝒢 V i j), LinearMap.add_apply]

/-- **The graded multiplication**, as a bilinear map of presheaves of modules. -/
def mulPresheaf (i j : ℤ) :
    BilinearMap (piecePresheaf 𝒢 i) (piecePresheaf 𝒢 j) (piecePresheaf 𝒢 (i + j)) where
  app U := AddMonoidHom.mk' (fun x => (mulSec 𝒢 U i j x).toAddMonoidHom)
    fun x x' => AddMonoidHom.ext fun y =>
      congrArg (fun g : (Γ(Spec R, U.unop) ⊗[R] 𝒢 j) →ₗ[Γ(Spec R, U.unop)]
          (Γ(Spec R, U.unop) ⊗[R] 𝒢 (i + j)) => g y)
        (map_add (mulSec 𝒢 U i j) x x')
  map_smul_left U r x y :=
    congrArg (fun g : (Γ(Spec R, U.unop) ⊗[R] 𝒢 j) →ₗ[Γ(Spec R, U.unop)]
        (Γ(Spec R, U.unop) ⊗[R] 𝒢 (i + j)) => g y)
      ((mulSec 𝒢 U i j).map_smul r x)
  map_smul_right U r x y := (mulSec 𝒢 U i j x).map_smul r y
  naturality f x y := mulSec_naturality 𝒢 f i j x y

/-- **The unit**, as a global section of the degree-zero piece. -/
def onePresheaf : (piecePresheaf 𝒢 0).sections :=
  PresheafOfModules.sectionsMk (fun U => (1 : Γ(Spec R, U.unop)) ⊗ₜ[R] gOne 𝒢)
    fun {U _} f => by
      change pieceRestrict 𝒢 f 0 ((1 : Γ(Spec R, U.unop)) ⊗ₜ[R] gOne 𝒢) = _
      rw [pieceRestrict_tmul]
      exact congrArg (fun c => c ⊗ₜ[R] gOne 𝒢) (AffineBaseChange.specRestrictₗ_one f.unop)

/-! ### The graded-algebra laws on sections -/

/-- Pure tensors in a piece are equal when their scalars agree and their values in `S` agree. -/
private theorem tmul_congr_of_val_eq {A : Type*} [CommSemiring A] [Algebra R A] {p : Submodule R S}
    {a a' : A} {x y : p} (ha : a = a') (hxy : (x : S) = (y : S)) :
    a ⊗ₜ[R] x = a' ⊗ₜ[R] y :=
  congrArg₂ (· ⊗ₜ[R] ·) ha (Subtype.ext hxy)

/-- **Associativity on sections**, across the degree identification. -/
theorem mulSec_assoc (U : ((Spec R).Opens)ᵒᵖ) (i j k : ℤ)
    (x : Γ(Spec R, U.unop) ⊗[R] 𝒢 i) (y : Γ(Spec R, U.unop) ⊗[R] 𝒢 j)
    (z : Γ(Spec R, U.unop) ⊗[R] 𝒢 k) :
    tensorCongr (A := Γ(Spec R, U.unop)) (congrArg 𝒢 (add_assoc i j k))
        (mulSec 𝒢 U (i + j) k (mulSec 𝒢 U i j x y) z) =
      mulSec 𝒢 U i (j + k) x (mulSec 𝒢 U j k y z) := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
      induction y using TensorProduct.inductionOn with
      | tmul b y =>
          induction z using TensorProduct.inductionOn with
          | tmul c z =>
              rw [mulSec_tmul, mulSec_tmul, mulSec_tmul, mulSec_tmul, tensorCongr_tmul]
              exact tmul_congr_of_val_eq (_root_.mul_assoc a b c) (_root_.mul_assoc (x : S) y z)
          | add z z' hz hz' =>
              simp only [map_add, hz, hz']
      | add y y' hy hy' =>
          simp only [map_add, LinearMap.add_apply, hy, hy']
  | add x x' hx hx' =>
      simp only [map_add, LinearMap.add_apply, hx, hx']

/-- **The left unit law on sections**, across the degree identification. -/
theorem mulSec_one_mul (U : ((Spec R).Opens)ᵒᵖ) (i : ℤ)
    (x : Γ(Spec R, U.unop) ⊗[R] 𝒢 i) :
    tensorCongr (A := Γ(Spec R, U.unop)) (congrArg 𝒢 (zero_add i))
        (mulSec 𝒢 U 0 i ((1 : Γ(Spec R, U.unop)) ⊗ₜ[R] gOne 𝒢) x) = x := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
      rw [mulSec_tmul, tensorCongr_tmul]
      exact tmul_congr_of_val_eq (_root_.one_mul a) (_root_.one_mul (x : S))
  | add x x' hx hx' =>
      simp only [map_add, hx, hx']

/-- **The right unit law on sections**, across the degree identification. -/
theorem mulSec_mul_one (U : ((Spec R).Opens)ᵒᵖ) (i : ℤ)
    (x : Γ(Spec R, U.unop) ⊗[R] 𝒢 i) :
    tensorCongr (A := Γ(Spec R, U.unop)) (congrArg 𝒢 (add_zero i))
        (mulSec 𝒢 U i 0 x ((1 : Γ(Spec R, U.unop)) ⊗ₜ[R] gOne 𝒢)) = x := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
      rw [mulSec_tmul, tensorCongr_tmul]
      exact tmul_congr_of_val_eq (_root_.mul_one a) (_root_.mul_one (x : S))
  | add x x' hx hx' =>
      simp only [map_add, LinearMap.add_apply, hx, hx']

/-- **Commutativity on sections**, across the degree identification. -/
theorem mulSec_comm (U : ((Spec R).Opens)ᵒᵖ) (i j : ℤ)
    (x : Γ(Spec R, U.unop) ⊗[R] 𝒢 i) (y : Γ(Spec R, U.unop) ⊗[R] 𝒢 j) :
    tensorCongr (A := Γ(Spec R, U.unop)) (congrArg 𝒢 (add_comm i j))
        (mulSec 𝒢 U i j x y) = mulSec 𝒢 U j i y x := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
      induction y using TensorProduct.inductionOn with
      | tmul b y =>
          rw [mulSec_tmul, mulSec_tmul, tensorCongr_tmul]
          exact tmul_congr_of_val_eq (_root_.mul_comm a b) (_root_.mul_comm (x : S) y)
      | add y y' hy hy' =>
          simp only [map_add, LinearMap.add_apply, hy, hy']
  | add x x' hx hx' =>
      simp only [map_add, LinearMap.add_apply, hx, hx']

/-- **The base change of `𝒢`, as a graded algebra of presheaves of `𝒪_{Spec R}`-modules.** -/
def presheafAlgebra : Stacks.GradedAlgebra (piecePresheaf 𝒢) where
  mul := mulPresheaf 𝒢
  one := onePresheaf 𝒢
  mul_assoc i j k U x y z :=
    heq_tensor_of_eq (congrArg 𝒢 (add_assoc i j k)) (mulSec_assoc 𝒢 U i j k x y z)
  one_mul i U x := heq_tensor_of_eq (congrArg 𝒢 (zero_add i)) (mulSec_one_mul 𝒢 U i x)
  mul_one i U x := heq_tensor_of_eq (congrArg 𝒢 (add_zero i)) (mulSec_mul_one 𝒢 U i x)

/-- The heterogeneous form of commutativity at the level of the presheaf algebra. -/
theorem presheafAlgebra_mul_comm (i j : ℤ) (U : ((Spec R).Opens)ᵒᵖ)
    (x : (piecePresheaf 𝒢 i).obj U) (y : (piecePresheaf 𝒢 j).obj U) :
    HEq (((presheafAlgebra 𝒢).mul i j).app U x y) (((presheafAlgebra 𝒢).mul j i).app U y x) :=
  heq_tensor_of_eq (congrArg 𝒢 (add_comm i j)) (mulSec_comm 𝒢 U i j x y)

/-! ### The sheaf of graded algebras -/

/-- The associated sheaf of the degree-`n` piece. -/
abbrev pieceSheaf (n : ℤ) : SheafOfModules.{u} (Spec R).ringCatSheaf :=
  tilde (pieceModule 𝒢 n)

/-- The comparison from the base-change presheaf of the degree-`n` piece to its associated
sheaf. -/
abbrev pieceCmp (n : ℤ) : piecePresheaf 𝒢 n ⟶ (pieceSheaf 𝒢 n).val :=
  AffineBaseChange.toTilde (pieceModule 𝒢 n)

/-- **The sheaf of graded `𝒪_{Spec R}`-algebras attached to the graded `R`-algebra `𝒢`**, with
degree-`n` homogeneous piece the associated sheaf `(𝒢 n)~`. -/
def specGradedAlgebra : SheafOfModules.GradedAlgebra.{u, u} (Spec R).ringCatSheaf :=
  (presheafAlgebra 𝒢).ofComparison (pieceSheaf 𝒢) (pieceCmp 𝒢)

/-- The multiplication of `specGradedAlgebra 𝒢` on the comparison images of two base-changed
local sections. -/
theorem specGradedAlgebra_mul_toTilde (i j : ℤ) (U : ((Spec R).Opens)ᵒᵖ)
    (x : (piecePresheaf 𝒢 i).obj U) (y : (piecePresheaf 𝒢 j).obj U) :
    ((specGradedAlgebra 𝒢).mul i j).app U
        (PresheafOfModules.Hom.app (pieceCmp 𝒢 i) U x)
        (PresheafOfModules.Hom.app (pieceCmp 𝒢 j) U y) =
      PresheafOfModules.Hom.app (pieceCmp 𝒢 (i + j)) U (mulSec 𝒢 U i j x y) :=
  (presheafAlgebra 𝒢).ofComparison_mul_comparison (pieceSheaf 𝒢) (pieceCmp 𝒢) i j U x y

/-- The unit of `specGradedAlgebra 𝒢` on `U` is the comparison image of `1 ⊗ 1`. -/
theorem specGradedAlgebra_one_eval (U : ((Spec R).Opens)ᵒᵖ) :
    (specGradedAlgebra 𝒢).one.eval U =
      PresheafOfModules.Hom.app (pieceCmp 𝒢 0) U ((1 : Γ(Spec R, U.unop)) ⊗ₜ[R] gOne 𝒢) :=
  rfl

/-- **The homogeneous multiplication of `specGradedAlgebra 𝒢` is commutative.** This is the
datum `Stacks.RelativeSpec.gradedAlgebraSheaf` asks for before it will read a sheaf of graded
algebras as a sheaf of commutative `𝒪_{Spec R}`-algebras, so it is what lets the relative
spectrum be formed.

A general local section of a piece is only *locally* a comparison image, so the identity cannot
be read off `specGradedAlgebra_mul_toTilde` directly: it is proved on the covering sieve of local
lifts, where `Stacks.GradedAlgebra.ofComparison_mul_restrict` reduces it to
`presheafAlgebra_mul_comm`. -/
theorem specGradedAlgebra_mul_comm (i j : ℤ) (U : ((Spec R).Opens)ᵒᵖ)
    (a : ((specGradedAlgebra 𝒢).piece i).val.obj U)
    (b : ((specGradedAlgebra 𝒢).piece j).val.obj U) :
    HEq (((specGradedAlgebra 𝒢).mul i j).app U a b)
      (((specGradedAlgebra 𝒢).mul j i).app U b a) := by
  refine Stacks.heq_of_isSeparated (congrArg (pieceSheaf 𝒢) (add_comm i j))
    ((Opens.grothendieckTopology ↥(Spec R)).intersection_covering
      (Stacks.cmpSieve_mem (pieceCmp 𝒢 i) a) (Stacks.cmpSieve_mem (pieceCmp 𝒢 j) b)) ?_
  rintro Y f ⟨⟨x₀, hx₀⟩, ⟨y₀, hy₀⟩⟩
  have hx : PresheafOfModules.Hom.app (pieceCmp 𝒢 i) (op Y) x₀ =
    (pieceSheaf 𝒢 i).val.map f.op a := hx₀
  have hy : PresheafOfModules.Hom.app (pieceCmp 𝒢 j) (op Y) y₀ =
    (pieceSheaf 𝒢 j).val.map f.op b := hy₀
  -- The two restrictions, stated with `specGradedAlgebra` rather than its unfolding, so that
  -- they rewrite the goal syntactically.
  have hL : (pieceSheaf 𝒢 (i + j)).val.map f.op
        (((specGradedAlgebra 𝒢).mul i j).app U a b) =
      PresheafOfModules.Hom.app (pieceCmp 𝒢 (i + j)) (op Y)
        (((presheafAlgebra 𝒢).mul i j).app (op Y) x₀ y₀) :=
    (presheafAlgebra 𝒢).ofComparison_mul_restrict (pieceSheaf 𝒢) (pieceCmp 𝒢) i j f.op a b
      x₀ y₀ hx hy
  have hR : (pieceSheaf 𝒢 (j + i)).val.map f.op
        (((specGradedAlgebra 𝒢).mul j i).app U b a) =
      PresheafOfModules.Hom.app (pieceCmp 𝒢 (j + i)) (op Y)
        (((presheafAlgebra 𝒢).mul j i).app (op Y) y₀ x₀) :=
    (presheafAlgebra 𝒢).ofComparison_mul_restrict (pieceSheaf 𝒢) (pieceCmp 𝒢) j i f.op b a
      y₀ x₀ hy hx
  rw [hL, hR]
  exact Stacks.heq_apply _ _ (fun n s => PresheafOfModules.Hom.app (pieceCmp 𝒢 n) (op Y) s)
    (add_comm i j) (presheafAlgebra_mul_comm 𝒢 i j (op Y) x₀ y₀)

/-- **The pieces are quasi-coherent**: each is an associated sheaf. -/
instance isQuasicoherent_specGradedAlgebra_piece (n : ℤ) :
    ((specGradedAlgebra 𝒢).piece n).IsQuasicoherent :=
  inferInstanceAs (tilde (pieceModule 𝒢 n)).IsQuasicoherent

/-- **A piece of a vanishing degree vanishes.** -/
theorem isZero_specGradedAlgebra_piece {n : ℤ} (hn : 𝒢 n = ⊥) :
    Limits.IsZero ((specGradedAlgebra 𝒢).piece n) := by
  have hsub : Subsingleton (pieceModule 𝒢 n) :=
    ⟨fun x y => Subtype.ext (((Submodule.eq_bot_iff _).1 hn _ x.2).trans
      (((Submodule.eq_bot_iff _).1 hn _ y.2)).symm)⟩
  have h0 : Limits.IsZero (pieceModule 𝒢 n) :=
    let := hsub
    ModuleCat.isZero_of_subsingleton _
  exact (tilde.functor R).map_isZero h0

/-! ### The global section named by a homogeneous element -/

/-- **The global section of `(𝒢 k)~` named by a homogeneous element `b` of degree `k`**: the
comparison image of `1 ⊗ b`, over every open. -/
def homogeneousSection {k : ℤ} (b : ↥(𝒢 k)) : ((specGradedAlgebra 𝒢).piece k).val.sections :=
  PresheafOfModules.sectionsMk
    (fun U => PresheafOfModules.Hom.app (pieceCmp 𝒢 k) U
      ((1 : Γ(Spec R, U.unop)) ⊗ₜ[R] b))
    (fun {U V} h => by
      refine Eq.trans (PresheafOfModules.naturality_apply (pieceCmp 𝒢 k) h
        ((1 : Γ(Spec R, U.unop)) ⊗ₜ[R] b)).symm ?_
      refine congrArg (fun z => PresheafOfModules.Hom.app (pieceCmp 𝒢 k) V z) ?_
      exact congrArg (fun c => c ⊗ₜ[R] b) (AffineBaseChange.specRestrictₗ_one h.unop))

/-- The section named by a sum is the sum of the sections. -/
theorem homogeneousSection_eval_add {k : ℤ} (b b' : ↥(𝒢 k)) (U : ((Spec R).Opens)ᵒᵖ) :
    (homogeneousSection 𝒢 (b + b')).eval U =
      (homogeneousSection 𝒢 b).eval U + (homogeneousSection 𝒢 b').eval U := by
  refine Eq.trans (congrArg (fun z => PresheafOfModules.Hom.app (pieceCmp 𝒢 k) U z)
    (TensorProduct.tmul_add (1 : Γ(Spec R, U.unop)) b b')) ?_
  exact map_add (AffineBaseChange.toTildeₗ (pieceModule 𝒢 k) U.unop) _ _

/-- **The section named by the unit of `S` is the unit of the algebra sheaf.** -/
theorem homogeneousSection_gOne : homogeneousSection 𝒢 (gOne 𝒢) = (specGradedAlgebra 𝒢).one :=
  PresheafOfModules.sections_ext _ _ fun U => (specGradedAlgebra_one_eval 𝒢 U).symm

/-- Transport along an equality of degrees carries the section named by an element to the
section named by any element with the same image in `S`. -/
theorem castHom_pieceCmp {d d' : ℤ} (h : d = d') (U : ((Spec R).Opens)ᵒᵖ)
    (a : Γ(Spec R, U.unop)) (x : ↥(𝒢 d)) (y : ↥(𝒢 d')) (hxy : (x : S) = (y : S)) :
    _root_.SheafOfModules.castHom (specGradedAlgebra 𝒢).piece h U
        (PresheafOfModules.Hom.app (pieceCmp 𝒢 d) U (a ⊗ₜ[R] x)) =
      PresheafOfModules.Hom.app (pieceCmp 𝒢 d') U (a ⊗ₜ[R] y) := by
  subst h
  exact congrArg (fun z : ↥(𝒢 d) => PresheafOfModules.Hom.app (pieceCmp 𝒢 d) U (a ⊗ₜ[R] z))
    (Subtype.ext hxy)

/-- **The section named by a product is the product of the sections**, across the degree
identification. The resulting element of `S` is specified only by its image, which is what lets
the two factors be read in either order. -/
theorem castHom_homogeneousSection_mul {i j m : ℤ} (h : i + j = m) (b : ↥(𝒢 i)) (b' : ↥(𝒢 j))
    (c : ↥(𝒢 m)) (hc : (c : S) = (b : S) * (b' : S)) (U : ((Spec R).Opens)ᵒᵖ) :
    _root_.SheafOfModules.castHom (specGradedAlgebra 𝒢).piece h U
        (((specGradedAlgebra 𝒢).mul i j).app U
          ((homogeneousSection 𝒢 b).eval U) ((homogeneousSection 𝒢 b').eval U)) =
      (homogeneousSection 𝒢 c).eval U := by
  refine Eq.trans (congrArg (_root_.SheafOfModules.castHom (specGradedAlgebra 𝒢).piece h U)
    (specGradedAlgebra_mul_toTilde 𝒢 i j U ((1 : Γ(Spec R, U.unop)) ⊗ₜ[R] b)
      ((1 : Γ(Spec R, U.unop)) ⊗ₜ[R] b'))) ?_
  refine Eq.trans (congrArg (fun z => _root_.SheafOfModules.castHom (specGradedAlgebra 𝒢).piece h U
    (PresheafOfModules.Hom.app (pieceCmp 𝒢 (i + j)) U z))
    (mulSec_tmul 𝒢 U i j 1 1 b b')) ?_
  refine Eq.trans (congrArg (fun a => _root_.SheafOfModules.castHom
      (specGradedAlgebra 𝒢).piece h U
      (PresheafOfModules.Hom.app (pieceCmp 𝒢 (i + j)) U (a ⊗ₜ[R] mulₗ 𝒢 i j b b')))
    (_root_.one_mul (1 : Γ(Spec R, U.unop)))) ?_
  exact castHom_pieceCmp 𝒢 h U 1 (mulₗ 𝒢 i j b b') c hc.symm

end Stacks.SpecGraded

end
