module

public import StacksFrontier.AlgebraicGeometry.Koszul.Sheaf.SheafifiedDifferential
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedRelativeTensorUnitor

/-!
# The exterior algebra of a sheaf of modules is graded-commutative

Stacks tag 062K calls the Koszul complex `K_•(φ)` a sheaf of **commutative** differential graded
algebras. The notion of a sheaf of differential graded algebras this library has,
`SheafOfModules.DifferentialGradedAlgebra`, is Stacks tag 0FRF's, which has no commutativity
axiom; so graded commutativity of the underlying algebra `⋀(F)` is not a field to be filled but a
statement to be proved, and this file proves it: for homogeneous local sections `x` of degree `p`
and `y` of degree `q`,
`x · y = (-1)^(p q) · y · x`.

## Main results

* `Koszul.ι_mul_comm_of_mem` and `Koszul.mul_comm_of_mem`: **graded commutativity of the exterior
  algebra at the ring level**, for the `ℕ`-indexed exterior powers.
* `Koszul.mul_comm_of_mem_intPiece`: the same for the `ℤ`-indexed exterior powers
  `ExteriorAlgebra.intPiece`, with the sign written as `Int.negOnePow` acting through the
  integers.
* `PresheafOfModules.exteriorAlgebraMul_comm`: **graded commutativity of the sectionwise exterior
  algebra of a presheaf of modules.**
* `SheafOfModules.sheafifiedExteriorMul_comm`: **graded commutativity of `⋀(F)`**, the exterior
  algebra of a sheaf of modules of Section 17.21.

## Implementation notes

**Mathlib has the anticommutation only on `ιMulti` generators**
(`ExteriorAlgebra.ιMulti_mul_ιMulti_anticomm`), which would have to be combined with a spanning
statement for the exterior powers. It is shorter to run the same double induction over
`Submodule.pow_induction_on_left'` that the Koszul Leibniz rule is proved by: commuting a
degree-one generator past a homogeneous element is one induction, and commuting two homogeneous
elements is that lemma inside a second.

**The sheaf statement is read on local lifts and concluded by separatedness**, exactly as
`SheafOfModules.koszulD_mul` is: the product of two local sections of `⋀(F)` becomes the unit
image of a sectionwise product after restriction along the intersection of two covering sieves of
local lifts (`Stacks.GradedAlgebra.sheafify_mul_restrict`), and `Stacks.eq_of_isSeparated`
finishes. The transport along `q + p = p + q` is the only one, and it is carried past restriction
and past the sheafification unit by `SheafOfModules.restriction_zsmul_gradedCast` and
`SheafOfModules.gradedCast_dependent`.

## References

* [Stacks Project, Tag 062K](https://stacks.math.columbia.edu/tag/062K)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Sheaf Opposite PresheafOfModules

open scoped ExteriorAlgebra

universe v u w

/-! ## The ring level -/

namespace Koszul

variable {R : Type u} [CommRing R] {E : Type v} [AddCommGroup E] [Module R E]

/-- **A degree-one generator commutes past a homogeneous element of the exterior algebra up to the
sign of its degree.** -/
theorem ι_mul_comm_of_mem (e : E) {q : ℕ} {b : ExteriorAlgebra R E} (hb : b ∈ ⋀[R]^q E) :
    ExteriorAlgebra.ι R e * b = ((-1 : ℤˣ) ^ q) • (b * ExteriorAlgebra.ι R e) := by
  induction hb using Submodule.pow_induction_on_left' with
  | algebraMap r => rw [pow_zero, one_smul, Algebra.commutes]
  | add x y i hx hy ihx ihy => rw [mul_add, add_mul, ihx, ihy, smul_add]
  | mem_mul m hm i x hx ih =>
    obtain ⟨f, rfl⟩ := hm
    have hswap : ExteriorAlgebra.ι R e * ExteriorAlgebra.ι R f =
        -(ExteriorAlgebra.ι R f * ExteriorAlgebra.ι R e) :=
      eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap e f)
    rw [← mul_assoc, hswap, neg_mul, mul_assoc, ih, mul_smul_comm, pow_succ, mul_smul,
      Units.neg_smul, one_smul, smul_neg, mul_assoc]

/-- **The exterior algebra is graded-commutative:** an element of exterior degree `p` and one of
exterior degree `q` commute up to the sign `(-1) ^ (p * q)`. -/
theorem mul_comm_of_mem {p q : ℕ} {a b : ExteriorAlgebra R E} (ha : a ∈ ⋀[R]^p E)
    (hb : b ∈ ⋀[R]^q E) : a * b = ((-1 : ℤˣ) ^ (p * q)) • (b * a) := by
  induction ha using Submodule.pow_induction_on_left' with
  | algebraMap r => rw [Nat.zero_mul, pow_zero, one_smul, Algebra.commutes]
  | add x y i hx hy ihx ihy => rw [add_mul, mul_add, ihx, ihy, smul_add]
  | mem_mul m hm i x hx ih =>
    obtain ⟨f, rfl⟩ := hm
    rw [mul_assoc, ih, mul_smul_comm, ← mul_assoc, ι_mul_comm_of_mem f hb, smul_mul_assoc,
      smul_smul, ← pow_add, Nat.succ_mul, ← mul_assoc]

/-- The sign of a nonnegative degree, written as the integer unit `Int.negOnePow` acting through
the integers, is the unit `(-1) ^ n` of the integers acting directly. -/
theorem negOnePow_natCast_units_zsmul (k : ℕ) (z : ExteriorAlgebra R E) :
    (Int.negOnePow (k : ℤ) : ℤ) • z = ((-1 : ℤˣ) ^ k) • z := by
  rcases Nat.even_or_odd k with h | h
  · rw [Int.negOnePow_even (k : ℤ) (by exact_mod_cast h), Units.val_one, one_zsmul,
      h.neg_one_pow, one_smul]
  · rw [Int.negOnePow_odd (k : ℤ) (by exact_mod_cast h), Units.val_neg, Units.val_one,
      neg_zsmul, one_zsmul, h.neg_one_pow, Units.neg_smul, one_smul]

/-- **Graded commutativity of the exterior algebra in the `ℤ`-indexed grading.** In a negative
degree the exterior power is zero and both sides vanish. -/
theorem mul_comm_of_mem_intPiece (p q : ℤ) {a b : ExteriorAlgebra R E}
    (ha : a ∈ ExteriorAlgebra.intPiece R E p) (hb : b ∈ ExteriorAlgebra.intPiece R E q) :
    a * b = (Int.negOnePow (p * q) : ℤ) • (b * a) := by
  cases p with
  | negSucc k =>
    rw [ExteriorAlgebra.eq_zero_of_mem_intPiece_of_neg R E (by omega) ha]
    simp
  | ofNat m =>
    cases q with
    | negSucc k =>
      rw [ExteriorAlgebra.eq_zero_of_mem_intPiece_of_neg R E (by omega) hb]
      simp
    | ofNat k =>
      refine (mul_comm_of_mem ha hb).trans ?_
      rw [show (Int.ofNat m * Int.ofNat k : ℤ) = ((m * k : ℕ) : ℤ) from rfl,
        negOnePow_natCast_units_zsmul]

end Koszul

/-! ## The sectionwise exterior algebra of a presheaf of modules -/

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  (F : PresheafOfModules.{max w w} (O ⋙ forget₂ _ RingCat))

/-- **The sectionwise exterior algebra of a presheaf of modules is graded-commutative.** The
product of a section of degree `q` and one of degree `p` lies in degree `q + p`, so the right-hand
side is transported into degree `p + q`. -/
theorem exteriorAlgebraMul_comm (p q : ℤ) (X : Cᵒᵖ)
    (x : (exteriorAlgebraPiece p F).obj X) (y : (exteriorAlgebraPiece q F).obj X) :
    (exteriorAlgebraMul F p q).app X x y =
      (Int.negOnePow (p * q) : ℤ) •
        SheafOfModules.gradedCast (fun t => (exteriorAlgebraPiece t F).obj X) (add_comm q p)
          ((exteriorAlgebraMul F q p).app X y x) := by
  refine exteriorAlgebraPieceVal_injective (p + q) F X ?_
  rw [exteriorAlgebraPieceVal_mul F p q X x y, exteriorAlgebraPieceVal_zsmul F (p + q) X _ _,
    exteriorAlgebraPieceVal_gradedCast F (add_comm q p) X _,
    exteriorAlgebraPieceVal_mul F q p X y x]
  exact Koszul.mul_comm_of_mem_intPiece p q x.2 y.2

end PresheafOfModules

/-! ## The exterior algebra of a sheaf of modules -/

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  (F : SheafOfModules.{w} (toRingCat J Osharp))

/-- **The exterior algebra `⋀(F)` of a sheaf of modules is graded-commutative**: on local sections
`x` of degree `p` and `y` of degree `q`, `x · y = (-1)^(p q) · y · x`. This is the property Stacks
tag 062K's adjective *commutative* names; the notion
`SheafOfModules.DifferentialGradedAlgebra`, which is Stacks tag 0FRF's, does not carry it as an
axiom, so it is recorded here. -/
theorem sheafifiedExteriorMul_comm (p q : ℤ) (U : Cᵒᵖ)
    (x : ((sheafifiedExteriorAlgebra J F).piece p).val.obj U)
    (y : ((sheafifiedExteriorAlgebra J F).piece q).val.obj U) :
    ((sheafifiedExteriorAlgebra J F).mul p q).app U x y =
      (Int.negOnePow (p * q) : ℤ) •
        gradedCast (fun t => ((sheafifiedExteriorAlgebra J F).piece t).val.obj U) (add_comm q p)
          (((sheafifiedExteriorAlgebra J F).mul q p).app U y x) := by
  refine Stacks.eq_of_isSeparated ((sheafifiedExteriorAlgebra J F).piece (p + q))
    (J.intersection_covering (Stacks.liftSieve_mem _ (exteriorAlgebraPiece p F.val) x)
      (Stacks.liftSieve_mem _ (exteriorAlgebraPiece q F.val) y)) ?_
  rintro Y f ⟨⟨x₀, hx₀⟩, ⟨y₀, hy₀⟩⟩
  have hmul : ∀ (a b : ℤ) x' y' x₀' y₀',
      exteriorUnit J F a (op Y) x₀' = ((sheafifiedExteriorAlgebra J F).piece a).val.map f.op x' →
      exteriorUnit J F b (op Y) y₀' = ((sheafifiedExteriorAlgebra J F).piece b).val.map f.op y' →
      ((sheafifiedExteriorAlgebra J F).piece (a + b)).val.map f.op
          (((sheafifiedExteriorAlgebra J F).mul a b).app U x' y') =
        exteriorUnit J F (a + b) (op Y) ((exteriorAlgebraMul F.val a b).app (op Y) x₀' y₀') :=
    fun a b _ _ _ _ => (exteriorAlgebraGradedAlgebra F.val).sheafify_mul_restrict
      (𝟙 (toRingCat J Osharp).obj) a b f.op _ _ _ _
  have hL := hmul p q x y x₀ y₀ hx₀ hy₀
  have hR := hmul q p y x y₀ x₀ hy₀ hx₀
  have hcast := restriction_zsmul_gradedCast
    (fun t => (sheafifiedExteriorAlgebra J F).piece t) (add_comm q p) f.op
    (Int.negOnePow (p * q) : ℤ) (((sheafifiedExteriorAlgebra J F).mul q p).app U y x)
  have hkey := exteriorAlgebraMul_comm F.val p q (op Y) x₀ y₀
  refine hL.trans (Eq.trans ?_ hcast.symm)
  rw [hkey, exteriorUnit_zsmul, gradedCast_dependent
      (Y := fun t => (exteriorAlgebraPiece t F.val).obj (op Y))
      (Z := fun t => ((sheafifiedExteriorAlgebra J F).piece t).val.obj (op Y))
      (fun t s => exteriorUnit J F t (op Y) s) (add_comm q p),
    ← hR]

end SheafOfModules

end
