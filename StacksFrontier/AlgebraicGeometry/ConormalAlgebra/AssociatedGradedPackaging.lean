module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraSheafification
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SectionwiseAlgebras
public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.AssociatedGradedAlgebra

/-!
# The associated graded algebra of a quasi-coherent ideal, as a sheaf of graded algebras

Let `X` be a scheme and `ℐ : X.IdealSheafData` a quasi-coherent sheaf of ideals.  The sheaves
`ℐⁿ/ℐⁿ⁺¹` (`Stacks.Conormal.grPiece`) and their multiplication `Stacks.Conormal.grMul` are
assembled into a `SheafOfModules.GradedAlgebra` over `𝒪_X`: the `ℕ`-indexed family is extended
to `ℤ` by zero in negative degrees, and the three graded laws are proved.

## Main definitions

* `Stacks.Conormal.grZPiece`: the `ℤ`-indexed family `ℐⁿ/ℐⁿ⁺¹` for `n ≥ 0`, zero otherwise.
* `Stacks.Conormal.grZMul`: its multiplication, `Stacks.Conormal.grMul` in nonnegative degrees
  and zero as soon as one degree is negative.
* `Stacks.Conormal.grZOne`: the class of `1`, a global section of `ℐ⁰/ℐ¹`.
* `Stacks.Conormal.grGradedAlgebra`: **`⨁_{n ≥ 0} ℐⁿ/ℐⁿ⁺¹`, as a sheaf of graded
  `𝒪_X`-algebras** — the right-hand side of the second identity of [Stacks, Tag 0633] part (1).

## Main results

* `Stacks.Conormal.grMul_heq_assoc`, `grMul_heq_one_mul`, `grMul_heq_mul_one`: the three graded
  laws in nonnegative degrees.
* `Stacks.Conormal.grMul_restrict`: the multiplication of the associated graded read on local
  lifts along `ℐⁿ ↠ ℐⁿ/ℐⁿ⁺¹`.
* `Stacks.Conormal.grGradedAlgebra_negative_isZero` and
  `grGradedAlgebra_isQuasicoherent`: the algebra is concentrated in nonnegative degrees and its
  pieces are quasi-coherent.

## Implementation notes

`Stacks.GradedAlgebra.extendFamily` and `.extend` perform the same `ℕ → ℤ` extension by zero,
but they land in `PresheafOfModules`, where the zero piece is not a sheaf.  The zero piece used
here is `SheafOfModules.free PEmpty`, the one `Stacks.Blowup.reesPiece` uses in negative degrees,
so the two algebras have *the same* negative pieces.

In negative degrees the multiplication is `Stacks.BilinearMap.zero` on the nose.

In `ℕ`, `k + 0` is definitionally `k` but `0 + k` is not, so `grMul_heq_mul_one` needs no
transport while `grMul_heq_one_mul` does.

## References

* [Stacks Project, Tag 0633](https://stacks.math.columbia.edu/tag/0633)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.GabberColimit Stacks.AlgebraicGeometry.IdealPowerSmul

universe u

namespace Stacks.Conormal

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-! ### The homogeneous pieces in every integer degree -/

/-- `ℐⁿ/ℐⁿ⁺¹` for `n ≥ 0`, and the zero sheaf of modules in negative degrees.

The two cases are stated against the constructors of `ℤ`: `Int.ofNat i + Int.ofNat j` reduces to
`Int.ofNat (i + j)`, so `grZPiece I (i + j)` is definitionally `grPiece I (i + j)` for
natural-number degrees and no transport appears in the multiplication. -/
def grZPiece : ℤ → X.Modules
  | Int.ofNat k => grPiece I k
  | Int.negSucc _ => SheafOfModules.free (R := X.ringCatSheaf) PEmpty

/-- In a natural-number degree `k`, the piece is `ℐᵏ/ℐᵏ⁺¹`. -/
theorem grZPiece_natCast (k : ℕ) : grZPiece I (k : ℤ) = grPiece I k := rfl

/-- The pieces in negative degrees vanish. -/
theorem grZPiece_negative_isZero (n : ℤ) (hn : n < 0) : IsZero (grZPiece I n) := by
  match n, hn with
  | Int.negSucc k, _ =>
    show IsZero (SheafOfModules.free (R := X.ringCatSheaf) PEmpty)
    rw [IsZero.iff_id_eq_zero]
    exact Sigma.hom_ext _ _ fun i ↦ i.elim

/-- Every piece `grZPiece I n` is quasi-coherent. -/
instance isQuasicoherent_grZPiece (n : ℤ) : (grZPiece I n).IsQuasicoherent := by
  match n with
  | Int.ofNat k => exact isQuasicoherent_grPiece I k
  | Int.negSucc _ =>
    exact inferInstanceAs
      ((SheafOfModules.free (R := X.ringCatSheaf) PEmpty).IsQuasicoherent)

/-! ### The unit -/

/-- `1`, as a global section of `ℐ⁰ · 𝒪_X`: the zeroth power of an ideal is the unit ideal, so
the constant function `1` is a section of it over every open. -/
def oneIdealPowerSection : (idealPower I 0).sections :=
  PresheafOfModules.sectionsMk
    (fun U => mkIdealPowerSection I 0 (1 : Γ(X, U.unop))
      (fun W _ => by simp))
    (fun {_ _} f => ambient_injective I 0 (map_one (X.presheaf.map f).hom))

/-- The section `oneIdealPowerSection I` is the function `1` over every open. -/
@[simp] theorem ambient_oneIdealPowerSection (U : (Opens ↥X)ᵒᵖ) :
    ambient I 0 ((oneIdealPowerSection I).eval U) = 1 := rfl

/-- **The class of `1`, a global section of `ℐ⁰/ℐ¹`**: the unit of the associated graded
algebra. -/
def grZOne : (grZPiece I 0).sections :=
  PresheafOfModules.sectionsMk
    (fun U => (grPieceπ I 0).val.app U ((oneIdealPowerSection I).eval U))
    (fun {U V} f =>
      ((PresheafOfModules.naturality_apply (grPieceπ I 0).val f
            ((oneIdealPowerSection I).eval U)).symm).trans
        (congrArg (fun s => (grPieceπ I 0).val.app V s)
          (PresheafOfModules.sections_property (oneIdealPowerSection I) f)))

/-- Over `U`, `grZOne I` is the class of `1` in `ℐ⁰/ℐ¹`. -/
theorem grZOne_eval (U : (Opens ↥X)ᵒᵖ) :
    (grZOne I).eval U = (grPieceπ I 0).val.app U ((oneIdealPowerSection I).eval U) := rfl

/-! ### Local lifts along the quotient map -/

/-- The sieve of local lifts of a section of `ℐⁿ/ℐⁿ⁺¹` along the quotient map from `ℐⁿ`. -/
abbrev grLiftSieve (n : ℕ) {U : (Opens ↥X)ᵒᵖ} (x : (grPiece I n).val.obj U) :
    Sieve U.unop :=
  Presheaf.imageSieve ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
    (grPieceπ I n).val) x

/-- **A section of `ℐⁿ/ℐⁿ⁺¹` lifts to `ℐⁿ` on a covering sieve**: the quotient map is locally
surjective, being an epimorphism of sheaves of modules. -/
theorem grLiftSieve_mem (n : ℕ) {U : (Opens ↥X)ᵒᵖ} (x : (grPiece I n).val.obj U) :
    grLiftSieve I n x ∈ (Opens.grothendieckTopology ↥X) U.unop :=
  Presheaf.imageSieve_mem _
    ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map (grPieceπ I n).val) x

/-- **The multiplication of the associated graded, read on local lifts.** If two local sections
of `ℐⁿ/ℐⁿ⁺¹` and `ℐᵐ/ℐᵐ⁺¹` lift, after restriction, to sections `p` and `q` of `ℐⁿ` and `ℐᵐ`,
then their product restricts to the class of `p · q`. -/
theorem grMul_restrict (n m : ℕ) {U V : (Opens ↥X)ᵒᵖ} (f : U ⟶ V)
    (b₁ : (grPiece I n).val.obj U) (b₂ : (grPiece I m).val.obj U)
    (p : (idealPower I n).val.obj V) (q : (idealPower I m).val.obj V)
    (hp : (grPieceπ I n).val.app V p = (grPiece I n).val.map f b₁)
    (hq : (grPieceπ I m).val.app V q = (grPiece I m).val.map f b₂) :
    (grPiece I (n + m)).val.map f ((grMul I n m).app U b₁ b₂) =
      (grPieceπ I (n + m)).val.app V (mulApp I n m V.unop p q) := by
  refine ((grMul I n m).naturality f b₁ b₂).trans ?_
  rw [← hp, ← hq]
  exact grMul_app_π I n m V p q

/-- Two sections of two powers of the filtration with propositionally equal degrees and the same
underlying function are heterogeneously equal. -/
theorem idealPower_heq {n m : ℕ} (hnm : n = m) {U : (Opens ↥X)ᵒᵖ}
    (x : (idealPower I n).val.obj U) (y : (idealPower I m).val.obj U)
    (h : ambient I n x = ambient I m y) : HEq x y := by
  subst hnm
  exact heq_of_eq (ambient_injective I n h)

/-- The classes in `ℐⁿ/ℐⁿ⁺¹` and `ℐᵐ/ℐᵐ⁺¹` of representatives with the same underlying function
are heterogeneously equal when `n = m`. -/
private theorem heq_grPieceπ_app {n m : ℕ} (hnm : n = m) {U : (Opens ↥X)ᵒᵖ}
    (p : (idealPower I n).val.obj U) (q : (idealPower I m).val.obj U)
    (h : ambient I n p = ambient I m q) :
    HEq ((grPieceπ I n).val.app U p) ((grPieceπ I m).val.app U q) := by
  subst hnm
  exact heq_of_eq (congrArg _ (ambient_injective I n h))

/-! ### The three graded laws in nonnegative degrees -/

/-- **The multiplication of the associated graded is associative.** -/
theorem grMul_heq_assoc (a b c : ℕ) (U : (Opens ↥X)ᵒᵖ)
    (x : (grPiece I a).val.obj U) (y : (grPiece I b).val.obj U)
    (z : (grPiece I c).val.obj U) :
    HEq ((grMul I (a + b) c).app U ((grMul I a b).app U x y) z)
      ((grMul I a (b + c)).app U x ((grMul I b c).app U y z)) := by
  refine Stacks.heq_of_isSeparated
    (congrArg (fun n : ℕ => grPiece I n) (Nat.add_assoc a b c))
    ((Opens.grothendieckTopology ↥X).intersection_covering
      ((Opens.grothendieckTopology ↥X).intersection_covering
        (grLiftSieve_mem I a x) (grLiftSieve_mem I b y))
      (grLiftSieve_mem I c z)) ?_
  rintro W f ⟨⟨⟨p, hp₀⟩, ⟨q, hq₀⟩⟩, ⟨r, hr₀⟩⟩
  have hp : (grPieceπ I a).val.app (op W) p = (grPiece I a).val.map f.op x := hp₀
  have hq : (grPieceπ I b).val.app (op W) q = (grPiece I b).val.map f.op y := hq₀
  have hr : (grPieceπ I c).val.app (op W) r = (grPiece I c).val.map f.op z := hr₀
  rw [grMul_restrict I (a + b) c f.op _ z (mulApp I a b W p q) r
      (grMul_restrict I a b f.op x y p q hp hq).symm hr,
    grMul_restrict I a (b + c) f.op x _ p (mulApp I b c W q r) hp
      (grMul_restrict I b c f.op y z q r hq hr).symm]
  exact heq_grPieceπ_app I (Nat.add_assoc a b c) _ _
    (mul_assoc (ambient I a p) (ambient I b q) (ambient I c r))

/-- **The class of `1` is a left identity for the multiplication of the associated graded.** -/
theorem grMul_heq_one_mul (a : ℕ) (U : (Opens ↥X)ᵒᵖ) (x : (grPiece I a).val.obj U) :
    HEq ((grMul I 0 a).app U ((grZOne I).eval U) x) x := by
  refine Stacks.heq_of_isSeparated
    (congrArg (fun n : ℕ => grPiece I n) (Nat.zero_add a))
    (grLiftSieve_mem I a x) ?_
  rintro W f ⟨p, hp₀⟩
  have hp : (grPieceπ I a).val.app (op W) p = (grPiece I a).val.map f.op x := hp₀
  rw [grMul_restrict I 0 a f.op _ x ((oneIdealPowerSection I).eval (op W)) p
      (PresheafOfModules.sections_property (grZOne I) f.op).symm hp, ← hp]
  exact heq_grPieceπ_app I (Nat.zero_add a) _ _
    (one_mul (ambient I a p))

/-- **The class of `1` is a right identity for the multiplication of the associated graded.** -/
theorem grMul_heq_mul_one (a : ℕ) (U : (Opens ↥X)ᵒᵖ) (x : (grPiece I a).val.obj U) :
    HEq ((grMul I a 0).app U x ((grZOne I).eval U)) x := by
  refine Stacks.heq_of_isSeparated
    (congrArg (fun n : ℕ => grPiece I n) (Nat.add_zero a))
    (grLiftSieve_mem I a x) ?_
  rintro W f ⟨p, hp₀⟩
  have hp : (grPieceπ I a).val.app (op W) p = (grPiece I a).val.map f.op x := hp₀
  rw [grMul_restrict I a 0 f.op x _ p ((oneIdealPowerSection I).eval (op W)) hp
      (PresheafOfModules.sections_property (grZOne I) f.op).symm, ← hp]
  exact heq_grPieceπ_app I (Nat.add_zero a) _ _
    (mul_one (ambient I a p))

/-! ### The multiplication in every pair of integer degrees -/

/-- The multiplication of the associated graded in every pair of integer degrees: `grMul` in
nonnegative degrees, and zero as soon as one of them is negative. -/
def grZMul : (i j : ℤ) →
    SheafOfModules.BilinearMap (grZPiece I i) (grZPiece I j) (grZPiece I (i + j))
  | Int.ofNat _, Int.ofNat _ => grMul I _ _
  | Int.ofNat _, Int.negSucc _ => Stacks.BilinearMap.zero
  | Int.negSucc _, _ => Stacks.BilinearMap.zero

/-- In natural-number degrees, `grZMul` is `grMul`. -/
theorem grZMul_natCast (n m : ℕ) : grZMul I (n : ℤ) (m : ℤ) = grMul I n m := rfl

/-- The multiplication vanishes when the first degree is negative. -/
theorem grZMul_app_eq_zero_of_neg_left {i : ℤ} (hi : i < 0) (j : ℤ) (U : (Opens ↥X)ᵒᵖ)
    (x : (grZPiece I i).val.obj U) (y : (grZPiece I j).val.obj U) :
    (grZMul I i j).app U x y = 0 := by
  match i, hi with
  | Int.negSucc _, _ => rfl

/-- The multiplication vanishes when the second degree is negative. -/
theorem grZMul_app_eq_zero_of_neg_right (i : ℤ) {j : ℤ} (hj : j < 0) (U : (Opens ↥X)ᵒᵖ)
    (x : (grZPiece I i).val.obj U) (y : (grZPiece I j).val.obj U) :
    (grZMul I i j).app U x y = 0 := by
  match i, j, hj with
  | Int.ofNat _, Int.negSucc _, _ => rfl
  | Int.negSucc _, Int.negSucc _, _ => rfl

/-- **In a negative degree every section of `grZPiece` vanishes.** -/
theorem grZPiece_section_eq_zero {n : ℤ} (hn : n < 0) (U : (Opens ↥X)ᵒᵖ)
    (x : (grZPiece I n).val.obj U) : x = 0 :=
  (ModuleCat.subsingleton_of_isZero
    ((PresheafOfModules.evaluation _ U).map_isZero
      ((SheafOfModules.forget _).map_isZero (grZPiece_negative_isZero I n hn)))).allEq x 0

/-- Two sections of two *equal* pieces which both vanish are heterogeneously equal. -/
theorem heq_of_eq_zero {M N : X.Modules} (hMN : M = N) {U : (Opens ↥X)ᵒᵖ}
    {x : M.val.obj U} {y : N.val.obj U} (hx : x = 0) (hy : y = 0) : HEq x y := by
  subst hMN hx hy
  rfl

/-! ### The sheaf of graded algebras -/

/-- **`⨁_{n ≥ 0} ℐⁿ/ℐⁿ⁺¹`, the associated graded algebra of a quasi-coherent sheaf of ideals, as
a sheaf of graded `𝒪_X`-algebras.**  This is the sheaf whose inverse image along a closed
immersion with ideal sheaf `ℐ` is the conormal algebra — the second identity of
[Stacks, Tag 0633] part (1).  It is an instance of the notion of a sheaf of graded algebras
of [Stacks, Tag 0FQW]. -/
def grGradedAlgebra : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf where
  piece n := grZPiece I n
  mul i j := grZMul I i j
  one := grZOne I
  mul_assoc i j k U x y z := by
    rcases lt_or_ge i 0 with hi | hi
    · refine heq_of_eq_zero (congrArg (grZPiece I) (add_assoc i j k)) ?_
        (grZMul_app_eq_zero_of_neg_left I hi (j + k) U x _)
      rw [grZMul_app_eq_zero_of_neg_left I hi j U x y]
      exact congrFun (congrArg _ (map_zero ((grZMul I (i + j) k).app U))) z
    rcases lt_or_ge j 0 with hj | hj
    · refine heq_of_eq_zero (congrArg (grZPiece I) (add_assoc i j k)) ?_ ?_
      · rw [grZMul_app_eq_zero_of_neg_right I i hj U x y]
        exact congrFun (congrArg _ (map_zero ((grZMul I (i + j) k).app U))) z
      · rw [grZMul_app_eq_zero_of_neg_left I hj k U y z]
        exact map_zero ((grZMul I i (j + k)).app U x)
    rcases lt_or_ge k 0 with hk | hk
    · refine heq_of_eq_zero (congrArg (grZPiece I) (add_assoc i j k))
        (grZMul_app_eq_zero_of_neg_right I (i + j) hk U _ z) ?_
      rw [grZMul_app_eq_zero_of_neg_right I j hk U y z]
      exact map_zero ((grZMul I i (j + k)).app U x)
    obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le hi
    obtain ⟨b, rfl⟩ := Int.eq_ofNat_of_zero_le hj
    obtain ⟨c, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    exact grMul_heq_assoc I a b c U x y z
  one_mul i U x := by
    rcases lt_or_ge i 0 with hi | hi
    · exact heq_of_eq_zero (congrArg (grZPiece I) (zero_add i))
        (grZMul_app_eq_zero_of_neg_right I 0 hi U _ x)
        (grZPiece_section_eq_zero I hi U x)
    obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le hi
    exact grMul_heq_one_mul I a U x
  mul_one i U x := by
    rcases lt_or_ge i 0 with hi | hi
    · exact heq_of_eq_zero (congrArg (grZPiece I) (add_zero i))
        (grZMul_app_eq_zero_of_neg_left I hi 0 U x _)
        (grZPiece_section_eq_zero I hi U x)
    obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le hi
    exact grMul_heq_mul_one I a U x

/-- The piece of `grGradedAlgebra I` in degree `n` is `grZPiece I n`. -/
@[simp] theorem grGradedAlgebra_piece (n : ℤ) :
    (grGradedAlgebra I).piece n = grZPiece I n := rfl

/-- The piece of `grGradedAlgebra I` in a natural-number degree `n` is `ℐⁿ/ℐⁿ⁺¹`. -/
theorem grGradedAlgebra_piece_natCast (n : ℕ) :
    (grGradedAlgebra I).piece (n : ℤ) = grPiece I n := rfl

/-- The multiplication of `grGradedAlgebra I` is `grZMul I`. -/
theorem grGradedAlgebra_mul (i j : ℤ) : (grGradedAlgebra I).mul i j = grZMul I i j := rfl

/-- The unit of `grGradedAlgebra I` is `grZOne I`. -/
theorem grGradedAlgebra_one : (grGradedAlgebra I).one = grZOne I := rfl

/-- **The associated graded algebra is concentrated in nonnegative degrees.** -/
theorem grGradedAlgebra_negative_isZero (n : ℤ) (hn : n < 0) :
    IsZero ((grGradedAlgebra I).piece n) :=
  grZPiece_negative_isZero I n hn

/-- **Every homogeneous piece of the associated graded algebra is quasi-coherent.** -/
theorem grGradedAlgebra_isQuasicoherent (n : ℤ) :
    ((grGradedAlgebra I).piece n).IsQuasicoherent :=
  isQuasicoherent_grZPiece I n

/-- The multiplication of the associated graded algebra computes the product of
representatives. -/
theorem grGradedAlgebra_mul_app_π (n m : ℕ) (U : (Opens ↥X)ᵒᵖ)
    (p : (idealPower I n).val.obj U) (q : (idealPower I m).val.obj U) :
    ((grGradedAlgebra I).mul (n : ℤ) (m : ℤ)).app U
        ((grPieceπ I n).val.app U p) ((grPieceπ I m).val.app U q) =
      (grPieceπ I (n + m)).val.app U (mulApp I n m U.unop p q) :=
  grMul_app_π I n m U p q

/-- The unit of the associated graded algebra is the class of `1`. -/
theorem grGradedAlgebra_one_eval (U : (Opens ↥X)ᵒᵖ) :
    (grGradedAlgebra I).one.eval U =
      (grPieceπ I 0).val.app U ((oneIdealPowerSection I).eval U) := rfl

end Stacks.Conormal

end
