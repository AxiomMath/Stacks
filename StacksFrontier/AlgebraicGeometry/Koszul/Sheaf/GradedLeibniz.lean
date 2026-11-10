module

public import StacksFrontier.AlgebraicGeometry.Koszul.Sheaf.Differential
public import StacksFrontier.RingTheory.Koszul.DifferentialGradedAlgebra

/-!
# The graded Leibniz rule for the Koszul differential, in every degree

`StacksFrontier.AlgebraicGeometry.Koszul.Sheaf.Differential` builds the Koszul differential of a
functional on a presheaf of modules and proves the graded Leibniz rule
`d (e ∧ x) = φ(e) · x - e ∧ d x` for a *degree-one generator* `e`. This file proves the rule for
an arbitrary homogeneous left factor: if `a` has exterior degree `p`, then
`d (a ∧ b) = d a ∧ b + (-1)^p · (a ∧ d b)`.

The statement is needed in exactly this generality by Stacks tag 062K, whose differential is
asserted to be a derivation of the whole exterior algebra and not merely to satisfy a recursion on
generators, and it is the form the Leibniz axiom of
`SheafOfModules.DifferentialGradedAlgebra` takes.

The file also provides the Koszul differential between two homogeneous degrees named
independently of one another, `PresheafOfModules.exteriorKoszulDOf`. The differential of
`StacksFrontier.AlgebraicGeometry.Koszul.Sheaf.Differential` has source
`exteriorAlgebraPiece (n + 1)`
on the nose, which is what makes the `ℕ`-indexed chain complex assemble with no transport; a
`CochainComplex` indexed by `ℤ`, on the other hand, wants a differential out of degree `-n` into
degree `-(n + 1)`, and `-(n + 1) + 1` is not syntactically `-n`.

## Main definitions

* `PresheafOfModules.exteriorKoszulDOf`: the Koszul differential from the exterior power of
  degree `p` to the one of degree `q`, for any pair of degrees with `q + 1 = p`.

## Main results

* `Koszul.contraction_mul_of_mem_intPiece`: **the graded Leibniz rule for the Koszul contraction
  at the ring level**, for a left factor in the `ℤ`-indexed exterior power of degree `n`, with the
  sign written as `Int.negOnePow n` acting through the integers.
* `Koszul.negOnePow_natCast_zsmul`: the two ways of writing the sign of a nonnegative degree, as
  the integer unit `Int.negOnePow` acting on an abelian group and as the ring element `(-1) ^ n`
  acting through the module structure, agree.
* `PresheafOfModules.exteriorAlgebraPieceVal_exteriorKoszulDOf`: on local sections
  `exteriorKoszulDOf` is contraction, and
  `PresheafOfModules.exteriorKoszulDOf_comp_exteriorKoszulDOf`: it squares to zero.
* `PresheafOfModules.exteriorAlgebraPieceVal_exteriorKoszulDOf_mul`: **the graded Leibniz rule
  for the Koszul differential of a presheaf of modules**, for a homogeneous left factor of any
  degree.

## Implementation notes

**The ring-level rule is not new mathematics; it is a restatement.**
`Koszul.HomologicalDifferentialGradedExteriorAlgebra.differential_mul_of_mem` already proves it
for an `ℕ`-indexed exterior power, by `Submodule.pow_induction_on_left'`. What this file adds is
the passage to the `ℤ`-indexed grading `ExteriorAlgebra.intPiece` that the sectionwise exterior
algebra of a presheaf of modules is graded by, and the passage from the sign `(-1) ^ n` in the
base ring to the sign `Int.negOnePow n` the differential-graded-algebra axioms are stated with.
In a negative degree the exterior power is zero and the rule is trivial.

**The Leibniz rule is stated on values rather than on homogeneous sections.** A local section of
`exteriorAlgebraPiece n F` is an element of the exterior algebra of the sections together with the
assertion that it lies in degree `n`, and `PresheafOfModules.exteriorAlgebraPieceVal` forgets the
assertion. Stating the rule on values means the three degrees `p`, `q` and `q + 1` it mentions are
unconstrained, so no transport along `p + q = (p + q - 1) + 1` appears; the product of the two
factors enters as a separate section together with the hypothesis that its value is the product,
which is the idiom of
`PresheafOfModules.exteriorAlgebraPieceVal_exteriorKoszulD_gen_mul`.

## References

* [Stacks Project, Tag 062K](https://stacks.math.columbia.edu/tag/062K)
* [Stacks Project, Tag 0622](https://stacks.math.columbia.edu/tag/0622)
-/

@[expose] public section

open CategoryTheory Opposite

open scoped ExteriorAlgebra

universe v u w a

namespace Koszul

variable {R : Type u} [CommRing R] {E : Type v} [AddCommGroup E] [Module R E]

/-- The sign of a nonnegative degree, written as the integer unit `Int.negOnePow` acting on the
exterior algebra, is the ring element `(-1) ^ n` acting on it. -/
theorem negOnePow_natCast_zsmul (k : ℕ) (z : ExteriorAlgebra R E) :
    ((Int.negOnePow (k : ℤ) : ℤ)) • z = ((-1 : R) ^ k) • z := by
  rcases Nat.even_or_odd k with h | h
  · rw [h.neg_one_pow, one_smul, Int.negOnePow_even (k : ℤ) (by exact_mod_cast h),
      Units.val_one, one_zsmul]
  · rw [h.neg_one_pow, Int.negOnePow_odd (k : ℤ) (by exact_mod_cast h), Units.val_neg,
      Units.val_one, neg_zsmul, one_zsmul, neg_smul, one_smul]

/-- **The graded Leibniz rule for the Koszul contraction.** Contraction by a functional is an
antiderivation of the exterior algebra: on a product whose left factor lies in the `ℤ`-indexed
exterior power of degree `n`, it is contraction of the left factor times the right factor plus
`(-1) ^ n` times the left factor times the contraction of the right one. -/
theorem contraction_mul_of_mem_intPiece (φ : Module.Dual R E) (n : ℤ)
    {a : ExteriorAlgebra R E} (ha : a ∈ ExteriorAlgebra.intPiece R E n)
    (b : ExteriorAlgebra R E) :
    contraction φ (a * b) =
      contraction φ a * b + (Int.negOnePow n : ℤ) • (a * contraction φ b) := by
  cases n with
  | ofNat k =>
    exact ((differentialGradedAlgebra φ).differential_mul_of_mem k ha b).trans
      (congrArg (fun t => contraction φ a * b + t) (negOnePow_natCast_zsmul k _).symm)
  | negSucc k =>
    rw [ExteriorAlgebra.eq_zero_of_mem_intPiece_of_neg R E (by omega) ha]
    simp

end Koszul

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  {F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)}
  (φ : ExteriorFunctional.{v, u, w, a} F)

/-- **The Koszul differential between two independently named degrees.** For degrees `p` and `q`
with `q + 1 = p` it is `PresheafOfModules.exteriorKoszulD` in degree `q`, transported along that
equality; on local sections it is still contraction by the functional. -/
noncomputable def exteriorKoszulDOf {p q : ℤ} (h : q + 1 = p) :
    exteriorAlgebraPiece p F ⟶ exteriorAlgebraPiece q F :=
  h ▸ exteriorKoszulD F φ q

/-- **On local sections `PresheafOfModules.exteriorKoszulDOf` is contraction.** -/
theorem exteriorAlgebraPieceVal_exteriorKoszulDOf {p q : ℤ} (h : q + 1 = p) (X : Cᵒᵖ)
    (z : (exteriorAlgebraPiece p F).obj X) :
    exteriorAlgebraPieceVal q F X (Hom.app (exteriorKoszulDOf φ h) X z) =
      Koszul.contraction (φ.dual X) (exteriorAlgebraPieceVal p F X z) := by
  subst h
  exact exteriorAlgebraPieceVal_exteriorKoszulD F φ q X z

/-- **`PresheafOfModules.exteriorKoszulDOf` squares to zero.** -/
theorem exteriorKoszulDOf_comp_exteriorKoszulDOf {p q r : ℤ} (h : q + 1 = p) (h' : r + 1 = q) :
    exteriorKoszulDOf φ h ≫ exteriorKoszulDOf φ h' = 0 := by
  subst h'
  subst h
  exact exteriorKoszulD_comp_exteriorKoszulD F φ r

/-- **The graded Leibniz rule for the Koszul differential of a presheaf of modules, for a
homogeneous left factor of any degree.** The product of a section `x` of degree `p` and a section
`y` of degree `q` is taken as a separate section `z`, together with the hypothesis that its value
is the product; the rule then reads
`d (x ∧ y) = d x ∧ y + (-1)^p · (x ∧ d y)` with both sides written in the exterior algebra of the
sections over `X`. -/
theorem exteriorAlgebraPieceVal_exteriorKoszulDOf_mul (p q : ℤ) {m n : ℤ} (h : n + 1 = m)
    (X : Cᵒᵖ) (x : (exteriorAlgebraPiece p F).obj X) (y : (exteriorAlgebraPiece q F).obj X)
    (z : (exteriorAlgebraPiece m F).obj X)
    (hz : exteriorAlgebraPieceVal m F X z =
      exteriorAlgebraPieceVal p F X x * exteriorAlgebraPieceVal q F X y) :
    exteriorAlgebraPieceVal n F X (Hom.app (exteriorKoszulDOf φ h) X z) =
      Koszul.contraction (φ.dual X) (exteriorAlgebraPieceVal p F X x) *
          exteriorAlgebraPieceVal q F X y +
        (Int.negOnePow p : ℤ) • (exteriorAlgebraPieceVal p F X x *
          Koszul.contraction (φ.dual X) (exteriorAlgebraPieceVal q F X y)) := by
  rw [exteriorAlgebraPieceVal_exteriorKoszulDOf, hz]
  exact Koszul.contraction_mul_of_mem_intPiece (φ.dual X) p x.2 _

end PresheafOfModules

end
