module

public import StacksFrontier.AlgebraicGeometry.SymGenDegreeOne.Sections
public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.Scheme
public import StacksFrontier.AlgebraicGeometry.RelativeProjBridge.SectionRing
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricAlgebraGrading

/-!
# `Sym(E)` is generated in degree one over every affine open

Let `X` be a scheme and `E` a quasi-coherent `𝒪_X`-module, and let
`A = Stacks.SymGraded.schemeSheafGradedAlgebra E hqc` be the symmetric algebra `Sym(E)` as the
sheaf-level graded algebra data of Situation 01NN. Its graded ring of sections over an open `U`
is the direct sum `⨁ n : ℕ, Γ(Sym^n(E), U)`. Over an affine open that ring is generated in
degree one over its degree-zero part, i.e.

`Algebra.adjoin (A.grading U 0) (A.grading U 1) = ⊤` for every affine open `U`.

## Main definitions

* `Stacks.SymGraded.unitSection`: **the sheafification unit on sections**, sending a homogeneous
  element of degree `m` of `Sym_{Γ(X, U)}(Γ(E, U))` to a section of `Sym^m(E)` over `U`.
* `Stacks.SymGraded.degreeOneSubalgebra`: the subalgebra of the graded ring of sections generated
  by the degree-one part over the degree-zero part.

## Main results

* `Stacks.SymGraded.unitSection_mul`: **the unit is multiplicative.** This is the reusable
  content, and it is free: `Stacks.GradedAlgebra.sheafify_mul_unit` says the sheafified
  multiplication agrees with the given one on unit-images, and the multiplication of `Sym(E)` is
  the sheafification of the sectionwise one by definition.
* `Stacks.SymGraded.of_unitSection_mul`: the same, read in the graded ring of sections, where it
  becomes `of m (unit x) * of n (unit y) = of (m + n) (unit (x * y))`.
* `Stacks.SymGraded.surjective_unitSection`: over an affine open the unit is surjective.
* `Stacks.SymGraded.adjoin_grading_one_eq_top`: **the target.** `Sym(E)` is generated in degree
  one over every affine open.

## Implementation notes

**Why multiplicativity of the unit, and not of `sheafificationIsoTilde`.** The identification of
the restricted piece with an associated sheaf
(`Stacks.SymGraded.AffinePieces.sheafificationIsoTilde`) is an isomorphism of *modules* and
nothing proves it multiplicative; it is assembled from `sheafification`, a counit and two local
bijectivity statements, none of which sees the graded multiplication. The sheafification *unit*
is multiplicative by construction, since the sheafified algebra's multiplication is *defined* by
extending the presheaf one along it. So the proof uses the isomorphism only through its
consequence that the unit is surjective on the sections over an affine open, and does the algebra
on the presheaf side, where the multiplication is the honest product of
`SymmetricAlgebra Γ(X, U) Γ(E, U)`.

**The induction needs no degree-one generators.** The step from `m` to `m + 1` writes
`Sym^{m+1} = Sym^m · Sym^1` (`Submodule.pow_succ` on the range of
`SymmetricAlgebra.ι`) and runs `Submodule.mul_induction_on`. For the degree-one factor nothing
has to be said at all: *every* element of `A.grading U 1` is a generator of the subalgebra by
definition, so there is no need to know it is a product of elements in the image of `ι`. In
particular `SymmetricAlgebra.symmetricPower_eq_span_prod_ι` is not used, and neither are the
`Fin n`-indexed products it is stated with.

**The membership proof is carried in an existential.** `Submodule.mul_induction_on` has a motive
`SymmetricAlgebra Γ(X, U) Γ(E, U) → Prop` with no membership argument, while the statement being
proved is about the *subtype* `Sym^{m+1}`. Taking the motive to be
`fun y => ∃ h : y ∈ Sym^{m+1}, …` supplies the missing membership in the additive case, where it
is otherwise unavailable; the value `unitSection … ⟨y, h⟩` does not depend on `h`, by proof
irrelevance.

**Degrees are indexed by `ℕ` throughout.** `unitSection` is stated at `(m : ℕ)` rather than at
`(n : ℤ)` so that its codomain is literally `A.sectionPieces U m`; the `ℤ`-indexed spelling makes
`DirectSum.of` reject it under `rw`, which works at `instances` transparency and will not unfold
the `def` `schemeSheafGradedAlgebra`. The two degree spellings `(m : ℤ) + (n : ℤ)` and
`((m + n : ℕ) : ℤ)` are definitionally equal, so no transport appears.

## References

* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.SheafSymmetricAlgebra

namespace Stacks.SymGraded

universe u

variable {X : Scheme.{u}} (E : X.Modules) (U : X.Opens) (hqc : IsQuasicoherentPieces E)

/-- **The sheafification unit on sections.** A homogeneous element of degree `m` of the symmetric
algebra of `Γ(E, U)` over `Γ(X, U)` determines a homogeneous section of degree `m` of the graded
algebra `Sym(E)` over `U`. -/
def unitSection (m : ℕ) (x : gradedPiece (R := Γ(X, U)) Γ(E, U) (m : ℤ)) :
    (schemeSheafGradedAlgebra E hqc).sectionPieces U m :=
  PresheafOfModules.Hom.app
    (PresheafOfModules.sheafifyUnit (𝟙 X.ringCatSheaf.obj) (siteGradedPiece E.val (m : ℤ)))
    (op U) x

/-- The unit on sections is additive. -/
theorem unitSection_add (m : ℕ) (x y : gradedPiece (R := Γ(X, U)) Γ(E, U) (m : ℤ)) :
    unitSection E U hqc m (x + y) = unitSection E U hqc m x + unitSection E U hqc m y :=
  map_add _ x y

/-- **The unit is multiplicative**: it carries the graded multiplication of the symmetric algebra
of the sections to the multiplication of `Sym(E)`. This is
`Stacks.GradedAlgebra.sheafify_mul_unit` for the sectionwise symmetric algebra. -/
theorem unitSection_mul (i j : ℕ) (x : gradedPiece (R := Γ(X, U)) Γ(E, U) (i : ℤ))
    (y : gradedPiece (R := Γ(X, U)) Γ(E, U) (j : ℤ)) :
    ((schemeSheafGradedAlgebra E hqc).mul (i : ℤ) (j : ℤ)).app U
        (unitSection E U hqc i x) (unitSection E U hqc j y) =
      unitSection E U hqc (i + j) (symMulₗ Γ(E, U) (i : ℤ) (j : ℤ) x y) :=
  (sitePresheafAlgebra E.val).sheafify_mul_unit (𝟙 X.ringCatSheaf.obj)
    (i : ℤ) (j : ℤ) (op U) x y

/-- The unit is multiplicative, read in the graded ring of sections. -/
theorem of_unitSection_mul (i j : ℕ) (x : gradedPiece (R := Γ(X, U)) Γ(E, U) (i : ℤ))
    (y : gradedPiece (R := Γ(X, U)) Γ(E, U) (j : ℤ)) :
    DirectSum.of ((schemeSheafGradedAlgebra E hqc).sectionPieces U) i (unitSection E U hqc i x) *
        DirectSum.of ((schemeSheafGradedAlgebra E hqc).sectionPieces U) j
          (unitSection E U hqc j y) =
      DirectSum.of ((schemeSheafGradedAlgebra E hqc).sectionPieces U) (i + j)
        (unitSection E U hqc (i + j) (symMulₗ Γ(E, U) (i : ℤ) (j : ℤ) x y)) :=
  (DirectSum.of_mul_of (unitSection E U hqc i x) (unitSection E U hqc j y)).trans
    (congrArg (DirectSum.of ((schemeSheafGradedAlgebra E hqc).sectionPieces U) (i + j))
      (((schemeSheafGradedAlgebra E hqc).gMul_def U (unitSection E U hqc i x)
        (unitSection E U hqc j y)).trans (unitSection_mul E U hqc i j x y)))

/-- The subalgebra of the graded ring of sections generated in degree one over degree zero. -/
abbrev degreeOneSubalgebra : Subalgebra ((schemeSheafGradedAlgebra E hqc).grading U 0)
    ((schemeSheafGradedAlgebra E hqc).sectionRing U) :=
  Algebra.adjoin ((schemeSheafGradedAlgebra E hqc).grading U 0)
    (((schemeSheafGradedAlgebra E hqc).grading U 1 :
      Set ((schemeSheafGradedAlgebra E hqc).sectionRing U)))

/-- Every homogeneous section of degree zero lies in the subalgebra generated in degree one. -/
theorem of_zero_mem (z : (schemeSheafGradedAlgebra E hqc).sectionPieces U 0) :
    DirectSum.of ((schemeSheafGradedAlgebra E hqc).sectionPieces U) 0 z ∈
      degreeOneSubalgebra E U hqc :=
  Subalgebra.algebraMap_mem _
    (⟨DirectSum.of ((schemeSheafGradedAlgebra E hqc).sectionPieces U) 0 z,
      (schemeSheafGradedAlgebra E hqc).of_mem_grading U z⟩ :
      (schemeSheafGradedAlgebra E hqc).grading U 0)

/-- Every homogeneous section of degree one lies in the subalgebra generated in degree one. -/
theorem of_one_mem (z : (schemeSheafGradedAlgebra E hqc).sectionPieces U 1) :
    DirectSum.of ((schemeSheafGradedAlgebra E hqc).sectionPieces U) 1 z ∈
      degreeOneSubalgebra E U hqc :=
  Algebra.subset_adjoin ((schemeSheafGradedAlgebra E hqc).of_mem_grading U z)

/-- The degree-`m+1` part of the symmetric algebra of the sections is the product of the
degree-`m` part and the degree-one part. -/
theorem symmetricPower_succ_eq_mul (m : ℕ) :
    SymPow.symmetricPower (m + 1) Γ(X, U) Γ(E, U) =
      SymPow.symmetricPower m Γ(X, U) Γ(E, U) * SymPow.symmetricPower 1 Γ(X, U) Γ(E, U) := by
  rw [SymPow.symmetricPower, SymPow.symmetricPower, SymPow.symmetricPower, pow_succ, pow_one]

/-- The inductive step: an element of `Sym^{m+1}` is a sum of products of an element of `Sym^m`
with an element of `Sym^1`, and the unit carries such a product to a product of homogeneous
sections of degrees `m` and `1`. -/
theorem of_unitSection_mem_of_mul (m : ℕ)
    (IH : ∀ w : (schemeSheafGradedAlgebra E hqc).sectionPieces U m,
      DirectSum.of ((schemeSheafGradedAlgebra E hqc).sectionPieces U) m w ∈
        degreeOneSubalgebra E U hqc)
    (y : SymmetricAlgebra Γ(X, U) Γ(E, U))
    (hy : y ∈ SymPow.symmetricPower m Γ(X, U) Γ(E, U) *
      SymPow.symmetricPower 1 Γ(X, U) Γ(E, U)) :
    ∃ h : y ∈ SymPow.symmetricPower (m + 1) Γ(X, U) Γ(E, U),
      DirectSum.of ((schemeSheafGradedAlgebra E hqc).sectionPieces U) (m + 1)
        (unitSection E U hqc (m + 1) ⟨y, h⟩) ∈ degreeOneSubalgebra E U hqc := by
  refine Submodule.mul_induction_on hy ?_ ?_
  · intro a ha b hb
    have hab : a * b ∈ SymPow.symmetricPower (m + 1) Γ(X, U) Γ(E, U) := by
      rw [symmetricPower_succ_eq_mul]
      exact Submodule.mul_mem_mul ha hb
    refine ⟨hab, ?_⟩
    have hmem := mul_mem (IH (unitSection E U hqc m ⟨a, ha⟩))
      (of_one_mem E U hqc (unitSection E U hqc 1 ⟨b, hb⟩))
    rwa [of_unitSection_mul E U hqc m 1 ⟨a, ha⟩ ⟨b, hb⟩] at hmem
  · rintro p q ⟨hp, hpB⟩ ⟨hq, hqB⟩
    refine ⟨add_mem hp hq, ?_⟩
    have hadd : (⟨p + q, add_mem hp hq⟩ :
          gradedPiece (R := Γ(X, U)) Γ(E, U) ((m + 1 : ℕ) : ℤ)) =
        (⟨p, hp⟩ : gradedPiece (R := Γ(X, U)) Γ(E, U) ((m + 1 : ℕ) : ℤ)) + ⟨q, hq⟩ :=
      Subtype.ext rfl
    rw [hadd, unitSection_add, map_add]
    exact add_mem hpB hqB

/-- **Every homogeneous section of `Sym(E)` of degree `m` over an affine open is the unit-image
of an element of `Sym^m` of the sections**: this is
`Stacks.SymGraded.AffinePieces.surjective_sheafifyUnit_image_top` at `fromSpec ''ᵁ ⊤ = U`. -/
theorem surjective_unitSection [E.IsQuasicoherent] (hU : IsAffineOpen U) (m : ℕ) :
    Function.Surjective (unitSection E U hqc m) :=
  AffinePieces.surjective_sheafifyUnit_image_top E hU (m : ℤ) U
    ((Scheme.Hom.image_top_eq_opensRange _).trans hU.opensRange_fromSpec)

/-- **Every homogeneous section of `Sym(E)` over an affine open lies in the subalgebra generated
in degree one.** -/
theorem of_mem_degreeOneSubalgebra [E.IsQuasicoherent] (hU : IsAffineOpen U) :
    ∀ (m : ℕ) (z : (schemeSheafGradedAlgebra E hqc).sectionPieces U m),
      DirectSum.of ((schemeSheafGradedAlgebra E hqc).sectionPieces U) m z ∈
        degreeOneSubalgebra E U hqc := by
  intro m
  induction m with
  | zero => exact of_zero_mem E U hqc
  | succ m IH =>
    intro z
    obtain ⟨x, hx'⟩ := surjective_unitSection E U hqc hU (m + 1) z
    have hxmem : (x : SymmetricAlgebra Γ(X, U) Γ(E, U)) ∈
        SymPow.symmetricPower m Γ(X, U) Γ(E, U) *
          SymPow.symmetricPower 1 Γ(X, U) Γ(E, U) := by
      rw [← symmetricPower_succ_eq_mul]
      exact x.2
    obtain ⟨h, hmem⟩ := of_unitSection_mem_of_mul E U hqc m IH _ hxmem
    have hz : DirectSum.of ((schemeSheafGradedAlgebra E hqc).sectionPieces U) (m + 1) z =
        DirectSum.of ((schemeSheafGradedAlgebra E hqc).sectionPieces U) (m + 1)
          (unitSection E U hqc (m + 1)
            ⟨(x : SymmetricAlgebra Γ(X, U) Γ(E, U)), h⟩) :=
      congrArg _ (hx'.symm.trans (congrArg (unitSection E U hqc (m + 1)) (Subtype.ext rfl)))
    rw [hz]
    exact hmem

/-- **`Sym(E)` is generated in degree one over every affine open of the base**, for `E` a
quasi-coherent module on an arbitrary scheme. -/
theorem adjoin_grading_one_eq_top [E.IsQuasicoherent] (hU : IsAffineOpen U) :
    Algebra.adjoin ((schemeSheafGradedAlgebra E hqc).grading U 0)
        (((schemeSheafGradedAlgebra E hqc).grading U 1 :
          Set ((schemeSheafGradedAlgebra E hqc).sectionRing U))) = ⊤ := by
  refine Algebra.eq_top_iff.2 fun w => ?_
  induction w using DirectSum.induction_on with
  | zero => exact zero_mem _
  | of m z => exact of_mem_degreeOneSubalgebra E U hqc hU m z
  | add p q hp hq => exact add_mem hp hq

end Stacks.SymGraded

end
