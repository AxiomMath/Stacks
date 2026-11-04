module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraSheafification
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedForgetColimits

/-!
# Negating the grading of a sheaf of graded algebras

A sheaf of graded algebras `A` (`SheafOfModules.GradedAlgebra`) is graded by `ℤ`, and the
differential of a sheaf of differential graded algebras
(`SheafOfModules.DifferentialGradedAlgebra`) *raises* that grading by one, because its underlying
complex is a `CochainComplex`. The Koszul differential lowers the exterior grading by one, so an
exterior algebra carrying it has to be read with the grading negated before it can be a sheaf of
differential graded algebras. This file performs that reindexing:
`SheafOfModules.GradedAlgebra.negate A` has `A.piece (-n)` in degree `n`.

The reindexing is not a relabelling of a family alone: the multiplication of `A` in degrees `-i`
and `-j` lands in `A.piece (-i + -j)`, whereas degree `i + j` of the reindexed algebra is
`A.piece (-(i + j))`. Those two integers are equal but not definitionally so, so the
multiplication has to be transported along the equality, which is what
`SheafOfModules.BilinearMap.castCodomain` does.

## Main definitions

* `SheafOfModules.BilinearMap.castCodomain`: a bilinear map of sheaves of modules whose codomain
  is transported along an equality of degrees.
* `SheafOfModules.GradedAlgebra.negate`: **a sheaf of graded algebras with its grading
  negated.**

## Main results

* `SheafOfModules.gradedCast_apply_const`, `gradedCast_zsmul`,
  `gradedCast_comp`, `SheafOfModules.heq_gradedCast`, `restriction_gradedCast`,
  `restriction_zsmul_gradedCast` and `restriction_gradedCast_add_zsmul`: the elementary calculus
  of `SheafOfModules.gradedCast`. Each is proved by substituting the degree equality, and
  together they are what lets a law stated with `gradedCast` be reduced to one with none.
  Additivity and the composite of two transports are the general
  `SheafOfModules.gradedCast_add` and `SheafOfModules.gradedCast_trans` of
  `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedForgetColimits`, stated for an arbitrary
  family of types rather than for a family of sheaves of modules; commutation with a degreewise
  family of maps is `SheafOfModules.gradedCast_dependent` of
  `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedRelativeTensorUnitor`.
* `SheafOfModules.BilinearMap.castCodomain_app`: the transported bilinear map on sections is the
  transport of the original value.
* `SheafOfModules.GradedAlgebra.negate_piece`, `negate_mul_app` and `negate_one`: the three data
  of the reindexed algebra.

## Implementation notes

**The laws of the reindexed algebra are proved by eliminating the transports, not by computing
with them.** Associativity of `negate A` has transports both outside and *inside* the arguments
of the multiplication. The outer ones are removed by `SheafOfModules.heq_gradedCast`, which says
a transported section is heterogeneously equal to the section itself; the inner ones by
`Stacks.heq_apply`, degreewise congruence, applied to the one-variable map obtained by freezing
the other argument. What is left is `A.mul_assoc` at the negated degrees.

**`negate` needs no transport in degree zero.** The unit of `negate A` is the unit of `A`,
because `-(0 : ℤ)` reduces to `0`.

## References

* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
* [Stacks Project, Tag 0FRF](https://stacks.math.columbia.edu/tag/0FRF)
-/

@[expose] public section

open CategoryTheory Opposite

universe t a v u

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

/-! ### The calculus of degree transports -/

/-- A degreewise family of maps into a *fixed* type does not see a transport. -/
theorem gradedCast_apply_const {ι : Type*} (B : ι → Type*) (D : Type*) (g : ∀ i, B i → D)
    {i j : ι} (h : i = j) (x : B i) : g j (gradedCast B h x) = g i x := by
  subst h; rfl

/-- A transport along an equality of degrees commutes with the action of the integers. -/
theorem gradedCast_zsmul (K : ℤ → SheafOfModules.{a} R) {i j : ℤ} (h : i = j) (U : Cᵒᵖ)
    (c : ℤ) (x : (K i).val.obj U) :
    gradedCast (fun q ↦ (K q).val.obj U) h (c • x) =
      c • gradedCast (fun q ↦ (K q).val.obj U) h x := by
  subst h; rfl

/-- A transport in a family reindexed through a map of index types is a transport in the
original family, along the image of the equality. -/
theorem gradedCast_comp {ι κ : Type*} (B : κ → Type*) (g : ι → κ) {i j : ι} (h : i = j)
    (x : B (g i)) :
    gradedCast (fun t ↦ B (g t)) h x = gradedCast B (congrArg g h) x := by
  subst h; rfl

/-- A transported term is heterogeneously equal to the term itself. -/
theorem heq_gradedCast {ι : Type*} (B : ι → Type*) {i j : ι} (h : i = j) (x : B i) :
    HEq (gradedCast B h x) x := by
  subst h; rfl

/-- A transport along an equality of degrees commutes with restriction. -/
theorem restriction_gradedCast (K : ℤ → SheafOfModules.{a} R) {i j : ℤ} (h : i = j)
    {U V : Cᵒᵖ} (f : U ⟶ V) (x : (K i).val.obj U) :
    (K j).val.map f (gradedCast (fun q ↦ (K q).val.obj U) h x) =
      gradedCast (fun q ↦ (K q).val.obj V) h ((K i).val.map f x) := by
  subst h; rfl

/-- Restriction of an integer multiple of a transported section. -/
theorem restriction_zsmul_gradedCast (K : ℤ → SheafOfModules.{a} R) {i j : ℤ} (h : i = j)
    {U V : Cᵒᵖ} (f : U ⟶ V) (c : ℤ) (x : (K i).val.obj U) :
    (K j).val.map f (c • gradedCast (fun t ↦ (K t).val.obj U) h x) =
      c • gradedCast (fun t ↦ (K t).val.obj V) h ((K i).val.map f x) := by
  simp [restriction_gradedCast]
  rfl

/-- **Restriction of the sum of two transported sections and an integer multiple of a third.**
This is the combination of `SheafOfModules.restriction_gradedCast` with additivity of restriction
that the Leibniz rule of a differential graded algebra is read along a covering sieve by; it is
stated as one lemma because the two sides mention the transports at two different objects of the
site, which no sequence of rewrites can relate without naming the families by hand. -/
theorem restriction_gradedCast_add_zsmul (K : ℤ → SheafOfModules.{a} R) {i j k : ℤ}
    (hi : i = k) (hj : j = k) {U V : Cᵒᵖ} (f : U ⟶ V) (c : ℤ) (x : (K i).val.obj U)
    (y : (K j).val.obj U) :
    (K k).val.map f (gradedCast (fun t ↦ (K t).val.obj U) hi x +
        c • gradedCast (fun t ↦ (K t).val.obj U) hj y) =
      gradedCast (fun t ↦ (K t).val.obj V) hi ((K i).val.map f x) +
        c • gradedCast (fun t ↦ (K t).val.obj V) hj ((K j).val.map f y) := by
  subst hi hj
  simp
  rfl

/-! ### Transporting the codomain of a bilinear map -/

namespace BilinearMap

/-- **A bilinear map of sheaves of modules with its codomain transported along an equality of
degrees.** This is what makes the multiplication of a graded algebra survive a reindexing of the
grading: the degrees of the codomain before and after the reindexing are equal, but not
definitionally. -/
noncomputable def castCodomain {M N : SheafOfModules.{a} R} {Q : ℤ → SheafOfModules.{a} R}
    {i j : ℤ} (h : i = j) (β : BilinearMap M N (Q i)) : BilinearMap M N (Q j) := h ▸ β

/-- The transported bilinear map on local sections: the transport of the original value. -/
theorem castCodomain_app {M N : SheafOfModules.{a} R} {Q : ℤ → SheafOfModules.{a} R}
    {i j : ℤ} (h : i = j) (β : BilinearMap M N (Q i)) (U : Cᵒᵖ) (x : M.val.obj U)
    (y : N.val.obj U) :
    (castCodomain h β).app U x y =
      gradedCast (fun q ↦ (Q q).val.obj U) h (β.app U x y) := by
  subst h; rfl

end BilinearMap

/-! ### The grading of a sheaf of graded algebras, negated -/

namespace GradedAlgebra

/-- **A sheaf of graded algebras with its grading negated**: in degree `n` it is the piece of
degree `-n` of the given algebra, and the product of a section of degree `i` and one of degree
`j` is their product in `A`, transported from degree `-i + -j` to degree `-(i + j)`. -/
noncomputable def negate (A : GradedAlgebra.{t, a} R) : GradedAlgebra.{t, a} R where
  piece n := A.piece (-n)
  mul i j := BilinearMap.castCodomain (Q := A.piece) (neg_add i j).symm (A.mul (-i) (-j))
  one := A.one
  mul_assoc i j k U x y z := by
    have hx := (heq_gradedCast (fun q : ℤ => ((A.piece q).val.obj U : Type _))
      (neg_add i j).symm ((A.mul (-i) (-j)).app U x y)).symm
    have hy := (heq_gradedCast (fun q : ℤ => ((A.piece q).val.obj U : Type _))
      (neg_add j k).symm ((A.mul (-j) (-k)).app U y z)).symm
    rw [BilinearMap.castCodomain_app, BilinearMap.castCodomain_app,
      BilinearMap.castCodomain_app, BilinearMap.castCodomain_app]
    refine (heq_gradedCast _ _ _).trans (HEq.trans ?_ (heq_gradedCast _ _ _).symm)
    refine HEq.trans (Stacks.heq_apply (fun p => (A.piece p).val.obj U)
      (fun p => (A.piece (p + -k)).val.obj U) (fun p s => (A.mul p (-k)).app U s z)
      (neg_add i j).symm hx).symm ?_
    refine HEq.trans (A.mul_assoc (-i) (-j) (-k) U x y z) ?_
    exact Stacks.heq_apply (fun q => (A.piece q).val.obj U)
      (fun q => (A.piece (-i + q)).val.obj U) (fun q s => (A.mul (-i) q).app U x s)
      (neg_add j k).symm hy
  one_mul i U x := by
    rw [BilinearMap.castCodomain_app]
    exact (heq_gradedCast _ _ _).trans (A.one_mul (-i) U x)
  mul_one i U x := by
    rw [BilinearMap.castCodomain_app]
    exact (heq_gradedCast _ _ _).trans (A.mul_one (-i) U x)

variable (A : GradedAlgebra.{t, a} R)

/-- The piece of degree `n` of `A.negate` is the piece of degree `-n` of `A`. -/
@[simp]
theorem negate_piece (n : ℤ) : A.negate.piece n = A.piece (-n) := rfl

/-- The unit of `A.negate` is the unit of `A`. -/
@[simp]
theorem negate_one : A.negate.one = A.one := rfl

/-- On local sections, the product in `A.negate` of sections of degrees `i` and `j` is their
product in `A`, transported from degree `-i + -j` to degree `-(i + j)`. -/
theorem negate_mul_app (i j : ℤ) (U : Cᵒᵖ) (x : (A.piece (-i)).val.obj U)
    (y : (A.piece (-j)).val.obj U) :
    (A.negate.mul i j).app U x y =
      gradedCast (fun q ↦ (A.piece q).val.obj U) (neg_add i j).symm
        ((A.mul (-i) (-j)).app U x y) :=
  BilinearMap.castCodomain_app (Q := A.piece) (neg_add i j).symm (A.mul (-i) (-j)) U x y

end GradedAlgebra

end SheafOfModules

end
