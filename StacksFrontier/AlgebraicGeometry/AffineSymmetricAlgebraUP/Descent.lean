module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPowerSheafification
public import StacksFrontier.AlgebraicGeometry.AffineSymmetricAlgebraUP.HomExtend

/-!
# Descending a degreewise morphism along a locally bijective comparison

`Stacks.GradedAlgebra.ofComparison` builds a sheaf of graded algebras out of a graded algebra
`A` of presheaves of modules and a degreewise locally bijective comparison `u n : P n ⟶ (S n).val`
into a family of sheaves. **This file proves its universal property**: a degreewise morphism
`g n : P n ⟶ (B.piece n).val` into a sheaf of graded algebras which is multiplicative on
homogeneous local sections and carries the unit to the unit extends uniquely to a unital
homomorphism out of `A.ofComparison S u`.

It also records the two facts about the ungraded realization of a graded algebra of presheaves
that a consumer of `Stacks.GradedAlgebra.proj` needs and
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPowerSheafification` does not state: the
projection kills the other homogeneous components, and it commutes with restriction.

## Main definitions

* `Stacks.GradedAlgebra.descCmpApp`: the degreewise morphism out of `A.ofComparison S u`
  determined by a degreewise morphism out of `P`, obtained from `Stacks.homExtend`.

## Main results

* `Stacks.GradedAlgebra.proj_incl_of_ne` and `Stacks.GradedAlgebra.sectionRestrict_proj`: the
  projection of the ungraded realization onto a homogeneous component vanishes on the other
  components and commutes with the restriction maps.
* `Stacks.GradedAlgebra.app_homogeneousProd`: **a degreewise multiplicative unital family of
  morphisms carries the ordered product of degree-one sections to the ordered product of their
  images.** Both the comparison of `ofComparison` and a `UnitalHom` of sheaves of graded algebras
  are such a family, and this is the lemma by which the degree-`n` component of a homomorphism
  out of a symmetric algebra is pinned down by its degree-one component.
* `Stacks.GradedAlgebra.existsUnique_descCmp`: **the universal property of `ofComparison`**, the
  exact analogue for a locally bijective comparison of
  `Stacks.GradedAlgebra.existsUnique_desc` for the sheafification.

## Implementation notes

The projection lemmas are stated over a presheaf of *commutative* rings, because
`Stacks.GradedAlgebra.proj` is: the symmetric-algebra consumer needs the sections of the base to
carry a `CommRing` instance, and that instance is found only for the spelling
`O ⋙ forget₂ CommRingCat RingCat`.

`Stacks.GradedAlgebra.sectionRestrict_proj` is stated with `Stacks.sectionRestrict` rather than
with `(Pc i).map f` so that the target type is written as `(Pc i).obj Y` and not as a restriction
of scalars, which is what lets it be rewritten with.

## References

* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite PresheafOfModules

universe v u t a w

namespace Stacks.GradedAlgebra

/-! ### The projection onto a homogeneous component -/

section Proj

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  {Pc : ℤ → PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)} (A : Stacks.GradedAlgebra Pc)

/-- The projection onto the degree-`i` component kills every other homogeneous component. -/
theorem proj_incl_of_ne (X : Cᵒᵖ) {i j : ℤ} (h : j ≠ i) (x : (Pc j).obj X) :
    A.proj X i (A.incl j x) = 0 := by
  change DirectSum.component _ ℤ (fun k => ((Pc k).obj X : Type (max w a))) i
    (DirectSum.of (fun k => ((Pc k).obj X : Type (max w a))) j x) = 0
  rw [← DirectSum.lof_eq_of ((O ⋙ forget₂ _ RingCat).obj X), DirectSum.component.of]
  exact dite_eq_right h

/-- The projection onto a homogeneous component commutes with the restriction maps. -/
theorem sectionRestrict_proj {X Y : Cᵒᵖ} (f : X ⟶ Y) (i : ℤ) (z : A.Total X) :
    Stacks.sectionRestrict (Pc i) f (A.proj X i z) = A.proj Y i (A.totalRestrict f z) := by
  induction z using A.incl_induction with
  | zero => simp only [map_zero]
  | incl j y =>
      rcases eq_or_ne j i with rfl | hne
      · rw [A.proj_incl, A.totalRestrict_incl, A.proj_incl]
      · rw [A.proj_incl_of_ne X hne, A.totalRestrict_incl, A.proj_incl_of_ne Y hne, map_zero]
  | add z z' hz hz' => simp only [map_add, hz, hz']

end Proj

/-! ### Degreewise multiplicative families and ordered products -/

section HomogeneousProd

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  {Pc Qc : ℤ → PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)}
  (A : Stacks.GradedAlgebra Pc) (D : Stacks.GradedAlgebra Qc) (ap : ∀ n : ℤ, Pc n ⟶ Qc n)

/-- **A degreewise multiplicative unital family of morphisms preserves the ordered product of
degree-one local sections.** This is what makes the degree-`n` component of such a family
determined by its degree-one component on a graded algebra generated in degree one. -/
theorem app_homogeneousProd
    (hmul : ∀ (i j : ℤ) (X : Cᵒᵖ) (x : (Pc i).obj X) (y : (Pc j).obj X),
      Hom.app (ap (i + j)) X ((A.mul i j).app X x y) =
        (D.mul i j).app X (Hom.app (ap i) X x) (Hom.app (ap j) X y))
    (hone : ∀ X : Cᵒᵖ, Hom.app (ap 0) X (A.one.eval X) = D.one.eval X)
    (X : Cᵒᵖ) (n : ℕ) (z : Fin n → (Pc 1).obj X) :
    Hom.app (ap (n : ℤ)) X (A.homogeneousProd X n z) =
      D.homogeneousProd X n fun i => Hom.app (ap 1) X (z i) := by
  induction n with
  | zero => exact hone X
  | succ n ih =>
      change Hom.app (ap ((n : ℤ) + 1)) X
        ((A.mul (n : ℤ) 1).app X (A.homogeneousProd X n fun i => z i.castSucc)
          (z (Fin.last n))) = _
      rw [hmul (n : ℤ) 1 X _ _, ih fun i => z i.castSucc]
      rfl

end HomogeneousProd

/-! ### The universal property of `ofComparison` -/

section Descent

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {P : ℤ → PresheafOfModules.{a} R.obj} (A : GradedAlgebra P)
  (S : ℤ → SheafOfModules.{a} R) (u : ∀ n, P n ⟶ (S n).val)
  [∀ n, PresheafOfModules.IsLocallySurjective J (u n)]
  [∀ n, PresheafOfModules.IsLocallyInjective J (u n)]
  {B : SheafOfModules.GradedAlgebra.{t, a} R}
  (g : ∀ n : ℤ, P n ⟶ (B.piece n).val)

/-- The degreewise morphism out of the transported algebra determined by a degreewise morphism
out of the graded algebra of presheaves. -/
def descCmpApp (n : ℤ) : (A.ofComparison S u).piece n ⟶ B.piece n :=
  ⟨(Stacks.homExtend (B.piece n).isSheaf (u n) (g n) : (S n).val ⟶ (B.piece n).val)⟩

/-- On local sections, `descCmpApp` composed with the comparison map `u n` is `g n`. -/
theorem descCmpApp_comparison (n : ℤ) (X : Cᵒᵖ) (s : (P n).obj X) :
    (A.descCmpApp S u g n).val.app X (Hom.app (u n) X s) = Hom.app (g n) X s :=
  Stacks.homExtend_comparison (T := (S n).val) (B.piece n).isSheaf (u n) (g n) X s

variable
  (hmul : ∀ (i j : ℤ) (X : Cᵒᵖ) (x : (P i).obj X) (y : (P j).obj X),
    Hom.app (g (i + j)) X ((A.mul i j).app X x y) =
      (B.mul i j).app X (Hom.app (g i) X x) (Hom.app (g j) X y))
  (hone : ∀ X : Cᵒᵖ, Hom.app (g 0) X (A.one.eval X) = B.one.eval X)

include hmul hone in
/-- **The universal property of `Stacks.GradedAlgebra.ofComparison`.** A degreewise morphism
into a sheaf of graded algebras which is multiplicative on homogeneous local sections and
carries the unit to the unit extends uniquely to a unital homomorphism out of the transported
algebra. -/
theorem existsUnique_descCmp :
    ∃! h : SheafOfModules.GradedAlgebra.UnitalHom (A.ofComparison S u) B,
      ∀ (n : ℤ) (X : Cᵒᵖ) (s : (P n).obj X),
        (h.app n).val.app X (Hom.app (u n) X s) = Hom.app (g n) X s := by
  refine ⟨{ app := A.descCmpApp S u g
            map_mul := ?_
            map_one := ?_ }, A.descCmpApp_comparison S u g, ?_⟩
  · intro i j X b₁ b₂
    refine eq_of_isSeparated (B.piece (i + j))
      (J.intersection_covering (cmpSieve_mem (u i) b₁) (cmpSieve_mem (u j) b₂)) ?_
    rintro Y f ⟨⟨x₀, hx₀⟩, ⟨y₀, hy₀⟩⟩
    have hx : Hom.app (u i) (op Y) x₀ = ((A.ofComparison S u).piece i).val.map f.op b₁ := hx₀
    have hy : Hom.app (u j) (op Y) y₀ = ((A.ofComparison S u).piece j).val.map f.op b₂ := hy₀
    rw [← naturality_apply (A.descCmpApp S u g (i + j)).val f.op,
      A.ofComparison_mul_restrict S u i j f.op b₁ b₂ x₀ y₀ hx hy,
      A.descCmpApp_comparison S u g (i + j), hmul i j (op Y) x₀ y₀,
      (B.mul i j).naturality f.op, ← naturality_apply (A.descCmpApp S u g i).val f.op,
      ← naturality_apply (A.descCmpApp S u g j).val f.op, ← hx, ← hy,
      A.descCmpApp_comparison S u g i (op Y) x₀, A.descCmpApp_comparison S u g j (op Y) y₀]
  · intro X
    exact (A.descCmpApp_comparison S u g 0 X (A.one.eval X)).trans (hone X)
  · intro h hh
    refine SheafOfModules.GradedAlgebra.UnitalHom.ext fun n => SheafOfModules.hom_ext ?_
    exact Stacks.hom_eq_of_app_eq (T := (S n).val) (B.piece n).isSheaf.isSeparated (u n)
      fun X s => (hh n X s).trans (A.descCmpApp_comparison S u g n X s).symm

end Descent

end Stacks.GradedAlgebra
