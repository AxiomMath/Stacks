module

public import Mathlib.Algebra.Category.AlgCat.Basic
public import Mathlib.Algebra.Homology.AlternatingConst
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import StacksFrontier.Cotangent.Resolution
public import StacksFrontier.Cotangent.StandardResolutionIsResolution

/-!
# Exactness of the Moore complex of the standard resolution

The standard augmented simplicial resolution `P• ⟶ B` of **Stacks 08PM** is a resolution in the
sense of **Stacks 08QI** (`CommAlgCat.standardResolution_isResolution`). By the three-way
criterion `CommAlgCat.isResolution_quasiIso_homotopyEquivalence_tfae` this means that the Moore
complex of the underlying simplicial abelian group of `P•` is quasi-isomorphic to the Moore
complex of the constant simplicial abelian group on `B`, and the latter is the alternating
constant complex, which is exact in every positive degree. So the Moore complex of `P•` is
exact in every positive degree too.

## Main definitions

* `CommAlgCat.forgetToAddCommGrp`: the underlying-abelian-group functor on commutative
  `A`-algebras, factored through `AlgCat A` and `ModuleCat A` exactly as the statement of
  `CommAlgCat.isResolution_quasiIso_homotopyEquivalence_tfae` factors it.
* `CommAlgCat.standardResolutionMooreComplex`: the alternating-face-map complex of the
  underlying simplicial abelian group of the standard resolution.

## Main results

* `CommAlgCat.standardResolutionMooreComplex_exactAt`: that complex is exact in every positive
  degree.
* `CommAlgCat.standardResolution_exists_of_delta_sub_delta_eq_zero`: the degree-one case read on
  elements — a `p ∈ P₁` with `δ₀ p = δ₁ p` is `δ₀ q - δ₁ q + δ₂ q` for some `q ∈ P₂`.

## Implementation notes

The constant half of the quasi-isomorphism is identified with `ChainComplex.alternatingConst`
in two steps: `CategoryTheory.Functor.constComp` moves the forgetful functor past the constant
simplicial object, and `AlgebraicTopology.alternatingFaceMapComplexConst` identifies the
alternating-face-map complex of a constant simplicial object with the alternating constant
complex. `ChainComplex.alternatingConst_exactAt` then supplies the exactness, and
`HomologicalComplex.exactAt_iff_of_quasiIsoAt` transports it across the quasi-isomorphism.

The passage to elements is `CategoryTheory.ShortComplex.ab_exact_iff`, which is available
because the quasi-isomorphism of
`CommAlgCat.isResolution_quasiIso_homotopyEquivalence_tfae` lives in `AddCommGrpCat`. The
forgetful chain `CommAlgCat A ⥤ AlgCat A ⥤ ModuleCat A ⥤ AddCommGrpCat` is the identity on
underlying types, on the underlying maps and on the additive structure, so the final transport
back to elements of the bundled algebras is definitional; it is performed with `exact` rather
than with rewriting.

No `@[stacks]` attribute is attached: this is a substrate lemma extracted from the resolution
criterion, and the tags it rests on are carried by
`CommAlgCat.standardResolution_isResolution` and
`CommAlgCat.isResolution_quasiIso_homotopyEquivalence_tfae`.

## References

* [Stacks Project, Tag 08QI](https://stacks.math.columbia.edu/tag/08QI)
* [Stacks Project, Tag 08PM](https://stacks.math.columbia.edu/tag/08PM)
-/

@[expose] public section

open CategoryTheory Opposite Simplicial AlgebraicTopology

universe u v

namespace CommAlgCat

variable (A : Type u) [CommRing A] (B : CommAlgCat.{max u v} A)

/-! ### The underlying simplicial abelian group and its Moore complex -/

/-- The underlying-abelian-group functor on commutative `A`-algebras, factored as
`CommAlgCat A ⥤ AlgCat A ⥤ ModuleCat A ⥤ AddCommGrpCat`. This is the factorisation used in the
statement of `CommAlgCat.isResolution_quasiIso_homotopyEquivalence_tfae`. -/
abbrev forgetToAddCommGrp : CommAlgCat.{max u v} A ⥤ AddCommGrpCat.{max u v} :=
  forget₂ (CommAlgCat.{max u v} A) (AlgCat.{max u v} A) ⋙
    forget₂ (AlgCat.{max u v} A) (ModuleCat.{max u v} A) ⋙
      forget₂ (ModuleCat.{max u v} A) AddCommGrpCat.{max u v}

/-- The underlying simplicial abelian group of the standard resolution of `B` over `A`. -/
noncomputable abbrev standardResolutionSimplicialAddCommGrp :
    SimplicialObject AddCommGrpCat.{max u v} :=
  (standardResolution A B).left ⋙ forgetToAddCommGrp.{u, v} A

/-- The Moore (alternating face map) complex of the underlying simplicial abelian group of the
standard resolution of `B` over `A`. -/
noncomputable abbrev standardResolutionMooreComplex : ChainComplex AddCommGrpCat.{max u v} ℕ :=
  (alternatingFaceMapComplex AddCommGrpCat.{max u v}).obj
    (standardResolutionSimplicialAddCommGrp.{u, v} A B)

/-- The first differential of the Moore complex is the alternating sum of the two faces. -/
theorem standardResolutionMooreComplex_d_one_zero :
    (standardResolutionMooreComplex.{u, v} A B).d 1 0 =
      (standardResolutionSimplicialAddCommGrp.{u, v} A B).δ 0 -
        (standardResolutionSimplicialAddCommGrp.{u, v} A B).δ 1 := by
  rw [alternatingFaceMapComplex_obj_d, AlternatingFaceMapComplex.objD, Fin.sum_univ_two,
    sub_eq_add_neg]
  simp

/-- The second differential of the Moore complex is the alternating sum of the three faces. -/
theorem standardResolutionMooreComplex_d_two_one :
    (standardResolutionMooreComplex.{u, v} A B).d 2 1 =
      (standardResolutionSimplicialAddCommGrp.{u, v} A B).δ 0 -
          (standardResolutionSimplicialAddCommGrp.{u, v} A B).δ 1 +
        (standardResolutionSimplicialAddCommGrp.{u, v} A B).δ 2 := by
  rw [alternatingFaceMapComplex_obj_d, AlternatingFaceMapComplex.objD, Fin.sum_univ_three,
    sub_eq_add_neg]
  simp

/-! ### Exactness in positive degrees -/

/-- The Moore complex of the underlying simplicial abelian group of the standard resolution is
exact in every positive degree: the augmentation is a quasi-isomorphism onto the constant
simplicial abelian group on `B`, whose Moore complex is the alternating constant complex. -/
theorem standardResolutionMooreComplex_exactAt (n : ℕ) (hn : n ≠ 0) :
    (standardResolutionMooreComplex.{u, v} A B).ExactAt n := by
  have hsurj : ∀ m : SimplexCategoryᵒᵖ,
      Function.Surjective ((standardResolution A B).hom.app m).hom := by
    intro m
    have hm : m = op ⦋m.unop.len⦌ := by rw [SimplexCategory.mk_len]
    rw [hm]
    exact surjective_standardResolution_augmentation A B m.unop.len
  set f := (alternatingFaceMapComplex AddCommGrpCat.{max u v}).map
    (Functor.whiskerRight (standardResolution A B).hom (forgetToAddCommGrp.{u, v} A))
  have hquasi : QuasiIso f :=
    ((isResolution_quasiIso_homotopyEquivalence_tfae A B (standardResolution A B).left
      (standardResolution A B).hom (standardResolution_obj_isPolynomialAlgebra A B)
      hsurj).out 1 2).mp (standardResolution_isResolution.{u, v} A B)
  have := hquasi.quasiIsoAt n
  refine (exactAt_iff_of_quasiIsoAt f n).mpr ?_
  refine HomologicalComplex.ExactAt.of_iso
    (ChainComplex.alternatingConst_exactAt
      ((forgetToAddCommGrp.{u, v} A).obj (CommAlgCat.of A B)) n hn) ?_
  exact ((alternatingFaceMapComplex AddCommGrpCat.{max u v}).mapIso
      (Functor.constComp SimplexCategoryᵒᵖ (CommAlgCat.of A B)
        (forgetToAddCommGrp.{u, v} A)) ≪≫
    alternatingFaceMapComplexConst.app _).symm

/-- Exactness of the Moore complex in degree one, read on elements: every `1`-cycle is a
boundary. -/
theorem standardResolutionMooreComplex_exists_of_d_eq_zero
    (x : (standardResolutionMooreComplex.{u, v} A B).X 1)
    (hx : (standardResolutionMooreComplex.{u, v} A B).d 1 0 x = 0) :
    ∃ y : (standardResolutionMooreComplex.{u, v} A B).X 2,
      (standardResolutionMooreComplex.{u, v} A B).d 2 1 y = x := by
  have hex := standardResolutionMooreComplex_exactAt.{u, v} A B 1 one_ne_zero
  rw [HomologicalComplex.exactAt_iff' _ 2 1 0 (by simp) (by simp)] at hex
  exact (ShortComplex.ab_exact_iff _).1 hex x hx

/-! ### The element form -/

/-- **The standard resolution is a resolution, so its Moore complex is exact in positive
degrees; in degree one this says that every `1`-cycle is a boundary.** Concretely: if an element
`x` of `P₁` has `δ₀ x = δ₁ x`, then it is the alternating sum of the three faces of some element
of `P₂`. -/
theorem standardResolution_exists_of_delta_sub_delta_eq_zero
    (x : (standardResolution A B).left.obj (op ⦋1⦌))
    (hx : (standardResolution A B).left.δ (0 : Fin 2) x
            - (standardResolution A B).left.δ (1 : Fin 2) x = 0) :
    ∃ y : (standardResolution A B).left.obj (op ⦋2⦌),
      (standardResolution A B).left.δ (0 : Fin 3) y
        - (standardResolution A B).left.δ (1 : Fin 3) y
        + (standardResolution A B).left.δ (2 : Fin 3) y = x := by
  have hx' : (standardResolutionMooreComplex.{u, v} A B).d 1 0 x = 0 := by
    rw [standardResolutionMooreComplex_d_one_zero]
    exact hx
  obtain ⟨y, hy⟩ := standardResolutionMooreComplex_exists_of_d_eq_zero.{u, v} A B x hx'
  rw [standardResolutionMooreComplex_d_two_one] at hy
  exact ⟨y, hy⟩

end CommAlgCat

end
