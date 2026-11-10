module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.GlobalFunctionsConstant
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.DegreeZero

/-!
# A morphism from projective space over an affine base to an affine scheme is constant

`StacksFrontier.AlgebraicGeometry.ProjectiveSpace.GlobalFunctionsConstant` computes the global
functions on `ℙⁿ_R` for a ring `R` and deduces that a morphism from `ℙⁿ_R` to an affine scheme
factors through `Spec R`.  A rigidity argument needs that statement over a base scheme which is
affine but is not presented as the spectrum of a ring, and needs it in the form of the structure
morphism of `ℙⁿ` over that base rather than of a chosen comparison with a polynomial model.
This file supplies both.

The passage from the spectrum of a ring to an arbitrary affine base is base change along the
isomorphism `Y ≅ Spec Γ(Y, 𝒪)`: projective space is stable under base change
(`AlgebraicGeometry.isPullback_projectiveSpaceOverMap`), and the base change of an isomorphism
is an isomorphism, so `ℙⁿ_Y ≅ ℙⁿ_{Spec Γ(Y, 𝒪)}` compatibly with the structure morphisms.

The factorization itself does not need the source to be projective space, nor the base to be
affine: a morphism `p : X ⟶ Y` inducing an isomorphism on global functions is one through which
every morphism from `X` to an affine scheme factors, by the `Γ`-`Spec` adjunction alone.  That
is `AlgebraicGeometry.exists_comp_eq_of_isIso_appTop`, and projective space enters only through
the hypothesis `IsIso p.appTop`.

## Main results

* `AlgebraicGeometry.exists_comp_eq_of_isIso_appTop`: a morphism which is an isomorphism on
  global functions is one every morphism to an affine scheme factors through.
* `AlgebraicGeometry.isIso_appTop_projectiveSpaceOverRing`: **`Γ(ℙⁿ_R, 𝒪) = R`**, in the form
  that factorization statement consumes.
* `AlgebraicGeometry.isIso_projectiveSpaceOverMap`: base change of projective space along an
  isomorphism of base schemes is an isomorphism.
* `AlgebraicGeometry.exists_comp_eq_structureMorphism_of_projectiveSpaceOver`: **a morphism from
  projective space over an affine base to an affine scheme is constant**, that is, it factors
  through the structure morphism.
* `AlgebraicGeometry.exists_comp_eq_of_isoProjectiveSpaceOver`: the same for a source only
  identified with projective space up to an isomorphism over the base.

## References

* [Stacks Project, Tag 01NF](https://stacks.math.columbia.edu/tag/01NF)
* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **Constancy from the global functions.** Let `p : X ⟶ Y` induce an isomorphism on global
functions.  Then every morphism from `X` to an affine scheme factors through `p`.

A morphism to an affine scheme `Y'` is the ring homomorphism it induces on global functions,
through the unit `X ⟶ Spec Γ(X, 𝒪)` of the `Γ`-`Spec` adjunction; the unit of `X` is the unit of
`Y` composed with `p`, because `p` is an isomorphism on global functions, and reading the
morphism off from the unit of `Y` instead gives the factorization.  Neither `Y` nor `X` need be
affine. -/
theorem exists_comp_eq_of_isIso_appTop {X Y Y' : Scheme.{u}} [IsAffine Y'] (p : X ⟶ Y)
    (hp : IsIso p.appTop) (μ : X ⟶ Y') :
    ∃ d : Y ⟶ Y', μ = p ≫ d := by
  refine ⟨Y.toSpecΓ ≫ Spec.map (inv p.appTop) ≫ Spec.map μ.appTop ≫ Y'.isoSpec.inv, ?_⟩
  rw [← Category.assoc, Scheme.toSpecΓ_naturality, Category.assoc,
    ← Category.assoc (Spec.map p.appTop), ← Spec.map_comp, IsIso.inv_hom_id, Spec.map_id,
    Category.id_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
    Scheme.toSpecΓ_isoSpec_inv, Category.comp_id]

open Stacks.AlgebraicGeometry in
/-- **The global functions on projective space over a ring are the coefficients**: the
structure morphism of `ℙⁿ_R` is an isomorphism on global functions. -/
alias isIso_appTop_projectiveSpaceOverRing :=
  ProjectiveSpaceHigherDirectImage.isIso_appTop_structureMorphism_projectiveSpaceOverRing

/-- **The base change of projective space along an isomorphism of base schemes is an
isomorphism**: projective space is stable under base change, and in a cartesian square opposite
an isomorphism stands an isomorphism. -/
theorem isIso_projectiveSpaceOverMap (n : ℕ) {S' S : Scheme.{u}} (g : S' ⟶ S) [IsIso g] :
    IsIso (projectiveSpaceOverMap n g) :=
  (isPullback_projectiveSpaceOverMap n g).isIso_fst_of_isIso

/-- **A morphism from projective space over an affine base to an affine scheme is constant**: it
factors through the structure morphism `ℙⁿ_Y ⟶ Y`.

The base is the spectrum of its own global functions, and projective space over it is the base
change of projective space over that spectrum along that isomorphism, so the statement is the
one over a ring transported along the induced isomorphism of projective spaces.

This is the geometric input of a rigidity argument over a base that is affine but not presented
as the spectrum of a ring: a complete fibre carries no nonconstant functions, so it cannot map
nontrivially to anything affine. -/
theorem exists_comp_eq_structureMorphism_of_projectiveSpaceOver (n : ℕ) {Y Y' : Scheme.{u}}
    [IsAffine Y] [IsAffine Y'] (μ : projectiveSpaceOver n Y ⟶ Y') :
    ∃ d : Y ⟶ Y', μ = (projectiveSpaceOver n Y ↘ Y) ≫ d := by
  have := isIso_projectiveSpaceOverMap n Y.isoSpec.hom
  obtain ⟨d, hd⟩ := exists_comp_eq_of_isIso_appTop
    (projectiveSpaceOver n (Spec Γ(Y, ⊤)) ↘ Spec Γ(Y, ⊤))
    (isIso_appTop_projectiveSpaceOverRing n Γ(Y, ⊤))
    (inv (projectiveSpaceOverMap n Y.isoSpec.hom) ≫ μ)
  have hw : projectiveSpaceOverMap n Y.isoSpec.hom ≫
      (projectiveSpaceOver n (Spec Γ(Y, ⊤)) ↘ Spec Γ(Y, ⊤)) =
      (projectiveSpaceOver n Y ↘ Y) ≫ Y.isoSpec.hom :=
    (isPullback_projectiveSpaceOverMap n Y.isoSpec.hom).w
  refine ⟨Y.isoSpec.hom ≫ d, ?_⟩
  rw [← Category.assoc, ← hw, Category.assoc, ← hd, IsIso.hom_inv_id_assoc]

/-- **A morphism to an affine scheme out of a scheme which is projective space over an affine
base is constant**, the identification with projective space being given up to an isomorphism
over the base.  This is the form a transport along a chain of comparisons consumes: the source
is some object isomorphic over `Y` to `ℙⁿ_Y`, and `q` is its structure morphism. -/
theorem exists_comp_eq_of_isoProjectiveSpaceOver (n : ℕ) {X Y Y' : Scheme.{u}}
    [IsAffine Y] [IsAffine Y'] (q : X ⟶ Y) (α : X ≅ projectiveSpaceOver n Y)
    (hα : α.hom ≫ (projectiveSpaceOver n Y ↘ Y) = q) (μ : X ⟶ Y') :
    ∃ d : Y ⟶ Y', μ = q ≫ d := by
  obtain ⟨d, hd⟩ := exists_comp_eq_structureMorphism_of_projectiveSpaceOver n (α.inv ≫ μ)
  exact ⟨d, by rw [← hα, Category.assoc, ← hd, Iso.hom_inv_id_assoc]⟩

end AlgebraicGeometry

end
