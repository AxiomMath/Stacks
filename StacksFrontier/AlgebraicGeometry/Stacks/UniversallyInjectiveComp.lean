module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductUniversalProperty
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyInjective
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Pasting

/-!
# Composition of universally injective morphisms of algebraic stacks (Stacks 0CI4)

The composite of a pair of universally injective 1-morphisms of algebraic stacks over `S` is
universally injective. This is **Stacks 0CI4**.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.bijective_pointsMap_preHom`: the map on points induced
  by a comparison 1-morphism between two 2-fibre products of one cospan is bijective.
* `AlgebraicGeometry.Stack.injective_pointsMap_fst_of_isTwoFibreProduct`: injectivity of the map
  on points of the first projection of a 2-fibre product does not depend on the chosen model.
* `AlgebraicGeometry.Stack.universallyInjective_comp`: **Stacks 0CI4**.

## Implementation notes

`AlgebraicGeometry.Stack.UniversallyInjective` quantifies over every model of the base change, so
proving it for `f ≫ g` means producing injectivity at an arbitrary 2-fibre product `P` of
`(k, f ≫ g)`. The hypotheses, however, are naturally applied to *chosen* models: the canonical
`Q := 𝒲 ×_𝒵 𝒴` of Stacks 04T2 and then the canonical `R := Q.pt ×_𝒴 𝒳`. Pasting those two
(`CategoryTheory.Bicategory.isTwoFibreProduct_pasteSnd`) gives one model of `𝒲 ×_𝒵 𝒳` whose
first projection is `R.fst ≫ Q.fst`, so its map on points is a composite of two injective maps.
Transporting to `P` is the only remaining step, and that is
`injective_pointsMap_fst_of_isTwoFibreProduct`.

The transport rests on `bijective_pointsMap_preHom`: terminality makes a comparison pre-morphism
`c : P ⟶ Q` and a comparison `d : Q ⟶ P` mutually inverse *up to a 2-morphism*, and the map on
points does not see 2-morphisms
(`AlgebraicGeometry.Stack.AlgebraicStacks.pointsMap_eq_of_hom₂`), so the two induced maps on
points are mutually inverse on the nose. Note that this is weaker than, and does not need, the
fact that the comparison is an equivalence of the underlying categories
(`CategoryTheory.Bicategory.isEquivalence_of_isTwoFibreProduct`).

## References

* [Stacks Project, Tag 04T2](https://stacks.math.columbia.edu/tag/04T2)
* [Stacks Project, Tag 0CI4](https://stacks.math.columbia.edu/tag/0CI4)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace AlgebraicStacks

/-- **The comparison of two 2-fibre products is a bijection on points.** For two 2-fibre products
`P`, `Q` of one cospan of algebraic stacks over `S` and any pre-morphism `c : P ⟶ Q` of
2-commutative squares, the induced map on points is bijective.

Terminality of `Q` and of `P` gives a pre-morphism `d : Q ⟶ P` whose two composites with `c` are
equivalent to the identities by invertible 2-morphisms, and the map on points is unchanged by a
2-morphism. -/
theorem bijective_pointsMap_preHom {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS}
    {f : 𝒳 ⟶ 𝒵} {g : 𝒴 ⟶ 𝒵} {P Q : Bicategory.TwoCommSq f g}
    (hP : Bicategory.IsTwoFibreProduct P) (hQ : Bicategory.IsTwoFibreProduct Q)
    (c : Bicategory.TwoCommSq.PreHom P Q) :
    Function.Bijective (pointsMap B S hS c.hom) := by
  classical
  obtain ⟨d, -⟩ := Quotient.exists_rep (hP.from Q)
  obtain ⟨θ, -, -⟩ := Quotient.exact
    (hP.hom_ext (Quotient.mk _ (c.comp d)) (Quotient.mk _ (Bicategory.TwoCommSq.PreHom.id P)))
  obtain ⟨ε, -, -⟩ := Quotient.exact
    (hQ.hom_ext (Quotient.mk _ (d.comp c)) (Quotient.mk _ (Bicategory.TwoCommSq.PreHom.id Q)))
  have key : ∀ {𝒜 ℬ : Stack.AlgebraicStacks.{u, w} B S hS} (a : 𝒜 ⟶ ℬ) (b : ℬ ⟶ 𝒜)
      (θ : a ≫ b ⟶ 𝟙 𝒜), pointsMap B S hS b ∘ pointsMap B S hS a = id := fun a b θ => by
    rw [← pointsMap_comp, pointsMap_eq_of_hom₂ B S hS θ, pointsMap_id]
  exact ⟨Function.LeftInverse.injective (congrFun (key _ _ θ.hom)),
    Function.RightInverse.surjective (congrFun (key _ _ ε.hom))⟩

end AlgebraicStacks

/-- **Injectivity on points of a base change does not depend on the chosen model.** If the first
projection of one 2-fibre product of a cospan of algebraic stacks is injective on points, then so
is the first projection of any other. -/
theorem injective_pointsMap_fst_of_isTwoFibreProduct
    {𝒳 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS} {f : 𝒳 ⟶ 𝒵} {g : 𝒴 ⟶ 𝒵}
    {P Q : Bicategory.TwoCommSq f g} (hP : Bicategory.IsTwoFibreProduct P)
    (hQ : Bicategory.IsTwoFibreProduct Q)
    (h : Function.Injective (AlgebraicStacks.pointsMap B S hS Q.fst)) :
    Function.Injective (AlgebraicStacks.pointsMap B S hS P.fst) := by
  classical
  obtain ⟨c, -⟩ := Quotient.exists_rep (hQ.from P)
  have hproj : AlgebraicStacks.pointsMap B S hS P.fst =
      AlgebraicStacks.pointsMap B S hS Q.fst ∘ AlgebraicStacks.pointsMap B S hS c.hom :=
    (AlgebraicStacks.pointsMap_eq_of_hom₂ B S hS c.isoFst.hom).trans
      (AlgebraicStacks.pointsMap_comp B S hS c.hom Q.fst)
  rw [hproj]
  exact h.comp (AlgebraicStacks.bijective_pointsMap_preHom B S hS hP hQ c).1

/-- **Stacks 0CI4.** The composite of a pair of universally injective 1-morphisms of algebraic
stacks over `S` is universally injective. -/
@[stacks 0CI4]
theorem universallyInjective_comp {𝒳 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵) (hf : UniversallyInjective B S hS f)
    (hg : UniversallyInjective B S hS g) :
    UniversallyInjective B S hS (f ≫ g) := by
  intro 𝒲 k P hP
  set Q := AlgebraicStacks.twoFibreProductSquare B S hS k g with hQdef
  have hQ := AlgebraicStacks.isTwoFibreProduct_twoFibreProductSquare B S hS k g
  set R := AlgebraicStacks.twoFibreProductSquare B S hS Q.snd f with hRdef
  have hR := AlgebraicStacks.isTwoFibreProduct_twoFibreProductSquare B S hS Q.snd f
  have hTfst : Function.Injective
      (AlgebraicStacks.pointsMap B S hS (Q.pasteSnd R).fst) := by
    change Function.Injective (AlgebraicStacks.pointsMap B S hS (R.fst ≫ Q.fst))
    rw [AlgebraicStacks.pointsMap_comp]
    exact (hg 𝒲 k Q hQ).comp (hf Q.pt Q.snd R hR)
  exact injective_pointsMap_fst_of_isTwoFibreProduct B S hS hP
    (Bicategory.isTwoFibreProduct_pasteSnd Q hQ R hR) hTfst

end AlgebraicGeometry.Stack

end
