module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.AssociatedSite
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStack
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyInjectiveBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyInjectiveDiagonal

/-!
# Universal injectivity is tested on the affine schemes over the target (Stacks 0DTN)

A 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` is universally injective (**Stacks 0CI2**)
exactly when for every affine scheme `U` of the big fppf site over `S` and every 1-morphism
`U ⟶ 𝒴` the base change `U ×_𝒴 𝒳 ⟶ U` is universally injective. This is **Stacks 0DTN**.

## Main results

* `AlgebraicGeometry.Stack.injective_pointsMap_of_universallyInjective`: a universally injective
  1-morphism is itself injective on points — the base change along the identity, obtained without
  having to exhibit it as a 2-fibre product.
* `AlgebraicGeometry.Stack.universallyInjective_iff_affineBaseChange`: **Stacks 0DTN**.

## Implementation notes

The forward implication is `AlgebraicGeometry.Stack.universallyInjective_baseChange`
(**Stacks 0CI3**): universal injectivity quantifies over every 2-fibre product of every cospan,
so a base change to an affine scheme is one of the cases it already covers.

For the converse the source tests `f` on a *smooth* affine chart `V ⟶ 𝒴` and argues that the
relative diagonals `Δ_g` of the base changes are jointly surjective, hence that `Δ_f` is
surjective, hence (**Stacks 0CPN**) that `f` is universally injective. Here the points of an
algebraic stack are, by **Stacks 04XG**
(`AlgebraicGeometry.Stack.FieldValuedPoint`), represented by objects lying over the spectrum of a
field, and the spectrum of a field is affine; so the affine scheme the criterion is applied to can
be taken to be the base of the field-valued point itself, and no smoothness and no joint
surjectivity is needed:

* the two points of the base change `P.pt` to be separated have the same image `w` in `|𝒲|`; a
  representative field-valued point of `w` has affine base `U` and names, by the 2-Yoneda lemma
  (**Stacks 004B**, `AlgebraicGeometry.Stack.objectMorphism`), a 1-morphism `u : U ⟶ 𝒲` whose
  image on points hits `w`;
* **Stacks 04XH** (`AlgebraicGeometry.Stack.AlgebraicStacks.exists_point_of_isTwoFibreProduct`)
  therefore lifts each of the two points to the base change `U ×_𝒲 P.pt`, both over the same
  point of `U`;
* that base change is, after pasting (`CategoryTheory.Bicategory.TwoCommSq.pasteFst`, which keeps
  the apex and the first projection), a base change of `f` to the affine scheme `U`, so the
  hypothesis applies to it and its first projection is injective on points; the two lifts agree,
  hence so do their images, which are the two points.

The step from universal injectivity of a 1-morphism to injectivity of its own map on points is
`injective_pointsMap_of_universallyInjective`. It goes through the relative diagonal rather than
through a 2-fibre product along an identity: a universally injective 1-morphism has surjective
relative diagonal (**Stacks 0CPN**) and a 1-morphism with surjective relative diagonal is
injective on points, both already available, which avoids having to certify the square with an
identity leg as a 2-fibre product.

The affine scheme is quantified as an object `U` of the big fppf site over `S` whose underlying
scheme is affine, and the test 1-morphism as a 1-morphism out of the algebraic stack
`AlgebraicGeometry.Stack.schemeStack` it represents (**Stacks 03YS**, part (3)); the base change
is any 2-fibre product of the cospan, so the statement is independent of the model chosen for it.

## References

* [Stacks Project, Tag 004B](https://stacks.math.columbia.edu/tag/004B)
* [Stacks Project, Tag 04XG](https://stacks.math.columbia.edu/tag/04XG)
* [Stacks Project, Tag 04XH](https://stacks.math.columbia.edu/tag/04XH)
* [Stacks Project, Tag 0CI2](https://stacks.math.columbia.edu/tag/0CI2)
* [Stacks Project, Tag 0CI3](https://stacks.math.columbia.edu/tag/0CI3)
* [Stacks Project, Tag 0CPN](https://stacks.math.columbia.edu/tag/0CPN)
* [Stacks Project, Tag 0DTN](https://stacks.math.columbia.edu/tag/0DTN)
-/

@[expose] public section

open CategoryTheory

attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}

/-- **A universally injective 1-morphism of algebraic stacks is injective on points.** Its
relative diagonal is surjective by **Stacks 0CPN**, and a 1-morphism with surjective relative
diagonal is injective on points. -/
theorem injective_pointsMap_of_universallyInjective (f : 𝒳 ⟶ 𝒴)
    (hf : UniversallyInjective B S hS f) :
    Function.Injective (AlgebraicStacks.pointsMap B S hS f) :=
  injective_pointsMap_of_isSurjective_relativeDiagonal B S hS f
    (isSurjective_relativeDiagonal_of_universallyInjective B S hS f hf)

/-- The base of a field-valued point of a category fibred in groupoids over the big fppf site of
`S` is affine: it is an object of the site whose underlying scheme is isomorphic to the spectrum
of a field. -/
theorem isAffine_base_of_fieldValuedPoint
    {𝒲 : BasedCategory.{u, u + 1} (BigFppfOver B S hS)}
    (p : FieldValuedPoint B S hS 𝒲) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj p.base) :=
  IsAffine.of_isIso p.isSpec.hom

/-- **Stacks 0DTN.** A 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` is universally
injective if and only if for every affine scheme `U` of the big fppf site over `S` and every
1-morphism from the algebraic stack it represents to `𝒴`, the base change of `f` is universally
injective.

The base change is an arbitrary 2-fibre product of the cospan, as in **Stacks 0CI2** itself, so
neither side depends on a chosen model. -/
@[stacks 0DTN]
theorem universallyInjective_iff_affineBaseChange (f : 𝒳 ⟶ 𝒴) :
    UniversallyInjective B S hS f ↔
      ∀ (U : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj U) →
        ∀ (g : schemeStack.{u, w} B S hS U ⟶ 𝒴) (P : Bicategory.TwoCommSq g f),
          Bicategory.IsTwoFibreProduct P → UniversallyInjective B S hS P.fst := by
  refine ⟨fun hf U _ g P hP => universallyInjective_baseChange B S hS f g hf P hP,
    fun hlocal 𝒲 g P hP t₁ t₂ ht => ?_⟩
  -- a representative field-valued point of the common image of `t₁` and `t₂` in `|𝒲|`
  obtain ⟨pw, hpw⟩ := Quotient.exists_rep (AlgebraicStacks.pointsMap B S hS P.fst t₁)
  -- its base is an affine object of the site, and it names a 1-morphism `u` to `𝒲`
  let U : BigFppfOver B S hS := pw.base
  let y₁ : 𝒲.val.val.p.Fiber U := ⟨pw.obj, pw.over⟩
  let u : schemeStack.{u, w} B S hS U ⟶ 𝒲 :=
    Bicategory.InducedBicategory.mkHom (objectMorphism B S hS 𝒲.val y₁)
  -- the tautological field-valued point of the affine scheme `U`
  let z₀ : FieldValuedPoint B S hS (schemeStack.{u, w} B S hS U).val.val :=
    { carrier := pw.carrier
      field := pw.field
      base := U
      isSpec := pw.isSpec
      obj := Over.mk (𝟙 U)
      over := rfl }
  have hz₀ : AlgebraicStacks.pointsMap B S hS u (Quotient.mk _ z₀) =
      AlgebraicStacks.pointsMap B S hS P.fst t₁ := by
    rw [← hpw]
    exact Quotient.sound ⟨_, ⟨𝟙 _⟩,
      ⟨(Functor.TwoYoneda.chosenLift 𝒲.val.val.p 𝒲.val.isFiberedInGroupoids U y₁
        (Over.mk (𝟙 U))).φ⟩⟩
  -- the base change of `P.pt ⟶ 𝒲` along `u`, which is also a base change of `f` to `U`
  let Q := AlgebraicStacks.twoFibreProductSquare B S hS u P.fst
  have hQ := AlgebraicStacks.isTwoFibreProduct_twoFibreProductSquare B S hS u P.fst
  obtain ⟨s₁, hs₁a, hs₁b⟩ := AlgebraicStacks.exists_point_of_isTwoFibreProduct B S hS Q hQ
    (Quotient.mk _ z₀) t₁ hz₀
  obtain ⟨s₂, hs₂a, hs₂b⟩ := AlgebraicStacks.exists_point_of_isTwoFibreProduct B S hS Q hQ
    (Quotient.mk _ z₀) t₂ (hz₀.trans ht)
  have hs : s₁ = s₂ := injective_pointsMap_of_universallyInjective B S hS Q.fst
    (hlocal U (isAffine_base_of_fieldValuedPoint B S hS pw) (u ≫ g) (P.pasteFst Q)
      (Bicategory.isTwoFibreProduct_pasteFst P hP Q hQ)) (hs₁a.trans hs₂a.symm)
  rw [← hs₁b, ← hs₂b, hs]

end AlgebraicGeometry.Stack

end
