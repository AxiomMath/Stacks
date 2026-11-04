module

public import StacksFrontier.AlgebraicGeometry.Stacks.ObjectPropertyOpenLocus
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableMorphismAlgebraicStackHomUniverse

/-!
# An open locus of an algebraic stack cut out by a property of its objects is algebraic

Let `𝒟` be a category fibred in groupoids over the big fppf site of a scheme `S`, and let `P` be
a property of the objects of `𝒟` which is inherited along morphisms. If `P` has an open locus
(`AlgebraicGeometry.Stack.HasOpenObjectPropertyLocus`: over every scheme-valued point of `𝒟` the
objects with the property are cut out by an open subscheme of the base), then the full
subcategory of `𝒟` on the objects with the property is fibred in groupoids, its inclusion is
representable by algebraic spaces, and so it is an algebraic stack whenever `𝒟` is (Stacks 05UM).

This is the step "it suffices to show that the inclusion is representable by open immersions" of
the proof of Stacks 0D41, and of every other argument which exhibits a stack as an open substack
of a known algebraic stack. The hom types of `𝒟` may live in any universe, because the stacks this
is applied to (the stack of coherent sheaves of Stacks 08KB and the Picard stack of Stacks 0372)
have hom types one universe above the schemes.

## Main results

* `CategoryTheory.Functor.IsFiberedInGroupoids.restrict_of_prop_of_hom`: the restriction of a
  functor fibred in groupoids to a full subcategory on a property inherited along morphisms is
  fibred in groupoids.
* `AlgebraicGeometry.Stack.isAlgebraicStack_objectPropertySubcategory`: the full subcategory of
  an algebraic stack on a property with an open locus is an algebraic stack.

## References

* [Stacks Project, Tag 05UM](https://stacks.math.columbia.edu/tag/05UM)
* [Stacks Project, Tag 04YL](https://stacks.math.columbia.edu/tag/04YL)
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace CategoryTheory.Functor

/-- The restriction of a functor fibred in groupoids to the full subcategory on a property of the
objects inherited along morphisms is fibred in groupoids: a lift of a morphism of the base to an
object with the property has the property, and the unique fill-ins of the ambient category are
morphisms of the full subcategory. -/
theorem IsFiberedInGroupoids.restrict_of_prop_of_hom {𝒳 𝒞 : Type*} [Category* 𝒳]
    [Category* 𝒞] {p : 𝒳 ⥤ 𝒞} (hp : p.IsFiberedInGroupoids) (P : ObjectProperty 𝒳)
    (hP : ∀ {a b : 𝒳}, (a ⟶ b) → P b → P a) : (P.ι ⋙ p).IsFiberedInGroupoids where
  exists_lift f x hx := by
    obtain ⟨y, φ, hφ⟩ := hp.exists_lift f x.obj hx
    refine ⟨⟨y, hP φ x.property⟩, ObjectProperty.homMk φ, ?_⟩
    cases hφ
    exact IsHomLift.map _
  unique_lift φ ψ f h := by
    obtain ⟨χ, hχ, huniq⟩ := hp.unique_lift φ.hom ψ.hom f h
    refine ⟨ObjectProperty.homMk χ, ⟨hχ.1, ?_⟩, fun χ' hχ' => ?_⟩
    · ext
      exact hχ.2
    · ext
      exact huniq χ'.hom ⟨hχ'.1, congrArg (·.hom) hχ'.2⟩

end CategoryTheory.Functor

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒟 : CatFiberedInGroupoids.{u, v, u + 1, u + 1} (BigFppfOver B S hS))
  (P : ObjectProperty 𝒟.val.obj)

/-- The full subcategory of a category fibred in groupoids on a property inherited along
morphisms is fibred in groupoids. -/
theorem objectPropertySubcategory_isFiberedInGroupoids
    (hP : ∀ {a b : 𝒟.val.obj}, (a ⟶ b) → P b → P a) :
    (objectPropertySubcategory B S hS 𝒟.val P).p.IsFiberedInGroupoids :=
  𝒟.isFiberedInGroupoids.restrict_of_prop_of_hom P hP

/-- **An open locus of an algebraic stack is an algebraic stack.** Let `P` be a property of the
objects of a category fibred in groupoids `𝒟` over the big fppf site of `S`, inherited along
morphisms and with an open locus. If `𝒟` is an algebraic stack, so is the full subcategory on
the objects with the property: its inclusion is representable by algebraic spaces
(`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_objectPropertyInclusion`), so
Stacks 05UM applies. -/
theorem isAlgebraicStack_objectPropertySubcategory
    (hP : ∀ {a b : 𝒟.val.obj}, (a ⟶ b) → P b → P a)
    (hopen : HasOpenObjectPropertyLocus B S hS 𝒟.val P)
    (h𝒟 : IsAlgebraicStack.{u, w} B S hS 𝒟.val) :
    IsAlgebraicStack.{u, w} B S hS (objectPropertySubcategory B S hS 𝒟.val P) :=
  isAlgebraicStack_source_of_isRepresentableByAlgebraicSpaces_homUniverse B S hS
    (𝒳 := CatFiberedInGroupoids.mk (objectPropertySubcategory B S hS 𝒟.val P)
      (objectPropertySubcategory_isFiberedInGroupoids B S hS 𝒟 P hP))
    (Bicategory.InducedBicategory.mkHom (objectPropertyInclusion B S hS 𝒟.val P))
    (isRepresentableByAlgebraicSpaces_objectPropertyInclusion B S hS 𝒟.val P
      ⟨fun e hX => hP e.inv hX⟩ hopen)
    h𝒟

end AlgebraicGeometry.Stack

end
