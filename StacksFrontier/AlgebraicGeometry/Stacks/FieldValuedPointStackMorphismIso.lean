module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableDecent

/-!
# A 1-morphism out of the spectrum of a field is the 1-morphism of a field-valued point

Let `𝒳` be a category fibred in groupoids over the big fppf site of `S`, let `V` be an object of
the site whose underlying scheme is the spectrum of a field, and let `H : V ⟶ 𝒳` be a 1-morphism
out of the category fibred in groupoids `V` represents. Then `H` is 2-isomorphic to the
1-morphism of **Stacks 0DRL** attached to the field-valued point of `𝒳` that `H` sends the
tautological point of `V` to.

This is the converse dictionary to `AlgebraicGeometry.Stack.fieldValuedPointStackMorphism`: a
field-valued point of `𝒳` determines a 1-morphism out of a field spectrum, and every such
1-morphism arises that way, up to a 2-isomorphism.

## Main definitions

* `AlgebraicGeometry.Stack.tautologicalFieldValuedPoint`: the field-valued point of the category
  fibred in groupoids a field spectrum of the site represents which the identity arrow names.

## Main results

* `AlgebraicGeometry.Stack.twoIso_fieldValuedPointMorphism_fieldValuedPointMap`: the
  2-isomorphism, at the level of categories fibred in groupoids.
* `AlgebraicGeometry.Stack.twoIso_fieldValuedPointStackMorphism_fieldValuedPointMap`: the same,
  read in the 2-category of algebraic stacks.

## How it is proved

Exactly as `AlgebraicGeometry.Stack.fieldValuedPointMorphism_comp_iso` is: the 2-Yoneda
evaluation at `V` (**Stacks 004B**) is an equivalence onto the fibre of `𝒳` over `V`, that fibre
is a groupoid, and the two 1-morphisms being compared have the *same* image under it up to the
chosen lift `H` makes at the identity arrow — which is an isomorphism because the fibre is a
groupoid. A fully faithful functor reflects isomorphisms, which produces the 2-isomorphism
upstairs.

## Implementation notes

The field is carried as data (`carrier` and the isomorphism of the underlying scheme with its
spectrum) rather than existentially, because `AlgebraicGeometry.Stack.FieldValuedPoint` carries
it as data. For the object `AlgebraicGeometry.Stack.fieldPointObject` of **Stacks 06PU** the
isomorphism is the identity.

No `@[stacks]` attribute is attached: this is the 2-Yoneda lemma **Stacks 004B** read at a
field-valued point, and that tag's covering set is elsewhere.

## References

* [Stacks Project, Tag 004B](https://stacks.math.columbia.edu/tag/004B)
* [Stacks Project, Tag 04XF](https://stacks.math.columbia.edu/tag/04XF)
* [Stacks Project, Tag 0DRL](https://stacks.math.columbia.edu/tag/0DRL)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The tautological field-valued point of a field spectrum of the site.** For an object `V`
of the big fppf site of `S` whose underlying scheme is the spectrum of a field `k`, the identity
arrow of `V` is an object of the slice over `V`, hence a field-valued point of the category
fibred in groupoids that `V` represents. -/
def tautologicalFieldValuedPoint (V : BigFppfOver B S hS) (k : Type u) [Field k]
    (hiso : (BigFppfOver.toScheme B S hS).obj V ≅ Spec (.of k)) :
    FieldValuedPoint B S hS (schemeFibredCategory B S hS V).val where
  carrier := k
  base := V
  isSpec := hiso
  obj := Over.mk (𝟙 V)
  «over» := rfl

/-- **A 1-morphism out of a field spectrum of the site is the 1-morphism of a field-valued
point.** `H` and the 1-morphism of the field-valued point it sends the tautological point of `V`
to are 2-isomorphic.

The 2-Yoneda evaluation at `V` is an equivalence onto the fibre of `𝒳` over `V`, which is a
groupoid, and the chosen lift of the identity arrow at the image point is a morphism of that
fibre from the evaluation of the point's 1-morphism to the evaluation of `H`; a fully faithful
functor reflects it. -/
@[sga "3 XI 1.7" "partial"]
def twoIso_fieldValuedPointMorphism_fieldValuedPointMap
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (V : BigFppfOver B S hS) (k : Type u) [Field k]
    (hiso : (BigFppfOver.toScheme B S hS).obj V ≅ Spec (.of k))
    (H : schemeFibredCategory B S hS V ⟶ 𝒳) :
    (fieldValuedPointMorphism B S hS 𝒳
        (fieldValuedPointMap B S hS (schemeFibredCategory B S hS V).val H.hom
          (tautologicalFieldValuedPoint B S hS V k hiso))).hom ≅ H.hom := by
  let p₀ := 𝒳.val.p
  let q := fieldValuedPointMap B S hS (schemeFibredCategory B S hS V).val H.hom
    (tautologicalFieldValuedPoint B S hS V k hiso)
  let qObj : p₀.Fiber V := Functor.Fiber.mk (a := q.obj) q.over
  let ev := Functor.twoYonedaEvaluation p₀ V
  have : ev.IsEquivalence :=
    Functor.twoYonedaEvaluation_isEquivalence p₀ 𝒳.isFiberedInGroupoids V
  have : IsGroupoid (p₀.Fiber V) := 𝒳.isFiberedInGroupoids.fiber_isGroupoid V
  let l := Functor.TwoYoneda.chosenLift p₀ 𝒳.isFiberedInGroupoids V qObj (Over.mk (𝟙 V))
  have : p₀.IsHomLift (𝟙 V) l.φ := by
    simpa using l.isStronglyCartesian.toIsHomLift
  let hFF : ev.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful ev
  let α : ev.obj (fieldValuedPointMorphism B S hS 𝒳 q).hom ⟶ ev.obj H.hom :=
    Functor.Fiber.homMk p₀ V l.φ
  exact hFF.preimageIso (asIso α)

/-- **A 1-morphism out of a field spectrum of the site is the 1-morphism of a field-valued
point, in the 2-category of algebraic stacks.** The reading of
`AlgebraicGeometry.Stack.twoIso_fieldValuedPointMorphism_fieldValuedPointMap` through
`AlgebraicGeometry.Stack.schemeStack` and
`AlgebraicGeometry.Stack.fieldValuedPointStackMorphism`. -/
def twoIso_fieldValuedPointStackMorphism_fieldValuedPointMap
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (V : BigFppfOver B S hS) (k : Type u) [Field k]
    (hiso : (BigFppfOver.toScheme B S hS).obj V ≅ Spec (.of k))
    (H : schemeStack.{u, w} B S hS V ⟶ 𝒳) :
    (fieldValuedPointStackMorphism.{u, w} B S hS 𝒳
        (fieldValuedPointMap B S hS (schemeFibredCategory B S hS V).val H.hom.hom
          (tautologicalFieldValuedPoint B S hS V k hiso))).hom ≅ H.hom :=
  Bicategory.InducedBicategory.isoMk
    (twoIso_fieldValuedPointMorphism_fieldValuedPointMap B S hS 𝒳.val V k hiso H.hom)

end AlgebraicGeometry.Stack

end
