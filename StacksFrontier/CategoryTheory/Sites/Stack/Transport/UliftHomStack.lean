module

public import StacksFrontier.CategoryTheory.FiberedCategory.UliftBasedCategory
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverBased
public import StacksFrontier.CategoryTheory.Sites.Stack.Transport

/-!
# Raising only the morphism universe of a category over a site

Let `𝒞` be a category and let `p : 𝒳 ⥤ 𝒞` be a category over it. Mathlib's
`CategoryTheory.ULiftHom` leaves the objects of a category alone and raises its morphisms, so
`CategoryTheory.ULiftHom.down ⋙ p` is a category over `𝒞` with the *same* objects as `𝒳`, with
morphisms in a larger universe, and equivalent to `p` in the 2-category of categories over `𝒞`.

Only the morphism universe is raised because that is the shape in which the explicit
stackification of Stacks 02ZN consumes its input: the pointwise groupoid fibration of a groupoid
in algebraic spaces already has its objects one universe above the site, and
`AlgebraicGeometry.Stack.quotientPrestack` raises only its morphisms. A target offered to the
determinacy clause of Stacks 02ZN therefore has to be presented at the same raised morphism
universe, with its objects left where they are;
`CategoryTheory.BasedCategory.ulift` raises both universes and so does not apply.

## Main definitions

* `CategoryTheory.Functor.uliftHomProj`: the morphism-universe lift of a category over `𝒞`.
* `CategoryTheory.Functor.isEquivalenceOver_uliftHomUp`: the lift is equivalent to the original
  category over `𝒞`.
* `CategoryTheory.Functor.uliftHomBasedEquivalence`: the same, read as a
  `CategoryTheory.BasedCategory.Equivalence`, which is the form Stacks 042W is stated with.

## Main results

* `CategoryTheory.Functor.isFiberedInGroupoids_uliftHomProj` and
  `CategoryTheory.Functor.isFibered_uliftHomProj`: the lift of a category fibred in groupoids is
  fibred in groupoids, hence fibred.
* `CategoryTheory.Functor.isStack_uliftHomProj` and
  `CategoryTheory.Functor.isStack_uliftHomProj_iff`: Stacks 026F for the lift.

## Implementation notes

`CategoryTheory.ULiftHom C` is a *definitional alias* for `C`, so the objects and the structure
functor are unchanged on the nose and both round trips of the comparison are the identity functor
definitionally. Every compatibility below is therefore `rfl`, and the unit and counit of the
equivalence are `CategoryTheory.Iso.refl`, exactly as for
`CategoryTheory.BasedCategory.uliftEquivalenceOver`.

Everything is stated for the *functor* `p` rather than for a `CategoryTheory.BasedCategory`, and
a based category is formed only where Stacks 042W needs one. Stating the comparison functors with
a `CategoryTheory.BasedCategory`'s `obj` field in their type makes the category instance on the
lift arrive by a projection out of a semireducible definition, which the elaborator's instance
check then refuses to identify with the one instance search finds.

That the lift is fibred in groupoids is Stacks 042X,
`CategoryTheory.Functor.IsFiberedInGroupoids.of_isEquivalenceOver`, and that it is a stack is
Stacks 042W, `CategoryTheory.BasedCategory.isStack_iff_of_equivalence`; neither is reproved.

## References

* [Stacks Project, Tag 026F](https://stacks.math.columbia.edu/tag/026F)
* [Stacks Project, Tag 042W](https://stacks.math.columbia.edu/tag/042W)
* [Stacks Project, Tag 042X](https://stacks.math.columbia.edu/tag/042X)
-/

@[expose] public section

namespace CategoryTheory.Functor

universe v₁ u₁ v₂ u₂ v₃

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳] (p : 𝒳 ⥤ 𝒞)

/-- The morphism-universe lift of a category over `𝒞`: the same objects and the same structure
functor, with the morphisms `ULift`ed. -/
abbrev uliftHomProj : ULiftHom.{v₃} 𝒳 ⥤ 𝒞 := (ULiftHom.down : ULiftHom.{v₃} 𝒳 ⥤ 𝒳) ⋙ p

/-- Forgetting the lift is a 1-morphism over `𝒞`. -/
lemma uliftHomDown_comp :
    (ULiftHom.down : ULiftHom.{v₃} 𝒳 ⥤ 𝒳) ⋙ p = (uliftHomProj p : ULiftHom.{v₃} 𝒳 ⥤ 𝒞) := rfl

/-- Taking the lift is a 1-morphism over `𝒞`. -/
lemma uliftHomUp_comp :
    (ULiftHom.up : 𝒳 ⥤ ULiftHom.{v₃} 𝒳) ⋙ (uliftHomProj p : ULiftHom.{v₃} 𝒳 ⥤ 𝒞) = p := rfl

/-- **The morphism-universe lift is equivalent to the original category over `𝒞`**: the
quasi-inverse is strictly over `𝒞` and both 2-cells are identities. -/
def isEquivalenceOver_uliftHomUp :
    IsEquivalenceOver p (uliftHomProj p : ULiftHom.{v₃} 𝒳 ⥤ 𝒞)
      (ULiftHom.up : 𝒳 ⥤ ULiftHom.{v₃} 𝒳) where
  inv := ULiftHom.down
  inv_over := uliftHomDown_comp p
  unitIso := Iso.refl _
  counitIso := Iso.refl _
  unit_vertical _ := IsHomLift.id rfl
  counit_vertical _ := IsHomLift.id rfl

/-- The morphism-universe lift, read as an equivalence over `𝒞` in the bundled sense. -/
def equivalenceOver_uliftHom :
    StacksRepresentableCFG.EquivalenceOver p (uliftHomProj p : ULiftHom.{v₃} 𝒳 ⥤ 𝒞) where
  hom := ⟨(ULiftHom.up : 𝒳 ⥤ ULiftHom.{v₃} 𝒳), uliftHomUp_comp p⟩
  inv := ⟨(ULiftHom.down : ULiftHom.{v₃} 𝒳 ⥤ 𝒳), uliftHomDown_comp p⟩
  unitIso := Iso.refl _
  counitIso := Iso.refl _
  unit_over := StacksRepresentableCFG.whiskerRight_eq_eqToHom _ _ _ fun _ => IsHomLift.id rfl
  counit_over := StacksRepresentableCFG.whiskerRight_eq_eqToHom _ _ _ fun _ => IsHomLift.id rfl

/-- The morphism-universe lift, read as an equivalence of the two based categories over `𝒞`.
This is the form Stacks 042W is stated with. -/
def uliftHomBasedEquivalence :
    BasedCategory.Equivalence (BasedCategory.ofFunctor p)
      (BasedCategory.ofFunctor (uliftHomProj p : ULiftHom.{v₃} 𝒳 ⥤ 𝒞)) :=
  StacksRepresentableCFG.EquivalenceOver.toBasedEquivalence (equivalenceOver_uliftHom p)

/-- **The morphism-universe lift of a category fibred in groupoids over `𝒞` is fibred in
groupoids.** This is Stacks 042X for the lifting equivalence. -/
theorem isFiberedInGroupoids_uliftHomProj (h : p.IsFiberedInGroupoids) :
    (uliftHomProj p : ULiftHom.{v₃} 𝒳 ⥤ 𝒞).IsFiberedInGroupoids :=
  IsFiberedInGroupoids.of_isEquivalenceOver (a := (ULiftHom.up : 𝒳 ⥤ ULiftHom.{v₃} 𝒳))
    (uliftHomUp_comp p) (isEquivalenceOver_uliftHomUp p) h

/-- The morphism-universe lift of a category fibred in groupoids is a fibred category. -/
theorem isFibered_uliftHomProj (h : p.IsFiberedInGroupoids) :
    (uliftHomProj p : ULiftHom.{v₃} 𝒳 ⥤ 𝒞).IsFibered :=
  (isFiberedInGroupoids_uliftHomProj p h).isFibered

/-- **Stacks 026F for the morphism-universe lift**: the lift of a stack over the site `(𝒞, J)` is
a stack over `(𝒞, J)`. -/
theorem isStack_uliftHomProj (J : GrothendieckTopology 𝒞) (h : p.IsStack J) :
    (uliftHomProj p : ULiftHom.{v₃} 𝒳 ⥤ 𝒞).IsStack J :=
  (uliftHomBasedEquivalence p).isStack J h

/-- **Raising the morphism universe neither creates nor destroys the stack condition.** -/
theorem isStack_uliftHomProj_iff (J : GrothendieckTopology 𝒞) :
    p.IsStack J ↔ (uliftHomProj p : ULiftHom.{v₃} 𝒳 ⥤ 𝒞).IsStack J :=
  BasedCategory.isStack_iff_of_equivalence (uliftHomBasedEquivalence p) J

end CategoryTheory.Functor

end
