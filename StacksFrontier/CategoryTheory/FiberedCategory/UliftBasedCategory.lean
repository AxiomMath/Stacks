module

public import Mathlib.CategoryTheory.Category.ULift
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Factorization
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverComp
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoCategory
public import StacksFrontier.CategoryTheory.Sites.Gerbe.Equivalence

/-!
# Raising the universes of a category over a base

Let `𝒞` be a category and let `𝒳` be a category over it. For any pair of universes there is a
category over `𝒞` with the same objects and morphisms up to `ULift`, living in the larger
universes, and equivalent to `𝒳` in the 2-category of categories over `𝒞`. It is
`CategoryTheory.BasedCategory.ulift`, built from Mathlib's universe-lifting equivalence
`CategoryTheory.ULiftHomULiftCategory.equiv`.

This is what makes a statement quantifying over categories over `𝒞` at *fixed* universes apply to
a category at smaller ones: the criteria (5)–(8) of Stacks 045G quantify over categories fibred in
groupoids whose universes are those of the site enlarged by two free parameters, while the
categories one wants to feed them — the slices of the site — live at the site's own universes. The
source takes no notice of the distinction; the universe-lifted slice is its formal counterpart.

## Main definitions

* `CategoryTheory.BasedCategory.ulift`: the universe lift of a category over `𝒞`, with
  `CategoryTheory.BasedCategory.uliftDown` and `CategoryTheory.BasedCategory.uliftUp` the two
  comparison functors.
* `CategoryTheory.CatFiberedInGroupoids.ulift`: the same for a category fibred in groupoids.

## Main results

* `CategoryTheory.BasedCategory.uliftEquivalenceOver`: the universe lift is equivalent to the
  original category in the 2-category of categories over `𝒞`.
* `CategoryTheory.BasedCategory.isFiberedInGroupoids_ulift`: the universe lift of a category fibred
  in groupoids is fibred in groupoids.

## Implementation notes

Both composites of Mathlib's universe-lifting equivalence are the identity functor *on the nose*:
`CategoryTheory.ULiftHom` does not change the type of objects and `CategoryTheory.ULift` is a
structure with eta, so the round trips are definitionally the identity
(`CategoryTheory.BasedCategory.uliftUp_comp_uliftDown` and its companion). That is why the unit and
counit of `CategoryTheory.BasedCategory.uliftEquivalenceOver` are `CategoryTheory.Iso.refl` and why
the structure functor of the lift can be taken to be the quasi-inverse followed by the original
structure functor, with no comparison isomorphism anywhere.

The `Category` instance on the lifted type is supplied explicitly rather than by instance search,
because the object and morphism universes are prescribed by the consumer; a
`CategoryTheory.BasedCategory` carries its instance in a field, so nothing is lost. For the same
reason the two comparison functors are named definitions whose *types* are stated through
`(𝒳.ulift).obj`: every later statement is then phrased with the instance that the lifted
`CategoryTheory.BasedCategory` carries, and no two spellings of it ever meet.

That the lift is fibred in groupoids is Stacks 042X,
`CategoryTheory.Functor.IsFiberedInGroupoids.of_isEquivalenceOver`, applied to the lifting
equivalence, whose unit and counit are identities and hence vertical.

## References

* [Stacks Project, Tag 042X](https://stacks.math.columbia.edu/tag/042X)
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.BasedCategory

universe v₁ u₁ v₂ u₂ v₃ u₃

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞]

/-- The universe lift of a category over `𝒞`: the objects are `ULift`ed into `Type (max u₂ u₃)`
and the morphisms into `Type (max v₂ v₃)`, and the structure functor is the quasi-inverse of
Mathlib's universe-lifting equivalence followed by the original structure functor. -/
def ulift (𝒳 : BasedCategory.{v₂, u₂} 𝒞) : BasedCategory.{max v₂ v₃, max u₂ u₃} 𝒞 :=
  letI : Category.{v₂} (ULift.{u₃} 𝒳.obj) := uliftCategory _
  { obj := ULiftHom.{v₃} (ULift.{u₃} 𝒳.obj)
    category := ULiftHom.category
    p := (ULiftHomULiftCategory.equiv.{v₃, u₃} 𝒳.obj).inverse ⋙ 𝒳.p }

/-- The comparison functor from the universe lift back to the original category: it forgets the
two `ULift`s. -/
def uliftDown (𝒳 : BasedCategory.{v₂, u₂} 𝒞) : (𝒳.ulift).obj ⥤ 𝒳.obj :=
  letI : Category.{v₂} (ULift.{u₃} 𝒳.obj) := uliftCategory _
  (ULiftHomULiftCategory.equiv.{v₃, u₃} 𝒳.obj).inverse

/-- The comparison functor from the original category into its universe lift. -/
def uliftUp (𝒳 : BasedCategory.{v₂, u₂} 𝒞) : 𝒳.obj ⥤ (𝒳.ulift).obj :=
  letI : Category.{v₂} (ULift.{u₃} 𝒳.obj) := uliftCategory _
  (ULiftHomULiftCategory.equiv.{v₃, u₃} 𝒳.obj).functor

/-- The structure functor of the universe lift is the comparison functor followed by the original
structure functor; in particular the comparison is a 1-morphism over `𝒞`. -/
lemma uliftDown_comp (𝒳 : BasedCategory.{v₂, u₂} 𝒞) :
    (uliftDown 𝒳 : (𝒳.ulift).obj ⥤ 𝒳.obj) ⋙ 𝒳.p = (𝒳.ulift).p := rfl

/-- The other comparison functor is a 1-morphism over `𝒞` as well. -/
lemma uliftUp_comp (𝒳 : BasedCategory.{v₂, u₂} 𝒞) :
    (uliftUp 𝒳 : 𝒳.obj ⥤ (𝒳.ulift).obj) ⋙ (𝒳.ulift).p = 𝒳.p := rfl

/-- Lifting and then forgetting is the identity, on the nose. -/
lemma uliftUp_comp_uliftDown (𝒳 : BasedCategory.{v₂, u₂} 𝒞) :
    (uliftUp 𝒳 : 𝒳.obj ⥤ (𝒳.ulift).obj) ⋙ uliftDown 𝒳 = 𝟭 𝒳.obj := rfl

/-- Forgetting and then lifting is the identity, on the nose. -/
lemma uliftDown_comp_uliftUp (𝒳 : BasedCategory.{v₂, u₂} 𝒞) :
    (uliftDown 𝒳 : (𝒳.ulift).obj ⥤ 𝒳.obj) ⋙ uliftUp 𝒳 = 𝟭 (𝒳.ulift).obj := rfl

/-- **The universe lift is equivalent to the original category over `𝒞`.** Both 1-morphisms are
strictly over `𝒞` and both 2-cells are identities. -/
def uliftEquivalenceOver (𝒳 : BasedCategory.{v₂, u₂} 𝒞) :
    StacksRepresentableCFG.EquivalenceOver (𝒳.ulift).p 𝒳.p where
  hom := ⟨uliftDown 𝒳, uliftDown_comp 𝒳⟩
  inv := ⟨uliftUp 𝒳, uliftUp_comp 𝒳⟩
  unitIso := Iso.refl _
  counitIso := Iso.refl _
  unit_over := StacksRepresentableCFG.whiskerRight_eq_eqToHom _ _ _ fun _ => IsHomLift.id rfl
  counit_over := StacksRepresentableCFG.whiskerRight_eq_eqToHom _ _ _ fun _ => IsHomLift.id rfl

/-- **The universe lift of a category fibred in groupoids over `𝒞` is fibred in groupoids over
`𝒞`.** This is Stacks 042X for the universe-lifting equivalence. -/
theorem isFiberedInGroupoids_ulift (𝒳 : BasedCategory.{v₂, u₂} 𝒞)
    (h : 𝒳.p.IsFiberedInGroupoids) : (𝒳.ulift).p.IsFiberedInGroupoids :=
  Functor.IsFiberedInGroupoids.of_isEquivalenceOver (a := uliftUp 𝒳) (uliftUp_comp 𝒳)
    { inv := uliftDown 𝒳
      inv_over := uliftDown_comp 𝒳
      unitIso := Iso.refl _
      counitIso := Iso.refl _
      unit_vertical := fun _ => IsHomLift.id rfl
      counit_vertical := fun _ => IsHomLift.id rfl } h

end CategoryTheory.BasedCategory

namespace CategoryTheory.CatFiberedInGroupoids

universe v₁ u₁ v₂ u₂ v₃ u₃

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞]

/-- The universe lift of a category fibred in groupoids over `𝒞`, as an object of the 2-category of
categories fibred in groupoids over `𝒞`. -/
def ulift (𝒳 : CatFiberedInGroupoids.{v₁, v₂, u₁, u₂} 𝒞) :
    CatFiberedInGroupoids.{v₁, max v₂ v₃, u₁, max u₂ u₃} 𝒞 :=
  CatFiberedInGroupoids.mk (𝒳.val.ulift)
    (BasedCategory.isFiberedInGroupoids_ulift 𝒳.val 𝒳.isFiberedInGroupoids)

/-- The based category underlying the universe lift of `𝒳` is the universe lift of the based
category underlying `𝒳`. -/
@[simp]
lemma ulift_val (𝒳 : CatFiberedInGroupoids.{v₁, v₂, u₁, u₂} 𝒞) :
    (𝒳.ulift : CatFiberedInGroupoids.{v₁, max v₂ v₃, u₁, max u₂ u₃} 𝒞).val = 𝒳.val.ulift := rfl

end CategoryTheory.CatFiberedInGroupoids

end
