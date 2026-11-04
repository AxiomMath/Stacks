module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FaithfulRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.SpacesOverAlgebraicStack
public import StacksFrontier.CategoryTheory.Bicategory.TwoOneCategory
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.LocallyGroupoid
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.WhiskerFaithful
public import StacksFrontier.CategoryTheory.FiberedInSetoids.Setoid

/-!
# `Spaces/𝒴` is very close to being a category (Stacks 04ZQ)

Let `𝒴` be an algebraic stack. Stacks 04ZQ introduces the 2-category `Spaces/𝒴` of algebraic
stacks over `𝒴` whose structure 1-morphism is representable by algebraic spaces
(`AlgebraicGeometry.Stack.SpacesOverStack`, built in
`StacksFrontier.AlgebraicGeometry.Stacks.SpacesOverAlgebraicStack`) and then makes two further
claims about it, which are what this file proves.

The first is that the hom-categories of `Spaces/𝒴` are *setoids* in the sense of Stacks 02XZ:
between two 1-morphisms there is at most one 2-morphism, and it is invertible. Thinness is where
representability enters. A 2-morphism `(g, β) ⟶ (g', β')` is a 2-morphism `α : g ⟶ g'` of the
source stacks subject to `β ≫ α ▷ f₂ = β'`; since `β` is invertible this pins down `α ▷ f₂`, and
`f₂` is faithful by **Stacks 04Y5**, the implication (3) ⟹ (2), so `α` itself is pinned down.

The second is that replacing the 1-morphisms of `Spaces/𝒴` by their isomorphism classes gives an
honest category, which the source then uses without further mention.

## Main definitions

* `AlgebraicGeometry.Stack.SpacesOverStack.homClass`: the isomorphism class of a 1-morphism of
  `Spaces/𝒴`.
* `AlgebraicGeometry.Stack.SpacesOverStack.isoClassCategory`: **Stacks 04ZQ**, the category
  obtained from `Spaces/𝒴` by replacing its 1-morphisms by their isomorphism classes.

## Main results

* `AlgebraicGeometry.Stack.SpacesOverStack.isSetoidCategory_hom`: **Stacks 04ZQ**, the
  hom-categories of `Spaces/𝒴` are setoids.
* `AlgebraicGeometry.Stack.SpacesOverStack.hom₂_ext`: the thinness half of that, stated on its
  own because it is what the rest of the file uses.
* `AlgebraicGeometry.Stack.SpacesOverStack.isoClassCategory_hom`,
  `AlgebraicGeometry.Stack.SpacesOverStack.homClass_surjective`,
  `AlgebraicGeometry.Stack.SpacesOverStack.isoClassCategory_id` and
  `AlgebraicGeometry.Stack.SpacesOverStack.isoClassCategory_comp`: that category has exactly the
  isomorphism classes of 1-morphisms as its morphisms, and its identities and composition are the
  induced ones. These pin down the content of `isoClassCategory`, which its type alone does not
  record.
* `AlgebraicGeometry.Stack.SpacesOverStack.homClass_eq_iff`: two 1-morphisms have the same
  isomorphism class exactly when some 2-morphism connects them — the setoid property again, now
  as a description of the morphisms of `isoClassCategory`.

## Implementation notes

`isoClassCategory` is a `def` producing a `Category` structure, not an `instance`. An instance
would clash with the `CategoryStruct` of the 2-category
(`AlgebraicGeometry.Stack.SpacesOverStack.instCategoryStruct`), which has the same object type
and the 1-morphisms themselves — not their isomorphism classes — as morphisms. The source's
"we will often perform this replacement without further mention" is a change of category, not an
extra structure on the old one, so a consumer selects it with `letI`.

Passing to isomorphism classes is what *produces* the category laws here. `Spaces/𝒴` is not
claimed to be a strict bicategory (see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Stacks.SpacesOverAlgebraicStack`), so its composition of
1-morphisms is associative and unital only up to the associator and the unitors; after
quotienting by isomorphism those structural 2-isomorphisms become equalities, and no strictness
is needed anywhere below.

The quotient is by isomorphism of 1-morphisms, `CategoryTheory.isIsomorphicSetoid`, which is the
source's "isomorphism classes of 1-morphisms". By `homClass_eq_iff` this is the same as the
relation "there exists a 2-morphism", precisely because the hom-categories are setoids; the
isomorphism-class form is the one the source names, so it is the one taken as the definition.

## References

* [Stacks Project, Tag 02XZ](https://stacks.math.columbia.edu/tag/02XZ)
* [Stacks Project, Tag 04Y5](https://stacks.math.columbia.edu/tag/04Y5)
* [Stacks Project, Tag 04ZQ](https://stacks.math.columbia.edu/tag/04ZQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Bicategory

namespace AlgebraicGeometry.Stack.SpacesOverStack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {𝒴 : AlgebraicStacks.{u, w} B S hS}

/-- The functor underlying the structure 1-morphism of an object of `Spaces/𝒴` is faithful: that
1-morphism is representable by algebraic spaces, and **Stacks 04Y5**, the implication (3) ⟹ (2),
turns representability into faithfulness. -/
theorem faithful_homFunctor_map (F : SpacesOverStack B S hS 𝒴) :
    (CatFiberedInGroupoids.homFunctor F.map.hom).Faithful :=
  AlgebraicGeometry.Stack.AlgebraicStacks.faithful_homFunctor_of_isRepresentableByAlgebraicSpaces
    B S hS F.map F.representable

/-- **The hom-categories of `Spaces/𝒴` are thin:** between two 1-morphisms there is at most one
2-morphism.

A 2-morphism `α : f ⟶ g` carries a 2-morphism `α.map` of the underlying 1-morphisms of algebraic
stacks, and its compatibility condition reads `f.comm ≫ α.map ▷ G.map = g.comm`. The 2-morphism
`f.comm` is invertible: algebraic stacks form a full sub-2-category of the categories fibred in
groupoids, where every 2-morphism is invertible
(`CategoryTheory.CatFiberedInGroupoids.homGroupoid`). So that condition determines
`α.map ▷ G.map`. The functor underlying `G.map` is
faithful by `AlgebraicGeometry.Stack.SpacesOverStack.faithful_homFunctor_map`, so right
whiskering by `G.map` is injective on 2-morphisms and `α.map` is determined as well. -/
theorem hom₂_ext {F G : SpacesOverStack B S hS 𝒴} {f g : F ⟶ G} (α β : f ⟶ g) : α = β := by
  have := faithful_homFunctor_map G
  have : IsIso f.comm := IsGroupoid.all_isIso f.comm
  have hw : α.map ▷ G.map = β.map ▷ G.map :=
    (cancel_epi f.comm).mp (α.compat.trans β.compat.symm)
  exact Hom₂.ext (Bicategory.InducedBicategory.hom₂_ext
    (CatFiberedInGroupoids.hom₂_ext_of_whiskerRight_faithful G.map.hom
      (congrArg (fun t => t.hom) hw)))

/-- **The hom-categories of `Spaces/𝒴` are groupoids.** A 2-morphism of `Spaces/𝒴` whose
underlying 2-morphism of algebraic stacks is invertible is itself invertible
(`AlgebraicGeometry.Stack.SpacesOverStack.Hom₂.iso`), and every 2-morphism of algebraic stacks is
invertible. -/
instance isGroupoid_hom (F G : SpacesOverStack B S hS 𝒴) : IsGroupoid (F ⟶ G) where
  all_isIso {_f _g} α :=
    haveI : IsIso α.map := IsGroupoid.all_isIso α.map
    have h : (Hom₂.iso (asIso α.map) α.compat).hom = α := Hom₂.ext rfl
    h ▸ (inferInstance : IsIso (Hom₂.iso (asIso α.map) α.compat).hom)

/-- **Stacks 04ZQ.** Every hom-category of `Spaces/𝒴` is a setoid in the sense of Stacks 02XZ:
it is a groupoid and it is thin, so a 1-morphism of `Spaces/𝒴` has no automorphism but the
identity. This is the source's claim that the morphism categories
`Mor_{Spaces/𝒴}((f₁ : 𝒳₁ ⟶ 𝒴), (f₂ : 𝒳₂ ⟶ 𝒴))` are all setoids. -/
@[stacks 04ZQ "the hom-categories are setoids"]
theorem isSetoidCategory_hom (F G : SpacesOverStack B S hS 𝒴) :
    IsSetoidCategory (F ⟶ G) :=
  ⟨fun _ => inferInstance, fun f α => hom₂_ext α (𝟙 f)⟩

/-- The isomorphism class of a 1-morphism of `Spaces/𝒴`, i.e. its image in the morphisms of
`AlgebraicGeometry.Stack.SpacesOverStack.isoClassCategory`. -/
def homClass {F G : SpacesOverStack B S hS 𝒴} (f : F ⟶ G) :
    Quotient (isIsomorphicSetoid (F ⟶ G)) :=
  Quotient.mk _ f

/-- **Stacks 04ZQ.** Replacing the 1-morphisms of `Spaces/𝒴` by their isomorphism classes gives a
category: the objects are those of `Spaces/𝒴`, a morphism `F ⟶ G` is an isomorphism class of
1-morphisms `F ⟶ G` of the 2-category, and the identities and the composition are induced by
those of the 2-category.

Composition descends because whiskering turns a pair of isomorphic 1-morphisms into isomorphic
composites, and the three category laws hold because the unitors and the associator of
`Spaces/𝒴` become equalities of isomorphism classes. -/
@[instance_reducible, stacks 04ZQ "the category of isomorphism classes of 1-morphisms"]
def isoClassCategory : Category.{u + 1} (SpacesOverStack B S hS 𝒴) where
  Hom F G := Quotient (isIsomorphicSetoid (F ⟶ G))
  id F := homClass (𝟙 F)
  comp := Quotient.map₂ (· ≫ ·) fun _ _ ⟨e⟩ _ _ ⟨e'⟩ =>
    ⟨whiskerRightIso e _ ≪≫ whiskerLeftIso _ e'⟩
  id_comp := Quotient.ind fun f => Quotient.sound ⟨λ_ f⟩
  comp_id := Quotient.ind fun f => Quotient.sound ⟨ρ_ f⟩
  assoc := Quotient.ind fun f => Quotient.ind fun g => Quotient.ind fun h =>
    Quotient.sound ⟨α_ f g h⟩

/-- A morphism of `AlgebraicGeometry.Stack.SpacesOverStack.isoClassCategory` is an isomorphism
class of 1-morphisms of `Spaces/𝒴`. -/
theorem isoClassCategory_hom (F G : SpacesOverStack B S hS 𝒴) :
    isoClassCategory.toCategoryStruct.toQuiver.Hom F G =
      Quotient (isIsomorphicSetoid (F ⟶ G)) :=
  rfl

/-- Every morphism of `AlgebraicGeometry.Stack.SpacesOverStack.isoClassCategory` is the
isomorphism class of a 1-morphism of `Spaces/𝒴`: no morphisms are added by the passage to
isomorphism classes. -/
theorem homClass_surjective (F G : SpacesOverStack B S hS 𝒴) :
    Function.Surjective (homClass (F := F) (G := G)) :=
  Quotient.exists_rep

/-- The identity of `AlgebraicGeometry.Stack.SpacesOverStack.isoClassCategory` is induced by the
identity 1-morphism of `Spaces/𝒴`. -/
theorem isoClassCategory_id (F : SpacesOverStack B S hS 𝒴) :
    isoClassCategory.toCategoryStruct.id F = homClass (𝟙 F) :=
  rfl

/-- The composition of `AlgebraicGeometry.Stack.SpacesOverStack.isoClassCategory` is induced by
the composition of 1-morphisms of `Spaces/𝒴`. -/
theorem isoClassCategory_comp {F G H : SpacesOverStack B S hS 𝒴} (f : F ⟶ G) (g : G ⟶ H) :
    isoClassCategory.toCategoryStruct.comp (homClass f) (homClass g) = homClass (f ≫ g) :=
  rfl

/-- Two 1-morphisms of `Spaces/𝒴` have the same isomorphism class exactly when there is a
2-morphism between them: the hom-categories are groupoids, so any 2-morphism is already an
isomorphism. This describes the morphisms of
`AlgebraicGeometry.Stack.SpacesOverStack.isoClassCategory` without mentioning invertibility. -/
theorem homClass_eq_iff {F G : SpacesOverStack B S hS 𝒴} (f g : F ⟶ G) :
    homClass f = homClass g ↔ Nonempty (f ⟶ g) :=
  ⟨fun h => (Quotient.exact h).elim fun e => ⟨e.hom⟩,
    fun ⟨α⟩ => Quotient.sound ⟨@asIso _ _ _ _ α (IsGroupoid.all_isIso α)⟩⟩

end AlgebraicGeometry.Stack.SpacesOverStack

end
