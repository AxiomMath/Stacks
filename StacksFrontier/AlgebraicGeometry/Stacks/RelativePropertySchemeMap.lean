module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.MorphismSpaceIsoClass
public import StacksFrontier.AlgebraicGeometry.Stacks.ObjectMorphismFactor
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRepresented

/-!
# The relative property of a 1-morphism induced by a morphism of the site

Let `P` be a property of morphisms of algebraic spaces over `S` which is stable under base change
and local on the target for the fppf precoverage, so that the relative property of **Stacks 03YK**
is available for it. This module supplies the two transports of that relative property which the
closure condition of **Stacks 07AK** (1) — hence **Stacks 0788** — needs beyond
`AlgebraicGeometry.Stack.hasRelativeProperty_comp` (**Stacks 045B**).

The first is the value of the relative property on the 1-morphism
`AlgebraicGeometry.Stack.schemeFibredCategoryMap` induced by a morphism `g : U ⟶ V` of the big
fppf category of `S`: it holds exactly when the morphism `h_U ⟶ h_V` of representable algebraic
spaces has `P`. The second is invariance of the relative property under a 2-isomorphism of the
1-morphism, which is what lets a property be transported along
`AlgebraicGeometry.Stack.objectMorphismFactorIso`.

## Main results

* `AlgebraicGeometry.Stack.representingMap_schemeFibredCategoryMap`: the morphism of representing
  presheaves induced by `AlgebraicGeometry.Stack.schemeFibredCategoryMap` at `g` is `yoneda.map g`.
* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_schemeFibredCategoryMap`: that
  1-morphism is representable by algebraic spaces.
* `AlgebraicGeometry.Stack.hasRelativeProperty_schemeFibredCategoryMap`: it has the relative
  property `P` as soon as `yoneda.map g` has `P` as a morphism of algebraic spaces over `S`.
* `AlgebraicGeometry.Stack.hasRelativeProperty_congr_twoIso`: the relative property is invariant
  under a 2-isomorphism of the 1-morphism.

## Implementation notes

No declaration here carries a `@[stacks]` attribute. The first two results are computations of
already tagged objects — `AlgebraicGeometry.Stack.morphismSpaceEquiv` (**Stacks 04SW**) and
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_of_isRepresentableByAlgebraicSpace`
(**Stacks 02ZZ**) — the third is the bridge of the Stacks 04XB conventions
(`AlgebraicGeometry.Stack.hasRelativeProperty_iff_prop_representingMap`) read at a represented
source and target, and the fourth is **Stacks 0457** for the relative property, which is proved as
`AlgebraicGeometry.Stack.hasRelativeProperty_of_equivalences`, at `a = b = `identity.

`AlgebraicGeometry.Stack.hasRelativeProperty_congr_twoIso` is therefore not a new proof: it is the
general-`P` form of `AlgebraicGeometry.Stack.isRelativelySmooth_congr_twoIso`, obtained
from the same theorem in the same way. The two composites of the 2-commutative square are the two
1-morphisms themselves because `CategoryTheory.BasedFunctor.id_comp` and `_comp_id` hold by `rfl`.

`AlgebraicGeometry.Stack.representingMap_schemeFibredCategoryMap` is proved through
`AlgebraicGeometry.Stack.morphismSpaceEquiv_eq_of_sectionOfObj` — a morphism of representing
presheaves is determined by its values on named sections — rather than through the shorter
`AlgebraicGeometry.Stack.morphismSpaceEquiv_eq_of_comp_eq`. The two functors that second criterion
compares are equal by `rfl`, but checking that `rfl` exhausts the kernel's deterministic budget,
and reporting the failure at the statement makes it read as a defective statement. On named
sections the computation is immediate once the equality of base objects is substituted: an object
of `(Sch/S)/U` names its own structure morphism, and postcomposition with `g` is what both sides
do to it.

## References

* [Stacks Project, Tag 02ZZ](https://stacks.math.columbia.edu/tag/02ZZ)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 0457](https://stacks.math.columbia.edu/tag/0457)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v w t

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The morphism of representing presheaves of Stacks 04SW for a morphism of the site.** The
1-morphism `AlgebraicGeometry.Stack.schemeFibredCategoryMap` induced by `g : U ⟶ V` induces, under
the identification of the slice over a scheme with the category of elements of the presheaf that
scheme represents, the morphism `yoneda.map g` of representable presheaves.

Both sides send the section of `h_U` named by an object of `(Sch/S)/U` — its own structure
morphism — to that morphism composed with `g`. -/
theorem representingMap_schemeFibredCategoryMap {U V : BigFppfOver B S hS} (g : U ⟶ V) :
    representingMap B S hS (schemeFibredCategory B S hS U) (schemeFibredCategory B S hS V)
        (yoneda.obj U) (yoneda.obj V)
        (PresheafOfCategories.sliceElementsEquivalenceOver U)
        (PresheafOfCategories.sliceElementsEquivalenceOver V)
        (schemeFibredCategoryMap B S hS g) = yoneda.map g := by
  refine morphismSpaceEquiv_eq_of_sectionOfObj B S hS _ _ _ _ _ _ _ _ (fun z W hz => ?_)
  cases hz
  rfl

/-- **Stacks 02ZZ for a morphism of the site.** The 1-morphism of represented categories fibred in
groupoids induced by a morphism `g : U ⟶ V` of the big fppf category of `S` is representable by
algebraic spaces: both its source and its target are representable by the algebraic spaces of
Stacks 025Z. -/
theorem isRepresentableByAlgebraicSpaces_schemeFibredCategoryMap
    {U V : BigFppfOver B S hS} (g : U ⟶ V) :
    IsRepresentableByAlgebraicSpaces B S hS (schemeFibredCategoryMap B S hS g).hom :=
  isRepresentableByAlgebraicSpaces_of_isRepresentableByAlgebraicSpace B S hS
    (schemeFibredCategoryMap B S hS g)
    (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS U)
    (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS V)

/-- **The relative property of Stacks 03YK for the 1-morphism induced by a morphism of the site.**
Let `P` be a property of morphisms of algebraic spaces over `S` stable under base change and local
on the target for the fppf precoverage. If the morphism `h_U ⟶ h_V` of representable algebraic
spaces attached to `g : U ⟶ V` has `P`, then the induced 1-morphism
`AlgebraicGeometry.Stack.schemeFibredCategoryMap` at `g` has `P` relatively.

This is the bridge of the Stacks 04XB conventions
(`AlgebraicGeometry.Stack.hasRelativeProperty_iff_prop_representingMap`) at a represented source
and target, with the induced morphism of representing presheaves computed by
`AlgebraicGeometry.Stack.representingMap_schemeFibredCategoryMap`. -/
theorem hasRelativeProperty_schemeFibredCategoryMap
    (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, t} B S hS)]
    {U V : BigFppfOver B S hS} (g : U ⟶ V)
    (hg : P (ObjectProperty.homMk (yoneda.map g) :
      (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS) ⟶
        ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩)) :
    HasRelativeProperty.{u, u, u + 1, t} B S hS P (schemeFibredCategoryMap B S hS g)
      (isRepresentableByAlgebraicSpaces_schemeFibredCategoryMap B S hS g) := by
  refine (hasRelativeProperty_iff_prop_representingMap.{u, t} B S hS P
    (schemeFibredCategoryMap B S hS g)
    (isRepresentableByAlgebraicSpaces_schemeFibredCategoryMap B S hS g)
    (yoneda.obj U) (yoneda.obj V)
    (isAlgebraicSpace_yoneda B S hS U) (isAlgebraicSpace_yoneda B S hS V)
    (PresheafOfCategories.sliceElementsEquivalenceOver U)
    (PresheafOfCategories.sliceElementsEquivalenceOver V)).2 ?_
  rw [representingMap_schemeFibredCategoryMap]
  exact hg

/-- **The relative property of Stacks 03YK is invariant under a 2-isomorphism of the 1-morphism.**
Two 2-isomorphic 1-morphisms of categories fibred in groupoids over the big fppf site of `S`, both
representable by algebraic spaces, have the relative property `P` together.

This is `AlgebraicGeometry.Stack.hasRelativeProperty_of_equivalences` — **Stacks 0457** for the
relative property — with both horizontal 1-morphisms of the 2-commutative square taken to be the
identity, for which the two composites are the two 1-morphisms themselves. No hypothesis on `P` is
used beyond the two that naming the relative property requires, and the smooth case
`AlgebraicGeometry.Stack.isRelativelySmooth_congr_twoIso` is this statement at
`AlgebraicGeometry.Space.smoothMorphismProperty`. -/
theorem hasRelativeProperty_congr_twoIso
    (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, t} B S hS)]
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)} {f g : 𝒳 ⟶ 𝒴}
    (e : f ≅ g)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom)
    (hg : IsRepresentableByAlgebraicSpaces B S hS g.hom)
    (h : HasRelativeProperty.{u, v, w, t} B S hS P f hf) :
    HasRelativeProperty.{u, v, w, t} B S hS P g hg := by
  have ha : Functor.IsEquivalence (BasedFunctor.id 𝒳.val).toFunctor :=
    inferInstanceAs (Functor.IsEquivalence (𝟭 𝒳.val.obj))
  have hb : Functor.IsEquivalence (BasedFunctor.id 𝒴.val).toFunctor :=
    inferInstanceAs (Functor.IsEquivalence (𝟭 𝒴.val.obj))
  exact hasRelativeProperty_of_equivalences B S hS P g f (BasedFunctor.id 𝒳.val)
    (BasedFunctor.id 𝒴.val) (twoIsoHomIso B S hS e) hf hg h

end AlgebraicGeometry.Stack

end
