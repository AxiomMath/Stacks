module

public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import StacksFrontier.CategoryTheory.Sites.Descent.PrestackOfCover
public import StacksFrontier.CategoryTheory.Sites.Glueing.AbsoluteGlueingAnySite

/-!
# The sheaf condition for a topology is local on a covering for a second topology

Let `C` be a category carrying two Grothendieck topologies `J` and `K`, neither assumed coarser
than the other, and let `X : I → C` be a family of objects covering the final object for `K`. A
presheaf on `C` which is a `K`-sheaf and whose restriction to the slice site `C/X i` is a `J`-sheaf
for every `i` is a `J`-sheaf.

## Main results

* `CategoryTheory.SiteGlueing.isSheaf_of_coversTop_of_isSheaf_over`: the statement for a presheaf
  of `w`-sets.
* `CategoryTheory.SiteGlueing.isSheaf_of_coversTop_of_isSheaf_over'`: the same for a presheaf with
  values in an arbitrary category.
* `CategoryTheory.SiteGlueing.isSheaf_of_coversTop_of_isSheaf_over_anyCategory` and
  `CategoryTheory.SiteGlueing.isSheaf_of_coversTop_of_isSheaf_over_anyCategory'`: the same two
  statements on a site with no `HasPullbacks` assumption.
-/

@[expose] public section

open CategoryTheory Opposite CategoryTheory.Limits

universe w t v₂ u₂ v u

namespace CategoryTheory.SiteGlueing

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- Let `J` and `K` be Grothendieck topologies on a category `C`, with no `HasPullbacks`
assumption, and let `X` be a family of objects covering the final object for `K`. A presheaf of
sets which is a `K`-sheaf and whose restriction to the slice site at each `X i` is a `J`-sheaf is
a `J`-sheaf. -/
theorem isSheaf_of_coversTop_of_isSheaf_over_anyCategory {K : GrothendieckTopology C}
    {I : Type t} {X : I → C} (hX : K.CoversTop X) (P : Cᵒᵖ ⥤ Type w)
    (hK : Presieve.IsSheaf K P)
    (h : ∀ i, Presieve.IsSheaf (J.over (X i)) ((Over.forget (X i)).op ⋙ P)) :
    Presieve.IsSheaf J P := by
  intro W S hS
  refine Presieve.isSheafFor_trans P (Sieve.ofObjects X W) S (hK _ (hX W)) ?_ ?_
  · intro Y f _
    exact (hK _ (K.pullback_stable f (hX W))).isSeparatedFor
  · rintro Y f ⟨i, ⟨a⟩⟩
    exact isSheafFor_of_isSheaf_over J P (h i) (Over.mk a) (J.pullback_stable f hS)

/-- Let `J` and `K` be Grothendieck topologies on a category `C`, with no `HasPullbacks`
assumption, and let `X` be a family of objects covering the final object for `K`. A presheaf with
values in a category `A` which is a `K`-sheaf and whose restriction to the slice site at each
`X i` is a `J`-sheaf is a `J`-sheaf. -/
theorem isSheaf_of_coversTop_of_isSheaf_over_anyCategory' {A : Type u₂} [Category.{v₂} A]
    {K : GrothendieckTopology C} {I : Type t} {X : I → C} (hX : K.CoversTop X)
    (P : Cᵒᵖ ⥤ A) (hK : Presheaf.IsSheaf K P)
    (h : ∀ i, Presheaf.IsSheaf (J.over (X i)) ((Over.forget (X i)).op ⋙ P)) :
    Presheaf.IsSheaf J P :=
  fun E => isSheaf_of_coversTop_of_isSheaf_over_anyCategory J hX _ (hK E) fun i => h i E

/-- A presheaf of sets which is a `K`-sheaf and whose restriction to the slice site at each
member of a family of objects covering the final object for `K` is a `J`-sheaf is a `J`-sheaf. -/
theorem isSheaf_of_coversTop_of_isSheaf_over [HasPullbacks C]
    {K : GrothendieckTopology C} {I : Type t} {X : I → C} (hX : K.CoversTop X)
    (P : Cᵒᵖ ⥤ Type w) (hK : Presieve.IsSheaf K P)
    (h : ∀ i, Presieve.IsSheaf (J.over (X i)) ((Over.forget (X i)).op ⋙ P)) :
    Presieve.IsSheaf J P :=
  isSheaf_of_coversTop_of_isSheaf_over_anyCategory J hX P hK h

/-- A presheaf with values in a category `A` which is a `K`-sheaf and whose restriction to the
slice site at each member of a family of objects covering the final object for `K` is a `J`-sheaf
is a `J`-sheaf. -/
theorem isSheaf_of_coversTop_of_isSheaf_over' [HasPullbacks C]
    {A : Type u₂} [Category.{v₂} A]
    {K : GrothendieckTopology C} {I : Type t} {X : I → C} (hX : K.CoversTop X)
    (P : Cᵒᵖ ⥤ A) (hK : Presheaf.IsSheaf K P)
    (h : ∀ i, Presheaf.IsSheaf (J.over (X i)) ((Over.forget (X i)).op ⋙ P)) :
    Presheaf.IsSheaf J P :=
  fun E => isSheaf_of_coversTop_of_isSheaf_over J hX _ (hK E) fun i => h i E

end CategoryTheory.SiteGlueing

end
