module

public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeAutomorphismSpaceGroupLaw
public import StacksFrontier.CategoryTheory.FiberedCategory.ElementsTotalPresheaf

/-!
# The relative sheaf of automorphisms as a presheaf over `Z` on the big fppf site

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S`, let `Z` be an algebraic space over
`S` and let `x : Z ⟶ 𝒳` be an algebraic-space-valued point. This file defines
`Isom_{𝒳/𝒴}(x, x)` as a presheaf on the big fppf site of `S`, through the total-presheaf
construction `CategoryTheory.PresheafOfCategories.elementsTotalPresheaf`: the presheaf `Σ_Z F`
on the big fppf site whose sections over `W` are the pairs of a point `z` of `Z` over `W` and a
section of `F` at `(W, z)`. Applied to the presheaf of relative automorphisms it gives the
presheaf whose sections over `W` are the pairs of a point `z` of `Z` over `W` and an automorphism
of `x(z)` killed by `f`, together with its structure morphism to `Z`; this presheaf is an
algebraic space.

## Main definitions

* `AlgebraicGeometry.Stack.relativeAutomorphismTotalPresheaf`: the presheaf `Isom_{𝒳/𝒴}(x, x)` on
  the big fppf site of `S`, as the total presheaf of the presheaf of relative automorphisms.
* `AlgebraicGeometry.Stack.relativeAutomorphismSpaceOver`: that presheaf as an object of
  `CategoryTheory.Over Z`.

## Main results

* `AlgebraicGeometry.Stack.isAlgebraicSpace_elementsTotalPresheaf`: if the category of elements
  of a presheaf `F` on the category of elements of `Z`, viewed over the site, is equivalent to a
  category represented by an algebraic space, then `Σ_Z F` is an algebraic space.
* `AlgebraicGeometry.Stack.isAlgebraicSpace_relativeAutomorphismTotalPresheaf`:
  `Isom_{𝒳/𝒴}(x, x)`, read on the big fppf site, is an algebraic space over `S`, so
  `AlgebraicGeometry.Stack.relativeAutomorphismSpaceOver` is an algebraic space over `Z`.

## References

* [Stacks Project, Tag 02XV](https://stacks.math.columbia.edu/tag/02XV)
* [Stacks Project, Tag 04SV](https://stacks.math.columbia.edu/tag/04SV)
* [Stacks Project, Tag 06PP](https://stacks.math.columbia.edu/tag/06PP)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w v₁ w₁

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hZ : IsAlgebraicSpace B S hS Z)
variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}

/-- The total presheaf of a presheaf `F` on the category of elements of an algebraic space `Z` is
an algebraic space, as soon as the category of elements of `F`, viewed over the big fppf site
through the projection of the category of elements of `Z`, is equivalent over the site to a
category represented by an algebraic space. -/
theorem isAlgebraicSpace_elementsTotalPresheaf
    {D : Type w₁} [Category.{v₁} D] {q : D ⥤ BigFppfOver B S hS}
    (F : ((presheafOfCategories (Z ⋙ typeToCat)).obj)ᵒᵖ ⥤ Type u)
    (e : StacksRepresentableCFG.EquivalenceOver
      (PresheafOfCategories.discreteProjection F ⋙ (presheafOfCategories (Z ⋙ typeToCat)).p) q)
    (hq : ∃ G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u, IsAlgebraicSpace B S hS G ∧
      Nonempty (StacksRepresentableCFG.EquivalenceOver q
        (presheafOfCategories (G ⋙ typeToCat)).p)) :
    IsAlgebraicSpace B S hS (PresheafOfCategories.elementsTotalPresheaf Z F) := by
  obtain ⟨G, hG, ⟨eG⟩⟩ := hq
  obtain ⟨i⟩ := (PresheafOfCategories.nonempty_equivalenceOver_iff
    (PresheafOfCategories.elementsTotalPresheaf Z F) G).mp
    ⟨(PresheafOfCategories.totalElementsEquivalenceOver Z F).symm.trans (e.trans eG)⟩
  let e' (P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : P ⋙ uliftFunctor.{u, u} ≅ P :=
    Functor.isoWhiskerLeft P uliftFunctorTrivial ≪≫ Functor.rightUnitor P
  exact AlgebraicGeometry.isAlgebraicSpace_of_iso B S hS ((e' _).symm ≪≫ i ≪≫ e' G) hG

/-- `Isom_{𝒳/𝒴}(x, x)` as a presheaf on the big fppf site of `S`: the total presheaf of the
presheaf of relative automorphisms of `x`. Its sections over an object `W` of the site are the
pairs consisting of a point `z` of `Z` over `W` and a vertical automorphism of `x(z)` killed by
`f`, and the restriction maps are the restriction of relative automorphisms along a morphism of
the category of elements of `Z`. -/
noncomputable abbrev relativeAutomorphismTotalPresheaf (f : 𝒳 ⟶ 𝒴)
    (x : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) :
    (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  PresheafOfCategories.elementsTotalPresheaf Z (relativeAutomorphismPresheaf B S hS Z hZ f x)

/-- `Isom_{𝒳/𝒴}(x, x)` as an object over `Z`: the presheaf
`AlgebraicGeometry.Stack.relativeAutomorphismTotalPresheaf` together with its structure morphism
to `Z`, which reads off the point of `Z` that a relative automorphism sits over. -/
noncomputable abbrev relativeAutomorphismSpaceOver (f : 𝒳 ⟶ 𝒴)
    (x : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) : Over Z :=
  Over.mk (PresheafOfCategories.elementsTotalProj Z
    (relativeAutomorphismPresheaf B S hS Z hZ f x))

/-- The category of elements of the presheaf of relative automorphisms, viewed over the big fppf
site of `S`, is equivalent over that site to the 2-fibre product `Z ×_{x, 𝒳} ℐ_{𝒳/𝒴}`. -/
theorem nonempty_equivalenceOver_relativeAutomorphismPresheaf_site (f : 𝒳 ⟶ 𝒴)
    (x : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) :
    Nonempty (StacksRepresentableCFG.EquivalenceOver
      (PresheafOfCategories.discreteProjection (relativeAutomorphismPresheaf B S hS Z hZ f x) ⋙
        (algebraicSpaceStack.{u, w} B S hS Z hZ).val.val.p)
      (relativeAutomorphismSpaceOverSpace B S hS Z hZ f x).val.p) :=
  (RelativeAutomorphismSpace.nonempty_equivalenceOver_comparison B S hS Z hZ f x).map
    fun ec =>
      ((ec.compRight (algebraicSpaceStack.{u, w} B S hS Z hZ).val.val.p).symm.ofEq
        (relativeAutomorphismSpaceOverSpaceProj B S hS Z hZ f x).w).symm

/-- The presheaf `AlgebraicGeometry.Stack.relativeAutomorphismTotalPresheaf`, whose sections over
`W` are the pairs of a point `z` of `Z` over `W` and an automorphism of `x(z)` killed by `f`, is
an algebraic space over `S`. -/
@[stacks 06PP
  "part (1): Isom_{X/Y}(x, x) as a presheaf over Z on the big fppf site is an algebraic space"]
theorem isAlgebraicSpace_relativeAutomorphismTotalPresheaf (f : 𝒳 ⟶ 𝒴)
    (x : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) :
    IsAlgebraicSpace B S hS (relativeAutomorphismTotalPresheaf B S hS Z hZ f x) :=
  isAlgebraicSpace_elementsTotalPresheaf B S hS Z
    (relativeAutomorphismPresheaf B S hS Z hZ f x)
    (nonempty_equivalenceOver_relativeAutomorphismPresheaf_site B S hS Z hZ f x).some
    (isRepresentableByAlgebraicSpace_relativeAutomorphismSpaceOverSpace B S hS Z hZ f x)

/-- The presheaf underlying the object `AlgebraicGeometry.Stack.relativeAutomorphismSpaceOver` of
`CategoryTheory.Over Z` is an algebraic space. -/
theorem isAlgebraicSpace_relativeAutomorphismSpaceOver_left (f : 𝒳 ⟶ 𝒴)
    (x : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) :
    IsAlgebraicSpace B S hS (relativeAutomorphismSpaceOver B S hS Z hZ f x).left :=
  isAlgebraicSpace_relativeAutomorphismTotalPresheaf B S hS Z hZ f x

end AlgebraicGeometry.Stack

end
