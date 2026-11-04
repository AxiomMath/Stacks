module

public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleFpqcDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModulePullbackPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleAllPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleIso
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleLocusOpen

/-!
# Flatness of a module over a target descends along a flat covering of the source

Let `a i : X i ⟶ X` be flat morphisms of algebraic spaces over a scheme `S` of a big fppf site,
jointly surjective on points, let `f : X ⟶ Z` be a morphism and `F` a quasi-coherent
`𝒪_X`-module.  If the inverse image of `F` along each `a i` is flat over `Z` along `a i ≫ f`, then
`F` is flat over `Z` along `f`: flatness over `Z` is checked at points (Stacks 05VU), and at a
point in the image of `a i` it is read on the inverse image along the flat morphism `a i`
(Stacks 05VY).  The composition statement (Stacks 05VX) is
`AlgebraicGeometry.Space.isFlatOver_comp_of_isFlat` of
`StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleFpqcDescent`.

## Main results

* `AlgebraicGeometry.Space.isFlatOver_of_flat_covering`: **flatness of a quasi-coherent module
  over a target descends along a jointly surjective family of flat morphisms of the source.**

## References

* [Stacks Project, Tag 05VX](https://stacks.math.columbia.edu/tag/05VX)
* [Stacks Project, Tag 05VU](https://stacks.math.columbia.edu/tag/05VU)
* [Stacks Project, Tag 05VY](https://stacks.math.columbia.edu/tag/05VY)
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {X Y Z : AlgebraicSpaces B S hS}

/-- **Flatness of a quasi-coherent module over a target descends along a jointly surjective
family of flat morphisms of the source.**  If `a i : X i ⟶ X` are flat, jointly surjective on
points, and the inverse image of `F` along each `a i` is isomorphic to a module flat over `Z` along
`a i ≫ f`, then `F` is flat over `Z` along `f`.  This is Stacks 05VY at each point. -/
theorem isFlatOver_of_flat_covering {I : Type v} (Xi : I → AlgebraicSpaces B S hS)
    (a : ∀ i, Xi i ⟶ X) (f : X ⟶ Z) (F : Modules.{u, u} B S hS X.1 X.2)
    [hF : F.IsQuasicoherentOnSite] (ha : ∀ i, IsFlat B S hS (a i).hom)
    (hsurj : ∀ x : points B S hS X.1, ∃ i y, pointsMap B S hS (Xi i).1 (a i).hom y = x)
    (Fi : ∀ i, Modules.{u, u} B S hS (Xi i).1 (Xi i).2)
    (e : ∀ i, (modulePullback B S hS (a i)).obj F ≅ Fi i)
    (hFi : ∀ i, IsFlatOver B S hS (Xi i).2 (a i ≫ f).hom (Fi i)) :
    IsFlatOver B S hS X.2 f.hom F := by
  refine (isFlatOver_iff_forall_isFlatOverAtPoint B S hS f F hF).2 fun x => ?_
  obtain ⟨i, y, rfl⟩ := hsurj x
  refine (isFlatOverAtPoint_modulePullback_iff_of_isFlatAt B S hS (a i) f F y
    (isFlatAt_of_isFlat B S hS (a i).hom (ha i) y)).2 ?_
  have hflat := (isFlatOver_iff_of_iso B S hS (Xi i).2 (a i ≫ f).hom (e i)).2 (hFi i)
  exact (isFlatOver_iff_forall_isFlatOverAtPoint B S hS (a i ≫ f) _
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (a i) F hF)).1 hflat y

end AlgebraicGeometry.Space

end
