module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupActions
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleSite
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# Points of a group algebraic space with values in an object of the site

Let `G` be a group algebraic space over the final algebraic space of the big fppf site of a
scheme `S`. For an object `T` of the site, the `T`-points of `G` are the morphisms over the final
algebraic space from the presheaf represented by `T` to `G`. They form a group, by Mathlib's group
structure on the morphisms into a group object of a cartesian monoidal category, and pulling back
along a morphism `T' ⟶ T` of the site is a group homomorphism.

## Main definitions

* `AlgebraicGeometry.Space.GroupAlgebraicSpace.toBase`: the structure morphism of the presheaf
  represented by `T` to the final algebraic space.
* `AlgebraicGeometry.Space.GroupAlgebraicSpace.SitePoint`: the group of `T`-points of `G`.
* `AlgebraicGeometry.Space.GroupAlgebraicSpace.SitePoint.pullback`: pullback of points along a
  morphism of the site, as a group homomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Space.GroupAlgebraicSpace

variable {𝒞 : BigFppfSite.{u}} {S : Scheme.{u}} {hS : 𝒞.Contains S}
  (G : GroupAlgebraicSpace 𝒞 S hS (terminalSpace 𝒞 S hS).obj (terminalSpace 𝒞 S hS).property)

/-- The structure morphism of the presheaf represented by an object `T` of the site to the final
algebraic space. -/
abbrev toBase (T : BigFppfOver 𝒞 S hS) : yoneda.obj T ⟶ (terminalSpace 𝒞 S hS).obj :=
  (baseTerminal_yonedaIsTerminal 𝒞 S hS).from _

/-- The `T`-points of a group algebraic space `G` over the final algebraic space: the morphisms
over the final algebraic space from the presheaf represented by `T` to `G`. -/
abbrev SitePoint (T : BigFppfOver 𝒞 S hS) : Type (u + 1) :=
  Over.mk (toBase T) ⟶ G.obj.X

/-- The `T`-points of a group algebraic space form a group. -/
instance (T : BigFppfOver 𝒞 S hS) : Group (G.SitePoint T) := Hom.group

/-- The morphism of presheaves over the final algebraic space induced by a morphism of the
site. -/
abbrev toBaseHom {T T' : BigFppfOver 𝒞 S hS} (m : T' ⟶ T) :
    Over.mk (toBase T') ⟶ Over.mk (toBase T) :=
  Over.homMk (yoneda.map m) ((baseTerminal_yonedaIsTerminal 𝒞 S hS).hom_ext _ _)

/-- **Pullback of points along a morphism of the site** is a group homomorphism: it is
precomposition with the induced morphism of represented presheaves. -/
def SitePoint.pullback {T T' : BigFppfOver 𝒞 S hS} (m : T' ⟶ T) :
    G.SitePoint T →* G.SitePoint T' where
  toFun g := toBaseHom m ≫ g
  map_one' := MonObj.comp_one _
  map_mul' _ _ := MonObj.comp_mul _ _ _

/-- Pullback of points is precomposition with the induced morphism of represented presheaves. -/
theorem SitePoint.pullback_apply {T T' : BigFppfOver 𝒞 S hS} (m : T' ⟶ T) (g : G.SitePoint T) :
    SitePoint.pullback G m g = toBaseHom m ≫ g :=
  rfl

/-- Pullback of points along an identity is the identity. -/
@[simp]
theorem SitePoint.pullback_id {T : BigFppfOver 𝒞 S hS} (g : G.SitePoint T) :
    SitePoint.pullback G (𝟙 T) g = g := by
  rw [pullback_apply]
  convert Category.id_comp g
  ext1
  exact yoneda.map_id T

/-- Pullback of points along a composite is the composite of the pullbacks. -/
theorem SitePoint.pullback_comp {T T' T'' : BigFppfOver 𝒞 S hS} (m : T' ⟶ T) (m' : T'' ⟶ T')
    (g : G.SitePoint T) :
    SitePoint.pullback G (m' ≫ m) g = SitePoint.pullback G m' (SitePoint.pullback G m g) := by
  simp only [pullback_apply, ← Category.assoc]
  congr 1

end AlgebraicGeometry.Space.GroupAlgebraicSpace

end
