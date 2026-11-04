module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import StacksFrontier.AlgebraicGeometry.Spaces.RingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules

/-!
# Cohomology on the small étale site of an algebraic space

Cohomology of an algebraic space `X` over `S` is the cohomology of the small étale site of
`X` with its structure sheaf, as constructed for an arbitrary site in Stacks 071H.  Two
pieces of that construction are specific to the small étale site and are collected here:
abelian sheaves on it have enough injectives, so right-derived functors out of it exist; and
when the base is the spectrum of a ring `A`, the structure morphism makes every cohomology
module an `A`-module.

## Main definitions

* `AlgebraicGeometry.Space.baseRingHom` is the canonical ring map from `A` to the ring of
  global functions on the small étale site of an algebraic space over `Spec A`: a scalar `a`
  is sent to the family of its pullbacks along the structure morphisms of the étale charts.
* `AlgebraicGeometry.Space.cohomologyOverBase` is cohomology on the small étale ringed site,
  with scalars restricted to `A` along `AlgebraicGeometry.Space.baseRingHom`.

## Main results

* `AlgebraicGeometry.Space.smallEtaleAbelianSheaf_enoughInjectives`: sheaves of abelian
  groups on the small étale site of a presheaf on the big fppf site over `S` have enough
  injectives.

## Implementation notes

Enough injectives comes from the site being essentially small, which
`AlgebraicGeometry.Space.SmallEtale.instEssentiallySmall` supplies and which needs neither
the sheaf condition nor an atlas; the instance is therefore stated for an arbitrary presheaf
on the big fppf category over `S`, as is
`AlgebraicGeometry.Space.smallEtaleRingedSite_hasWeakSheafify_over`.  The abelian sheaves
are valued in `Ab.{u + 1}`, the universe in which the small étale site of a `Scheme.{u}` is
a site.

`AlgebraicGeometry.Space.baseRingHom` is a map into
`Stacks.Cohomology.SiteModules.GlobalSectionRing`, the ring of compatible families of
sections of the structure sheaf, rather than into the sections over a terminal object: the
small étale site has no terminal object, and Stacks 071H is phrased for the whole site.  Its
compatibility condition is the statement that pulling a scalar back along a chart and then
restricting along a chart morphism agrees with pulling it back along the composite chart,
which is `Over.w` of that chart morphism transported through the inclusion of the big fppf
site.

The module universe of `AlgebraicGeometry.Space.cohomologyOverBase` is enlarged to
`max (u + 1) w` because `Stacks.Cohomology.SiteModules.globalModuleCohomology` is the derived
functor of global sections on sheaves of modules whose sections live in a universe containing
the site, and `AlgebraicGeometry.Space.Modules` leaves that universe free.

## References

* [Stacks Project, Tag 071H](https://stacks.math.columbia.edu/tag/071H)
* [Stacks Project, Tag 08AS](https://stacks.math.columbia.edu/tag/08AS)
* [Stacks Project, Tag 0A4K](https://stacks.math.columbia.edu/tag/0A4K)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.Space

/-- Sheaves of abelian groups on the small étale site of a presheaf on the big fppf category
over `S` have enough injectives: the site is essentially small, so its category of abelian
sheaves is a Grothendieck abelian category. -/
instance smallEtaleAbelianSheaf_enoughInjectives (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    EnoughInjectives (Sheaf (SmallEtale.topology B S hS F) Ab.{u + 1}) := by
  let : EssentiallySmall.{u + 1} (SmallEtale B S hS F) := inferInstance
  let : IsGrothendieckAbelian.{u + 1}
      (Sheaf (SmallEtale.topology B S hS F) Ab.{u + 1}) :=
    Sheaf.isGrothendieckAbelian_of_essentiallySmall
      (SmallEtale.topology B S hS F) Ab.{u + 1}
  exact IsGrothendieckAbelian.enoughInjectives

variable (A : Type u) [CommRing A] (B : BigFppfSite.{u})
    (hA : B.Contains (Spec (.of A)))
    (X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of A)) hA X)

/-- The canonical action of the base ring on global functions of an algebraic space over
`Spec A`: a scalar is sent to the family of its pullbacks along the structure morphisms of
the étale charts, which is compatible with restriction because each chart morphism is a
morphism over `Spec A`. -/
def baseRingHom :
    A →+* Stacks.Cohomology.SiteModules.GlobalSectionRing
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O)) where
  toFun a := ⟨(fun U =>
    (((Scheme.ΓSpecIso (.of A)).inv ≫
      Scheme.Γ.map ((B.inclusion.map
        ((SmallEtale.toOver B (Spec (.of A)) hA X).obj U.unop).hom).op)).hom a)),
    by
      intro U V g
      let T := SmallEtale.toOver B (Spec (.of A)) hA X
      have hw :
          B.inclusion.map (T.map g.unop).left ≫
              B.inclusion.map (T.obj U.unop).hom =
            B.inclusion.map (T.obj V.unop).hom := by
        simpa only [← Functor.map_comp] using
          congrArg B.inclusion.map (Over.w (T.map g.unop))
      change (((Scheme.ΓSpecIso (.of A)).inv ≫
        (B.inclusion.map (T.obj U.unop).hom).appTop ≫
        (B.inclusion.map (T.map g.unop).left).appTop).hom a) =
        (((Scheme.ΓSpecIso (.of A)).inv ≫
          (B.inclusion.map (T.obj V.unop).hom).appTop).hom a)
      rw [← Scheme.Hom.comp_appTop, hw]⟩
  map_one' := Subtype.ext <| funext fun _ => RingHom.map_one _
  map_mul' a b := Subtype.ext <| funext fun _ => RingHom.map_mul _ a b
  map_zero' := Subtype.ext <| funext fun _ => RingHom.map_zero _
  map_add' a b := Subtype.ext <| funext fun _ => RingHom.map_add _ a b

/-- Cohomology of an `𝒪_X`-module on the small étale ringed site of an algebraic space over
`Spec A`, regarded as an `A`-module along `AlgebraicGeometry.Space.baseRingHom`. -/
abbrev cohomologyOverBase (M : Modules.{u, max (u + 1) w} B (Spec (.of A)) hA X hX) (i : ℕ) :
    ModuleCat.{max (u + 1) w} A :=
  (ModuleCat.restrictScalars (baseRingHom A B hA X hX)).obj
    ((Stacks.Cohomology.SiteModules.globalModuleCohomology.{u + 1, u, u, max (u + 1) w}
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O)) i).obj M)

end AlgebraicGeometry.Space

end
