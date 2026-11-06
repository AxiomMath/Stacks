module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import StacksFrontier.AlgebraicGeometry.Stacks.AutomorphismGroupAtPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.Gerbe
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStack

/-!
# Gerbes over a scheme, and gerbes over a scheme with a given group

Let `𝒳` be an algebraic stack over a scheme `S` of a big fppf site. Section 06RB of the Stacks
project speaks of an algebraic stack which *is a gerbe over a scheme*, and of one which is a gerbe
over a scheme *with group* `G`, for a group scheme `G` (Example 06RE: the strata of `[U/𝐆_m]` are
gerbes over schemes with groups `μ_{p^i}` and `𝐆_m`). This module records the two notions.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.IsGerbeOverScheme`: there are an object `T` of the
  site and a 1-morphism `𝒳 ⟶ (Sch/T)_fppf` making `𝒳` a gerbe over `(Sch/T)_fppf` in the sense of
  Stacks 06QC.
* `AlgebraicGeometry.Stack.AlgebraicStacks.baseOver`: the base `T_x ⟶ S` of an object `x` of `𝒳`,
  as an object of the slice over `S`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.IsGerbeOverSchemeWithGroup`: `𝒳` is a gerbe over a
  scheme, and its automorphism groups are banded by the group scheme `G` over `S`: there is a
  family of group isomorphisms from the automorphism group of every object `x` (the automorphisms
  lying over the identity of `T_x`, Stacks 0DTW) to the group of sections of `G` over `T_x`,
  natural with respect to every morphism of `𝒳`.

## Implementation notes

The band is a family of isomorphisms indexed by all objects of `𝒳`, and its naturality is asked
for along every morphism `f : x ⟶ y` of `𝒳`, not only along morphisms of a fibre: whenever two
automorphisms `a` of `x` and `b` of `y` are intertwined by `f`, the section of `G` attached to `a`
is the restriction along the base morphism of `f` of the section attached to `b`. For `f` a
pullback morphism this is compatibility with restriction, and for `f` an automorphism it is
compatibility with conjugation. So the condition says that the inertia of `𝒳` is the pullback of
`G`, as a sheaf of groups, which is what "with group `G`" means.

## References

* [Stacks Project, Section 06RB](https://stacks.math.columbia.edu/tag/06RB)
* [Stacks Project, Tag 06QC](https://stacks.math.columbia.edu/tag/06QC)
* [Stacks Project, Tag 06RE](https://stacks.math.columbia.edu/tag/06RE)
-/

@[expose] public section

open CategoryTheory
open scoped MonObj

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An algebraic stack over `S` *is a gerbe over a scheme* when there are an object `T` of the
big fppf site of `S` and a 1-morphism `𝒳 ⟶ (Sch/T)_fppf` making `𝒳` a gerbe over
`(Sch/T)_fppf` in the sense of Stacks 06QC. -/
def IsGerbeOverScheme (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS) : Prop :=
  ∃ (T : BigFppfOver B S hS) (f : 𝒳 ⟶ schemeStack.{u, w} B S hS T), IsGerbeOver B S hS f

variable {B S hS}

/-- The base `T_x ⟶ S` of an object `x` of an algebraic stack over `S`, as a scheme over `S`. -/
abbrev baseOver {𝒳 : Stack.AlgebraicStacks.{u, w} B S hS} (x : 𝒳.val.val.obj) : Over S :=
  Over.mk (𝒳.val.val.p.obj x).hom.hom

variable (B S hS) in
/-- An algebraic stack `𝒳` over `S` is a *gerbe over a scheme with group* `G`, a group scheme
over `S`, when it is a gerbe over a scheme and its automorphism groups are banded by `G`: for
every object `x` the group of automorphisms of `x` lying over the identity of its base `T_x` is
isomorphic to the group of sections of `G` over `T_x`, and these isomorphisms are natural along
every morphism of `𝒳`: if `f : x ⟶ y` intertwines an automorphism `a` of `x` with an automorphism
`b` of `y`, then the section attached to `a` is the restriction along the base of `f` of the
section attached to `b`. -/
def IsGerbeOverSchemeWithGroup (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS) (G : Over S)
    [GrpObj G] : Prop :=
  IsGerbeOverScheme B S hS 𝒳 ∧
    ∃ band : ∀ x : 𝒳.val.val.obj, 𝒳.val.val.p.verticalAut x ≃* (baseOver x ⟶ G),
      ∀ (x y : 𝒳.val.val.obj) (f : x ⟶ y) (a : 𝒳.val.val.p.verticalAut x)
        (b : 𝒳.val.val.p.verticalAut y),
        (a : Aut x).asIso.hom ≫ f = f ≫ (b : Aut y).asIso.hom →
          (band x a).left = (𝒳.val.val.p.map f).left.hom ≫ (band y b).left

end AlgebraicGeometry.Stack.AlgebraicStacks

end
