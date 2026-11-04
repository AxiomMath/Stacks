module

public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Pullback

/-!
# The free module sheaf commutes with inverse image, restriction and the constant sheaf

Let `(C, J)` be a site and `R` a ring. The free module sheaf functor
`Λ_{(-)} = CategoryTheory.Sheaf.composeAndSheafify J (ModuleCat.free R)` takes a sheaf of sets `G`
to the sheafification of the sectionwise free `R`-module on `G`. It is a left adjoint of the
functor taking a sheaf of modules to its underlying sheaf of sets, and the three isomorphisms
below say that it commutes with the three operations one performs on a sheaf of sets while
testing local constancy: inverse image along a continuous functor of sites, restriction to a
localized site, and formation of the constant sheaf.

## Main results

* `CategoryTheory.Sheaf.composeAndSheafifyFreeSheafPullbackIso`: `Λ_{π^{-1}G} ≅ π^{-1}Λ_G`,
  naturally in `G`, for `π` a continuous functor of sites whose pushforward has a left adjoint.
* `CategoryTheory.Sheaf.composeAndSheafifyFreeOverPullbackIso`: `Λ_{G|_V} ≅ (Λ_G)|_V`, naturally
  in `G`, for `V` an object of `C`.
* `CategoryTheory.Sheaf.constantSheafComposeAndSheafifyFreeIso`: the free module sheaf on the
  constant sheaf of sets at `S` is the constant sheaf of modules at the free `R`-module on `S`,
  for a site with a terminal object.

## Implementation notes

The first and the third are instances of the uniqueness of a left adjoint: both sides of each are
left adjoint to one and the same composite of the forgetful functor on sheaves of modules with,
respectively, the pushforward along `π` and the sections over the terminal object, the two orders
in which those are performed agreeing definitionally. This is the argument of
`Stacks.Cohomology.DerivedLowerShriek.freeAbelianSheafPullbackIso`, with the free–forget adjunction
`ModuleCat.adj` in place of `AddCommGrpCat.adj`.

The second is not of that form, restriction to `C / V` not being a left adjoint of anything the
free module sheaf functor interacts with; instead, taking the sectionwise free module commutes
with restriction definitionally, both being whiskerings, and what remains is that restriction
commutes with sheafification, which is Mathlib's
`CategoryTheory.Functor.pushforwardContinuousSheafificationCompatibility` — `Over.forget V` being
both continuous and cocontinuous for `J.over V` and `J`. That statement is universe polymorphic
and asks only that module-valued presheaves on `C / V` admit pointwise right Kan extensions along
`(Over.forget V).op`; for a site whose objects form a `Type (u + 1)` with `Category.{u}`, as a
small étale site does, instance search supplies those from the limits of `ModuleCat.{u + 1} R`.

This is the sheaves-of-modules form of the comparison; the abelian-sheaf form, for a small site,
is the same statement with `ModuleCat R` replaced by `AddCommGrpCat`.

## References

* [Stacks Project, Tag 03S8](https://stacks.math.columbia.edu/tag/03S8)
* [Stacks Project, Tag 00XK](https://stacks.math.columbia.edu/tag/00XK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v' v u' u

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (R : Type w) [Ring R]
  [HasWeakSheafify J (ModuleCat.{w} R)] [HasWeakSheafify J (Type w)]

/-- **The free module sheaf commutes with inverse image.** For a continuous functor `π` of sites
whose pushforward on sheaves of sets and on sheaves of modules both have left adjoints,
`Λ_{π^{-1}G} ≅ π^{-1}Λ_G`, naturally in the sheaf of sets `G`.

Both composites are left adjoint to the pushforward along `π` of the underlying sheaf of sets,
which does not depend on the order in which pushforward and forgetting are performed. -/
public def composeAndSheafifyFreeSheafPullbackIso {D : Type u'} [Category.{v'} D]
    (K : GrothendieckTopology D) (π : C ⥤ D) [π.IsContinuous J K]
    [HasWeakSheafify K (ModuleCat.{w} R)] [HasWeakSheafify K (Type w)]
    [(π.sheafPushforwardContinuous (ModuleCat.{w} R) J K).IsRightAdjoint]
    [(π.sheafPushforwardContinuous (Type w) J K).IsRightAdjoint] :
    composeAndSheafify J (ModuleCat.free R) ⋙ π.sheafPullback (ModuleCat.{w} R) J K ≅
      π.sheafPullback (Type w) J K ⋙ composeAndSheafify K (ModuleCat.free R) :=
  Adjunction.leftAdjointUniq
    ((adjunction J (ModuleCat.adj R)).comp (π.sheafAdjunctionContinuous (ModuleCat.{w} R) J K))
    ((π.sheafAdjunctionContinuous (Type w) J K).comp (adjunction K (ModuleCat.adj R)))

/-- **The free module sheaf commutes with restriction to a localized site.** For an object `V` of
`C`, `Λ_{G|_V} ≅ (Λ_G)|_V`, naturally in the sheaf of sets `G`.

Restriction to `C / V` is precomposition with `(Over.forget V).op`, and so commutes with the
sectionwise free module definitionally; that it commutes with sheafification is
`CategoryTheory.Functor.pushforwardContinuousSheafificationCompatibility`, `Over.forget V` being
continuous and cocontinuous. -/
public def composeAndSheafifyFreeOverPullbackIso (V : C)
    [HasWeakSheafify (J.over V) (ModuleCat.{w} R)] [HasWeakSheafify (J.over V) (Type w)]
    [∀ F : (Over V)ᵒᵖ ⥤ ModuleCat.{w} R, (Over.forget V).op.HasPointwiseRightKanExtension F] :
    composeAndSheafify J (ModuleCat.free R) ⋙ J.overPullback (ModuleCat.{w} R) V ≅
      J.overPullback (Type w) V ⋙ composeAndSheafify (J.over V) (ModuleCat.free R) :=
  (Functor.isoWhiskerLeft
    (sheafToPresheaf J (Type w) ⋙
      (Functor.whiskeringRight Cᵒᵖ (Type w) (ModuleCat.{w} R)).obj (ModuleCat.free R))
    ((Over.forget V).pushforwardContinuousSheafificationCompatibility
      (ModuleCat.{w} R) (J.over V) J)).symm

/-- **The free module sheaf on a constant sheaf of sets is constant.** On a site with a terminal
object `T`, the free module sheaf on the constant sheaf of sets at `S` is the constant sheaf of
modules at the free `R`-module on `S`, naturally in `S`.

Both composites are left adjoint to the `R`-module of sections over `T` of a sheaf of modules,
read either as the sections of the underlying sheaf of sets or as the underlying set of the
sections. -/
public def constantSheafComposeAndSheafifyFreeIso {T : C} (hT : IsTerminal T) :
    constantSheaf J (Type w) ⋙ composeAndSheafify J (ModuleCat.free R) ≅
      ModuleCat.free R ⋙ constantSheaf J (ModuleCat.{w} R) :=
  Adjunction.leftAdjointUniq
    ((constantSheafAdj J (Type w) hT).comp (adjunction J (ModuleCat.adj R)))
    ((ModuleCat.adj R).comp (constantSheafAdj J (ModuleCat.{w} R) hT))

end CategoryTheory.Sheaf

end
