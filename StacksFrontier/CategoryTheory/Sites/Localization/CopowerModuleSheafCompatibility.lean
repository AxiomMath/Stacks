module

public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Pullback
public import StacksFrontier.Algebra.Category.ModuleCat.Copower

/-!
# The copower module sheaf commutes with inverse image, restriction and the constant sheaf

Let `(C, J)` be a site, `R` a ring and `M` a module over it. The copower module sheaf functor
`M_{(-)} = CategoryTheory.Sheaf.composeAndSheafify J (ModuleCat.copower M)` takes a sheaf of sets
`G` to the sheafification of the sectionwise copower `⨁_{G} M`. It is a left adjoint, of the
functor taking a sheaf of modules to its sheaf of morphisms out of `M`, and the three
isomorphisms below say that it commutes with the three operations one performs on a sheaf of sets
while testing local constancy: inverse image along a continuous functor of sites, restriction to
a localized site, and formation of the constant sheaf.

This is `StacksFrontier.CategoryTheory.Sites.Localization.FreeModuleSheafCompatibility` with
`ModuleCat.free R` replaced by `ModuleCat.copower M`. The difference is the universe of the ring:
`ModuleCat.free R : Type r ⥤ ModuleCat.{r} R` forces the ring into the module universe, whereas
`ModuleCat.copower M : Type w ⥤ ModuleCat.{w} R` leaves it free. At
`M = ModuleCat.of R (ULift.{w} R)` the two functors agree up to isomorphism when both are
defined, and only the second is defined when the ring is in a smaller universe than the modules.

## Main results

* `CategoryTheory.Sheaf.composeAndSheafifyModuleCopowerSheafPullbackIso`:
  `M_{π^{-1}G} ≅ π^{-1}M_G`, naturally in `G`, for `π` a continuous functor of sites whose
  pushforward has a left adjoint.
* `CategoryTheory.Sheaf.composeAndSheafifyModuleCopowerOverPullbackIso`: `M_{G|_V} ≅ (M_G)|_V`,
  naturally in `G`, for `V` an object of `C`.
* `CategoryTheory.Sheaf.constantSheafComposeAndSheafifyModuleCopowerIso`: the copower module
  sheaf on the constant sheaf of sets at `S` is the constant sheaf of modules at the copower of
  `M` by `S`, for a site with a terminal object.

## Implementation notes

The first and the third are instances of the uniqueness of a left adjoint, exactly as their
`ModuleCat.free` counterparts are: both sides of each are left adjoint to one and the same
composite of `CategoryTheory.coyoneda.obj (op M)` on sheaves with, respectively, the pushforward
along `π` and the sections over the terminal object, the two orders in which those are performed
agreeing definitionally.

The second is not of that form, restriction to `C / V` not being a left adjoint of anything the
copower module sheaf functor interacts with; instead, taking the sectionwise copower commutes
with restriction definitionally, both being whiskerings, and what remains is that restriction
commutes with sheafification, which is Mathlib's
`CategoryTheory.Functor.pushforwardContinuousSheafificationCompatibility`.

The `CategoryTheory.Functor.IsRightAdjoint` instance for `CategoryTheory.coyoneda.obj (op M)` is
`ModuleCat.coyonedaObj_isRightAdjoint`, declared a local instance so that
`CategoryTheory.GrothendieckTopology.HasSheafCompose` is available for
`CategoryTheory.Sheaf.adjunction`.

## References

* [Stacks Project, Tag 03S8](https://stacks.math.columbia.edu/tag/03S8)
* [Stacks Project, Tag 00XK](https://stacks.math.columbia.edu/tag/00XK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v' v u' u r

attribute [local instance] ModuleCat.coyonedaObj_isRightAdjoint

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) {R : Type r} [Ring R]
  (M : ModuleCat.{w} R) [HasWeakSheafify J (ModuleCat.{w} R)] [HasWeakSheafify J (Type w)]

/-- **The copower module sheaf commutes with inverse image.** For a continuous functor `π` of
sites whose pushforward on sheaves of sets and on sheaves of modules both have left adjoints,
`M_{π^{-1}G} ≅ π^{-1}M_G`, naturally in the sheaf of sets `G`.

Both composites are left adjoint to the pushforward along `π` of the sheaf of morphisms out of
`M`, which does not depend on the order in which pushforward and that passage are performed. -/
public def composeAndSheafifyModuleCopowerSheafPullbackIso {D : Type u'} [Category.{v'} D]
    (K : GrothendieckTopology D) (π : C ⥤ D) [π.IsContinuous J K]
    [HasWeakSheafify K (ModuleCat.{w} R)] [HasWeakSheafify K (Type w)]
    [(π.sheafPushforwardContinuous (ModuleCat.{w} R) J K).IsRightAdjoint]
    [(π.sheafPushforwardContinuous (Type w) J K).IsRightAdjoint] :
    composeAndSheafify J (ModuleCat.copower M) ⋙ π.sheafPullback (ModuleCat.{w} R) J K ≅
      π.sheafPullback (Type w) J K ⋙ composeAndSheafify K (ModuleCat.copower M) :=
  Adjunction.leftAdjointUniq
    ((adjunction J (ModuleCat.copowerAdj M)).comp
      (π.sheafAdjunctionContinuous (ModuleCat.{w} R) J K))
    ((π.sheafAdjunctionContinuous (Type w) J K).comp (adjunction K (ModuleCat.copowerAdj M)))

/-- **The copower module sheaf commutes with restriction to a localized site.** For an object `V`
of `C`, `M_{G|_V} ≅ (M_G)|_V`, naturally in the sheaf of sets `G`. -/
public def composeAndSheafifyModuleCopowerOverPullbackIso (V : C)
    [HasWeakSheafify (J.over V) (ModuleCat.{w} R)] [HasWeakSheafify (J.over V) (Type w)]
    [∀ F : (Over V)ᵒᵖ ⥤ ModuleCat.{w} R, (Over.forget V).op.HasPointwiseRightKanExtension F] :
    composeAndSheafify J (ModuleCat.copower M) ⋙ J.overPullback (ModuleCat.{w} R) V ≅
      J.overPullback (Type w) V ⋙ composeAndSheafify (J.over V) (ModuleCat.copower M) :=
  (Functor.isoWhiskerLeft
    (sheafToPresheaf J (Type w) ⋙
      (Functor.whiskeringRight Cᵒᵖ (Type w) (ModuleCat.{w} R)).obj (ModuleCat.copower M))
    ((Over.forget V).pushforwardContinuousSheafificationCompatibility
      (ModuleCat.{w} R) (J.over V) J)).symm

/-- **The copower module sheaf on a constant sheaf of sets is constant.** On a site with a
terminal object `T`, the copower module sheaf by `M` on the constant sheaf of sets at `S` is the
constant sheaf of modules at the copower of `M` by `S`, naturally in `S`.

Both composites are left adjoint to the morphisms from `M` into the sections over `T`. -/
public def constantSheafComposeAndSheafifyModuleCopowerIso {T : C} (hT : IsTerminal T) :
    constantSheaf J (Type w) ⋙ composeAndSheafify J (ModuleCat.copower M) ≅
      ModuleCat.copower M ⋙ constantSheaf J (ModuleCat.{w} R) :=
  Adjunction.leftAdjointUniq
    ((constantSheafAdj J (Type w) hT).comp (adjunction J (ModuleCat.copowerAdj M)))
    ((ModuleCat.copowerAdj M).comp (constantSheafAdj J (ModuleCat.{w} R) hT))

end CategoryTheory.Sheaf

end
