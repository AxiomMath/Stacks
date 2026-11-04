module

public import StacksFrontier.AlgebraicGeometry.Stacks.VersalChartSmoothBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsiteSheafPushforwardBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsitePushforwardFormula
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsiteDerivedPushforwardBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStackTerminalSubsite
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStackLisseSubsiteQuasiCompact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SlicePresentationRestriction
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.DerivedFlatFppfRestriction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.RestrictionPreservesInjectivesEssentiallySmall

/-!
# Local presentations at an object and global presentations of the pullback

Let `y` be a flat (resp. smooth) object of an algebraic stack `𝒳` over the scheme `U`, and let
`f'_y` be the restriction of the 1-morphism `y : (Sch/U) → 𝒳` to the flat-fppf (resp.
lisse-étale) sites (Stacks 07AT). If a sheaf of modules `H` on the flat-fppf (resp. lisse-étale)
site of `𝒳` has a global presentation over `y` (the clause of Stacks 03DL (6)), then its
restriction along `f'_y` has a global presentation (Stacks 03DE (6)) on the flat-fppf (resp.
lisse-étale) site of `(Sch/U)`. This is the step of the proof of Stacks 07B3 which recalls that the
pullback `f_i^{-1}` "is" the restriction to `𝒳/f_i` (Stacks 06W1): the site of `(Sch/U)` has the
terminal object `U/U`, carried to an object with an arrow to `y` (the chosen cartesian arrow of
the 2-Yoneda lemma), so `f'_y` factors through the slice at `y`
(`Stacks.SheafOfModules.isPresentedByGlobalSections_pushforward_of_isTerminal`).

The restriction is taken along any isomorphism of structure sheaves; the statement does not depend
on that choice.

## Main results

* `AlgebraicGeometry.Stack.FlatFppf.isPresentedByGlobalSections_pushforward_primedSiteFunctor`.
* `AlgebraicGeometry.Stack.LisseEtale.isPresentedByGlobalSections_pushforward_primedSiteFunctor`.

## References

* [Stacks Project, Tag 07B3](https://stacks.math.columbia.edu/tag/07B3)
* [Stacks Project, Tag 06W1](https://stacks.math.columbia.edu/tag/06W1)
* [Stacks Project, Tag 07AT](https://stacks.math.columbia.edu/tag/07AT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Stack

/-- On the slice over an object `y` with `Over y` essentially small, sheafification of abelian
presheaves exists and inverts exactly the locally bijective morphisms. -/
private theorem hasSheafify_and_wEqualsLocallyBijective_over {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) (y : C) [EssentiallySmall.{u} (Over y)] :
    HasSheafify (J.over y) AddCommGrpCat.{u} ∧
      (J.over y).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  ⟨hasSheafifyEssentiallySmallSite.{u, u, u + 1, u + 1, u} _ _,
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u, u + 1, u + 1, u} _⟩

namespace FlatFppf

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : AlgebraicStacks.{u, w} B S hS) (y : FlatFppf B S hS 𝒳)

/-- The image under `f'_y` of the terminal object `U/U` of the flat-fppf site of `(Sch/U)` maps to
`y`, by the chosen cartesian arrow of the 2-Yoneda lemma. -/
def primedSiteFunctorTerminalHom :
    (primedSiteFunctor B S hS (objectStackMap B S hS 𝒳 y.obj) y.property).obj
      ⟨Over.mk (𝟙 (𝒳.val.val.p.obj y.obj)), flatObject_schemeStack_id.{u, w} B S hS _⟩ ⟶ y :=
  ObjectProperty.homMk (Functor.TwoYoneda.chosenLift 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
    (𝒳.val.val.p.obj y.obj) (Functor.Fiber.mk (a := y.obj) rfl) (Over.mk (𝟙 _))).φ

/-- `f'_y` is continuous (Stacks 07AT (2)), as a local instance. -/
local instance isContinuous_primedSiteFunctor_objectStackMap :
    (primedSiteFunctor B S hS (objectStackMap B S hS 𝒳 y.obj) y.property).IsContinuous
      (topology B S hS (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj y.obj))) (topology B S hS 𝒳) :=
  isContinuous_subsiteFunctor_topology B S hS (objectStackMap B S hS 𝒳 y.obj) y.property

/-- **A presentation at a flat object `y` is a global presentation after restriction along
`f'_y`.** For `H` a module on the flat-fppf site of `𝒳` with a global presentation over `y`, and
any isomorphism `χ` of the structure sheaf of the flat-fppf site of `(Sch/U)` with the restriction
of that of `𝒳`, the restriction of `H` along `f'_y` (the restriction of `y : (Sch/U) → 𝒳` to the
flat-fppf sites) has a global presentation at the universe of the sections. -/
theorem isPresentedByGlobalSections_pushforward_primedSiteFunctor
    {R : Sheaf (topology B S hS 𝒳) RingCat.{u}}
    {R' : Sheaf (topology B S hS (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj y.obj))) RingCat.{u}}
    (χ : R' ⟶ ((primedSiteFunctor B S hS (objectStackMap B S hS 𝒳 y.obj)
      y.property).sheafPushforwardContinuous RingCat.{u}
        (topology B S hS (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj y.obj)))
        (topology B S hS 𝒳)).obj R) [IsIso χ]
    {H : SheafOfModules.{u} R} (hH : (H.over y).HasGlobalPresentation) :
    ((SheafOfModules.pushforward.{u} χ).obj H).IsPresentedByGlobalSections := by
  have := isCocontinuous_subsiteFunctor_topology B S hS (objectStackMap B S hS 𝒳 y.obj)
    y.property
  have := hasSheafify_addCommGrpCat B S hS (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj y.obj))
  have := wEqualsLocallyBijective_addCommGrpCat B S hS
    (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj y.obj))
  have : EssentiallySmall.{u} (Over y) :=
    Stacks.Sites.ExtensionByZero.OfEssentiallySmall.essentiallySmall_over y
  obtain ⟨_, _⟩ := hasSheafify_and_wEqualsLocallyBijective_over (topology B S hS 𝒳) y
  exact Stacks.SheafOfModules.isPresentedByGlobalSections_pushforward_of_isTerminal R
    (isTerminalFlatObjectSchemeStackId.{u, w} B S hS (𝒳.val.val.p.obj y.obj))
    (primedSiteFunctor B S hS (objectStackMap B S hS 𝒳 y.obj) y.property) y
    (primedSiteFunctorTerminalHom B S hS 𝒳 y) χ hH

end FlatFppf

namespace LisseEtale

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : AlgebraicStacks.{u, w} B S hS) (y : LisseEtale.{u, w} B S hS 𝒳)

/-- The image under `f'_y` of the terminal object `U/U` of the lisse-étale site of `(Sch/U)` maps
to `y`, by the chosen cartesian arrow of the 2-Yoneda lemma. -/
def primedSiteFunctorTerminalHom :
    (primedSiteFunctor.{u, w} B S hS (objectStackMap B S hS 𝒳 y.obj) y.property).obj
      ⟨Over.mk (𝟙 (𝒳.val.val.p.obj y.obj)), smoothObject_schemeStack_id.{u, w} B S hS _⟩ ⟶ y :=
  ObjectProperty.homMk (Functor.TwoYoneda.chosenLift 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
    (𝒳.val.val.p.obj y.obj) (Functor.Fiber.mk (a := y.obj) rfl) (Over.mk (𝟙 _))).φ

/-- `f'_y` is continuous (Stacks 07AT (1)), as a local instance. -/
local instance isContinuous_primedSiteFunctor_objectStackMap :
    (primedSiteFunctor.{u, w} B S hS (objectStackMap B S hS 𝒳 y.obj) y.property).IsContinuous
      (inclusionTopology.{u, w} B S hS (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj y.obj)))
      (inclusionTopology.{u, w} B S hS 𝒳) :=
  isContinuous_subsiteFunctor.{u, w} B S hS (objectStackMap B S hS 𝒳 y.obj) y.property

/-- **A presentation at a smooth object `y` is a global presentation after restriction along
`f'_y`.** For `H` a module on the lisse-étale site of `𝒳` with a global presentation over `y`,
and any isomorphism `χ` of the structure sheaf of the lisse-étale site of `(Sch/U)` with the
restriction of that of `𝒳`, the restriction of `H` along `f'_y` has a global presentation at the
universe of the sections. -/
theorem isPresentedByGlobalSections_pushforward_primedSiteFunctor
    {R : Sheaf (inclusionTopology.{u, w} B S hS 𝒳) RingCat.{u}}
    {R' : Sheaf (inclusionTopology.{u, w} B S hS (schemeStack.{u, w} B S hS
      (𝒳.val.val.p.obj y.obj))) RingCat.{u}}
    (χ : R' ⟶ ((primedSiteFunctor.{u, w} B S hS (objectStackMap B S hS 𝒳 y.obj)
      y.property).sheafPushforwardContinuous RingCat.{u}
        (inclusionTopology.{u, w} B S hS (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj y.obj)))
        (inclusionTopology.{u, w} B S hS 𝒳)).obj R) [IsIso χ]
    {H : SheafOfModules.{u} R} (hH : (H.over y).HasGlobalPresentation) :
    ((SheafOfModules.pushforward.{u} χ).obj H).IsPresentedByGlobalSections := by
  have := isCocontinuous_subsiteFunctor.{u, w} B S hS (objectStackMap B S hS 𝒳 y.obj)
    y.property
  have := hasSheafify_inclusionTopology B S hS
    (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj y.obj))
  have := wEqualsLocallyBijective_inclusionTopology B S hS
    (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj y.obj))
  have : EssentiallySmall.{u} (Over y) :=
    Stacks.Sites.ExtensionByZero.OfEssentiallySmall.essentiallySmall_over y
  obtain ⟨_, _⟩ := hasSheafify_and_wEqualsLocallyBijective_over
    (inclusionTopology.{u, w} B S hS 𝒳) y
  exact Stacks.SheafOfModules.isPresentedByGlobalSections_pushforward_of_isTerminal R
    (isTerminalSmoothObjectSchemeStackId.{u, w} B S hS (𝒳.val.val.p.obj y.obj))
    (primedSiteFunctor.{u, w} B S hS (objectStackMap B S hS 𝒳 y.obj) y.property) y
    (primedSiteFunctorTerminalHom B S hS 𝒳 y) χ hH

end LisseEtale

end AlgebraicGeometry.Stack
