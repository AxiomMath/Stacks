module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackEssentiallySmall
public import StacksFrontier.CategoryTheory.FiberedCategory.ProductProjection
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.RingedToposOfAFibredCategory
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.SimplicialModulesAbelian
import StacksCore.Tactic.StacksAttribute

/-!
# Lower shriek on simplicial modules over a constant simplicial sheaf of rings

Let `C` be a site, let `O` be a sheaf of rings on `C` and let `π : Δ × C ⥤ C` be the projection.
A simplicial module over the constant simplicial sheaf of rings on `O` is a sheaf of modules over
`π^{-1}O` on `Δ × C`, and this file constructs the two functors between those modules and the
sheaves of `O`-modules on `C` that Stacks Remark 09CY takes as its starting point: the inverse
image `π^{-1}` and its left adjoint `π_!`.

## Main definitions

* `Stacks.SimplicialModules.projectionRingMap`: the comparison of the sheaf of rings on `Δ × C`
  attached to the constant simplicial sheaf of rings on `O` with the restriction of `O` along
  `π`; it is the identity on sections.
* `Stacks.SimplicialModules.moduleInverseImage`: `π^{-1} : Mod(O) ⥤ Mod(π^{-1}O)`.
* `Stacks.SimplicialModules.moduleLowerShriek`: `π_! : Mod(π^{-1}O) ⥤ Mod(O)`, the left adjoint,
  with its adjunction `Stacks.SimplicialModules.moduleLowerShriekAdjunction`.

## Main results

* `Stacks.SimplicialModules.moduleInverseImage_isRightAdjoint`: `π^{-1}` on sheaves of modules
  admits a left adjoint. This is the existence statement of Stacks 08PC part (1) for the
  projection, which is what Stacks Remark 09CY specializes.
* `Stacks.SimplicialModules.moduleLowerShriek_additive`: `π_!` is additive, being a left adjoint;
  this is what lets it be applied degreewise to complexes.

## Implementation notes

`π^{-1}` is not built here from the inverse image of a morphism of ringed topoi, as
`StacksFrontier/CategoryTheory/Sites/Cohomology/FibredCategory/ModuleInverseImage.lean` does for the
standing data of Stacks 08PA. That development ties the universe of the module sections to the
universes of the two sites and takes a `CommRingCat`-valued structure sheaf, whereas Stacks 09D1
and its successors are stated for an arbitrary `RingCat`-valued sheaf of rings `O` with its own
universe `r`. What is used instead is Mathlib's pushforward of sheaves of modules along a
continuous functor of sites, whose ring universe and module universe are independent, together
with the presheaf-level existence of its left adjoint over an essentially small site at a free
module universe
(`PresheafOfModules.isRightAdjoint_pushforward_of_essentiallySmall_univLE`). Taking the module
sections in `max u v r w` makes the smallness of the values of the sheaves of rings automatic and
matches the universe at which `Stacks.SimplicialModules.abelian` supplies the abelian structure.

The projection is continuous for the inherited topology because it is a fibred category, which is
the continuity half of Stacks 06NW
(`Stacks.Sites.FibredCategory.isContinuous_inheritedTopology_of_isFibered`).

## References

* [Stacks Project, Tag 09CY](https://stacks.math.columbia.edu/tag/09CY), the lower shriek of the
  projection of a fibred category.
* [Stacks Project, Tag 08PC](https://stacks.math.columbia.edu/tag/08PC), part (1).
* [Stacks Project, Tag 09D1](https://stacks.math.columbia.edu/tag/09D1), simplicial modules.
* [Stacks Project, Tag 06NW](https://stacks.math.columbia.edu/tag/06NW), the inherited site.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe t w v u r

namespace Stacks.SimplicialModules

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- The projection `π : Δ × C ⥤ C`. -/
abbrev simplicialProjection : SimplexCategory × C ⥤ C :=
  CategoryTheory.Prod.snd SimplexCategory C

/-- The topology on `Δ × C` inherited from `C` along the projection, which is the one in which
Stacks 09D1 takes the sheaf condition on a simplicial module. -/
abbrev simplicialProjectionTopology : GrothendieckTopology (SimplexCategory × C) :=
  (simplicialProjection (C := C)).inheritedTopology J

/-- **Stacks 06NW, continuity half, for the projection `Δ × C ⥤ C`.** The projection is a fibred
category, so it is continuous from the inherited topology to `J`. -/
instance projection_isContinuous :
    (simplicialProjection (C := C)).IsContinuous (simplicialProjectionTopology J) J :=
  Stacks.Sites.FibredCategory.isContinuous_inheritedTopology_of_isFibered _ J

/-- `Δ × C` is essentially small in any universe containing the universes of `C`. Not an
instance: the universe `max u v r w` cannot be read back from the goal. -/
theorem essentiallySmall_prod :
    EssentiallySmall.{max u v t} (SimplexCategory × C) :=
  have : Small.{max u v t} (SimplexCategory × C) := small_max.{max v t, u} _
  have : LocallySmall.{max u v t} (SimplexCategory × C) :=
    ⟨fun _ _ ↦ small_max.{max u t, v} _⟩
  essentiallySmall_of_small_of_locallySmall _

/-- `C` is locally small in any universe containing the universe of its morphisms. Not an
instance, for the same reason as `essentiallySmall_prod`. -/
theorem locallySmall_base : LocallySmall.{max u v t} C :=
  ⟨fun _ _ ↦ small_max.{max u t, v} _⟩

variable (O : Sheaf J RingCat.{r})

/-- The sheaf of rings on `Δ × C` attached to the constant simplicial sheaf of rings on `O` *is*
the restriction `π^{-1}O` of `O` along the projection: the comparison between the two is the
identity on sections. -/
def projectionRingMap :
    ringSheaf J ((Functor.const SimplexCategoryᵒᵖ).obj O) ⟶
      ((simplicialProjection (C := C)).sheafPushforwardContinuous RingCat.{r}
        (simplicialProjectionTopology J) J).obj O :=
  𝟙 _

/-- The two sheaves of rings are the same: the sections and the restriction maps of the sheaf of
rings attached to the constant simplicial sheaf of rings on `O` are those of `π^{-1}O`. -/
theorem ringSheaf_constant_eq :
    ringSheaf J ((Functor.const SimplexCategoryᵒᵖ).obj O) =
      ((simplicialProjection (C := C)).sheafPushforwardContinuous RingCat.{r}
        (simplicialProjectionTopology J) J).obj O :=
  rfl

/-- Smallness of the values of `π^{-1}O`, needed for the presheaf-level left adjoint at a module
universe independent of the ring universe. Not an instance, the universe being unreadable from
the goal. -/
theorem small_projectionRingSheaf_obj (X : (SimplexCategory × C)ᵒᵖ) :
    Small.{max u v r w}
      ((((simplicialProjection (C := C)).sheafPushforwardContinuous RingCat.{r}
        (simplicialProjectionTopology J) J).obj O).obj.obj X) :=
  small_max.{max u v w, r} _

/-- Smallness of the values of `O`, for the same reason. -/
theorem small_ringSheaf_obj (X : Cᵒᵖ) :
    Small.{max u v r w} (O.obj.obj X) :=
  small_max.{max u v w, r} _

section

variable [HasWeakSheafify J AddCommGrpCat.{max u v r w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r w}]

/-- `π^{-1} : Mod(O) ⥤ Mod(π^{-1}O)`, the inverse image of sheaves of `O`-modules along the
projection: restriction of the sections along `π`, read as modules over `π^{-1}O`. -/
abbrev moduleInverseImage :
    SheafOfModules.{max u v r w} O ⥤
      SheafOfModules.{max u v r w}
        (ringSheaf J ((Functor.const SimplexCategoryᵒᵖ).obj O)) :=
  SheafOfModules.pushforward.{max u v r w} (projectionRingMap J O)

/-- **Stacks 08PC part (1) for the projection `Δ × C ⥤ C`, on sheaves of modules.** The inverse
image `π^{-1}` of sheaves of `O`-modules admits a left adjoint `π_!`. This is the input Stacks
Remark 09CY specializes from Stacks 08PC; the left adjoint exists because `Δ × C` is essentially
small in the universe of the module sections. -/
instance moduleInverseImage_isRightAdjoint :
    (moduleInverseImage.{w} J O).IsRightAdjoint :=
  have := essentiallySmall_prod.{max r w, v, u} (C := C)
  have := locallySmall_base.{max r w, v, u} (C := C)
  have := small_projectionRingSheaf_obj.{w} J O
  have := small_ringSheaf_obj.{w} J O
  have : (PresheafOfModules.pushforward.{max u v r w}
      (projectionRingMap J O).hom).IsRightAdjoint :=
    PresheafOfModules.isRightAdjoint_pushforward_of_essentiallySmall_univLE.{max u v r w}
      (projectionRingMap J O).hom
  inferInstance

/-- `π_! : Mod(π^{-1}O) ⥤ Mod(O)`, the left adjoint of the inverse image along the projection.
It is not a chosen functor: a left adjoint is unique up to canonical isomorphism. -/
abbrev moduleLowerShriek :
    SheafOfModules.{max u v r w}
        (ringSheaf J ((Functor.const SimplexCategoryᵒᵖ).obj O)) ⥤
      SheafOfModules.{max u v r w} O :=
  SheafOfModules.pullback.{max u v r w} (projectionRingMap J O)

/-- The adjunction `π_! ⊣ π^{-1}` on sheaves of modules. -/
abbrev moduleLowerShriekAdjunction :
    moduleLowerShriek.{w} J O ⊣ moduleInverseImage.{w} J O :=
  SheafOfModules.pullbackPushforwardAdjunction.{max u v r w} (projectionRingMap J O)

/-- `π^{-1}` on sheaves of modules is additive: it restricts the sections along `π`, and the
addition of morphisms of sheaves of modules is computed on sections. -/
instance moduleInverseImage_additive : (moduleInverseImage.{w} J O).Additive where
  map_add := rfl

/-- `π_!` on sheaves of modules is additive, being a left adjoint of the additive `π^{-1}`. This
is what lets it be applied degreewise to complexes, which is how `Lπ_!` is formed. -/
instance moduleLowerShriek_additive : (moduleLowerShriek.{w} J O).Additive :=
  have := moduleInverseImage_additive.{w} J O
  (moduleLowerShriekAdjunction.{w} J O).left_adjoint_additive

end

end Stacks.SimplicialModules

end
