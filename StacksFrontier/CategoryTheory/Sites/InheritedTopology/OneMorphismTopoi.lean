module

public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.OneMorphismContinuity
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoi
import StacksCore.Tactic.StacksAttribute

/-!
# The morphism of topoi induced by a 1-morphism of fibred categories, over any base

Let `(𝒞, J)` be a site and let `F : 𝒳 ⥤ 𝒴` be a 1-morphism of fibred categories over `𝒞`
(Stacks 02XP), with `p : 𝒳 ⥤ 𝒞` and `q : 𝒴 ⥤ 𝒞`. Endow `𝒳` and `𝒴` with the topologies they
inherit from `(𝒞, J)` (Stacks 06NV). By
`CategoryTheory.Functor.IsFibredOneMorphism.isContinuous_inheritedTopology` and
`CategoryTheory.Functor.IsFibredOneMorphism.isCocontinuous_inheritedTopology` the functor `F` is
continuous and cocontinuous, with nothing assumed of the base beyond its topology. This file
derives from those two facts the rest of Stacks 06NW: `F` induces a morphism of topoi
`f : Sh(𝒳) ⟶ Sh(𝒴)` with `f⁻¹ = F^s = F^p` plain restriction along `F.op`, so that
`f⁻¹(𝒢)(x) = 𝒢(F x)`, and `f_* = {}_sF = {}_pF` the right Kan extension along `F.op`.

No fibre products are assumed in `𝒞`. The forms in
`StacksFrontier/CategoryTheory/Sites/InheritedTopology/Functoriality.lean` are the special case
`[HasPullbacks 𝒞]`.

## Main results

* `CategoryTheory.Functor.IsFibredOneMorphism.sheafPushforwardContinuousCompSheafToPresheafIso`:
  the inverse image `f⁻¹` is restriction along `F.op`, with no sheafification.
* `CategoryTheory.Functor.IsFibredOneMorphism.sheafPushforwardContinuous_obj_obj_obj`: the
  formula `f⁻¹(𝒢)(x) = 𝒢(F x)`.
* `CategoryTheory.Functor.IsFibredOneMorphism.preservesFiniteLimits_sheafPushforwardContinuous`:
  `f⁻¹` is left exact.
* `CategoryTheory.Functor.IsFibredOneMorphism.sheafPushforwardCocontinuousCompSheafToPresheafIso`:
  the direct image `f_*` is the right Kan extension along `F.op`, with no sheafification.
* `CategoryTheory.Functor.IsFibredOneMorphism.sheafAdjunctionCocontinuous`: the adjunction
  `f⁻¹ ⊣ f_*`.
* `CategoryTheory.Functor.IsFibredOneMorphism.morphismOfTopoi`: the morphism of topoi
  `f : Sh(𝒳) ⟶ Sh(𝒴)` itself.
* `CategoryTheory.Functor.IsFibredOneMorphism.morphismOfTopoiType` and its companions with suffix
  `Type`/`_type`: the same for sheaves of sets, where every hypothesis on the coefficients is
  discharged by instances.

## Implementation notes

Sheaves take values in an arbitrary category `A`; Stacks' sheaves of sets are the case
`A = Type w`. The direct image exists as a right Kan extension whenever the pointwise right Kan
extensions along `F.op` exist, which is the hypothesis `[∀ G, F.op.HasPointwiseRightKanExtension G]`
(an instance for `A = Type w` and small `𝒳`, `𝒴`); left exactness of `f⁻¹` uses that `A` has finite
limits.

## References

* [Stacks Project, Tag 06NW](https://stacks.math.columbia.edu/tag/06NW)
-/

@[expose] public section

open CategoryTheory Limits

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory.Functor

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
  {𝒴 : Type u₃} [Category.{v₃} 𝒴]
  (J : GrothendieckTopology 𝒞) {p : 𝒳 ⥤ 𝒞} {q : 𝒴 ⥤ 𝒞} {F : 𝒳 ⥤ 𝒴}
  [p.IsFibered] (hF : p.IsFibredOneMorphism q F) (A : Type u₄) [Category.{v₄} A]

/-- **Stacks 06NW, `f⁻¹ = F^p`, over any base.** The inverse image of the morphism of topoi
induced by a 1-morphism `F` of fibred categories over a site is plain restriction along `F.op`: as
a functor to presheaves on `𝒳` it is `sheafToPresheaf` followed by precomposition with `F.op`, with
no sheafification. No fibre products of the base are assumed. -/
@[stacks 06NW "`f⁻¹ = F^s = F^p`: the inverse image is restriction along `F.op`, unsheafified."]
def IsFibredOneMorphism.sheafPushforwardContinuousCompSheafToPresheafIso :
    letI := hF.isContinuous_inheritedTopology J
    F.sheafPushforwardContinuous A (p.inheritedTopology J) (q.inheritedTopology J) ⋙
        sheafToPresheaf (p.inheritedTopology J) A ≅
      sheafToPresheaf (q.inheritedTopology J) A ⋙ (whiskeringLeft _ _ _).obj F.op :=
  have := hF.isContinuous_inheritedTopology J
  F.sheafPushforwardContinuousCompSheafToPresheafIso A _ _

/-- **Stacks 06NW, `f⁻¹(𝒢)(x) = 𝒢(F(x))`, over any base.** The sections of the inverse image of
a sheaf `𝒢` on `𝒴` over an object `x` of `𝒳` are the sections of `𝒢` over `F x`. No fibre
products of the base are assumed. -/
@[stacks 06NW "The formula `f⁻¹(𝒢)(x) = 𝒢(F(x))`."]
theorem IsFibredOneMorphism.sheafPushforwardContinuous_obj_obj_obj :
    letI := hF.isContinuous_inheritedTopology J
    ∀ (𝒢 : Sheaf (q.inheritedTopology J) A) (x : 𝒳),
      ((F.sheafPushforwardContinuous A (p.inheritedTopology J)
            (q.inheritedTopology J)).obj 𝒢).obj.obj (Opposite.op x) =
        𝒢.obj.obj (Opposite.op (F.obj x)) :=
  have := hF.isContinuous_inheritedTopology J
  fun 𝒢 x ↦ F.sheafPushforwardContinuous_obj_obj_obj A _ _ 𝒢 (Opposite.op x)

/-- **Stacks 06NW, left exactness of `f⁻¹`, over any base.** The inverse image of the morphism of
topoi induced by a 1-morphism of fibred categories over a site preserves finite limits. No fibre
products of the base are assumed. -/
@[stacks 06NW "Left exactness of `f⁻¹`, part of `f` being a morphism of topoi."]
theorem IsFibredOneMorphism.preservesFiniteLimits_sheafPushforwardContinuous
    [HasFiniteLimits A] :
    letI := hF.isContinuous_inheritedTopology J
    PreservesFiniteLimits (F.sheafPushforwardContinuous A (p.inheritedTopology J)
      (q.inheritedTopology J)) := by
  have := hF.isContinuous_inheritedTopology J
  constructor
  intro S _ _
  have : PreservesLimitsOfShape S
      (F.sheafPushforwardContinuous A (p.inheritedTopology J) (q.inheritedTopology J) ⋙
        sheafToPresheaf (p.inheritedTopology J) A) :=
    preservesLimitsOfShape_of_natIso
      (F.sheafPushforwardContinuousCompSheafToPresheafIso A _ _).symm
  exact preservesLimitsOfShape_of_reflects_of_preserves _ (sheafToPresheaf _ A)

/-- **Stacks 06NW, `f_* = {}_pF`, over any base.** The direct image of the morphism of topoi
induced by a 1-morphism `F` of fibred categories over a site is the right Kan extension along
`F.op`, taken on sheaves: as a functor to presheaves on `𝒴` it is `sheafToPresheaf` followed by
`F.op.ran`, with no sheafification. No fibre products of the base are assumed. -/
@[stacks 06NW "`f_* = {}_sF = {}_pF`: the direct image is the right Kan extension along `F.op`."]
noncomputable def IsFibredOneMorphism.sheafPushforwardCocontinuousCompSheafToPresheafIso
    [∀ (G : 𝒳ᵒᵖ ⥤ A), F.op.HasPointwiseRightKanExtension G] :
    letI := hF.isCocontinuous_inheritedTopology J
    F.sheafPushforwardCocontinuous A (p.inheritedTopology J) (q.inheritedTopology J) ⋙
        sheafToPresheaf (q.inheritedTopology J) A ≅
      sheafToPresheaf (p.inheritedTopology J) A ⋙ F.op.ran :=
  have := hF.isCocontinuous_inheritedTopology J
  F.sheafPushforwardCocontinuousCompSheafToPresheafIso A _ _

/-- **Stacks 06NW, the adjunction `f⁻¹ ⊣ f_*`, over any base.** For a 1-morphism `F` of fibred
categories over a site, restriction `F.sheafPushforwardContinuous` along `F.op` is left adjoint to
the right Kan extension `F.sheafPushforwardCocontinuous` along `F.op`, as functors between the
sheaf categories of the two inherited sites. No fibre products of the base are assumed. -/
@[stacks 06NW "The adjunction `f⁻¹ ⊣ f_*` between `F^s` and `{}_sF`."]
noncomputable def IsFibredOneMorphism.sheafAdjunctionCocontinuous
    [∀ (G : 𝒳ᵒᵖ ⥤ A), F.op.HasPointwiseRightKanExtension G] :
    letI := hF.isContinuous_inheritedTopology J
    letI := hF.isCocontinuous_inheritedTopology J
    F.sheafPushforwardContinuous A (p.inheritedTopology J) (q.inheritedTopology J) ⊣
      F.sheafPushforwardCocontinuous A (p.inheritedTopology J) (q.inheritedTopology J) :=
  have := hF.isContinuous_inheritedTopology J
  have := hF.isCocontinuous_inheritedTopology J
  F.sheafAdjunctionCocontinuous A _ _

/-- **Stacks 06NW, the morphism of topoi, over any base.** A 1-morphism `F : 𝒳 ⥤ 𝒴` of fibred
categories over a site `(𝒞, J)` induces a morphism of topoi `f : Sh(𝒳) ⟶ Sh(𝒴)` between the
inherited sites, whose inverse image `f⁻¹ = F^s` is restriction along `F.op`
(`IsFibredOneMorphism.sheafPushforwardContinuousCompSheafToPresheafIso`) and whose direct image
`f_* = {}_sF` is the right Kan extension along `F.op`
(`IsFibredOneMorphism.sheafPushforwardCocontinuousCompSheafToPresheafIso`). No fibre products of
the base are assumed. -/
@[stacks 06NW "The morphism of topoi `f = (F^s, {}_sF) : Sh(𝒳) ⟶ Sh(𝒴)`."]
noncomputable def IsFibredOneMorphism.morphismOfTopoi [HasFiniteLimits A]
    [∀ (G : 𝒳ᵒᵖ ⥤ A), F.op.HasPointwiseRightKanExtension G] :
    MorphismOfTopoi (Sheaf (p.inheritedTopology J) A) (Sheaf (q.inheritedTopology J) A) :=
  letI := hF.isContinuous_inheritedTopology J
  letI := hF.isCocontinuous_inheritedTopology J
  { pushforward := F.sheafPushforwardCocontinuous A (p.inheritedTopology J) (q.inheritedTopology J)
    inverseImage := F.sheafPushforwardContinuous A (p.inheritedTopology J) (q.inheritedTopology J)
    adj := hF.sheafAdjunctionCocontinuous J A
    preservesFiniteLimits := hF.preservesFiniteLimits_sheafPushforwardContinuous J A }

/-- The inverse image of `IsFibredOneMorphism.morphismOfTopoi` is restriction
`F.sheafPushforwardContinuous` along `F.op`. -/
theorem IsFibredOneMorphism.morphismOfTopoi_inverseImage [HasFiniteLimits A]
    [∀ (G : 𝒳ᵒᵖ ⥤ A), F.op.HasPointwiseRightKanExtension G] :
    letI := hF.isContinuous_inheritedTopology J
    (hF.morphismOfTopoi J A).inverseImage =
      F.sheafPushforwardContinuous A (p.inheritedTopology J) (q.inheritedTopology J) :=
  rfl

/-- The direct image of `IsFibredOneMorphism.morphismOfTopoi` is the right Kan extension
`F.sheafPushforwardCocontinuous` along `F.op`. -/
theorem IsFibredOneMorphism.morphismOfTopoi_pushforward [HasFiniteLimits A]
    [∀ (G : 𝒳ᵒᵖ ⥤ A), F.op.HasPointwiseRightKanExtension G] :
    letI := hF.isCocontinuous_inheritedTopology J
    (hF.morphismOfTopoi J A).pushforward =
      F.sheafPushforwardCocontinuous A (p.inheritedTopology J) (q.inheritedTopology J) :=
  rfl

/-! ### Sheaves of sets

Stacks 06NW is about sheaves of sets. For `A = Type (max u₂ v₃ w)` the hypotheses above are
discharged by instances: `Type` has finite limits, and the pointwise right Kan extensions along
`F.op` exist because the indexing categories `StructuredArrow y F.op` live in `Type (max u₂ v₃)`,
so they are small for `Type (max u₂ v₃ w)`. The universe `max u₂ v₃ w` is any universe large enough
to contain the objects of `𝒳` and the morphisms of `𝒴`, as in Stacks' choice of a universe of sets
containing the sites involved. The inverse image statements
(`IsFibredOneMorphism.sheafPushforwardContinuousCompSheafToPresheafIso`,
`IsFibredOneMorphism.sheafPushforwardContinuous_obj_obj_obj`) carry no hypothesis on `A` at all.
-/

section Types

universe w

/-- **Stacks 06NW, left exactness of `f⁻¹`, for sheaves of sets.** The inverse image of the
morphism of topoi induced by a 1-morphism of fibred categories over a site preserves finite limits
of sheaves of sets. No fibre products of the base are assumed. -/
@[stacks 06NW "Left exactness of `f⁻¹` on sheaves of sets, with no hypothesis beyond the source's."]
theorem IsFibredOneMorphism.preservesFiniteLimits_sheafPushforwardContinuous_type :
    letI := hF.isContinuous_inheritedTopology J
    PreservesFiniteLimits (F.sheafPushforwardContinuous (Type w) (p.inheritedTopology J)
      (q.inheritedTopology J)) :=
  hF.preservesFiniteLimits_sheafPushforwardContinuous J (Type w)

/-- **Stacks 06NW, `f_* = {}_pF`, for sheaves of sets.** On sheaves of sets, the direct image of
the morphism of topoi induced by a 1-morphism `F` of fibred categories over a site is the right Kan
extension along `F.op`, with no sheafification; the Kan extensions exist with no further
hypothesis. No fibre products of the base are assumed. -/
@[stacks 06NW "`f_* = {}_pF` on sheaves of sets, with no hypothesis beyond the source's."]
noncomputable def IsFibredOneMorphism.sheafPushforwardCocontinuousCompSheafToPresheafIsoType :
    letI := hF.isCocontinuous_inheritedTopology J
    F.sheafPushforwardCocontinuous (Type (max u₂ v₃ w)) (p.inheritedTopology J)
          (q.inheritedTopology J) ⋙
        sheafToPresheaf (q.inheritedTopology J) (Type (max u₂ v₃ w)) ≅
      sheafToPresheaf (p.inheritedTopology J) (Type (max u₂ v₃ w)) ⋙ F.op.ran :=
  hF.sheafPushforwardCocontinuousCompSheafToPresheafIso J (Type (max u₂ v₃ w))

/-- **Stacks 06NW, the adjunction `f⁻¹ ⊣ f_*`, for sheaves of sets.** On sheaves of sets,
restriction along `F.op` is left adjoint to the right Kan extension along `F.op`, with no
hypothesis beyond the source's. No fibre products of the base are assumed. -/
@[stacks 06NW "The adjunction `f⁻¹ ⊣ f_*` on sheaves of sets, no hypothesis beyond the source's."]
noncomputable def IsFibredOneMorphism.sheafAdjunctionCocontinuousType :
    letI := hF.isContinuous_inheritedTopology J
    letI := hF.isCocontinuous_inheritedTopology J
    F.sheafPushforwardContinuous (Type (max u₂ v₃ w)) (p.inheritedTopology J)
        (q.inheritedTopology J) ⊣
      F.sheafPushforwardCocontinuous (Type (max u₂ v₃ w)) (p.inheritedTopology J)
        (q.inheritedTopology J) :=
  hF.sheafAdjunctionCocontinuous J (Type (max u₂ v₃ w))

/-- **Stacks 06NW, the morphism of topoi, for sheaves of sets.** A 1-morphism `F : 𝒳 ⥤ 𝒴` of
fibred categories over a site `(𝒞, J)` induces a morphism of topoi `f : Sh(𝒳) ⟶ Sh(𝒴)` between the
topoi of sheaves of sets on the inherited sites, with `f⁻¹ = F^p` restriction along `F.op` and
`f_* = {}_pF` the right Kan extension along `F.op`. No hypothesis beyond the source's: in
particular no fibre products of the base. -/
@[stacks 06NW "The morphism of topoi `f : Sh(𝒳) ⟶ Sh(𝒴)` of sheaves of sets, with no hypothesis \
beyond the source's."]
noncomputable def IsFibredOneMorphism.morphismOfTopoiType :
    MorphismOfTopoi (Sheaf (p.inheritedTopology J) (Type (max u₂ v₃ w)))
      (Sheaf (q.inheritedTopology J) (Type (max u₂ v₃ w))) :=
  hF.morphismOfTopoi J (Type (max u₂ v₃ w))

end Types

end CategoryTheory.Functor

end
