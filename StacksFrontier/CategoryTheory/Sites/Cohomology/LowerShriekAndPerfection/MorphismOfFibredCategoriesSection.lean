module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.RingedToposOfAMorphism
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriekAndPerfection.FibredCategorySection
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.Slice
public import StacksFrontier.CategoryTheory.Sites.Localization.LocalizationComposite
public import StacksFrontier.CategoryTheory.Sites.Localization.PushforwardAdjunction
public import StacksFrontier.CategoryTheory.Sites.CocontinuousRightAdjointMorphismOfSites

/-!
# A section compatible with both localized projections of a morphism of fibred categories

Let `(D, O_D)` be a ringed site, let `p : C ⥤ D` and `p' : C' ⥤ D` be fibred categories over its
underlying site and let `u : C' ⥤ C` be a 1-morphism of fibred categories over `D`, as in the
standing data of Stacks 08PA. Fix an object `U'` of `C'`, put `U = u(U')` and `V = p'(U')`, and
consider the three localized morphisms of topoi

```
Sh(C'/U') --g'--> Sh(C/U)
       \            /
       π'_{U'}    π_U
          \        /
          Sh(D/V)
```

obtained by localizing the two projections and the 1-morphism. Then `π'_{U'}` has a section
`σ' : Sh(D/V) ⟶ Sh(C'/U')` whose inverse image is the direct image of `π'_{U'}`, and the
composite `σ = g' ∘ σ'` is simultaneously a section of `π_U` whose inverse image is the direct
image of `π_U`.

The section is the one of Stacks 08P9 for the fibred category `p'`, transported along the
identification `p'(U') = p(u(U'))` that the 1-morphism supplies. That it also sections the
*other* projection is the only point with content: the cartesian section functors of `p'` and of
`p` are compared by the universal property of a cartesian lift, since `u` carries cartesian lifts
for `p'` to cartesian lifts for `p`.

## Main definitions

* `Stacks.Sites.FibredCategory.MorphismSituation.sourceSliceProjectionAt`: the projection of the
  slice `C'/U'` to a slice of the base, through an identification of the base object.
* `Stacks.Sites.FibredCategory.MorphismSituation.CompatibleLocalizedSection`: the localized
  triangle of topoi together with a section of both projections, with each geometric map pinned by
  the (co)continuous functor it comes from.

## Main results

* `Stacks.Sites.FibredCategory.MorphismSituation.compatibleLocalizedSection`: that datum exists
  for every object of the source fibred category.

## Implementation notes

Both projections are put over one slice `D/p(u(U'))` of the base using the equality
`p'(U') = p(u(U'))`, so that the two section identities can be stated at all; the transport is
`CategoryTheory.Over.map` of the corresponding `eqToHom`, which is an equivalence of localized
sites, so continuity, cocontinuity and the adjunction all transport along it.

As in Stacks 08P9, an identity of morphisms of topoi is recorded as a pair of natural isomorphisms
of the two induced functors rather than as an equality, since the adjunction datum of a morphism of
topoi is not canonical; and each geometric map is pinned by an equation identifying its inverse
image with restriction along the corresponding functor of slice sites and its direct image with
the right Kan extension, so that an arbitrary morphism of topoi cannot serve in its place.

Continuity of the localized 1-morphism `Over.post u` is not formal: it is the continuity half of
Stacks 06NW applied to `Over.post u` as a 1-morphism of the two slices over `D`, together with
`CategoryTheory.Functor.inheritedTopology_overForget_comp` identifying the topology a slice
inherits from `D` with the localization of the inherited topology. Cocontinuity, by contrast, is
inherited from cocontinuity of `u` itself by Stacks 03EG.

## References

* [Stacks Project, Tag 08PB](https://stacks.math.columbia.edu/tag/08PB)
* [Stacks Project, Tag 08PA](https://stacks.math.columbia.edu/tag/08PA)
* [Stacks Project, Tag 08P9](https://stacks.math.columbia.edu/tag/08P9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits

namespace Stacks.Sites.FibredCategory.MorphismSituation

universe u₀ u₁ u₂ v₀ v₁ v₂ w

variable (S : MorphismSituation.{u₀, u₁, u₂, v₀, v₁, v₂, max w u₀ u₁ u₂ v₀ v₁ v₂})
  (U' : S.source)

/-- The base object of `U'` computed through the source projection agrees with the one computed
through the 1-morphism and the target projection, since `u ⋙ p = p'`. -/
theorem p'_obj_eq : S.p'.obj U' = S.p.obj (S.u.obj U') :=
  (Functor.congr_obj S.isFibredOneMorphism.comp_eq U').symm

/-- The projection of the slice `C'/U'` to the slice of the base at `V`, for any object `V` of
the base identified with `p'(U')`. Taking `V` to be `p(u(U'))` puts it over the same slice of the
base as the localized target projection. -/
def sourceSliceProjectionAt {V : S.base.C} (h : S.p'.obj U' = V) : Over U' ⥤ Over V :=
  (Over.post S.p' : Over U' ⥤ Over (S.p'.obj U')) ⋙ Over.map (eqToHom h)

/-- The projection of the slice `C'/U'` to the slice of the base at `p(u(U'))`. -/
abbrev sourceSliceProjection : Over U' ⥤ Over (S.p.obj (S.u.obj U')) :=
  sourceSliceProjectionAt S U' (p'_obj_eq S U')

/-- **Stacks 08PB.** The localized triangle of topoi, together with a section of the localized
source projection whose composite with the localized 1-morphism is a section of the localized
target projection. Each geometric map is pinned by the functor of slice sites it comes from, and
each section identity is recorded on both induced functors. -/
structure CompatibleLocalizedSection where
  /-- The localized source projection is continuous. -/
  sourceContinuous : (sourceSliceProjection S U').IsContinuous
    (S.sourceTopology.over U') (S.base.J.over (S.p.obj (S.u.obj U')))
  /-- The localized source projection is cocontinuous. -/
  sourceCocontinuous : (sourceSliceProjection S U').IsCocontinuous
    (S.sourceTopology.over U') (S.base.J.over (S.p.obj (S.u.obj U')))
  /-- The localized target projection is continuous. -/
  totalContinuous : (Over.post S.p : Over (S.u.obj U') ⥤
    Over (S.p.obj (S.u.obj U'))).IsContinuous
      (S.totalTopology.over (S.u.obj U')) (S.base.J.over (S.p.obj (S.u.obj U')))
  /-- The localized target projection is cocontinuous. -/
  totalCocontinuous : (Over.post S.p : Over (S.u.obj U') ⥤
    Over (S.p.obj (S.u.obj U'))).IsCocontinuous
      (S.totalTopology.over (S.u.obj U')) (S.base.J.over (S.p.obj (S.u.obj U')))
  /-- The localized 1-morphism is continuous. -/
  morphismContinuous : (Over.post S.u : Over U' ⥤ Over (S.u.obj U')).IsContinuous
    (S.sourceTopology.over U') (S.totalTopology.over (S.u.obj U'))
  /-- The localized 1-morphism is cocontinuous. -/
  morphismCocontinuous : (Over.post S.u : Over U' ⥤ Over (S.u.obj U')).IsCocontinuous
    (S.sourceTopology.over U') (S.totalTopology.over (S.u.obj U'))
  /-- The morphism of topoi `π'_{U'}`. -/
  sourceProjection : MorphismOfTopoi
    (Sheaf (S.sourceTopology.over U') (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)))
    (Sheaf (S.base.J.over (S.p.obj (S.u.obj U'))) (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)))
  /-- The morphism of topoi `π_U`. -/
  totalProjection : MorphismOfTopoi
    (Sheaf (S.totalTopology.over (S.u.obj U')) (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)))
    (Sheaf (S.base.J.over (S.p.obj (S.u.obj U'))) (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)))
  /-- The morphism of topoi `g'`. -/
  localizedMorphism : MorphismOfTopoi
    (Sheaf (S.sourceTopology.over U') (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)))
    (Sheaf (S.totalTopology.over (S.u.obj U')) (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)))
  /-- The inverse image of `π'_{U'}` is restriction along the localized source projection. -/
  sourceProjection_inverseImage :
    letI := sourceContinuous
    sourceProjection.inverseImage =
      (sourceSliceProjection S U').sheafPushforwardContinuous
        (Type (max w u₀ u₁ u₂ v₀ v₁ v₂))
        (S.sourceTopology.over U') (S.base.J.over (S.p.obj (S.u.obj U')))
  /-- The direct image of `π'_{U'}` is the right Kan extension along the localized source
  projection. -/
  sourceProjection_pushforward :
    letI := sourceCocontinuous
    sourceProjection.pushforward =
      (sourceSliceProjection S U').sheafPushforwardCocontinuous
        (Type (max w u₀ u₁ u₂ v₀ v₁ v₂))
        (S.sourceTopology.over U') (S.base.J.over (S.p.obj (S.u.obj U')))
  /-- The inverse image of `π_U` is restriction along the localized target projection. -/
  totalProjection_inverseImage :
    letI := totalContinuous
    totalProjection.inverseImage =
      (Over.post S.p :
        Over (S.u.obj U') ⥤ Over (S.p.obj (S.u.obj U'))).sheafPushforwardContinuous
        (Type (max w u₀ u₁ u₂ v₀ v₁ v₂))
        (S.totalTopology.over (S.u.obj U')) (S.base.J.over (S.p.obj (S.u.obj U')))
  /-- The direct image of `π_U` is the right Kan extension along the localized target
  projection. -/
  totalProjection_pushforward :
    letI := totalCocontinuous
    totalProjection.pushforward =
      (Over.post S.p :
        Over (S.u.obj U') ⥤ Over (S.p.obj (S.u.obj U'))).sheafPushforwardCocontinuous
        (Type (max w u₀ u₁ u₂ v₀ v₁ v₂))
        (S.totalTopology.over (S.u.obj U')) (S.base.J.over (S.p.obj (S.u.obj U')))
  /-- The inverse image of `g'` is restriction along the localized 1-morphism. -/
  localizedMorphism_inverseImage :
    letI := morphismContinuous
    localizedMorphism.inverseImage =
      (Over.post S.u : Over U' ⥤ Over (S.u.obj U')).sheafPushforwardContinuous
        (Type (max w u₀ u₁ u₂ v₀ v₁ v₂))
        (S.sourceTopology.over U') (S.totalTopology.over (S.u.obj U'))
  /-- The direct image of `g'` is the right Kan extension along the localized 1-morphism. -/
  localizedMorphism_pushforward :
    letI := morphismCocontinuous
    localizedMorphism.pushforward =
      (Over.post S.u : Over U' ⥤ Over (S.u.obj U')).sheafPushforwardCocontinuous
        (Type (max w u₀ u₁ u₂ v₀ v₁ v₂))
        (S.sourceTopology.over U') (S.totalTopology.over (S.u.obj U'))
  /-- The section `σ'`. -/
  rightSection : MorphismOfTopoi
    (Sheaf (S.base.J.over (S.p.obj (S.u.obj U'))) (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)))
    (Sheaf (S.sourceTopology.over U') (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)))
  /-- `(σ')^{-1} = π'_{U',*}`. -/
  section_inverseImage : rightSection.inverseImage = sourceProjection.pushforward
  /-- `σ^{-1} = π_{U,*}`, for `σ = g' ∘ σ'`. -/
  section_to_total_inverseImage :
    (localizedMorphism.comp rightSection).inverseImage ≅ totalProjection.pushforward
  /-- `π'_{U'} ∘ σ' = id`, on inverse images. -/
  source_rightInverse_inverseImage :
    (sourceProjection.comp rightSection).inverseImage ≅
      𝟭 (Sheaf (S.base.J.over (S.p.obj (S.u.obj U')))
        (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)))
  /-- `π'_{U'} ∘ σ' = id`, on direct images. -/
  source_rightInverse_pushforward :
    (sourceProjection.comp rightSection).pushforward ≅
      𝟭 (Sheaf (S.base.J.over (S.p.obj (S.u.obj U')))
        (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)))
  /-- `π_U ∘ σ = id`, on inverse images. -/
  total_rightInverse_inverseImage :
    (totalProjection.comp (localizedMorphism.comp rightSection)).inverseImage ≅
      𝟭 (Sheaf (S.base.J.over (S.p.obj (S.u.obj U')))
        (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)))
  /-- `π_U ∘ σ = id`, on direct images. -/
  total_rightInverse_pushforward :
    (totalProjection.comp (localizedMorphism.comp rightSection)).pushforward ≅
      𝟭 (Sheaf (S.base.J.over (S.p.obj (S.u.obj U')))
        (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)))

/-- The datum of Stacks 08P9 for the source fibred category, transported to a slice of the base
at an arbitrary object identified with `p'(U')`. -/
private structure SourceSliceSectionData {V : S.base.C} (h : S.p'.obj U' = V) where
  continuous : (sourceSliceProjectionAt S U' h).IsContinuous
    (S.sourceTopology.over U') (S.base.J.over V)
  cocontinuous : (sourceSliceProjectionAt S U' h).IsCocontinuous
    (S.sourceTopology.over U') (S.base.J.over V)
  projection : MorphismOfTopoi
    (Sheaf (S.sourceTopology.over U') (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)))
    (Sheaf (S.base.J.over V) (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)))
  projection_inverseImage :
    let := continuous
    projection.inverseImage = (sourceSliceProjectionAt S U' h).sheafPushforwardContinuous
      (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)) (S.sourceTopology.over U') (S.base.J.over V)
  projection_pushforward :
    let := cocontinuous
    projection.pushforward = (sourceSliceProjectionAt S U' h).sheafPushforwardCocontinuous
      (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)) (S.sourceTopology.over U') (S.base.J.over V)
  rightSection : MorphismOfTopoi
    (Sheaf (S.base.J.over V) (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)))
    (Sheaf (S.sourceTopology.over U') (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)))
  section_inverseImage : rightSection.inverseImage = projection.pushforward
  cartesianSectionFunctor : Over V ⥤ Over U'
  cartesianSection_base : cartesianSectionFunctor ⋙ sourceSliceProjectionAt S U' h ≅
    𝟭 (Over V)
  cartesianSection_adjunction : sourceSliceProjectionAt S U' h ⊣ cartesianSectionFunctor
  cartesianSection_isCartesian (X : Over V) :
    S.p'.IsStronglyCartesian (S.p'.map ((cartesianSectionFunctor.obj X).hom))
      ((cartesianSectionFunctor.obj X).hom)
  cartesianSection_isContinuous : cartesianSectionFunctor.IsContinuous
    (S.base.J.over V) (S.sourceTopology.over U')
  cartesianSection_isCocontinuous : cartesianSectionFunctor.IsCocontinuous
    (S.base.J.over V) (S.sourceTopology.over U')
  section_inverseImage_cartesian : rightSection.inverseImage ≅
    cartesianSectionFunctor.sheafPushforwardContinuous
      (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)) (S.base.J.over V) (S.sourceTopology.over U')
  source_rightInverse_inverseImage :
    (projection.comp rightSection).inverseImage ≅
      𝟭 (Sheaf (S.base.J.over V) (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)))
  source_rightInverse_pushforward :
    (projection.comp rightSection).pushforward ≅
      𝟭 (Sheaf (S.base.J.over V) (Type (max w u₀ u₁ u₂ v₀ v₁ v₂)))

private def sourceSliceSectionData {V : S.base.C} (h : S.p'.obj U' = V) :
    SourceSliceSectionData S U' h := by
  let A := Type (max w u₀ u₁ u₂ v₀ v₁ v₂)
  let TS : FibredCategorySituation.{u₀, v₀, u₂, v₂, max w u₀ u₁ u₂ v₀ v₁ v₂} :=
    { base := S.base, C := S.source, p := S.p', isFibered := S.p'Fibered }
  let D := localizedProjectionSection TS U'
  let q₀ : Over U' ⥤ Over (S.p'.obj U') := Over.post S.p'
  let e : Over (S.p'.obj U') ≌ Over V := Over.mapIso (eqToIso h)
  let q : Over U' ⥤ Over V := q₀ ⋙ Over.map (eqToHom h)
  let v : Over V ⥤ Over U' := Over.map (eqToHom h.symm) ⋙ D.cartesianSectionFunctor
  have hqCont : q.IsContinuous (S.sourceTopology.over U') (S.base.J.over V) := by
    have := D.isContinuous
    exact Functor.isContinuous_comp q₀ (Over.map (eqToHom h))
      (S.sourceTopology.over U') (S.base.J.over (S.p'.obj U')) (S.base.J.over V)
  have hqCocont : q.IsCocontinuous (S.sourceTopology.over U') (S.base.J.over V) := by
    have := D.isCocontinuous
    exact CategoryTheory.isCocontinuous_comp q₀ (Over.map (eqToHom h))
      (S.sourceTopology.over U') (S.base.J.over (S.p'.obj U'))
  have hvCont : v.IsContinuous (S.base.J.over V) (S.sourceTopology.over U') := by
    have := D.cartesianSection_isContinuous
    exact Functor.isContinuous_comp (Over.map (eqToHom h.symm)) D.cartesianSectionFunctor
      (S.base.J.over V) (S.base.J.over (S.p'.obj U')) (S.sourceTopology.over U')
  have hvCocont : v.IsCocontinuous (S.base.J.over V) (S.sourceTopology.over U') := by
    have := D.cartesianSection_isCocontinuous
    exact CategoryTheory.isCocontinuous_comp (Over.map (eqToHom h.symm))
      D.cartesianSectionFunctor (S.base.J.over V) (S.base.J.over (S.p'.obj U'))
  let adj : q ⊣ v := by
    simpa [q, v, q₀, e] using D.cartesianSection_adjunction.comp e.toAdjunction
  let π : MorphismOfTopoi (Sheaf (S.sourceTopology.over U') A) (Sheaf (S.base.J.over V) A) :=
    { inverseImage := q.sheafPushforwardContinuous A (S.sourceTopology.over U') (S.base.J.over V)
      pushforward := q.sheafPushforwardCocontinuous A (S.sourceTopology.over U') (S.base.J.over V)
      adj := q.sheafAdjunctionCocontinuous A (S.sourceTopology.over U') (S.base.J.over V)
      preservesFiniteLimits := inferInstance }
  let eSheaf :
      q.sheafPushforwardCocontinuous A (S.sourceTopology.over U') (S.base.J.over V) ≅
        v.sheafPushforwardContinuous A (S.base.J.over V) (S.sourceTopology.over U') :=
    adj.sheafPushforwardCocontinuousIso A
  let σ : MorphismOfTopoi (Sheaf (S.base.J.over V) A) (Sheaf (S.sourceTopology.over U') A) :=
    { inverseImage := q.sheafPushforwardCocontinuous A (S.sourceTopology.over U') (S.base.J.over V)
      pushforward := v.sheafPushforwardCocontinuous A (S.base.J.over V) (S.sourceTopology.over U')
      adj := (v.sheafAdjunctionCocontinuous A (S.base.J.over V)
        (S.sourceTopology.over U')).ofNatIsoLeft eSheaf.symm
      preservesFiniteLimits := Limits.preservesFiniteLimits_of_natIso eSheaf.symm }
  have hbase : v ⋙ q ≅ 𝟭 (Over V) := by
    cases h
    let q₀ : Over U' ⥤ Over (S.p'.obj U') := Over.post S.p'
    let v₀ := D.cartesianSectionFunctor
    let e₀ : Over.map (𝟙 (S.p'.obj U')) ≅ 𝟭 _ := Over.mapId _
    let iv : Over.map (𝟙 (S.p'.obj U')) ⋙ v₀ ≅ v₀ :=
      Functor.isoWhiskerRight e₀ v₀ ≪≫ Functor.leftUnitor v₀
    let iq : q₀ ⋙ Over.map (𝟙 (S.p'.obj U')) ≅ q₀ :=
      Functor.isoWhiskerLeft q₀ e₀ ≪≫ Functor.rightUnitor q₀
    exact
      Functor.isoWhiskerRight iv (q₀ ⋙ Over.map (𝟙 (S.p'.obj U'))) ≪≫
      Functor.associator (𝟭 _) v₀ (q₀ ⋙ Over.map (𝟙 (S.p'.obj U'))) ≪≫
      Functor.leftUnitor (v₀ ⋙ (q₀ ⋙ Over.map (𝟙 (S.p'.obj U')))) ≪≫
      Functor.isoWhiskerLeft v₀ iq ≪≫ D.cartesianSection_base
  let hi : (π.comp σ).inverseImage ≅ 𝟭 (Sheaf (S.base.J.over V) A) :=
    Functor.isoWhiskerLeft
        (q.sheafPushforwardContinuous A (S.sourceTopology.over U') (S.base.J.over V)) eSheaf ≪≫
      Functor.sheafPushforwardContinuousComp' hbase A
        (S.base.J.over V) (S.sourceTopology.over U') (S.base.J.over V) ≪≫
      Functor.sheafPushforwardContinuousId A (S.base.J.over V)
  exact
    { continuous := hqCont
      cocontinuous := hqCocont
      projection := π
      projection_inverseImage := rfl
      projection_pushforward := rfl
      rightSection := σ
      section_inverseImage := rfl
      cartesianSectionFunctor := v
      cartesianSection_base := hbase
      cartesianSection_adjunction := adj
      cartesianSection_isCartesian := fun X =>
        D.cartesianSection_isCartesian ((Over.map (eqToHom h.symm)).obj X)
      cartesianSection_isContinuous := hvCont
      cartesianSection_isCocontinuous := hvCocont
      section_inverseImage_cartesian := eSheaf
      source_rightInverse_inverseImage := hi
      source_rightInverse_pushforward :=
        ((π.comp σ).adj.ofNatIsoLeft hi).rightAdjointUniq Adjunction.id }

section LocalizedOneMorphism

-- The situation is named `M` here rather than `S`: `subst_hom_lift` introduces a local named `S`
-- for the base object it substitutes, which would shadow the situation inside the proof below.
variable (M : MorphismSituation.{u₀, u₁, u₂, v₀, v₁, v₂, max w u₀ u₁ u₂ v₀ v₁ v₂})
  (U : M.source)

/-- **Stacks 06NW for the localized 1-morphism, continuity half.** `Over.post u` is continuous
for the localized inherited topologies: it is a 1-morphism of fibred categories from
`Over.forget U' ⋙ p'` to `Over.forget (u U') ⋙ p` over the base, and the topologies these two
inherit are the localizations of the inherited topologies. -/
theorem isContinuous_overPost_u :
    (Over.post M.u : Over U ⥤ Over (M.u.obj U)).IsContinuous
      (M.sourceTopology.over U) (M.totalTopology.over (M.u.obj U)) := by
  let q : Over (M.u.obj U) ⥤ M.base.C := Over.forget (M.u.obj U) ⋙ M.p
  let q' : Over U ⥤ M.base.C := Over.forget U ⋙ M.p'
  let v : Over U ⥤ Over (M.u.obj U) := Over.post M.u
  let : q.IsFibered := Functor.IsFibered.comp_functor (Over.forget (M.u.obj U)) M.p
  let : q'.IsFibered := Functor.IsFibered.comp_functor (Over.forget U) M.p'
  have hc : v ⋙ q = q' := by
    show (Over.post M.u ⋙ Over.forget (M.u.obj U)) ⋙ M.p = _
    rw [Over.post_forget_eq_forget_comp, Functor.assoc, M.isFibredOneMorphism.comp_eq]
  have hu : q'.IsFibredOneMorphism q v :=
    { comp_eq := hc
      map_isStronglyCartesian := by
        intro R T f X Y g hg
        subst_hom_lift q' f g
        have h := (Functor.isStronglyCartesian_overForget_comp_iff M.p' U g).1 hg
        have h' := M.isFibredOneMorphism.map_isStronglyCartesian
          (M.p'.map g.left) g.left h
        have hm : M.p.IsStronglyCartesian (M.p.map (M.u.map g.left)) (M.u.map g.left) :=
          Functor.isStronglyCartesian_map_self M.p (M.p'.map g.left) (M.u.map g.left)
        rw [← hc]
        exact (Functor.isStronglyCartesian_overForget_comp_iff M.p (M.u.obj U) (v.map g)).2 hm }
  simpa only [q, q', Functor.inheritedTopology_overForget_comp] using
    Functor.IsFibredOneMorphism.isContinuous_inheritedTopology M.base.J hu

end LocalizedOneMorphism

/-- The localized source projection factors through the localized 1-morphism followed by the
localized target projection, the comparison being induced by `u ⋙ p = p'`. -/
def sourceSliceProjectionComp :
    sourceSliceProjection S U' ≅
      (Over.post S.u : Over U' ⥤ Over (S.u.obj U')) ⋙
        (Over.post S.p : Over (S.u.obj U') ⥤ Over (S.p.obj (S.u.obj U'))) := by
  let e := (eqToIso S.isFibredOneMorphism.comp_eq).symm
  let ePost := Over.postCongr (X := U') e
  change (Over.post S.p' ⋙ Over.map (eqToHom (p'_obj_eq S U'))) ≅ _
  have he : eqToHom (p'_obj_eq S U') = e.hom.app U' := by
    simp [e]
  exact
    Functor.isoWhiskerLeft (Over.post S.p') (Over.mapCongr _ _ he) ≪≫ ePost ≪≫
      Over.postComp (X := U') S.u S.p

/-- The cartesian section functor of the source, followed by the localized 1-morphism, is the
cartesian section functor of the target. Both structure arrows are strongly cartesian over the
same morphism of the base, so the universal property produces a unique comparison, and that
comparison is natural because a cartesian arrow separates morphisms into its source. -/
private def cartesianSectionFunctorComp
    (E : SourceSliceSectionData S U' (p'_obj_eq S U'))
    (T : LocalizedProjectionSection
      ({ base := S.base, C := S.total, p := S.p, isFibered := S.pFibered } :
        FibredCategorySituation.{u₀, v₀, u₁, v₁,
          max w u₀ u₁ u₂ v₀ v₁ v₂}) (S.u.obj U')) :
    E.cartesianSectionFunctor ⋙ (Over.post S.u : Over U' ⥤ Over (S.u.obj U')) ≅
      T.cartesianSectionFunctor := by
  let q : Over U' ⥤ Over (S.u.obj U') := Over.post S.u
  let r : Over (S.u.obj U') ⥤ Over (S.p.obj (S.u.obj U')) := Over.post S.p
  let v := E.cartesianSectionFunctor
  let t := T.cartesianSectionFunctor
  let hbase : (v ⋙ q) ⋙ r ≅ 𝟭 (Over (S.p.obj (S.u.obj U'))) :=
    Functor.associator v q r ≪≫
      Functor.isoWhiskerLeft v (sourceSliceProjectionComp S U').symm ≪≫
      E.cartesianSection_base
  let bNat : (v ⋙ q) ⋙ r ≅ t ⋙ r := hbase ≪≫ T.cartesianSection_base.symm
  let αdata (X : Over (S.p.obj (S.u.obj U'))) :
      { i : (v ⋙ q).obj X ≅ t.obj X // r.map i.hom = bNat.hom.app X } := by
    let b : r.obj ((v ⋙ q).obj X) ≅ r.obj (t.obj X) := bNat.app X
    let e : S.p.obj ((v ⋙ q).obj X).left ≅ S.p.obj (t.obj X).left :=
      (Over.forget _).mapIso b
    have ht : S.p.IsStronglyCartesian (S.p.map (t.obj X).hom) (t.obj X).hom :=
      T.cartesianSection_isCartesian X
    have hv : S.p.IsStronglyCartesian
        (S.p.map ((v ⋙ q).obj X).hom) ((v ⋙ q).obj X).hom := by
      change S.p.IsStronglyCartesian
        ((S.u ⋙ S.p).map (v.obj X).hom) (S.u.map (v.obj X).hom)
      rw [S.isFibredOneMorphism.comp_eq]
      exact S.isFibredOneMorphism.map_isStronglyCartesian
        (S.p'.map (v.obj X).hom) (v.obj X).hom (E.cartesianSection_isCartesian X)
    have hb : S.p.map ((v ⋙ q).obj X).hom =
        e.hom ≫ S.p.map (t.obj X).hom := by
      rw [show e.hom = b.hom.left from rfl]
      simpa [r, Over.post] using (Over.w b.hom).symm
    let d : ((v ⋙ q).obj X).left ≅ (t.obj X).left :=
      Functor.IsStronglyCartesian.domainIsoOfBaseIso S.p (g := e) hb
        (t.obj X).hom ((v ⋙ q).obj X).hom
    have hd : d.hom ≫ (t.obj X).hom = ((v ⋙ q).obj X).hom := by
      change (Functor.IsStronglyCartesian.map S.p (S.p.map (t.obj X).hom)
        (t.obj X).hom hb ((v ⋙ q).obj X).hom) ≫
        (t.obj X).hom = ((v ⋙ q).obj X).hom
      exact Functor.IsStronglyCartesian.fac S.p (S.p.map (t.obj X).hom)
        (t.obj X).hom hb ((v ⋙ q).obj X).hom
    refine ⟨Over.isoMk d hd, ?_⟩
    apply Over.OverMorphism.ext
    change S.p.map d.hom = e.hom
    have h : S.p.IsHomLift e.hom d.hom :=
      Functor.IsStronglyCartesian.domainUniqueUpToIso_inv_isHomLift S.p hb _ _
    simpa using (IsHomLift.fac' S.p e.hom d.hom)
  let α (X : Over (S.p.obj (S.u.obj U'))) : (v ⋙ q).obj X ≅ t.obj X := (αdata X).1
  refine NatIso.ofComponents α (fun {X Y} f => ?_)
  have hα (Z : Over (S.p.obj (S.u.obj U'))) :
      r.map (α Z).hom = bNat.hom.app Z := (αdata Z).2
  have hr : r.map ((v ⋙ q).map f ≫ (α Y).hom) =
      r.map ((α X).hom ≫ t.map f) := by
    simp only [Functor.map_comp, hα]
    exact bNat.hom.naturality f
  apply Over.OverMorphism.ext
  let ψ₁ : ((v ⋙ q).obj X).left ⟶ (t.obj Y).left :=
    ((v ⋙ q).map f ≫ (α Y).hom).left
  let ψ₂ : ((v ⋙ q).obj X).left ⟶ (t.obj Y).left :=
    ((α X).hom ≫ t.map f).left
  change ψ₁ = ψ₂
  have hg : S.p.map ψ₁ = S.p.map ψ₂ := by
    simpa [ψ₁, ψ₂, r, Over.post] using congrArg Over.Hom.left hr
  have ht : S.p.IsStronglyCartesian (S.p.map (t.obj Y).hom) (t.obj Y).hom :=
    T.cartesianSection_isCartesian Y
  let : S.p.IsHomLift (S.p.map ψ₁) ψ₂ := by
    rw [hg]
    infer_instance
  exact Functor.IsStronglyCartesian.ext S.p (S.p.map (t.obj Y).hom) (t.obj Y).hom (S.p.map ψ₁)
    ((Over.w ((v ⋙ q).map f ≫ (α Y).hom)).trans
      (Over.w ((α X).hom ≫ t.map f)).symm)

/-- **The cartesian section functor of Stacks 08P9 for the source, over the slice at `p(u(U'))`.**
An object `V ⟶ p(u(U'))` of the slice of the base is sent to the source of the chosen strongly
cartesian lift, with target `U'`, of the corresponding morphism `V ⟶ p'(U')`. This is the slice
over which the localized target projection lives, so this functor is the one that pairs with the
cartesian section functor of the target. -/
@[no_expose]
def sourceSliceCartesianSectionFunctor : Over (S.p.obj (S.u.obj U')) ⥤ Over U' :=
  (sourceSliceSectionData S U' (p'_obj_eq S U')).cartesianSectionFunctor

/-- The localized source projection is continuous from the slice `C'/U'` to the slice of the base
at `p(u(U'))`. -/
theorem sourceSliceProjection_isContinuous :
    (sourceSliceProjection S U').IsContinuous
      (S.sourceTopology.over U') (S.base.J.over (S.p.obj (S.u.obj U'))) :=
  (sourceSliceSectionData S U' (p'_obj_eq S U')).continuous

/-- The localized source projection is cocontinuous from the slice `C'/U'` to the slice of the
base at `p(u(U'))`. -/
theorem sourceSliceProjection_isCocontinuous :
    (sourceSliceProjection S U').IsCocontinuous
      (S.sourceTopology.over U') (S.base.J.over (S.p.obj (S.u.obj U'))) :=
  (sourceSliceSectionData S U' (p'_obj_eq S U')).cocontinuous

/-- The cartesian section functor of the source is continuous, the chosen cartesian lifts of a
covering of `V` covering the lift of `V`. -/
theorem sourceSliceCartesianSection_isContinuous :
    (sourceSliceCartesianSectionFunctor S U').IsContinuous
      (S.base.J.over (S.p.obj (S.u.obj U'))) (S.sourceTopology.over U') :=
  (sourceSliceSectionData S U' (p'_obj_eq S U')).cartesianSection_isContinuous

/-- The cartesian section functor of the source is cocontinuous. -/
theorem sourceSliceCartesianSection_isCocontinuous :
    (sourceSliceCartesianSectionFunctor S U').IsCocontinuous
      (S.base.J.over (S.p.obj (S.u.obj U'))) (S.sourceTopology.over U') :=
  (sourceSliceSectionData S U' (p'_obj_eq S U')).cartesianSection_isCocontinuous

/-- **The cartesian section functor of the source is right adjoint to the localized source
projection.** This is what makes restriction along the cartesian lifts exact and injective
preserving. -/
@[no_expose]
def sourceSliceCartesianSection_adjunction :
    sourceSliceProjection S U' ⊣ sourceSliceCartesianSectionFunctor S U' :=
  (sourceSliceSectionData S U' (p'_obj_eq S U')).cartesianSection_adjunction

/-- The cartesian section functor of the source is a section of the localized source
projection. -/
@[no_expose]
def sourceSliceCartesianSection_base :
    sourceSliceCartesianSectionFunctor S U' ⋙ sourceSliceProjection S U' ≅
      𝟭 (Over (S.p.obj (S.u.obj U'))) :=
  (sourceSliceSectionData S U' (p'_obj_eq S U')).cartesianSection_base

/-- The structure arrow of the chosen lift is strongly cartesian for the source projection. -/
theorem sourceSliceCartesianSection_isCartesian (X : Over (S.p.obj (S.u.obj U'))) :
    S.p'.IsStronglyCartesian
      (S.p'.map ((sourceSliceCartesianSectionFunctor S U').obj X).hom)
      ((sourceSliceCartesianSectionFunctor S U').obj X).hom :=
  (sourceSliceSectionData S U' (p'_obj_eq S U')).cartesianSection_isCartesian X

/-- **The cartesian section functor of the source, followed by the localized 1-morphism, is the
cartesian section functor of the target.** This is `cartesianSectionFunctorComp` read at the
datum `sourceSliceSectionData` of Stacks 08P9 for the source. -/
@[no_expose]
def sourceSliceCartesianSectionFunctorComp
    (T : LocalizedProjectionSection
      ({ base := S.base, C := S.total, p := S.p, isFibered := S.pFibered } :
        FibredCategorySituation.{u₀, v₀, u₁, v₁,
          max w u₀ u₁ u₂ v₀ v₁ v₂}) (S.u.obj U')) :
    sourceSliceCartesianSectionFunctor S U' ⋙
        (Over.post S.u : Over U' ⥤ Over (S.u.obj U')) ≅
      T.cartesianSectionFunctor :=
  cartesianSectionFunctorComp S U' (sourceSliceSectionData S U' (p'_obj_eq S U')) T

private theorem nonempty_compatibleLocalizedSection :
    Nonempty (CompatibleLocalizedSection S U') := by
  let A := Type (max w u₀ u₁ u₂ v₀ v₁ v₂)
  let E := sourceSliceSectionData S U' (p'_obj_eq S U')
  let TS : FibredCategorySituation.{u₀, v₀, u₁, v₁, max w u₀ u₁ u₂ v₀ v₁ v₂} :=
    { base := S.base, C := S.total, p := S.p, isFibered := S.pFibered }
  let T := localizedProjectionSection TS (S.u.obj U')
  have huCont : (Over.post S.u : Over U' ⥤ Over (S.u.obj U')).IsContinuous
      (S.sourceTopology.over U') (S.totalTopology.over (S.u.obj U')) :=
    isContinuous_overPost_u S U'
  have huCocont : (Over.post S.u : Over U' ⥤ Over (S.u.obj U')).IsCocontinuous
      (S.sourceTopology.over U') (S.totalTopology.over (S.u.obj U')) :=
    inferInstance
  let q : Over U' ⥤ Over (S.u.obj U') := Over.post S.u
  let g : MorphismOfTopoi
      (Sheaf (S.sourceTopology.over U') A)
      (Sheaf (S.totalTopology.over (S.u.obj U')) A) :=
    { inverseImage := q.sheafPushforwardContinuous A
        (S.sourceTopology.over U') (S.totalTopology.over (S.u.obj U'))
      pushforward := q.sheafPushforwardCocontinuous A
        (S.sourceTopology.over U') (S.totalTopology.over (S.u.obj U'))
      adj := q.sheafAdjunctionCocontinuous A
        (S.sourceTopology.over U') (S.totalTopology.over (S.u.obj U'))
      preservesFiniteLimits := inferInstance }
  let v : Over (S.p.obj (S.u.obj U')) ⥤ Over U' := E.cartesianSectionFunctor
  let vₜ : Over (S.p.obj (S.u.obj U')) ⥤ Over (S.u.obj U') := T.cartesianSectionFunctor
  let : v.IsContinuous (S.base.J.over (S.p.obj (S.u.obj U')))
      (S.sourceTopology.over U') := E.cartesianSection_isContinuous
  let : vₜ.IsContinuous (S.base.J.over (S.p.obj (S.u.obj U')))
      (S.totalTopology.over (S.u.obj U')) := T.cartesianSection_isContinuous
  let ev : v ⋙ q ≅ vₜ := cartesianSectionFunctorComp S U' E T
  let hsection : (g.comp E.rightSection).inverseImage ≅ T.projection.pushforward :=
    Functor.isoWhiskerLeft g.inverseImage E.section_inverseImage_cartesian ≪≫
      Functor.sheafPushforwardContinuousComp' ev A
        (S.base.J.over (S.p.obj (S.u.obj U')))
        (S.sourceTopology.over U') (S.totalTopology.over (S.u.obj U')) ≪≫
      T.rightSection_inverseImage_cartesian.symm ≪≫
      eqToIso T.rightSection_inverseImage
  let hi : (T.projection.comp (g.comp E.rightSection)).inverseImage ≅
      𝟭 (Sheaf (S.base.J.over (S.p.obj (S.u.obj U'))) A) :=
    Functor.isoWhiskerLeft T.projection.inverseImage hsection ≪≫
      eqToIso (by rw [← T.rightSection_inverseImage]; rfl) ≪≫
      T.rightSection_rightInverse_inverseImage
  exact
    ⟨{ sourceContinuous := E.continuous
       sourceCocontinuous := E.cocontinuous
       totalContinuous := T.isContinuous
       totalCocontinuous := T.isCocontinuous
       morphismContinuous := huCont
       morphismCocontinuous := huCocont
       sourceProjection := E.projection
       totalProjection := T.projection
       localizedMorphism := g
       sourceProjection_inverseImage := E.projection_inverseImage
       sourceProjection_pushforward := E.projection_pushforward
       totalProjection_inverseImage := T.projection_inverseImage
       totalProjection_pushforward := T.projection_pushforward
       localizedMorphism_inverseImage := rfl
       localizedMorphism_pushforward := rfl
       rightSection := E.rightSection
       section_inverseImage := E.section_inverseImage
       section_to_total_inverseImage := hsection
       source_rightInverse_inverseImage := E.source_rightInverse_inverseImage
       source_rightInverse_pushforward := E.source_rightInverse_pushforward
       total_rightInverse_inverseImage := hi
       total_rightInverse_pushforward :=
         ((T.projection.comp (g.comp E.rightSection)).adj.ofNatIsoLeft hi).rightAdjointUniq
           Adjunction.id }⟩

/-- **Stacks 08PB.** The localized projections of a 1-morphism of fibred categories admit a
common section: a morphism of topoi `σ' : Sh(D/V) ⟶ Sh(C'/U')` with `π'_{U'} ∘ σ' = id` and
`(σ')^{-1} = π'_{U',*}`, whose composite `σ = g' ∘ σ'` satisfies `π_U ∘ σ = id` and
`σ^{-1} = π_{U,*}`. -/
@[stacks 08PB]
def compatibleLocalizedSection : CompatibleLocalizedSection S U' :=
  Classical.choice (by exact nonempty_compatibleLocalizedSection S U')

end Stacks.Sites.FibredCategory.MorphismSituation

end
