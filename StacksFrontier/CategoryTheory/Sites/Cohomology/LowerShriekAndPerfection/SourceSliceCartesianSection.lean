module

public import StacksFrontier.CategoryTheory.Adjunction.UniqueCompHomEquiv
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.RingedToposOfAMorphism
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriekAndPerfection.FibredCategorySection
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriekAndPerfection.MorphismOfFibredCategoriesSection
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.Slice
public import StacksFrontier.CategoryTheory.Sites.Localization.LocalizationComposite
public import StacksFrontier.CategoryTheory.Sites.Localization.PushforwardAdjunction
public import StacksFrontier.CategoryTheory.Sites.Localization.PushforwardAdjunctionUnit
public import StacksFrontier.CategoryTheory.Sites.CocontinuousRightAdjointMorphismOfSites
import StacksCore.Tactic.StacksAttribute

/-!
# The cartesian section of the source slice and the localized lower shriek

Let `S` be a morphism situation of fibred categories over a site (Stacks 08PA) and let `U'` be
an object of the source.  The localized projection of the source slice over `U'` onto the base
slice over `p(u(U'))` has a cartesian section, left adjoint to it (Stacks 08P9), and that section
followed by `Over.post u` is the cartesian section of the target slice
(`MorphismSituation.cartesianSectionFunctorComp` in the proof of Stacks 08PB).  These are 2-cells
and adjunctions of categories, so restriction along them is an adjunction at any coefficients,
and composing the three identifies the localized `g'_!` of the source projection with the
inverse image along the target projection.

## Main definitions

* `Stacks.Sites.FibredCategory.MorphismSituation.localizedLowerShriekSourceProjectionIso`: the
  localized lower shriek of the source projection is restriction along the target cartesian
  section, at any coefficients.

## Main results

All names below are in the namespace `Stacks.Sites.FibredCategory.MorphismSituation`.

* `homEquiv_localizedLowerShriekSourceProjectionIso_hom_app_comp_of_unit`: the adjoint
  transpose of a component of that isomorphism.
* `overPullback_comp_sourceSliceProjection_eq`.

## Implementation notes

The construction of the cartesian section is carried out again here, privately, with one more
recorded property than in `MorphismOfFibredCategoriesSection.lean`: the counit of the
cartesian-section adjunction is the base comparison isomorphism, which is what the transpose
computations need.

## References

* [Stacks Project, Tag 08P9](https://stacks.math.columbia.edu/tag/08P9)
* [Stacks Project, Tag 08PB](https://stacks.math.columbia.edu/tag/08PB)
* [Stacks Project, Tag 08PC](https://stacks.math.columbia.edu/tag/08PC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits

namespace Stacks.Sites.FibredCategory.MorphismSituation

universe u₀ u₁ u₂ v₀ v₁ v₂ w

variable (S : MorphismSituation.{u₀, u₁, u₂, v₀, v₁, v₂, max w u₀ u₁ u₂ v₀ v₁ v₂})
  (U' : S.source)

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
  cartesianSection_counit : cartesianSection_adjunction.counit = cartesianSection_base.hom
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
    have : q₀.IsContinuous (S.sourceTopology.over U') (S.base.J.over (S.p'.obj U')) :=
      D.isContinuous
    exact Functor.isContinuous_comp q₀ (Over.map (eqToHom h))
      (S.sourceTopology.over U') (S.base.J.over (S.p'.obj U')) (S.base.J.over V)
  have hqCocont : q.IsCocontinuous (S.sourceTopology.over U') (S.base.J.over V) := by
    have : q₀.IsCocontinuous (S.sourceTopology.over U') (S.base.J.over (S.p'.obj U')) :=
      D.isCocontinuous
    exact CategoryTheory.isCocontinuous_comp q₀ (Over.map (eqToHom h))
      (S.sourceTopology.over U') (S.base.J.over (S.p'.obj U'))
  have hvCont : v.IsContinuous (S.base.J.over V) (S.sourceTopology.over U') := by
    have : D.cartesianSectionFunctor.IsContinuous
        (S.base.J.over (S.p'.obj U')) (S.sourceTopology.over U') :=
      D.cartesianSection_isContinuous
    exact Functor.isContinuous_comp (Over.map (eqToHom h.symm)) D.cartesianSectionFunctor
      (S.base.J.over V) (S.base.J.over (S.p'.obj U')) (S.sourceTopology.over U')
  have hvCocont : v.IsCocontinuous (S.base.J.over V) (S.sourceTopology.over U') := by
    have : D.cartesianSectionFunctor.IsCocontinuous
        (S.base.J.over (S.p'.obj U')) (S.sourceTopology.over U') :=
      D.cartesianSection_isCocontinuous
    exact CategoryTheory.isCocontinuous_comp (Over.map (eqToHom h.symm))
      D.cartesianSectionFunctor (S.base.J.over V) (S.base.J.over (S.p'.obj U'))
  let adj : q ⊣ v := D.cartesianSection_adjunction.comp e.toAdjunction
  -- The counit of the transported adjunction is the transport of the counit, which by
  -- `cartesianSection_counit` is the comparison isomorphism on the base slice; so the
  -- transported comparison can be *defined* as that counit, and the new field is `rfl`.
  haveI (X : Over V) : IsIso (adj.counit.app X) := by
    change IsIso ((D.cartesianSection_adjunction.comp e.toAdjunction).counit.app X)
    rw [Adjunction.comp_counit_app, D.cartesianSection_counit,
      Equivalence.toAdjunction_counit]
    infer_instance
  haveI : IsIso adj.counit := NatIso.isIso_of_isIso_app _
  let hbase : v ⋙ q ≅ 𝟭 (Over V) := asIso adj.counit
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
      cartesianSection_counit := rfl
      cartesianSection_isCartesian X :=
        D.cartesianSection_isCartesian ((Over.map (eqToHom h.symm)).obj X)
      cartesianSection_isContinuous := hvCont
      cartesianSection_isCocontinuous := hvCocont
      section_inverseImage_cartesian := eSheaf
      source_rightInverse_inverseImage := hi
      source_rightInverse_pushforward :=
        ((π.comp σ).adj.ofNatIsoLeft hi).rightAdjointUniq (Adjunction.id) }

/-- **The comparison of cartesian sections, read on the base slice.** The source cartesian
section followed by the localized 1-morphism and then projected to the base is the identity —
by `sourceSliceProjectionComp` and the source's own base comparison — and so is the target
cartesian section projected to the base, by *its* base comparison. This isomorphism between the
two projections is what the universal property of a cartesian lift turns into
`cartesianSectionFunctorComp`, and
`post_map_cartesianSectionFunctorComp_hom_app` records that it does. -/
private def cartesianSectionFunctorCompBase
    (E : SourceSliceSectionData S U' (p'_obj_eq S U'))
    (T : LocalizedProjectionSection
      ({ base := S.base, C := S.total, p := S.p, isFibered := S.pFibered } :
        FibredCategorySituation.{u₀, v₀, u₁, v₁,
          max w u₀ u₁ u₂ v₀ v₁ v₂}) (S.u.obj U')) :
    (E.cartesianSectionFunctor ⋙ (Over.post S.u : Over U' ⥤ Over (S.u.obj U'))) ⋙
        (Over.post S.p : Over (S.u.obj U') ⥤ Over (S.p.obj (S.u.obj U'))) ≅
      T.cartesianSectionFunctor ⋙
        (Over.post S.p : Over (S.u.obj U') ⥤ Over (S.p.obj (S.u.obj U'))) :=
  Functor.associator E.cartesianSectionFunctor
      (Over.post S.u : Over U' ⥤ Over (S.u.obj U'))
      (Over.post S.p : Over (S.u.obj U') ⥤ Over (S.p.obj (S.u.obj U'))) ≪≫
    Functor.isoWhiskerLeft E.cartesianSectionFunctor (sourceSliceProjectionComp S U').symm ≪≫
    E.cartesianSection_base ≪≫ T.cartesianSection_base.symm

/-- The component of `cartesianSectionFunctorComp` at a single object, together with the
property that pins it: it projects to the component of `cartesianSectionFunctorCompBase`.

Both structure arrows are strongly cartesian over the same morphism of the base — on the source
side because a 1-morphism of fibred categories carries cartesian lifts to cartesian lifts — so
the universal property produces the isomorphism and the projection equation at once. -/
private def cartesianSectionFunctorCompApp
    (E : SourceSliceSectionData S U' (p'_obj_eq S U'))
    (T : LocalizedProjectionSection
      ({ base := S.base, C := S.total, p := S.p, isFibered := S.pFibered } :
        FibredCategorySituation.{u₀, v₀, u₁, v₁,
          max w u₀ u₁ u₂ v₀ v₁ v₂}) (S.u.obj U'))
    (X : Over (S.p.obj (S.u.obj U'))) :
    { i : (E.cartesianSectionFunctor ⋙
          (Over.post S.u : Over U' ⥤ Over (S.u.obj U'))).obj X ≅
        T.cartesianSectionFunctor.obj X //
      (Over.post S.p : Over (S.u.obj U') ⥤ Over (S.p.obj (S.u.obj U'))).map i.hom =
        (cartesianSectionFunctorCompBase S U' E T).hom.app X } := by
  let q : Over U' ⥤ Over (S.u.obj U') := Over.post S.u
  let r : Over (S.u.obj U') ⥤ Over (S.p.obj (S.u.obj U')) := Over.post S.p
  let v := E.cartesianSectionFunctor
  let t := T.cartesianSectionFunctor
  let bNat : (v ⋙ q) ⋙ r ≅ t ⋙ r := cartesianSectionFunctorCompBase S U' E T
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
  have hd : d.hom ≫ (t.obj X).hom = ((v ⋙ q).obj X).hom :=
    Functor.IsStronglyCartesian.fac S.p (S.p.map (t.obj X).hom)
      (t.obj X).hom hb ((v ⋙ q).obj X).hom
  refine ⟨Over.isoMk d hd, ?_⟩
  apply Over.OverMorphism.ext
  change S.p.map d.hom = e.hom
  have : S.p.IsHomLift e.hom d.hom := by
    dsimp [d]
    infer_instance
  simpa using (IsHomLift.fac' S.p e.hom d.hom)

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
  let bNat : (v ⋙ q) ⋙ r ≅ t ⋙ r := cartesianSectionFunctorCompBase S U' E T
  let α (X : Over (S.p.obj (S.u.obj U'))) : (v ⋙ q).obj X ≅ t.obj X :=
    (cartesianSectionFunctorCompApp S U' E T X).1
  refine NatIso.ofComponents α (fun {X Y} f => ?_)
  have hα (Z : Over (S.p.obj (S.u.obj U'))) :
      r.map (α Z).hom = bNat.hom.app Z := (cartesianSectionFunctorCompApp S U' E T Z).2
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
  have : S.p.IsHomLift (S.p.map ψ₁) ψ₂ := by
    rw [hg]
    infer_instance
  exact Functor.IsStronglyCartesian.ext S.p (S.p.map (t.obj Y).hom) (t.obj Y).hom (S.p.map ψ₁)
    ((Over.w ((v ⋙ q).map f ≫ (α Y).hom)).trans (Over.w ((α X).hom ≫ t.map f)).symm)

/-- **What pins the Stacks 08PB comparison of cartesian sections**: projected to the base slice
it is `cartesianSectionFunctorCompBase`, the comparison the universal property was fed.

Spelled out, and with `cartesianSection_counit` reading the two base comparisons as the counits
of the two adjunctions, this is the 2-cell identity that the compatibility hypothesis of
`CategoryTheory.Adjunction.leftAdjointUniq_comp_ofNatIsoRight_hom_app_of_unit` asks for at this
situation; see `sourceSliceProjectionComp_counit_compat`. -/
private theorem post_map_cartesianSectionFunctorComp_hom_app
    (E : SourceSliceSectionData S U' (p'_obj_eq S U'))
    (T : LocalizedProjectionSection
      ({ base := S.base, C := S.total, p := S.p, isFibered := S.pFibered } :
        FibredCategorySituation.{u₀, v₀, u₁, v₁,
          max w u₀ u₁ u₂ v₀ v₁ v₂}) (S.u.obj U'))
    (X : Over (S.p.obj (S.u.obj U'))) :
    (Over.post S.p : Over (S.u.obj U') ⥤ Over (S.p.obj (S.u.obj U'))).map
        ((cartesianSectionFunctorComp S U' E T).hom.app X) =
      (cartesianSectionFunctorCompBase S U' E T).hom.app X :=
  (cartesianSectionFunctorCompApp S U' E T X).2

/-- **The 2-cell identity on the base slice that the mate-form of Stacks 08PB rests on.** The
counit of the target cartesian section's adjunction, at an object of the base slice, is the
counit of the source's read back along the Stacks 08PB comparison of the two cartesian sections
and along the factorisation `sourceSliceProjectionComp` of the localized source projection.

This is `post_map_cartesianSectionFunctorComp_hom_app` with the two base comparisons replaced by
the two counits — which is what `LocalizedProjectionSection.cartesianSection_counit` and
`SourceSliceSectionData.cartesianSection_counit` record — and the composite rearranged so that
the target counit stands alone. Nothing else about either adjunction is used, which is the whole
point: both come from `Classical.choice`. -/
private theorem sourceSliceProjectionComp_counit_compat
    (E : SourceSliceSectionData S U' (p'_obj_eq S U'))
    (T : LocalizedProjectionSection
      ({ base := S.base, C := S.total, p := S.p, isFibered := S.pFibered } :
        FibredCategorySituation.{u₀, v₀, u₁, v₁,
          max w u₀ u₁ u₂ v₀ v₁ v₂}) (S.u.obj U'))
    (X : Over (S.p.obj (S.u.obj U'))) :
    (Over.post S.p : Over (S.u.obj U') ⥤ Over (S.p.obj (S.u.obj U'))).map
          ((cartesianSectionFunctorComp S U' E T).inv.app X) ≫
        (sourceSliceProjectionComp S U').inv.app (E.cartesianSectionFunctor.obj X) ≫
          E.cartesianSection_adjunction.counit.app X =
      T.cartesianSection_adjunction.counit.app X := by
  rw [E.cartesianSection_counit, T.cartesianSection_counit]
  have key : (sourceSliceProjectionComp S U').inv.app (E.cartesianSectionFunctor.obj X) ≫
      E.cartesianSection_base.hom.app X =
      (Over.post S.p : Over (S.u.obj U') ⥤ Over (S.p.obj (S.u.obj U'))).map
          ((cartesianSectionFunctorComp S U' E T).hom.app X) ≫
        T.cartesianSection_base.hom.app X := by
    rw [post_map_cartesianSectionFunctorComp_hom_app]
    simp [cartesianSectionFunctorCompBase]
  rw [key, ← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-! ## The localized lower shriek of an inverse image from the base -/

universe ua va

attribute [instance] sourceSliceProjection_isContinuous

/-- The localized target projection `π_U : C/u(U') ⥤ D/p(u(U'))` is continuous. -/
instance isContinuous_overPostProjection :
    (Over.post S.p : Over (S.u.obj U') ⥤ Over (S.p.obj (S.u.obj U'))).IsContinuous
      (S.totalTopology.over (S.u.obj U')) (S.base.J.over (S.p.obj (S.u.obj U'))) :=
  (localizedProjectionSection
    ({ base := S.base, C := S.total, p := S.p, isFibered := S.pFibered } :
      FibredCategorySituation.{u₀, v₀, u₁, v₁, max w u₀ u₁ u₂ v₀ v₁ v₂})
    (S.u.obj U')).isContinuous

-- Continuity of the localized 1-morphism is already proved above; the statement below needs it
-- as an instance, and no second copy of it is introduced.
attribute [instance] isContinuous_overPost_u

/-- **The localized lower shriek carries an inverse image from the base to the inverse image
from the base**: for sheaves with values in any category `A`,

`g'_! ∘ (π'_{U'})^{-1} ≅ (π_U)^{-1}`,

where `g'_!` is the left adjoint of restriction along the localized 1-morphism `Over.post u` and
the two inverse images are restriction along the localized projections. Taking `A` to be abelian
groups and evaluating at the localized structure sheaf `O_{p(u(U'))}` gives
`(g')_!^{Ab} O_{U'} ≅ O_U`, which is the statement that the proof of Stacks 08PC (2) reduces the
commutation of lower shriek with the forgetful functor to.

The proof is the Hom-chain of the source, read as a composition of adjunctions. Restriction along
the localized source projection is left adjoint to restriction along its cartesian section, and
likewise for the target, by Stacks 08P9 and
`CategoryTheory.Adjunction.sheafPushforwardAdjunction`; `g'_!` is left adjoint to restriction
along `Over.post u`. Composing the first and third exhibits `g'_! ∘ (π'_{U'})^{-1}` as a left
adjoint of restriction along the source cartesian section followed by `Over.post u`, which by
`cartesianSectionFunctorComp` — the content of Stacks 08PB — is the target cartesian section. So
it is a left adjoint of the same functor as `(π_U)^{-1}`, and left adjoints are unique.

Only continuity of the four functors is used; neither cocontinuity nor the right Kan extensions
of the morphisms of topoi above enter, which is why the conclusion holds at arbitrary
coefficients.

The body is not exposed: it is built from the file-private witness of Stacks 08PB. -/
@[no_expose]
noncomputable def localizedLowerShriekSourceProjectionIso (A : Type ua) [Category.{va} A]
    [((Over.post S.u : Over U' ⥤ Over (S.u.obj U')).sheafPushforwardContinuous A
      (S.sourceTopology.over U') (S.totalTopology.over (S.u.obj U'))).IsRightAdjoint] :
    (sourceSliceProjection S U').sheafPushforwardContinuous A
        (S.sourceTopology.over U') (S.base.J.over (S.p.obj (S.u.obj U'))) ⋙
      (Over.post S.u : Over U' ⥤ Over (S.u.obj U')).sheafPullback A
        (S.sourceTopology.over U') (S.totalTopology.over (S.u.obj U')) ≅
      (Over.post S.p :
          Over (S.u.obj U') ⥤ Over (S.p.obj (S.u.obj U'))).sheafPushforwardContinuous A
        (S.totalTopology.over (S.u.obj U')) (S.base.J.over (S.p.obj (S.u.obj U'))) := by
  let E := sourceSliceSectionData S U' (p'_obj_eq S U')
  let T := localizedProjectionSection
    ({ base := S.base, C := S.total, p := S.p, isFibered := S.pFibered } :
      FibredCategorySituation.{u₀, v₀, u₁, v₁, max w u₀ u₁ u₂ v₀ v₁ v₂}) (S.u.obj U')
  letI : E.cartesianSectionFunctor.IsContinuous
      (S.base.J.over (S.p.obj (S.u.obj U'))) (S.sourceTopology.over U') :=
    E.cartesianSection_isContinuous
  letI : T.cartesianSectionFunctor.IsContinuous
      (S.base.J.over (S.p.obj (S.u.obj U'))) (S.totalTopology.over (S.u.obj U')) :=
    T.cartesianSection_isContinuous
  exact (((E.cartesianSection_adjunction.sheafPushforwardAdjunction
          (J := S.sourceTopology.over U')
          (K := S.base.J.over (S.p.obj (S.u.obj U'))) A).comp
        ((Over.post S.u : Over U' ⥤ Over (S.u.obj U')).sheafAdjunctionContinuous A
          (S.sourceTopology.over U') (S.totalTopology.over (S.u.obj U')))).ofNatIsoRight
      (Functor.sheafPushforwardContinuousComp' (cartesianSectionFunctorComp S U' E T) A
        (S.base.J.over (S.p.obj (S.u.obj U'))) (S.sourceTopology.over U')
        (S.totalTopology.over (S.u.obj U')))).leftAdjointUniq
    (T.cartesianSection_adjunction.sheafPushforwardAdjunction
      (J := S.totalTopology.over (S.u.obj U'))
      (K := S.base.J.over (S.p.obj (S.u.obj U'))) A)

/-- The cartesian section of the localized source projection is continuous. -/
private instance isContinuous_sourceSliceCartesianSection :
    ((sourceSliceSectionData S U' (p'_obj_eq S U')).cartesianSectionFunctor).IsContinuous
      (S.base.J.over (S.p.obj (S.u.obj U'))) (S.sourceTopology.over U') :=
  (sourceSliceSectionData S U' (p'_obj_eq S U')).cartesianSection_isContinuous

/-- The cartesian section of the localized source projection is cocontinuous. Recorded beside
`isContinuous_sourceSliceCartesianSection` because the Stacks 08P9 datum it is read off is
file-private, so no consumer can produce it: restriction along the section is right exact only
through this, and that right exactness is what
`MorphismSituation.sourceCartesianLiftRestriction` needs. -/
private instance isCocontinuous_sourceSliceCartesianSection :
    ((sourceSliceSectionData S U' (p'_obj_eq S U')).cartesianSectionFunctor).IsCocontinuous
      (S.base.J.over (S.p.obj (S.u.obj U'))) (S.sourceTopology.over U') :=
  (sourceSliceSectionData S U' (p'_obj_eq S U')).cartesianSection_isCocontinuous

/-- **The cartesian section of the localized source projection sends the terminal object of
`D/p(u(U'))` back to `U'`.** Its value at `𝟙 : p(u(U')) ⟶ p(u(U'))` is a strongly cartesian
morphism of `C'` lying over an isomorphism of the base, hence is itself an isomorphism.

Recorded here, beside the section, because the cartesian and base-comparison fields of the
Stacks 08P9 datum are file-private; the Stacks 0D6X argument of
`MorphismSituation.subsingleton_ext_extensionByZeroUnitAb_abelianInverseImage` reads morphisms
out of `j_{U'!} ℤ_{U'}` as the value of restriction along the section at that terminal object,
and needs exactly this identification.

The body is not exposed: it is built from the file-private witness of Stacks 08P9 for the
source. -/
@[no_expose]
private def sourceSliceCartesianSectionObjIso :
    (((sourceSliceSectionData S U' (p'_obj_eq S U')).cartesianSectionFunctor).obj
      (Over.mk (𝟙 (S.p.obj (S.u.obj U'))))).left ≅ U' := by
  let E := sourceSliceSectionData S U' (p'_obj_eq S U')
  let T : Over (S.p.obj (S.u.obj U')) := Over.mk (𝟙 (S.p.obj (S.u.obj U')))
  let e := E.cartesianSection_base.app T
  have he : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  have hw : e.hom.left =
      S.p'.map ((E.cartesianSectionFunctor.obj T).hom) ≫ eqToHom (p'_obj_eq S U') := by
    simpa [T, e, sourceSliceProjectionAt, Over.post] using Over.w e.hom
  haveI : IsIso (S.p'.map ((E.cartesianSectionFunctor.obj T).hom) ≫
    eqToHom (p'_obj_eq S U')) := hw ▸ he
  haveI : IsIso (S.p'.map ((E.cartesianSectionFunctor.obj T).hom)) :=
    IsIso.of_isIso_comp_right _ (eqToHom (p'_obj_eq S U'))
  haveI := E.cartesianSection_isCartesian T
  haveI : IsIso ((E.cartesianSectionFunctor.obj T).hom) :=
    Functor.IsStronglyCartesian.isIso_of_base_isIso S.p'
      (S.p'.map ((E.cartesianSectionFunctor.obj T).hom)) _
  exact asIso (E.cartesianSectionFunctor.obj T).hom

/-- **The localized source projection is left adjoint to its cartesian section**, part of the
Stacks 08P9 datum for the source: `π'_{U'} ⊣ σ'`. The body is not exposed, the datum being the
file-private witness. -/
@[no_expose]
private def sourceSliceCartesianSectionAdjunction :
    sourceSliceProjection S U' ⊣
      (sourceSliceSectionData S U' (p'_obj_eq S U')).cartesianSectionFunctor :=
  (sourceSliceSectionData S U' (p'_obj_eq S U')).cartesianSection_adjunction

/-- **Stacks 08PB as a comparison of cartesian sections.** The cartesian section of the
localized source projection, followed by the localized 1-morphism, is the cartesian section of
the localized target projection:

`σ' ⋙ Over.post u ≅ σ_U`.

Both structure arrows are strongly cartesian over the same morphism of the base, so the
universal property produces the comparison; that is the content of the tag. The body is not
exposed: it is built from the file-private witnesses of both sections. -/
@[no_expose]
private def sourceSliceCartesianSectionComp :
    (sourceSliceSectionData S U' (p'_obj_eq S U')).cartesianSectionFunctor ⋙
        (Over.post S.u : Over U' ⥤ Over (S.u.obj U')) ≅
      (localizedProjectionSection
        ({ base := S.base, C := S.total, p := S.p, isFibered := S.pFibered } :
          FibredCategorySituation.{u₀, v₀, u₁, v₁,
            max w u₀ u₁ u₂ v₀ v₁ v₂}) (S.u.obj U')).cartesianSectionFunctor :=
  cartesianSectionFunctorComp S U' (sourceSliceSectionData S U' (p'_obj_eq S U'))
    (localizedProjectionSection
      ({ base := S.base, C := S.total, p := S.p, isFibered := S.pFibered } :
        FibredCategorySituation.{u₀, v₀, u₁, v₁,
          max w u₀ u₁ u₂ v₀ v₁ v₂}) (S.u.obj U'))

/-- The cartesian section of the localized target projection is continuous. -/
private instance isContinuous_targetSliceCartesianSection :
    (localizedProjectionSection
        ({ base := S.base, C := S.total, p := S.p, isFibered := S.pFibered } :
          FibredCategorySituation.{u₀, v₀, u₁, v₁,
            max w u₀ u₁ u₂ v₀ v₁ v₂}) (S.u.obj U')).cartesianSectionFunctor.IsContinuous
      (S.base.J.over (S.p.obj (S.u.obj U'))) (S.totalTopology.over (S.u.obj U')) :=
  (localizedProjectionSection
    ({ base := S.base, C := S.total, p := S.p, isFibered := S.pFibered } :
      FibredCategorySituation.{u₀, v₀, u₁, v₁,
        max w u₀ u₁ u₂ v₀ v₁ v₂}) (S.u.obj U')).cartesianSection_isContinuous

/-- **The adjoint transpose of a component of the Stacks 08PB comparison.**

`localizedLowerShriekSourceProjectionIso` compares the two left adjoints
`(π'_{U'})^{-1} ⋙ g'_!` and `(π_U)^{-1}` of restriction along the target cartesian section — the
first of them as a composite of two adjunctions, with its right adjoint read through Stacks
08PB. So for a morphism `g` out of `(π_U)^{-1} Z` the transpose, under the *outer* adjunction of
that composite — the one of the localized 1-morphism `Over.post u` — of its component at `Z`
followed by `g` is the inverse transpose, under the adjunction of the source cartesian section,
of the transpose of `g` under the target one, read back along Stacks 08PB. That is
`CategoryTheory.Adjunction.homEquiv_leftAdjointUniq_comp_ofNatIsoRight_hom_app_comp`.

**This has to be stated here.** `localizedLowerShriekSourceProjectionIso` is `@[no_expose]`, its
body being built from the file-private witnesses of Stacks 08P9 and 08PB, so outside this module
the definition is opaque: nothing can see the `CategoryTheory.Adjunction.leftAdjointUniq` that
it is, `unfold` fails on it by measurement, and the general transpose lemma has nothing to match
against. Inside this module the body is visible and the computation is that lemma applied.

Stating it is what forces the source cartesian section, its adjunction and
`sourceSliceCartesianSectionComp` to be named at all: the value of the transpose is an
expression in exactly those three, which before this were available only as fields of the
private witness. -/
private theorem homEquiv_localizedLowerShriekSourceProjectionIso_hom_app_comp (A : Type ua)
    [Category.{va} A]
    [((Over.post S.u : Over U' ⥤ Over (S.u.obj U')).sheafPushforwardContinuous A
      (S.sourceTopology.over U') (S.totalTopology.over (S.u.obj U'))).IsRightAdjoint]
    (Z : Sheaf (S.base.J.over (S.p.obj (S.u.obj U'))) A)
    {Y : Sheaf (S.totalTopology.over (S.u.obj U')) A}
    (g : ((Over.post S.p :
        Over (S.u.obj U') ⥤ Over (S.p.obj (S.u.obj U'))).sheafPushforwardContinuous A
        (S.totalTopology.over (S.u.obj U'))
        (S.base.J.over (S.p.obj (S.u.obj U')))).obj Z ⟶ Y) :
    ((Over.post S.u : Over U' ⥤ Over (S.u.obj U')).sheafAdjunctionContinuous A
        (S.sourceTopology.over U') (S.totalTopology.over (S.u.obj U'))).homEquiv
        (((sourceSliceProjection S U').sheafPushforwardContinuous A
          (S.sourceTopology.over U') (S.base.J.over (S.p.obj (S.u.obj U')))).obj Z) Y
        ((localizedLowerShriekSourceProjectionIso S U' A).hom.app Z ≫ g) =
      (((sourceSliceCartesianSectionAdjunction S U').sheafPushforwardAdjunction
            (J := S.sourceTopology.over U')
            (K := S.base.J.over (S.p.obj (S.u.obj U'))) A).homEquiv Z
          (((Over.post S.u : Over U' ⥤ Over (S.u.obj U')).sheafPushforwardContinuous A
            (S.sourceTopology.over U') (S.totalTopology.over (S.u.obj U'))).obj Y)).symm
        (((localizedProjectionSection
                ({ base := S.base, C := S.total, p := S.p, isFibered := S.pFibered } :
                  FibredCategorySituation.{u₀, v₀, u₁, v₁,
                    max w u₀ u₁ u₂ v₀ v₁ v₂})
                (S.u.obj U')).cartesianSection_adjunction.sheafPushforwardAdjunction
              (J := S.totalTopology.over (S.u.obj U'))
              (K := S.base.J.over (S.p.obj (S.u.obj U'))) A).homEquiv Z Y g ≫
          (Functor.sheafPushforwardContinuousComp' (sourceSliceCartesianSectionComp S U') A
            (S.base.J.over (S.p.obj (S.u.obj U'))) (S.sourceTopology.over U')
            (S.totalTopology.over (S.u.obj U'))).inv.app Y) :=
  Adjunction.homEquiv_leftAdjointUniq_comp_ofNatIsoRight_hom_app_comp _ _ _ _ _ _

/-- **The adjoint transpose of a component of the Stacks 08PB comparison, with neither chosen
adjunction in the answer.**

In the situation of `homEquiv_localizedLowerShriekSourceProjectionIso_hom_app_comp`, the
transpose is *also* equal to the restriction along the factorisation
`π'_{U'} ≅ Over.post u ⋙ π_{u(U')}` of the localized source projection, followed by restriction
along `Over.post u` of `g`. Neither cartesian section's adjunction occurs; and that is what makes
the statement usable, both coming from `Classical.choice`.

This is the `_of_unit` variant of
`CategoryTheory.Adjunction.homEquiv_leftAdjointUniq_comp_ofNatIsoRight_hom_app_comp`, whose
compatibility hypothesis on the two units is discharged by
`sourceSliceProjectionComp_counit_compat` — the 2-cell identity on the base slice that Stacks
08PB's comparison satisfies by construction — after
`CategoryTheory.Adjunction.sheafPushforwardAdjunction_unit_hom_app` computes both units as
restriction along the two site-level counits. -/
theorem homEquiv_localizedLowerShriekSourceProjectionIso_hom_app_comp_of_unit (A : Type ua)
    [Category.{va} A]
    [((Over.post S.u : Over U' ⥤ Over (S.u.obj U')).sheafPushforwardContinuous A
      (S.sourceTopology.over U') (S.totalTopology.over (S.u.obj U'))).IsRightAdjoint]
    (Z : Sheaf (S.base.J.over (S.p.obj (S.u.obj U'))) A)
    {Y : Sheaf (S.totalTopology.over (S.u.obj U')) A}
    (g : ((Over.post S.p :
        Over (S.u.obj U') ⥤ Over (S.p.obj (S.u.obj U'))).sheafPushforwardContinuous A
        (S.totalTopology.over (S.u.obj U'))
        (S.base.J.over (S.p.obj (S.u.obj U')))).obj Z ⟶ Y) :
    ((Over.post S.u : Over U' ⥤ Over (S.u.obj U')).sheafAdjunctionContinuous A
        (S.sourceTopology.over U') (S.totalTopology.over (S.u.obj U'))).homEquiv
        (((sourceSliceProjection S U').sheafPushforwardContinuous A
          (S.sourceTopology.over U') (S.base.J.over (S.p.obj (S.u.obj U')))).obj Z) Y
        ((localizedLowerShriekSourceProjectionIso S U' A).hom.app Z ≫ g) =
      (Functor.sheafPushforwardContinuousComp' (sourceSliceProjectionComp S U').symm A
            (S.sourceTopology.over U') (S.totalTopology.over (S.u.obj U'))
            (S.base.J.over (S.p.obj (S.u.obj U')))).inv.app Z ≫
        ((Over.post S.u : Over U' ⥤ Over (S.u.obj U')).sheafPushforwardContinuous A
          (S.sourceTopology.over U') (S.totalTopology.over (S.u.obj U'))).map g := by
  refine Adjunction.homEquiv_leftAdjointUniq_comp_ofNatIsoRight_hom_app_comp_of_unit
    _ _ _ _ _ ?_ Z g
  intro W
  refine Sheaf.hom_ext ?_
  ext Yop
  dsimp only [Functor.sheafPushforwardContinuous, ObjectProperty.lift]
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    Adjunction.sheafPushforwardAdjunction_unit_hom_app]
  simp only [id_obj, comp_obj, ObjectProperty.ι_obj, whiskeringLeft_obj_obj, op_obj,
    Functor.comp_map, ObjectProperty.ι_map, whiskeringLeft_obj_map, Opposite.op_unop,
    ObjectProperty.homMk_hom, whiskerLeft_app,
    sheafPushforwardContinuousComp'_inv_app_hom_app, Iso.symm_hom,
    sheafPushforwardContinuousComp'_hom_app_hom_app, op_map, Quiver.Hom.unop_op]
  rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp, Category.assoc,
    sourceSliceProjectionComp_counit_compat]

/-! ## The localized structure sheaves as restrictions from the base slice -/

/-- The localized source projection followed by the forgetful functor of the base slice is the
forgetful functor of the source slice followed by the source's structure functor:

`π'_{U'} ⋙ j_V = j_{U'} ⋙ p'`.

Both sides send an object `(X, X ⟶ U')` of `C'/U'` to `X` and a morphism of slices to its
underlying morphism, so this holds on the nose: the `Over.post` half is
`CategoryTheory.Over.post_forget_eq_forget_comp` and `Over.map` does not move the underlying
object at all, so the reindexing `Over.map (eqToHom (p'_obj_eq S U'))` that distinguishes
`sourceSliceProjection` from a bare `Over.post S.p'` is invisible after `Over.forget`. -/
private theorem sourceSliceProjection_comp_forget :
    sourceSliceProjection S U' ⋙ Over.forget (S.p.obj (S.u.obj U')) =
      Over.forget U' ⋙ S.p' :=
  rfl

/-- **The structure sheaf of the localized source is the restriction of the one on the base
slice.** For sheaves with values in any category `A`, restricting a sheaf on the base to the
base slice at `V = p(u(U'))` and then along the localized source projection *is* restricting it
along `p'` and then to the source slice at `U'`:

`(π'_{U'})^{-1} ∘ j_V^{-1} = j_{U'}^{-1} ∘ (π')^{-1}`.

Evaluated at the base structure sheaf — at `A = CommRingCat`, at `A = RingCat`, or at
`A = AddCommGrpCat` on an underlying abelian sheaf — this says that the structure sheaf
`O_{U'}` of the localized source is `(π'_{U'})^{-1} O_V`. That is one of the two inputs the
Stacks 08PC (2) reduction needs on top of `localizedLowerShriekSourceProjectionIso`: that
isomorphism produces `g'_!((π'_{U'})^{-1} F) ≅ (π_U)^{-1} F` for a sheaf `F` on the base slice,
and to read it as `g'_! O_{U'} ≅ O_U` both localized structure sheaves have to be exhibited as
restrictions of one and the same `F` — here `F = O_V`.

This is *not* `CategoryTheory.sheafPushforwardContinuous_overPost_eq`, which is the same
assertion for a bare `Over.post u` and is the input used below. The difference is the whole
reason this statement is needed: `sourceSliceProjection` is `Over.post S.p'` followed by
`Over.map (eqToHom (p'_obj_eq S U'))`, which transports the base slice from `p'(U')` to
`p(u(U'))`. Without that transport the source half of the reduction lands over a *different*
slice of the base from the target half, and the two cannot be compared; `p'_obj_eq` is exactly
the identification `p' = u ⋙ p` of the situation's `isFibredOneMorphism`.

Like its `Over.post` ancestor the equation is `rfl`: both sides are precomposition with the
opposite of one and the same functor `Over U' ⥤ D`, namely the one of
`sourceSliceProjection_comp_forget`.

The **target** half of the same statement — `(π_U)^{-1} ∘ j_V^{-1} = j_{u(U')}^{-1} ∘ π^{-1}` —
is deliberately not restated here: it is `sheafPushforwardContinuous_overPost_eq` at
`u := S.p` and `V := S.u.obj U'`, no reindexing being needed on that side, with
`isContinuous_overPostProjection` above discharging its continuity hypothesis. Natural-iso
packagings of the `Over.post` case are
`AlgebraicGeometry.RingedSite.MorphismLocalization.localizationComparisonIso` and
`CategoryTheory.sheafPullbackOverPostIso`; the `eqToIso` of the equation below plays that role
for the reindexed projection. -/
theorem overPullback_comp_sourceSliceProjection_eq (A : Type ua) [Category.{va} A] :
    S.base.J.overPullback A (S.p.obj (S.u.obj U')) ⋙
        (sourceSliceProjection S U').sheafPushforwardContinuous A
          (S.sourceTopology.over U') (S.base.J.over (S.p.obj (S.u.obj U'))) =
      S.p'.sheafPushforwardContinuous A S.sourceTopology S.base.J ⋙
        S.sourceTopology.overPullback A U' :=
  rfl

end Stacks.Sites.FibredCategory.MorphismSituation

end
