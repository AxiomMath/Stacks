module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalPresentationRestriction
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.JointlySurjectiveDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SiteEquivalenceAffine
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SubsiteLowerShriekQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Stacks.FibreEssentialSmallness
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStackTerminalSubsite
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasBridges
public import StacksFrontier.AlgebraicGeometry.Stacks.SubcategoryUnitLowerShriekAtlas
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsiteModuleShriekBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.EtaleLocalLifts

/-!
# `g_!` of a quasi-coherent module is quasi-coherent (Stacks 07B0)

Let `𝒳` be an algebraic stack and let `g` be the morphism of ringed topoi of **Stacks 0788**
attached to the inclusion of the lisse-étale site `𝒳_{lisse,étale}` into `𝒳_étale` (case (1)),
respectively of the flat-fppf site `𝒳_{flat,fppf}` into `𝒳_fppf` (case (2)), with `g_!` the
lower shriek on sheaves of modules of **Stacks 0789**. **Stacks 07B0** says that for every
quasi-coherent module `H` on the subsite, `g_!H` is a quasi-coherent module on `𝒳`.

## Main results

* `AlgebraicGeometry.Stack.LisseEtale.isQuasicoherentClause_fppf_moduleLowerShriek`:
  **Stacks 07B0** (1). For a quasi-coherent `O_{𝒳_{lisse,étale}}`-module `H`, the module `g_!H`
  is a sheaf for the fppf topology and is quasi-coherent on `(𝒳_fppf, O_𝒳)`, that is, it is a
  quasi-coherent module on `𝒳` in the sense of **Stacks 06WG**.
* `FlatFppf.isQuasicoherentOnSite_moduleLowerShriek_of_isQuasicoherentOnSite` (in the namespace
  `AlgebraicGeometry.Stack`): **Stacks 07B0** (2). For a quasi-coherent
  `O_{𝒳_{flat,fppf}}`-module `H`, `g_!H` is quasi-coherent on `(𝒳_fppf, O_𝒳)`.

## References

* [Stacks Project, Tag 0788](https://stacks.math.columbia.edu/tag/0788)
* [Stacks Project, Tag 0789](https://stacks.math.columbia.edu/tag/0789)
* [Stacks Project, Tag 078A](https://stacks.math.columbia.edu/tag/078A)
* [Stacks Project, Tag 06WG](https://stacks.math.columbia.edu/tag/06WG)
* [Stacks Project, Tag 06XH](https://stacks.math.columbia.edu/tag/06XH)
* [Stacks Project, Tag 07AT](https://stacks.math.columbia.edu/tag/07AT)
* [Stacks Project, Tag 07AZ](https://stacks.math.columbia.edu/tag/07AZ)
* [Stacks Project, Tag 07B0](https://stacks.math.columbia.edu/tag/07B0)
* [Stacks Project, Tag 0EM8](https://stacks.math.columbia.edu/tag/0EM8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u t

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- `g_!` carries a module presented by global sections to a module with a global presentation. -/
private theorem hasGlobalPresentation_subsiteModuleLowerShriek
    {X : Type (u + 1)} [Category.{u} X] (p : X ⥤ BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids) (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)
    (P : ObjectProperty X) [EssentiallySmall.{u} X]
    [P.ι.IsContinuous (subsiteTopology B S hS p τ P) (associatedTopology B S hS p τ)]
    [P.ι.IsCocontinuous (subsiteTopology B S hS p τ P) (associatedTopology B S hS p τ)]
    (hO : IsIso (subsiteUnitLowerShriekMap B S hS p hp τ hτ P))
    (H : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (subsiteRingedTopos B S hS p hp τ hτ P).O))
    (hH : H.IsPresentedByGlobalSections) :
    ((subsiteModuleLowerShriek B S hS p hp τ hτ P).obj H).HasGlobalPresentation := by
  have _ := isIso_subsiteModuleLowerShriekAdjunction_unit B S hS p hp τ hτ P
  have hff := Adjunction.fullyFaithfulLOfIsIsoUnit
    (subsiteModuleLowerShriekAdjunction B S hS p hp τ hτ P)
  have _ := hff.full
  have _ := hff.faithful
  have _ : PreservesColimitsOfSize.{u, u} (subsiteModuleLowerShriek B S hS p hp τ hτ P) :=
    Adjunction.leftAdjoint_preservesColimits
      (subsiteModuleLowerShriekAdjunction B S hS p hp τ hτ P)
  exact Stacks.SheafOfModules.hasGlobalPresentation_of_isPresentedByGlobalSections
    ((Stacks.Sheaves.GlobalTypeComparison.isPresentedByGlobalSections_iff
      (subsiteModuleLowerShriek B S hS p hp τ hτ P)
      (asIso (subsiteUnitLowerShriekMap B S hS p hp τ hτ P)) H).1 hH)

/-- If `H` is quasi-coherent and `M` has a global presentation over `F y` whenever `H` has one over
`y`, then the arrows into `F s` over which `M` has a global presentation cover `F s`. -/
private theorem presentedSieve_mem_of_isQuasicoherentOnSite
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D] (F : C ⥤ D)
    {K : GrothendieckTopology C} {J : GrothendieckTopology D} [F.IsContinuous K J]
    {R : Sheaf K RingCat.{u}} {R' : Sheaf J RingCat.{u}} (H : SheafOfModules.{u} R)
    (M : SheafOfModules.{u} R') (hH : H.IsQuasicoherentOnSite)
    (h : ∀ y, (H.over y).HasGlobalPresentation → (M.over (F.obj y)).HasGlobalPresentation)
    (s : C) : Stacks.SheafOfModules.presentedSieve M (F.obj s) ∈ J (F.obj s) := by
  obtain ⟨I, V, β, hcov, hpres⟩ := hH.locally_hasGlobalPresentation s
  refine J.superset_covering ?_ ((CoverPreserving.of_isContinuous F K J).cover_preserve hcov)
  rintro Z u ⟨A, c, g, hc, rfl⟩
  obtain ⟨i, b, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hc
  exact Stacks.SheafOfModules.GlobalPresentationTransport.hasGlobalPresentation_overMap M
    (g ≫ F.map b) (h _ (hpres i))

/-- If the singleton sieve of `α : y ⟶ x` is covering and `M` is presented over the covering sieve
of some `z` receiving a map from `y`, then `M` is presented over a covering sieve of `x`. -/
private theorem presentedSieve_mem_of_generate_singleton_mem
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    (M : SheafOfModules.{u} R) {x y z : C} (α : y ⟶ x) (g : y ⟶ z)
    (hα : Sieve.generate (Presieve.singleton α) ∈ J x)
    (hz : Stacks.SheafOfModules.presentedSieve M z ∈ J z) :
    Stacks.SheafOfModules.presentedSieve M x ∈ J x := by
  refine J.transitive hα _ ?_
  rintro W w ⟨Y, h, k, hk, rfl⟩
  cases hk
  rw [Stacks.SheafOfModules.presentedSieve_pullback]
  exact Stacks.SheafOfModules.presentedSieve_mem_of_hom M (h ≫ g) hz

/-! ### The lisse-étale site -/

namespace LisseEtale

variable (𝒳 : AlgebraicStacks.{u, t} B S hS)

attribute [local instance] isContinuous_inclusion' isCocontinuous_inclusion'

/-- Let `f : 𝒰 ⟶ 𝒳` be a smooth 1-morphism of algebraic stacks whose lisse-étale site has a final
object `T`, sent by `f` to an object isomorphic to a smooth object `y` of `𝒳`. If `H` is a sheaf of
`O_{𝒳_{lisse,étale}}`-modules whose restriction to the slice at `y` has a global presentation, then
so does the restriction of `g_!H` to the slice at `y` in `𝒳_étale`. -/
theorem hasGlobalPresentation_over_moduleLowerShriek_of_chart
    {𝒰 : AlgebraicStacks.{u, t} B S hS} (f : 𝒰 ⟶ 𝒳) (hf : AlgebraicStacks.IsSmooth B S hS f)
    {T : LisseEtale.{u, t} B S hS 𝒰} (hT : IsTerminal T) (y : LisseEtale.{u, t} B S hS 𝒳)
    (e : f.hom.hom.toFunctor.obj T.obj ≅ y.obj)
    (H : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos.{u, t} B S hS 𝒳
      (closedUnderSmoothMorphisms.{u, t} B S hS 𝒳)).O))
    (hH : (H.over y).HasGlobalPresentation) :
    (((moduleLowerShriek.{u, t} B S hS 𝒳).obj H).over y.obj).HasGlobalPresentation := by
  have := isContinuous_subsiteFunctor B S hS f hf
  have := isCocontinuous_subsiteFunctor B S hS f hf
  have h₁ : (H.over ((SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor
      (smoothObject.{u, t} B S hS 𝒰) (smoothObject_map.{u, t} B S hS f hf)).obj
        T)).HasGlobalPresentation :=
    Stacks.SheafOfModules.GlobalPresentationTransport.hasGlobalPresentation_overMap H
      (ObjectProperty.homMk e.hom) hH
  have h₂ := Stacks.SheafOfModules.hasGlobalPresentation_pushforward_of_isTerminal.{u + 1, u, u}
    (SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor
      (smoothObject.{u, t} B S hS 𝒰)
      (smoothObject_map.{u, t} B S hS f hf)) hT
    (subsiteRing_obj_eq B S hS f (etaleTopology B) (etaleTopology_le_topology B)
      (smoothObject.{u, t} B S hS 𝒰)
      (smoothObject.{u, t} B S hS 𝒳) (smoothObject_map.{u, t} B S hS f hf)) H h₁
  have h₃ :=
    Stacks.SheafOfModules.isPresentedByGlobalSections_of_hasGlobalPresentation_of_isTerminal hT h₂
  have h₅ := hasGlobalPresentation_subsiteModuleLowerShriek B S hS
    𝒰.val.val.p 𝒰.val.isFiberedInGroupoids (etaleTopology B) (etaleTopology_le_topology B)
    (smoothObject.{u, t} B S hS 𝒰) (isIso_unitLowerShriekMap_algebraicStack.{u, t} B S hS 𝒰) _ h₃
  have h₆ := SheafOfModules.HasGlobalPresentation.of_iso
    ((moduleShriekBaseChangeIso B S hS f hf).app H) h₅
  have h₇ := Stacks.SheafOfModules.hasGlobalPresentation_over _ T.obj h₆
  have h₈ := hasGlobalPresentation_of_modulePullback B S hS
    𝒰.val.val.p 𝒳.val.val.p
    𝒰.val.isFiberedInGroupoids 𝒳.val.isFiberedInGroupoids
    f.hom.hom.toFunctor (CatFiberedInGroupoids.homFunctor_comp_p f.hom) (etaleTopology B)
    (etaleTopology_le_topology B) _ T.obj h₇
  exact Stacks.SheafOfModules.GlobalPresentationTransport.hasGlobalPresentation_overMap _ e.inv h₈

/-- If `H` is a sheaf of `O_{𝒳_{lisse,étale}}`-modules whose restriction to the slice at a smooth
object `y` has a global presentation, then the restriction of `g_!H` to the slice at `y` in
`𝒳_étale` has a global presentation. -/
theorem hasGlobalPresentation_over_moduleLowerShriek
    (H : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos.{u, t} B S hS 𝒳
      (closedUnderSmoothMorphisms.{u, t} B S hS 𝒳)).O))
    (y : LisseEtale.{u, t} B S hS 𝒳) (hH : (H.over y).HasGlobalPresentation) :
    (((moduleLowerShriek.{u, t} B S hS 𝒳).obj H).over y.obj).HasGlobalPresentation := by
  let U : BigFppfOver B S hS := 𝒳.val.val.p.obj y.obj
  let f : schemeStack.{u, t} B S hS U ⟶ 𝒳 :=
    Bicategory.InducedBicategory.mkHom
      (objectMorphism B S hS 𝒳.val (Functor.Fiber.mk (a := y.obj) rfl))
  let T : LisseEtale.{u, t} B S hS (schemeStack.{u, t} B S hS U) :=
    ⟨Over.mk (𝟙 U), smoothObject_schemeStack_id.{u, t} B S hS U⟩
  have hT : IsTerminal T :=
    (smoothObject.{u, t} B S hS (schemeStack.{u, t} B S hS U)).isTerminalFullSubcategory
      Over.mkIdTerminal _
  let e : f.hom.hom.toFunctor.obj T.obj ≅ y.obj :=
    Functor.Fiber.fiberInclusion.mapIso
      (Functor.TwoYoneda.liftBasedEvaluationIso 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids U
        (Functor.Fiber.mk (a := y.obj) rfl))
  exact hasGlobalPresentation_over_moduleLowerShriek_of_chart B S hS 𝒳 f y.property hT y e H hH

/-- For a quasi-coherent sheaf of `O_{𝒳_{lisse,étale}}`-modules `H`, the module `g_!H` is
quasi-coherent on `(𝒳_étale, O_𝒳)`. -/
theorem isQuasicoherentOnSite_moduleLowerShriek_of_isQuasicoherentOnSite
    (H : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos.{u, t} B S hS 𝒳
      (closedUnderSmoothMorphisms.{u, t} B S hS 𝒳)).O))
    (hH : H.IsQuasicoherentOnSite) :
    ((moduleLowerShriek.{u, t} B S hS 𝒳).obj H).IsQuasicoherentOnSite := by
  let M := (moduleLowerShriek.{u, t} B S hS 𝒳).obj H
  have hsm := presentedSieve_mem_of_isQuasicoherentOnSite
    (smoothObject.{u, t} B S hS 𝒳).ι H M hH fun y =>
      hasGlobalPresentation_over_moduleLowerShriek B S hS 𝒳 H y
  refine Stacks.SheafOfModules.isQuasicoherentOnSite_of_presentedSieve_mem M fun x => ?_
  obtain ⟨U₀, a, hasm, hasurj⟩ := exists_smooth_surjective_schemeStack.{u, t} B S hS 𝒳
  obtain ⟨x', α, hgen⟩ := exists_etaleLocalLift B S hS a hasurj hasm x
  let s : LisseEtale.{u, t} B S hS 𝒳 :=
    ⟨a.hom.hom.toFunctor.obj (Over.mk (𝟙 U₀)),
      smoothObject_map.{u, t} B S hS a hasm ⟨_, smoothObject_schemeStack_id.{u, t} B S hS U₀⟩⟩
  exact presentedSieve_mem_of_generate_singleton_mem M α
    (a.hom.hom.toFunctor.map (Over.mkIdTerminal.from x')) hgen (hsm s)

/-- Let `𝒳` be an algebraic stack and let `H` be a quasi-coherent
`O_{𝒳_{lisse,étale}}`-module on the lisse-étale site of `𝒳`. Then `g_!H` is a quasi-coherent
module on `𝒳`, where `g_!` is the lower shriek on sheaves of modules of **Stacks 0789** (1).

A quasi-coherent module on `𝒳` is one in the sense of **Stacks 06WG**: a sheaf for the fppf
topology which is quasi-coherent on `(𝒳_fppf, O_𝒳)`. The conclusion is this property of the
underlying presheaf of modules of the sheaf `g_!H` on `𝒳_étale`, in the form of
`AlgebraicGeometry.FibredSite.IsQuasicoherentClause` at `.fppf` (**Stacks 0EM8**). -/
@[stacks 07B0 "part (1): for every quasi-coherent module `H` on the lisse-étale site of an \
algebraic stack `𝒳`, `g_!H` is a quasi-coherent module on `𝒳` — an fppf sheaf, quasi-coherent \
on `(𝒳_fppf, O_𝒳)` (the 06WG notion, read through the fppf clause of 0EM8)"]
theorem isQuasicoherentClause_fppf_moduleLowerShriek
    (H : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos.{u, t} B S hS 𝒳
      (closedUnderSmoothMorphisms.{u, t} B S hS 𝒳)).O))
    (hH : H.IsQuasicoherentOnSite) :
    FibredSite.IsQuasicoherentClause B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf
      ((moduleLowerShriek.{u, t} B S hS 𝒳).obj H).val :=
  FibredSite.isQuasicoherentClause_fppf_of_isQuasicoherentClause B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids .etale
    (FibredSite.isSheafFppfOfQuasicoherentOnSite_etale B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids)
    ⟨((moduleLowerShriek.{u, t} B S hS 𝒳).obj H).isSheaf,
      isQuasicoherentOnSite_moduleLowerShriek_of_isQuasicoherentOnSite B S hS 𝒳 H hH⟩

end LisseEtale

/-! ### The flat-fppf site -/

namespace FlatFppf

variable (𝒳 : AlgebraicStacks.{u, t} B S hS)

attribute [local instance] isContinuous_inclusion' isCocontinuous_inclusion'

/-- Let `f : 𝒰 ⟶ 𝒳` be a flat 1-morphism of algebraic stacks whose flat-fppf site has a final
object `T`, sent by `f` to an object isomorphic to a flat object `y` of `𝒳`. If `H` is a sheaf of
`O_{𝒳_{flat,fppf}}`-modules whose restriction to the slice at `y` has a global presentation, then
so does the restriction of `g_!H` to the slice at `y` in `𝒳_fppf`. -/
theorem hasGlobalPresentation_over_moduleLowerShriek_of_chart
    {𝒰 : AlgebraicStacks.{u, t} B S hS} (f : 𝒰 ⟶ 𝒳) (hf : AlgebraicStacks.IsFlat B S hS f)
    {T : FlatFppf B S hS 𝒰} (hT : IsTerminal T) (y : FlatFppf B S hS 𝒳)
    (e : f.hom.hom.toFunctor.obj T.obj ≅ y.obj)
    (H : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (subsiteRingedTopos B S hS
      𝒳.val.val.p 𝒳.val.isFiberedInGroupoids B.topology le_rfl (objectProperty B S hS 𝒳)).O))
    (hH : (H.over y).HasGlobalPresentation) :
    (((moduleLowerShriek B S hS 𝒳).obj H).over y.obj).HasGlobalPresentation := by
  have := isContinuous_subsiteFunctor B S hS f hf
  have := isCocontinuous_subsiteFunctor B S hS f hf
  have h₁ : (H.over ((SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor
      (objectProperty B S hS 𝒰) (flatObject_map B S hS f hf)).obj T)).HasGlobalPresentation :=
    Stacks.SheafOfModules.GlobalPresentationTransport.hasGlobalPresentation_overMap H
      (ObjectProperty.homMk e.hom) hH
  have h₂ := Stacks.SheafOfModules.hasGlobalPresentation_pushforward_of_isTerminal.{u + 1, u, u}
    (SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor
      (objectProperty B S hS 𝒰)
      (flatObject_map B S hS f hf)) hT
    (subsiteRing_obj_eq B S hS f B.topology le_rfl
      (objectProperty B S hS 𝒰)
      (objectProperty B S hS 𝒳) (flatObject_map B S hS f hf)) H h₁
  have h₃ :=
    Stacks.SheafOfModules.isPresentedByGlobalSections_of_hasGlobalPresentation_of_isTerminal hT h₂
  have h₅ := hasGlobalPresentation_subsiteModuleLowerShriek B S hS
    𝒰.val.val.p 𝒰.val.isFiberedInGroupoids B.topology le_rfl (objectProperty B S hS 𝒰)
    (isIso_unitLowerShriekMap_algebraicStack B S hS 𝒰) _ h₃
  have h₆ := SheafOfModules.HasGlobalPresentation.of_iso
    ((moduleShriekBaseChangeIso B S hS f hf).app H) h₅
  have h₇ := Stacks.SheafOfModules.hasGlobalPresentation_over _ T.obj h₆
  have h₈ := hasGlobalPresentation_of_modulePullback B S hS
    𝒰.val.val.p 𝒳.val.val.p
    𝒰.val.isFiberedInGroupoids 𝒳.val.isFiberedInGroupoids
    f.hom.hom.toFunctor (CatFiberedInGroupoids.homFunctor_comp_p f.hom) B.topology le_rfl _ T.obj h₇
  exact Stacks.SheafOfModules.GlobalPresentationTransport.hasGlobalPresentation_overMap _ e.inv h₈

/-- If `H` is a sheaf of `O_{𝒳_{flat,fppf}}`-modules whose restriction to the slice at a flat
object `y` has a global presentation, then the restriction of `g_!H` to the slice at `y` in
`𝒳_fppf` has a global presentation. -/
theorem hasGlobalPresentation_over_moduleLowerShriek
    (H : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (subsiteRingedTopos B S hS
      𝒳.val.val.p 𝒳.val.isFiberedInGroupoids B.topology le_rfl (objectProperty B S hS 𝒳)).O))
    (y : FlatFppf B S hS 𝒳) (hH : (H.over y).HasGlobalPresentation) :
    (((moduleLowerShriek B S hS 𝒳).obj H).over y.obj).HasGlobalPresentation := by
  let U : BigFppfOver B S hS := 𝒳.val.val.p.obj y.obj
  let f : schemeStack.{u, t} B S hS U ⟶ 𝒳 :=
    Bicategory.InducedBicategory.mkHom
      (objectMorphism B S hS 𝒳.val (Functor.Fiber.mk (a := y.obj) rfl))
  let T : FlatFppf B S hS (schemeStack.{u, t} B S hS U) :=
    ⟨Over.mk (𝟙 U), flatObject_schemeStack_id.{u, t} B S hS U⟩
  have hT : IsTerminal T :=
    (objectProperty B S hS (schemeStack.{u, t} B S hS U)).isTerminalFullSubcategory
      Over.mkIdTerminal _
  let e : f.hom.hom.toFunctor.obj T.obj ≅ y.obj :=
    Functor.Fiber.fiberInclusion.mapIso
      (Functor.TwoYoneda.liftBasedEvaluationIso 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids U
        (Functor.Fiber.mk (a := y.obj) rfl))
  exact hasGlobalPresentation_over_moduleLowerShriek_of_chart B S hS 𝒳 f
    ((AlgebraicStacks.isFlat_iff_hasPropertyOnSomeSmoothDiagram B S hS f).2 y.property) hT y e H hH

/-- Let `𝒳` be an algebraic stack and let `H` be a quasi-coherent
`O_{𝒳_{flat,fppf}}`-module on the flat-fppf site of `𝒳`. Then `g_!H` is a quasi-coherent module
on `𝒳`, where `g_!` is the lower shriek on sheaves of modules of **Stacks 0789** (2): it is
quasi-coherent on `(𝒳_fppf, O_𝒳)`, the ambient site being `𝒳_fppf` itself, which is
quasi-coherence of a module on `𝒳` in the sense of **Stacks 06WG**. -/
@[stacks 07B0 "part (2): for every quasi-coherent module `H` on the flat-fppf site of an \
algebraic stack `𝒳`, `g_!H` is a quasi-coherent module on `𝒳`, i.e. quasi-coherent on \
`(𝒳_fppf, O_𝒳)` (06WG)"]
theorem isQuasicoherentOnSite_moduleLowerShriek_of_isQuasicoherentOnSite
    (H : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (subsiteRingedTopos B S hS
      𝒳.val.val.p 𝒳.val.isFiberedInGroupoids B.topology le_rfl (objectProperty B S hS 𝒳)).O))
    (hH : H.IsQuasicoherentOnSite) :
    ((moduleLowerShriek B S hS 𝒳).obj H).IsQuasicoherentOnSite := by
  let M := (moduleLowerShriek B S hS 𝒳).obj H
  have hsm := presentedSieve_mem_of_isQuasicoherentOnSite
    (objectProperty B S hS 𝒳).ι H M hH fun y =>
      hasGlobalPresentation_over_moduleLowerShriek B S hS 𝒳 H y
  refine Stacks.SheafOfModules.isQuasicoherentOnSite_of_presentedSieve_mem M fun x => ?_
  obtain ⟨U₀, a, hasm, hasurj⟩ := exists_smooth_surjective_schemeStack.{u, t} B S hS 𝒳
  obtain ⟨x', α, hgen⟩ := exists_etaleLocalLift B S hS a hasurj hasm x
  let s : FlatFppf B S hS 𝒳 :=
    ⟨a.hom.hom.toFunctor.obj (Over.mk (𝟙 U₀)),
      flatObject_map B S hS a (AlgebraicStacks.isFlat_of_isSmooth B S hS a hasm)
        ⟨_, flatObject_schemeStack_id.{u, t} B S hS U₀⟩⟩
  exact presentedSieve_mem_of_generate_singleton_mem M α
    (a.hom.hom.toFunctor.map (Over.mkIdTerminal.from x'))
    (BigFppfOver.associatedTopology_le_fppf B S hS 𝒳.val.val.p .etale x hgen) (hsm s)

end FlatFppf


end AlgebraicGeometry.Stack

end
