module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmoothObjectDetection
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatFppfCartesianQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentLocallyQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeWeakSerreFppf
public import StacksFrontier.AlgebraicGeometry.Stacks.SubcategoryModuleLowerShriekForget

/-!
# Quasi-coherent modules restrict to quasi-coherent modules on the lisse-étale site

Let `𝒳` be an algebraic stack, `𝒳_{lisse,étale}` its lisse-étale site (**Stacks 0787**), ringed by
the restriction `𝒪` of the structure sheaf of `𝒳_étale`, and `g` the morphism of ringed topoi of
**Stacks 0788** (1), with pullback `g^{-1} = g^*` on sheaves of modules. This file proves that
`g^{-1}` of the étale module underlying a quasi-coherent `𝒪_𝒳`-module is quasi-coherent on
`𝒳_{lisse,étale}`, and records how isomorphisms are seen after `g^{-1}`.

## The proof

The smooth objects lying over affine schemes form a dense subsite of `𝒳_{lisse,étale}`: every
smooth object is étale-covered by smooth objects over affine schemes, the lifts of an affine open
covering of the scheme below it
(`AlgebraicGeometry.Stack.exists_isAffine_etale_covering_of_object`).
Quasi-coherence is detected on a dense subsite (Stacks 03DM), and a module all of whose
base-change maps between objects of that subsite are isomorphisms is quasi-coherent
(`Stacks.SheafOfModules.isQuasicoherentOnSite_of_isIso_restrictionBaseChange_of_isCoverDense`).
`g^{-1}` is restriction along the inclusion of the smooth objects
(`AlgebraicGeometry.Stack.subsiteModulePullbackRestrictionIso`), and a quasi-coherent module is
cartesian between affine objects
(`AlgebraicGeometry.FibredSite.isIso_restrictionBaseChange_of_isQuasicoherentOnSite`).

## Main results

* `AlgebraicGeometry.Stack.LisseEtale.isCoverDense_affineObject_ι`: the smooth objects over
  affine schemes are cover dense in `𝒳_{lisse,étale}`.
* `AlgebraicGeometry.Stack.LisseEtale.isQuasicoherentOnSite_of_isIso_restrictionBaseChange_affine`:
  a module on `𝒳_{lisse,étale}` cartesian between smooth objects over affine schemes is
  quasi-coherent.
* `LisseEtale.isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite` (in the namespace
  `AlgebraicGeometry.Stack`):
  `g^{-1}` of a quasi-coherent `𝒪_𝒳`-module is quasi-coherent.
* `AlgebraicGeometry.Stack.LisseEtale.bijective_app_of_isIso_modulePullback_map` and
  `AlgebraicGeometry.Stack.LisseEtale.isIso_modulePullback_map_of_bijective`: `g^{-1}` of a map is
  an isomorphism exactly when the map is bijective on the sections over every smooth object.

## References

* [Stacks Project, Tag 0787](https://stacks.math.columbia.edu/tag/0787)
* [Stacks Project, Tag 0788](https://stacks.math.columbia.edu/tag/0788)
* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
* [Stacks Project, Tag 0GZV](https://stacks.math.columbia.edu/tag/0GZV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Stack.LisseEtale

universe u t

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : Stack.AlgebraicStacks.{u, t} B S hS)

attribute [local instance] isContinuous_inclusion' isCocontinuous_inclusion'

/-- The smooth objects of an algebraic stack lying over affine schemes. -/
abbrev affineObject : ObjectProperty (LisseEtale.{u, t} B S hS 𝒳) :=
  fun y => IsAffine (𝒳.val.val.p.obj y.obj).left.1

/-- **The smooth objects over affine schemes are cover dense in the lisse-étale site**: every
smooth object is étale-covered by smooth objects over affine schemes, the lifts of an affine open
covering of the scheme below it, which lie over open immersions and so are smooth objects. -/
instance isCoverDense_affineObject_ι :
    (affineObject B S hS 𝒳).ι.IsCoverDense (inclusionTopology.{u, t} B S hS 𝒳) where
  is_cover y := by
    obtain ⟨I, z, g, hcov, haff, het⟩ :=
      exists_isAffine_etale_covering_of_object B S hS 𝒳 y.obj
    have hsm : ∀ i, smoothObject.{u, t} B S hS 𝒳 (z i) := fun i =>
      closedUnderSmoothMorphisms.{u, t} B S hS 𝒳 (g i) (by
        have := het i
        infer_instance) y.property
    let zh (i : I) : LisseEtale.{u, t} B S hS 𝒳 := ⟨z i, hsm i⟩
    let gh (i : I) : zh i ⟶ y := ObjectProperty.homMk (g i)
    have hR : Sieve.generate (Presieve.ofArrows zh gh) ∈
        inclusionTopology.{u, t} B S hS 𝒳 y := by
      rw [inclusionTopology, Functor.inheritedTopology_eq]
      refine Precoverage.generate_mem_toGrothendieck ⟨fun _ _ _ => inferInstance, ?_⟩
      rw [GrothendieckTopology.mem_toPrecoverage_iff, Presieve.map_ofArrows]
      exact hcov
    refine (inclusionTopology.{u, t} B S hS 𝒳).superset_covering ?_ hR
    rintro Z f ⟨W, k, _, ⟨j⟩, rfl⟩
    exact ⟨⟨⟨zh j, haff j⟩, k, gh j, rfl⟩⟩

/-- **A module on the lisse-étale site cartesian between smooth objects over affine schemes is
quasi-coherent.** Let `ℋ` be a sheaf of modules on the lisse-étale site of an algebraic stack such
that for every arrow `y ⟶ y'` between smooth objects lying over affine schemes the base-change
map `ℋ(y') ⊗_{𝒪(y')} 𝒪(y) ⟶ ℋ(y)` is an isomorphism. Then `ℋ` is quasi-coherent.

Quasi-coherence is detected on the dense subsite of the smooth objects over affine schemes
(Stacks 03DM), where every arrow is cartesian, so that the restriction of `ℋ` is quasi-coherent by
the core of Stacks 0GZV. -/
theorem isQuasicoherentOnSite_of_isIso_restrictionBaseChange_affine
    (H : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos.{u, t} B S hS 𝒳
      (closedUnderSmoothMorphisms.{u, t} B S hS 𝒳)).O))
    (hH : ∀ ⦃y y' : LisseEtale.{u, t} B S hS 𝒳⦄ (f : y ⟶ y'),
      IsAffine (𝒳.val.val.p.obj y.obj).left.1 → IsAffine (𝒳.val.val.p.obj y'.obj).left.1 →
      IsIso (Stacks.PresheafOfModules.restrictionBaseChange
        (R := (subsiteStructureSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
          (etaleTopology B) (etaleTopology_le_topology B)
          (smoothObject.{u, t} B S hS 𝒳)).obj) H.val f.op)) :
    H.IsQuasicoherentOnSite :=
  Stacks.SheafOfModules.isQuasicoherentOnSite_of_isIso_restrictionBaseChange_of_isCoverDense
    (affineObject B S hS 𝒳).ι (inclusionTopology.{u, t} B S hS 𝒳)
    (subsiteStructureSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (etaleTopology B)
      (etaleTopology_le_topology B) (smoothObject.{u, t} B S hS 𝒳)) H
    fun U V _ => hH _ U.property V.property

/-- `g^* = g^{-1}`: the pullback of sheaves of modules to the lisse-étale site is restriction
along the inclusion of the smooth objects. -/
def modulePullbackRestrictionIso : modulePullback.{u, t} B S hS 𝒳 ≅
      SheafOfModules.pushforward.{u} (𝟙 (subsiteRingSheaf B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids (etaleTopology B) (etaleTopology_le_topology B)
          (smoothObject.{u, t} B S hS 𝒳))) :=
  subsiteModulePullbackRestrictionIso B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
    (etaleTopology B) (etaleTopology_le_topology B) (smoothObject.{u, t} B S hS 𝒳)

/-- `g^{-1}` on `𝒪_𝒳`-modules: the étale module underlying an `𝒪_𝒳`-module, pulled back to the
lisse-étale site. The étale module is read through
`Stacks.SheafOfModules.comparisonPushforward`, which is the direct image `ε_*` along
`𝒳_fppf ⟶ 𝒳_étale`, `AlgebraicGeometry.Stack.fppfModulesToEtaleModules`, on the nose
(`AlgebraicGeometry.Stack.LisseEtale.fppfModulePullback_eq`): neither changes the underlying
presheaf of modules. -/
abbrev fppfModulePullback :
    fppfModules B S hS 𝒳 ⥤ SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (ringedTopos.{u, t} B S hS 𝒳 (closedUnderSmoothMorphisms.{u, t} B S hS 𝒳)).O) :=
  Stacks.SheafOfModules.comparisonPushforward
      (BigFppfOver.associatedTopology_le_fppf B S hS 𝒳.val.val.p .etale)
      (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf) ⋙
    modulePullback.{u, t} B S hS 𝒳

/-- `g^{-1}` on `𝒪_𝒳`-modules is `ε_*` followed by the pullback to the lisse-étale site. -/
theorem fppfModulePullback_eq :
    fppfModulePullback B S hS 𝒳 =
      fppfModulesToEtaleModules B S hS 𝒳 ⋙ modulePullback.{u, t} B S hS 𝒳 :=
  rfl

/-- **`g^{-1}` of a quasi-coherent `𝒪_𝒳`-module is quasi-coherent on the lisse-étale site**: it is
cartesian between the smooth objects over affine schemes, being the restriction of a module
cartesian between all objects over affine schemes. -/
theorem isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite (G : fppfModules B S hS 𝒳)
    (hG : G.IsQuasicoherentOnSite) :
    ((fppfModulePullback B S hS 𝒳).obj G).IsQuasicoherentOnSite := by
  refine isQuasicoherentOnSite_of_isIso_restrictionBaseChange_affine B S hS 𝒳 _ ?_
  intro y y' f hy hy'
  -- the base change map of `G` along `f`, read successively over the fppf structure sheaf, the
  -- étale one, and the restricted one; the three are the same map
  have h0 : IsIso (Stacks.PresheafOfModules.restrictionBaseChange
      (R := (FibredSite.structureSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf).obj)
      G.val f.hom.op) :=
    FibredSite.isIso_restrictionBaseChange_of_isQuasicoherentOnSite G hG f.hom hy hy'
  have h1 : IsIso (Stacks.PresheafOfModules.restrictionBaseChange
      (R := (structureSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (etaleTopology B)
        (etaleTopology_le_topology B)).obj)
      ((Stacks.SheafOfModules.comparisonPushforward
      (BigFppfOver.associatedTopology_le_fppf B S hS 𝒳.val.val.p .etale)
      (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids .fppf)).obj G).val f.hom.op) := h0
  have h2 : IsIso (Stacks.PresheafOfModules.restrictionBaseChange
      (R := (subsiteStructureSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
        (etaleTopology B) (etaleTopology_le_topology B) (smoothObject.{u, t} B S hS 𝒳)).obj)
      ((SheafOfModules.forget _).obj
        ((SheafOfModules.pushforward.{u} (𝟙 (subsiteRingSheaf B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids (etaleTopology B) (etaleTopology_le_topology B)
          (smoothObject.{u, t} B S hS 𝒳)))).obj ((Stacks.SheafOfModules.comparisonPushforward
      (BigFppfOver.associatedTopology_le_fppf B S hS 𝒳.val.val.p .etale)
      (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids .fppf)).obj G)))
      f.op) := h1
  exact @Stacks.PresheafOfModules.isIso_restrictionBaseChange_of_iso _ _ _ _ _
    ((SheafOfModules.forget _).mapIso ((modulePullbackRestrictionIso B S hS 𝒳).app
      ((Stacks.SheafOfModules.comparisonPushforward
      (BigFppfOver.associatedTopology_le_fppf B S hS 𝒳.val.val.p .etale)
      (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids .fppf)).obj G)).symm) _ _ f.op h2

/-- `g^{-1}` of a map of `𝒪_𝒳`-modules is an isomorphism iff the map is bijective on sections over
every smooth object. -/
private theorem isIso_fppfModulePullback_map_iff {F G : fppfModules B S hS 𝒳} (φ : F ⟶ G) :
    IsIso ((fppfModulePullback B S hS 𝒳).map φ) ↔
      ∀ x : 𝒳.val.val.obj, smoothObject.{u, t} B S hS 𝒳 x →
        Function.Bijective (φ.val.app (op x)) := by
  refine (NatIso.isIso_map_iff (modulePullbackRestrictionIso B S hS 𝒳) _).trans ?_
  rw [← isIso_iff_of_reflects_iso _
    (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _), NatTrans.isIso_iff_isIso_app]
  refine ⟨fun h x hx => ?_, fun h => ?_⟩
  · have := h (op ⟨x, hx⟩)
    rwa [ConcreteCategory.isIso_iff_bijective] at this
  · rintro ⟨⟨x, hx⟩⟩
    rw [ConcreteCategory.isIso_iff_bijective]
    exact h x hx

/-- A map of `𝒪_𝒳`-modules whose pullback to the lisse-étale site is an isomorphism is bijective
on sections over every smooth object. -/
theorem bijective_app_of_isIso_modulePullback_map {F G : fppfModules B S hS 𝒳} (φ : F ⟶ G)
    (h : IsIso ((fppfModulePullback B S hS 𝒳).map φ)) (x : 𝒳.val.val.obj)
    (hx : smoothObject.{u, t} B S hS 𝒳 x) : Function.Bijective (φ.val.app (op x)) :=
  (isIso_fppfModulePullback_map_iff B S hS 𝒳 φ).1 h x hx

/-- **A map of `𝒪_𝒳`-modules bijective on sections over every smooth object becomes an
isomorphism on the lisse-étale site.** -/
theorem isIso_modulePullback_map_of_bijective {F G : fppfModules B S hS 𝒳} (φ : F ⟶ G)
    (h : ∀ x : 𝒳.val.val.obj, smoothObject.{u, t} B S hS 𝒳 x →
      Function.Bijective (φ.val.app (op x))) :
    IsIso ((fppfModulePullback B S hS 𝒳).map φ) :=
  (isIso_fppfModulePullback_map_iff B S hS 𝒳 φ).2 h

end AlgebraicGeometry.Stack.LisseEtale

end
