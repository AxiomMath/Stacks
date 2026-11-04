module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentEtaleLocality
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentTensor
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SiteEquivalenceAffine
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentDenseSubsite
public import StacksFrontier.CategoryTheory.Sites.Localization.SlicePostContinuous

/-!
# Local quasi-coherence from quasi-coherence on the inherited étale site

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids.  **Stacks 06WJ** calls a sheaf of
`𝒪_𝒳`-modules on the inherited étale site *locally quasi-coherent* when, at every object `x` of
`𝒳`, its restriction `F|_{U_ét}` to the small étale site of the scheme `U` below `x` is
quasi-coherent there.  This file proves that a module quasi-coherent on the inherited étale site
`(𝒳_ét, 𝒪_𝒳)` is locally quasi-coherent, and hence that every quasi-coherent module on `𝒳`
(Stacks 06WG) is locally quasi-coherent, which is the first clause of the forward direction of
Stacks 06WK.

The step is Stacks 03DM for clause (6) of Stacks 03DL along the restriction functor of
**Stacks 06W1**: that functor is continuous and cocontinuous
(`AlgebraicGeometry.Stack.isContinuous_and_isCocontinuous_restrictToSmallEtale`), and
`Stacks.SheafOfModules.isQuasicoherentOnSite_pushforward` carries quasi-coherence along any such
functor once the structure sheaves are identified, which
`AlgebraicGeometry.Stack.localStructurePresheafIso` does.  A module quasi-coherent on the
inherited fppf site is quasi-coherent on the inherited étale site by Stacks 0EM8
(`AlgebraicGeometry.FibredSite.quasicoherentOnSiteOfLeFppf_etale`).

## Main results

* `AlgebraicGeometry.Stack.isQuasicoherentOnSite_restrictModuleToSmallEtale`: the second clause
  of Stacks 06WJ from quasi-coherence on the inherited étale site, at every module universe.
* `AlgebraicGeometry.Stack.isLocallyQuasicoherent_of_isQuasicoherentOnSite_etale`: Stacks 06WJ from
  quasi-coherence on the inherited étale site.
* `AlgebraicGeometry.Stack.isLocallyQuasicoherent_toSiteModules_etale`: a quasi-coherent module
  on `𝒳`, read on the inherited étale site, is locally quasi-coherent.

## Implementation notes

The objects of `𝒳` lie in `Type (u + 1)` and its morphisms in `Type u`, the universes of the
small étale site, because `Stacks.SheafOfModules.isQuasicoherentOnSite_pushforward` is stated for
two sites in one pair of universes.

The module is the one of `AlgebraicGeometry.Stack.restrictModuleToSmallEtale`, on the nose: the
restriction along the Stacks 06W1 functor together with the transport of scalars through
`AlgebraicGeometry.Stack.localStructurePresheafIso` is the pushforward of modules along that
identification, so `Stacks.SheafOfModules.isQuasicoherentOnSite_pushforward` applies to it with
no comparison isomorphism in the way.  The sheafification instances on the two slice sites are
supplied at the raised module universe by
`CategoryTheory.GrothendieckTopology.hasSheafify_addCommGrpCat` and
`AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat`.

The localization of the restriction functor is continuous by
`CategoryTheory.Functor.isContinuous_overPost`, which holds for every continuous functor of
sites, so no dense-subsite hypothesis on the small étale inclusion is needed.

## References

* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
* [Stacks Project, Tag 06WK](https://stacks.math.columbia.edu/tag/06WK)
* [Stacks Project, Tag 06W1](https://stacks.math.columbia.edu/tag/06W1)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
* [Stacks Project, Tag 0EM8](https://stacks.math.columbia.edu/tag/0EM8)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u v w m

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type (u + 1)} [Category.{u} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids)

/-- **The second clause of Stacks 06WJ, from quasi-coherence on the inherited étale site.**  If a
sheaf of `𝒪_𝒳`-modules on the inherited étale site of `𝒳` is quasi-coherent there in the sense of
**Stacks 03DL**(6), then its restriction `F|_{U_ét}` to the small étale site of the scheme `U`
below any object `x` is quasi-coherent on that site.

This is **Stacks 03DM** along the restriction functor of **Stacks 06W1**, which is continuous and
cocontinuous by `AlgebraicGeometry.Stack.isContinuous_and_isCocontinuous_restrictToSmallEtale`;
its localizations are continuous by `CategoryTheory.Functor.isContinuous_overPost`, and the
structure sheaf of the small étale site of `U` is identified with the restricted structure sheaf
of `𝒳` by `AlgebraicGeometry.Stack.localStructurePresheafIso`. -/
theorem isQuasicoherentOnSite_restrictModuleToSmallEtale
    (M : SheafOfModules.{m} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)))
    (hM : M.IsQuasicoherentOnSite) (x : 𝒳) :
    (⟨restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) M.val,
      restrictModuleToSmallEtale_isSheaf B E h S hS p hp x M.val M.isSheaf⟩ :
      SheafOfModules.{m} (SmallEtale.structureSheaf E (p.obj x).left.1
        (contains_base B E h S hS p x))).IsQuasicoherentOnSite := by
  let := isEquivalence_overPost B S hS p hp x
  let q := smallEtaleInclusion B E h (p.obj x).left.1 (contains_base B E h S hS p x) ⋙
      (Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).inv ⋙ Over.forget x
  let J := associatedTopology B S hS p (etaleTopology B)
  let K := SmallEtale.topology E (p.obj x).left.1 (contains_base B E h S hS p x)
  obtain ⟨h₁, h₂⟩ := isContinuous_and_isCocontinuous_restrictToSmallEtale B E h S hS p hp x
  have : q.IsContinuous K J := h₁
  have : q.IsCocontinuous K J := h₂
  have : ∀ X, (Over.post (X := X) q).IsContinuous (K.over X) (J.over (q.obj X)) :=
    fun X => Functor.isContinuous_overPost K J q X
  let φ : SmallEtale.structureSheaf E (p.obj x).left.1 (contains_base B E h S hS p x) ⟶
      (q.sheafPushforwardContinuous RingCat.{u} K J).obj
        (ringStructureSheafCore B S hS p hp (etaleTopology B)
          (etaleTopology_le_topology B)) :=
    ⟨(localStructurePresheafIso B E h S hS p hp x (etaleTopology B)
      (etaleTopology_le_topology B)).hom⟩
  have : IsIso φ := by
    have : IsIso ((sheafToPresheaf K RingCat.{u}).map φ) :=
      inferInstanceAs (IsIso (localStructurePresheafIso B E h S hS p hp x
        (etaleTopology B) (etaleTopology_le_topology B)).hom)
    exact isIso_of_reflects_iso φ (sheafToPresheaf K RingCat.{u})
  have hcol : ∀ (X : SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x)) (Y : 𝒳)
      (f : q.obj X ⟶ Y),
      Limits.PreservesColimitsOfSize.{max (u + 1) m, max (u + 1) m}
        (SheafOfModules.pushforward.{max (u + 1) m}
          (R := (ringStructureSheafCore B S hS p hp (etaleTopology B)
            (etaleTopology_le_topology B)).over Y)
          (F := Over.post (X := X) q ⋙ Over.map f)
          (((Over.forget X).sheafPushforwardContinuous RingCat.{u} (K.over X) K).map φ)) := by
    intro X Y f
    have : (Over.post (X := X) q ⋙ Over.map f).IsCocontinuous (K.over X) (J.over Y) :=
      isCocontinuous_comp _ _ (K.over X) (J.over (q.obj X))
    have sheafify : ∀ {C : Type (u + 1)} [Category.{u} C] (T : GrothendieckTopology C),
        HasWeakSheafify T AddCommGrpCat.{max (u + 1) m} ∧
          T.WEqualsLocallyBijective AddCommGrpCat.{max (u + 1) m} := fun T =>
      ⟨(GrothendieckTopology.hasSheafify_addCommGrpCat T).isRightAdjoint,
        AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat T⟩
    obtain ⟨_, _⟩ := sheafify (K.over X)
    obtain ⟨_, _⟩ := sheafify (J.over Y)
    exact Stacks.SheafOfModules.pushforward_preservesColimits
      (Over.post (X := X) q ⋙ Over.map f) _
  exact Stacks.SheafOfModules.isQuasicoherentOnSite_pushforward q φ hcol M hM

/-- **Stacks 06WJ from quasi-coherence on the inherited étale site, with no hypothesis.**  A
sheaf of `𝒪_𝒳`-modules quasi-coherent on `(𝒳_ét, 𝒪_𝒳)` is locally quasi-coherent.

The étale sheaf condition is the one the module carries, and the quasi-coherence of the
restriction at each object is
`AlgebraicGeometry.Stack.isQuasicoherentOnSite_restrictModuleToSmallEtale`. -/
theorem isLocallyQuasicoherent_of_isQuasicoherentOnSite_etale
    (M : SheafOfModules.{m} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)))
    (hM : M.IsQuasicoherentOnSite) :
    IsLocallyQuasicoherent B E h S hS p hp M.val :=
  ⟨M.isSheaf, fun x =>
    ⟨restrictModuleToSmallEtale_isSheaf B E h S hS p hp x M.val M.isSheaf,
      isQuasicoherentOnSite_restrictModuleToSmallEtale B E h S hS p hp M hM x⟩⟩

/-- **Every quasi-coherent module on `𝒳` is locally quasi-coherent.**  A module quasi-coherent
on the inherited fppf site (Stacks 06WG), read on the inherited étale site, is locally
quasi-coherent (Stacks 06WJ): it is quasi-coherent on the inherited étale site by Stacks 0EM8,
and `AlgebraicGeometry.Stack.isLocallyQuasicoherent_of_isQuasicoherentOnSite_etale` applies. -/
theorem isLocallyQuasicoherent_toSiteModules_etale
    (F : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS p hp) :
    IsLocallyQuasicoherent B E h S hS p hp
      ((FibredSite.toSiteModules B S hS p hp .etale).obj F).val :=
  isLocallyQuasicoherent_of_isQuasicoherentOnSite_etale B E h S hS p hp
    ((FibredSite.toSiteModules B S hS p hp .etale).obj F)
    (FibredSite.quasicoherentOnSiteOfLeFppf_etale B S hS p hp F.obj F.property)

end AlgebraicGeometry.Stack

end
