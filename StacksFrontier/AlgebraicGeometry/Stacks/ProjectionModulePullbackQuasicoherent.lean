module

public import StacksFrontier.AlgebraicGeometry.Stacks.ProjectionPullbackQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.FibredSiteSheafFppf
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentOnSiteCoarserFromFppf
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasicoherentRestrictionAlgebraicSpaceExtensions
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasicoherentRestrictionDescentInputs

/-!
# The inverse image of modules along the projection of an algebraic space

Let `𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids representable by an algebraic space
`X`. This file identifies the chosen left adjoint
`AlgebraicGeometry.Space.projectionModulePullback` of restriction to the small étale site of `X`
with the inverse image of modules `AlgebraicGeometry.RingedToposHom.pullbackModules` along the
morphism of ringed topoi `π_X`, and deduces that it preserves quasi-coherence.

## Main results

* `AlgebraicGeometry.Space.restrictionRingStructureSheaf_eq`: the identification
  `u_{X,*}𝒪_𝒳 = 𝒪_X` on underlying sheaves of rings.
* `AlgebraicGeometry.Space.fSharpRing_projectionRingedSiteHom_eq_restrictionStructureHom`: the
  structure map of `π_X` as a morphism of ringed sites is the coefficient homomorphism of
  equation 075K on modules.
* `AlgebraicGeometry.Space.pushforwardTopos_projectionRingedSiteHom_eq_moduleRestriction`: the
  direct image of modules along the site presentation of `π_X` is equation 075K on modules.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_projectionModulePullback`: the chosen left
  adjoint `π_X^*` carries quasi-coherent modules to modules quasi-coherent on the inherited
  étale site.
* `AlgebraicGeometry.Space.projectionPullbackPreservesQuasicoherent`: `π_X^*` corestricts to the
  quasi-coherent modules.
* `AlgebraicGeometry.Space.isEquivalence_quasicoherentRestriction_of_counitIsIso` and
  `AlgebraicGeometry.Space.nonempty_inv_toSiteModules_iso_projectionModulePullback_of_counitIsIso`:
  if the counit of `π_X^* ⊣ i_X^*` is an isomorphism at the quasi-coherent modules, restriction
  is an equivalence of quasi-coherent modules with inverse `π_X^*`.

## Implementation notes

`AlgebraicGeometry.RingedToposHom.pullbackModules` and
`AlgebraicGeometry.RingedToposSiteHom.pushforwardTopos` exist only at a module universe equal to
the universe of the sections of the structure sheaves, which is the universe `u` of the schemes;
so every statement of this file is at the module universe `u`.

## References

* [Stacks Project, Tag 0GQD](https://stacks.math.columbia.edu/tag/0GQD)
* [Stacks Project, Tag 073M](https://stacks.math.columbia.edu/tag/073M)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
* [Stacks Project, Tag 0EM8](https://stacks.math.columbia.edu/tag/0EM8)
* [Stacks Project, Equation 075K](https://stacks.math.columbia.edu/tag/075K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u v w

attribute [local instance] hasSheafCompose_forget_ringCat
  Stacks.hasSheafCompose_forget₂_commRingCat

section General

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : AlgebraicSpaces B S hS)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids)
  (e : StacksRepresentableCFG.EquivalenceOver p
    (presheafOfCategories (X.1 ⋙ typeToCat)).p)

/-! ### Equation 075K on modules is the direct image of the site presentation of `π_X` -/

/-- Restriction along `u_X : X_étale ⥤ 𝒳` carries the sheaf of rings underlying the structure
sheaf of `𝒳` to the sheaf of rings underlying the structure sheaf of the small étale site of
`X`. -/
theorem restrictionRingStructureSheaf_eq :
    letI := restrictionFunctor_isContinuous B S hS X.1 p hp e
    ((restrictionFunctor B S hS X.1 p e).sheafPushforwardContinuous RingCat.{u}
      (SmallEtale.topology B S hS X.1)
      (BigFppfOver.associatedTopology B S hS p .etale)).obj
        (FibredSite.ringStructureSheafCore B S hS p hp .etale) =
      structureRingSheaf B S hS X :=
  congrArg ((sheafCompose (SmallEtale.topology B S hS X.1)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj)
    (inverseImage_structureSheaf_eq B S hS X.1 p hp e X.2)

/-- The structure map of the site presentation of `π_X`, as a homomorphism of sheaves of rings,
is the coefficient homomorphism `AlgebraicGeometry.Space.restrictionStructureHom` of equation
075K on modules. -/
theorem fSharpRing_projectionRingedSiteHom_eq_restrictionStructureHom :
    ((projectionRingedSiteHomGeneral B S hS X.1 p hp X.2 e).toRingedToposSiteHom).fSharpRing =
      restrictionStructureHom B S hS X p hp e := by
  let := restrictionFunctor_isContinuous B S hS X.1 p hp e
  have hw : ∀ (T : SmallEtale B S hS X.1 ⥤ BigFppfOver B S hS)
      (hc : restrictionFunctor B S hS X.1 p e ⋙ p = T),
      Functor.whiskerRight (NatTrans.op (eqToHom hc))
          (BigFppfOver.structureSheaf B S hS).obj =
        eqToHom (congrArg (fun F : SmallEtale B S hS X.1 ⥤ BigFppfOver B S hS =>
          F.op ⋙ (BigFppfOver.structureSheaf B S hS).obj) hc).symm := by
    rintro T rfl
    simp
    rfl
  rw [show ((projectionRingedSiteHomGeneral B S hS X.1 p hp X.2 e).toRingedToposSiteHom
      ).fSharpRing =
      (sheafCompose (SmallEtale.topology B S hS X.1)
        (forget₂ CommRingCat.{u} RingCat.{u})).map
          (eqToHom (inverseImage_structureSheaf_eq B S hS X.1 p hp e X.2).symm) from rfl,
    eqToHom_map]
  apply Sheaf.hom_ext
  rw [show (restrictionStructureHom B S hS X p hp e).hom =
      Functor.whiskerRight (NatTrans.op (eqToHom (restrictionFunctor_comp B S hS X.1 p e)))
        (BigFppfOver.structureSheaf B S hS).obj from rfl,
    hw _ (restrictionFunctor_comp B S hS X.1 p e)]
  exact eqToHom_map (sheafToPresheaf (SmallEtale.topology B S hS X.1) RingCat.{u}) _

/-- The direct image of sheaves of modules along the site presentation of `π_X` is equal to
`AlgebraicGeometry.Space.moduleRestriction`, equation 075K on modules. -/
theorem pushforwardTopos_projectionRingedSiteHom_eq_moduleRestriction :
    ((projectionRingedSiteHomGeneral B S hS X.1 p hp X.2 e).toRingedToposSiteHom
      ).pushforwardTopos = moduleRestriction.{u, v, w, u} B S hS X p hp e := by
  let := restrictionFunctor_isContinuous B S hS X.1 p hp e
  let := ((projectionRingedSiteHomGeneral B S hS X.1 p hp X.2 e).toRingedToposSiteHom
    ).isContinuous
  show SheafOfModules.pushforward.{u}
      ((projectionRingedSiteHomGeneral B S hS X.1 p hp X.2 e).toRingedToposSiteHom).fSharpRing =
    SheafOfModules.pushforward.{u} (restrictionStructureHom B S hS X p hp e)
  rw [fSharpRing_projectionRingedSiteHom_eq_restrictionStructureHom]
  rfl

/-! ### Quasi-coherence of `π_X^*` -/

include hp in
/-- The chosen left adjoint `AlgebraicGeometry.Space.projectionModulePullback` of restriction
carries a quasi-coherent `𝒪_X`-module to a module quasi-coherent on the inherited étale site of
`𝒳`, at the module universe `u` of the schemes. -/
theorem isQuasicoherentOnSite_projectionModulePullback
    (G : Modules.{u, u} B S hS X.1 X.2) (hG : G.IsQuasicoherentOnSite) :
    ((projectionModulePullback.{u, v, w, u} B S hS X p hp e).obj G).IsQuasicoherentOnSite := by
  let : EssentiallySmall.{u} 𝒳 := essentiallySmall_of_equivalenceOver B S hS X.1 p e
  let : EssentiallySmall.{u} (FibredSite.ringedSite B S hS p hp .etale).C :=
    essentiallySmall_of_equivalenceOver B S hS X.1 p e
  let : LocallySmall.{u} (FibredSite.ringedSite B S hS p hp .etale).C :=
    inferInstanceAs (LocallySmall.{u} 𝒳)
  let : EssentiallySmall.{u} (smallEtaleRingedSite B S hS X.1 X.2).C :=
    inferInstanceAs (EssentiallySmall.{u} (SmallEtale B S hS X.1))
  let : HasWeakSheafify (FibredSite.ringedSite B S hS p hp .etale).J AddCommGrpCat.{u} :=
    FibredSite.hasWeakSheafify_associatedTopology B S hS p .etale
  let : (FibredSite.ringedSite B S hS p hp .etale).J.WEqualsLocallyBijective
      AddCommGrpCat.{u} :=
    FibredSite.wEqualsLocallyBijective_associatedTopology B S hS p .etale
  let : HasWeakSheafify (FibredSite.associatedRingedTopos B S hS p hp .etale).J
      AddCommGrpCat.{u} :=
    FibredSite.hasWeakSheafify_associatedTopology B S hS p .etale
  let : (FibredSite.associatedRingedTopos B S hS p hp .etale).J.WEqualsLocallyBijective
      AddCommGrpCat.{u} :=
    FibredSite.wEqualsLocallyBijective_associatedTopology B S hS p .etale
  refine SheafOfModules.IsQuasicoherentOnSite.of_iso
    ((Adjunction.leftAdjointUniq
      (projectionModulePullbackAdjunction.{u, v, w, u} B S hS X p hp e)
      ((RingedToposHom.pullbackAdjPushforwardModules
        (projectionRingedToposHom B S hS X.1 p hp X.2 e)).ofNatIsoRight
          ((projectionRingedSiteHomGeneral B S hS X.1 p hp X.2 e).pushforwardToposIsoGeneral ≪≫
            eqToIso (pushforwardTopos_projectionRingedSiteHom_eq_moduleRestriction
              B S hS X p hp e)))).app G).symm ?_
  exact isQuasicoherentOnSite_projectionPullbackModules B S hS X.1 p hp X.2 e G hG

/-! ### Corestriction of `π_X^*` to quasi-coherent modules -/

include hp in
/-- At the module universe `u`, the functor `π_X^*` corestricts to a functor
`QCoh(𝒪_X) ⥤ QCoh(𝒪_𝒳)` whose composite with the reading of a quasi-coherent fppf module as an
étale sheaf of modules is `π_X^*` on the underlying `𝒪_X`-modules. -/
theorem projectionPullbackPreservesQuasicoherent :
    ProjectionPullbackPreservesQuasicoherent.{u, v, w, u} B S hS X p hp e := by
  have hcl : ∀ G : QuasicoherentSheaves.{u, u} B S hS X.1 X.2,
      FibredSite.IsQuasicoherentClause B S hS p hp .fppf
        ((projectionModulePullback.{u, v, w, u} B S hS X p hp e).obj G.obj).val := fun G =>
    FibredSite.isQuasicoherentClause_fppf_of_isQuasicoherentClause B S hS p hp .etale
      (FibredSite.isSheafFppfOfQuasicoherentOnSite_siteKind B S hS p hp .etale)
      ⟨((projectionModulePullback.{u, v, w, u} B S hS X p hp e).obj G.obj).isSheaf,
        isQuasicoherentOnSite_projectionModulePullback B S hS X p hp e G.obj G.property⟩
  choose hsh hqcf using hcl
  refine ⟨{ obj := fun G => ⟨⟨_, hsh G⟩, hqcf G⟩
            map := fun f =>
              ⟨⟨((projectionModulePullback.{u, v, w, u} B S hS X p hp e).map f.hom).val⟩⟩
            map_id := fun G => ?_
            map_comp := fun f g => ?_ }, ⟨Iso.refl _⟩⟩
  · simp
    rfl
  · simp
    rfl

end General

/-! ### Restriction of quasi-coherent modules for `𝒳 : Type (u + 1)` -/

section SmallFibred

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : AlgebraicSpaces B S hS)
  {𝒳 : Type (u + 1)} [Category.{u} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids)
  (e : StacksRepresentableCFG.EquivalenceOver p
    (presheafOfCategories (X.1 ⋙ typeToCat)).p)

/-- The corestriction of `π_X^*` to quasi-coherent modules, together with the invertibility of the
unit of `π_X^* ⊣ i_X^*` at quasi-coherent `𝒪_X`-modules. -/
private theorem exists_quasicoherent_pullback_functor_isIso_unit :
    ∃ Pq : QuasicoherentSheaves.{u, u} B S hS X.1 X.2 ⥤
        FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS p hp,
      Nonempty (Pq ⋙ FibredSite.toSiteModules B S hS p hp .etale ≅
        (quasicoherentModulesProperty.{u, u} B S hS X).ι ⋙
          projectionModulePullback.{u, u + 1, u, u} B S hS X p hp e) ∧
      ∀ G : QuasicoherentSheaves.{u, u} B S hS X.1 X.2,
        IsIso ((projectionModulePullbackAdjunction.{u, u + 1, u, u} B S hS X p hp e).unit.app
          ((quasicoherentModulesProperty.{u, u} B S hS X).ι.obj G)) := by
  obtain ⟨Pq, hPq⟩ := projectionPullbackPreservesQuasicoherent.{u, u + 1, u} B S hS X p hp e
  let := isIso_unit_moduleRestriction'.{u, u + 1, u} B S hS X p hp e
    (projectionModulePullbackAdjunction.{u, u + 1, u, u} B S hS X p hp e)
  exact ⟨Pq, hPq, fun _ => NatIso.isIso_app_of_isIso _ _⟩

include hp in
/-- At the module universe `u`, restriction to the small étale site of `X` is an equivalence
`QCoh(𝒪_𝒳) ⥤ QCoh(𝒪_X)` as soon as the counit of `π_X^* ⊣ i_X^*` is an isomorphism at the
quasi-coherent modules. -/
theorem isEquivalence_quasicoherentRestriction_of_counitIsIso
    (hcounit : ProjectionPullbackCounitIsIso.{u, u + 1, u, u} B S hS X p hp e) :
    (quasicoherentRestriction.{u, u + 1, u, u} B S hS X p hp e
      (restrictionPreservesQuasicoherent B S hS X p hp e)).IsEquivalence := by
  obtain ⟨Pq, ⟨hPq⟩, hunit⟩ := exists_quasicoherent_pullback_functor_isIso_unit B S hS X p hp e
  exact isEquivalence_quasicoherentRestriction.{u, u + 1, u, u} B S hS X p hp e
    (restrictionPreservesQuasicoherent B S hS X p hp e)
    (projectionModulePullbackAdjunction.{u, u + 1, u, u} B S hS X p hp e) Pq hPq
    hunit hcounit

include hp in
/-- At the module universe `u`, if the counit of `π_X^* ⊣ i_X^*` is an isomorphism at the
quasi-coherent modules, the inverse of the restriction equivalence
`AlgebraicGeometry.Space.quasicoherentRestriction` is `𝒢 ↦ π_X^*𝒢`, read on underlying
modules. -/
theorem nonempty_inv_toSiteModules_iso_projectionModulePullback_of_counitIsIso
    (hcounit : ProjectionPullbackCounitIsIso.{u, u + 1, u, u} B S hS X p hp e) :
    letI := isEquivalence_quasicoherentRestriction_of_counitIsIso B S hS X p hp e hcounit
    Nonempty ((quasicoherentRestriction.{u, u + 1, u, u} B S hS X p hp e
          (restrictionPreservesQuasicoherent B S hS X p hp e)).inv ⋙
        FibredSite.toSiteModules B S hS p hp .etale ≅
      (quasicoherentModulesProperty.{u, u} B S hS X).ι ⋙
        projectionModulePullback.{u, u + 1, u, u} B S hS X p hp e) := by
  obtain ⟨Pq, ⟨hPq⟩, hunit⟩ := exists_quasicoherent_pullback_functor_isIso_unit B S hS X p hp e
  obtain ⟨i⟩ := nonempty_inv_iso_quasicoherentInverse.{u, u + 1, u, u} B S hS X p hp e
    (restrictionPreservesQuasicoherent B S hS X p hp e)
    (projectionModulePullbackAdjunction.{u, u + 1, u, u} B S hS X p hp e) Pq hPq
    hunit hcounit
  exact ⟨Functor.isoWhiskerRight i (FibredSite.toSiteModules B S hS p hp .etale) ≪≫ hPq⟩

end SmallFibred

end AlgebraicGeometry.Space

end
