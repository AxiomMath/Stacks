module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRelocalize
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentModules
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalTypesUnderSpecialCocontinuous
public import StacksFrontier.AlgebraicGeometry.Topologies.CoherentKernelOnSite

/-!
# Modules on an algebraic space and on its lower-shriek extension

Let `h : W ⟶ S` be a morphism of a big fppf site and let `F` be an algebraic space over `W`,
with lower-shriek extension `Λ_h F`, an algebraic space over `S`.  The equivalence of small
étale sites `AlgebraicGeometry.Space.SmallEtale.relocalizeEquivalence` does not change the
scheme underlying a chart and carries the structure sheaf of `Λ_h F` to that of `F` on the nose,
so reindexing along it identifies the `𝒪`-modules on the two spaces.  This file records that
equivalence of module categories and the invariance of quasi-coherence and coherence under it.

## Main definitions

* `AlgebraicGeometry.Space.relocalizeModulesEquivalenceSE`: the equivalence
  `Mod(𝒪_F) ≌ Mod(𝒪_{Λ_h F})`.

## Main results

* `AlgebraicGeometry.Space.isQuasicoherentOnSite_relocalizeModulesEquivalence_inverse_iff` and
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_relocalizeModulesEquivalence_functor_iff`:
  quasi-coherence is preserved and reflected.
* `AlgebraicGeometry.Space.isCoherentOnSite_relocalizeModulesEquivalenceSE_inverse_iff`,
  `AlgebraicGeometry.Space.isCoherentOnSite_relocalizeModulesEquivalence_functor_iff`,
  `AlgebraicGeometry.Space.isCoherent_relocalizeModulesEquivalenceSE_inverse_iff` and
  `AlgebraicGeometry.Space.isCoherent_relocalizeModulesEquivalence_functor_iff`: coherence
  (Stacks 07UA) is preserved and reflected.

## Implementation notes

The inverse functor of the equivalence is the direct image along the functor of the equivalence
of sites, with the identity as structure map; it is the restriction of modules to a dense
subsite along a cocontinuous functor, so coherence travels along it by the special cocontinuous
case of Stacks 03DM, `Stacks.Sheaves.SpecialCocontinuous.isCoherentOnSite_iff`.  The forward
direction is read off the unit of the equivalence.

## References

* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
* [Stacks Project, Tag 07UA](https://stacks.math.columbia.edu/tag/07UA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (W S : Scheme.{u}) (hW : B.Contains W) (hS : B.Contains S)
  (h : B.obj hW ⟶ B.obj hS) {F : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u}

namespace SmallEtale

/-- The functor of the equivalence of small étale sites carries covering families to covering
families. -/
theorem relocalizeEquivalence_functor_coverPreserving :
    CoverPreserving (topology B W hW F)
      (topology B S hS ((OverShriek.relocalizePresheafFunctor h).obj F))
      (relocalizeEquivalence B W S hW hS h F).functor :=
  Functor.isContinuous_iff_coverPreserving.1 inferInstance

/-- The inverse of the equivalence of small étale sites carries covering families to covering
families. -/
theorem relocalizeEquivalence_inverse_coverPreserving :
    CoverPreserving (topology B S hS ((OverShriek.relocalizePresheafFunctor h).obj F))
      (topology B W hW F) (relocalizeEquivalence B W S hW hS h F).inverse :=
  Functor.isContinuous_iff_coverPreserving.1 inferInstance

/-- The functor of the equivalence of small étale sites is cocontinuous. -/
instance isCocontinuous_relocalizeEquivalence_functor :
    (relocalizeEquivalence B W S hW hS h F).functor.IsCocontinuous (topology B W hW F)
      (topology B S hS ((OverShriek.relocalizePresheafFunctor h).obj F)) :=
  ((relocalizeEquivalence B W S hW hS h F).toAdjunction.isCocontinuous_iff_coverPreserving _ _).2
    (relocalizeEquivalence_inverse_coverPreserving B W S hW hS h)

/-- The inverse of the equivalence of small étale sites is cocontinuous. -/
instance isCocontinuous_relocalizeEquivalence_inverse :
    (relocalizeEquivalence B W S hW hS h F).inverse.IsCocontinuous
      (topology B S hS ((OverShriek.relocalizePresheafFunctor h).obj F)) (topology B W hW F) :=
  ((relocalizeEquivalence B W S hW hS h F).symm.toAdjunction.isCocontinuous_iff_coverPreserving
    _ _).2 (relocalizeEquivalence_functor_coverPreserving B W S hW hS h)

/-- The small étale site of `F` is a dense subsite of that of `Λ_h F` along the functor of the
equivalence of small étale sites. -/
instance isDenseSubsite_relocalizeEquivalence_functor :
    (relocalizeEquivalence B W S hW hS h F).functor.IsDenseSubsite (topology B W hW F)
      (topology B S hS ((OverShriek.relocalizePresheafFunctor h).obj F)) :=
  Equivalence.isDenseSubsite_functor_of_isCocontinuous _ _ (relocalizeEquivalence B W S hW hS h F)

end SmallEtale

variable (hF : IsAlgebraicSpace B W hW F)
  (hF' : IsAlgebraicSpace B S hS ((OverShriek.relocalizePresheafFunctor h).obj F))

/-- The structure sheaf of rings of `Λ_h F`, typed at the small étale topology. -/
abbrev relocalizeRingSheafSE :
    Sheaf (SmallEtale.topology B S hS ((OverShriek.relocalizePresheafFunctor h).obj F))
      RingCat.{u} :=
  Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS _ hF').O

/-- **The `𝒪`-modules of `F` are the `𝒪`-modules of `Λ_h F`**: reindexing along the equivalence
of small étale sites, whose inverse is the direct image along the functor of that
equivalence. -/
def relocalizeModulesEquivalenceSE :
    Modules.{u, u} B W hW F hF ≌ Modules.{u, u} B S hS _ hF' :=
  (Stacks.SheafOfModules.reindexEquivalence (J' := SmallEtale.topology B W hW F)
    (SmallEtale.relocalizeEquivalence B W S hW hS h F)
    (relocalizeRingSheafSE B W S hW hS h hF')).symm

/-- The inverse of the equivalence of module categories is the restriction of modules along the
functor of the equivalence of small étale sites. -/
theorem relocalizeModulesEquivalence_inverse :
    (relocalizeModulesEquivalenceSE B W S hW hS h hF hF').inverse =
      Stacks.DenseSubsiteModules.moduleRestriction (SmallEtale.topology B W hW F)
        (SmallEtale.topology B S hS _) (SmallEtale.relocalizeEquivalence B W S hW hS h F).functor
        (relocalizeRingSheafSE B W S hW hS h hF') :=
  rfl

/-- The sections of the module attached to a module on `Λ_h F` over a chart of `F` are its
sections over the corresponding chart of `Λ_h F`. -/
theorem relocalizeModulesEquivalence_inverse_obj_val_obj
    (M : Modules.{u, u} B S hS _ hF') (U : (SmallEtale B W hW F)ᵒᵖ) :
    ((relocalizeModulesEquivalenceSE B W S hW hS h hF hF').inverse.obj M).val.obj U =
      M.val.obj (op ((SmallEtale.relocalizeEquivalence B W S hW hS h F).functor.obj U.unop)) :=
  rfl

/-- **Quasi-coherence is carried from `Λ_h F` to `F` and back.** -/
theorem isQuasicoherentOnSite_relocalizeModulesEquivalence_inverse_iff
    (M : Modules.{u, u} B S hS _ hF') :
    ((relocalizeModulesEquivalenceSE B W S hW hS h hF hF').inverse.obj M).IsQuasicoherentOnSite ↔
      M.IsQuasicoherentOnSite :=
  Stacks.SheafOfModules.isQuasicoherentOnSite_reindex_iff (J' := SmallEtale.topology B W hW F)
    (J := SmallEtale.topology B S hS _)
    (SmallEtale.relocalizeEquivalence B W S hW hS h F) (relocalizeRingSheafSE B W S hW hS h hF') M

/-- **Quasi-coherence is carried from `F` to `Λ_h F` and back.** -/
theorem isQuasicoherentOnSite_relocalizeModulesEquivalence_functor_iff
    (N : Modules.{u, u} B W hW F hF) :
    ((relocalizeModulesEquivalenceSE B W S hW hS h hF hF').functor.obj N).IsQuasicoherentOnSite ↔
      N.IsQuasicoherentOnSite :=
  (isQuasicoherentOnSite_relocalizeModulesEquivalence_inverse_iff B W S hW hS h hF hF' _).symm.trans
    ⟨fun hN => SheafOfModules.IsQuasicoherentOnSite.of_iso
      ((relocalizeModulesEquivalenceSE B W S hW hS h hF hF').unitIso.app N).symm hN,
    fun hN => SheafOfModules.IsQuasicoherentOnSite.of_iso
      ((relocalizeModulesEquivalenceSE B W S hW hS h hF hF').unitIso.app N) hN⟩

/-- **Coherence on the site is carried from `Λ_h F` to `F` and back**: the special cocontinuous
case of Stacks 03DM. -/
theorem isCoherentOnSite_relocalizeModulesEquivalenceSE_inverse_iff
    (M : Modules.{u, u} B S hS _ hF') :
    ((relocalizeModulesEquivalenceSE B W S hW hS h hF hF').inverse.obj M).IsCoherentOnSite ↔
      M.IsCoherentOnSite :=
  (Stacks.Sheaves.SpecialCocontinuous.isCoherentOnSite_iff (SmallEtale.topology B W hW F)
    (SmallEtale.topology B S hS _) (SmallEtale.relocalizeEquivalence B W S hW hS h F).functor
    (relocalizeRingSheafSE B W S hW hS h hF') M).symm

/-- **Coherence on the site is carried from `F` to `Λ_h F` and back.** -/
theorem isCoherentOnSite_relocalizeModulesEquivalence_functor_iff
    (N : Modules.{u, u} B W hW F hF) :
    ((relocalizeModulesEquivalenceSE B W S hW hS h hF hF').functor.obj N).IsCoherentOnSite ↔
      N.IsCoherentOnSite :=
  (isCoherentOnSite_relocalizeModulesEquivalenceSE_inverse_iff B W S hW hS h hF hF' _).symm.trans
    ⟨fun hN => Stacks.SheafOfModules.isCoherentOnSite_of_iso
      ((relocalizeModulesEquivalenceSE B W S hW hS h hF hF').unitIso.app N).symm hN,
    fun hN => Stacks.SheafOfModules.isCoherentOnSite_of_iso
      ((relocalizeModulesEquivalenceSE B W S hW hS h hF hF').unitIso.app N) hN⟩

/-- Coherence of modules on two algebraic spaces agrees as soon as quasi-coherence and coherence
on the site do. -/
private theorem isCoherent_iff_of_iff {B₁ B₂ : BigFppfSite.{u}} {W₁ W₂ : Scheme.{u}}
    {hW₁ : B₁.Contains W₁} {hW₂ : B₂.Contains W₂} {F₁ : (BigFppfOver B₁ W₁ hW₁)ᵒᵖ ⥤ Type u}
    {F₂ : (BigFppfOver B₂ W₂ hW₂)ᵒᵖ ⥤ Type u} {hF₁ : IsAlgebraicSpace B₁ W₁ hW₁ F₁}
    {hF₂ : IsAlgebraicSpace B₂ W₂ hW₂ F₂} {M : Modules.{u, u} B₁ W₁ hW₁ F₁ hF₁}
    {N : Modules.{u, u} B₂ W₂ hW₂ F₂ hF₂} (hq : M.IsQuasicoherentOnSite ↔ N.IsQuasicoherentOnSite)
    (hc : M.IsCoherentOnSite ↔ N.IsCoherentOnSite) :
    IsCoherent B₁ W₁ hW₁ F₁ hF₁ M ↔ IsCoherent B₂ W₂ hW₂ F₂ hF₂ N :=
  ⟨fun h => IsCoherent.mk (toIsQuasicoherentOnSite := hq.1 h.toIsQuasicoherentOnSite)
      (toIsCoherentOnSite := hc.1 h.toIsCoherentOnSite),
    fun h => IsCoherent.mk (toIsQuasicoherentOnSite := hq.2 h.toIsQuasicoherentOnSite)
      (toIsCoherentOnSite := hc.2 h.toIsCoherentOnSite)⟩

/-- **Coherence (Stacks 07UA) is carried from `Λ_h F` to `F` and back.** -/
theorem isCoherent_relocalizeModulesEquivalenceSE_inverse_iff (M : Modules.{u, u} B S hS _ hF') :
    IsCoherent B W hW F hF ((relocalizeModulesEquivalenceSE B W S hW hS h hF hF').inverse.obj M) ↔
      IsCoherent B S hS _ hF' M :=
  isCoherent_iff_of_iff
    (isQuasicoherentOnSite_relocalizeModulesEquivalence_inverse_iff B W S hW hS h hF hF' M)
    (isCoherentOnSite_relocalizeModulesEquivalenceSE_inverse_iff B W S hW hS h hF hF' M)

/-- **Coherence (Stacks 07UA) is carried from `F` to `Λ_h F` and back.** -/
theorem isCoherent_relocalizeModulesEquivalence_functor_iff (N : Modules.{u, u} B W hW F hF) :
    IsCoherent B S hS _ hF' ((relocalizeModulesEquivalenceSE B W S hW hS h hF hF').functor.obj N) ↔
      IsCoherent B W hW F hF N :=
  isCoherent_iff_of_iff
    (isQuasicoherentOnSite_relocalizeModulesEquivalence_functor_iff B W S hW hS h hF hF' N)
    (isCoherentOnSite_relocalizeModulesEquivalence_functor_iff B W S hW hS h hF hF' N)

end AlgebraicGeometry.Space

end
