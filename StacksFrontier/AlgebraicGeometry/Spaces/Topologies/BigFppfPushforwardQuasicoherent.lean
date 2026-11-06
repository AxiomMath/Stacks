module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.CartesianFaithfullyFlat
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DenseSubsiteBaseChangePresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalPresentationOfPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfAffineCartesianModules
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleAffineSchemesOver
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.JointlySurjectiveDescent
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentCokernels
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposSiteHomOfRingedSite

/-!
# The direct image `a_{X,*}` of a quasi-coherent module on `(Spaces/X)_fppf`

Let `T` be a big fppf site of algebraic spaces over a scheme `S`, `X` one of its objects and
`a_X : ((Spaces/X)_fppf, 𝒪) ⟶ (X_{spaces,étale}, 𝒪_X)` the morphism of Stacks 0DGM. For a
quasi-coherent `𝒪`-module `H` on `(Spaces/X)_fppf` the direct image `a_{X,*}H` is quasi-coherent.

Over an affine object `W` of the spaces-étale site, the restriction of `a_{X,*}H` to the affine
schemes étale over `W` has the sections and restriction maps of `H` itself, so it is cartesian
because `H` is (Stacks 03DX). A cartesian module on that dense subsite is the base change presheaf
of its sections over the terminal object, so `a_{X,*}H` is `M^a` over `W`, which has a global
presentation; the affine objects cover every object of the spaces-étale site.

## Main results

* `BigFppfSpaceSite.EtaleAffineSchemesOver.hasGlobalPresentation_pushforward_over`:
  over an affine object of the spaces-étale site, `a_{X,*}H` has a global presentation.
* `BigFppfSpaceSite.isQuasicoherentOnSite_pushforward_of_isQuasicoherentOnSite`:
  **`a_{X,*}H` is quasi-coherent**, the direct image half of Stacks 0DGN (5).

## Implementation notes

The restriction of `a_{X,*}H` to the affine schemes étale over `W` is compared with the
restriction of `H` along the inclusion of those into all affine schemes over `W` by
`EtaleAffineSchemesOver.pushforwardRestrictionValIso`, whose components are identities. The
target is written as `PresheafOfModules.pushforward` along the inclusion with structure map
`eqToHom rfl`, so that both sides are built from the same number of restrictions of scalars;
written as `PresheafOfModules.pushforward₀` the same identity is a `whnf` timeout.

## References

* [Stacks Project, Tag 0DGN](https://stacks.math.columbia.edu/tag/0DGN)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.BigFppfSpaceSite

variable {S : Scheme.{u}} {T : BigFppfSpaceSite S} {X : T.Spaces}

namespace EtaleAffineSchemesOver

variable {W : Space.SpacesEtale T.schemeSite S T.scheme_mem X} (V₀ : T.Schemes)
  (hV₀ : IsAffine ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).obj V₀))
  (e : (schemeSpaceFunctor T.schemeSite S T.scheme_mem).obj V₀ ≅ W.obj.left)

/-- The restriction of the direct image `a_{X,*}H` to the affine schemes étale over `W`. -/
noncomputable abbrev pushforwardRestriction (H : SheafOfModules.{u + 1} (bigFppfRingSheaf T X)) :
    SheafOfModules.{u + 1} (Stacks.DenseSubsiteModules.ringRestriction (topology W)
      ((Space.SpacesEtale.topology T.schemeSite S T.scheme_mem X).over W) (toSmallSlice W)
      sliceRingSheaf) :=
  (Stacks.DenseSubsiteModules.moduleRestriction (topology W)
    ((Space.SpacesEtale.topology T.schemeSite S T.scheme_mem X).over W) (toSmallSlice W)
    sliceRingSheaf).obj
    (((fppfToSpacesEtaleRingedSiteHom T X).toRingedToposSiteHom.pushforwardTopos.obj H).over W)

/-- The sections of the restriction of `a_{X,*}H` to the affine schemes étale over `W` are those of
the restriction of `H` to all affine schemes over `W`. -/
noncomputable def pushforwardRestrictionValIso (H : SheafOfModules.{u + 1} (bigFppfRingSheaf T X)) :
    (pushforwardRestriction (W := W) H).val ≅
      (PresheafOfModules.pushforward (F := (IsEtaleAffineSchemeOver W).ι)
        (R := AffineSchemesOver.ringPresheaf (T := T) (V := W.obj))
        (eqToHom (rfl : (ringPresheaf (W := W)) = (IsEtaleAffineSchemeOver W).ι.op ⋙
          AffineSchemesOver.ringPresheaf (T := T) (V := W.obj)))).obj
        (AffineSchemesOver.affineRestriction H).val :=
  PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) (fun _ _ _ ↦ rfl)

include hV₀ e in
/-- **The restriction of `a_{X,*}H` to the affine schemes étale over `W` is cartesian** when `H` is
locally presented: its base-change comparisons are those of `H` between affine schemes over `W`. -/
theorem isIso_restrictionBaseChange_pushforwardRestriction
    (H : SheafOfModules.{u + 1} (bigFppfRingSheaf T X))
    (hH : ∀ Z : BigFppfSpaceOver T X,
      Sieve.generate (fun (Z' : BigFppfSpaceOver T X) (_ : Z' ⟶ Z) ↦
        (H.over Z').HasGlobalPresentation) ∈ BigFppfSpaceOver.topology T X Z)
    {A B : EtaleAffineSchemesOver W} (k : A ⟶ B) :
    IsIso (Stacks.PresheafOfModules.restrictionBaseChange.{_, _, u + 1, u + 1}
      (R := Stacks.TerminalBaseChange.commPresheaf (ringPresheaf (W := W)))
      (pushforwardRestriction H).val k.op) := by
  have h := AffineSchemesOver.isIso_restrictionBaseChange_of_locallyPresented (U := W.obj)
    V₀ hV₀ e H hH ((IsEtaleAffineSchemeOver W).ι.map k)
  have h₁ : IsIso (Stacks.PresheafOfModules.restrictionBaseChange.{_, _, u + 1, u + 1}
      (R := Stacks.TerminalBaseChange.commPresheaf
        (AffineSchemesOver.ringPresheaf (T := T) (V := W.obj)))
      (AffineSchemesOver.affineRestriction H).val ((IsEtaleAffineSchemeOver W).ι.map k).op) :=
    h
  have h₂ := Stacks.PresheafOfModules.isIso_restrictionBaseChange_of_iso_presheafPushforward
    (IsEtaleAffineSchemeOver W).ι (AffineSchemesOver.ringPresheaf (T := T) (V := W.obj))
    (ringPresheaf (W := W)) rfl (AffineSchemesOver.affineRestriction H).val
    (pushforwardRestriction H).val (pushforwardRestrictionValIso H) k h₁
  convert h₂ using 2

set_option synthInstance.maxHeartbeats 400000 in
include hV₀ e in
/-- **Over an affine object `W` of the spaces-étale site, the direct image `a_{X,*}H` of a locally
presented module is `M^a`**, hence has a global presentation: on the affine schemes étale over
`W` it is cartesian over the morphisms to the terminal one, so it is the base change presheaf of
its sections over `W`. -/
theorem hasGlobalPresentation_pushforward_over
    (H : SheafOfModules.{u + 1} (bigFppfRingSheaf T X))
    (hH : ∀ Z : BigFppfSpaceOver T X,
      Sieve.generate (fun (Z' : BigFppfSpaceOver T X) (_ : Z' ⟶ Z) ↦
        (H.over Z').HasGlobalPresentation) ∈ BigFppfSpaceOver.topology T X Z) :
    (((fppfToSpacesEtaleRingedSiteHom T X).toRingedToposSiteHom.pushforwardTopos.obj H).over
      W).HasGlobalPresentation := by
  let hs := baseChangeIsSheaf V₀ hV₀ e
  let N := pushforwardRestriction (W := W) H
  have hc : IsIso (Stacks.TerminalBaseChange.baseChangeComparison.{u + 1} (ringPresheaf (W := W))
      (isTerminalOfIso V₀ hV₀ e) N.val) :=
    Stacks.TerminalBaseChange.isIso_baseChangeComparison_of_forall _ _ _ (fun U ↦ by
      have h := isIso_restrictionBaseChange_pushforwardRestriction V₀ hV₀ e H hH
        ((isTerminalOfIso V₀ hV₀ e).from U.unop)
      convert h using 2 <;> rfl)
  let M := N.val.obj (op (ofIso V₀ hV₀ e))
  let i₁ : (Stacks.DenseSubsiteBaseChange.baseChangeSheaf hs).obj M ≅ N :=
    (SheafOfModules.fullyFaithfulForget _).preimageIso
      (@asIso _ _ _ _ (Stacks.TerminalBaseChange.baseChangeComparison.{u + 1}
        (ringPresheaf (W := W)) (isTerminalOfIso V₀ hV₀ e) N.val) hc)
  let E := Stacks.DenseSubsiteModules.moduleRestrictionEquivalence (topology W)
    ((Space.SpacesEtale.topology T.schemeSite S T.scheme_mem X).over W) (toSmallSlice W)
    sliceRingSheaf
  let i₂ : ((fppfToSpacesEtaleRingedSiteHom T X).toRingedToposSiteHom.pushforwardTopos.obj H).over
      W ≅ (Stacks.DenseSubsiteBaseChange.associatedSheaf hs).obj M :=
    E.unitIso.app _ ≪≫ E.inverse.mapIso i₁.symm
  obtain ⟨p⟩ := Stacks.DenseSubsiteBaseChange.nonempty_presentation_associatedSheaf hs
    (isTerminal_toSmallSlice_ofIso V₀ hV₀ e) M
  exact SheafOfModules.HasGlobalPresentation.of_iso i₂.symm
    (SheafOfModules.HasGlobalPresentation.of_presentation' p)

end EtaleAffineSchemesOver

/-- **A quasi-coherent module on `(Spaces/X)_fppf` has a global presentation over the members of
a covering of every object.** -/
theorem generate_hasGlobalPresentation_mem_of_isQuasicoherentOnSite
    (H : SheafOfModules.{u + 1} (bigFppfRingSheaf T X)) [hH : H.IsQuasicoherentOnSite]
    (Z : BigFppfSpaceOver T X) :
    Sieve.generate (fun (Z' : BigFppfSpaceOver T X) (_ : Z' ⟶ Z) ↦
      (H.over Z').HasGlobalPresentation) ∈ BigFppfSpaceOver.topology T X Z := by
  obtain ⟨I, V, f, hcov, hpres⟩ := hH.locally_hasGlobalPresentation Z
  refine GrothendieckTopology.superset_covering _ ?_ hcov
  rw [Sieve.ofArrows, Sieve.generate_le_iff]
  rintro _ _ ⟨i⟩
  exact Sieve.le_generate _ _ _ (hpres i)

/-- **Stacks 0DGN (5), quasi-coherence of the direct image: `a_{X,*}H` is quasi-coherent** for a
quasi-coherent `𝒪`-module `H` on `(Spaces/X)_fppf`. Over every affine object `W` of the
spaces-étale site the direct image is `M^a` for its module of sections `M` over `W`, so it has a
global presentation there, and the affine objects cover every object. -/
theorem isQuasicoherentOnSite_pushforward_of_isQuasicoherentOnSite
    (H : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf (bigFppfRingedSite T X).O))
    [H.IsQuasicoherentOnSite] :
    ((fppfToSpacesEtaleRingedSiteHom T X).toRingedToposSiteHom.pushforwardTopos.obj
      H).IsQuasicoherentOnSite := by
  refine Stacks.SheafOfModules.isQuasicoherentOnSite_of_presentedSieve_mem _ (fun U ↦ ?_)
  refine GrothendieckTopology.superset_covering _ ?_
    (Space.SpacesEtale.generate_affineSchemePresieve_mem T.schemeSite S T.scheme_mem X U)
  rw [Sieve.generate_le_iff]
  rintro W _ ⟨V₀, hV₀, ⟨e⟩⟩
  exact EtaleAffineSchemesOver.hasGlobalPresentation_pushforward_over V₀ hV₀ e H
    (generate_hasGlobalPresentation_mem_of_isQuasicoherentOnSite H)

end AlgebraicGeometry.BigFppfSpaceSite

end
