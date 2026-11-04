module

public import Mathlib.Topology.Sets.OpenCover
public import Mathlib.Topology.Sheaves.Stalks
public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.AlgebraicGeometry.SectionsColimit.Basic

/-!
# Local criteria for a morphism of modules to be invertible, and inverse images

This file collects the three facts about sheaves of modules on schemes that the base-change
assertion of Stacks Tag 02KG is proved from: that invertibility is local on the scheme, that
on an affine scheme invertibility of a morphism of quasi-coherent modules is detected on
global sections, and that the inverse image of a quasi-coherent module is quasi-coherent.

## Main results

* `Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_stalk` and
  `Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_restrict`: a morphism of sheaves
  of modules which is invertible on every stalk, respectively whose restriction to each member
  of an open covering is invertible, is invertible.
* `Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_moduleSpecΓ`: on an affine scheme
  a morphism of quasi-coherent modules which is invertible on global sections is invertible.
* `Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback`: the inverse image of a
  quasi-coherent module along an arbitrary morphism of schemes is quasi-coherent.  This is
  Stacks Tag 01BG; the affine case `isQuasicoherent_pullback_of_isAffine` is reduced to
  `Stacks.AlgebraicGeometry.SectionsColimit.isQuasicoherent_pullback_specMap` by conjugating
  with `AlgebraicGeometry.Scheme.isoSpec`.

## Implementation notes

`isIso_of_isIso_stalk` is Mathlib's `TopCat.Presheaf.isIso_of_stalkFunctor_map_iso` for the
underlying sheaf of abelian groups, combined with the fact that
`AlgebraicGeometry.Scheme.Modules.toPresheaf` reflects isomorphisms.  Locality is then
obtained from `AlgebraicGeometry.Scheme.Modules.restrictStalkNatIso`, which identifies the
stalks of a restriction with the stalks of the original module.

`isIso_of_isIso_moduleSpecΓ` is the naturality of
`AlgebraicGeometry.Scheme.Modules.fromTildeΓNatTrans` together with
`AlgebraicGeometry.isQuasicoherent_iff_isIso_fromTildeΓ`, which makes the components of that
natural transformation invertible at quasi-coherent modules.

For `isQuasicoherent_pullback` the covering used is the one produced by
`TopologicalSpace.Opens.IsBasis.isOpenCover_mem_and_le` from the affine opens of the source
and the preimages of the affine opens of the target: over such a member `U`, lying over an
affine open `V`, the morphism factors as `U.ι ≫ f = f.resLE V U _ ≫ V.ι`, so the restriction
of `f ^* F` to `U` is an inverse image of `F.restrict V.ι` along a morphism of affine schemes.

Several `IsIso` instances below are supplied by explicit application of
`CategoryTheory.IsIso.comp_isIso` rather than by `infer_instance`: the category structure on
`AlgebraicGeometry.Scheme.Modules` is a different instance from the one on `SheafOfModules`,
equal to it only after unfolding a non-reducible definition, and instance search does not see
through that.

## References

* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.AffineBaseChange

/-! ### Invertibility is local -/

/-- A morphism of sheaves of modules on a scheme which is invertible on every stalk is
invertible. -/
theorem isIso_of_isIso_stalk {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N)
    (h : ∀ x : X, IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map φ.mapPresheaf)) :
    IsIso φ := by
  rw [← isIso_iff_of_reflects_iso _ (Scheme.Modules.toPresheaf X)]
  let ψ : (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf Ab.{u} X.toTopCat) ⟶
      ⟨N.presheaf, N.isSheaf⟩ := ⟨φ.mapPresheaf⟩
  have := TopCat.Presheaf.isIso_of_stalkFunctor_map_iso ψ
  exact (TopCat.Sheaf.forget Ab.{u} X.toTopCat).map_isIso ψ

/-- If a natural transformation is invertible at `X` and `Y`, then `F.map φ` being invertible
implies that `G.map φ` is. -/
private theorem isIso_map_of_isIso_app {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    (α : F ⟶ G) {X Y : C} (φ : X ⟶ Y) [IsIso (α.app X)] [IsIso (α.app Y)] [IsIso (F.map φ)] :
    IsIso (G.map φ) := by
  have : IsIso (α.app X ≫ G.map φ) := by
    rw [← α.naturality φ]
    infer_instance
  exact IsIso.of_isIso_comp_left (α.app X) _

/-- Invertibility of a morphism of sheaves of modules on a scheme is local on the scheme: it
suffices that the restriction to each member of an open covering be invertible. -/
theorem isIso_of_isIso_restrict {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N)
    {I : Type*} (U : I → X.Opens) (hU : IsOpenCover U)
    (h : ∀ i, IsIso ((Scheme.Modules.restrictFunctor (U i).ι).map φ)) : IsIso φ := by
  have key : ∀ (i : I) (y : (U i).toScheme), IsIso ((Scheme.Modules.toPresheaf X ⋙
      TopCat.Presheaf.stalkFunctor Ab.{u} ((U i).ι y)).map φ) := by
    intro i y
    have : IsIso ((Scheme.Modules.restrictFunctor (U i).ι).map φ) := h i
    have h3 : IsIso ((Scheme.Modules.restrictFunctor (U i).ι ⋙ Scheme.Modules.toPresheaf _ ⋙
        TopCat.Presheaf.stalkFunctor Ab.{u} y).map φ) :=
      Functor.map_isIso (Scheme.Modules.toPresheaf _ ⋙
        TopCat.Presheaf.stalkFunctor Ab.{u} y) _
    exact isIso_map_of_isIso_app (Scheme.Modules.restrictStalkNatIso (U i).ι y).hom φ
  refine isIso_of_isIso_stalk φ fun x ↦ ?_
  obtain ⟨i, hi⟩ := hU.exists_mem x
  exact key i ⟨x, hi⟩

/-! ### The affine criterion -/

/-- On an affine scheme, a morphism of quasi-coherent modules which is invertible on global
sections is invertible. -/
theorem isIso_of_isIso_moduleSpecΓ {R : CommRingCat.{u}} {M N : (Spec R).Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (φ : M ⟶ N)
    (h : IsIso (moduleSpecΓFunctor.map φ)) : IsIso φ := by
  have : IsIso (Scheme.Modules.fromTildeΓNatTrans.app M) :=
    (isQuasicoherent_iff_isIso_fromTildeΓ M).mp ‹_›
  have : IsIso (Scheme.Modules.fromTildeΓNatTrans.app N) :=
    (isQuasicoherent_iff_isIso_fromTildeΓ N).mp ‹_›
  have : IsIso ((moduleSpecΓFunctor (R := R) ⋙ tilde.functor R).map φ) :=
    Functor.map_isIso (tilde.functor R) _
  exact isIso_map_of_isIso_app (G := 𝟭 _) Scheme.Modules.fromTildeΓNatTrans φ

/-! ### Quasi-coherence of the inverse image -/

/-- The inverse image of a quasi-coherent module along an open immersion is quasi-coherent. -/
theorem isQuasicoherent_pullback_of_isOpenImmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (N : Y.Modules) [N.IsQuasicoherent] :
    ((Scheme.Modules.pullback f).obj N).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    ((Scheme.Modules.restrictFunctorIsoPullback f).app N) inferInstance

/-- The inverse image of a quasi-coherent module along a morphism of affine schemes is
quasi-coherent. -/
theorem isQuasicoherent_pullback_of_isAffine {Y Z : Scheme.{u}} [IsAffine Y] [IsAffine Z]
    (h : Y ⟶ Z) (N : Z.Modules) [N.IsQuasicoherent] :
    ((Scheme.Modules.pullback h).obj N).IsQuasicoherent := by
  have key : h = Y.isoSpec.hom ≫ (Spec.map h.appTop ≫ Z.isoSpec.inv) := by
    rw [Scheme.isoSpec_inv_naturality, Iso.hom_inv_id_assoc]
  have h₁ := isQuasicoherent_pullback_of_isOpenImmersion Z.isoSpec.inv N
  have h₂ := SectionsColimit.isQuasicoherent_pullback_specMap h.appTop
    ((Scheme.Modules.pullback Z.isoSpec.inv).obj N)
  have h₃ := isQuasicoherent_pullback_of_isOpenImmersion Y.isoSpec.hom
    ((Scheme.Modules.pullback (Spec.map h.appTop)).obj
      ((Scheme.Modules.pullback Z.isoSpec.inv).obj N))
  have iso : (Scheme.Modules.pullback Y.isoSpec.hom).obj
      ((Scheme.Modules.pullback (Spec.map h.appTop)).obj
        ((Scheme.Modules.pullback Z.isoSpec.inv).obj N)) ≅
      (Scheme.Modules.pullback h).obj N :=
    (Scheme.Modules.pullback Y.isoSpec.hom).mapIso
        ((Scheme.Modules.pullbackComp (Spec.map h.appTop) Z.isoSpec.inv).app N) ≪≫
      (Scheme.Modules.pullbackComp Y.isoSpec.hom (Spec.map h.appTop ≫ Z.isoSpec.inv)).app N ≪≫
      (Scheme.Modules.pullbackCongr key).symm.app N
  exact (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso iso h₃

/-- **Stacks Project, Tag 01BG.** The inverse image of a quasi-coherent module along an
arbitrary morphism of schemes is quasi-coherent. -/
theorem isQuasicoherent_pullback {X S : Scheme.{u}} (f : X ⟶ S) (F : S.Modules)
    [F.IsQuasicoherent] : ((Scheme.Modules.pullback f).obj F).IsQuasicoherent := by
  have hU := X.isBasis_affineOpens.isOpenCover_mem_and_le
    ((S.isBasis_affineOpens).isOpenCover.comap f.base.hom)
  refine AffinePushforward.isQuasicoherent_of_presentations _ _ hU (fun W ↦ ?_)
  obtain ⟨⟨U₀, V₀⟩, hUaff, hle⟩ := W
  set U : X.Opens := U₀ with hUdef
  set V : S.Opens := (V₀ : S.Opens) with hVdef
  have hV : IsAffine V.toScheme := V₀.2
  have hUa : IsAffine U.toScheme := hUaff
  have hle' : U ≤ f ⁻¹ᵁ V := hle
  have hr : U.ι ≫ f = f.resLE V U hle' ≫ V.ι := (Scheme.Hom.resLE_comp_ι f hle').symm
  have hqc := isQuasicoherent_pullback_of_isAffine (f.resLE V U hle') (F.restrict V.ι)
  have iso : (Scheme.Modules.pullback (f.resLE V U hle')).obj (F.restrict V.ι) ≅
      ((Scheme.Modules.pullback f).obj F).restrict U.ι :=
    (Scheme.Modules.pullback (f.resLE V U hle')).mapIso
        ((Scheme.Modules.restrictFunctorIsoPullback V.ι).app F) ≪≫
      (Scheme.Modules.pullbackComp (f.resLE V U hle') V.ι).app F ≪≫
      (Scheme.Modules.pullbackCongr hr).symm.app F ≪≫
      ((Scheme.Modules.pullbackComp U.ι f).app F).symm ≪≫
      ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app
        ((Scheme.Modules.pullback f).obj F)).symm
  have : (((Scheme.Modules.pullback f).obj F).restrict U.ι).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).prop_of_iso iso hqc
  exact (AffinePushforward.nonempty_presentation_of_isoSpec hUaff.isoSpec _).some

end Stacks.AlgebraicGeometry.AffineBaseChange

end
