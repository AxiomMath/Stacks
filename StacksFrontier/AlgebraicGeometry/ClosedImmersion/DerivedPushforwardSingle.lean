module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ExactPushforwardSingleComp

/-!
# `(i_* F)[0] ≅ Ri_*(F[0])` for a closed immersion of schemes

Let `i : X' ⟶ X` be a closed immersion of schemes. The direct image `i_*` of sheaves of modules
is exact, so a module placed in degree `0` has no higher direct images: there is an isomorphism
`(i_* F)[0] ≅ Ri_*(F[0])`, natural in the `𝒪_{X'}`-module `F` (no quasi-coherence is needed). Along
a composite `k = j ≫ i` of closed immersions it is compatible with the composition isomorphisms of
the direct images and of the derived pushforwards.

## Main definitions

* `AlgebraicGeometry.closedImmersionDerivedPushforwardSingleIso`: the natural isomorphism
  `i_* ⋙ (-)[0] ≅ (-)[0] ⋙ Ri_*` of functors `X'.Modules ⥤ D(X)`.

## Main results

* `AlgebraicGeometry.closedImmersionDerivedPushforwardSingleIso_comp_hom_app`: the compatibility
  with `Scheme.Modules.pushforwardComp`, `Scheme.Modules.pushforwardCongr` and
  `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCompIso` along `j ≫ i = k`.

## Implementation notes

Both are the ringed-space statements
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardSingleIso` and
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardSingleIso_comp_hom_app` at the
underlying morphisms of ringed spaces, where exactness of the direct image is
`Stacks.ClosedImmersion.preservesFiniteColimits_modulePushforward_of_isClosedImmersion`. The type
ascriptions read them between the derived categories of `X'.Modules` and `X.Modules`, the spelling
of `Scheme.Modules.pushforward`, the same functor as
`RingedSpaceModuleAdjunction.modulePushforward` of the underlying morphism of ringed spaces. They
live at the standard model `HasDerivedCategory.standard`, the only model at which the derived
pushforward along a morphism of schemes is reached in this spelling; it is installed for each
declaration only.

## References

* [Stacks Project, Tag 01XC](https://stacks.math.columbia.edu/tag/01XC)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

namespace AlgebraicGeometry

universe u

noncomputable section

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **`(i_* F)[0] ≅ Ri_*(F[0])` for a closed immersion of schemes**, naturally in the
`𝒪_{X'}`-module `F`.

This is `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardSingleIso` at the
underlying morphism of ringed spaces, along which the direct image is exact; it is read between the
derived categories of `X'.Modules` and `X.Modules`. Stated at the standard model
`HasDerivedCategory.standard`, installed for this declaration only. -/
def closedImmersionDerivedPushforwardSingleIso {X' X : Scheme.{u}} (i : X' ⟶ X)
    [IsClosedImmersion i] :
    Scheme.Modules.pushforward i ⋙ DerivedCategory.singleFunctor X.Modules 0 ≅
      DerivedCategory.singleFunctor X'.Modules 0 ⋙
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward i.toLRSHom.toShHom :
          DerivedCategory X'.Modules ⥤ DerivedCategory X.Modules) :=
  Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardSingleIso i.toLRSHom.toShHom

/-- `Scheme.Modules.pushforwardCongr` at a reflexivity proof has identity components. -/
private theorem pushforwardCongr_rfl_inv_app {X' X : Scheme.{u}} (f : X' ⟶ X) (F : X'.Modules) :
    (Scheme.Modules.pushforwardCongr (rfl : f = f)).inv.app F = 𝟙 _ := by
  ext U
  simp

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **`(k_* F)[0] ≅ Rk_*(F[0])` along a composite `k = j ≫ i` of closed immersions.** For closed
immersions of schemes `j : X'' ⟶ X'`, `i : X' ⟶ X` and `k` with `j ≫ i = k`,
`closedImmersionDerivedPushforwardSingleIso k` at a module `F` on `X''` is the composition
isomorphism `(k_* F)[0] ≅ (i_* j_* F)[0]` of the direct images
(`Scheme.Modules.pushforwardComp` followed by `Scheme.Modules.pushforwardCongr`), then the
isomorphism for `i` at `j_* F`, then `Ri_*` of the isomorphism for `j` at `F`, then the composition
isomorphism `Ri_*(Rj_*(F[0])) ≅ Rk_*(F[0])` of the derived pushforwards
(`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCompIso` at the underlying
morphisms of ringed spaces, transported along `j ≫ i = k` read on those morphisms).

Stated at the standard model `HasDerivedCategory.standard`, the model of
`derivedPushforwardCompIso`, installed for this declaration only. -/
theorem closedImmersionDerivedPushforwardSingleIso_comp_hom_app {X'' X' X : Scheme.{u}}
    (j : X'' ⟶ X') (i : X' ⟶ X) (k : X'' ⟶ X) (hk : j ≫ i = k)
    [IsClosedImmersion j] [IsClosedImmersion i] [IsClosedImmersion k] (F : X''.Modules) :
    (closedImmersionDerivedPushforwardSingleIso k).hom.app F =
      (DerivedCategory.singleFunctor X.Modules 0).map
          ((Scheme.Modules.pushforwardComp j i ≪≫ Scheme.Modules.pushforwardCongr hk).inv.app F) ≫
        (closedImmersionDerivedPushforwardSingleIso i).hom.app
          ((Scheme.Modules.pushforward j).obj F) ≫
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward i.toLRSHom.toShHom :
            DerivedCategory X'.Modules ⥤ DerivedCategory X.Modules).map
          ((closedImmersionDerivedPushforwardSingleIso j).hom.app F) ≫
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCompIso
            j.toLRSHom.toShHom i.toLRSHom.toShHom ≪≫
          eqToIso (congrArg (fun h : X''.toLocallyRingedSpace.toSheafedSpace ⟶
              X.toLocallyRingedSpace.toSheafedSpace =>
            Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward h)
              (show j.toLRSHom.toShHom ≫ i.toLRSHom.toShHom = k.toLRSHom.toShHom from
                congrArg (fun m : X'' ⟶ X => m.toLRSHom.toShHom) hk))).hom.app
          ((DerivedCategory.singleFunctor X''.Modules 0).obj F) := by
  subst hk
  have : PreservesFiniteColimits
      (modulePushforward (j.toLRSHom.toShHom ≫ i.toLRSHom.toShHom)) :=
    inferInstanceAs (PreservesFiniteColimits (modulePushforward (j ≫ i).toLRSHom.toShHom))
  have h :=
    Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardSingleIso_comp_hom_app
      j.toLRSHom.toShHom i.toLRSHom.toShHom F
  have h1 : (modulePushforwardComp j.toLRSHom.toShHom i.toLRSHom.toShHom).inv.app F =
      (Scheme.Modules.pushforwardComp j i ≪≫ Scheme.Modules.pushforwardCongr rfl).inv.app F := by
    rw [Iso.trans_inv, NatTrans.comp_app, pushforwardCongr_rfl_inv_app, Category.id_comp]
    rfl
  have h2 : ∀ Y, (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCompIso
        j.toLRSHom.toShHom i.toLRSHom.toShHom).hom.app Y =
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCompIso
          j.toLRSHom.toShHom i.toLRSHom.toShHom ≪≫
        eqToIso (congrArg (fun h : X''.toLocallyRingedSpace.toSheafedSpace ⟶
            X.toLocallyRingedSpace.toSheafedSpace =>
          Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward h)
            (show j.toLRSHom.toShHom ≫ i.toLRSHom.toShHom = (j ≫ i).toLRSHom.toShHom from
              rfl))).hom.app Y := fun Y => by
    simp only [Iso.trans_hom, NatTrans.comp_app, eqToIso.hom, eqToHom_app]
    exact (Category.comp_id _).symm
  rw [h1, h2] at h
  exact h

end

end AlgebraicGeometry

end
