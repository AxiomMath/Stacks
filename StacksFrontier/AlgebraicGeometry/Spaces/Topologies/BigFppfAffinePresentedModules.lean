module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfAffineCechVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfRingedTopos
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfRingedSite
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DenseSubsiteBaseChangePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.TensorQuasicoherent

/-!
# Presented modules on the affine objects of the big fppf site of an algebraic space

Let `T` be a big fppf site of algebraic spaces over a scheme `S`, `X` one of its objects and `U`
an object of `(Spaces/X)_fppf` identified with the algebraic space of an affine scheme. A sheaf
of modules on the slice at `U` which is the sheaf `M^a` attached to a module `M` over the ring
of `U` restricts, on the affine schemes over `U`, to the base change presheaf
`A ↦ 𝒪(A) ⊗ M`. Consequently the higher fppf cohomology of a sheaf of modules vanishes on every
affine object over which it has a global presentation.

The morphism `a_X` of Stacks 0DGM is also recorded as a morphism of ringed *sites*, with the
inclusion of the spaces-étale site as its functor.

## Main definitions

* `AlgebraicGeometry.BigFppfSpaceSite.fppfToSpacesEtaleRingedSiteHom`: `a_X` as a morphism of
  ringed sites.

## Main results

* `AlgebraicGeometry.BigFppfSpaceSite.AffineSchemesOver.nonempty_toOver_iso_baseChange`: the
  restriction of a sheaf of modules identified with `M^a` on the slice at `U` to the affine
  schemes over `U` is the base change presheaf.
* `AffineSchemesOver.exists_toOver_iso_baseChange_of_hasGlobalPresentation`: a sheaf of modules
  with a global presentation on the slice at `U` restricts to a base change presheaf on the
  affine schemes over `U`.
* `AlgebraicGeometry.BigFppfSpaceSite.isZero_H'_of_hasGlobalPresentation`: higher cohomology of a
  sheaf of modules vanishes on an affine object over which it has a global presentation.

## References

* [Stacks Project, Tag 0DGM](https://stacks.math.columbia.edu/tag/0DGM)
* [Stacks Project, Tag 0DGN](https://stacks.math.columbia.edu/tag/0DGN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.BigFppfSpaceSite

variable {S : Scheme.{u}} {T : BigFppfSpaceSite S} {X : T.Spaces}

variable (T X) in
/-- **The morphism `a_X` of Stacks 0DGM as a morphism of ringed sites**
`((Spaces/X)_fppf, 𝒪) ⟶ (X_{spaces,étale}, 𝒪_X)`: its functor is the inclusion of the
spaces-étale site and its structure map is the identity on global regular functions. -/
noncomputable def fppfToSpacesEtaleRingedSiteHom :
    RingedSite.Hom (bigFppfRingedSite T X)
      (Space.spacesEtaleRingedSite T.schemeSite S T.scheme_mem X) where
  u := Space.SpacesEtale.inclusion T.schemeSite S T.scheme_mem X
  isMorphismOfSites := spacesEtaleInclusion_isMorphismOfSites T X
  fsharp := (spacesEtaleRestrictionStructureIso T X).hom

namespace AffineSchemesOver

variable {U : BigFppfSpaceOver T X}

/-- **On the affine schemes over `U`, a sheaf of modules identified with `M^a` on the slice at
`U` is the base change presheaf `A ↦ 𝒪(A) ⊗ M`.** -/
theorem nonempty_toOver_iso_baseChange (N : SheafOfModules.{u + 1} (bigFppfRingSheaf T X))
    (W : T.Schemes) (hW : IsAffine ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).obj W))
    (eW : (schemeSpaceFunctor T.schemeSite S T.scheme_mem).obj W ≅ U.left)
    (M : ModuleCat.{u + 1} ((ringPresheaf (T := T) (V := U)).obj (op (ofIso W hW eW))))
    (e : N.over U ≅ (associatedSheaf W hW eW).obj M) :
    Nonempty ((toOver T U).op ⋙ ((SheafOfModules.toSheaf _).obj N).obj ≅
      ((Stacks.TerminalBaseChange.baseChangePresheaf.{u + 1} (ringPresheaf (T := T) (V := U))
        (isTerminalOfIso W hW eW)).obj M).presheaf) := by
  let R := Stacks.DenseSubsiteModules.moduleRestriction (topology (T := T) (V := U))
    ((BigFppfSpaceOver.topology T X).over U) (toSlice T U) sliceRingSheaf
  let e' : R.obj (N.over U) ≅
      (Stacks.DenseSubsiteBaseChange.baseChangeSheaf (baseChangeIsSheaf W hW eW)).obj M :=
    R.mapIso e ≪≫ (Stacks.DenseSubsiteBaseChange.associatedSheafRestrictionIso
      (baseChangeIsSheaf W hW eW)).app M
  have h₁ : (toSlice T U).op ⋙ ((SheafOfModules.toSheaf (sliceRingSheaf (T := T) (V := U))).obj
      (N.over U)).obj = (sheafToPresheaf _ _).obj
        ((SheafOfModules.toSheaf _).obj (R.obj (N.over U))) :=
    rfl
  have h₂ : (toOver T U).op ⋙ ((SheafOfModules.toSheaf _).obj N).obj =
      (toSlice T U).op ⋙ ((SheafOfModules.toSheaf (sliceRingSheaf (T := T) (V := U))).obj
        (N.over U)).obj := rfl
  exact ⟨eqToIso (h₂.trans h₁) ≪≫
    (sheafToPresheaf _ _).mapIso ((SheafOfModules.toSheaf _).mapIso e')⟩

/-- The image in the slice at `U` of an affine scheme identified with `U` is terminal. -/
noncomputable def isTerminal_toSlice_ofIso (W : T.Schemes)
    (hW : IsAffine ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).obj W))
    (eW : (schemeSpaceFunctor T.schemeSite S T.scheme_mem).obj W ≅ U.left) :
    IsTerminal ((toSlice T U).obj (ofIso W hW eW)) :=
  Over.mkIdTerminal.ofIso
    (Over.isoMk (f := (toSlice T U).obj (ofIso W hW eW)) (g := Over.mk (𝟙 U))
      (Over.isoMk (f := Over.mk (eW.hom ≫ U.hom)) (g := U) eW rfl)
      (Over.OverMorphism.ext (Category.comp_id _))).symm

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for the module categories over the slice of the big fppf site is slow
/-- **A sheaf of modules on `(Spaces/X)_fppf` with a global presentation on the slice at `U` is a
base change presheaf `A ↦ 𝒪(A) ⊗ M` on the affine schemes over `U`.** -/
theorem exists_toOver_iso_baseChange_of_hasGlobalPresentation
    (N : SheafOfModules.{u + 1} (bigFppfRingSheaf T X)) (hN : (N.over U).HasGlobalPresentation)
    (W : T.Schemes) (hW : IsAffine ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).obj W))
    (eW : (schemeSpaceFunctor T.schemeSite S T.scheme_mem).obj W ≅ U.left) :
    ∃ M : ModuleCat.{u + 1} ((ringPresheaf (T := T) (V := U)).obj (op (ofIso W hW eW))),
      Nonempty ((toOver T U).op ⋙ ((SheafOfModules.toSheaf _).obj N).obj ≅
        ((Stacks.TerminalBaseChange.baseChangePresheaf.{u + 1} (ringPresheaf (T := T) (V := U))
          (isTerminalOfIso W hW eW)).obj M).presheaf) := by
  obtain ⟨p⟩ := SheafOfModules.HasGlobalPresentation.nonempty_presentation.{u + 1, u + 1, u + 1} hN
  obtain ⟨M, ⟨e⟩⟩ := Stacks.DenseSubsiteBaseChange.exists_iso_associatedSheaf_of_presentation
    (baseChangeIsSheaf W hW eW) (isTerminal_toSlice_ofIso W hW eW) p
  exact ⟨M, nonempty_toOver_iso_baseChange N W hW eW M e⟩

end AffineSchemesOver

attribute [local instance] hasExt_bigFppfSpaceOver in
/-- **Higher cohomology on `(Spaces/X)_fppf` of a sheaf of modules vanishes on every affine
object over which the sheaf has a global presentation.** -/
theorem isZero_H'_of_hasGlobalPresentation (N : SheafOfModules.{u + 1} (bigFppfRingSheaf T X))
    (U : Over X) (hU : BigFppfSpaceOver.IsAffineSchemeOver T X U)
    (hN : (N.over U).HasGlobalPresentation) (p : ℕ) (hp : 0 < p) :
    IsZero (Sheaf.H' ((SheafOfModules.toSheaf _).obj N) p U) :=
  isZero_H'_of_baseChange
    {U | BigFppfSpaceOver.IsAffineSchemeOver T X U ∧ (N.over U).HasGlobalPresentation}
    (fun _ hU => hU.1)
    (fun f hU hU' =>
      ⟨hU', SheafOfModules.HasGlobalPresentation.overMap.{u + 1, u + 1, u + 1} N f hU.2⟩)
    _ (fun _ hU W hW eW =>
      AffineSchemesOver.exists_toOver_iso_baseChange_of_hasGlobalPresentation N hU.2 W hW eW)
    U ⟨hU, hN⟩ p hp

end AlgebraicGeometry.BigFppfSpaceSite

end
