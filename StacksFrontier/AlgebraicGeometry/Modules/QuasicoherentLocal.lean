module

public import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Quasi-coherence of a sheaf of modules is local on the base

Let `X` be a scheme and `M` an `𝒪_X`-module. If `X` is covered by opens `U i` such that each
restriction `M|_{U i}` is quasi-coherent, then `M` itself is quasi-coherent. This is
`Stacks.Modules.isQuasicoherent_of_restrict`.

## Main definitions

* `Stacks.Modules.presentationOfIso` transports a `SheafOfModules.Presentation` along an
  isomorphism of sheaves of modules.
* `Stacks.Modules.presentationOver` turns a presentation of `M|_U`, a module on the open
  subscheme `U`, into a presentation of `M.over U`, the same module seen on the slice site
  `Over U`.
* `Stacks.Modules.presentationRestrictImage` moves a presentation of `(M|_U)|_W`, for `W` an
  open of `U`, to a presentation of `M|_{U.ι ''ᵁ W}`.

## Main results

* `Stacks.Modules.isQuasicoherent_of_presentation`: a module which has a *global* presentation
  on each member of an open cover is quasi-coherent.
* `Stacks.Modules.isQuasicoherent_of_restrict`: quasi-coherence is local on the base.

## Implementation notes

Mathlib's `SheafOfModules.IsQuasicoherent` is phrased on the slice sites: a
`SheafOfModules.QuasicoherentData` for `M` is a family of opens covering the terminal object
together with a presentation of `M.over (U i)`, a sheaf of modules for the sheaf of rings
`𝒪_X.over (U i)` on the category `Over (U i)`. Everything stated about schemes, on the other
hand, is phrased with `AlgebraicGeometry.Scheme.Modules.restrict` along the open immersion
`(U i).ι`. The two are compared by `AlgebraicGeometry.Scheme.Modules.overEquiv`, whose forward
direction is `AlgebraicGeometry.Scheme.Modules.overFunctorEquiv`; passing a presentation
*backwards* along that equivalence is what `presentationOver` does, and it is the only real
content below. The open-cover hypothesis is then fed to Mathlib's `QuasicoherentData`
directly, and the reduction from "each `M|_{U i}` is quasi-coherent" to "each member of some
refinement has a global presentation" is Mathlib's
`AlgebraicGeometry.Scheme.Modules.exists_isOpenCover_presentation` applied to each `M|_{U i}`,
with the resulting opens of `U i` pushed forward to opens of `X` along `(U i).ι`.

Two elaboration points govern the shape of this file. First, `Scheme.Modules` carries its own
`CategoryTheory.Category` instance, whose `Hom` field is `Scheme.Modules.Hom`, and that is only
*definitionally* — not reducibly — the `Hom` of `SheafOfModules.instCategory`. Any term whose
type mentions `X.Modules` and which is handed to a declaration stated for `SheafOfModules` is
retyped by unification, after which typeclass resolution (which unfolds at reducible
transparency only) can no longer see through the two `Hom` fields, and instances such as
`PreservesColimitsOfSize _` or `IsIso _.hom` fail to synthesize even when a `haveI` of exactly
that statement is in scope. The remedy used throughout is to state a helper whose binders are
literally `SheafOfModules.{u} R`, so that all instance resolution happens there, and then to
apply that helper at the `Scheme.Modules` types, where only term-level (default transparency)
defeq is needed: this is what `presentationOfIso` and the auxiliary
`presentationOverOfFunctorIso` are for. Second, the same mismatch is why
`SheafOfModules.isQuasicoherent_pushforward_of_isLeftAdjoint` cannot be used to transport
quasi-coherence along `overEquiv`: the `IsIso φ` side condition is not synthesizable at
reducible transparency, and Mathlib itself only gets through by enabling
`backward.isDefEq.respectTransparency false`. Transporting a *presentation* instead, as here,
avoids that side condition entirely.

## References

* [Stacks Project, Tag 01BD](https://stacks.math.columbia.edu/tag/01BD)
* [Stacks Project, Tag 01BE](https://stacks.math.columbia.edu/tag/01BE)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits SheafOfModules TopologicalSpace
open AlgebraicGeometry.Scheme.Modules (restrictFunctor restrictFunctorComp restrictFunctorCongr
  restrictFunctorId presentationRestrict)

universe w u v₁ u₁

namespace Stacks.Modules

/-- Transport a presentation of a sheaf of modules along an isomorphism.

This is `SheafOfModules.Presentation.ofIsIso` packaged to take an isomorphism rather than a
morphism with an `IsIso` instance; stating it for `SheafOfModules.{u} R` means the `IsIso`
instance is resolved here, where the sheaf-of-modules category instance is the syntactic one. -/
noncomputable def presentationOfIso {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} [HasSheafify J AddCommGrpCat]
    [J.WEqualsLocallyBijective AddCommGrpCat] {M N : SheafOfModules.{u} R} (e : M ≅ N)
    (P : M.Presentation) : N.Presentation :=
  Presentation.ofIsIso e.hom P

variable {X : Scheme.{u}}

/-- The equivalence between sheaves of modules on the slice site `Over U` and sheaves of
modules on the open subscheme `U`, with both sides written as `SheafOfModules` rather than
`Scheme.Modules`.

This is `AlgebraicGeometry.Scheme.Modules.overEquiv` with its type left inferred, so that
instance resolution for its inverse functor never has to compare the two category instances on
sheaves of modules over the open subscheme. -/
noncomputable def overEquivAux (U : X.Opens) :
    SheafOfModules.{u} (X.ringCatSheaf.over U) ≌
      SheafOfModules.{u} ((Opens.sheafRestrict U).obj X.ringCatSheaf) :=
  Opens.sheafOfModulesEquivOver U X.ringCatSheaf

/-- A presentation of a sheaf of modules on the open subscheme `U` transports, along
`Stacks.Modules.overEquivAux` and an identification `e` of its forward image, to a
presentation on the slice site `Over U`.

The inverse of the equivalence preserves colimits because it is a left adjoint, and
`TopologicalSpace.Opens.sheafOfModulesEquivOverInverseUnit` says it takes the structure sheaf
of `U` to the structure sheaf of the slice site, which are the two hypotheses of
`SheafOfModules.Presentation.map`. -/
noncomputable def presentationOverOfFunctorIso (U : X.Opens)
    {M : SheafOfModules.{u} (X.ringCatSheaf.over U)}
    {N : SheafOfModules.{u} ((Opens.sheafRestrict U).obj X.ringCatSheaf)}
    (e : (overEquivAux U).functor.obj M ≅ N) (P : N.Presentation) : M.Presentation :=
  presentationOfIso
    (((overEquivAux U).unitIso.app M ≪≫ (overEquivAux U).inverse.mapIso e).symm)
    (P.map (overEquivAux U).inverse
      (U.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf).symm)

/-- A presentation of the restriction `M|_U` of an `𝒪_X`-module to an open subscheme yields a
presentation of `M.over U`, the same module regarded as a sheaf of modules for `𝒪_X.over U` on
the slice site `Over U`.

The identification of the two is `AlgebraicGeometry.Scheme.Modules.overFunctorEquiv`. -/
noncomputable def presentationOver {U : X.Opens} {M : X.Modules}
    (P : (M.restrict U.ι).Presentation) : (M.over U).Presentation :=
  presentationOverOfFunctorIso U ((Scheme.Modules.overFunctorEquiv U).app M) P

/-- The quasi-coherent data assembled from an open cover of `X` together with a global
presentation of the restriction of `M` to each member of the cover. -/
noncomputable def quasicoherentDataOfPresentation (M : X.Modules) {I : Type w}
    (U : I → X.Opens) (hU : iSup U = ⊤) (P : ∀ i, (M.restrict (U i).ι).Presentation) :
    QuasicoherentData.{w, u, u, u} M where
  I := I
  X := U
  coversTop := (Opens.coversTop_iff (T := (X : TopCat.{u})) U).mpr hU
  presentation i := presentationOver (P i)

/-- A sheaf of modules on a scheme which has a global presentation on every member of some
open cover is quasi-coherent. -/
theorem isQuasicoherent_of_presentation (M : X.Modules) {I : Type w} (U : I → X.Opens)
    (hU : iSup U = ⊤) (P : ∀ i, (M.restrict (U i).ι).Presentation) : M.IsQuasicoherent :=
  (quasicoherentDataOfPresentation M U hU P).isQuasicoherent

/-- A presentation of `(M|_U)|_W`, for `W` an open of the open subscheme `U`, is a presentation
of `M|_{U.ι ''ᵁ W}`.

The two restrictions differ by the isomorphism `AlgebraicGeometry.Scheme.Hom.isoImage` between
`W` and its image in `X`, along which a presentation is moved by
`AlgebraicGeometry.Scheme.Modules.presentationRestrict`. -/
noncomputable def presentationRestrictImage {M : X.Modules} (U : X.Opens)
    (W : U.toScheme.Opens) (P : ((M.restrict U.ι).restrict W.ι).Presentation) :
    (M.restrict (U.ι ''ᵁ W).ι).Presentation :=
  letI e := U.ι.isoImage W
  letI iso₁ : restrictFunctor U.ι ⋙ restrictFunctor W.ι ≅
      restrictFunctor (U.ι ''ᵁ W).ι ⋙ restrictFunctor e.hom :=
    (restrictFunctorComp W.ι U.ι).symm ≪≫
      (restrictFunctorCongr (Scheme.Hom.isoImage_hom_ι U.ι W)).symm ≪≫
      restrictFunctorComp e.hom (U.ι ''ᵁ W).ι
  letI iso₂ : restrictFunctor e.hom ⋙ restrictFunctor e.inv ≅ 𝟭 _ :=
    (restrictFunctorComp e.inv e.hom).symm ≪≫
      restrictFunctorCongr e.inv_hom_id ≪≫ restrictFunctorId
  presentationOfIso (iso₂.app (M.restrict (U.ι ''ᵁ W).ι))
    (presentationRestrict e.inv (presentationOfIso (iso₁.app M) P))

/-- **Quasi-coherence is local on the base.** If a scheme `X` is covered by opens `U i` such
that the restriction of an `𝒪_X`-module `M` to each `U i` is quasi-coherent, then `M` is
quasi-coherent.

Each `M|_{U i}` is, by `AlgebraicGeometry.Scheme.Modules.exists_isOpenCover_presentation`,
globally presented on an open cover of `U i`; pushing those opens forward to `X` along
`(U i).ι` gives an open cover of `X` on each member of which `M` is globally presented, which
is `Stacks.Modules.isQuasicoherent_of_presentation`. -/
theorem isQuasicoherent_of_restrict (M : X.Modules) {I : Type w} (U : I → X.Opens)
    (hU : iSup U = ⊤) (h : ∀ i, (M.restrict (U i).ι).IsQuasicoherent) : M.IsQuasicoherent := by
  choose κ W P hcov _ using fun i ↦
    have := h i
    Scheme.Modules.exists_isOpenCover_presentation (M.restrict (U i).ι)
  refine isQuasicoherent_of_presentation M (I := Σ i, κ i)
    (fun j ↦ (U j.1).ι ''ᵁ W j.1 j.2) ?_ fun j ↦ presentationRestrictImage _ _ (P j.1 j.2)
  have key (i : I) : ⨆ k, (U i).ι ''ᵁ W i k = U i :=
    (Scheme.Hom.image_iSup (U i).ι (W i)).symm.trans <| by
      rw [show ⨆ k, W i k = ⊤ from hcov i]; exact (U i).ι_image_top
  rw [iSup_sigma, ← hU]
  exact iSup_congr key

end Stacks.Modules

end
