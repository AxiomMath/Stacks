module

public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentBaseChange
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.LocallyFreeSite

/-!
# Recognising a finite locally free module of rank `r` from its sections on affine opens

Let `F` be a quasi-coherent `𝒪_X`-module and `U` an affine open of `X`. This file identifies
the restriction of `F` to `Spec Γ(X, U)` with the sheaf associated to the `Γ(X, U)`-module
`Γ(F, U)`, and deduces that `F` is finite locally free of rank `r` as soon as `Γ(F, U)` is a
finite locally free `Γ(X, U)`-module of rank `r` for the members `U` of some affine cover.

## Main definitions

* `Stacks.Modules.freeRestrictIso`: restriction along an open immersion carries a free sheaf of
  modules to the free sheaf on the same index type.
* `Stacks.Modules.restrictImageIso` compares the restriction of `F` to an open `W` of the source
  of an open immersion `g` with its restriction to the image `g ''ᵁ W`.
* `Stacks.Modules.restrictFromSpecSectionsEquiv`: the global sections of the restriction of `F`
  along `AlgebraicGeometry.IsAffineOpen.fromSpec` are `Γ(F, U)`, linearly over `Γ(X, U)`.
* `Stacks.Modules.tildeIsoRestrictFromSpec`: the restriction of a quasi-coherent `F` to
  `Spec Γ(X, U)` is the sheaf associated to `Γ(F, U)`.

## Main results

* `Stacks.Modules.isFiniteLocallyFreeOfRank_of_iso`: finite local freeness of rank `r` only
  depends on the isomorphism class.
* `Stacks.Modules.exists_restrict_iso_free_of_isOpenImmersion`: a trivialisation of `F` found
  after restricting along an open immersion is a trivialisation of `F` on an open of `X`.
* `Stacks.Modules.isFiniteLocallyFreeOfRank_restrict_fromSpec`: Stacks Tag 05JM for `F` on an
  affine open, in the form the affine-local criteria produce.
* `Stacks.Modules.isFiniteLocallyFreeOfRank_of_module_affineOpens`: the global criterion — if
  every point lies in an affine open `U` with `Γ(F, U)` finite locally free of rank `r`, then
  `F` is finite locally free of rank `r`.

## Implementation notes

Everything is phrased with `AlgebraicGeometry.IsAffineOpen.fromSpec`, the open immersion
`Spec Γ(X, U) ⟶ X` with image `U`, rather than with the inclusion `U.ι` of the open subscheme.
This is what makes `tildeIsoRestrictFromSpec` cheap: the source of `fromSpec` is *literally*
`Spec Γ(X, U)`, so `AlgebraicGeometry.Scheme.Modules.fromTildeΓ` applies to the restriction
with no transport along `AlgebraicGeometry.Scheme.isoSpec`, and the ring over which the module
of global sections is taken is literally `Γ(X, U)`. Had the inclusion `U.ι` been used instead,
the sections would have been a module over `Γ(U.toScheme, ⊤)`, which is `Γ(X, U)` only up to
`AlgebraicGeometry.Scheme.Opens.ι_image_top`, and transporting
`Module.IsFiniteLocallyFreeOfRank` across a ring isomorphism means moving localizations of both
the ring and the module. The `Γ(X, U)`-linear identification of the sections is
`Stacks.AlgebraicGeometry.QuasicoherentBaseChange.restrictSectionsEquiv` followed by
`Stacks.AlgebraicGeometry.QuasicoherentBaseChange.sectionsCongrSelf`.

Because `Stacks.Modules.exists_restrict_iso_free_of_isOpenImmersion` produces the defining
datum of `AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFreeOfRank` at a single point, no
separate locality statement is needed: the global criterion feeds it one point at a time.

`freeRestrictIso` supplies the `CategoryTheory.Limits.PreservesColimitsOfShape` hypothesis of
`CategoryTheory.SheafOfModules.mapFreeIso` by explicit application rather than by instance
search: the instance is about
`SheafOfModules` while the functor's codomain is `AlgebraicGeometry.Scheme.Modules`, and
typeclass resolution unfolds at reducible transparency only.

## References

* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
* [Stacks Project, Tag 01IA](https://stacks.math.columbia.edu/tag/01IA)
* [Stacks Project, Tag 05JM](https://stacks.math.columbia.edu/tag/05JM)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange
open AlgebraicGeometry.Scheme.Modules (restrictFunctor restrictFunctorComp restrictFunctorCongr
  restrictFunctorId)

universe u

namespace Stacks.Modules

variable {X : Scheme.{u}}

/-- **Restriction along an open immersion preserves free sheaves.** Restriction is a left
adjoint, so it preserves the coproduct of copies of the structure sheaf that defines a free
sheaf, and it carries the structure sheaf to the structure sheaf by
`AlgebraicGeometry.Scheme.Modules.restrictUnitIso`. -/
noncomputable def freeRestrictIso {Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (I : Type u) :
    SheafOfModules.free (R := Y.ringCatSheaf) I ≅
      (restrictFunctor f).obj (SheafOfModules.free I) :=
  letI F := restrictFunctor f
  letI h : Limits.PreservesColimitsOfShape.{u, u} (Discrete I) F :=
    Functor.instPreservesColimitsOfShapeOfIsLeftAdjoint.{u, u, u, u + 1, u, u + 1} F
  @SheafOfModules.mapFreeIso _ _ _ _ _ _ _ _ _ _ _ _ F I h
    (Scheme.Modules.restrictUnitIso f).symm

/-- Finite local freeness of rank `r` only depends on the isomorphism class of the module. -/
theorem isFiniteLocallyFreeOfRank_of_iso {F G : X.Modules} (e : F ≅ G) (r : ℕ)
    (h : F.IsFiniteLocallyFreeOfRank r) : G.IsFiniteLocallyFreeOfRank r := fun x ↦
  let ⟨U, hU, hi⟩ := h x
  ⟨U, hU, ⟨(restrictFunctor U.ι).mapIso e.symm ≪≫ hi.some⟩⟩

/-- **Restricting to an open of the source of an open immersion, versus to its image.** For
`g : Y ⟶ X` an open immersion and `W` an open of `Y`, the two restrictions of `F` differ by the
isomorphism `AlgebraicGeometry.Scheme.Hom.isoImage` between `W` and `g ''ᵁ W`. -/
noncomputable def restrictImageIso {Y : Scheme.{u}} (g : Y ⟶ X) [IsOpenImmersion g]
    (W : Y.Opens) (F : X.Modules) :
    (F.restrict g).restrict W.ι ≅ (F.restrict (g ''ᵁ W).ι).restrict (g.isoImage W).hom :=
  ((restrictFunctorComp W.ι g).symm ≪≫
    (restrictFunctorCongr (Scheme.Hom.isoImage_hom_ι g W)).symm ≪≫
    restrictFunctorComp (g.isoImage W).hom (g ''ᵁ W).ι).app F

/-- **A trivialisation found after restricting along an open immersion is a trivialisation on an
open of the ambient scheme.** If `F` pulled back along an open immersion `g` is finite locally
free of rank `r`, then every point of the image of `g` has an open neighbourhood in `X` on which
`F` is free of rank `r`, and that neighbourhood is contained in the image of `g`. -/
theorem exists_restrict_iso_free_of_isOpenImmersion {Y : Scheme.{u}} (g : Y ⟶ X)
    [IsOpenImmersion g] (F : X.Modules) (r : ℕ) (y : Y)
    (h : (F.restrict g).IsFiniteLocallyFreeOfRank r) :
    ∃ U : X.Opens, g.base y ∈ U ∧ U ≤ g.opensRange ∧
      Nonempty (F.restrict U.ι ≅ SheafOfModules.free.{u} (ULift (Fin r))) := by
  obtain ⟨W, hW, ⟨e⟩⟩ := h y
  let e₀ := g.isoImage W
  let iso₂ : restrictFunctor e₀.hom ⋙ restrictFunctor e₀.inv ≅ 𝟭 _ :=
    (restrictFunctorComp e₀.inv e₀.hom).symm ≪≫
      restrictFunctorCongr e₀.inv_hom_id ≪≫ restrictFunctorId
  refine ⟨g ''ᵁ W, ⟨y, hW, rfl⟩, ?_, ⟨?_⟩⟩
  · rintro _ ⟨w, -, rfl⟩
    exact ⟨w, rfl⟩
  exact (iso₂.app (F.restrict (g ''ᵁ W).ι)).symm ≪≫
    (restrictFunctor e₀.inv).mapIso ((restrictImageIso g W F).symm ≪≫ e) ≪≫
    (freeRestrictIso e₀.inv (ULift (Fin r))).symm

/-- The image of `AlgebraicGeometry.IsAffineOpen.fromSpec` is the affine open it comes from. -/
theorem image_top_fromSpec {U : X.Opens} (hU : IsAffineOpen U) :
    hU.fromSpec ''ᵁ (⊤ : (Spec Γ(X, U)).Opens) = U :=
  (Scheme.Hom.image_top_eq_opensRange _).trans hU.opensRange_fromSpec

/-- **The global sections of `F` restricted to `Spec Γ(X, U)` are `Γ(F, U)`**, as modules over
`Γ(X, U)`. -/
noncomputable def restrictFromSpecSectionsEquiv (F : X.Modules) {U : X.Opens}
    (hU : IsAffineOpen U) :
    Γ(F.restrict hU.fromSpec, (⊤ : (Spec Γ(X, U)).Opens)) ≃ₗ[Γ(X, U)] Γ(F, U) :=
  (restrictSectionsEquiv F hU ⊤).trans
    (sectionsCongrSelf F (image_top_fromSpec hU) (fromSpec_image_le hU ⊤))

/-- **Stacks Project, Tag 01IA, for an affine open of an arbitrary scheme.** The restriction of
a quasi-coherent `𝒪_X`-module `F` to `Spec Γ(X, U)`, along an affine open `U` of `X`, is the
sheaf associated to the `Γ(X, U)`-module `Γ(F, U)`.

This is `AlgebraicGeometry.Scheme.Modules.fromTildeΓ` of the restriction, which is invertible
because the restriction of a quasi-coherent module is quasi-coherent, composed with the
identification `Stacks.Modules.restrictFromSpecSectionsEquiv` of its global sections. -/
noncomputable def tildeIsoRestrictFromSpec (F : X.Modules) [F.IsQuasicoherent] {U : X.Opens}
    (hU : IsAffineOpen U) :
    tilde (R := Γ(X, U)) (ModuleCat.of Γ(X, U) Γ(F, U)) ≅ F.restrict hU.fromSpec :=
  haveI h : IsIso (F.restrict hU.fromSpec).fromTildeΓ :=
    (isQuasicoherent_iff_isIso_fromTildeΓ _).mp inferInstance
  (tilde.functor _).mapIso (restrictFromSpecSectionsEquiv F hU).symm.toModuleIso ≪≫
    @asIso _ _ _ _ (F.restrict hU.fromSpec).fromTildeΓ h

/-- **The sections of a quasi-coherent module on an affine open determine its local freeness.**
If `Γ(F, U)` is a finite locally free `Γ(X, U)`-module of rank `r`, the restriction of `F` to
`Spec Γ(X, U)` is a finite locally free `𝒪`-module of rank `r`.

This is the module-level bridge `tilde_isFiniteLocallyFreeOfRank_iff` of Stacks Tag 05JM,
transported along `Stacks.Modules.tildeIsoRestrictFromSpec`. -/
theorem isFiniteLocallyFreeOfRank_restrict_fromSpec (F : X.Modules) [F.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) (r : ℕ)
    (h : Module.IsFiniteLocallyFreeOfRank Γ(X, U) Γ(F, U) r) :
    (F.restrict hU.fromSpec).IsFiniteLocallyFreeOfRank r :=
  isFiniteLocallyFreeOfRank_of_iso (tildeIsoRestrictFromSpec F hU) r
    ((tilde_isFiniteLocallyFreeOfRank_iff Γ(X, U) Γ(F, U) r).mpr h)

/-- **Finite local freeness of rank `r` is affine-local on sections.** A quasi-coherent
`𝒪_X`-module each of whose points lies in an affine open `U` with `Γ(F, U)` a finite locally
free `Γ(X, U)`-module of rank `r` is a finite locally free `𝒪_X`-module of rank `r`.

The point lies in the image of `AlgebraicGeometry.IsAffineOpen.fromSpec` of such a `U`, where
`Stacks.Modules.isFiniteLocallyFreeOfRank_restrict_fromSpec` applies; the trivialisation is
transported back to an open of `X` by
`Stacks.Modules.exists_restrict_iso_free_of_isOpenImmersion`. -/
theorem isFiniteLocallyFreeOfRank_of_module_affineOpens (F : X.Modules) [F.IsQuasicoherent]
    (r : ℕ) (h : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
      Module.IsFiniteLocallyFreeOfRank Γ(X, U.1) Γ(F, U.1) r) :
    F.IsFiniteLocallyFreeOfRank r := by
  intro x
  obtain ⟨U, hxU, hmod⟩ := h x
  have hU : IsAffineOpen U.1 := U.2
  have hx : x ∈ Set.range hU.fromSpec.base := by
    rwa [← Scheme.Hom.coe_opensRange, hU.opensRange_fromSpec]
  obtain ⟨y, hy⟩ := hx
  obtain ⟨V, hxV, -, hfree⟩ := exists_restrict_iso_free_of_isOpenImmersion hU.fromSpec F r y
    (isFiniteLocallyFreeOfRank_restrict_fromSpec F hU r hmod)
  exact ⟨V, hy ▸ hxV, hfree⟩

end Stacks.Modules

end
