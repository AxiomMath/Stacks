module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleHigherDirectImageRestriction
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleQuasicoherentTransfer
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.QuasicoherentWeakSerre
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.SmallEtaleAssociatedModuleExact

/-!
# Extensions of quasi-coherent modules on the small étale site

Let `S` be a scheme, let `ε^* = AlgebraicGeometry.SmallEtale.associatedModule` be the functor
`𝓕 ↦ 𝓕^a` from `𝒪_S`-modules to `𝒪`-modules on the small étale site `S_étale`, and let
`ε_* = AlgebraicGeometry.SmallEtale.restrictModule` be its right adjoint, restriction to the small
Zariski site of `S`. Let `C` be a short exact sequence `0 → 𝓕₁ → 𝓔 → 𝓕₂ → 0` of `𝒪`-modules on
`S_étale` whose outer terms are quasi-coherent, and suppose that `ε_*` carries the epimorphism
`𝓔 → 𝓕₂` to an epimorphism. Then the restriction of `C` to the small Zariski site is short exact,
the restriction `𝓔|_{S_Zar}` is quasi-coherent, and the counit `ε^* ε_* 𝓔 → 𝓔` is an isomorphism.
Hence `𝓔` is in the essential image of `𝓕 ↦ 𝓕^a`: this is Stacks 06VE (10) at `τ = étale` under
the hypothesis on `ε_*`.

## Main results

* `AlgebraicGeometry.SmallEtale.shortExact_map_restrictModule`: the restriction of a short exact
  sequence to `S_Zar` is short exact.
* `AlgebraicGeometry.SmallEtale.isQuasicoherent_restrictModule_X₂`: the restriction of the middle
  term is quasi-coherent on `S`.
* `AlgebraicGeometry.SmallEtale.isIso_counit_X₂`: the counit is an isomorphism at the middle term.
* `AlgebraicGeometry.SmallEtale.essImage_X₂_of_shortExact_of_epi_restrictModule`: the middle term
  is in the essential image of `𝓕 ↦ 𝓕^a`.
* `AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_X₂_of_shortExact_of_epi_restrictModule`: the
  middle term is quasi-coherent on the site.
* `SmallEtale.isClosedUnderExtensions_isQuasicoherentOnSite_of_epi_restrictModule`: quasi-coherence
  on the small étale site is closed under extensions, provided `ε_*` carries the epimorphism of
  every short exact sequence with quasi-coherent outer terms to an epimorphism.

## References

* [Stacks Project, Tag 06VE](https://stacks.math.columbia.edu/tag/06VE)
* [Stacks Project, Tag 0GNB](https://stacks.math.columbia.edu/tag/0GNB)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 01LA](https://stacks.math.columbia.edu/tag/01LA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section

variable {B S hS}
variable {C : ShortComplex (SheafOfModules.{u} (structureSheaf B S hS))}

/-! ### Restriction of the sequence to the small Zariski site -/

/-- The restriction of a short exact sequence `C` of `𝒪`-modules on `S_étale` to the small
Zariski site of `S` is short exact, provided `ε_*` carries the epimorphism `C.g` to an
epimorphism. -/
public theorem shortExact_map_restrictModule (hC : C.ShortExact)
    (hepi : Epi ((restrictModule B S hS).map C.g)) :
    (C.map (restrictModule B S hS)).ShortExact := by
  have := hC.mono_f
  have : (restrictModule B S hS).PreservesMonomorphisms := inferInstance
  exact { exact := hC.exact.map_of_mono_of_preservesKernel _ inferInstance inferInstance
          mono_f := (inferInstance : Mono ((restrictModule B S hS).map C.f))
          epi_g := hepi }

/-! ### Quasi-coherence of the restricted middle term -/

/-- Let `C` be a short exact sequence of `𝒪`-modules on `S_étale` with quasi-coherent outer terms
such that `ε_*` carries `C.g` to an epimorphism. Then the restriction of the middle term `C.X₂` to
the small Zariski site of `S` is a quasi-coherent `𝒪_S`-module. -/
public theorem isQuasicoherent_restrictModule_X₂ (hC : C.ShortExact)
    (h₁ : C.X₁.IsQuasicoherentOnSite) (h₃ : C.X₃.IsQuasicoherentOnSite)
    (hepi : Epi ((restrictModule B S hS).map C.g)) :
    SheafOfModules.IsQuasicoherent (R := S.ringCatSheaf)
      ((restrictModule B S hS).obj C.X₂) :=
  Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_X₂_of_shortExact
    (shortExact_map_restrictModule hC hepi)
    (isQuasicoherent_restrictModule B S hS C.X₁ h₁)
    (isQuasicoherent_restrictModule B S hS C.X₃ h₃)

/-! ### The counit at the middle term -/

/-- Let `C` be a short exact sequence of `𝒪`-modules on `S_étale` with quasi-coherent outer terms
such that `ε_*` carries `C.g` to an epimorphism. Then the counit `ε^* ε_* C.X₂ ⟶ C.X₂` is an
isomorphism. -/
public theorem isIso_counit_X₂ (hC : C.ShortExact)
    (h₁ : C.X₁.IsQuasicoherentOnSite) (h₃ : C.X₃.IsQuasicoherentOnSite)
    (hepi : Epi ((restrictModule B S hS).map C.g)) :
    IsIso ((associatedModuleAdjunction B S hS).counit.app C.X₂) := by
  have := preservesFiniteLimits_associatedModule B S hS
  exact ShortComplex.isIso₂_of_shortExact_of_isIso₁₃'
    (C.mapNatTrans (associatedModuleAdjunction B S hS).counit)
    ((shortExact_map_restrictModule hC hepi).map_of_exact _) hC
    (isIso_counit' B S hS C.X₁ h₁) (isIso_counit' B S hS C.X₃ h₃)

/-! ### Extensions of quasi-coherent modules -/

/-- Let `0 → 𝓕₁ → 𝓔 → 𝓕₂ → 0` be a short exact sequence of `𝒪`-modules on the small étale site of
`S` with quasi-coherent outer terms, such that `ε_*` carries `𝓔 → 𝓕₂` to an epimorphism. Then `𝓔`
is in the essential image of `QCoh(𝒪_S) ⥤ Mod(S_étale, 𝒪)`, `𝓕 ↦ 𝓕^a`: it is the image of
`𝓔|_{S_Zar}`. -/
public theorem essImage_X₂_of_shortExact_of_epi_restrictModule (hC : C.ShortExact)
    (h₁ : C.X₁.IsQuasicoherentOnSite) (h₃ : C.X₃.IsQuasicoherentOnSite)
    (hepi : Epi ((restrictModule B S hS).map C.g)) :
    (associatedModuleQcoh B S hS).essImage C.X₂ :=
  have := isIso_counit_X₂ hC h₁ h₃ hepi
  ⟨⟨(restrictModule B S hS).obj C.X₂, isQuasicoherent_restrictModule_X₂ hC h₁ h₃ hepi⟩,
    ⟨asIso ((associatedModuleAdjunction B S hS).counit.app C.X₂)⟩⟩

/-- Let `C` be a short exact sequence of `𝒪`-modules on `S_étale` with quasi-coherent outer terms
such that `ε_*` carries `C.g` to an epimorphism. Then the middle term `C.X₂` is quasi-coherent on
the site. -/
public theorem isQuasicoherentOnSite_X₂_of_shortExact_of_epi_restrictModule (hC : C.ShortExact)
    (h₁ : C.X₁.IsQuasicoherentOnSite) (h₃ : C.X₃.IsQuasicoherentOnSite)
    (hepi : Epi ((restrictModule B S hS).map C.g)) :
    C.X₂.IsQuasicoherentOnSite :=
  have := isIso_counit_X₂ hC h₁ h₃ hepi
  SheafOfModules.IsQuasicoherentOnSite.of_iso
    (asIso ((associatedModuleAdjunction B S hS).counit.app C.X₂))
    (isQuasicoherentOnSite_associatedModule_of_isQuasicoherent B S hS _
      (isQuasicoherent_restrictModule_X₂ hC h₁ h₃ hepi))

end

/-- Quasi-coherence on the small étale site of `S` is closed under extensions, provided `ε_*`
carries the epimorphism of every short exact sequence with quasi-coherent outer terms to an
epimorphism. -/
public theorem isClosedUnderExtensions_isQuasicoherentOnSite_of_epi_restrictModule
    (hepi : ∀ {C : ShortComplex (SheafOfModules.{u} (structureSheaf B S hS))}, C.ShortExact →
      C.X₁.IsQuasicoherentOnSite → C.X₃.IsQuasicoherentOnSite →
      Epi ((restrictModule B S hS).map C.g)) :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (structureSheaf B S hS)).IsClosedUnderExtensions where
  prop_X₂_of_shortExact hC h₁ h₃ :=
    isQuasicoherentOnSite_X₂_of_shortExact_of_epi_restrictModule hC h₁ h₃ (hepi hC h₁ h₃)

end AlgebraicGeometry.SmallEtale

end
