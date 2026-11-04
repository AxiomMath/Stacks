module

public import StacksFrontier.AlgebraicGeometry.AmpleBridge.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleFamilyRelativeAmple.Basic
public import StacksFrontier.AlgebraicGeometry.AmplePredicateBridge.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleTransport.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.CanonicalSectionNonvanishing
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.AmpleFamilyCartier.Basic

/-!
# Ample families from complements of effective Cartier divisors

Let `X` be a scheme, `D 0, …, D (m-1)` effective Cartier divisors on `X` with empty common
intersection and `L 0, …, L (m-1)` invertible `𝒪_X`-modules with `L i` ample on `X ∖ D i`.
[Stacks, Tag 0GTS] says that `X` has an ample family of invertible modules; this file proves it.

## Main results

* `Stacks.AmpleFamilyCartier.exists_affine_nonvanishing_of_isAmple_restrict`: the body of the
  source's proof at one point. If `L` is ample on the nonvanishing open `W` of a global section
  `s` of an invertible module `M`, every point of `W` lies in an affine nonvanishing locus of a
  global section of `(L^{⊗ n} ⊗ M^{⊗ (k+1)}) ⊗ M^{⊗ (k+1)}` for some `n`, `k`.
* `Stacks.AmpleFamilyCartier.isAmple_pullbackModule_of_isAmpleOnComplement` and
  `Stacks.AmpleFamilyCartier.nonvanishingOpen_canonicalSection`: the two inputs of that step
  at `W = X ∖ D`, `M = 𝒪_X(D)` and `s = 1_D`.
* `Stacks.AmpleFamilyCartier.exists_isAmpleFamily_of_isAmpleOnComplement_cover`:
  **[Stacks, Tag 0GTS].**

## Implementation notes

Ampleness of `L|_W` gives `n ≥ 1` and a section `t` of `L^{⊗ n}` over `W` whose nonvanishing
locus is affine and contains the point. Properties, Lemma 28.18.2 ([Stacks, Tag 01PW]), in the form
`Stacks.TensorSectionPower.exists_tensorSection_of_compactSpace`, which runs over a cover
trivializing `M` and needs only that `X` be quasi-compact and quasi-separated, writes
`t ⊗ s'|_W = ρ|_W` for a global section `ρ` of `L^{⊗ n} ⊗ M^{⊗ (k+1)}` and a global section
`s'` of `M^{⊗ (k+1)}` with nonvanishing open `W`. The product `ρ ⊗ s'` then has nonvanishing locus
`X_t`: this is the source's replacement of `N` by `N + 1`, which makes the extension vanish along
`D`. The family is indexed by the triples `(i, n, k)`, and the exponent in the ample family
is `1`.

`X` is quasi-compact and quasi-separated under the hypotheses of the tag by
`Stacks.AmpleFamilyCartier.compactSpace_of_isAmpleOnComplement_cover` and
`Stacks.AmpleFamilyCartier.quasiSeparatedSpace_of_isAmpleOnComplement_cover`.

## References

* [Stacks Project, Tag 0GTS](https://stacks.math.columbia.edu/tag/0GTS)
* [Stacks Project, Tag 0FXR](https://stacks.math.columbia.edu/tag/0FXR)
* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory TopologicalSpace Opposite
open Stacks.Ample Stacks.AmpleTheory
open Stacks.TensorSectionPower (powObj)
open Stacks.SectionExtension (resTop)
open Stacks.SectionTensorFormula (tensorSection)

universe u

namespace Stacks.AmpleFamilyCartier

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive
  Stacks.TensorSectionNonvanishing.isInvertibleModule_tensorObj

variable {X : Scheme.{u}}

/-- **The pointwise step of [Stacks, Tag 0GTS].** Let `X` be quasi-compact and quasi-separated,
`M` an invertible module with a global section `s` whose nonvanishing open is `W`, and `L` an
invertible module ample on `W`. Every point `x ∈ W` lies in an affine open which is the
nonvanishing locus of a global section of `(L^{⊗ n} ⊗ M^{⊗ (k+1)}) ⊗ M^{⊗ (k+1)}` for some
`n` and `k`. -/
theorem exists_affine_nonvanishing_of_isAmple_restrict [CompactSpace X] [QuasiSeparatedSpace X]
    (L : X.Modules) [IsInvertibleModule X L] (M : X.Modules) [IsInvertibleModule X M]
    (s : Γ(M, ⊤)) (W : X.Opens) (hW : Stacks.NonvanishingOpen.nonvanishingOpen X M s = W)
    (hamp : IsAmple W.toScheme (Stacks.AmpleLocallyClosed.pullbackModule W.ι L))
    (x : X) (hx : x ∈ W) :
    ∃ (n k : ℕ) (g : Γ((tensorPowModule X L (n : ℤ) ⊗ powObj M k) ⊗ powObj M k, ⊤))
      (U : X.Opens),
      (U : Set X) = nonvanishingLocus ((tensorPowModule X L (n : ℤ) ⊗ powObj M k) ⊗
          powObj M k) g ∧ x ∈ U ∧ IsAffineOpen U := by
  classical
  obtain ⟨n, t, hxt, hAff⟩ :=
    Stacks.AmpleFamilyRelativeAmple.exists_section_affine_nonvanishingOpenOn_of_isAmple_restrict
      L W hamp x hx
  have : (tensorPowModule X L (n : ℤ)).IsQuasicoherent :=
    Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule _
  obtain ⟨k, σ₂, ρ, hW2, heq⟩ := Stacks.TensorSectionPower.exists_tensorSection_of_compactSpace
    M s (tensorPowModule X L (n : ℤ)) W hW t
  have hσ₂y : ∀ (y : X) (hy : y ∈ W),
      ((powObj M k).presheaf.germ W y hy).hom (resTop W σ₂) ∉
        Stacks.ModuleStalk.maximalSmul (powObj M k) y := by
    intro y hy
    rw [resTop, TopCat.Presheaf.Γgerm_res_apply (C := Ab.{u})
      (i := homOfLE (le_top : W ≤ ⊤)) (powObj M k).presheaf y hy σ₂]
    exact (hW2 ▸ hy : y ∈ Stacks.NonvanishingOpen.nonvanishingOpen X _ σ₂)
  refine ⟨n, k, tensorSection _ _ ρ σ₂,
    Stacks.SectionPowerOpen.nonvanishingOpenOn (tensorPowModule X L (n : ℤ)) W t,
    ?_, hxt, hAff⟩
  rw [Stacks.TensorSectionProduct.nonvanishingLocus_tensorSection,
    Stacks.SectionPowerOpen.coe_nonvanishingOpenOn]
  refine Set.ext fun y => ?_
  constructor
  · rintro ⟨hyW, hyt⟩
    exact ⟨(Stacks.TensorSectionProduct.mem_nonvanishingLocus_iff_of_resTop_eq ρ t
      (resTop W σ₂) heq hyW).mpr ⟨hyt, hσ₂y y hyW⟩,
      (hW2 ▸ hyW : y ∈ Stacks.NonvanishingOpen.nonvanishingOpen X _ σ₂)⟩
  · rintro ⟨hyρ, hyσ⟩
    have hyW : y ∈ W := by rwa [hW2]
    exact ⟨hyW, ((Stacks.TensorSectionProduct.mem_nonvanishingLocus_iff_of_resTop_eq ρ t
      (resTop W σ₂) heq hyW).mp hyρ).1⟩

/-- Ampleness on the complement of `D`, in the spelling of
`Stacks.AmpleFamilyCartier.IsAmpleOnComplement`, read in the spelling of the ampleness theory. -/
theorem isAmple_pullbackModule_of_isAmpleOnComplement {D : X.IdealSheafData} {L : X.Modules}
    [IsInvertibleModule X L] (h : IsAmpleOnComplement D L) :
    IsAmple (Scheme.Opens.toScheme D.support.compl)
      (Stacks.AmpleLocallyClosed.pullbackModule (Scheme.Opens.ι D.support.compl) L) := by
  obtain ⟨hinv, hamp⟩ := h
  have i2 : AlgebraicGeometry.SheafOfModules.IsInvertible
      (Scheme.Opens.toScheme D.support.compl).toRingedSpace.presheaf
      (structureSheafRing (Scheme.Opens.toScheme D.support.compl).toRingedSpace).property
      ((Scheme.Modules.pullback (Scheme.Opens.ι D.support.compl)).obj L) :=
    Stacks.RingedSpace.algebraicGeometryIsInvertible_modulePullback
      (Scheme.Opens.ι D.support.compl).toLRSHom.toShHom L
  exact (Stacks.AmpleBridge.isAmple_iff_isAmple _ _).mpr
    (@AlgebraicGeometry.Scheme.Modules.isAmple_of_iso _ _ _ hinv i2
      ((Scheme.Modules.restrictFunctorIsoPullback (Scheme.Opens.ι D.support.compl)).app L) hamp)

/-- The nonvanishing open of the canonical section `1_D` of `𝒪_X(D)` is the complement of `D`. -/
theorem nonvanishingOpen_canonicalSection (D : X.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] :
    Stacks.NonvanishingOpen.nonvanishingOpen X (Stacks.Divisors.invertibleSheaf D : X.Modules)
      (Stacks.Divisors.canonicalSection D) = D.support.compl :=
  Opens.ext <| (Stacks.AmplePredicateBridge.coe_nonvanishingOpen_sectionsOfTop X
    (Stacks.Divisors.invertibleSheaf D : X.Modules) (Stacks.Divisors.canonicalSection D)).symm.trans
    (Stacks.Divisors.nonvanishingLocus_canonicalSections D)

/-- **[Stacks, Tag 0GTS].** Let `X` be a scheme, let `D 0, …, D (m-1)` be effective Cartier
divisors on `X` and `L 0, …, L (m-1)` invertible `𝒪_X`-modules such that the divisors have empty
common intersection (every point lies in the complement of some `D i`) and `L i` restricted to
`X ∖ D i` is ample. Then `X` has an ample family of invertible modules. -/
@[stacks 0GTS]
theorem exists_isAmpleFamily_of_isAmpleOnComplement_cover {m : ℕ}
    (D : Fin m → X.IdealSheafData) (L : Fin m → X.Modules)
    (hD : ∀ i, Stacks.Divisors.IsEffectiveCartierDivisor (D i))
    (hL : ∀ i, Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L i))
    (hcover : ∀ x : X, ∃ i, x ∈ (D i).support.compl)
    (hample : ∀ i, IsAmpleOnComplement (D i) (L i)) :
    ∃ (J : Type u) (N : J → X.Modules), X.IsAmpleFamily N := by
  have : CompactSpace X := compactSpace_of_isAmpleOnComplement_cover hcover hample
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_isAmpleOnComplement_cover hD hcover hample
  refine exists_isAmpleFamily_of_pointwise_affine_nonvanishing X fun x => ?_
  obtain ⟨i, hi⟩ := hcover x
  have := hD i
  have : IsInvertibleModule X (L i) :=
    (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _
      (L i)).mp (hL i)
  obtain ⟨n, k, g, U, hU, hxU, hUaff⟩ := exists_affine_nonvanishing_of_isAmple_restrict (L i)
    (Stacks.Divisors.invertibleSheaf (D i) : X.Modules) (Stacks.Divisors.canonicalSection (D i))
    (D i).support.compl (nonvanishingOpen_canonicalSection (D i))
    (isAmple_pullbackModule_of_isAmpleOnComplement (hample i)) x hi
  have hM : IsInvertibleModule X (Stacks.Divisors.invertibleSheaf (D i) : X.Modules) :=
    (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _ _).mp
      (Stacks.Divisors.stacksIsInvertible_invertibleSheaf (D i))
  have := @Stacks.TensorSectionPower.isInvertibleModule_powObj _ _ hM k
  refine ⟨(tensorPowModule X (L i) (n : ℤ) ⊗
      powObj (Stacks.Divisors.invertibleSheaf (D i) : X.Modules) k) ⊗
      powObj (Stacks.Divisors.invertibleSheaf (D i) : X.Modules) k,
    (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _
      _).mpr inferInstance,
    Stacks.SheafOfModules.sectionsOfTop _ g, U, ?_, hxU, hUaff⟩
  exact hU.trans (Stacks.AmpleFamilyRelativeAmple.nonvanishingSet_sectionsOfTop _ g).symm

end Stacks.AmpleFamilyCartier

end
