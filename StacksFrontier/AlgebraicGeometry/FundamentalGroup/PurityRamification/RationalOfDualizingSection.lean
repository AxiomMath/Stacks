module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.DualizingDivisor.RationalSingularity
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeIdealSheaf
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeRegular
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularSectionIntegral
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SectionDegree

/-!
# A rational singularity from a section of the dualizing module of a resolution

In the proof of [Stacks, Tag 0EA3] the relative dualizing module `ω_W` of the resolution
`W ⟶ Spec(𝒪_{X, x})` acquires, from the étaleness of `X ⟶ Spec(A)` away from
`\overline{\{x\}}`, a global section generating it over the punctured spectrum; the source writes
this as `ω_W = 𝒪_W(E)` with `E` effective and exceptional and concludes by [Stacks, Tag 0EA2]
(first sentence). This file makes that step: an invertible module `L` on the integral scheme `W`
with a nonzero global section `s` is `𝒪_W(Z(s))` for the effective Cartier divisor `Z(s)`
([Stacks, Tag 01X0]), and `Z(s)` lies over the closed point when `s` generates `L` at every point
over the punctured spectrum.

## Main results

* `AlgebraicGeometry.definesRationalSingularity_of_relativeDualizingModule_section`
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite IsLocalRing DerivedCategory Stacks.Duality
open Stacks.SheafOfModules (nonvanishingLocus)

universe u

namespace AlgebraicGeometry

/-- **A section of the dualizing module of a resolution generating it over the punctured
spectrum forces a rational singularity.** Let `A` be a Noetherian normal local Nagata domain of
dimension two with a dualizing module `ω_A`, and `f : X ⟶ Spec(A)` a resolution of
singularities. Suppose `ω_X = H^{-2}(f^×(ω_A[2]))` (as in
`AlgebraicGeometry.DualizingDivisor.definesRationalSingularity_of_relativeDualizingModule_iso`)
is isomorphic to an invertible module `L` with a nonzero global section `s` which generates `L`
at every point not over the closed point. Then `A` defines a rational singularity: the zero
scheme `E` of `s` is an effective Cartier divisor with `L ≅ 𝒪_X(E)` ([Stacks, Tag 01X0]), it lies
over the closed point, and [Stacks, Tag 0EA2] (first sentence) applies. -/
theorem definesRationalSingularity_of_relativeDualizingModule_section (A : Type u) [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] [IsNormalDomain A] (hdim : ringKrullDim A = 2)
    (hNagata : IsNagataRing A) (ωA : ModuleCat.{u} A)
    (hω : Stacks.Duality.IsDualizingRingModule A ωA)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) (hf : IsResolution f)
    (L : X.Modules) [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (e : haveI : IsProper f := hf.1.isProper
      haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
      haveI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
      Nonempty (relativeDualizingModule f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
        ((derivedTilde (CommRingCat.of A)).obj ((singleFunctor (ModuleCat.{u} A) (-2)).obj ωA)) ≅
          L))
    (s : L.sections) (hs : s.eval (op ⊤) ≠ 0)
    (hgen : ∀ x : X, f x ≠ closedPoint A → x ∈ nonvanishingLocus (X := X.toRingedSpace) L s) :
    DefinesRationalSingularity A := by
  have : IsIntegral X := hf.1.source_isIntegral
  have hreg := isRegularSection_of_eval_top_ne_zero L s hs
  have : Stacks.Divisors.IsEffectiveCartierDivisor (zeroScheme X L (s.eval (op ⊤))) :=
    (isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection X L s).mpr hreg
  refine DualizingDivisor.definesRationalSingularity_of_relativeDualizingModule_iso A hdim
    hNagata ωA hω f hf (zeroScheme X L (s.eval (op ⊤))) (fun x hx => ?_) ?_
  · by_contra hfx
    have h := hgen x hfx
    rw [nonvanishingLocus_eq_compl_supportSet_zeroScheme L s hs] at h
    exact h hx
  · obtain ⟨e⟩ := e
    exact ⟨e ≪≫ invertibleSheafIsoZeroSchemeOfIsRegularSection L s hreg⟩

end AlgebraicGeometry

end
