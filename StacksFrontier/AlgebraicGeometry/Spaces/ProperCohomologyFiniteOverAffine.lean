module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProperCohomologyFiniteWitness
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants

/-!
# Finiteness of the cohomology of a coherent module on a proper algebraic space

Let `T` be an affine object of the big fppf site whose scheme is locally Noetherian, so that
`A = Γ(T, 𝒪_T)` is a Noetherian ring, and let `f : X ⟶ h_T` be a proper morphism of algebraic
spaces over `S`.  For every coherent `𝒪_X`-module `F` every cohomology module `H^n(X, F)` is a
finite module over `Γ(h_T, 𝒪) ≅ A`, read along the ring map of [Stacks, Tag 0732].

This is the content of [Stacks, Tag 08AS] (`H^i(X, F)` is a finite `A`-module for `X` proper
over `Spec A`, `A` Noetherian), proved as the source proves it through [Stacks, Tag 08AR]: the
property is closed under extensions, kernels and cokernels of coherent modules over the
Noetherian ring `Γ(h_T, 𝒪)` and under direct-sum descent, so the dévissage of [Stacks, Tag 08AN]
(`AlgebraicGeometry.Space.hasFiniteGlobalCohomologyOver_of_witness`) reduces it to one coherent
module with given integral scheme-theoretic support, which Chow's lemma provides
(`AlgebraicGeometry.Space.hasCoherentWitnessOnIntegralSubspaces_hasFiniteGlobalCohomologyOver`).

No tag attribute is attached: the statement is phrased over an affine object of the site of an
arbitrary base `S`, which is the generality its consumers need, and is used below for
[Stacks, Tag 08AU].

## Main results

* `AlgebraicGeometry.Space.isNoetherianRing_globalSections_schemeSpace`: `Γ(h_T, 𝒪)` is
  Noetherian.
* `AlgebraicGeometry.Space.isNoetherian_of_isProper_schemeSpace`: `X` is Noetherian.
* `AlgebraicGeometry.Space.hasFiniteGlobalCohomologyOver_of_isProper`: the finiteness.

## References

* [Stacks Project, Tag 08AS](https://stacks.math.columbia.edu/tag/08AS)
* [Stacks Project, Tag 08AR](https://stacks.math.columbia.edu/tag/08AR)
* [Stacks Project, Tag 08AN](https://stacks.math.columbia.edu/tag/08AN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.SheafOfModules.Tensor (ringSheaf)

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The global functions on the algebraic space of an affine locally Noetherian object of the
site form a Noetherian ring**: they are the functions on the scheme
(`AlgebraicGeometry.Space.globalSectionsChartRingEquiv` at the terminal identity chart). -/
theorem isNoetherianRing_globalSections_schemeSpace (T : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    [_root_.AlgebraicGeometry.IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj T)] :
    IsNoetherianRing (RingCat.sectionsSubring
      (ringSheaf (smallEtaleRingedSite B S hS (schemeSpace T).1 (schemeSpace T).2).O).obj) := by
  have : IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) :=
    _root_.AlgebraicGeometry.IsLocallyNoetherian.component_noetherian
      ⟨⊤, isAffineOpen_top _⟩
  exact @isNoetherianRing_of_ringEquiv _ _ _ _
    (globalSectionsChartRingEquiv B S hS (schemeSpace T) (isTerminalIdEtaleChart B S hS T)).symm
    this

/-- **An algebraic space proper over the space of an affine locally Noetherian object of the site
is Noetherian.** -/
theorem isNoetherian_of_isProper_schemeSpace (hZtop : B.Contains (⊤_ Scheme.{u}))
    {X : AlgebraicSpaces B S hS} {T : BigFppfOver B S hS}
    (hTa : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (hTn : _root_.AlgebraicGeometry.IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj T))
    (f : X ⟶ schemeSpace T) (hf : IsProper B S hS f.hom) :
    IsNoetherian B S hS hZtop X.1 :=
  ⟨isQuasiCompactSpace_of_isQuasiCompact_of_isAffineSpace B S hS f.hom
      (isAffineSpace_yoneda B S hS T hTa) hf.2.1.2,
    isAbsolutelyQuasiSeparated_of_isAbsolutelySeparated B S hS hZtop X.1
      (isAbsolutelySeparated_of_isSeparated_to_affine B S hS hZtop T hTa f.hom hf.1),
    isLocallyNoetherian_of_isLocallyOfFiniteType B S hS X.2 (schemeSpace T).2 f.hom hf.2.1.1
      (hasEtaleLocalProperty_of_representable B S hS _ _ T (Iso.refl _) hTn)⟩

/-- **The cohomology of a coherent module on an algebraic space proper over an affine Noetherian
base is finite** ([Stacks, Tag 08AS]).  For a proper `f : X ⟶ h_T`, `T` an affine locally
Noetherian object of the site, and a coherent `𝒪_X`-module `F`, every `H^n(X, F)` is a finite
`Γ(h_T, 𝒪)`-module along the ring map of [Stacks, Tag 0732]. -/
theorem hasFiniteGlobalCohomologyOver_of_isProper (hZtop : B.Contains (⊤_ Scheme.{u}))
    {X : AlgebraicSpaces B S hS} {T : BigFppfOver B S hS}
    [hTa : IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    [hTn : _root_.AlgebraicGeometry.IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj T)]
    (f : X ⟶ schemeSpace T) (hf : IsProper B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : IsCoherent B S hS X.1 X.2 F) :
    HasFiniteGlobalCohomologyOver B S hS f F :=
  have := isNoetherianRing_globalSections_schemeSpace B S hS T
  hasFiniteGlobalCohomologyOver_of_witness B S hS f hZtop
    (isNoetherian_of_isProper_schemeSpace B S hS hZtop hTa hTn f hf)
    (hasCoherentWitnessOnIntegralSubspaces_hasFiniteGlobalCohomologyOver B S hS hZtop f hf) F hF

end AlgebraicGeometry.Space

end
