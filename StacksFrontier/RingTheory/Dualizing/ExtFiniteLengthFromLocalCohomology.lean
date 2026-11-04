module

public import StacksFrontier.AlgebraicGeometry.AmpleWire.UnitStalk
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleDepthFourVanishing
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityLocalCase.PuncturedComplement
public import StacksFrontier.RingTheory.Dualizing.DualExtAnnihilator
public import StacksFrontier.RingTheory.Dualizing.ExtShortExact
public import StacksFrontier.RingTheory.Dualizing.ExtVanishingRange
public import StacksFrontier.RingTheory.LocalCohomology.DepthVanishing.Supported
public import StacksFrontier.RingTheory.Support.Finite

import all StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleInvertible

/-!
# Finite length of the dual Ext from finiteness of local cohomology

Let `(A, 𝔪)` be a Noetherian local ring with a normalized dualizing complex `ω`, and let `M` be a
finite `A`-module. By part (5) of [Stacks, Tag 0DWZ] the modules `Ext_A^{-i}(M, ω)` and
`H^i_𝔪(M)` have the same annihilator, and by part (1) the first of them is a finite `A`-module.
So as soon as `H^i_𝔪(M)` is itself a finite `A`-module, both modules have closed support cut out
by that one annihilator, and the support of a local cohomology module with support in `V(𝔪)` is
contained in `V(𝔪) = {𝔪}`. A finite module supported at the closed point has finite length, which
is the first result below.

The remaining results supply the geometric input in the shape the Kollár vanishing argument
consumes it. For an invertible module `F` on the punctured spectrum of a Noetherian local ring of
depth at least three, the global sections `M = Γ(Spec A, ι_*F)` of its direct image satisfy the
finiteness hypothesis in degrees `i ≤ 2`: this is [Stacks, Tag 0BPY], already available for a
quasi-coherent module whose restriction to the punctured spectrum is finite locally free. And for
the structure sheaf itself those global sections are `A` (Hartogs, in depth at least two), so the
dual Ext in degree `-2` vanishes by the vanishing range below the depth.

## Main results

* `Dualizing.linearEquiv_moduleExtInto_of_linearEquiv` — linearly equivalent modules have
  linearly equivalent dual Ext modules in every degree.
* `Dualizing.isFiniteLength_moduleExtInto_of_finite_localCohomology` — `Ext_A^{-i}(M, ω)` has
  finite length as soon as `H^i_𝔪(M)` is a finite `A`-module.
* `Stacks.Algebraization.finite_localCohomology_globalSections_pushforward_of_isInvertible` —
  `H^i_𝔪(Γ(Spec A, ι_*F))` is a finite `A`-module for `i ≤ 2`, for `F` invertible on the
  punctured spectrum of a Noetherian local ring of depth at least three.
* `Stacks.Algebraization.nonempty_linearEquiv_globalSections_pushforward_unit` — in depth at
  least two the global sections of the direct image of the structure sheaf of the punctured
  spectrum are `A`.
* `Stacks.Algebraization.subsingleton_moduleExtInto_globalSections_pushforward_unit` — the
  resulting vanishing of the dual Ext of those global sections in degree `-2`.

## Implementation notes

The dual Ext modules of linearly equivalent modules are compared through
`Dualizing.objExtPrecomp` of the corresponding isomorphism of `ModuleCat` objects, which is an
isomorphism of modules by the functoriality lemmas `Dualizing.objExtPrecomp_comp` and
`Dualizing.objExtPrecomp_id`.

The direct image of an invertible module from the punctured spectrum is coherent by
`Stacks.Algebraization.isCoherent_isReflexive_pushforward_puncturedSpectrum`, which is `private`
in `StacksFrontier/AlgebraicGeometry/Algebraization/CoherentTripleInvertible.lean` and so is reached
through `import all` rather than restated here.

## References

* [Stacks Project, Tag 0DWZ](https://stacks.math.columbia.edu/tag/0DWZ)
* [Stacks Project, Tag 0BPY](https://stacks.math.columbia.edu/tag/0BPY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Dualizing

/-- **Linearly equivalent modules have linearly equivalent dual Ext modules.** The comparison is
precomposition with the corresponding isomorphism of `ModuleCat` objects, whose inverse is
precomposition with the inverse isomorphism. -/
def linearEquiv_moduleExtInto_of_linearEquiv {A : Type u} [CommRing A] {M N : Type v}
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] (e : M ≃ₗ[A] N)
    (K : DerivedCategory (ModuleCat.{v} A)) (i : ℤ) :
    moduleExtInto N K i ≃ₗ[A] moduleExtInto M K i :=
  LinearEquiv.ofLinear (objExtPrecomp e.toModuleIso.hom K i) (objExtPrecomp e.toModuleIso.inv K i)
    (by rw [← objExtPrecomp_comp, Iso.hom_inv_id, objExtPrecomp_id])
    (by rw [← objExtPrecomp_comp, Iso.inv_hom_id, objExtPrecomp_id])

/-- **The dual Ext module has finite length once the local cohomology is finite.** Let `(A, 𝔪)`
be a Noetherian local ring with a normalized dualizing complex `ω` and let `M` be a finite
`A`-module. If `H^i_𝔪(M)` is a finite `A`-module, then `Ext_A^{-i}(M, ω)` has finite length.

Both modules are finite — the dual Ext by part (1) of [Stacks, Tag 0DWZ] — and they have the same
annihilator by part (5) of that tag, so they have the same support. The support of a local
cohomology module with support in `V(𝔪)` is contained in `V(𝔪)`, which is the closed point, and a
finite module supported at the closed point has finite length. -/
theorem isFiniteLength_moduleExtInto_of_finite_localCohomology
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (ω : DerivedCategory (ModuleCat.{u} A)) (hω : IsNormalizedDualizingComplex.{u, u} ω)
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M] (i : ℤ)
    (hfin : Module.Finite A (Stacks.LocalCohomology.localCohomologyWithSupportIn.{u, 0} A
      (PrimeSpectrum.zeroLocus ((IsLocalRing.maximalIdeal A : Ideal A) : Set A))
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M)) i)) :
    IsFiniteLength A (moduleExtInto M ω (-i)) := by
  have hEfin : Module.Finite A (moduleExtInto M ω (-i)) := moduleExtInto_finite ω hω i
  rcases subsingleton_or_nontrivial (moduleExtInto M ω (-i)) with _ | hnt
  · exact IsFiniteLength.of_subsingleton
  · refine isFiniteLength_of_support ?_
    have hann : Module.annihilator A (moduleExtInto M ω (-i)) =
        Module.annihilator A (Stacks.LocalCohomology.localCohomologyWithSupportIn.{u, 0} A
          (PrimeSpectrum.zeroLocus ((IsLocalRing.maximalIdeal A : Ideal A) : Set A))
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M)) i) :=
      annihilator_moduleExtInto_eq_annihilator_localCohomology M ω hω i
    have hsupp : Module.support A (moduleExtInto M ω (-i)) ⊆ {closedPoint A} := by
      rw [Module.support_eq_zeroLocus, hann, ← Module.support_eq_zeroLocus,
        ← AlgebraicGeometry.zeroLocus_maximalIdeal_eq_singleton A]
      exact Stacks.LocalCohomology.support_localCohomologyWithSupportIn_subset.{u, 0} _ _ i
    rcases Set.subset_singleton_iff_eq.mp hsupp with hempty | heq
    · exact absurd (Module.support_eq_empty_iff.mp hempty) (not_subsingleton _)
    · exact heq

end Dualizing

namespace Stacks.Algebraization

/-- **[Stacks, Tag 0BPY] for the global sections of the direct image of an invertible module on
the punctured spectrum.** Let `A` be a Noetherian local ring of depth at least three and let `F`
be an invertible module on the punctured spectrum of `A`. Then `H^i_𝔪` of the global sections of
the direct image of `F` is a finite `A`-module for every `i ≤ 2`.

The direct image is coherent, so its global sections are finite, and its restriction back to the
punctured spectrum is `F` again, hence finite locally free; that is exactly the hypothesis of
`Stacks.Algebraization.finite_localCohomology_globalSections_of_isFiniteLocallyFree_restrict`. -/
theorem finite_localCohomology_globalSections_pushforward_of_isInvertible
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (F : (Stacks.Divisors.puncturedSpectrum A).toScheme.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible
      (Stacks.Divisors.puncturedSpectrum A).toScheme.presheaf
      (Stacks.Divisors.puncturedSpectrum A).toScheme.ringCatSheaf.2 F]
    (hdepth : 3 ≤ Module.depth A (IsLocalRing.maximalIdeal A) A) (i : ℕ) (hi : i ≤ 2) :
    Module.Finite A (Stacks.LocalCohomology.localCohomologyWithSupportIn.{u, 0} A
      (PrimeSpectrum.zeroLocus ((IsLocalRing.maximalIdeal A : Ideal A) : Set A))
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        ((moduleSpecΓFunctor (R := CommRingCat.of A)).obj
          ((Scheme.Modules.pushforward (Stacks.Divisors.puncturedSpectrum A).ι).obj F)))
        (i : ℤ)) := by
  set G := (Scheme.Modules.pushforward (Stacks.Divisors.puncturedSpectrum A).ι).obj F
  obtain ⟨hcG, -⟩ :=
    isCoherent_isReflexive_pushforward_puncturedSpectrum A F (le_trans (by decide) hdepth)
  have : _root_.SheafOfModules.IsCoherent G := hcG
  have : G.IsQuasicoherent := isQuasicoherent_of_isCoherent G
  have hMfin : Module.Finite A ((moduleSpecΓFunctor (R := CommRingCat.of A)).obj G) :=
    finite_globalSections_of_isCoherent G hcG
  have hFL : Scheme.Modules.IsFiniteLocallyFree
      (G.restrict (Stacks.Divisors.puncturedSpectrum A).ι) :=
    Scheme.Modules.IsFiniteLocallyFree.of_iso
      ((Scheme.Modules.restrictFunctorAdjCounitIso
        (Stacks.Divisors.puncturedSpectrum A).ι).app F).symm
      (isFiniteLocallyFree_of_isInvertible_scheme _ F)
  exact finite_localCohomology_globalSections_of_isFiniteLocallyFree_restrict A G hMfin hdepth
    hFL i hi

/-- **Hartogs for the structure sheaf of the punctured spectrum.** For a Noetherian local ring of
depth at least two, the global sections of the direct image of the structure sheaf of the
punctured spectrum are `A`.

The structure sheaf of `Spec A` is invertible, so in depth at least two it is the direct image of
its own restriction to the punctured spectrum; that restriction is the structure sheaf of the
punctured spectrum, and the global sections of the structure sheaf of `Spec A` are `A`. -/
theorem nonempty_linearEquiv_globalSections_pushforward_unit
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hdepth : 2 ≤ Module.depth A (IsLocalRing.maximalIdeal A) A) :
    Nonempty (((moduleSpecΓFunctor (R := CommRingCat.of A)).obj
      ((Scheme.Modules.pushforward (Stacks.Divisors.puncturedSpectrum A).ι).obj
        (Stacks.Ample.unitModule (Stacks.Divisors.puncturedSpectrum A).toScheme)) : Type u)
      ≃ₗ[A] A) := by
  let U := Stacks.Divisors.puncturedSpectrum A
  let O := SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf
  let adj := Scheme.Modules.pullbackPushforwardAdjunction U.ι
  have hOA : IsIso (adj.unit.app O) := isIso_unit_puncturedSpectrum_of_isInvertible A O hdepth
  let eU : (Scheme.Modules.pullback U.ι).obj O ≅ SheafOfModules.unit U.toScheme.ringCatSheaf :=
    ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app _).symm ≪≫
      Scheme.Modules.restrictUnitIso U.ι
  let eP : (Scheme.Modules.pushforward U.ι).obj (Stacks.Ample.unitModule U.toScheme) ≅ O :=
    (Scheme.Modules.pushforward U.ι).mapIso eU.symm ≪≫ (asIso (adj.unit.app O)).symm
  exact ⟨((moduleSpecΓFunctor (R := CommRingCat.of A)).mapIso eP).toLinearEquiv.trans
    (unitSpecSectionsEquiv A)⟩

/-- **The dual Ext of the global sections of the direct image of the structure sheaf of the
punctured spectrum vanishes in degree `-2`.** For a Noetherian local ring of depth at least three
with a normalized dualizing complex, those global sections are `A` by Hartogs, and the dual Ext of
`A` vanishes in every degree `-i` with `i` below the depth. -/
theorem subsingleton_moduleExtInto_globalSections_pushforward_unit
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (ω : DerivedCategory (ModuleCat.{u} A)) (hω : Dualizing.IsNormalizedDualizingComplex.{u, u} ω)
    (hdepth : 3 ≤ Module.depth A (IsLocalRing.maximalIdeal A) A) :
    Subsingleton (Dualizing.moduleExtInto
      (((moduleSpecΓFunctor (R := CommRingCat.of A)).obj
        ((Scheme.Modules.pushforward (Stacks.Divisors.puncturedSpectrum A).ι).obj
          (Stacks.Ample.unitModule (Stacks.Divisors.puncturedSpectrum A).toScheme))) : Type u)
      ω (-2)) := by
  obtain ⟨e⟩ := nonempty_linearEquiv_globalSections_pushforward_unit A (le_trans (by decide) hdepth)
  have hA : Subsingleton (Dualizing.moduleExtInto A ω (-(2 : ℕ) : ℤ)) :=
    Dualizing.subsingleton_moduleExtInto_of_lt_depth_bound ω hω 3 (by exact_mod_cast hdepth) 2
      (by norm_num)
  rw [show (-(2 : ℕ) : ℤ) = (-2 : ℤ) by norm_num] at hA
  exact (Dualizing.linearEquiv_moduleExtInto_of_linearEquiv e ω (-2)).symm.toEquiv.subsingleton

end Stacks.Algebraization

end
