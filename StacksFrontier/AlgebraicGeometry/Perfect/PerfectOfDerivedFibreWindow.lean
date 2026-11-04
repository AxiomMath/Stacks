module

public import StacksFrontier.AlgebraicGeometry.Perfect.SingleDegreeRankOpenUniversal
public import StacksFrontier.AlgebraicGeometry.Perfect.TensorFinitelyPresentedPerfectPushforward
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentFrom.AffineAvatar
public import StacksFrontier.AlgebraicGeometry.DerivedTildePerfect
public import StacksFrontier.Algebra.Homology.PseudoCoherentNakayama
public import StacksFrontier.Homology.Perfect.Local
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.LocallySmall
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.OpenCover
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectProperPushforwardBaseChange

/-!
# A pseudo-coherent complex with bounded derived fibres is perfect

Let `X` be a scheme and `E` a pseudo-coherent object of `D(𝒪_X)`. If at every point `x ∈ X` the
derived fibre `E ⊗ᴸ κ(x)` has no cohomology outside a fixed window `[a, b]`, then `E` is perfect.
On an affine open `Spec A ⊆ X` the object `E` is `M̃` for a pseudo-coherent `M ∈ D(A)`
(Stacks 08E8); the derived fibres of `M` are those of `E` (Stacks 0BDI's base change of the
derived-fibre Betti numbers), so `M` is perfect by the fibre criterion Stacks 068V, hence so is
`M̃` (Stacks 08EB), and perfectness is local (Stacks 08CM).

## Main results

* `StacksDraft.Perfect.isPerfect_of_finrank_derivedFibreHomology_eq_zero`: the ring-level
  statement, from the vanishing of the dimensions of the fibre cohomology outside `[a, b]`.
* `AlgebraicGeometry.Scheme.Modules.isPerfect_of_isPseudoCoherent_of_finrank_derivedFibre`:
  the statement on a scheme.

## References

* [Stacks Project, Tag 068V](https://stacks.math.columbia.edu/tag/068V)
* [Stacks Project, Tag 08EB](https://stacks.math.columbia.edu/tag/08EB)
* [Stacks Project, Tag 0BDI](https://stacks.math.columbia.edu/tag/0BDI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open Stacks.AlgebraicGeometry.RelativelyPerfectProperPushforward
  (derivedRestrictIsoStandardPullback)
open CochainComplex.DerivedExtensionScalars

universe u

namespace StacksDraft.Perfect

/-- The cohomology of the derived fibre of a pseudo-coherent object of `D(R)` at a prime is
finite dimensional: the derived fibre is pseudo-coherent over the residue field, represented by a
bounded above complex of finite dimensional vector spaces. -/
theorem finiteDimensional_derivedFibreHomology {R : Type u} [CommRing R] (p : Ideal R)
    [p.IsPrime] (K : @DerivedCategory (ModuleCat.{u} R) _ _ (HasDerivedCategory.standard _))
    (hK : @StacksDraft.PseudoCoherence.IsPseudoCoherent _ _ (_) K)
    (j : ℤ) :
    FiniteDimensional p.ResidueField (derivedFibreHomology.{u, u} p K j) := by
  let := HasDerivedCategory.standard (ModuleCat.{u} R)
  let := HasDerivedCategory.standard (ModuleCat.{u} p.ResidueField)
  obtain ⟨E, hE, ⟨e⟩⟩ :=
    StacksDraft.PseudoCoherence.isPseudoCoherent_totalDerivedExtensionScalars_obj
    (totalDerivedExtensionScalars.{u, u, u} (algebraMap R p.ResidueField)) hK
  have hX : FiniteDimensional p.ResidueField (E.X j) := (hE.finiteFree j).1
  have hcyc : FiniteDimensional p.ResidueField (E.cycles j) :=
    FiniteDimensional.of_injective (ModuleCat.Hom.hom (E.iCycles j))
      ((ModuleCat.mono_iff_injective _).1 inferInstance)
  let ι := ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} p.ResidueField) j).app E).symm ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat.{u} p.ResidueField) j).mapIso e
  exact Module.Finite.of_surjective (ι.toLinearEquiv.toLinearMap ∘ₗ (E.homologyπ j).hom)
    (ι.toLinearEquiv.surjective.comp ((ModuleCat.epi_iff_surjective _).1 inferInstance))

/-- **A pseudo-coherent object of `D(R)` with derived fibres in a window is perfect** (the
backward direction of Stacks 068V, with the vanishing read on the dimensions of the fibre
cohomology). -/
theorem isPerfect_of_finrank_derivedFibreHomology_eq_zero {R : Type u} [CommRing R]
    (K : @DerivedCategory (ModuleCat.{u} R) _ _ (HasDerivedCategory.standard _))
    (hK : @StacksDraft.PseudoCoherence.IsPseudoCoherent _ _ (_) K)
    (a b : ℤ)
    (h : ∀ (p : PrimeSpectrum R) (j : ℤ), j < a ∨ b < j →
      Module.finrank p.asIdeal.ResidueField (derivedFibreHomology.{u, u} p.asIdeal K j) = 0) :
    @IsPerfect R _ (HasDerivedCategory.standard _) K := by
  let := HasDerivedCategory.standard (ModuleCat.{u} R)
  refine ((isPerfect_and_torAmplitude_iff_fibreCohomologyVanishes.{u, u} K hK a b).1.2
    fun q i hi => ?_).1
  refine (fibreCohomologyVanishes_iff_isZero_homology.{u, u} q.asIdeal K hK i).2 ?_
  have := finiteDimensional_derivedFibreHomology q.asIdeal K hK i
  have := Module.finrank_zero_iff.1 (h q i hi)
  exact ModuleCat.isZero_of_subsingleton _

end StacksDraft.Perfect

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- The derived pullback at the standard model of the derived categories, the model at which the
derived-fibre Betti numbers of this development are stated. -/
local notation "𝕃 " f:max => @derivedPullback _ _ f (HasDerivedCategory.standard _)
  (HasDerivedCategory.standard _) _

/-- Cohomology sheaves at the standard model. -/
local notation "ℍ " C:max n:max => @DerivedCategory.homologyFunctor C _ _
  (HasDerivedCategory.standard C) n

/-- **Perfectness is local, tested on the spectra of affine opens.** An object of `D(𝒪_X)` whose
derived pullback along `Spec Γ(X, W) ⟶ X` is perfect for every affine open `W` is perfect (all
at the standard model of the derived categories, the model of
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback`). -/
theorem isPerfect_of_forall_isAffineOpen_fromSpec
    (K : @DerivedCategory X.Modules _ _ (HasDerivedCategory.standard _))
    (h : ∀ (W : X.Opens) (hW : IsAffineOpen W),
      @RingedSpace.IsPerfect (Spec Γ(X, W)).toRingedSpace (HasDerivedCategory.standard _)
        ((𝕃 hW.fromSpec.toLRSHom.toShHom).obj K)) :
    @RingedSpace.IsPerfect X.toRingedSpace (HasDerivedCategory.standard _) K := by
  refine (PerfectApproximation.isPerfect_standard_iff K).2
    (Stacks.Duality.OpenImmersion.isPerfect_of_forall_exists_isPerfect_derivedRestrict _
      fun y => ?_)
  obtain ⟨W, hW, hyW, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
    (show y ∈ (⊤ : X.Opens) from trivial)
  have hW' : IsAffineOpen W := hW
  have : IsOpenImmersion hW'.fromSpec := hW'.isOpenImmersion_fromSpec
  exact ⟨Spec Γ(X, W), hW'.fromSpec, inferInstance, hW.primeIdealOf ⟨y, hyW⟩,
    hW'.fromSpec_primeIdealOf ⟨y, hyW⟩,
    @Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso (Spec Γ(X, W)).toRingedSpace
      (Scheme.Modules.hasDerivedCategory _) _ _
      (derivedRestrictIsoStandardPullback hW'.fromSpec K).symm
      ((PerfectApproximation.isPerfect_standard_iff _).1 (h W hW'))⟩

/-- **A pseudo-coherent object of `D(𝒪_X)` whose derived fibres lie in a window is perfect.**
If `E` is pseudo-coherent and at every point `x` the derived fibre `E ⊗ᴸ κ(x)` has no cohomology
in degrees outside `[a, b]`, then `E` is perfect. Everything is read at the standard model of the
derived categories. -/
theorem isPerfect_of_isPseudoCoherent_of_finrank_derivedFibre
    (E : @DerivedCategory X.Modules _ _ (HasDerivedCategory.standard _))
    (hE : @RingedSpace.IsPseudoCoherent X.toRingedSpace (HasDerivedCategory.standard _) E)
    (a b : ℤ)
    (h : ∀ (x : X) (j : ℤ), j < a ∨ b < j → Module.finrank (X.residueField x)
        ((moduleSpecΓFunctor (R := X.residueField x)).obj
          ((ℍ (Spec (X.residueField x)).Modules j).obj
            ((𝕃 (X.fromSpecResidueField x).toLRSHom.toShHom).obj E))) = 0) :
    @RingedSpace.IsPerfect X.toRingedSpace (HasDerivedCategory.standard _) E := by
  refine isPerfect_of_forall_isAffineOpen_fromSpec E fun W hW => ?_
  let A : CommRingCat.{u} := Γ(X, W)
  let φ : Spec A ⟶ X := hW.fromSpec
  let G := (𝕃 φ.toLRSHom.toShHom).obj E
  have hG :
      @RingedSpace.IsPseudoCoherent (Spec A).toRingedSpace (HasDerivedCategory.standard _) G :=
    Scheme.Hom.isPseudoCoherent_derivedPullback φ E hE
  obtain ⟨M, hM, ⟨eM⟩⟩ := RingedSpace.exists_isPseudoCoherent_iso_mapDerivedCategory_tilde A G hG
  have hfib (p : PrimeSpectrum A) (j : ℤ) (hj : j < a ∨ b < j) : Module.finrank
      p.asIdeal.ResidueField (StacksDraft.Perfect.derivedFibreHomology.{u, u} p.asIdeal M j) =
        0 := by
    rw [finrank_derivedFibreHomology_eq M p j, ← h (φ.base p) j hj]
    refine Eq.trans ?_ (DerivedFibreBetti.finrank_residueFibre_eq φ E p j)
    exact ((moduleSpecΓFunctor (R := (Spec A).residueField p)).mapIso
      ((ℍ (Spec ((Spec A).residueField p)).Modules j).mapIso
        ((𝕃 ((Spec A).fromSpecResidueField p).toLRSHom.toShHom).mapIso
          eM))).toLinearEquiv.finrank_eq
  exact @Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso (Spec A).toRingedSpace
    (HasDerivedCategory.standard _) _ _ eM ((isPerfect_tilde_iff M).2
      (StacksDraft.Perfect.isPerfect_of_finrank_derivedFibreHomology_eq_zero M hM a b hfib))

end AlgebraicGeometry.Scheme.Modules
