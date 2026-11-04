module

public import StacksFrontier.AlgebraicGeometry.Duality.CohenMacaulayLocus
public import StacksFrontier.AlgebraicGeometry.Reflexive.ExtensionChain.Depth
public import StacksFrontier.AlgebraicGeometry.Scheme.Points.StalkSemilinearLocalization
public import StacksFrontier.RingTheory.Dualizing.ConcentratedDualizingModule
import all StacksFrontier.AlgebraicGeometry.Duality.CohenMacaulayLocus
import all StacksFrontier.RingTheory.Dualizing.LocallyShiftedSingle

/-!
# The dualizing module of a Cohen--Macaulay scheme is Cohen--Macaulay

Let `X` be a locally Noetherian scheme carrying a dualizing complex `ω_X^•` whose cohomology is
concentrated in a single degree `n`. Then `ω_X = H^n(ω_X^•)` is a Cohen--Macaulay
`𝒪_X`-module in the sense of [Stacks, Tag 0343]
(`AlgebraicGeometry.SheafIsCohenMacaulay`). Together with
`Stacks.Duality.exists_coherent_iso_single_of_connected` this completes the final assertion of
[Stacks, Tag 0AWT] for a connected Cohen--Macaulay `X`.

## Main results

* `Stacks.Duality.sheafIsCohenMacaulay_homology_of_concentrated` — the clause itself, for an
  arbitrary degree of concentration.
* `Stacks.Duality.exists_coherent_cohenMacaulay_iso_single_of_connected` —
  **[Stacks, Tag 0AWT], the final assertion in full**: on a connected Cohen--Macaulay scheme
  with a dualizing complex there is an integer `n` and a coherent Cohen--Macaulay module `ω_X`
  with `ω_X^• ≅ ω_X[-n]`.

## Implementation notes

Serre's condition at a point is read through the two transports that were already in the tree and
are now joined up:

* **the ring-theoretic input.** `Dualizing.isMaximalCohenMacaulay_homology_of_concentrated` is the
  final clause of [Stacks, Tag 0AWS] with the normalization hypothesis removed, which is what
  makes it applicable here: the degree `n` is the globally constant one of
  `Stacks.Duality.exists_coherent_iso_single_of_connected`, not `-\dim 𝒪_{X,x}`, and the
  normalizing shift between the two is determined rather than assumed. The implementation notes
  of `StacksFrontier/AlgebraicGeometry/Duality/CohenMacaulayLocus.lean` used to record this
  identification as the real content of the clause and as not done; it is done, in
  `StacksFrontier/RingTheory/Dualizing/ConcentratedDualizingModule.lean`;
* **the semilinear transport.**
  `Stacks.ModuleStalkSpecialization.min_supportDim_le_depth_stalk` turns maximal
  Cohen--Macaulayness of the localized sections over `Γ(X, U)_𝔭` into the inequality
  `AlgebraicGeometry.SheafHasPropertySk` asks for at a point of the affine open `U`.

Between the two sits the comparison of the localized sections of `H^n(ω_X^•)` with the degree-`n`
cohomology of the derived localization of an affine dualizing model, which is
`Stacks.Duality.exists_specModule_homology_iso` followed by
`Dualizing.localizedHomologyAtPrimeIsoGeneric`. Both are isomorphisms of `Γ(X, U)`-modules while
the conclusion is about `Γ(X, U)_𝔭`-modules, and the two localizations are modules over that ring
with the expected scalar tower, so `LinearEquiv.extendScalarsOfIsLocalization` upgrades the
linearity instead of a semilinearity argument being needed a second time.

`AlgebraicGeometry.SheafHasPropertySk` is stated with the module structure on a stalk of
[Stacks, Tag 01CB] rather than the one instance search finds on a `Scheme.Modules`; the two are
equal but not definitionally so, and
`Stacks.AlgebraicGeometry.ReflexiveModules.sheafHasPropertySk_of_forall` is the transport.

## References

* [Stacks Project, Tag 0AWT](https://stacks.math.columbia.edu/tag/0AWT)
* [Stacks Project, Tag 0AWS](https://stacks.math.columbia.edu/tag/0AWS)
* [Stacks Project, Tag 0343](https://stacks.math.columbia.edu/tag/0343)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.CoherentTFAE Stacks.AlgebraicGeometry.FiniteDirectImageCoherent

universe u w

namespace Stacks.Duality

/-- A linear equivalence of modules induces one of their localizations, linear over the localized
ring. `LocalizedModule.map` is already linear over `Localization T`; only bijectivity has to be
read off. -/
private def localizedModuleCongrLocalization {A : Type u} [CommRing A] (T : Submonoid A)
    {M N : Type u} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (e : M ≃ₗ[A] N) : LocalizedModule T M ≃ₗ[Localization T] LocalizedModule T N :=
  LinearEquiv.ofBijective (LocalizedModule.map T e.toLinearMap)
    ⟨LocalizedModule.map_injective T _ e.injective,
      LocalizedModule.map_surjective T _ e.surjective⟩

/-- The cohomology sheaves of a dualizing complex are quasi-coherent, being coherent. -/
private lemma isQuasicoherent_homology_of_isDualizingComplex {X : Scheme.{u}}
    [IsLocallyNoetherian X] [HasDerivedCategory.{w} X.Modules] {K : DerivedCategory X.Modules}
    (hK : IsDualizingComplex K) (i : ℤ) :
    ((DerivedCategory.homologyFunctor X.Modules i).obj K).IsQuasicoherent :=
  have := isCoherent_homology_of_isDualizingComplex hK i
  (isQuasicoherent_isFiniteType_of_isCoherent _).1

/-- **The localized sections of the concentrated cohomology sheaf are maximal Cohen--Macaulay.**
At a point `x` of an affine open `U`, the sections of `H^n(ω_X^•)` over `U` localize at the prime
of `x` to the degree-`n` cohomology of the derived localization of an affine dualizing model,
which is a dualizing complex over `Γ(X, U)_𝔭` concentrated in degree `n`; the ring-level clause of
[Stacks, Tag 0AWS] applies to it. -/
private lemma isMaximalCohenMacaulay_localizedSections {X : Scheme.{u}} [IsLocallyNoetherian X]
    [HasDerivedCategory.{w} X.Modules] {K : DerivedCategory X.Modules}
    (hK : IsDualizingComplex K) (n : ℤ)
    (hn : ∀ i : ℤ, i ≠ n → IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj K))
    {U : X.Opens} (hU : IsAffineOpen U) {x : X} (hx : x ∈ U) :
    Module.IsMaximalCohenMacaulay
      (Localization.AtPrime (hU.primeIdealOf ⟨x, hx⟩).asIdeal)
      (LocalizedModule (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
        Γ((DerivedCategory.homologyFunctor X.Modules n).obj K, U)) := by
  let : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let := HasDerivedCategory.standard (ModuleCat.{u} Γ(X, U))
  let : (hU.primeIdealOf ⟨x, hx⟩).asIdeal.IsPrime := (hU.primeIdealOf ⟨x, hx⟩).isPrime
  let : IsNoetherianRing (Localization.AtPrime (hU.primeIdealOf ⟨x, hx⟩).asIdeal) :=
    IsLocalization.isNoetherianRing (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl _ inferInstance
  let := HasDerivedCategory.standard
    (ModuleCat.{u} (Localization.AtPrime (hU.primeIdealOf ⟨x, hx⟩).asIdeal))
  obtain ⟨ω, hω, hiso⟩ := exists_specModule_homology_iso hU (hK U hU)
  have hωp : Dualizing.IsDualizingComplex
      ((StacksDraft.PseudoCoherence.derivedExtensionScalars
        (algebraMap Γ(X, U)
          (Localization.AtPrime (hU.primeIdealOf ⟨x, hx⟩).asIdeal))).obj ω) :=
    Dualizing.isDualizingComplex_localization
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl ω hω
  have htr : ∀ i : ℤ,
      Subsingleton (((DerivedCategory.homologyFunctor X.Modules i).obj K).presheaf.stalk x) ↔
        Subsingleton (LocalizedModule (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U)) i).obj ω)) := by
    intro i
    have := isQuasicoherent_homology_of_isDualizingComplex hK i
    exact (subsingleton_stalk_iff_subsingleton_localizedSpecModule _ hU hx).trans
      (subsingleton_localizedModule_congr _ (hiso i).some.toLinearEquiv)
  have hconc : ∀ i : ℤ, i ≠ n →
      IsZero ((DerivedCategory.homologyFunctor
        (ModuleCat.{u} (Localization.AtPrime (hU.primeIdealOf ⟨x, hx⟩).asIdeal)) i).obj
        ((StacksDraft.PseudoCoherence.derivedExtensionScalars
          (algebraMap Γ(X, U)
            (Localization.AtPrime (hU.primeIdealOf ⟨x, hx⟩).asIdeal))).obj ω)) := by
    intro i hi
    refine (isZero_localizedHomology_iff _ ω i).mpr ((htr i).mp ?_)
    exact ModuleCat.isZero_iff_subsingleton.mp
      (((AlgebraicGeometry.SheafOfModules.isZero_iff_forall_isZero_stalkFunctor_obj
        X.ringCatSheaf _).mp (hn i hi)) x)
  have hmcm := Dualizing.isMaximalCohenMacaulay_homology_of_concentrated _ hωp n hconc
  have hsec := localizedModuleCongrLocalization
    (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
    ((specModuleIsoSections ((DerivedCategory.homologyFunctor X.Modules n).obj K)
      ⟨U, hU⟩).symm ≪≫ (hiso n).some).toLinearEquiv
  have hloc := LinearEquiv.extendScalarsOfIsLocalization
    (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
    (Localization.AtPrime (hU.primeIdealOf ⟨x, hx⟩).asIdeal)
    (Dualizing.localizedHomologyAtPrimeIsoGeneric
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal ω n).toLinearEquiv
  have e := (hsec ≪≫ₗ hloc).symm
  exact Module.isMaximalCohenMacaulay_of_semilinearEquiv
    (RingEquiv.refl (Localization.AtPrime (hU.primeIdealOf ⟨x, hx⟩).asIdeal))
    e.toAddEquiv (fun a m => e.map_smul a m) hmcm

/-- **Stacks Project, Tag 0AWT, the Cohen--Macaulayness of the dualizing module.** If the
cohomology of a dualizing complex on a locally Noetherian scheme is concentrated in the single
degree `n`, then `H^n` of it is a Cohen--Macaulay `𝒪_X`-module in the sense of
[Stacks, Tag 0343]. -/
@[stacks 0AWT "the dualizing module is Cohen--Macaulay, at an arbitrary degree of concentration"]
public theorem sheafIsCohenMacaulay_homology_of_concentrated {X : Scheme.{u}}
    [IsLocallyNoetherian X] [HasDerivedCategory.{w} X.Modules]
    (K : DerivedCategory X.Modules) (hK : IsDualizingComplex K) (n : ℤ)
    (hn : ∀ i : ℤ, i ≠ n → IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj K)) :
    AlgebraicGeometry.SheafIsCohenMacaulay X
      ((DerivedCategory.homologyFunctor X.Modules n).obj K) := by
  intro k
  refine Stacks.AlgebraicGeometry.ReflexiveModules.sheafHasPropertySk_of_forall _ k fun x => ?_
  obtain ⟨-, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have := isQuasicoherent_homology_of_isDualizingComplex hK n
  exact Stacks.ModuleStalkSpecialization.min_supportDim_le_depth_stalk _ hU hxU
    (isMaximalCohenMacaulay_localizedSections hK n hn hU hxU) k

/-- An object isomorphic to a module placed in degree `n` has vanishing cohomology in every
other degree. -/
private lemma isZero_homology_of_iso_single {X : Scheme.{u}}
    [HasDerivedCategory.{w} X.Modules] (K : DerivedCategory X.Modules) (n : ℤ) (M : X.Modules)
    (e : K ≅ (DerivedCategory.singleFunctor X.Modules n).obj M) (i : ℤ) (hi : i ≠ n) :
    IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj K) := by
  refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctor X.Modules i).mapIso e)
  exact (HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) n M i hi).of_iso
    ((DerivedCategory.homologyFunctorFactors X.Modules i).app
      ((CochainComplex.singleFunctor X.Modules n).obj M))

/-- **Stacks Project, Tag 0AWT, the final assertion, in full.** If `X` is connected and
Cohen--Macaulay then there is an integer `n` and a coherent Cohen--Macaulay `𝒪_X`-module
`ω_X = H^n(ω_X^•)` with `ω_X^• = ω_X[-n]`.

This is `Stacks.Duality.exists_coherent_iso_single_of_connected` together with the
Cohen--Macaulayness clause of the source, which that statement omits. -/
@[stacks 0AWT "the final assertion, in full"]
public theorem exists_coherent_cohenMacaulay_iso_single_of_connected {X : Scheme.{u}}
    [IsLocallyNoetherian X] [ConnectedSpace X] [HasDerivedCategory.{w} X.Modules]
    (K : DerivedCategory X.Modules) (hK : IsDualizingComplex K)
    (hX : AlgebraicGeometry.IsCohenMacaulay X) :
    ∃ n : ℤ, _root_.SheafOfModules.IsCoherent
        ((DerivedCategory.homologyFunctor X.Modules n).obj K) ∧
      AlgebraicGeometry.SheafIsCohenMacaulay X
        ((DerivedCategory.homologyFunctor X.Modules n).obj K) ∧
      Nonempty (K ≅ (DerivedCategory.singleFunctor X.Modules n).obj
        ((DerivedCategory.homologyFunctor X.Modules n).obj K)) := by
  obtain ⟨n, hcoh, ⟨e⟩⟩ := exists_coherent_iso_single_of_connected K hK hX
  exact ⟨n, hcoh, sheafIsCohenMacaulay_homology_of_concentrated K hK n
    (isZero_homology_of_iso_single K n _ e), ⟨e⟩⟩

end Stacks.Duality

end
