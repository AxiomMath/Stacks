module

public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.CohenMacaulayCurveDuality
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinSchemes.StalkwiseInvertible
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinSchemes.CohenMacaulay
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FreeNeighbourhoodRank
public import StacksFrontier.AlgebraicGeometry.ModuleDescent.InvertibleInput
import StacksCore.Tactic.StacksAttribute
import all StacksFrontier.AlgebraicGeometry.Duality.GorensteinSchemes.StalkwiseInvertible
import all StacksFrontier.RingTheory.Dualizing.LocalCriterionInvertible

/-!
# The dualizing sheaf of a proper Gorenstein curve is invertible

Let `X` be a proper scheme over a field `k` which is Gorenstein and equidimensional of dimension
one, and let `ω_X = H^{-1}(ω_X^•)` be the dualizing sheaf of [Stacks, Tag 0BS2], with
`ω_X^• = f^×(𝒪_{Spec k})`. Then `ω_X` is an invertible `𝒪_X`-module, which is clause (1) of
[Stacks, Tag 0BS6].

## Main results

* `Stacks.Duality.nonempty_stalk_dualizingSheafOverField_iso_of_isGorenstein`: every stalk
  `ω_{X,x}` is isomorphic to `𝒪_{X,x}`.
* `Stacks.Duality.isFiniteLocallyFreeOfRank_one_dualizingSheafOverField_of_isGorenstein`:
  `ω_X` is finite locally free of rank one.
* `Stacks.Duality.isInvertible_dualizingSheafOverField_of_isGorenstein`: `ω_X` is invertible
  (and finite locally free of rank one).

## References

* [Stacks Project, Tag 0BS6](https://stacks.math.columbia.edu/tag/0BS6)
* [Stacks Project, Tag 0BFQ](https://stacks.math.columbia.edu/tag/0BFQ)
* [Stacks Project, Tag 0C00](https://stacks.math.columbia.edu/tag/0C00)
* [Stacks Project, Tag 0B8J](https://stacks.math.columbia.edu/tag/0B8J)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u w

namespace Stacks.Duality

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]

/-- **At a Gorenstein point the stalks of the cohomology sheaves of a dualizing complex are
concentrated in one degree, where they are the local ring.** Let `X` be a locally Noetherian
scheme with a dualizing complex `K` and `x` a point with `𝒪_{X,x}` Gorenstein. Then there is an
`n` with `(H^i(K))_x = 0` for `i ≠ n` and `(H^n(K))_x ≅ 𝒪_{X,x}`. -/
theorem exists_stalk_homology_concentrated_free_of_isGorensteinLocalRing
    [IsLocallyNoetherian X] [HasDerivedCategory.{w} X.Modules] {K : DerivedCategory X.Modules}
    (hK : IsDualizingComplex K) (x : X)
    (hx : Dualizing.IsGorensteinLocalRing (X.presheaf.stalk x)) :
    ∃ n : ℤ,
      (∀ i : ℤ, i ≠ n → IsZero ((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).obj
        ((DerivedCategory.homologyFunctor X.Modules i).obj K))) ∧
      Nonempty ((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).obj
          ((DerivedCategory.homologyFunctor X.Modules n).obj K) ≅
        ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x)) := by
  let := HasDerivedCategory.standard (ModuleCat.{u} (X.presheaf.stalk x))
  let := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory
    (X.presheaf.stalk x)).choose
  obtain ⟨-, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let := HasDerivedCategory.standard (ModuleCat.{u} Γ(X, U))
  let : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    X.presheaf.algebra_section_stalk (⟨x, hxU⟩ : U)
  let : (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.IsPrime := (hU.primeIdealOf ⟨x, hxU⟩).isPrime
  let : IsLocalization.AtPrime (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hxU⟩).asIdeal :=
    hU.isLocalization_stalk ⟨x, hxU⟩
  obtain ⟨ω, hω, htr⟩ := exists_model_stalk_module_translation hK hU
  have hωB : Dualizing.IsDualizingComplex
      ((StacksDraft.PseudoCoherence.derivedExtensionScalars
        (algebraMap Γ(X, U) (X.presheaf.stalk x))).obj ω) :=
    Dualizing.isDualizingComplex_localization
      (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl ω hω
  have hdeg : ∀ i : ℤ,
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (X.presheaf.stalk x)) i).obj
          ((StacksDraft.PseudoCoherence.derivedExtensionScalars
            (algebraMap Γ(X, U) (X.presheaf.stalk x))).obj ω) ≅
        (Stacks.ModuleSkyscraper.modulesStalkFunctor X x).obj
          ((DerivedCategory.homologyFunctor X.Modules i).obj K) := fun i =>
    isoOfRestrictScalarsIso (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
      ((localizedHomologyIsoOfIsLocalization _ ω i).symm ≪≫ (htr i x hxU).some.toModuleIso)
  have hinv := (Dualizing.local_criterion_native (X.presheaf.stalk x) _ hωB).mp hx
  obtain ⟨n, hz, ⟨e⟩⟩ := (Dualizing.isInvertible_iff_homology_concentrated_free _).mp hinv
  exact ⟨n, fun i hi => (hz i hi).of_iso (hdeg i).symm, ⟨(hdeg n).symm ≪≫ e⟩⟩

/-- **The stalks of the dualizing sheaf of a proper Gorenstein curve are free of rank one.** Let
`X` be a proper scheme over a field `k` which is Gorenstein and equidimensional of dimension one.
Then at every point `x` the stalk of `ω_X = H^{-1}(f^×(𝒪_{Spec k}))` is isomorphic to `𝒪_{X,x}`. -/
theorem nonempty_stalk_dualizingSheafOverField_iso_of_isGorenstein
    (hG : AlgebraicGeometry.IsGorenstein X) (hequi : TopologicalSpace.Equidimensional X)
    (hdim : topologicalKrullDim X = 1) (x : X) :
    Nonempty ((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).obj (dualizingSheafOverField f) ≅
      ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x)) := by
  have hcm := AlgebraicGeometry.isCohenMacaulay_of_isGorenstein X
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hK := isDualizingComplex_dualizingComplexOverField_of_topologicalKrullDim_le_one f hdim.le
  obtain ⟨n, hz, ⟨e⟩⟩ :=
    exists_stalk_homology_concentrated_free_of_isGorensteinLocalRing hK x
      (hG.isGorensteinLocalRing x)
  have hn : n = -1 := by
    by_contra hne
    exact not_nontrivial_iff_subsingleton.mpr
      (ModuleCat.isZero_iff_subsingleton.mp (hz (-1) (Ne.symm hne)))
      (nontrivial_stalk_dualizingSheafOverField_of_isCohenMacaulay f hcm hequi hdim x)
  subst hn
  exact ⟨e⟩

/-- **The dualizing sheaf of a proper Gorenstein curve is finite locally free of rank one.** Let
`X` be a proper scheme over a field `k` which is Gorenstein and equidimensional of dimension one.
Then `ω_X = H^{-1}(f^×(𝒪_{Spec k}))` is finite locally free of rank one. -/
theorem isFiniteLocallyFreeOfRank_one_dualizingSheafOverField_of_isGorenstein
    (hG : AlgebraicGeometry.IsGorenstein X) (hequi : TopologicalSpace.Equidimensional X)
    (hdim : topologicalKrullDim X = 1) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (dualizingSheafOverField f) 1 := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hcoh := (dualizingSheafOverField_isCoherent_isCohenMacaulay_supp_eq_univ f
    (AlgebraicGeometry.isCohenMacaulay_of_isGorenstein X) hequi hdim).1
  exact AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_of_forall_stalk_basis _ hcoh 1
    fun x => (Module.Basis.singleton (Fin 1) (X.presheaf.stalk x)).map
      (Iso.toLinearEquiv
        (nonempty_stalk_dualizingSheafOverField_iso_of_isGorenstein f hG hequi hdim x).some).symm

/-- **The dualizing sheaf of a proper Gorenstein curve is invertible.** Let `X` be a proper scheme
over a field `k` which is Gorenstein and equidimensional of dimension one, and let
`ω_X = H^{-1}(f^×(𝒪_{Spec k}))` be the dualizing sheaf of [Stacks, Tag 0BS2]. Then `ω_X` is an
invertible `𝒪_X`-module, and it is finite locally free of rank one. -/
@[stacks 0BS6 "(1)"]
theorem isInvertible_dualizingSheafOverField_of_isGorenstein
    (hG : AlgebraicGeometry.IsGorenstein X) (hequi : TopologicalSpace.Equidimensional X)
    (hdim : topologicalKrullDim X = 1) :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
        (dualizingSheafOverField f) ∧
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        (dualizingSheafOverField f) 1 :=
  have h := isFiniteLocallyFreeOfRank_one_dualizingSheafOverField_of_isGorenstein f hG hequi hdim
  ⟨Stacks.ModuleDescent.isInvertible_of_isFiniteLocallyFreeOfRank_one X _ h, h⟩

end Stacks.Duality

end
