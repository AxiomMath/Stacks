module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DimensionFunctionScheme
import all StacksFrontier.AlgebraicGeometry.Duality.CohenMacaulayLocus
import all StacksFrontier.RingTheory.Dualizing.LocallyShiftedSingle
import StacksFrontier.RingTheory.Dualizing.NormalizedUniqueness

/-!
# The dimension function of a dualizing complex on a scheme exists

[Stacks, Tag 0AWF] asserts of a locally Noetherian scheme `X` carrying a dualizing complex
`ω_X^•` both that `X` is universally catenary and that *the* function `x ↦ δ(x)` determined by
the rule that `ω_{X,x}^•⟦-δ(x)⟧` is a normalized dualizing complex over `𝒪_{X,x}` is a dimension
function.  `Stacks.Duality.exists_dimensionFunction_of_isDualizingShiftFunction` proves the
second clause of any function with that property, carrying the property as the hypothesis
`Stacks.Duality.IsDualizingShiftFunction`;
`Stacks.Duality.exists_isDualizingShiftFunction_of_isAffine` produces such a function on an
affine scheme only.  This file produces it on every locally Noetherian scheme, so that the
hypothesis is discharged and both clauses of the tag hold unconditionally.

## Main results

* `Stacks.Duality.exists_isDualizingShiftFunction` — the function `δ` of [Stacks, Tag 0AWF]
  exists on a locally Noetherian scheme carrying a dualizing complex.
* `Stacks.Duality.isUniversallyCatenary_and_exists_dimensionFunction_of_isDualizingComplex` —
  the two clauses of [Stacks, Tag 0AWF] for `δ` read off the dualizing models, with no
  hypothesis on `δ`: `X` is universally catenary, and the function `δ` exists and is a
  dimension function. The source's statement, with `δ` read off the derived stalk, is
  `Stacks.Duality.isUniversallyCatenary_and_isDimensionFunction_associatedShiftFunction` in
  `StacksFrontier/AlgebraicGeometry/Duality/RelativeDualizing/DerivedStalkModel.lean`.

## Implementation notes

*What had to be proved.*  The shift at a point is read off a dualizing model of `K` over an
affine open neighbourhood, and a point lies in many affine opens; the function exists exactly
when the shifts those models produce at a common point agree.  That is
`Stacks.Duality.dualizingDimension_eq_of_isDualizingModelOn`, and with it in hand `δ` is defined
with no choice at all, as the infimum of the set of candidate shifts at the point
(`Stacks.Duality.dualizingShiftSet`), which the comparison shows to be a singleton.  The source
needs none of this because it reads the shift off the derived stalk of `K`, which depends on no
open; the identification of the derived stalk with the extension of a model is
`Stacks.Duality.nonempty_derivedStalkOfComplex_iso_extendScalars`, in
`StacksFrontier/AlgebraicGeometry/Duality/RelativeDualizing/DerivedStalkModel.lean`, which gives the
source's reading directly.

*How two models are compared.*  Let `y` lie in affine opens `U` and `V` with dualizing models
`ω` over `Γ(X, U)` and `ω'` over `Γ(X, V)`.  Both extend, along the respective localization maps,
to dualizing complexes over the *one* ring `𝒪_{X,y}`
(`Dualizing.isDualizingComplex_localization`, [Stacks, Tag 0A7G]; the local ring is the
localization of the sections of either open by
`AlgebraicGeometry.IsAffineOpen.isLocalization_stalk`), and their normalizing shifts are the
values of `Dualizing.dualizingDimension` at the two primes
(`Dualizing.isNormalizedDualizingComplex_derivedExtensionScalars_iff_eq_dualizingDimension`,
which is already stated at an arbitrary presentation of the localization).  The two extensions
are **not** identified with each other — that would be the missing dictionary again — but their
*vanishing patterns* are: in degree `i` the cohomology of either one vanishes exactly when the
stalk at `y` of the `i`-th cohomology sheaf of `K` does.  Two normalized dualizing complexes
over a Noetherian local ring are isomorphic ([Stacks, Tag 0A83],
`Dualizing.IsNormalizedDualizingComplex.nonempty_iso`), so the two translates of that one
pattern coincide, and a nonempty set of integers bounded above admits no nontrivial translation
to itself.  Nonemptiness is that a dualizing complex over a Noetherian local ring is nonzero and
boundedness is its finite injective dimension.

*Two private helpers of other modules are reused rather than restated.*
`Stacks.Duality.subsingleton_stalk_homology_iff_of_isDualizingModelOn` is the translation table
of `StacksFrontier/AlgebraicGeometry/Duality/CohenMacaulayLocus.lean` with the dualizing model
supplied instead of produced — that file's `exists_model_stalk_translation` quantifies the model
existentially, which loses its identity, while comparing two models needs each one named.  The
`import all` of that module and of
`StacksFrontier/RingTheory/Dualizing/LocallyShiftedSingle.lean` is for their `private`
declarations; nothing in either is edited.

*Cohomology at an arbitrary presentation of the localization.*
`Dualizing.localizedHomologyAtPrimeIsoGeneric` identifies the cohomology of a derived
localization with the localization of the cohomology at the particular presentation
`Localization.AtPrime p`.  The comparison above needs it at `𝒪_{X,y}`, so
`Stacks.Duality.localizedHomologyIsoOfIsLocalization` restates it for an arbitrary
presentation; the identification it is assembled from,
`CochainComplex.DerivedTensor.derivedExtensionScalarsLocalizationHomologyIso`, is already
generic, so only the wrapper is new.

*Derived categories.* `D(𝒪_X)` is an instance argument, as in `Stacks.Duality.IsDualizingComplex`
and as in `StacksFrontier/AlgebraicGeometry/Duality/RelativeDualizing/DimensionFunctionScheme.lean`,
so no model is pinned for it.  The derived categories of `ModuleCat Γ(X, U)` and of modules over
the local ring are at `CategoryTheory.HasDerivedCategory.standard`, which is forced:
`Dualizing.IsNormalizedDualizingComplex` bakes that model into its own type.

## References

* [Stacks Project, Tag 0AWF](https://stacks.math.columbia.edu/tag/0AWF)
* [Stacks Project, Tag 0A7G](https://stacks.math.columbia.edu/tag/0A7G)
* [Stacks Project, Tag 0A7W](https://stacks.math.columbia.edu/tag/0A7W)
* [Stacks Project, Tag 0A7Z](https://stacks.math.columbia.edu/tag/0A7Z)
* [Stacks Project, Tag 0A83](https://stacks.math.columbia.edu/tag/0A83)
* [Stacks Project, Tag 0A87](https://stacks.math.columbia.edu/tag/0A87)
* [Stacks Project, Tag 0AWR](https://stacks.math.columbia.edu/tag/0AWR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u w

attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.Duality

/-! ### Cohomology and localization at an arbitrary presentation -/

/-- **Cohomology commutes with derived localization**, at an arbitrary ring `B` presenting the
localization of `A` at `S`. This is `Dualizing.localizedHomologyAtPrimeIsoGeneric` with the
particular presentation `Localization S` replaced by any other; the identification it is built
from, `CochainComplex.DerivedTensor.derivedExtensionScalarsLocalizationHomologyIso`, is already
stated for an arbitrary presentation. -/
private def localizedHomologyIsoOfIsLocalization {A : Type u} [CommRing A] (S : Submonoid A)
    (B : Type u) [CommRing B] [Algebra A B] [IsLocalization S B]
    (K : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) :
    ModuleCat.of A (LocalizedModule S
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj K)) ≅
      (ModuleCat.restrictScalars (algebraMap A B)).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) n).obj
          ((StacksDraft.PseudoCoherence.derivedExtensionScalars (algebraMap A B)).obj K)) := by
  let U := ModuleCat.uliftFunctor.{u, u} A
  let Kbig := U.mapDerivedCategory.obj K
  refine Iso.symm ?_
  change (ModuleCat.restrictScalars (algebraMap A B)).obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) n).obj
        ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars
          (algebraMap A B)).functor.obj Kbig)) ≅ _
  exact (CochainComplex.DerivedTensor.derivedExtensionScalarsLocalizationHomologyIso
      (R := A) (A := B) S n).app Kbig ≪≫
    (CochainComplex.DerivedTensor.localizedModuleFunctor.{u, u} S).mapIso
      ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso U n).app K) ≪≫
    Dualizing.localizedModuleUliftIso (R := A) S
      (M := (DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj K)

/-- Vanishing of the degree `i` cohomology of the derived localization is vanishing of the
localization of the degree `i` cohomology, at an arbitrary presentation of the localization. -/
private lemma isZero_homology_derivedExtensionScalars_iff {A : Type u} [CommRing A]
    (S : Submonoid A) (B : Type u) [CommRing B] [Algebra A B] [IsLocalization S B]
    (K : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).obj
        ((StacksDraft.PseudoCoherence.derivedExtensionScalars (algebraMap A B)).obj K)) ↔
      Subsingleton (LocalizedModule S
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K)) := by
  rw [← isZero_restrictScalars_iff (algebraMap A B),
    ← (localizedHomologyIsoOfIsLocalization S B K i).isZero_iff,
    ModuleCat.isZero_iff_subsingleton]

/-! ### The normalizing shift is determined by the vanishing pattern -/

/-- **Two dualizing complexes over a Noetherian local ring with the same vanishing pattern have
the same normalizing shift.** Their normalizations are isomorphic
(`Dualizing.IsNormalizedDualizingComplex.nonempty_iso`, [Stacks, Tag 0A83]), so the two sets of
degrees in which their cohomology is nonzero — each a translate of the common pattern — agree;
a set of integers that is nonempty and bounded above has only the trivial translation taking it
to itself. Nonemptiness is that a dualizing complex over a Noetherian local ring is nonzero
([Stacks, Tag 0AWR]) and boundedness is that it has finite injective dimension. -/
private lemma eq_of_isNormalizedDualizingComplex_of_isZero_homology_iff {R : Type u} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R]
    {L L' : DerivedCategory (ModuleCat.{u} R)} (hL : Dualizing.IsDualizingComplex L)
    {n n' : ℤ}
    (hn : Dualizing.IsNormalizedDualizingComplex.{u, u} (L⟦-n⟧))
    (hn' : Dualizing.IsNormalizedDualizingComplex.{u, u} (L'⟦-n'⟧))
    (hpat : ∀ i : ℤ, IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj L) ↔
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj L')) :
    n = n' := by
  classical
  obtain ⟨e⟩ := Dualizing.IsNormalizedDualizingComplex.nonempty_iso hn hn'
  -- `H^j(L)` vanishes exactly when `H^(j + (n - n'))(L)` does.
  have key : ∀ j : ℤ,
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) j).obj L) ↔
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) (j + (n - n'))).obj L) := by
    intro j
    have h1 : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) (n + j)).obj (L⟦-n⟧)) ↔
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) (n + j)).obj (L'⟦-n'⟧)) :=
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) (n + j)).mapIso e).isZero_iff
    rw [← (homologyShiftObjIso L (-n) (n + j) j (by omega)).isZero_iff, h1,
      (homologyShiftObjIso L' (-n') (n + j) (j + (n - n')) (by omega)).isZero_iff, ← hpat]
  obtain ⟨a, b, hab⟩ := exists_isZero_homology_outside_Icc L hL
  obtain ⟨i₀, hi₀⟩ := exists_not_isZero_homology L hL
  obtain ⟨m, hm, hmax⟩ := Int.exists_greatest_of_bdd
    (P := fun j : ℤ => ¬ IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) j).obj L))
    ⟨b, fun z hz => by
      by_contra hlt
      exact hz (hab z (by simp only [Finset.mem_Icc]; omega))⟩
    ⟨i₀, hi₀⟩
  have hup : ¬ IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R)
      (m + (n - n'))).obj L) := fun hz => hm ((key m).mpr hz)
  have hdown : ¬ IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R)
      (m - (n - n'))).obj L) := by
    intro hz
    have hshift := (key (m - (n - n'))).mp hz
    rw [show m - (n - n') + (n - n') = m by omega] at hshift
    exact hm hshift
  have h1 := hmax _ hup
  have h2 := hmax _ hdown
  omega

/-! ### The vanishing pattern of a dualizing model at a point -/

section Scheme

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [HasDerivedCategory.{w} X.Modules]

open Stacks.AlgebraicGeometry.CoherentTFAE Stacks.AlgebraicGeometry.FiniteDirectImageCoherent

/-- **A given dualizing model at an affine open computes the sections of every cohomology
sheaf.** This is `Stacks.Duality.exists_specModule_homology_iso` with the model supplied rather
than produced, which is what the comparison of two models needs. -/
private lemma specModule_homology_iso_of_isDualizingModelOn {K : DerivedCategory X.Modules}
    {U : X.Opens} (hU : IsAffineOpen U) (ω : DerivedCategory (ModuleCat.{u} Γ(X, U)))
    (hmodel : IsDualizingModelOn K hU ω) (i : ℤ) :
    Nonempty (specModule ((DerivedCategory.homologyFunctor X.Modules i).obj K) hU ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U)) i).obj ω) := by
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let := HasDerivedCategory.standard U.toScheme.Modules
  obtain ⟨hω, ⟨e⟩⟩ := hmodel
  exact ⟨specModuleIsoOfTildeIso _ hU _ <| ((Dualizing.mapDerivedCategoryHomologyIso
      (Scheme.Modules.restrictFunctor U.ι) i).app K).symm ≪≫
    (DerivedCategory.homologyFunctor _ i).mapIso e ≪≫
    (Dualizing.mapDerivedCategoryHomologyIso
      (tilde.functor Γ(X, U) ⋙ Scheme.Modules.restrictFunctor hU.isoSpec.hom) i).app ω ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback hU.isoSpec.hom).app _⟩

/-- **The translation table at a given dualizing model.** At a point `y` of an affine open `U`
carrying the dualizing model `ω` of `K`, the stalk at `y` of the degree `i` cohomology sheaf of
`K` vanishes exactly when `H^i(ω)` localizes to zero at the prime of `y`. -/
private lemma subsingleton_stalk_homology_iff_of_isDualizingModelOn
    {K : DerivedCategory X.Modules} (hK : IsDualizingComplex K)
    {U : X.Opens} (hU : IsAffineOpen U) (ω : DerivedCategory (ModuleCat.{u} Γ(X, U)))
    (hmodel : IsDualizingModelOn K hU ω) (i : ℤ) (y : X) (hy : y ∈ U) :
    Subsingleton (((DerivedCategory.homologyFunctor X.Modules i).obj K).presheaf.stalk y) ↔
      Subsingleton (LocalizedModule (hU.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U)) i).obj ω)) := by
  have : _root_.SheafOfModules.IsCoherent ((DerivedCategory.homologyFunctor X.Modules i).obj K) :=
    isCoherent_homology_of_isDualizingComplex hK i
  have : ((DerivedCategory.homologyFunctor X.Modules i).obj K).IsQuasicoherent :=
    (isQuasicoherent_isFiniteType_of_isCoherent _).1
  exact (subsingleton_stalk_iff_subsingleton_localizedSpecModule _ hU hy).trans
    (subsingleton_localizedModule_congr _
      (specModule_homology_iso_of_isDualizingModelOn hU ω hmodel i).some.toLinearEquiv)

/-! ### The normalizing shift does not depend on the model -/

/-- **A dualizing model extends to a normalized dualizing complex over the stalk, with the
vanishing pattern of the stalks of `K`.** For a dualizing model `ω` of `K` over an affine open
`U` and `y ∈ U`, its extension `L` to `𝒪_{X,y}` is a dualizing complex, `L⟦-δ_ω(p_y)⟧` is
normalized, and `H^i(L)` vanishes exactly when the stalk at `y` of the `i`-th cohomology sheaf of
`K` does. -/
private lemma isNormalized_and_isZero_homology_of_isDualizingModelOn
    {K : DerivedCategory X.Modules} (hK : IsDualizingComplex K)
    {U : X.Opens} (hU : IsAffineOpen U) [IsNoetherianRing Γ(X, U)]
    (ω : DerivedCategory (ModuleCat.{u} Γ(X, U))) (hω : IsDualizingModelOn K hU ω)
    (y : X) (hy : y ∈ U) [Algebra Γ(X, U) ↥(X.presheaf.stalk y)]
    [IsLocalization.AtPrime ↥(X.presheaf.stalk y) (hU.primeIdealOf ⟨y, hy⟩).asIdeal]
    [IsNoetherianRing ↥(X.presheaf.stalk y)] [IsLocalRing ↥(X.presheaf.stalk y)] :
    Dualizing.IsDualizingComplex ((StacksDraft.PseudoCoherence.derivedExtensionScalars
        (algebraMap Γ(X, U) ↥(X.presheaf.stalk y))).obj ω) ∧
      Dualizing.IsNormalizedDualizingComplex.{u, u}
        (((StacksDraft.PseudoCoherence.derivedExtensionScalars
          (algebraMap Γ(X, U) ↥(X.presheaf.stalk y))).obj ω)⟦-Dualizing.dualizingDimension.{u, u} ω
            (hU.primeIdealOf ⟨y, hy⟩)⟧) ∧
      ∀ i : ℤ, IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} ↥(X.presheaf.stalk y)) i).obj
          ((StacksDraft.PseudoCoherence.derivedExtensionScalars
            (algebraMap Γ(X, U) ↥(X.presheaf.stalk y))).obj ω)) ↔
        Subsingleton (((DerivedCategory.homologyFunctor X.Modules i).obj K).presheaf.stalk y) :=
  have : (hU.primeIdealOf ⟨y, hy⟩).asIdeal.IsPrime := (hU.primeIdealOf ⟨y, hy⟩).isPrime
  ⟨Dualizing.isDualizingComplex_localization
      (hU.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl ω hω.1,
    (Dualizing.isNormalizedDualizingComplex_derivedExtensionScalars_iff_eq_dualizingDimension
      ω hω.1 (hU.primeIdealOf ⟨y, hy⟩) ↥(X.presheaf.stalk y) _).mpr rfl,
    fun i => (isZero_homology_derivedExtensionScalars_iff _ _ ω i).trans
      (subsingleton_stalk_homology_iff_of_isDualizingModelOn hK hU ω hω i y hy).symm⟩

/-- **The value of the dimension function at a point is independent of the dualizing model that
computes it.** Let `y` lie in two affine opens `U` and `V`, each carrying a dualizing model of
the same dualizing complex `K`. Both models extend to dualizing complexes over the one local
ring `𝒪_{X,y}`, and the degrees in which their cohomology survives are the same, each being the
set of degrees in which the cohomology sheaves of `K` have nonvanishing stalk at `y`
(`Stacks.Duality.subsingleton_stalk_homology_iff_of_isDualizingModelOn`); so the normalizing
shifts agree. -/
private lemma dualizingDimension_eq_of_isDualizingModelOn
    {K : DerivedCategory X.Modules} (hK : IsDualizingComplex K)
    {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    [IsNoetherianRing Γ(X, U)] [IsNoetherianRing Γ(X, V)]
    (ω : DerivedCategory (ModuleCat.{u} Γ(X, U))) (hω : IsDualizingModelOn K hU ω)
    (ω' : DerivedCategory (ModuleCat.{u} Γ(X, V))) (hω' : IsDualizingModelOn K hV ω')
    (y : X) (hyU : y ∈ U) (hyV : y ∈ V) :
    Dualizing.dualizingDimension.{u, u} ω (hU.primeIdealOf ⟨y, hyU⟩) =
      Dualizing.dualizingDimension.{u, u} ω' (hV.primeIdealOf ⟨y, hyV⟩) := by
  let : Algebra Γ(X, U) ↥(X.presheaf.stalk y) := X.presheaf.algebra_section_stalk ⟨y, hyU⟩
  let : Algebra Γ(X, V) ↥(X.presheaf.stalk y) := X.presheaf.algebra_section_stalk ⟨y, hyV⟩
  have : IsLocalization.AtPrime ↥(X.presheaf.stalk y) (hU.primeIdealOf ⟨y, hyU⟩).asIdeal :=
    hU.isLocalization_stalk ⟨y, hyU⟩
  have : IsLocalization.AtPrime ↥(X.presheaf.stalk y) (hV.primeIdealOf ⟨y, hyV⟩).asIdeal :=
    hV.isLocalization_stalk ⟨y, hyV⟩
  have : (hU.primeIdealOf ⟨y, hyU⟩).asIdeal.IsPrime := (hU.primeIdealOf ⟨y, hyU⟩).isPrime
  have : IsNoetherianRing ↥(X.presheaf.stalk y) :=
    IsLocalization.isNoetherianRing (hU.primeIdealOf ⟨y, hyU⟩).asIdeal.primeCompl _ inferInstance
  have : IsLocalRing ↥(X.presheaf.stalk y) :=
    IsLocalization.AtPrime.isLocalRing _ (hU.primeIdealOf ⟨y, hyU⟩).asIdeal
  obtain ⟨hLU, hnU, hpU⟩ :=
    isNormalized_and_isZero_homology_of_isDualizingModelOn hK hU ω hω y hyU
  obtain ⟨-, hnV, hpV⟩ :=
    isNormalized_and_isZero_homology_of_isDualizingModelOn hK hV ω' hω' y hyV
  exact eq_of_isNormalizedDualizingComplex_of_isZero_homology_iff hLU hnU hnV fun i =>
    (hpU i).trans (hpV i).symm

/-! ### The shift function exists -/

/-- **The candidate values at `y` of the shift function of `K`**: the integers `n` for which
some affine open neighbourhood of `y` carries a dualizing model `ω` of `K` with
`ω^•_{X,y}⟦-n⟧` a normalized dualizing complex over `𝒪_{X,y}`. -/
private def dualizingShiftSet (K : DerivedCategory X.Modules) (y : X) : Set ℤ :=
  {n : ℤ | ∃ (U : X.Opens) (hU : IsAffineOpen U) (hy : y ∈ U)
    (ω : DerivedCategory (ModuleCat.{u} Γ(X, U))),
      IsDualizingModelOn K hU ω ∧ IsNormalizedShiftAt hU ω ⟨y, hy⟩ n}

/-- **The shift function of `K`.** The candidate set is a singleton, by
`Stacks.Duality.dualizingShift_isNormalizedShiftAt`, and the infimum names its element; no
choice of affine open or of dualizing model is made. -/
private def dualizingShift (K : DerivedCategory X.Modules) (y : X) : ℤ :=
  sInf (dualizingShiftSet K y)

/-- **Every dualizing model normalizes at the value of `Stacks.Duality.dualizingShift`.** The
candidate set at `y` is the singleton `{δ_ω(p_y)}` for any one model `ω` over an affine open
neighbourhood of `y`: it contains that value, and every other model produces the same one by
`Stacks.Duality.dualizingDimension_eq_of_isDualizingModelOn`. -/
private lemma dualizingShift_isNormalizedShiftAt {K : DerivedCategory X.Modules}
    (hK : IsDualizingComplex K) {U : X.Opens} (hU : IsAffineOpen U)
    (ω : DerivedCategory (ModuleCat.{u} Γ(X, U))) (hω : IsDualizingModelOn K hU ω)
    (y : X) (hy : y ∈ U) :
    IsNormalizedShiftAt hU ω ⟨y, hy⟩ (dualizingShift K y) := by
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have hset : dualizingShiftSet K y =
      {Dualizing.dualizingDimension.{u, u} ω (hU.primeIdealOf ⟨y, hy⟩)} := by
    ext n
    simp only [Set.mem_singleton_iff, dualizingShiftSet, Set.mem_ofPred_eq]
    refine ⟨?_, fun hn => ⟨U, hU, hy, ω, hω,
      (isNormalizedShiftAt_iff_eq_dualizingDimension hU ω hω.1 ⟨y, hy⟩ n).mpr hn⟩⟩
    rintro ⟨V, hV, hyV, ω', hω', hn⟩
    have : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
    rw [isNormalizedShiftAt_iff_eq_dualizingDimension hV ω' hω'.1 ⟨y, hyV⟩ n] at hn
    exact hn.trans (dualizingDimension_eq_of_isDualizingModelOn hK hV hU ω' hω' ω hω y hyV hy)
  rw [isNormalizedShiftAt_iff_eq_dualizingDimension hU ω hω.1 ⟨y, hy⟩ _]
  show dualizingShift K y = _
  rw [dualizingShift, hset, csInf_singleton]

/-- **The function `δ` of [Stacks, Tag 0AWF] exists, in the model reading.** On a locally
Noetherian scheme carrying a dualizing complex `K` there is a function `δ : X → ℤ` such that at
every point some affine open neighbourhood carries a dualizing model `ω` of `K` with
`ω^•_{X,y}⟦-δ(y)⟧` a normalized dualizing complex over `𝒪_{X,y}` for every `y` of that
neighbourhood.

This removes the hypothesis `Stacks.Duality.IsDualizingShiftFunction` from
`Stacks.Duality.exists_dimensionFunction_of_isDualizingShiftFunction`: the normalizing shift at
a point is the same for every dualizing model over every affine open neighbourhood of it, so the
locally defined shifts glue. -/
public theorem exists_isDualizingShiftFunction {K : DerivedCategory X.Modules}
    (hK : IsDualizingComplex K) :
    ∃ δ : X → ℤ, IsDualizingShiftFunction K δ := by
  refine ⟨dualizingShift K, fun x => ?_⟩
  obtain ⟨-, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  obtain ⟨ω, hω, he⟩ := hK U hU
  exact ⟨U, hU, hxU, ω, ⟨hω, he⟩,
    fun y => dualizingShift_isNormalizedShiftAt hK hU ω ⟨hω, he⟩ y y.2⟩

/-- **The two clauses of [Stacks, Tag 0AWF], for the model reading of `δ`.** A locally Noetherian
scheme `X` carrying a dualizing complex `K` is universally catenary, and the function
`δ : X → ℤ` determined by the rule that `ω^•_{X,x}⟦-δ(x)⟧` is a normalized dualizing complex over
`𝒪_{X,x}`, with `ω^•_{X,x}` the extension of a dualizing model over an affine open
neighbourhood, exists and is a dimension function on `X`.

Universal catenarity is `Stacks.Duality.isUniversallyCatenary_of_isDualizingComplex`; the
existence of `δ` is `Stacks.Duality.exists_isDualizingShiftFunction`; and that such a `δ` is a
dimension function is `Stacks.Duality.exists_dimensionFunction_of_isDualizingShiftFunction`,
the affine case [Stacks, Tag 0A7Z] spread over an affine cover. -/
public theorem isUniversallyCatenary_and_exists_dimensionFunction_of_isDualizingComplex
    {K : DerivedCategory X.Modules} (hK : IsDualizingComplex K) :
    AlgebraicGeometry.Scheme.IsUniversallyCatenary X ∧
      ∃ δ : X → ℤ, IsDualizingShiftFunction K δ ∧
        ∃ d : DimensionFunction X, ∀ x : X, d x = δ x := by
  obtain ⟨δ, hδ⟩ := exists_isDualizingShiftFunction hK
  exact ⟨isUniversallyCatenary_of_isDualizingComplex hK, δ, hδ,
    exists_dimensionFunction_of_isDualizingShiftFunction K δ hδ⟩

end Scheme

end Stacks.Duality

end
