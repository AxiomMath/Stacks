module

public import Mathlib.Algebra.Category.ModuleCat.Localization
public import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.Shrink
public import Mathlib.CategoryTheory.Preadditive.Projective.Preserves
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.RingTheory.LocalProperties.ProjectiveDimension
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import StacksFrontier.Algebra.Homology.ProjectiveDimension.FiniteResolution
public import StacksFrontier.Homology.Perfect.Basic
public import StacksFrontier.Homology.Perfect.Module
public import StacksFrontier.RingTheory.RegularLocalRing.GlobalDimension
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Perfect complexes over a regular ring

Let `R` be a regular commutative ring. Over such a ring, perfectness is no longer a genuinely
homological condition: an `R`-module is perfect exactly when it is finite, and an object of the
derived category `D(R)` is perfect exactly when it is bounded and all of its cohomology modules
are finite. The module statement is proved by producing a uniform bound on projective dimension:
the locus of primes at which a finite module has projective dimension at most `n` is open, these
loci exhaust the prime spectrum because each local ring of `R` is regular and hence of finite
global dimension, and the spectrum is quasi-compact. The derived statement then follows from the
module statement together with [stacks 066U], which upgrades perfect cohomology to perfectness for
a bounded object.

## Main results

* `StacksDraft.Perfect.isPerfectModule_iff_finite_and_isPerfect_iff_bounded_finiteCohomology`:
  over a regular ring, perfect modules are exactly the finite modules, and perfect objects of the
  derived category are exactly the bounded objects with finite cohomology modules ([stacks 066Z]).

## Implementation notes

A complex is represented by its object in the derived category. Membership in the bounded derived
category is expressed by the existence of lower and upper bounds for the canonical t-structure.
Modules and complexes live in the common universe `max u v` containing the ring, so that the
finite free resolutions used in the proof are available in the same module category; the auxiliary
lemmas are therefore stated for a module category `ModuleCat.{v} R` over a ring `R : Type u`
carrying `Small.{v} R`, which is what the descent to `ModuleCat.{u} R` used for global dimension
requires.

## References

* [Stacks Project, Tag 066Z](https://stacks.math.columbia.edu/tag/066Z)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace StacksDraft.Perfect

/-- The locus of primes `p` of `R` at which the localization of `M` has projective dimension at
most `n`. -/
private def projectiveDimensionLELocus {R : Type u} [CommRing R] [Small.{v} R]
    (M : ModuleCat.{v} R) (n : ℕ) : Set (PrimeSpectrum R) :=
  {p | HasProjectiveDimensionLE (M.localizedModule p.asIdeal.primeCompl) n}

/-- For a finite module, the locus where the projective dimension is at most `0` is the free
locus: over a local ring a finite projective module is free, and conversely. -/
private lemma projectiveDimensionLELocus_zero {R : Type u} [CommRing R] [Small.{v} R]
    (M : ModuleCat.{v} R) [Module.Finite R M] :
    projectiveDimensionLELocus M 0 = Module.freeLocus R M := by
  ext p
  show (HasProjectiveDimensionLE (M.localizedModule p.asIdeal.primeCompl) 0) ↔
    Module.Free (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M)
  have : Module.Finite (Localization.AtPrime p.asIdeal)
      (LocalizedModule p.asIdeal.primeCompl M) :=
    Module.Finite.of_isLocalizedModule p.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)
  show HasProjectiveDimensionLT (M.localizedModule p.asIdeal.primeCompl) 1 ↔ _
  rw [← projective_iff_hasProjectiveDimensionLT_one]
  have : Small.{v} (Localization.AtPrime p.asIdeal) :=
    small_of_surjective Localization.mkHom_surjective
  have : Small.{v} (LocalizedModule p.asIdeal.primeCompl M) :=
    small_of_surjective (IsLocalizedModule.mk'_surjective p.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M))
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have : Module.Projective (Localization.AtPrime p.asIdeal)
        (Shrink.{v} (LocalizedModule p.asIdeal.primeCompl M)) :=
      ModuleCat.projective_of_module_projective (M.localizedModule p.asIdeal.primeCompl)
    have : Module.Projective (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl M) := Module.Projective.of_shrink
    have : Module.Flat (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl M) := Module.Flat.of_projective
    exact Module.free_of_flat_of_isLocalRing
  · have : Module.Projective (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl M) := .of_free
    have : Module.Projective (Localization.AtPrime p.asIdeal)
        (M.localizedModule p.asIdeal.primeCompl) :=
      Module.Projective.of_equiv' (Shrink.linearEquiv.{v} _ _).symm
    exact ModuleCat.projective_of_categoryTheory_projective _

/-- Over a Noetherian ring, the locus where a finite module has projective dimension at most `n`
is open: the case `n = 0` is openness of the free locus, and the inductive step transfers the
question to the kernel of a finite presentation, using that localization is exact and preserves
projectives. -/
private lemma isOpen_projectiveDimensionLELocus {R : Type u} [CommRing R] [Small.{v} R]
    [IsNoetherianRing R] (M : ModuleCat.{v} R) [Module.Finite R M] (n : ℕ) :
    IsOpen (projectiveDimensionLELocus M n) := by
  induction n generalizing M with
  | zero =>
    rw [projectiveDimensionLELocus_zero]
    have : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
    exact Module.isOpen_freeLocus
  | succ n ih =>
    obtain ⟨P, _, _, _, _, f, surjf⟩ := Module.exists_finite_presentation R M
    let S := f.shortComplexKer
    have hS : S.ShortExact := LinearMap.shortExact_shortComplexKer surjf
    have hP : Projective S.X₂ := ModuleCat.projective_of_categoryTheory_projective S.X₂
    have heq : projectiveDimensionLELocus M (n + 1) =
        projectiveDimensionLELocus (ModuleCat.of R (LinearMap.ker f)) n := by
      ext p
      let Sp := S.map (ModuleCat.localizedModuleFunctor p.asIdeal.primeCompl)
      have hSp : Sp.ShortExact :=
        hS.map_of_exact (ModuleCat.localizedModuleFunctor p.asIdeal.primeCompl)
      have hp : Projective Sp.X₂ :=
        (ModuleCat.localizedModuleFunctor.{v} p.asIdeal.primeCompl).projective_obj_of_projective
          hP
      show HasProjectiveDimensionLE Sp.X₃ (n + 1) ↔
        HasProjectiveDimensionLE Sp.X₁ n
      exact hSp.hasProjectiveDimensionLT_X₃_iff n hp
    exact heq ▸ ih _

/-- A finite module over a regular local ring has finite projective dimension, because such a ring
has finite global dimension. -/
@[sga "6 IX 1.5" "partial"]
private lemma projectiveDimension_ne_top_of_isRegularLocalRing {R : Type u} [CommRing R]
    [IsRegularLocalRing R] [Small.{v} R] (M : ModuleCat.{v} R) [Module.Finite R M] :
    projectiveDimension M ≠ ⊤ := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  have : Small.{u} (M : Type v) := small_of_surjective hf
  let N : ModuleCat.{u} R := ModuleCat.of R (Shrink.{u} M)
  have hglob : (⨆ L : ModuleCat.{u} R, projectiveDimension L) ≠ ⊤ :=
    ((isRegularLocalRing_tfae (R := R)).out 3 2).mp ‹IsRegularLocalRing R›
  have hN : projectiveDimension N ≠ ⊤ :=
    ne_top_of_le_ne_top hglob (le_iSup (fun L : ModuleCat.{u} R => projectiveDimension L) N)
  rwa [ModuleCat.projectiveDimension_eq_of_linearEquiv (Shrink.linearEquiv.{u} R M)] at hN

/-- A finite module over a regular ring has projective dimension at most some natural number:
the loci of bounded projective dimension are open and cover the spectrum, which is quasi-compact,
so finitely many of them suffice and one may take the maximum of the corresponding bounds. -/
private lemma exists_hasProjectiveDimensionLE {R : Type u} [CommRing R] [IsRegularRing R]
    [Small.{v} R] (M : ModuleCat.{v} R) [Module.Finite R M] :
    ∃ n : ℕ, HasProjectiveDimensionLE M n := by
  let U : ℕ → Set (PrimeSpectrum R) := projectiveDimensionLELocus M
  have hcover : (Set.univ : Set (PrimeSpectrum R)) ⊆ ⋃ n, U n := by
    intro p _
    have : Small.{v} (Localization.AtPrime p.asIdeal) :=
      small_of_surjective Localization.mkHom_surjective
    have : IsRegularLocalRing (Localization.AtPrime p.asIdeal) :=
      IsRegularRing.isRegularLocalRing_localization p.asIdeal
    have : Module.Finite (Localization.AtPrime p.asIdeal)
        (M.localizedModule p.asIdeal.primeCompl) :=
      Module.Finite.of_isLocalizedModule p.asIdeal.primeCompl
        (M.localizedModuleMkLinearMap p.asIdeal.primeCompl)
    obtain ⟨n, hn⟩ := (projectiveDimension_ne_top_iff
      (M.localizedModule p.asIdeal.primeCompl)).mp
        (projectiveDimension_ne_top_of_isRegularLocalRing _)
    exact Set.mem_iUnion.mpr ⟨n, hn⟩
  obtain ⟨t, ht⟩ :=
    isCompact_univ.elim_finite_subcover U (isOpen_projectiveDimensionLELocus M) hcover
  refine ⟨t.sup id, (M.hasProjectiveDimensionLE_iff_forall_primeSpectrum _).mpr fun p ↦ ?_⟩
  obtain ⟨i, hit, hpi⟩ : ∃ i ∈ t, p ∈ U i := by
    simpa only [Set.mem_iUnion, exists_prop] using ht (Set.mem_univ p)
  have hle : i ≤ t.sup id := Finset.le_sup (f := id) hit
  have : HasProjectiveDimensionLT (M.localizedModule p.asIdeal.primeCompl) (i + 1) := hpi
  exact hasProjectiveDimensionLT_of_ge _ (i + 1) (t.sup id + 1) (by omega)

/-- A finite module over a regular ring is perfect: it has finite projective dimension, hence a
finite resolution by finite projective modules, which is the characterization [stacks 066Q] of
perfectness. -/
private lemma isPerfectModule_of_finite {R : Type u} [CommRing R] [IsRegularRing R]
    [Small.{v} R] (M : Type v) [AddCommGroup M] [Module R M]
    [Module.Finite R M] : IsPerfectModule (R := R) M := by
  obtain ⟨d, hd⟩ := exists_hasProjectiveDimensionLE (ModuleCat.of R M)
  obtain ⟨F, hF⟩ :=
    (ModuleCat.hasProjectiveDimensionLE_iff_exists_leftResolution_projective_finite
      (ModuleCat.of R M) d).mp hd
  let G : ModuleResolution R M :=
    { complex := F.complex
      hasHomology := F.hasHomology
      π := F.π
      quasiIso := F.quasiIso }
  have hG : ∀ i : ℕ, Module.Finite R (G.complex.X i) ∧
      Module.Projective R (G.complex.X i) := by
    intro i
    obtain ⟨_, hfin⟩ := F.property i
    exact ⟨hfin, ModuleCat.projective_of_module_projective _⟩
  exact (isPerfectModule_iff_exists_finite_projective_resolution M).2 ⟨d, G, hG, hF⟩

/-- Over a Noetherian ring, a cochain complex with a finite module in degree `i` has finite
homology in degree `i`: the cycles are a submodule of a Noetherian module and the homology is a
quotient of the cycles. -/
private lemma finite_homology_of_finite_X {R : Type u} [CommRing R] [IsNoetherianRing R]
    (P : CochainComplex (ModuleCat.{v} R) ℤ) (i : ℤ)
    [Module.Finite R (P.X i)] : Module.Finite R (P.homology i) := by
  have : Module.Finite R (P.cycles i) :=
    Module.Finite.of_injective (P.iCycles i).hom
      ((ModuleCat.mono_iff_injective _).mp (inferInstance : Mono (P.iCycles i)))
  exact Module.Finite.of_surjective (P.homologyπ i).hom
    ((ModuleCat.epi_iff_surjective _).mp (inferInstance : Epi (P.homologyπ i)))

/-- Over a Noetherian ring, a perfect object of the derived category is bounded and has finite
cohomology modules: transport the bounds and the finiteness of homology along the isomorphism with
a bounded complex of finite projective modules. -/
private lemma bounded_and_finite_homology_of_isPerfect {R : Type u} [CommRing R]
    [IsNoetherianRing R] (K : DerivedCategory (ModuleCat.{v} R)) (hK : IsPerfect K) :
    (∃ a : ℤ, K.IsGE a) ∧ (∃ b : ℤ, K.IsLE b) ∧
      ∀ i : ℤ, Module.Finite R
        ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj K) := by
  obtain ⟨P, a, b, hPge, hPle, hPfin, _, ⟨e⟩⟩ := hK
  have : P.IsStrictlyGE a := hPge
  have : P.IsStrictlyLE b := hPle
  refine ⟨⟨a, ?_⟩, ⟨b, ?_⟩, fun i ↦ ?_⟩
  · exact DerivedCategory.TStructure.t.isGE_of_iso e.symm a
  · exact DerivedCategory.TStructure.t.isLE_of_iso e.symm b
  · have : Module.Finite R (P.X i) := hPfin i
    have : Module.Finite R
        ((HomologicalComplex.homologyFunctor (ModuleCat.{v} R)
          (ComplexShape.up ℤ) i).obj P) := finite_homology_of_finite_X P i
    have : Module.Finite R
        ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj
          (DerivedCategory.Q.obj P)) :=
      Module.Finite.equiv
        ((DerivedCategory.homologyFunctorFactors (ModuleCat.{v} R) i).app P).symm.toLinearEquiv
    exact Module.Finite.equiv
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).mapIso e.symm).toLinearEquiv

/-- **Stacks 066Z.** Over a regular ring, perfect modules are precisely finite modules, and
perfect derived objects are precisely the bounded objects with finite cohomology modules. -/
@[stacks 066Z]
theorem isPerfectModule_iff_finite_and_isPerfect_iff_bounded_finiteCohomology
    {R : Type u} [CommRing R] [IsRegularRing R] :
    (∀ (M : Type (max u v)) [AddCommGroup M] [Module R M],
      IsPerfectModule (R := R) M ↔ Module.Finite R M) ∧
    (∀ K : DerivedCategory (ModuleCat.{max u v} R),
      IsPerfect K ↔
        ((∃ a : ℤ, K.IsGE a) ∧ (∃ b : ℤ, K.IsLE b) ∧
          ∀ i : ℤ,
            Module.Finite R
              ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).obj K))) := by
  have hmod : ∀ (M : Type (max u v)) [AddCommGroup M] [Module R M],
      IsPerfectModule (R := R) M ↔ Module.Finite R M := by
    intro M _ _
    refine ⟨fun h ↦ ?_, fun _ ↦ isPerfectModule_of_finite (R := R) M⟩
    have : Module.Finite R
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0 ⋙
          DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) 0).obj (ModuleCat.of R M)) :=
      (bounded_and_finite_homology_of_isPerfect _ h).2.2 0
    exact Module.Finite.equiv
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso
        (ModuleCat.{max u v} R) 0).app (ModuleCat.of R M)).toLinearEquiv
  exact ⟨hmod, fun K ↦ ⟨bounded_and_finite_homology_of_isPerfect K, fun h ↦
    isPerfect_of_bounded_of_cohomology_isPerfect K ⟨h.1, h.2.1⟩ fun i ↦ (hmod _).2 (h.2.2 i)⟩⟩

end StacksDraft.Perfect
