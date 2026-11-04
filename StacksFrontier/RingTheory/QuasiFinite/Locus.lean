module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.Unramified.LocalStructure
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The quasi-finite locus of a finite type ring map is open

## Main definitions

* `quasiFiniteLocus`: the set of primes of `S` at which the `R`-algebra `S` is quasi-finite.

## Main results

* `exists_basicOpen_subset_quasiFiniteLocus`: every point of the quasi-finite locus of a finite
  type ring map has a basic open neighbourhood contained in the locus.
* `isOpen_quasiFiniteLocus`: the quasi-finite locus of a finite type ring map is open.
-/

@[expose] public section



open Algebra

/-- The set of points `q ∈ Spec(S)` at which the `R`-algebra `S` is quasi-finite. -/
def quasiFiniteLocus (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] :
    Set (PrimeSpectrum S) :=
  { p | Algebra.QuasiFiniteAt R p.asIdeal }

/-- Local form of openness of the quasi-finite locus: given a finite-type ring
map `R → S` and a point `q ∈ Spec(S)` at which `S/R` is quasi-finite, there is
an element `r ∉ q.asIdeal` such that `S/R` is quasi-finite at every prime ideal
in the basic open `D(r)`. -/
@[ega "III 4.4.3" "special case", sga "3 V 7.3" "special case"]
lemma exists_basicOpen_subset_quasiFiniteLocus
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    (q : PrimeSpectrum S) (hq : Algebra.QuasiFiniteAt R q.asIdeal) :
    ∃ r : S, r ∉ q.asIdeal ∧
      ∀ p : PrimeSpectrum S, r ∉ p.asIdeal → Algebra.QuasiFiniteAt R p.asIdeal := by
  -- From quasi-finite + finite type, Zariski's main property holds at `q`.
  have hZMT : ZariskisMainProperty R q.asIdeal :=
    have : Algebra.QuasiFiniteAt R q.asIdeal := hq
    ZariskisMainProperty.of_finiteType _
  -- Extract a finite `R`-subalgebra `S'` and `r ∈ S'`, `(r : S) ∉ q`, such that
  -- the away map `Localization.Away r → Localization.Away (r : S)` is bijective.
  obtain ⟨S', hS'fg, r, hrq, hbij⟩ :=
    hZMT.exists_fg_and_exists_notMem_and_awayMap_bijective _
  have hS'fin : Module.Finite R S' := ⟨(Submodule.fg_top _).mpr hS'fg⟩
  have hAwayS' : Algebra.QuasiFinite R (Localization.Away r) := .trans _ S' _
  have hAway : Algebra.QuasiFinite R (Localization.Away r.val) :=
    .of_surjective_algHom (Localization.awayMapₐ S'.val r) hbij.right
  refine ⟨r.val, hrq, fun p hrp ↦ ?_⟩
  let f : Localization.Away r.val →ₐ[S] Localization.AtPrime p.asIdeal :=
    IsLocalization.liftAlgHom (M := .powers r.val) (f := Algebra.ofId _ _) <| by
      simpa [Submonoid.mem_powers_iff] using
        (IsLocalization.map_units (M := p.asIdeal.primeCompl)
          (Localization.AtPrime p.asIdeal) ⟨r.val, hrp⟩).pow
  refine .of_forall_exists_mul_mem_range (f.restrictScalars R) fun x ↦ ?_
  obtain ⟨x, ⟨s, hs⟩, rfl⟩ := IsLocalization.exists_mk'_eq p.asIdeal.primeCompl x
  exact ⟨algebraMap _ _ s, by simpa using IsLocalization.map_units _ ⟨s, hs⟩,
    algebraMap _ _ x, by simp⟩

/-- For a finite-type ring map `R → S`, the locus in `Spec(S)` where `S/R` is quasi-finite is
open. -/
@[stacks 00QA,
  ega "III 4.4.10" "affine case",
  ega "IV 13.1.4" "affine case",
  ega "III 4.4.3" "affine case, X' open", sga "3 V 7.3" "special case"]
theorem isOpen_quasiFiniteLocus
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S] :
    IsOpen (quasiFiniteLocus R S) := by
  refine isOpen_iff_forall_mem_open.mpr fun q hq ↦ ?_
  obtain ⟨r, hrq, hr⟩ := exists_basicOpen_subset_quasiFiniteLocus R S q hq
  exact ⟨(PrimeSpectrum.basicOpen r : Set (PrimeSpectrum S)),
    fun p hp ↦ hr p ((PrimeSpectrum.mem_basicOpen r p).mp hp), (PrimeSpectrum.basicOpen r).isOpen,
    (PrimeSpectrum.mem_basicOpen r q).mpr hrq⟩

end
