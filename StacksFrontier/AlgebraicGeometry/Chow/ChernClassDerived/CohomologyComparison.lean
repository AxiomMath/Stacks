module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassComplex
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.TwoTermResolution
public import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FiniteLocallyFreeBiprod
public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.Quasicoherent.IdealPowerMultiple
public import StacksFrontier.Deformation.ToposThickening.ModulesOnThickening.ExtBoundary
public import StacksFrontier.Deformation.ToposThickening.ModulesOnThickening.ExtTorsor
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic

/-!
# The alternating class of a complex depends only on its derived object

Let `X` be a locally Noetherian scheme and let `E` be an object of `D(𝒪_X)` whose cohomology
modules `H^i(E)` are perfect of Tor dimension at most one. This file proves that two bounded
complexes `P` and `Q` of finite locally free `𝒪_X`-modules representing `E` have the same
alternating class `∑_n (-1)^n [P^n] = ∑_n (-1)^n [Q^n]` in `K_0(Vect(X))`. This is the algebraic
heart of the proof of Stacks 0ESZ — its last two paragraphs — and, through the constructions of
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassComplex`, gives the independence of the
representative for the Chern classes, the power sum classes and the Chern character of a
complex.

The proof follows the source. First, Stacks 0F8J: by descending induction on the degree, the
short exact sequences

  `0 ⟶ Im(d^{n-1}) ⟶ Ker(d^n) ⟶ H^n ⟶ 0`  and  `0 ⟶ Ker(d^n) ⟶ P^n ⟶ Im(d^n) ⟶ 0`

show that all kernels and images of the differentials are finite locally free: the kernel of a
surjection from a finite locally free module onto a module of Tor dimension at most one is flat,
and on a locally Noetherian scheme it is also of finite presentation, hence finite locally free
(Stacks 05P2). This produces the datum `Stacks.Chow.BoundedComplexSplitting`. Second, Schanuel's
lemma, Stacks 00O3: for the two presentations `0 ⟶ B_P ⟶ Z_P ⟶ H ⟶ 0` and
`0 ⟶ B_Q ⟶ Z_Q ⟶ H ⟶ 0` of one cohomology module, the fibre product `𝒢 = Z_P ×_H Z_Q` is the
kernel of `Z_P ⊞ Z_Q ⟶ H`, hence finite locally free, and it sits in short exact sequences
`0 ⟶ B_P ⟶ 𝒢 ⟶ Z_Q ⟶ 0` and `0 ⟶ B_Q ⟶ 𝒢 ⟶ Z_P ⟶ 0`. This produces the datum
`Stacks.Chow.ComplexCohomologyComparison`, and
`Stacks.Chow.alternatingKClass_eq_of_cohomologyComparison` concludes.

## Main definitions

* `Stacks.Chow.differentialImage` — the image `Im(d^{n-1}) ⊆ P^n` of a differential.
* `Stacks.Chow.boundedComplexSplitting` — the kernels and images of the differentials of a
  bounded complex of finite locally free modules whose cohomology modules have Tor dimension at
  most one, as a `Stacks.Chow.BoundedComplexSplitting`.
* `Stacks.Chow.schanuelModule` — the fibre product `Z_P ×_H Z_Q` of Schanuel's lemma.
* `Stacks.Chow.complexCohomologyComparison` — two such complexes with isomorphic cohomology, with
  their Schanuel modules, as a `Stacks.Chow.ComplexCohomologyComparison`.

## Main results

* `Stacks.Chow.isFiniteLocallyFree_cycles_and_differentialImage` — Stacks 0F8J for a bounded
  above complex on a locally Noetherian scheme: the kernels and images of the differentials are
  finite locally free.
* `Stacks.Chow.isFiniteLocallyFree_schanuelModule` — Schanuel's lemma, Stacks 00O3: the
  Schanuel module is finite locally free.
* `Stacks.Chow.alternatingKClass_eq_of_iso_derivedCategory` — two bounded complexes of finite
  locally free modules representing the same object of `D(𝒪_X)`, whose cohomology modules are
  perfect of Tor dimension at most one, have the same alternating class in `K_0(Vect(X))`.

## Implementation notes

The scheme is assumed locally Noetherian, as is every scheme locally of finite type over the
base of Situation 02QL, which is where Stacks 0ESZ takes place. It is used once: an image of a
differential, a quasi-coherent submodule of a finite locally free module, is then of finite
presentation (Stacks 01Y1 and 01XZ).

The image `Im(d^{n-1})` is taken of the differential `P^{prev n} ⟶ P^n`, with
`prev n = n - 1` only propositionally, so that the surjection `P^n ⟶ Im(d^n)` and the
inclusion `Im(d^n) ⟶ P^{n+1}` of `Stacks.Chow.BoundedComplexSplitting` need no transport.

## References

* [Stacks Project, Tag 0ESZ](https://stacks.math.columbia.edu/tag/0ESZ)
* [Stacks Project, Tag 0F8J](https://stacks.math.columbia.edu/tag/0F8J)
* [Stacks Project, Tag 00O3](https://stacks.math.columbia.edu/tag/00O3)
* [Stacks Project, Tag 05P2](https://stacks.math.columbia.edu/tag/05P2)
* [Stacks Project, Tag 01Y1](https://stacks.math.columbia.edu/tag/01Y1)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.PerfectComplexes Stacks.Cohomology.TorAmplitude

universe u

namespace Stacks.Chow

attribute [local instance] HasDerivedCategory.standard

variable {X : Scheme.{u}}

/-! ### Finiteness of submodules of finite locally free modules -/

/-- A finite locally free module on a scheme is quasi-coherent; this is
`Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree` read at the
spelling of `Stacks.FiniteLocallyFree.IsFiniteLocallyFree`. -/
private theorem isQuasicoherent_of_stacks {M : X.Modules}
    (h : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) M) :
    M.IsQuasicoherent :=
  Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree M

/-- On a locally Noetherian scheme, a quasi-coherent submodule of a finite locally free module is
of finite presentation: it is of finite type by Stacks 01Y1, hence coherent by Stacks 01XZ. -/
theorem isFinitePresentation_of_mono_of_isFiniteLocallyFree [IsLocallyNoetherian X]
    {G F : X.Modules} [G.IsQuasicoherent]
    (hF : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) F)
    (ι : G ⟶ F) [Mono ι] : G.IsFinitePresentation := by
  have : F.IsQuasicoherent := isQuasicoherent_of_stacks hF
  have : F.IsFiniteType := Stacks.FiniteLocallyFree.isFiniteType (h := hF) F
  have : G.IsFiniteType :=
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isFiniteType_of_mono_of_isQuasicoherent ι
  exact (Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_iff_isFinitePresentation G).1
    (Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_of_isQuasicoherent_of_isFiniteType G)

/-- **The kernel of a surjection from a finite locally free module onto a module of Tor dimension
at most one is finite locally free**, on a locally Noetherian scheme, as soon as it is
quasi-coherent. -/
theorem isFiniteLocallyFree_of_shortExact_of_isLocallyNoetherian [IsLocallyNoetherian X]
    (S : ShortComplex X.Modules) (hS : S.ShortExact) [S.X₁.IsQuasicoherent]
    (h₂ : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) S.X₂)
    (h₃ : HasTorAmplitude X.toRingedSpace
      ((DerivedCategory.singleFunctor X.Modules 0).obj S.X₃) (-1) 0) :
    Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) S.X₁ := by
  have := hS.mono_f
  exact isFiniteLocallyFree_of_shortExact_hasTorAmplitude S hS h₂ h₃
    (isFinitePresentation_of_mono_of_isFiniteLocallyFree h₂ S.f)

/-! ### The images of the differentials of a complex -/

section Images

variable (P : CochainComplex X.Modules ℤ)

/-- The image `Im(d^{n-1}) ⊆ P^n` of the differential into degree `n`. -/
abbrev differentialImage (n : ℤ) : X.Modules :=
  Limits.image (P.d ((ComplexShape.up ℤ).prev n) n)

/-- The inclusion `Im(d^{n-1}) ⟶ P^n`. -/
abbrev differentialImageι (n : ℤ) : differentialImage P n ⟶ P.X n :=
  image.ι _

/-- The surjection `P^n ⟶ Im(d^n)` of a term onto the image of its differential. -/
def toDifferentialImage (n : ℤ) : P.X n ⟶ differentialImage P (n + 1) :=
  (P.xPrevIso (show (ComplexShape.up ℤ).Rel n (n + 1) from rfl)).inv ≫ factorThruImage _

/-- The map of a term onto the image of its differential is an epimorphism. -/
instance (n : ℤ) : Epi (toDifferentialImage P n) :=
  epi_comp _ _

/-- The surjection onto the image followed by the inclusion of the image is the differential. -/
@[reassoc (attr := simp)]
theorem toDifferentialImage_comp_ι (n : ℤ) :
    toDifferentialImage P n ≫ differentialImageι P (n + 1) = P.d n (n + 1) := by
  rw [toDifferentialImage, Category.assoc, image.fac]
  exact P.xPrevIso_comp_dTo (show (ComplexShape.up ℤ).Rel n (n + 1) from rfl)

/-- The image factorization of the differential into degree `n`. -/
@[reassoc (attr := simp)]
theorem factorThruImage_comp_differentialImageι (n : ℤ) :
    factorThruImage (P.d ((ComplexShape.up ℤ).prev n) n) ≫ differentialImageι P n =
      P.d ((ComplexShape.up ℤ).prev n) n :=
  image.fac _

/-- The inclusion `Im(d^{n-1}) ⟶ Ker(d^n)` of the image into the cycles. -/
def differentialImageToCycles (n : ℤ) : differentialImage P n ⟶ P.cycles n :=
  P.liftCycles (differentialImageι P n) (n + 1) (by simp) (by
    rw [← cancel_epi (factorThruImage (P.d ((ComplexShape.up ℤ).prev n) n)),
      factorThruImage_comp_differentialImageι_assoc, HomologicalComplex.d_comp_d, comp_zero])

/-- The inclusion of the image into the cycles, followed by the inclusion of the cycles into the
term, is the inclusion of the image into the term. -/
@[reassoc (attr := simp)]
theorem differentialImageToCycles_iCycles (n : ℤ) :
    differentialImageToCycles P n ≫ P.iCycles n = differentialImageι P n := by
  simp [differentialImageToCycles]

/-- The inclusion of the image into the cycles is a monomorphism. -/
instance (n : ℤ) : Mono (differentialImageToCycles P n) :=
  mono_of_mono_fac (differentialImageToCycles_iCycles P n)

/-- The map `P^{n-1} ⟶ Ker(d^n)` induced by the differential factors through the image. -/
@[reassoc]
theorem factorThruImage_comp_differentialImageToCycles (n : ℤ) :
    factorThruImage (P.d ((ComplexShape.up ℤ).prev n) n) ≫ differentialImageToCycles P n =
      P.toCycles ((ComplexShape.up ℤ).prev n) n := by
  rw [← cancel_mono (P.iCycles n)]
  simp

/-- The image maps to zero in the cohomology. -/
@[reassoc (attr := simp)]
theorem differentialImageToCycles_homologyπ (n : ℤ) :
    differentialImageToCycles P n ≫ P.homologyπ n = 0 := by
  rw [← cancel_epi (factorThruImage (P.d ((ComplexShape.up ℤ).prev n) n)),
    factorThruImage_comp_differentialImageToCycles_assoc, comp_zero]
  exact P.toCycles_comp_homologyπ _ n

/-- The short complex `0 ⟶ Im(d^{n-1}) ⟶ Ker(d^n) ⟶ H^n ⟶ 0`. -/
abbrev cohomologyShortComplex (n : ℤ) : ShortComplex X.Modules :=
  ShortComplex.mk (differentialImageToCycles P n) (P.homologyπ n)
    (differentialImageToCycles_homologyπ P n)

/-- **The cohomology module is the quotient of the cycles by the image.** The sequence
`0 ⟶ Im(d^{n-1}) ⟶ Ker(d^n) ⟶ H^n ⟶ 0` is short exact. -/
theorem shortExact_cohomologyShortComplex (n : ℤ) : (cohomologyShortComplex P n).ShortExact :=
  ⟨ShortComplex.exact_of_g_is_cokernel _
    (isCokernelOfComp _ _ (P.homologyIsCokernel ((ComplexShape.up ℤ).prev n) n rfl)
      (differentialImageToCycles_homologyπ P n)
      (factorThruImage_comp_differentialImageToCycles P n))⟩

/-- The short complex `0 ⟶ Ker(d^n) ⟶ P^n ⟶ Im(d^n) ⟶ 0`. -/
abbrev termShortComplex (n : ℤ) : ShortComplex X.Modules :=
  ShortComplex.mk (P.iCycles n) (toDifferentialImage P n) (by
    rw [← cancel_mono (differentialImageι P (n + 1))]
    simp)

/-- **A term is an extension of the image of its differential by the cycles.** The sequence
`0 ⟶ Ker(d^n) ⟶ P^n ⟶ Im(d^n) ⟶ 0` is short exact. -/
theorem shortExact_termShortComplex (n : ℤ) : (termShortComplex P n).ShortExact :=
  ⟨ShortComplex.exact_of_f_is_kernel _
    (isKernelOfComp _ _ (P.cyclesIsKernel n (n + 1) (by simp)) _
      (toDifferentialImage_comp_ι P n))⟩

end Images

/-! ### Stacks 0F8J for a bounded above complex -/

section FiniteLocallyFree

variable (P : CochainComplex X.Modules ℤ)

/-- The cycles of a complex of quasi-coherent modules are quasi-coherent. -/
theorem isQuasicoherent_cycles (n : ℤ) [(P.X n).IsQuasicoherent]
    [(P.X (n + 1)).IsQuasicoherent] : (P.cycles n).IsQuasicoherent :=
  ObjectProperty.prop_of_iso (SheafOfModules.isQuasicoherent X.ringCatSheaf)
    (IsLimit.conePointUniqueUpToIso (kernelIsKernel (P.d n (n + 1)))
      (P.cyclesIsKernel n (n + 1) (by simp)))
    (Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel (P.d n (n + 1)))

/-- **The image step of Stacks 0F8J.** If `Ker(d^n)` is finite locally free and `H^n` has Tor
dimension at most one, then `Im(d^{n-1})` is finite locally free, as the kernel of
`Ker(d^n) ⟶ H^n`. -/
theorem isFiniteLocallyFree_differentialImage [IsLocallyNoetherian X] (n : ℤ)
    (hX : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
      (P.X ((ComplexShape.up ℤ).prev n)))
    (hX' : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) (P.X n))
    (hZ : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
      (P.cycles n))
    (hH : HasTorAmplitude X.toRingedSpace
      ((DerivedCategory.singleFunctor X.Modules 0).obj (P.homology n)) (-1) 0) :
    Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
      (differentialImage P n) := by
  have := isQuasicoherent_of_stacks hX
  have := isQuasicoherent_of_stacks hX'
  have : (differentialImage P n).IsQuasicoherent := isQuasicoherent_image _
  exact isFiniteLocallyFree_of_shortExact_of_isLocallyNoetherian _
    (shortExact_cohomologyShortComplex P n) hZ hH

/-- **The kernel step of Stacks 0F8J.** If `P^n` and `Im(d^n)` are finite locally free, then so
is `Ker(d^n)`, as the kernel of the surjection `P^n ⟶ Im(d^n)`. -/
theorem isFiniteLocallyFree_cycles [IsLocallyNoetherian X] (n : ℤ)
    (hX : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) (P.X n))
    (hX' : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
      (P.X (n + 1)))
    (hB : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
      (differentialImage P (n + 1))) :
    Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
      (P.cycles n) := by
  have := isQuasicoherent_of_stacks hX
  have := isQuasicoherent_of_stacks hX'
  have := isQuasicoherent_cycles P n
  exact isFiniteLocallyFree_of_shortExact_of_isLocallyNoetherian _
    (shortExact_termShortComplex P n) hX
    (FlatOpcycles.hasTorAmplitude_mono.{u, u + 1}
      (hasTorAmplitude_singleFunctor_of_isFiniteLocallyFree X _ hB)
      (show (-1 : ℤ) ≤ 0 by omega) le_rfl)

/-- For a bounded above complex of finite locally free modules on a locally Noetherian scheme
whose cohomology modules have Tor dimension at most one, every kernel `Ker(d^n)` is finite
locally free. -/
private theorem isFiniteLocallyFree_cycles_of_bounded_above [IsLocallyNoetherian X]
    (hP : ∀ n, Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
      (P.X n))
    (N : ℤ) (htop : ∀ n, N < n → IsZero (P.X n))
    (hH : ∀ n, HasTorAmplitude X.toRingedSpace
      ((DerivedCategory.singleFunctor X.Modules 0).obj (P.homology n)) (-1) 0) (n : ℤ) :
    Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
      (P.cycles n) := by
  have key : ∀ m : ℕ, Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u}
      (R := X.ringCatSheaf) (P.cycles (N + 1 - m)) := by
    intro m
    induction m with
    | zero =>
      exact Stacks.Perfect.BoundedLocallyFreeComplexes.finiteLocallyFree_of_isZero X _
        ((htop _ (by omega)).of_mono (P.iCycles _))
    | succ m ih =>
      have e : N + 1 - ((m + 1 : ℕ) : ℤ) + 1 = N + 1 - m := by omega
      have hB := isFiniteLocallyFree_differentialImage P (N + 1 - m) (hP _) (hP _) ih (hH _)
      rw [← e] at hB
      exact isFiniteLocallyFree_cycles P _ (hP _) (hP _) hB
  by_cases hn : n ≤ N + 1
  · have := key (N + 1 - n).toNat
    rwa [show N + 1 - ((N + 1 - n).toNat : ℤ) = n by omega] at this
  · exact Stacks.Perfect.BoundedLocallyFreeComplexes.finiteLocallyFree_of_isZero X _
      ((htop _ (by omega)).of_mono (P.iCycles _))

/-- **Stacks 0F8J, for a bounded above complex on a locally Noetherian scheme.** Let `P` be a
complex of finite locally free modules whose terms vanish above the degree `N`, and whose
cohomology modules all have Tor dimension at most one. Then every kernel `Ker(d^n)` and every
image `Im(d^{n-1})` is finite locally free. The proof is the source's descending induction. -/
theorem isFiniteLocallyFree_cycles_and_differentialImage [IsLocallyNoetherian X]
    (hP : ∀ n, Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
      (P.X n))
    (N : ℤ) (htop : ∀ n, N < n → IsZero (P.X n))
    (hH : ∀ n, HasTorAmplitude X.toRingedSpace
      ((DerivedCategory.singleFunctor X.Modules 0).obj (P.homology n)) (-1) 0) (n : ℤ) :
    Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) (P.cycles n) ∧
      Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
        (differentialImage P n) :=
  ⟨isFiniteLocallyFree_cycles_of_bounded_above P hP N htop hH n,
    isFiniteLocallyFree_differentialImage P n (hP _) (hP _)
      (isFiniteLocallyFree_cycles_of_bounded_above P hP N htop hH n) (hH n)⟩

end FiniteLocallyFree

/-! ### The splitting of a bounded complex -/

/-- **The degreewise splitting of Stacks 0F8J.** For a complex `P` of finite locally free modules
on a locally Noetherian scheme, with terms vanishing outside the degrees `a, …, a + k` and
cohomology modules of Tor dimension at most one, the kernels `Ker(d^n)` and images
`Im(d^{n-1})` with their degreewise short exact sequences, as a
`Stacks.Chow.BoundedComplexSplitting`. -/
def boundedComplexSplitting [IsLocallyNoetherian X] (P : CochainComplex X.Modules ℤ) (a : ℤ)
    (k : ℕ)
    (hP : ∀ n, Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
      (P.X n))
    (hvanish : ∀ n, (n < a ∨ a + (k : ℤ) < n) → IsZero (P.X n))
    (hH : ∀ n, HasTorAmplitude X.toRingedSpace
      ((DerivedCategory.singleFunctor X.Modules 0).obj (P.homology n)) (-1) 0) :
    BoundedComplexSplitting X P a k where
  cocycles n := P.cycles n
  coboundaries n := differentialImage P n
  isFiniteLocallyFree_X := hP
  isFiniteLocallyFree_cocycles n :=
    (isFiniteLocallyFree_cycles_and_differentialImage P hP (a + k)
      (fun m hm => hvanish m (Or.inr hm)) hH n).1
  isFiniteLocallyFree_coboundaries n :=
    (isFiniteLocallyFree_cycles_and_differentialImage P hP (a + k)
      (fun m hm => hvanish m (Or.inr hm)) hH n).2
  cocyclesι n := P.iCycles n
  toCoboundaries n := toDifferentialImage P n
  coboundariesι n := differentialImageι P n
  mono_cocyclesι n := inferInstance
  epi_toCoboundaries n := inferInstance
  mono_coboundariesι n := inferInstance
  cocyclesι_comp_toCoboundaries n := (termShortComplex P n).zero
  exact n := (shortExact_termShortComplex P n).exact
  toCoboundaries_comp_coboundariesι n := toDifferentialImage_comp_ι P n
  isZero_coboundaries_bot :=
    (hvanish _ (Or.inl (by rw [CochainComplex.prev]; omega))).of_epi
      (factorThruImage (P.d ((ComplexShape.up ℤ).prev a) a))
  isZero_coboundaries_top :=
    (hvanish _ (Or.inr (by omega))).of_mono (differentialImageι P (a + k + 1))

/-! ### Schanuel's lemma -/

section Schanuel

variable {C : Type*} [Category C] [Abelian C]

/-- **The defining sequence of the Schanuel module.** For `π : Z ⟶ H` an epimorphism and any
`π' : Z' ⟶ H`, the sequence `0 ⟶ Z ×_H Z' ⟶ Z ⊞ Z' ⟶ H ⟶ 0`, the second map being `(π, -π')`,
is short exact. -/
theorem shortExact_pullbackToBiproduct {Z Z' H : C} (π : Z ⟶ H) (π' : Z' ⟶ H) [Epi π] :
    (ShortComplex.mk (Abelian.PullbackToBiproductIsKernel.pullbackToBiproduct π π')
      (biprod.desc π (-π'))
      (Abelian.PullbackToBiproductIsKernel.pullbackToBiproductFork π π').condition).ShortExact :=
  have : Epi (biprod.desc π (-π')) := epi_of_epi_fac (biprod.inl_desc π (-π'))
  ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_f_is_kernel _
      (Abelian.PullbackToBiproductIsKernel.isLimitPullbackToBiproduct π π'))
    (mono_of_isLimit_fork (Abelian.PullbackToBiproductIsKernel.isLimitPullbackToBiproduct π π'))
    inferInstance

end Schanuel

/-! ### Two complexes with isomorphic cohomology -/

section Comparison

/-- The cohomology modules of a complex of quasi-coherent modules are quasi-coherent. -/
theorem isQuasicoherent_homology (P : CochainComplex X.Modules ℤ) (n : ℤ)
    [(P.X ((ComplexShape.up ℤ).prev n)).IsQuasicoherent] [(P.cycles n).IsQuasicoherent] :
    (P.homology n).IsQuasicoherent :=
  ObjectProperty.prop_of_iso (SheafOfModules.isQuasicoherent X.ringCatSheaf)
    (IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel _)
      (P.homologyIsCokernel ((ComplexShape.up ℤ).prev n) n rfl))
    (Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel
      (P.toCycles ((ComplexShape.up ℤ).prev n) n))

/-- The presentation `0 ⟶ Im(d^{n-1}) ⟶ Ker(d^n) ⟶ H ⟶ 0` of a module `H` isomorphic to the
`n`-th cohomology module of `Q`, through an isomorphism `e : H^n(Q) ≅ H`. -/
abbrev cohomologyShortComplexOfIso (Q : CochainComplex X.Modules ℤ) (n : ℤ) {H : X.Modules}
    (e : Q.homology n ≅ H) : ShortComplex X.Modules :=
  ShortComplex.mk (differentialImageToCycles Q n) (Q.homologyπ n ≫ e.hom) (by simp)

/-- The presentation `0 ⟶ Im(d^{n-1}) ⟶ Ker(d^n) ⟶ H ⟶ 0` through an isomorphism
`H^n(Q) ≅ H` is short exact. -/
theorem shortExact_cohomologyShortComplexOfIso (Q : CochainComplex X.Modules ℤ) (n : ℤ)
    {H : X.Modules} (e : Q.homology n ≅ H) : (cohomologyShortComplexOfIso Q n e).ShortExact :=
  ShortComplex.shortExact_of_iso
    (ShortComplex.isoMk (S₁ := cohomologyShortComplex Q n) (S₂ := cohomologyShortComplexOfIso Q n e)
      (Iso.refl _) (Iso.refl _) e (by simp) (by simp))
    (shortExact_cohomologyShortComplex Q n)

/-- **The Schanuel module** of the two presentations `0 ⟶ B_P ⟶ Z_P ⟶ H ⟶ 0` and
`0 ⟶ B_Q ⟶ Z_Q ⟶ H ⟶ 0` of one cohomology module: the fibre product `Z_P ×_H Z_Q`, which is the
kernel of `Z_P ⊞ Z_Q ⟶ H`. -/
abbrev schanuelModule (P Q : CochainComplex X.Modules ℤ) (n : ℤ)
    (e : Q.homology n ≅ P.homology n) : X.Modules :=
  pullback (P.homologyπ n) (Q.homologyπ n ≫ e.hom)

/-- **Schanuel's lemma, Stacks 00O3, for finite locally free modules on a locally Noetherian
scheme.** If the cycles of `P` and `Q` in degree `n` are finite locally free and the cohomology
module has Tor dimension at most one, the Schanuel module `Z_P ×_H Z_Q` is finite locally free. -/
theorem isFiniteLocallyFree_schanuelModule [IsLocallyNoetherian X]
    (P Q : CochainComplex X.Modules ℤ) (n : ℤ) (e : Q.homology n ≅ P.homology n)
    (hXP : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
      (P.X ((ComplexShape.up ℤ).prev n)))
    (hZP : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
      (P.cycles n))
    (hZQ : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
      (Q.cycles n))
    (hH : HasTorAmplitude X.toRingedSpace
      ((DerivedCategory.singleFunctor X.Modules 0).obj (P.homology n)) (-1) 0) :
    Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
      (schanuelModule P Q n e) := by
  have := isQuasicoherent_of_stacks hXP
  have := isQuasicoherent_of_stacks hZP
  have := isQuasicoherent_of_stacks hZQ
  have := isQuasicoherent_homology P n
  have hsum : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
      (ShortComplex.mk (Abelian.PullbackToBiproductIsKernel.pullbackToBiproduct (P.homologyπ n)
        (Q.homologyπ n ≫ e.hom)) (biprod.desc (P.homologyπ n) (-(Q.homologyπ n ≫ e.hom)))
        (Abelian.PullbackToBiproductIsKernel.pullbackToBiproductFork (P.homologyπ n)
          (Q.homologyπ n ≫ e.hom)).condition).X₂ :=
    SheafOfModules.isFiniteLocallyFree_biprod (P.cycles n) (Q.cycles n)
  have := isQuasicoherent_of_stacks hsum
  have iso := IsLimit.conePointUniqueUpToIso (kernelIsKernel _)
    (Abelian.PullbackToBiproductIsKernel.isLimitPullbackToBiproduct (P.homologyπ n)
      (Q.homologyπ n ≫ e.hom))
  have : (schanuelModule P Q n e).IsQuasicoherent :=
    ObjectProperty.prop_of_iso (SheafOfModules.isQuasicoherent X.ringCatSheaf) iso
      (Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel _)
  exact isFiniteLocallyFree_of_shortExact_of_isLocallyNoetherian _
    (shortExact_pullbackToBiproduct (P.homologyπ n) (Q.homologyπ n ≫ e.hom)) hsum hH

/-- The first Schanuel sequence `0 ⟶ B^n_P ⟶ Z^n_P ×_{H^n} Z^n_Q ⟶ Z^n_Q ⟶ 0`. -/
abbrev schanuelShortComplexFirst (P Q : CochainComplex X.Modules ℤ) (n : ℤ)
    (e : Q.homology n ≅ P.homology n) : ShortComplex X.Modules :=
  ShortComplex.mk
    (pullback.lift (differentialImageToCycles P n) 0 (by simp) :
      differentialImage P n ⟶ schanuelModule P Q n e)
    (pullback.snd _ _) (pullback.lift_snd _ _ _)

/-- The first Schanuel sequence is short exact: the kernel of the second projection of
`Z^n_P ×_{H^n} Z^n_Q` is the kernel `B^n_P` of `Z^n_P ⟶ H^n`. -/
theorem shortExact_schanuelShortComplexFirst (P Q : CochainComplex X.Modules ℤ) (n : ℤ)
    (e : Q.homology n ≅ P.homology n) : (schanuelShortComplexFirst P Q n e).ShortExact :=
  (shortExact_cohomologyShortComplex P n).shortExact_pullbackSnd (Q.homologyπ n ≫ e.hom)

/-- The second Schanuel sequence `0 ⟶ B^n_Q ⟶ Z^n_P ×_{H^n} Z^n_Q ⟶ Z^n_P ⟶ 0`. -/
abbrev schanuelShortComplexSecond (P Q : CochainComplex X.Modules ℤ) (n : ℤ)
    (e : Q.homology n ≅ P.homology n) : ShortComplex X.Modules :=
  ShortComplex.mk
    (pullback.lift 0 (differentialImageToCycles Q n) (by simp) :
      differentialImage Q n ⟶ schanuelModule P Q n e)
    (pullback.fst _ _) (pullback.lift_fst _ _ _)

/-- The second Schanuel sequence is short exact: the kernel of the first projection of
`Z^n_P ×_{H^n} Z^n_Q` is the kernel `B^n_Q` of `Z^n_Q ⟶ H^n`. -/
theorem shortExact_schanuelShortComplexSecond (P Q : CochainComplex X.Modules ℤ) (n : ℤ)
    (e : Q.homology n ≅ P.homology n) : (schanuelShortComplexSecond P Q n e).ShortExact :=
  Abelian.shortExact_pullback (shortExact_cohomologyShortComplexOfIso Q n e) (P.homologyπ n)

/-- **The comparison datum of two complexes with isomorphic cohomology.** For complexes `P` and
`Q` of finite locally free modules on a locally Noetherian scheme, with terms vanishing outside
the degrees `a, …, a + k`, cohomology modules of Tor dimension at most one, and isomorphisms
`H^n(Q) ≅ H^n(P)`, the presentations `0 ⟶ B^n ⟶ Z^n ⟶ H^n ⟶ 0` of the cohomology modules and
the Schanuel modules `Z^n_P ×_{H^n} Z^n_Q` with their two short exact sequences, as a
`Stacks.Chow.ComplexCohomologyComparison`. -/
def complexCohomologyComparison [IsLocallyNoetherian X] (P Q : CochainComplex X.Modules ℤ)
    (a : ℤ) (k : ℕ)
    (hP : ∀ n, Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
      (P.X n))
    (hQ : ∀ n, Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
      (Q.X n))
    (hvanishP : ∀ n, (n < a ∨ a + (k : ℤ) < n) → IsZero (P.X n))
    (hvanishQ : ∀ n, (n < a ∨ a + (k : ℤ) < n) → IsZero (Q.X n))
    (hHP : ∀ n, HasTorAmplitude X.toRingedSpace
      ((DerivedCategory.singleFunctor X.Modules 0).obj (P.homology n)) (-1) 0)
    (hHQ : ∀ n, HasTorAmplitude X.toRingedSpace
      ((DerivedCategory.singleFunctor X.Modules 0).obj (Q.homology n)) (-1) 0)
    (e : ∀ n, Q.homology n ≅ P.homology n) :
    ComplexCohomologyComparison (boundedComplexSplitting P a k hP hvanishP hHP)
      (boundedComplexSplitting Q a k hQ hvanishQ hHQ) where
  cohomology n := P.homology n
  firstCoboundariesι n := differentialImageToCycles P n
  firstCoboundariesι_comp n := differentialImageToCycles_iCycles P n
  firstπ n := P.homologyπ n
  firstw n := differentialImageToCycles_homologyπ P n
  mono_firstCoboundariesι n := inferInstanceAs (Mono (differentialImageToCycles P n))
  epi_firstπ n := inferInstanceAs (Epi (P.homologyπ n))
  firstExact n := (shortExact_cohomologyShortComplex P n).exact
  secondCoboundariesι n := differentialImageToCycles Q n
  secondCoboundariesι_comp n := differentialImageToCycles_iCycles Q n
  secondπ n := Q.homologyπ n ≫ (e n).hom
  secondw n := (cohomologyShortComplexOfIso Q n (e n)).zero
  mono_secondCoboundariesι n := inferInstanceAs (Mono (differentialImageToCycles Q n))
  epi_secondπ n := inferInstanceAs (Epi (Q.homologyπ n ≫ (e n).hom))
  secondExact n := (shortExact_cohomologyShortComplexOfIso Q n (e n)).exact
  schanuel n := schanuelModule P Q n (e n)
  isFiniteLocallyFree_schanuel n :=
    isFiniteLocallyFree_schanuelModule P Q n (e n) (hP _)
      (isFiniteLocallyFree_cycles_and_differentialImage P hP (a + k)
        (fun m hm => hvanishP m (Or.inr hm)) hHP n).1
      (isFiniteLocallyFree_cycles_and_differentialImage Q hQ (a + k)
        (fun m hm => hvanishQ m (Or.inr hm)) hHQ n).1 (hHP n)
  firstSchanuelι n := (schanuelShortComplexFirst P Q n (e n)).f
  firstSchanuelπ n := (schanuelShortComplexFirst P Q n (e n)).g
  firstSchanuelw n := (schanuelShortComplexFirst P Q n (e n)).zero
  mono_firstSchanuelι n := (shortExact_schanuelShortComplexFirst P Q n (e n)).mono_f
  epi_firstSchanuelπ n := (shortExact_schanuelShortComplexFirst P Q n (e n)).epi_g
  firstSchanuelExact n := (shortExact_schanuelShortComplexFirst P Q n (e n)).exact
  secondSchanuelι n := (schanuelShortComplexSecond P Q n (e n)).f
  secondSchanuelπ n := (schanuelShortComplexSecond P Q n (e n)).g
  secondSchanuelw n := (schanuelShortComplexSecond P Q n (e n)).zero
  mono_secondSchanuelι n := (shortExact_schanuelShortComplexSecond P Q n (e n)).mono_f
  epi_secondSchanuelπ n := (shortExact_schanuelShortComplexSecond P Q n (e n)).epi_g
  secondSchanuelExact n := (shortExact_schanuelShortComplexSecond P Q n (e n)).exact

end Comparison

/-! ### The alternating class depends only on the derived object -/

/-- **The alternating class `∑_n (-1)^n [ℰ^n]` in `K_0(Vect(X))` of a bounded complex of finite
locally free modules depends only on the object of `D(𝒪_X)` it represents**, when the cohomology
modules of that object are perfect of Tor dimension at most one. This is the algebraic heart of
the proof of Stacks 0ESZ (its last two paragraphs): by Stacks 0F8J the kernels and images of the
differentials of both complexes are finite locally free, and Schanuel's lemma, Stacks 00O3,
compares the two presentations `0 ⟶ Im(d^{n-1}) ⟶ Ker(d^n) ⟶ H^n(E) ⟶ 0`.

The scheme is locally Noetherian, as is every scheme locally of finite type over the base of
Situation 02QL. -/
theorem alternatingKClass_eq_of_iso_derivedCategory [IsLocallyNoetherian X]
    (P Q : CochainComplex X.Modules ℤ) (a : ℤ) (k : ℕ)
    (hP : ∀ n, Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
      (P.X n))
    (hQ : ∀ n, Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
      (Q.X n))
    (hvanishP : ∀ n, (n < a ∨ a + (k : ℤ) < n) → IsZero (P.X n))
    (hvanishQ : ∀ n, (n < a ∨ a + (k : ℤ) < n) → IsZero (Q.X n))
    (E : DerivedCategory X.Modules) (hPE : Nonempty (E ≅ DerivedCategory.Q.obj P))
    (hQE : Nonempty (E ≅ DerivedCategory.Q.obj Q))
    (hE : ∀ i : ℤ,
      IsPerfect.{u, u, u + 1} ((DerivedCategory.singleFunctor X.Modules 0).obj
        ((DerivedCategory.homologyFunctor X.Modules i).obj E)) ∧
      HasTorAmplitude X.toRingedSpace ((DerivedCategory.singleFunctor X.Modules 0).obj
        ((DerivedCategory.homologyFunctor X.Modules i).obj E)) (-1) 0) :
    alternatingKClass X P a k = alternatingKClass X Q a k := by
  obtain ⟨eP⟩ := hPE
  obtain ⟨eQ⟩ := hQE
  let iso : ∀ R : CochainComplex X.Modules ℤ, (E ≅ DerivedCategory.Q.obj R) → ∀ n,
      R.homology n ≅ (DerivedCategory.homologyFunctor X.Modules n).obj E := fun R eR n =>
    ((DerivedCategory.homologyFunctorFactors X.Modules n).app R).symm ≪≫
      (DerivedCategory.homologyFunctor X.Modules n).mapIso eR.symm
  have hH : ∀ R (eR : E ≅ DerivedCategory.Q.obj R) n, HasTorAmplitude X.toRingedSpace
      ((DerivedCategory.singleFunctor X.Modules 0).obj (R.homology n)) (-1) 0 := fun R eR n =>
    FlatOpcycles.hasTorAmplitude_of_iso.{u, u + 1} (hE n).2
      ((DerivedCategory.singleFunctor X.Modules 0).mapIso (iso R eR n))
  exact alternatingKClass_eq_of_cohomologyComparison _ _
    (complexCohomologyComparison P Q a k hP hQ hvanishP hvanishQ (hH P eP) (hH Q eQ)
      fun n => iso Q eQ n ≪≫ (iso P eP n).symm)

end Stacks.Chow
