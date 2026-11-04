module

public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.Topology.Constructible.IrreducibleMeet

/-!
# A finite-presentation morphism whose image of a locally closed set is not constructible

Chevalley's theorem fails for locally closed subsets: there is a morphism of finite
presentation between affine schemes and a locally closed subset of the source whose image is not
a finite union of locally closed subsets of the target.

The example is the projection `Spec B[T] → Spec B` for
`B = ℚ[x₀, y₀, x₁, y₁, …]`. In the source one cuts out the closed set where
`xᵢ · ∏_{j ≤ i} (T - (j+1))` vanishes for every `i`, and intersects it with the open set where
some `yₙ · ∏_{j ≤ n} (T - (j+1))` is invertible. The image is the set of primes of `B` that
contain `x₀, …, xₙ` but not `yₙ`, for some `n`. If that set were covered by `m` locally closed
subsets, the shift endomorphism `xᵢ ↦ x_{i-1}`, `yᵢ ↦ y_{i-1}` (with the index-`0` variables
sent to `0`) would pull the cover back to one with `m - 1` members, and induction on `m` gives a
contradiction.

## Main results

* `Stacks.Examples.exists_affine_finitePresentation_image_not_finiteUnionLocallyClosed`: the
  counterexample.

## Implementation notes

The image is taken under the map of underlying topological spaces of the scheme morphism, and
`IsFiniteUnionLocallyClosed` is the finiteness property negated in the source. The base field is
`ULift ℚ` so that the schemes live in a prescribed universe.

## References

* [Stacks Project, Tag 0GZM](https://stacks.math.columbia.edu/tag/0GZM)
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Examples

private instance : NoZeroDivisors (ULift.{u} ℚ) where
  eq_zero_or_eq_zero_of_mul_eq_zero := by
    intro a b hab
    have h : a.down * b.down = 0 := congrArg ULift.down hab
    rcases mul_eq_zero.mp h with ha | hb
    · exact Or.inl (ULift.down_injective ha)
    · exact Or.inr (ULift.down_injective hb)

private instance : IsDomain (ULift.{u} ℚ) := by
  let : IsCancelMulZero (ULift.{u} ℚ) :=
    (isCancelMulZero_iff_noZeroDivisors).2 inferInstance
  exact IsDomain.mk

/-- The base ring `ℚ[x₀, y₀, x₁, y₁, …]` of the counterexample. -/
abbrev ChevalleyBaseRing : Type u := MvPolynomial (ℕ × Bool) (ULift.{u} ℚ)

/-- The coordinate ring `ℚ[x₀, y₀, …][T]` of the source of the counterexample. -/
abbrev ChevalleyTotalRing : Type u := Polynomial ChevalleyBaseRing

private instance : IsDomain ChevalleyBaseRing := by
  let : IsCancelMulZero ChevalleyBaseRing :=
    (isCancelMulZero_iff_noZeroDivisors).2 inferInstance
  exact IsDomain.mk

private def xCoord (i : ℕ) : ChevalleyBaseRing := MvPolynomial.X (i, false)

private def yCoord (i : ℕ) : ChevalleyBaseRing := MvPolynomial.X (i, true)

private def rootFactors (n : ℕ) : Polynomial ChevalleyBaseRing :=
  ∏ i ∈ Finset.range (n + 1), (Polynomial.X - Polynomial.C (i + 1 : ChevalleyBaseRing))

private def equation (i : ℕ) : ChevalleyTotalRing :=
  Polynomial.C (xCoord i) * rootFactors i

private def closedPart : Set (PrimeSpectrum ChevalleyTotalRing) :=
  PrimeSpectrum.zeroLocus (Set.range equation)

private def openPiece (n : ℕ) : Set (PrimeSpectrum ChevalleyTotalRing) :=
  PrimeSpectrum.basicOpen (Polynomial.C (yCoord n) * rootFactors n)

private def openPart : Set (PrimeSpectrum ChevalleyTotalRing) := ⋃ n, openPiece n

private def locallyClosedPart : Set (PrimeSpectrum ChevalleyTotalRing) := closedPart ∩ openPart

private def imageSet : Set (PrimeSpectrum ChevalleyBaseRing) :=
  {p | ∃ n, (∀ i ≤ n, xCoord i ∈ p.asIdeal) ∧ yCoord n ∉ p.asIdeal}

private def closureOfImage : Set (PrimeSpectrum ChevalleyBaseRing) :=
  PrimeSpectrum.zeroLocus ({xCoord 0} : Set ChevalleyBaseRing)

private def closureGeneric : PrimeSpectrum ChevalleyBaseRing :=
  ⟨Ideal.span {xCoord 0}, by
    have hp : Prime (xCoord 0) :=
      MvPolynomial.X_prime (R := ULift.{u} ℚ) (i := (0, false))
    exact (Ideal.span_singleton_prime hp.ne_zero).mpr hp⟩

private theorem closureGeneric_generic : IsGenericPoint closureGeneric closureOfImage := by
  change closure ({closureGeneric} : Set (PrimeSpectrum ChevalleyBaseRing)) = closureOfImage
  rw [PrimeSpectrum.closure_singleton]
  simp [closureGeneric, closureOfImage]

private theorem closureGeneric_mem_imageSet : closureGeneric.{u} ∈ imageSet.{u} := by
  refine ⟨0, ?_, ?_⟩
  · intro i hi
    obtain rfl : i = 0 := by omega
    simp [closureGeneric, xCoord]
  · intro hy
    have hy' : yCoord.{u} 0 ∈ Ideal.span {xCoord.{u} 0} := by
      simpa [closureGeneric] using hy
    obtain ⟨a, ha⟩ := (Ideal.mem_span_singleton' (x := yCoord.{u} 0)
      (y := xCoord.{u} 0)).mp hy'
    let e : ChevalleyBaseRing.{u} →+* ULift.{u} ℚ :=
      (MvPolynomial.aeval (R := ULift.{u} ℚ) fun ij : ℕ × Bool =>
        if ij = (0, false) then 0 else if ij = (0, true) then 1 else 0).toRingHom
    have h := congrArg e ha
    rw [map_mul, show e (xCoord 0) = 0 by simp [e, xCoord], mul_zero,
      show e (yCoord 0) = 1 by simp [e, yCoord]] at h
    norm_num at h

private def shiftHom : ChevalleyBaseRing →+* ChevalleyBaseRing :=
  (MvPolynomial.aeval fun ij : ℕ × Bool =>
    if ij.1 = 0 then 0 else MvPolynomial.X (ij.1 - 1, ij.2)).toRingHom

private def raiseHom : ChevalleyBaseRing →+* ChevalleyBaseRing :=
  (MvPolynomial.aeval fun ij : ℕ × Bool => MvPolynomial.X (ij.1 + 1, ij.2)).toRingHom

private theorem shiftHom_comp_raiseHom : shiftHom.comp raiseHom = RingHom.id _ := by
  refine MvPolynomial.ringHom_ext (fun r => ?_) fun ⟨i, b⟩ => ?_ <;> simp [shiftHom, raiseHom]

private theorem shiftHom_surjective : Function.Surjective shiftHom := fun r =>
  ⟨raiseHom r, congrFun (congrArg DFunLike.coe shiftHom_comp_raiseHom) r⟩

private def shiftPoint (p : PrimeSpectrum ChevalleyBaseRing) :
    PrimeSpectrum ChevalleyBaseRing := PrimeSpectrum.comap shiftHom p

private def shiftGeneric : PrimeSpectrum ChevalleyBaseRing :=
  ⟨RingHom.ker shiftHom, RingHom.ker_isPrime shiftHom⟩

private theorem shiftPoint_range :
    Set.range shiftPoint = PrimeSpectrum.zeroLocus (RingHom.ker shiftHom) :=
  range_comap_of_surjective _ _ shiftHom_surjective

private theorem shiftGeneric_generic : IsGenericPoint shiftGeneric (Set.range shiftPoint) := by
  change closure ({shiftGeneric} : Set (PrimeSpectrum ChevalleyBaseRing)) = _
  rw [PrimeSpectrum.closure_singleton, shiftPoint_range]
  rfl

private theorem shiftGeneric_mem_closureOfImage : shiftGeneric ∈ closureOfImage := by
  rw [closureOfImage, PrimeSpectrum.mem_zeroLocus]
  rintro x rfl
  change xCoord 0 ∈ RingHom.ker shiftHom
  simp [RingHom.mem_ker, shiftHom, xCoord]

private theorem closureOfImage_isIrreducible : IsIrreducible closureOfImage := by
  rw [← closureGeneric_generic]
  exact isIrreducible_singleton.closure

private theorem imageSet_subset_closureOfImage : imageSet ⊆ closureOfImage := by
  rintro p ⟨n, hx, hy⟩
  rw [closureOfImage, PrimeSpectrum.mem_zeroLocus]
  rintro x rfl
  exact hx 0 (Nat.zero_le n)

private theorem closureOfImage_subset_closure_imageSet :
    closureOfImage ⊆ closure imageSet := by
  rw [← closureGeneric_generic]
  exact closure_mono (by simpa using closureGeneric_mem_imageSet)

private theorem imageSet_closure : closure imageSet = closureOfImage :=
  le_antisymm (closure_minimal imageSet_subset_closureOfImage (PrimeSpectrum.isClosed_zeroLocus _))
    closureOfImage_subset_closure_imageSet

private theorem shiftGeneric_notMem_imageSet : shiftGeneric ∉ imageSet := by
  rintro ⟨n, hx, hy⟩
  by_cases hn : n = 0
  · subst n
    apply hy
    change shiftHom (yCoord 0) = 0
    simp [shiftHom, yCoord]
  · have hx1_not : xCoord 1 ∉ shiftGeneric.asIdeal := by
      change shiftHom (xCoord 1) ≠ 0
      simp [shiftHom, xCoord, MvPolynomial.X_ne_zero]
    exact hx1_not (hx 1 (by omega))

/-- The shift sends the index-`0` variables into every prime. -/
private theorem X_zero_mem_shiftPoint (b : Bool) (p : PrimeSpectrum ChevalleyBaseRing) :
    (MvPolynomial.X (0, b) : ChevalleyBaseRing) ∈ (shiftPoint p).asIdeal := by
  simp [shiftPoint, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, shiftHom]

/-- A variable of positive index lies in `shiftPoint p` iff its shifted variable lies in `p`. -/
private theorem X_succ_mem_shiftPoint (b : Bool) (i : ℕ) (p : PrimeSpectrum ChevalleyBaseRing) :
    (MvPolynomial.X (i + 1, b) : ChevalleyBaseRing) ∈ (shiftPoint p).asIdeal ↔
      (MvPolynomial.X (i, b) : ChevalleyBaseRing) ∈ p.asIdeal := by
  simp [shiftPoint, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, shiftHom]

private theorem shiftPoint_mem_imageSet (p : PrimeSpectrum ChevalleyBaseRing) :
    p ∈ imageSet ↔ shiftPoint p ∈ imageSet := by
  constructor
  · rintro ⟨n, hx, hy⟩
    refine ⟨n + 1, fun i hi => ?_, (X_succ_mem_shiftPoint true n p).not.2 hy⟩
    cases i with
    | zero => exact X_zero_mem_shiftPoint false p
    | succ i => exact (X_succ_mem_shiftPoint false i p).2 (hx i (by omega))
  · rintro ⟨_ | n, hx, hy⟩
    · exact (hy (X_zero_mem_shiftPoint true p)).elim
    · exact ⟨n, fun i hi => (X_succ_mem_shiftPoint false i p).1 (hx (i + 1) (by omega)),
        (X_succ_mem_shiftPoint true n p).not.1 hy⟩

private theorem natDifference_isUnit (n k : ℕ) (hk : k ≤ n) :
    IsUnit ((n + 2 : ChevalleyBaseRing.{u}) - (k + 1 : ChevalleyBaseRing.{u})) := by
  let d := n - k + 1
  have hd : 0 < d := Nat.succ_pos _
  have hdn : (d : ULift.{u} ℚ) ≠ 0 := by
    intro h
    have h' : (d : ℚ) = 0 := by simpa using congrArg ULift.down h
    exact (Nat.ne_of_gt hd) (by exact_mod_cast h')
  have hcast : (n : ChevalleyBaseRing.{u}) + 2 = (k : ChevalleyBaseRing.{u}) + 1 + d := by
    have hNat : n + 2 = k + 1 + d := by dsimp [d]; omega
    calc
      (n : ChevalleyBaseRing.{u}) + 2 = ((n + 2 : ℕ) : ChevalleyBaseRing.{u}) := by simp
      _ = ((k + 1 + d : ℕ) : ChevalleyBaseRing.{u}) :=
        congrArg (fun m : ℕ => (m : ChevalleyBaseRing.{u})) hNat
      _ = (k : ChevalleyBaseRing.{u}) + 1 + d := by simp [Nat.cast_add]
  have heq : ((n : ChevalleyBaseRing.{u}) + 2) - ((k : ChevalleyBaseRing.{u}) + 1) =
      MvPolynomial.C (d : ULift.{u} ℚ) := by
    calc
      ((n : ChevalleyBaseRing.{u}) + 2) - ((k : ChevalleyBaseRing.{u}) + 1) =
          (d : ChevalleyBaseRing.{u}) := by rw [hcast]; ring
      _ = MvPolynomial.C (d : ULift.{u} ℚ) := by simp
  exact heq.symm ▸ (isUnit_iff_ne_zero.mpr hdn).map
    (MvPolynomial.C : ULift.{u} ℚ →+* ChevalleyBaseRing.{u})

private theorem rootFactors_eval_isUnit (n : ℕ) :
    IsUnit (Polynomial.evalRingHom (n + 2 : ChevalleyBaseRing) (rootFactors n)) := by
  change IsUnit (Polynomial.eval (n + 2 : ChevalleyBaseRing) (rootFactors n))
  rw [rootFactors, Polynomial.eval_prod, IsUnit.prod_iff]
  intro i hi
  rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  exact natDifference_isUnit n i (by simpa using Finset.mem_range.mp hi)

private def baseScheme : Scheme.{u} := Spec (CommRingCat.of ChevalleyBaseRing)

private def totalScheme : Scheme.{u} := Spec (CommRingCat.of ChevalleyTotalRing)

private def polynomialAlgebraMap :
    @RingHom ChevalleyBaseRing ChevalleyTotalRing
      CommRing.toCommSemiring.toNonAssocSemiring
      (CommRing.toCommSemiring.toSemiring.toNonAssocSemiring) where
  toFun := algebraMap ChevalleyBaseRing ChevalleyTotalRing
  map_one' := by simp
  map_mul' := by simp
  map_zero' := by simp
  map_add' := by simp

private def projection : totalScheme ⟶ baseScheme :=
  Spec.map (CommRingCat.ofHom polynomialAlgebraMap)

private theorem projection_finitePresentation : FinitePresentation projection := by
  change FinitePresentation (Spec.map (CommRingCat.ofHom polynomialAlgebraMap))
  apply FinitePresentation.mk
  · rw [LocallyOfFinitePresentation.SpecMap_iff]
    exact RingHom.finitePresentation_algebraMap.mpr inferInstance
  · infer_instance
  · exact (quasiSeparated_iff_quasiSeparatedSpace _).2 inferInstance

private theorem locallyClosedPart_isLocallyClosed : IsLocallyClosed locallyClosedPart := by
  refine ⟨openPart, closedPart, isOpen_iUnion fun n => (PrimeSpectrum.basicOpen _).isOpen,
    PrimeSpectrum.isClosed_zeroLocus _, ?_⟩
  simp [locallyClosedPart, Set.inter_comm]

private theorem projection_image_subset :
    Set.image (PrimeSpectrum.comap
      (algebraMap ChevalleyBaseRing ChevalleyTotalRing)) locallyClosedPart ⊆ imageSet := by
  classical
  rintro p ⟨q, hq, rfl⟩
  have hZ : q ∈ PrimeSpectrum.zeroLocus (Set.range equation) := by
    simpa [locallyClosedPart, closedPart] using hq.1
  rcases Set.mem_iUnion.mp (by simpa [locallyClosedPart, openPart] using hq.2) with ⟨n, hn⟩
  have hopen : Polynomial.C (yCoord n) * rootFactors n ∉ q.asIdeal :=
    (PrimeSpectrum.mem_basicOpen _ _).mp hn
  have hprod : rootFactors n ∉ q.asIdeal := fun hp =>
    hopen ((q.isPrime.mul_mem_iff_mem_or_mem).2 (Or.inr hp))
  have hfactor (k : ℕ) (hk : k ∈ Finset.range (n + 1)) :
      Polynomial.X - Polynomial.C (k + 1 : ChevalleyBaseRing) ∉ q.asIdeal := fun hp =>
    hprod ((q.isPrime.prod_mem_iff).2 ⟨k, hk, hp⟩)
  refine ⟨n, ?_, ?_⟩
  · intro i hi
    have hroot : rootFactors i ∉ q.asIdeal := by
      intro hp
      obtain ⟨k, hk, hmem⟩ := (q.isPrime.prod_mem_iff).mp hp
      exact hfactor k (Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hk)
        (Nat.succ_le_succ hi))) hmem
    have hx : Polynomial.C (xCoord i) ∈ q.asIdeal :=
      (q.isPrime.mul_mem_iff_mem_or_mem).mp ((PrimeSpectrum.mem_zeroLocus q _).mp hZ ⟨i, rfl⟩)
        |>.resolve_right hroot
    simpa [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, equation] using hx
  · exact fun hy => hopen ((q.isPrime.mul_mem_iff_mem_or_mem).2
      (Or.inl (by simpa [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] using hy)))

private theorem imageSet_subset :
    imageSet ⊆ Set.image (PrimeSpectrum.comap
      (algebraMap ChevalleyBaseRing ChevalleyTotalRing)) locallyClosedPart := by
  classical
  rintro p ⟨n, hcoords, hy⟩
  let ev : ChevalleyTotalRing →+* ChevalleyBaseRing :=
    Polynomial.evalRingHom (n + 2 : ChevalleyBaseRing)
  let q := PrimeSpectrum.comap ev p
  have heval (i : ℕ) : ev (equation i) ∈ p.asIdeal := by
    by_cases hi : i ≤ n
    · change ev (Polynomial.C (xCoord i) * rootFactors i) ∈ p.asIdeal
      simpa [ev] using p.asIdeal.mul_mem_right _ (hcoords i hi)
    · have hzero' : Polynomial.eval (n + 2 : ChevalleyBaseRing) (rootFactors i) = 0 := by
        rw [rootFactors, Polynomial.eval_prod]
        apply Finset.prod_eq_zero (i := n + 1)
        · simp only [Finset.mem_range]
          omega
        · simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
          push_cast
          ring
      change Polynomial.eval (n + 2 : ChevalleyBaseRing)
        (Polynomial.C (xCoord i) * rootFactors i) ∈ p.asIdeal
      rw [Polynomial.eval_mul, hzero', mul_zero]
      exact p.asIdeal.zero_mem
  have hqZ : q ∈ closedPart := (PrimeSpectrum.mem_zeroLocus q _).2 <| by
    rintro _ ⟨i, rfl⟩
    exact heval i
  have hqU : q ∈ openPart := by
    rw [openPart, Set.mem_iUnion]
    refine ⟨n, ?_⟩
    change q ∈ PrimeSpectrum.basicOpen (Polynomial.C (yCoord n) * rootFactors n)
    rw [PrimeSpectrum.mem_basicOpen, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
    intro hmem
    have hmem' : yCoord n *
        Polynomial.evalRingHom (n + 2 : ChevalleyBaseRing) (rootFactors n) ∈ p.asIdeal := by
      change ev (Polynomial.C (yCoord n) * rootFactors n) ∈ p.asIdeal at hmem
      simpa [ev, map_mul, Polynomial.eval_C] using hmem
    exact hy ((Ideal.mul_unit_mem_iff_mem p.asIdeal (rootFactors_eval_isUnit n)).mp hmem')
  refine ⟨q, ⟨by simpa [locallyClosedPart] using hqZ, by simpa [locallyClosedPart] using hqU⟩, ?_⟩
  rw [← PrimeSpectrum.comap_comp_apply]
  have hev : ev.comp (algebraMap ChevalleyBaseRing ChevalleyTotalRing) = RingHom.id _ :=
    MvPolynomial.ringHom_ext (fun r => by simp [ev]) fun i => by simp [ev]
  rw [hev, PrimeSpectrum.comap_id]

private theorem projection_image_eq :
    Set.image projection.base locallyClosedPart = imageSet := by
  change Set.image
    (PrimeSpectrum.comap (algebraMap ChevalleyBaseRing ChevalleyTotalRing))
      locallyClosedPart = _
  exact Set.Subset.antisymm projection_image_subset imageSet_subset

private theorem cover_size_bound (n : ℕ) :
    ∀ (m : ℕ) (L : Fin m → Set (PrimeSpectrum ChevalleyBaseRing)),
      (∀ i, IsLocallyClosed (L i)) → (⋃ i, L i) = imageSet → n ≤ m := by
  induction n with
  | zero => exact fun m _ _ _ => Nat.zero_le m
  | succ n ih =>
      intro m L hL hcover
      cases m with
      | zero =>
          have hmem : closureGeneric ∈ (⋃ i : Fin 0, L i) := hcover ▸ closureGeneric_mem_imageSet
          simp at hmem
      | succ k =>
          have hLi_subset_B (i : Fin (k + 1)) : L i ⊆ imageSet := fun p hp =>
            hcover ▸ Set.mem_iUnion.mpr ⟨i, hp⟩
          have hHsub : closureOfImage ⊆ ⋃ i, closure (L i) := by
            rw [← imageSet_closure]
            refine closure_minimal ?_ (isClosed_iUnion_of_finite fun i => isClosed_closure)
            intro p hp
            rcases Set.mem_iUnion.mp (hcover ▸ hp) with ⟨i, hi⟩
            exact Set.mem_iUnion.mpr ⟨i, subset_closure hi⟩
          obtain ⟨i₀, hHtoLi⟩ :=
            irreducible_subset_finite_iUnion_closed closureOfImage_isIrreducible
              (fun i : Fin (k + 1) => closure (L i)) (fun _ => isClosed_closure) hHsub
          obtain ⟨U, C, hU, hC, hLiEq⟩ := hL i₀
          have hH_subset_C : closureOfImage ⊆ C :=
            hHtoLi.trans (closure_minimal (by rw [hLiEq]; exact Set.inter_subset_right) hC)
          have hAvoid (p : PrimeSpectrum ChevalleyBaseRing) : shiftPoint p ∉ L i₀ := by
            intro hpLi
            rw [hLiEq] at hpLi
            have hgenericClosure : shiftPoint p ∈ closure {shiftGeneric} := by
              rw [shiftGeneric_generic]
              exact ⟨p, rfl⟩
            have hqU : shiftGeneric ∈ U := by
              simpa using (mem_closure_iff.mp hgenericClosure) U hU hpLi.1
            have hqC : shiftGeneric ∈ C := hH_subset_C shiftGeneric_mem_closureOfImage
            exact shiftGeneric_notMem_imageSet (hLi_subset_B i₀ (by
              rw [hLiEq]
              exact ⟨hqU, hqC⟩))
          let L' (j : Fin k) : Set (PrimeSpectrum ChevalleyBaseRing) :=
            closureOfImage ∩ shiftPoint ⁻¹' L (i₀.succAbove j)
          have hL' (j : Fin k) : IsLocallyClosed (L' j) :=
            IsLocallyClosed.inter
              (⟨Set.univ, closureOfImage, isOpen_univ,
                PrimeSpectrum.isClosed_zeroLocus _, by simp⟩ :
                IsLocallyClosed closureOfImage)
              ((hL (i₀.succAbove j)).preimage (PrimeSpectrum.continuous_comap shiftHom))
          have hcover' : (⋃ j, L' j) = imageSet := by
            refine Set.Subset.antisymm (fun p hp => ?_) fun p hp => ?_
            · rcases Set.mem_iUnion.mp hp with ⟨j, _, hpL⟩
              exact (shiftPoint_mem_imageSet p).2 (hLi_subset_B (i₀.succAbove j) hpL)
            · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp
                (hcover ▸ (shiftPoint_mem_imageSet p).1 hp : shiftPoint p ∈ ⋃ i, L i)
              obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq fun h : i = i₀ => hAvoid p (h ▸ hi)
              exact Set.mem_iUnion.mpr ⟨j, ⟨imageSet_subset_closureOfImage hp,
                show shiftPoint p ∈ L (i₀.succAbove j) from hi⟩⟩
          exact Nat.succ_le_succ (ih k L' hL' hcover')

private theorem imageSet_not_finiteUnionLocallyClosed :
    ¬ IsFiniteUnionLocallyClosed imageSet := by
  rintro ⟨m, L, hL, hcover⟩
  exact Nat.not_succ_le_self m (cover_size_bound (m + 1) m L hL hcover.symm)

/-- **Stacks 0GZM.** A finite-presentation morphism of affine schemes can take a locally closed
subset to a set that is not a finite union of locally closed subsets. -/
@[stacks 0GZM]
theorem exists_affine_finitePresentation_image_not_finiteUnionLocallyClosed :
    ∃ (X Y : Scheme.{u}) (f : X ⟶ Y) (T : Set X),
      IsAffine X ∧ IsAffine Y ∧ FinitePresentation f ∧
        IsLocallyClosed T ∧ ¬ IsFiniteUnionLocallyClosed (f.base '' T) := by
  refine ⟨totalScheme, baseScheme, projection, locallyClosedPart,
    AlgebraicGeometry.isAffine_Spec _, AlgebraicGeometry.isAffine_Spec _,
    projection_finitePresentation, locallyClosedPart_isLocallyClosed,
    projection_image_eq ▸ imageSet_not_finiteUnionLocallyClosed⟩

end Stacks.Examples

end

end
