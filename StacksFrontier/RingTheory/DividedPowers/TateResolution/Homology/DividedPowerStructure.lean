module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.Basic
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.Homology.Representative
import all StacksFrontier.RingTheory.DividedPowers.TateResolution.Homology.GradedAlgebra
import all StacksFrontier.RingTheory.DividedPowers.TateResolution.Homology.Representative

/-!
# The divided power structure on homology

This file proves that a surjective morphism from a positively acyclic divided-power differential
graded algebra induces a graded algebra structure and divided powers on the homology quotient of
its target, agreeing with the original divided powers on homogeneous cycles (Tag 09PK).
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v w t

/-- A linear map sending each `S i` into `T i` sends `⨆ i, S i` into `⨆ i, T i`. -/
private theorem map_mem_iSup_of_forall_mem {R : Type u} {M : Type v} {N : Type w} {ι : Type t}
    [Semiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    (f : M →ₗ[R] N) (S : ι → Submodule R M) (T : ι → Submodule R N)
    (h : ∀ i, ∀ z ∈ S i, f z ∈ T i) {z : M} (hz : z ∈ ⨆ i, S i) : f z ∈ ⨆ i, T i :=
  (iSup_le fun i _ hz' => Submodule.mem_iSup_of_mem i (h i _ hz')
    : ⨆ i, S i ≤ (⨆ i, T i).comap f) hz

/-- A surjective morphism from a positively acyclic divided-power DGA induces divided
powers on the actual homology quotient of its target. The induced operations agree with
the original operations on homogeneous cycles. -/
@[stacks 09PK]
public theorem dividedPowerStructureOnHomology_of_surjective
    {R : Type u} {A : Type v} {B : Type w}
    [CommRing R] [Ring A] [Ring B]
    [Algebra R A] [Algebra R B]
    (𝒜 : ℕ → Submodule R A) (ℬ : ℕ → Submodule R B)
    [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
    [IsStrictlyGradedComm 𝒜] [IsStrictlyGradedComm ℬ]
    (dA : A →ₗ[R] A) (dB : B →ₗ[R] B)
    [IsDifferentialGradedAlgebra 𝒜 dA] [IsDifferentialGradedAlgebra ℬ dB]
    (γA : DividedPowerStructure 𝒜) (γB : DividedPowerStructure ℬ)
    [IsCompatibleWithDifferential γA dA] [IsCompatibleWithDifferential γB dB]
    (f : A →ₐ[R] B)
    (hf_grade : ∀ {n : ℕ} {x : A}, x ∈ 𝒜 n → f x ∈ ℬ n)
    (hf_d : ∀ x : A, f (dA x) = dB (f x))
    (hf_dpow : ∀ {n : ℕ} {x : A}, x ∈ positiveEvenPart 𝒜 →
      f (γA.dpow n x) = γB.dpow n (f x))
    (hf_surjective : Function.Surjective f)
    (hA : ∀ {n : ℕ}, 0 < n → ∀ {x : A}, x ∈ 𝒜 n → dA x = 0 →
      ∃ z : A, z ∈ 𝒜 (n + 1) ∧ dA z = x)
    : ∃ hRing : Ring (Homology (𝒜 := ℬ) dB),
      letI : Ring (Homology (𝒜 := ℬ) dB) := hRing
      ∃ hAlgebra : Algebra R (Homology (𝒜 := ℬ) dB),
        letI : Algebra R (Homology (𝒜 := ℬ) dB) := hAlgebra
        letI : AddCommMonoid (Homology (𝒜 := ℬ) dB) := hRing.toAddCommMonoid
        letI : Module R (Homology (𝒜 := ℬ) dB) := Algebra.toModule
        let ℋ : ℕ → Submodule R (Homology (𝒜 := ℬ) dB) := fun n =>
          Submodule.span R {z | ∃ x : cycles dB, (x : B) ∈ ℬ n ∧
            (Submodule.Quotient.mk x : Homology (𝒜 := ℬ) dB) = z}
        ∃ hGraded : GradedAlgebra ℋ,
          letI : GradedAlgebra ℋ := hGraded
          ∃ hStrict : IsStrictlyGradedComm ℋ,
            letI : IsStrictlyGradedComm ℋ := hStrict
            ∃ γH : @DividedPowerStructure R (Homology (𝒜 := ℬ) dB)
                _ hRing hAlgebra ℋ hGraded hStrict,
              (Submodule.Quotient.mk (0 : cycles dB) :
                Homology (𝒜 := ℬ) dB) = 0 ∧
              (∀ x y : cycles dB,
                (Submodule.Quotient.mk (x + y) : Homology (𝒜 := ℬ) dB) =
                  Submodule.Quotient.mk x + Submodule.Quotient.mk y) ∧
              (∀ (r : R) (x : cycles dB),
                (Submodule.Quotient.mk (r • x) : Homology (𝒜 := ℬ) dB) =
                  r • (Submodule.Quotient.mk x : Homology (𝒜 := ℬ) dB)) ∧
              (∃ h1 : dB (1 : B) = 0,
                (Submodule.Quotient.mk (⟨1, h1⟩ : cycles dB) :
                  Homology (𝒜 := ℬ) dB) = 1) ∧
              (∀ {x y : B} (hx : dB x = 0) (hy : dB y = 0),
                ∃ hxy : dB (x * y) = 0,
                  (Submodule.Quotient.mk (⟨x * y, hxy⟩ : cycles dB) :
                    Homology (𝒜 := ℬ) dB) =
                    Submodule.Quotient.mk (⟨x, hx⟩ : cycles dB) *
                      Submodule.Quotient.mk (⟨y, hy⟩ : cycles dB)) ∧
              (∀ {n : ℕ} {x : B} (_hx : x ∈ positiveEvenPart ℬ)
                  (hd : dB x = 0),
                ∃ hγ : dB (γB.dpow n x) = 0,
                  γH.dpow n (Submodule.Quotient.mk (⟨x, hd⟩ : cycles dB)) =
                    Submodule.Quotient.mk (⟨γB.dpow n x, hγ⟩ : cycles dB)) := by
  classical
  let : Ring (cycles dB) := cyclesRing ℬ dB
  let : Algebra R (cycles dB) := cyclesAlgebra ℬ dB
  let hRing : Ring (Homology (𝒜 := ℬ) dB) := homologyRing (𝒜 := ℬ) dB
  refine ⟨hRing, ?_⟩
  let : Ring (Homology (𝒜 := ℬ) dB) := hRing
  let hAlgebra : Algebra R (Homology (𝒜 := ℬ) dB) := homologyAlgebra (𝒜 := ℬ) dB
  refine ⟨hAlgebra, ?_⟩
  let : Algebra R (Homology (𝒜 := ℬ) dB) := hAlgebra
  let : AddCommMonoid (Homology (𝒜 := ℬ) dB) := hRing.toAddCommMonoid
  let : Module R (Homology (𝒜 := ℬ) dB) := Algebra.toModule
  have : (boundaryIdeal (𝒜 := ℬ) dB).IsTwoSided :=
    boundaryIdeal_isTwoSided (𝒜 := ℬ) dB
  let ℋ : ℕ → Submodule R (Homology (𝒜 := ℬ) dB) := fun n =>
    Submodule.span R {z | ∃ x : cycles dB, (x : B) ∈ ℬ n ∧
      (Submodule.Quotient.mk x : Homology (𝒜 := ℬ) dB) = z}
  let : DirectSum.Decomposition (cyclesGrading ℬ dB) := cyclesGrading_decomposition ℬ dB
  have hboundary : ∀ n {x : cycles dB},
      x ∈ boundaries (𝒜 := ℬ) dB →
        (DirectSum.decompose (cyclesGrading ℬ dB) x n : cycles dB) ∈
          boundaries (𝒜 := ℬ) dB :=
    fun n _ hx => boundaries_homogeneous (d := dB) hx n
  let : DirectSum.Decomposition
      (quotientGrading (cyclesGrading ℬ dB) (boundaries (𝒜 := ℬ) dB)) :=
    quotientGrading_decomposition (cyclesGrading ℬ dB) (boundaries (𝒜 := ℬ) dB) hboundary
  have hℋeq := homologyGrading_eq_quotientGrading ℬ dB
  let Q := quotientGrading (cyclesGrading ℬ dB) (boundaries (𝒜 := ℬ) dB)
  have hℋQ (n : ℕ) : ℋ n = Q n := congrFun hℋeq n
  have hQmem : ∀ {i : ℕ} {x : Homology (𝒜 := ℬ) dB}, x ∈ Q i →
      ∃ x' : cycles dB, (x' : B) ∈ ℬ i ∧ Submodule.mkQ (boundaries (𝒜 := ℬ) dB) x' = x :=
    fun hx => Submodule.mem_map.1 hx
  have hGradedOneQ : SetLike.GradedOne Q := by
    refine ⟨?_⟩
    have h1 : dB (1 : B) = 0 :=
      IsDifferentialGradedAlgebra.d_grade_zero (𝒜 := ℬ) (d := dB)
        SetLike.GradedOne.one_mem
    show Submodule.mkQ (boundaries (𝒜 := ℬ) dB) (⟨1, h1⟩ : cycles dB) ∈
        Submodule.map (Submodule.mkQ (boundaries (𝒜 := ℬ) dB))
          (cyclesGrading ℬ dB 0)
    rw [Submodule.mem_map]
    refine ⟨⟨1, h1⟩, ?_, rfl⟩
    show (1 : B) ∈ ℬ 0
    exact SetLike.GradedOne.one_mem
  have mkQ_mul (x y : cycles dB) :
      Submodule.mkQ (boundaries (𝒜 := ℬ) dB) (x * y) =
        Submodule.mkQ (boundaries (𝒜 := ℬ) dB) x *
          Submodule.mkQ (boundaries (𝒜 := ℬ) dB) y := rfl
  have mkQ_add (x y : cycles dB) :
      Submodule.mkQ (boundaries (𝒜 := ℬ) dB) (x + y) =
        Submodule.mkQ (boundaries (𝒜 := ℬ) dB) x +
          Submodule.mkQ (boundaries (𝒜 := ℬ) dB) y := rfl
  have mkQ_one : Submodule.mkQ (boundaries (𝒜 := ℬ) dB) (1 : cycles dB) = 1 := rfl
  have mkQ_pow (z : cycles dB) (n : ℕ) :
      Submodule.mkQ (boundaries (𝒜 := ℬ) dB) (z ^ n) =
        (Submodule.mkQ (boundaries (𝒜 := ℬ) dB) z) ^ n := by
    induction n with
    | zero => simp [mkQ_one]
    | succ n ih => rw [pow_succ, pow_succ, mkQ_mul, ih]
  have dNat (k : ℕ) : dB (k : B) = 0 := by
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Nat.cast_succ, map_add, ih]
        have hone := IsDifferentialGradedAlgebra.d_grade_zero
          (𝒜 := ℬ) (d := dB) SetLike.GradedOne.one_mem
        simp [hone]
  let natCycle : ℕ → cycles dB := fun k =>
    ⟨(k : B), LinearMap.mem_ker.mpr (dNat k)⟩
  have natCycle_succ (k : ℕ) : natCycle (k + 1) = natCycle k + 1 := by
    apply Subtype.ext
    simp only [natCycle, Nat.cast_succ, Submodule.coe_add]
    rfl
  have mkQ_natCast (k : ℕ) :
      Submodule.mkQ (boundaries (𝒜 := ℬ) dB) (natCycle k) =
        (k : Homology (𝒜 := ℬ) dB) := by
    induction k with
    | zero =>
        have hz : natCycle 0 = 0 := by
          apply Subtype.ext
          simp [natCycle]
        rw [hz]
        simp
        rfl
    | succ k ih =>
        rw [natCycle_succ, mkQ_add, ih, mkQ_one]
        simp [Nat.cast_succ]
  have mkQ_sum (s : Finset (ℕ × ℕ)) (g : ℕ × ℕ → cycles dB) :
      Submodule.mkQ (boundaries (𝒜 := ℬ) dB) (∑ i ∈ s, g i) =
        ∑ i ∈ s, Submodule.mkQ (boundaries (𝒜 := ℬ) dB) (g i) := by
    classical
    induction s using Finset.induction_on with
    | empty => rfl
    | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, mkQ_add, ih]
  have hGradedMulQ : SetLike.GradedMul Q := by
      refine ⟨?_⟩
      intro i j x y hx hy
      obtain ⟨x', hx', rfl⟩ := hQmem hx
      obtain ⟨y', hy', rfl⟩ := hQmem hy
      have hxyc : dB ((x' : B) * (y' : B)) = 0 :=
        differential_mul_of_cycles ℬ dB x'.property y'.property
      have hmem : (⟨(x' : B) * (y' : B), hxyc⟩ : cycles dB) ∈
          cyclesGrading ℬ dB (i + j) := by
        show ((x' : B) * (y' : B)) ∈ ℬ (i + j)
        exact SetLike.GradedMul.mul_mem hx' hy'
      show Submodule.mkQ (boundaries (𝒜 := ℬ) dB)
          (⟨(x' : B) * (y' : B), hxyc⟩ : cycles dB) ∈
            Submodule.map (Submodule.mkQ (boundaries (𝒜 := ℬ) dB))
              (cyclesGrading ℬ dB (i + j))
      exact Submodule.mem_map_of_mem hmem
  let : SetLike.GradedOne Q := hGradedOneQ
  let : SetLike.GradedMul Q := hGradedMulQ
  have hGradedMonoidQ : SetLike.GradedMonoid Q := SetLike.GradedMonoid.mk
  let hGradedMonoid : SetLike.GradedMonoid ℋ := by
    unfold ℋ
    exact hℋeq ▸ hGradedMonoidQ
  let : SetLike.GradedMonoid ℋ := hGradedMonoid
  let hDecompQ : DirectSum.Decomposition
      (quotientGrading (cyclesGrading ℬ dB) (boundaries (𝒜 := ℬ) dB)) :=
    quotientGrading_decomposition (cyclesGrading ℬ dB) (boundaries (𝒜 := ℬ) dB) hboundary
  let : DirectSum.Decomposition ℋ := by
    unfold ℋ
    exact hℋeq ▸ hDecompQ
  let hGraded : GradedAlgebra ℋ := GradedRing.mk
  have hStrictQ : IsStrictlyGradedComm Q := by
    constructor
    · intro i j x y hx hy
      obtain ⟨x', hx', rfl⟩ := hQmem hx
      obtain ⟨y', hy', rfl⟩ := hQmem hy
      show Submodule.mkQ (boundaries (𝒜 := ℬ) dB) x' *
          Submodule.mkQ (boundaries (𝒜 := ℬ) dB) y' = _
      have hcomm : x' * y' = (-1 : R) ^ (i * j) • (y' * x') :=
        Subtype.ext (IsStrictlyGradedComm.graded_comm hx' hy')
      calc
        _ = Submodule.mkQ (boundaries (𝒜 := ℬ) dB) (x' * y') := (mkQ_mul x' y').symm
        _ = Submodule.mkQ (boundaries (𝒜 := ℬ) dB)
            ((-1 : R) ^ (i * j) • (y' * x')) := congrArg _ hcomm
        _ = _ := rfl
    · intro i x hx
      obtain ⟨x', hx', rfl⟩ := hQmem hx
      have hxSq : x' ^ 2 = 0 := Subtype.ext (IsStrictlyGradedComm.odd_sq_zero hx')
      have hxMul : x' * x' = 0 := by simpa [pow_two] using hxSq
      calc
        (Submodule.mkQ (boundaries (𝒜 := ℬ) dB) x') ^ 2 =
            Submodule.mkQ (boundaries (𝒜 := ℬ) dB) (x' * x') := by
              rw [pow_two, ← mkQ_mul]
        _ = 0 := congrArg (Submodule.mkQ (boundaries (𝒜 := ℬ) dB)) hxMul
  let hStrict : IsStrictlyGradedComm ℋ := by
    unfold ℋ
    exact hℋeq ▸ hStrictQ
  refine ⟨hGraded, ?_⟩
  have mkQ_mem_grade : ∀ {n : ℕ} {y : cycles dB}, y ∈ cyclesGrading ℬ dB n →
      Submodule.mkQ (boundaries (𝒜 := ℬ) dB) y ∈ ℋ n := fun {n} {y} hy =>
    Submodule.subset_span ⟨y, hy, rfl⟩
  have hPEPLift : ∀ {x : Homology (𝒜 := ℬ) dB}, x ∈ positiveEvenPart ℋ →
      ∃ y : cycles dB, y ∈ positiveEvenPart (cyclesGrading ℬ dB) ∧
        Submodule.mkQ (boundaries (𝒜 := ℬ) dB) y = x := by
    intro x hx
    exact @exists_positiveEven_lift_of_preimage R (cycles dB) (Homology (𝒜 := ℬ) dB)
      _ _ _ _ _ (cyclesGrading ℬ dB) ℋ
      (cyclesGrading_decomposition ℬ dB) inferInstance
      (Submodule.mkQ (boundaries (𝒜 := ℬ) dB)) mkQ_mem_grade
      x hx (Submodule.mkQ_surjective (boundaries (𝒜 := ℬ) dB) x)
  let liftPEP (x : Homology (𝒜 := ℬ) dB)
      (hx : x ∈ positiveEvenPart ℋ) : cycles dB :=
    Classical.choose (hPEPLift hx)
  have liftPEP_mem (x : Homology (𝒜 := ℬ) dB) (hx : x ∈ positiveEvenPart ℋ) :
      liftPEP x hx ∈ positiveEvenPart (cyclesGrading ℬ dB) :=
    (Classical.choose_spec (hPEPLift hx)).1
  have liftPEP_mk (x : Homology (𝒜 := ℬ) dB) (hx : x ∈ positiveEvenPart ℋ) :
      Submodule.mkQ (boundaries (𝒜 := ℬ) dB) (liftPEP x hx) = x :=
    (Classical.choose_spec (hPEPLift hx)).2
  have liftPEP_coe (x : Homology (𝒜 := ℬ) dB) (hx : x ∈ positiveEvenPart ℋ) :
      (liftPEP x hx : B) ∈ positiveEvenPart ℬ := by
    exact map_mem_iSup_of_forall_mem (cycles dB).subtype _ (fun n => ℬ (2 * (n + 1)))
      (fun _ _ hz => hz) (liftPEP_mem x hx)
  have hEvenLift : ∀ {x : Homology (𝒜 := ℬ) dB}, x ∈ evenPart ℋ →
      ∃ y : cycles dB, y ∈ evenPart (cyclesGrading ℬ dB) ∧
        Submodule.mkQ (boundaries (𝒜 := ℬ) dB) y = x := by
    intro x hx
    exact @exists_even_lift R (cycles dB) (Homology (𝒜 := ℬ) dB)
      _ _ _ _ _ (cyclesGrading ℬ dB) ℋ
      (cyclesGrading_decomposition ℬ dB) inferInstance
      (Submodule.mkQ (boundaries (𝒜 := ℬ) dB)) mkQ_mem_grade
      (fun y => Submodule.mkQ_surjective (boundaries (𝒜 := ℬ) dB) y) x hx
  let liftEven (x : Homology (𝒜 := ℬ) dB) (hx : x ∈ evenPart ℋ) : cycles dB :=
    Classical.choose (hEvenLift hx)
  have liftEven_mem (x : Homology (𝒜 := ℬ) dB) (hx : x ∈ evenPart ℋ) :
      liftEven x hx ∈ evenPart (cyclesGrading ℬ dB) :=
    (Classical.choose_spec (hEvenLift hx)).1
  have liftEven_mk (x : Homology (𝒜 := ℬ) dB) (hx : x ∈ evenPart ℋ) :
      Submodule.mkQ (boundaries (𝒜 := ℬ) dB) (liftEven x hx) = x :=
    (Classical.choose_spec (hEvenLift hx)).2
  have liftEven_coe (x : Homology (𝒜 := ℬ) dB) (hx : x ∈ evenPart ℋ) :
      (liftEven x hx : B) ∈ evenPart ℬ := by
    exact map_mem_iSup_of_forall_mem (cycles dB).subtype _ (fun n => ℬ (2 * n))
      (fun _ _ hz => hz) (liftEven_mem x hx)
  have cyclePositiveEven (y : cycles dB) (hy : (y : B) ∈ positiveEvenPart ℬ) :
      y ∈ positiveEvenPart (cyclesGrading ℬ dB) := by
    obtain ⟨z, hz, hzeq⟩ := @exists_positiveEven_lift_of_preimage R (cycles dB) B
      _ _ _ _ _ (cyclesGrading ℬ dB) ℬ
      (cyclesGrading_decomposition ℬ dB)
      (inferInstance : DirectSum.Decomposition ℬ)
      (cycles dB).subtype
      (fun {n} {x} hx => hx) (y : B) hy ⟨y, rfl⟩
    rwa [Subtype.ext hzeq] at hz
  have quotientPositiveEven (z : cycles dB)
      (hz : z ∈ positiveEvenPart (cyclesGrading ℬ dB)) :
      Submodule.mkQ (boundaries (𝒜 := ℬ) dB) z ∈ positiveEvenPart ℋ := by
    have hQ : Submodule.mkQ (boundaries (𝒜 := ℬ) dB) z ∈ positiveEvenPart Q :=
      map_mem_iSup_of_forall_mem (Submodule.mkQ (boundaries (𝒜 := ℬ) dB))
        (fun n => cyclesGrading ℬ dB (2 * (n + 1))) (fun n => Q (2 * (n + 1)))
        (fun _ _ hz => Submodule.mem_map_of_mem hz) hz
    unfold ℋ
    exact hℋeq ▸ hQ
  let dpowH : ℕ → Homology (𝒜 := ℬ) dB → Homology (𝒜 := ℬ) dB :=
    fun n x => if hx : x ∈ positiveEvenPart ℋ then
      Submodule.mkQ (boundaries (𝒜 := ℬ) dB)
        ⟨γB.dpow n (liftPEP x hx : B),
          dpow_cycle_of_cycle ℬ dB γB (liftPEP_coe x hx)
            (liftPEP x hx).property n⟩ else 0
  have dpowClass_eq_of_rep (x : Homology (𝒜 := ℬ) dB)
      (hx : x ∈ positiveEvenPart ℋ) (y : cycles dB)
      (hy : (y : B) ∈ positiveEvenPart ℬ)
      (hrep : Submodule.mkQ (boundaries (𝒜 := ℬ) dB) y = x) (n : ℕ) :
      Submodule.mkQ (boundaries (𝒜 := ℬ) dB)
          ⟨γB.dpow n (liftPEP x hx : B),
            dpow_cycle_of_cycle ℬ dB γB (liftPEP_coe x hx)
              (liftPEP x hx).property n⟩ =
        Submodule.mkQ (boundaries (𝒜 := ℬ) dB)
          ⟨γB.dpow n (y : B), dpow_cycle_of_cycle ℬ dB γB hy y.property n⟩ := by
    have hquot : Submodule.mkQ (boundaries (𝒜 := ℬ) dB) y =
        Submodule.mkQ (boundaries (𝒜 := ℬ) dB) (liftPEP x hx) :=
      hrep.trans (liftPEP_mk x hx).symm
    have hbound : y - liftPEP x hx ∈ boundaries (𝒜 := ℬ) dB :=
      (Submodule.Quotient.eq (boundaries (𝒜 := ℬ) dB)).mp hquot
    have hpre : ∃ z, dB z = (y : B) - (liftPEP x hx : B) :=
      (mem_boundaries_iff (d := dB) (y - liftPEP x hx)).mp hbound
    have hdiff := dpow_positiveEven_eq_mod_boundary 𝒜 ℬ dA dB γA γB f
      hf_grade hf_d hf_dpow hf_surjective hA
      (liftPEP_coe x hx) hy (liftPEP x hx).property y.property hpre n
    have hpre' := LinearMap.mem_range.mp hdiff
    have hbound' :
        (⟨γB.dpow n (y : B), dpow_cycle_of_cycle ℬ dB γB hy y.property n⟩ : cycles dB) -
          ⟨γB.dpow n (liftPEP x hx : B),
            dpow_cycle_of_cycle ℬ dB γB (liftPEP_coe x hx)
              (liftPEP x hx).property n⟩ ∈ boundaries (𝒜 := ℬ) dB := by
      apply (mem_boundaries_iff (d := dB) _).2
      rcases hpre' with ⟨z, hz⟩
      refine ⟨z, ?_⟩
      simpa only [Submodule.coe_sub] using hz
    apply (Submodule.Quotient.eq (boundaries (𝒜 := ℬ) dB)).mpr
    simpa only [neg_sub] using Submodule.neg_mem _ hbound'
  have dpowH_eq_rep (x : Homology (𝒜 := ℬ) dB)
      (hx : x ∈ positiveEvenPart ℋ) (y : cycles dB)
      (hy : (y : B) ∈ positiveEvenPart ℬ)
      (hrep : Submodule.mkQ (boundaries (𝒜 := ℬ) dB) y = x) (n : ℕ) :
      dpowH n x = Submodule.mkQ (boundaries (𝒜 := ℬ) dB)
        ⟨γB.dpow n (y : B), dpow_cycle_of_cycle ℬ dB γB hy y.property n⟩ := by
    simpa [dpowH, hx] using dpowClass_eq_of_rep x hx y hy hrep n
  have dpow_zero_of_pos_grade_zero (n : ℕ) (hn : n ≠ 0) :
      γB.dpow n (0 : B) = 0 := by
    have hzeroPos : (0 : B) ∈ positiveEvenPart ℬ := Submodule.zero_mem _
    have hzeroGrade : (0 : B) ∈ ℬ 0 := Submodule.zero_mem _
    have hgrade := γB.dpow_mem_grade (d := 0) hn hzeroPos hzeroGrade
    have hgrade0 : γB.dpow n 0 ∈ ℬ 0 := by simpa using hgrade
    have hmem := γB.dpow_mem hn hzeroPos
    have hdecomp := decompose_eq_zero_of_mem_positiveEven_of_not_grade ℬ hmem
      (i := 0) (by rintro ⟨k, hk⟩; omega)
    have hsame := DirectSum.decompose_of_mem_same ℬ hgrade0
    rw [← hsame, hdecomp]
  let γH : @DividedPowerStructure R (Homology (𝒜 := ℬ) dB)
      _ hRing hAlgebra ℋ hGraded hStrict := by
    classical
    refine {
      dpow := dpowH
      dpow_null := by
        intro n x hx
        simp [dpowH, hx]
        rfl
      dpow_zero := by
        intro x hx
        simp [dpowH, hx, γB.dpow_zero (liftPEP_coe x hx)]
        rfl
      dpow_one := by
        intro x hx
        simpa [dpowH, hx, γB.dpow_one (liftPEP_coe x hx)] using liftPEP_mk x hx
      dpow_mem := by
        intro n x hn hx
        have hmemB := γB.dpow_mem hn (liftPEP_coe x hx)
        have hcycle := dpow_cycle_of_cycle ℬ dB γB (liftPEP_coe x hx)
          (liftPEP x hx).property n
        simpa [dpowH, hx] using quotientPositiveEven _ (cyclePositiveEven ⟨_, hcycle⟩ hmemB)
      dpow_mem_grade := by
        intro n d x hn hx hxd
        have hxQ : x ∈ Q (2 * d) := hℋQ _ ▸ hxd
        by_cases hd : d = 0
        · subst d
          have hdecomp := decompose_eq_zero_of_mem_positiveEven_of_not_grade ℋ hx
            (i := 0) (by rintro ⟨k, hk⟩; omega)
          have hsame := DirectSum.decompose_of_mem_same ℋ hxd
          have hxzero : x = 0 := by rw [← hsame, hdecomp]; rfl
          have hzpep : (0 : Homology (𝒜 := ℬ) dB) ∈ positiveEvenPart ℋ :=
            Submodule.zero_mem _
          have hzeroCycle : (0 : B) ∈ positiveEvenPart ℬ := Submodule.zero_mem _
          have hzeroKer : (0 : B) ∈ cycles dB := LinearMap.mem_ker.mpr (map_zero dB)
          let z0 : cycles dB := ⟨0, hzeroKer⟩
          have hz0cycle : dB (z0 : B) = 0 := LinearMap.mem_ker.mp z0.property
          have hzeroRep := dpowH_eq_rep (0 : Homology (𝒜 := ℬ) dB) hzpep
            z0 hzeroCycle rfl n
          have hγcycle : dB (γB.dpow n (z0 : B)) = 0 :=
            dpow_cycle_of_cycle ℬ dB γB hzeroCycle hz0cycle n
          have hγzero : γB.dpow n (z0 : B) = 0 := by
            simpa using dpow_zero_of_pos_grade_zero n hn
          have hγSubtype :
              (⟨γB.dpow n (z0 : B), LinearMap.mem_ker.mpr hγcycle⟩ : cycles dB) = 0 :=
            Subtype.ext hγzero
          have hdpow0 : dpowH n (0 : Homology (𝒜 := ℬ) dB) = 0 := by
            rw [hzeroRep]
            calc
              _ = Submodule.mkQ (boundaries (𝒜 := ℬ) dB) 0 := congrArg _ hγSubtype
              _ = 0 := by simp
          rw [hxzero, hdpow0]
          exact Submodule.zero_mem _
        · have hdpos : 0 < d := Nat.pos_of_ne_zero hd
          obtain ⟨y, hygrade, hrep⟩ := hQmem hxQ
          have hypos : (y : B) ∈ positiveEvenPart ℬ :=
            mem_positiveEvenPart_of_mem_grade ℬ hdpos hygrade
          have hdpowgrade := γB.dpow_mem_grade hn hypos hygrade
          have hycycle : dB (y : B) = 0 := LinearMap.mem_ker.mp y.property
          have hdpowcycle := dpow_cycle_of_cycle ℬ dB γB hypos hycycle n
          let ydpow : cycles dB :=
            ⟨γB.dpow n (y : B), LinearMap.mem_ker.mpr hdpowcycle⟩
          have hout :
              ydpow ∈ cyclesGrading ℬ dB (2 * n * d) := by
            show γB.dpow n (y : B) ∈ ℬ (2 * n * d)
            exact hdpowgrade
          have houtQ : Submodule.mkQ (boundaries (𝒜 := ℬ) dB)
              ydpow ∈ Q (2 * n * d) :=
            Submodule.mem_map_of_mem hout
          rw [dpowH_eq_rep x hx y hypos hrep n]
          show Submodule.mkQ (boundaries (𝒜 := ℬ) dB) ydpow ∈ ℋ (2 * n * d)
          exact (hℋQ _).symm ▸ houtQ
      dpow_mul := by
        intro m n x hx
        have hxB := liftPEP_coe x hx
        have hxm := dpowH_eq_rep x hx (liftPEP x hx) hxB
          (liftPEP_mk x hx) m
        have hxn := dpowH_eq_rep x hx (liftPEP x hx) hxB
          (liftPEP_mk x hx) n
        have hxmn := dpowH_eq_rep x hx (liftPEP x hx) hxB
          (liftPEP_mk x hx) (n + m)
        rw [hxn, hxm, hxmn]
        exact congrArg (Submodule.mkQ (boundaries (𝒜 := ℬ) dB)) (Subtype.ext (γB.dpow_mul hxB))
      dpow_mul_even := by
        intro n x y hn hx hy
        let x₀ := liftEven x hx
        let y₀ := liftPEP y hy
        have hxB := liftEven_coe x hx
        have hyB := liftPEP_coe y hy
        have hprodPos : x * y ∈ positiveEvenPart ℋ :=
          evenPart_mul_positiveEvenPart ℋ hx hy
        have hprodB : ((x₀ : B) * (y₀ : B)) ∈ positiveEvenPart ℬ :=
          evenPart_mul_positiveEvenPart ℬ hxB hyB
        have hcoeMul : ((x₀ * y₀ : cycles dB) : B) =
            (x₀ : B) * (y₀ : B) := by rfl
        have hprodRep : Submodule.mkQ (boundaries (𝒜 := ℬ) dB) (x₀ * y₀) = x * y := by
          rw [mkQ_mul x₀ y₀, liftEven_mk x hx, liftPEP_mk y hy]
        have hprodB' : ((x₀ * y₀ : cycles dB) : B) ∈ positiveEvenPart ℬ := by
          rw [hcoeMul]
          exact hprodB
        have hx₀cycle : dB (x₀ : B) = 0 := LinearMap.mem_ker.mp x₀.property
        have hy₀cycle : dB (y₀ : B) = 0 := LinearMap.mem_ker.mp y₀.property
        have hprodcycle : dB ((x₀ : B) * (y₀ : B)) = 0 :=
          differential_mul_of_cycles ℬ dB hx₀cycle hy₀cycle
        have hdpowYcycle : dB (γB.dpow n (y₀ : B)) = 0 :=
          dpow_cycle_of_cycle ℬ dB γB hyB hy₀cycle n
        let p : cycles dB :=
          ⟨γB.dpow n ((x₀ : B) * (y₀ : B)), LinearMap.mem_ker.mpr
            (dpow_cycle_of_cycle ℬ dB γB hprodB hprodcycle n)⟩
        let q : cycles dB :=
          ⟨γB.dpow n (y₀ : B), LinearMap.mem_ker.mpr hdpowYcycle⟩
        have hsource := γB.dpow_mul_even hn hxB hyB
        have hpq : p = x₀ ^ n * q := Subtype.ext hsource
        calc
          dpowH n (x * y) = Submodule.mkQ (boundaries (𝒜 := ℬ) dB) p := by
            simpa [p, hcoeMul] using
              dpowH_eq_rep (x * y) hprodPos (x₀ * y₀) hprodB' hprodRep n
          _ = Submodule.mkQ (boundaries (𝒜 := ℬ) dB) (x₀ ^ n * q) :=
            congrArg _ hpq
          _ = (Submodule.mkQ (boundaries (𝒜 := ℬ) dB) x₀) ^ n *
                Submodule.mkQ (boundaries (𝒜 := ℬ) dB) q := by
            rw [mkQ_mul, mkQ_pow]
          _ = x ^ n * dpowH n y := by
            rw [liftEven_mk x hx,
              dpowH_eq_rep y hy y₀ hyB (liftPEP_mk y hy) n]
      dpow_mul_odd := by
        intro n d e x y hn hx hy
        show dpowH n (x * y) = 0
        obtain ⟨x₀, hx₀, rfl⟩ := hQmem (hℋQ _ ▸ hx)
        obtain ⟨y₀, hy₀, rfl⟩ := hQmem (hℋQ _ ▸ hy)
        let z : cycles dB := x₀ * y₀
        have hgrade : (x₀ : B) * (y₀ : B) ∈
            ℬ ((2 * d + 1) + (2 * e + 1)) :=
          SetLike.GradedMul.mul_mem hx₀ hy₀
        have hgrade' : (x₀ : B) * (y₀ : B) ∈ ℬ (2 * (d + e + 1)) := by
          have hidx : (2 * d + 1) + (2 * e + 1) = 2 * (d + e + 1) := by omega
          simpa only [hidx] using hgrade
        have hclass :
            Submodule.mkQ (boundaries (𝒜 := ℬ) dB) z =
              Submodule.mkQ (boundaries (𝒜 := ℬ) dB) x₀ *
                Submodule.mkQ (boundaries (𝒜 := ℬ) dB) y₀ :=
          mkQ_mul x₀ y₀
        have hzB : (z : B) ∈ positiveEvenPart ℬ := by
          show (x₀ : B) * (y₀ : B) ∈ positiveEvenPart ℬ
          exact mem_positiveEvenPart_of_mem_grade ℬ (d := d + e + 1) (by omega) hgrade'
        have hzH := quotientPositiveEven z (cyclePositiveEven z hzB)
        rw [← hclass]
        rw [dpowH_eq_rep (Submodule.mkQ (boundaries (𝒜 := ℬ) dB) z) hzH
          z hzB rfl n]
        have hzero := γB.dpow_mul_odd hn hx₀ hy₀
        have hzcycle := dpow_cycle_of_cycle ℬ dB γB hzB z.property n
        have hzero' :
            (⟨γB.dpow n ((x₀ : B) * (y₀ : B)), hzcycle⟩ : cycles dB) = 0 :=
          Subtype.ext hzero
        show Submodule.mkQ (boundaries (𝒜 := ℬ) dB)
          ⟨γB.dpow n ((x₀ : B) * (y₀ : B)), hzcycle⟩ = 0
        rw [hzero']
        simp
      dpow_add := by
        intro n x y hx hy
        let x₀ := liftPEP x hx
        let y₀ := liftPEP y hy
        have hxB := liftPEP_coe x hx
        have hyB := liftPEP_coe y hy
        have hsumpos : x + y ∈ positiveEvenPart ℋ := Submodule.add_mem _ hx hy
        have hsumcoe : ((x₀ + y₀ : cycles dB) : B) ∈ positiveEvenPart ℬ :=
          Submodule.add_mem _ hxB hyB
        have hsumcycle : dB ((x₀ : B) + (y₀ : B)) = 0 := by
          rw [map_add, (liftPEP x hx).property, (liftPEP y hy).property]
          simp
        have hsumrep : Submodule.mkQ (boundaries (𝒜 := ℬ) dB)
            (x₀ + y₀ : cycles dB) = x + y := by
          rw [map_add, liftPEP_mk x hx, liftPEP_mk y hy]
        have hsource :
            (⟨γB.dpow n ((x₀ : B) + (y₀ : B)),
              dpow_cycle_of_cycle (x := (x₀ : B) + (y₀ : B)) ℬ dB γB
                hsumcoe hsumcycle n⟩ : cycles dB) =
              ∑ ij ∈ Finset.antidiagonal n,
                (⟨γB.dpow ij.1 (x₀ : B) * γB.dpow ij.2 (y₀ : B),
                  differential_mul_of_cycles ℬ dB
                    (dpow_cycle_of_cycle (x := (x₀ : B)) ℬ dB γB hxB
                      (liftPEP x hx).property ij.1)
                    (dpow_cycle_of_cycle (x := (y₀ : B)) ℬ dB γB hyB
                      (liftPEP y hy).property ij.2)⟩ : cycles dB) := by
          apply Subtype.ext
          show γB.dpow n ((x₀ : B) + (y₀ : B)) =
            ↑(∑ ij ∈ Finset.antidiagonal n,
              (⟨γB.dpow ij.1 (x₀ : B) * γB.dpow ij.2 (y₀ : B),
                differential_mul_of_cycles ℬ dB
                  (dpow_cycle_of_cycle (x := (x₀ : B)) ℬ dB γB hxB
                    (liftPEP x hx).property ij.1)
                  (dpow_cycle_of_cycle (x := (y₀ : B)) ℬ dB γB hyB
                    (liftPEP y hy).property ij.2)⟩ : cycles dB))
          simpa using (γB.dpow_add (n := n) hxB hyB)
        have hquot := congrArg (Submodule.mkQ (boundaries (𝒜 := ℬ) dB)) hsource
        have hquot' :
            Submodule.mkQ (boundaries (𝒜 := ℬ) dB)
                ⟨γB.dpow n ((x₀ : B) + (y₀ : B)),
                  dpow_cycle_of_cycle (x := (x₀ : B) + (y₀ : B)) ℬ dB γB
                    hsumcoe hsumcycle n⟩ =
              ∑ ij ∈ Finset.antidiagonal n,
                Submodule.mkQ (boundaries (𝒜 := ℬ) dB)
                  ⟨γB.dpow ij.1 (x₀ : B) * γB.dpow ij.2 (y₀ : B),
                    differential_mul_of_cycles ℬ dB
                      (dpow_cycle_of_cycle (x := (x₀ : B)) ℬ dB γB hxB
                        (liftPEP x hx).property ij.1)
                      (dpow_cycle_of_cycle (x := (y₀ : B)) ℬ dB γB hyB
                        (liftPEP y hy).property ij.2)⟩ := by
          calc
            _ = Submodule.mkQ (boundaries (𝒜 := ℬ) dB)
                (∑ ij ∈ Finset.antidiagonal n,
                  (⟨γB.dpow ij.1 (x₀ : B) * γB.dpow ij.2 (y₀ : B),
                    differential_mul_of_cycles ℬ dB
                      (dpow_cycle_of_cycle (x := (x₀ : B)) ℬ dB γB hxB
                        (liftPEP x hx).property ij.1)
                      (dpow_cycle_of_cycle (x := (y₀ : B)) ℬ dB γB hyB
                        (liftPEP y hy).property ij.2)⟩ : cycles dB)) := hquot
            _ = _ := mkQ_sum _ _
        calc
          dpowH n (x + y) = Submodule.mkQ (boundaries (𝒜 := ℬ) dB)
              ⟨γB.dpow n ((x₀ : B) + (y₀ : B)),
                dpow_cycle_of_cycle (x := (x₀ : B) + (y₀ : B)) ℬ dB γB
                  hsumcoe hsumcycle n⟩ :=
            dpowH_eq_rep (x + y) hsumpos (x₀ + y₀) hsumcoe hsumrep n
          _ = ∑ ij ∈ Finset.antidiagonal n,
              Submodule.mkQ (boundaries (𝒜 := ℬ) dB)
                ⟨γB.dpow ij.1 (x₀ : B) * γB.dpow ij.2 (y₀ : B),
                  differential_mul_of_cycles ℬ dB
                    (dpow_cycle_of_cycle (x := (x₀ : B)) ℬ dB γB hxB
                      (liftPEP x hx).property ij.1)
                    (dpow_cycle_of_cycle (x := (y₀ : B)) ℬ dB γB hyB
                      (liftPEP y hy).property ij.2)⟩ := hquot'
          _ = ∑ ij ∈ Finset.antidiagonal n,
              dpowH ij.1 x * dpowH ij.2 y := by
            apply Finset.sum_congr rfl
            intro ij hij
            rw [dpowH_eq_rep x hx x₀ hxB (liftPEP_mk x hx) ij.1,
              dpowH_eq_rep y hy y₀ hyB (liftPEP_mk y hy) ij.2]
            let a : cycles dB := ⟨γB.dpow ij.1 (x₀ : B),
              dpow_cycle_of_cycle (x := (x₀ : B)) ℬ dB γB hxB
                (liftPEP x hx).property ij.1⟩
            let b : cycles dB := ⟨γB.dpow ij.2 (y₀ : B),
              dpow_cycle_of_cycle (x := (y₀ : B)) ℬ dB γB hyB
                (liftPEP y hy).property ij.2⟩
            have hab :
                (⟨γB.dpow ij.1 (x₀ : B) * γB.dpow ij.2 (y₀ : B),
                  differential_mul_of_cycles ℬ dB a.property b.property⟩ : cycles dB) =
                  a * b := by
              apply Subtype.ext
              rfl
            calc
              _ = Submodule.mkQ (boundaries (𝒜 := ℬ) dB) (a * b) :=
                congrArg _ hab
              _ = _ := mkQ_mul a b
      dpow_dpow := by
        intro m n x hm hn hx
        let x₀ := liftPEP x hx
        have hxB := liftPEP_coe x hx
        have hinnerB : γB.dpow m (x₀ : B) ∈ positiveEvenPart ℬ :=
          γB.dpow_mem hm hxB
        have hx₀cycle : dB (x₀ : B) = 0 := LinearMap.mem_ker.mp x₀.property
        have hinnerCycle : dB (γB.dpow m (x₀ : B)) = 0 :=
          dpow_cycle_of_cycle ℬ dB γB hxB hx₀cycle m
        let inner : cycles dB :=
          ⟨γB.dpow m (x₀ : B), LinearMap.mem_ker.mpr hinnerCycle⟩
        have hinnerCyclePos : inner ∈ positiveEvenPart (cyclesGrading ℬ dB) :=
          cyclePositiveEven inner hinnerB
        have hinnerRep : dpowH m x =
            Submodule.mkQ (boundaries (𝒜 := ℬ) dB) inner := by
          simpa [inner] using dpowH_eq_rep x hx x₀ hxB
            (liftPEP_mk x hx) m
        have hinnerPos : dpowH m x ∈ positiveEvenPart ℋ :=
          hinnerRep.symm ▸ quotientPositiveEven inner hinnerCyclePos
        have houterCycle : dB (γB.dpow n (inner : B)) = 0 :=
          dpow_cycle_of_cycle ℬ dB γB hinnerB hinnerCycle n
        let outer : cycles dB :=
          ⟨γB.dpow n (inner : B), LinearMap.mem_ker.mpr houterCycle⟩
        let last : cycles dB :=
          ⟨γB.dpow (n * m) (x₀ : B),
            LinearMap.mem_ker.mpr
              (dpow_cycle_of_cycle ℬ dB γB hxB hx₀cycle (n * m))⟩
        let coeff : ℕ := (n * m).factorial / (n.factorial * m.factorial ^ n)
        have hsource : outer = natCycle coeff * last := by
          apply Subtype.ext
          have hinnerCoerce : (inner : B) = γB.dpow m (x₀ : B) := rfl
          show γB.dpow n (inner : B) =
            ((natCycle coeff : cycles dB) : B) * (last : B)
          rw [hinnerCoerce]
          show γB.dpow n (γB.dpow m (x₀ : B)) =
            (coeff : B) * γB.dpow (n * m) (x₀ : B)
          exact γB.dpow_dpow hm hn hxB
        have houterRep : dpowH n (dpowH m x) =
            Submodule.mkQ (boundaries (𝒜 := ℬ) dB) outer := by
          simpa [outer] using dpowH_eq_rep (dpowH m x) hinnerPos inner
            hinnerB hinnerRep.symm n
        have hlastRep : dpowH (n * m) x =
            Submodule.mkQ (boundaries (𝒜 := ℬ) dB) last := by
          simpa [last] using dpowH_eq_rep x hx x₀ hxB
            (liftPEP_mk x hx) (n * m)
        calc
          dpowH n (dpowH m x) =
              Submodule.mkQ (boundaries (𝒜 := ℬ) dB) outer := houterRep
          _ = Submodule.mkQ (boundaries (𝒜 := ℬ) dB) (natCycle coeff * last) :=
            congrArg _ hsource
          _ = (coeff : Homology (𝒜 := ℬ) dB) *
                Submodule.mkQ (boundaries (𝒜 := ℬ) dB) last := by
            rw [mkQ_mul, mkQ_natCast]
          _ = (coeff : Homology (𝒜 := ℬ) dB) * dpowH (n * m) x := by
            rw [hlastRep]
      }
  refine ⟨hStrict, γH, rfl, (fun _ _ => rfl), (fun _ _ => rfl), ?_, ?_, ?_⟩
  · exact ⟨IsDifferentialGradedAlgebra.d_grade_zero (𝒜 := ℬ) (d := dB)
      SetLike.GradedOne.one_mem, rfl⟩
  · intro x y hx hy
    exact ⟨differential_mul_of_cycles ℬ dB hx hy, mkQ_mul ⟨x, hx⟩ ⟨y, hy⟩⟩
  intro n x hx hd
  let y : cycles dB := ⟨x, hd⟩
  have hxH : Submodule.mkQ (boundaries (𝒜 := ℬ) dB) y ∈ positiveEvenPart ℋ :=
    quotientPositiveEven y (cyclePositiveEven y hx)
  refine ⟨dpow_cycle_of_cycle ℬ dB γB hx (by simpa [y] using hd) n, ?_⟩
  have hrepr := dpowH_eq_rep
    (Submodule.mkQ (boundaries (𝒜 := ℬ) dB) y) hxH y hx rfl n
  show dpowH n (Submodule.mkQ (boundaries (𝒜 := ℬ) dB) y) =
    Submodule.mkQ (boundaries (𝒜 := ℬ) dB)
      ⟨γB.dpow n x, dpow_cycle_of_cycle ℬ dB γB hx hd n⟩
  exact hrepr

end DividedPowers.TateResolution
