module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.LinearAlgebra.Pi
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.ExteriorAlgebraGrading
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.OddVariable
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.TransportDividedPowers

/-!
# Divided powers on the exterior algebra of a finite free module

The exterior algebra on finitely many degree-one generators is an iterated odd-variable
extension of the base ring ([Stacks, Tag 09PH]), and so carries divided powers on its positive
even part.

The single step is the identification `⋀[R] M ⟨T⟩ ≃ₐ[R] ⋀[R] (M × R)`, where the left side is the
odd-variable extension of `DividedPowers.TateResolution.OddVariableExtension` in degree `1` and
the adjoined variable is sent to the wedge generator of the new coordinate. The identification is
an equivalence of graded algebras, so
`DividedPowers.TateResolution.DividedPowerStructure.transport` moves the divided powers of
`DividedPowers.TateResolution.oddVariableDividedPowerStructure` across it. Iterating the step
along `(Fin (r + 1) → R) ≃ₗ[R] (Fin r → R) × R`, starting from the subsingleton module where the
positive even part vanishes, gives divided powers on `⋀[R] (Fin r → R)` for every `r`.

## Main definitions

* `DividedPowers.TateResolution.ExteriorOddVariable.equiv` — the identification of the
  odd-variable extension of `⋀[R] M` with `⋀[R] (M × R)`.
* `DividedPowers.TateResolution.exteriorProdDividedPowerStructure` — the divided powers on
  `⋀[R] (M × R)` obtained from divided powers on `⋀[R] M`.
* `DividedPowers.TateResolution.exteriorDividedPowerStructure` — the divided powers on
  `⋀[R] (Fin r → R)`.

## Main results

* `DividedPowers.TateResolution.ExteriorOddVariable.hom_mem_exteriorPower` — the identification
  preserves the grading.
* `DividedPowers.TateResolution.ExteriorOddVariable.mem_grade_iff` — the identification matches
  the two gradings.

## Implementation notes

The odd-variable extension is `TrivSqZeroExt` for a twisted bimodule structure, with its own
`Algebra R` instance, so the comparison map is written out as `a + bT ↦ ι(a) + ι(b) · T` rather
than obtained from `TrivSqZeroExt.lift`.

## References

* [Stacks Project, Tag 09PH](https://stacks.math.columbia.edu/tag/09PH)
* [Stacks Project, Tag 0GZ4](https://stacks.math.columbia.edu/tag/0GZ4)
-/

@[expose] public section

namespace DividedPowers.TateResolution

open scoped ExteriorAlgebra

universe u v

/-- The grading of `⋀[R] M` by its exterior powers. -/
public abbrev exteriorGrade (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M]
    [Module R M] (m : ℕ) : Submodule R (ExteriorAlgebra R M) := ⋀[R]^m M

namespace ExteriorOddVariable

attribute [local implicit_reducible] TwistedModule

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- The algebra map `⋀[R] M →ₐ[R] ⋀[R] (M × R)` induced by the first inclusion. -/
public noncomputable def incl :
    ExteriorAlgebra R M →ₐ[R] ExteriorAlgebra R (M × R) :=
  ExteriorAlgebra.map (LinearMap.inl R M R)

/-- The algebra map `⋀[R] (M × R) →ₐ[R] ⋀[R] M` induced by the first projection. -/
public noncomputable def proj :
    ExteriorAlgebra R (M × R) →ₐ[R] ExteriorAlgebra R M :=
  ExteriorAlgebra.map (LinearMap.fst R M R)

/-- The wedge generator of the adjoined coordinate. -/
public noncomputable def gen : ExteriorAlgebra R (M × R) :=
  ExteriorAlgebra.ι R ((0, 1) : M × R)

/-- Contraction by the second coordinate: the Koszul differential of `(m, t) ↦ t`. -/
public noncomputable def contr :
    ExteriorAlgebra R (M × R) →ₗ[R] ExteriorAlgebra R (M × R) :=
  CliffordAlgebra.contractLeft (LinearMap.snd R M R)

/-- The grading sign of `⋀[R] M` in degree one. -/
public noncomputable def sgn : ExteriorAlgebra R M ≃+* ExteriorAlgebra R M :=
  signRingEquiv (exteriorGrade R M) 1

/-- The grading sign is an involution. -/
public theorem sgn_sgn (a : ExteriorAlgebra R M) : sgn (sgn a) = a :=
  signRingHom_involutive (exteriorGrade R M) 1 a

/-- The grading sign acts on `⋀[R]^m M` by `(-1) ^ m`. -/
public theorem sgn_of_mem {m : ℕ} {a : ExteriorAlgebra R M} (ha : a ∈ ⋀[R]^m M) :
    sgn a = (-1 : R) ^ (1 * m) • a :=
  signRingEquiv_of_mem (exteriorGrade R M) 1 m ha

/-- The first inclusion sends the generator `ι x` to `ι (x, 0)`. -/
@[simp]
public theorem incl_apply_ι (x : M) :
    incl (ExteriorAlgebra.ι R x) = ExteriorAlgebra.ι R ((x, 0) : M × R) := by
  rw [incl, ExteriorAlgebra.map_apply_ι]; rfl

/-- The first projection composed with the first inclusion is the identity. -/
public theorem proj_comp_incl :
    (proj (R := R) (M := M)).comp incl = AlgHom.id R (ExteriorAlgebra R M) := by
  rw [proj, incl, ExteriorAlgebra.map_comp_map,
    show (LinearMap.fst R M R).comp (LinearMap.inl R M R) = LinearMap.id from by ext x; rfl,
    ExteriorAlgebra.map_id]

/-- The first projection is a left inverse of the first inclusion. -/
@[simp]
public theorem proj_incl (a : ExteriorAlgebra R M) : proj (incl a) = a :=
  AlgHom.congr_fun (proj_comp_incl (R := R) (M := M)) a

/-- The first inclusion is injective. -/
public theorem incl_injective : Function.Injective (incl (R := R) (M := M)) :=
  Function.LeftInverse.injective (g := proj) proj_incl

/-- The first projection kills the adjoined generator. -/
@[simp]
public theorem proj_gen : proj (gen (R := R) (M := M)) = 0 := by
  rw [gen, proj, ExteriorAlgebra.map_apply_ι,
    show (LinearMap.fst R M R) ((0, 1) : M × R) = 0 from rfl, _root_.map_zero]

/-- The adjoined generator has degree one. -/
public theorem gen_mem : gen (R := R) (M := M) ∈ ⋀[R]^1 (M × R) :=
  ExteriorAlgebra.ι_mem_exteriorPower_one _

/-- The adjoined generator squares to zero. -/
@[simp]
public theorem gen_mul_gen : gen (R := R) (M := M) * gen = 0 :=
  ExteriorAlgebra.ι_sq_zero _

/-- The first inclusion preserves the grading. -/
public theorem incl_mem {m : ℕ} {a : ExteriorAlgebra R M} (ha : a ∈ ⋀[R]^m M) :
    incl a ∈ ⋀[R]^m (M × R) :=
  ExteriorAlgebra.map_mem_exteriorPower _ ha

/-- The Koszul commutation rule between the adjoined generator and a coefficient. -/
public theorem gen_mul_incl (a : ExteriorAlgebra R M) :
    gen * incl a = incl (sgn a) * gen := by
  induction a using DirectSum.Decomposition.inductionOn (exteriorGrade R M) with
  | zero => simp
  | @homogeneous m a =>
    rw [sgn_of_mem a.property, _root_.map_smul, smul_mul_assoc]
    exact ExteriorAlgebra.mul_comm_exteriorPower gen_mem (incl_mem a.property)
  | add a b ha hb => simp only [_root_.map_add, mul_add, add_mul, ha, hb]

/-- The Koszul commutation rule between a coefficient and the adjoined generator. -/
public theorem incl_mul_gen (a : ExteriorAlgebra R M) :
    incl a * gen = gen * incl (sgn a) := by
  rw [gen_mul_incl, sgn_sgn]

/-- A coefficient between two copies of the adjoined generator gives zero. -/
@[simp]
public theorem gen_mul_incl_mul_gen (a : ExteriorAlgebra R M) :
    gen * (incl a * gen) = 0 := by
  rw [← mul_assoc, gen_mul_incl, mul_assoc, gen_mul_gen, mul_zero]

/-- Contraction by the second coordinate kills the image of `⋀[R] M`. -/
@[simp]
public theorem contr_incl (a : ExteriorAlgebra R M) : contr (incl a) = 0 := by
  induction a using CliffordAlgebra.left_induction with
  | algebraMap r =>
    rw [AlgHom.commutes]
    exact CliffordAlgebra.contractLeft_algebraMap _ _ _
  | add x y hx hy => rw [_root_.map_add, _root_.map_add, hx, hy, add_zero]
  | ι_mul x m hx =>
    rw [_root_.map_mul, incl_apply_ι, contr, CliffordAlgebra.contractLeft_ι_mul,
      show (LinearMap.snd R M R) ((m, 0) : M × R) = 0 from rfl, zero_smul,
      show CliffordAlgebra.contractLeft (LinearMap.snd R M R) (incl x) = contr (incl x) from rfl,
      hx, mul_zero, sub_zero]

/-- Contraction by the second coordinate satisfies `contr (gen * y) = y - gen * contr y`. -/
public theorem contr_gen_mul (y : ExteriorAlgebra R (M × R)) :
    contr (gen * y) = y - gen * contr y := by
  rw [contr, gen, CliffordAlgebra.contractLeft_ι_mul,
    show (LinearMap.snd R M R) ((0, 1) : M × R) = 1 from rfl, one_smul]

/-- The comparison map `a + bT ↦ ι(a) + ι(b) · T` from the odd-variable extension of `⋀[R] M`
to `⋀[R] (M × R)`. -/
public noncomputable def hom :
    OddVariableExtension (exteriorGrade R M) 1 →ₐ[R] ExteriorAlgebra R (M × R) where
  toFun x := incl (TrivSqZeroExt.fst x) + incl (TrivSqZeroExt.snd x) * gen
  map_one' := by
    rw [show TrivSqZeroExt.fst (1 : OddVariableExtension (exteriorGrade R M) 1) = 1 from rfl,
      show (TrivSqZeroExt.snd (1 : OddVariableExtension (exteriorGrade R M) 1) :
        ExteriorAlgebra R M) = 0 from rfl]
    simp
  map_mul' x y := by
    rw [show TrivSqZeroExt.fst (x * y) = TrivSqZeroExt.fst x * TrivSqZeroExt.fst y from rfl,
      show (TrivSqZeroExt.snd (x * y) : ExteriorAlgebra R M) =
          TrivSqZeroExt.fst x * (TrivSqZeroExt.snd y : ExteriorAlgebra R M) +
            (TrivSqZeroExt.snd x : ExteriorAlgebra R M) * sgn (TrivSqZeroExt.fst y) from
        OddVariableExtension.mul_snd (exteriorGrade R M) 1 x y]
    simp only [_root_.map_mul, _root_.map_add, add_mul, mul_add, mul_assoc,
      gen_mul_incl_mul_gen, gen_mul_incl, mul_zero, add_zero]
    abel
  map_zero' := by
    rw [show TrivSqZeroExt.fst (0 : OddVariableExtension (exteriorGrade R M) 1) = 0 from rfl,
      show (TrivSqZeroExt.snd (0 : OddVariableExtension (exteriorGrade R M) 1) :
        ExteriorAlgebra R M) = 0 from rfl]
    simp
  map_add' x y := by
    rw [show TrivSqZeroExt.fst (x + y) = TrivSqZeroExt.fst x + TrivSqZeroExt.fst y from rfl,
      show (TrivSqZeroExt.snd (x + y) : ExteriorAlgebra R M) =
        (TrivSqZeroExt.snd x : ExteriorAlgebra R M) +
          (TrivSqZeroExt.snd y : ExteriorAlgebra R M) from rfl]
    simp only [_root_.map_add, add_mul]
    abel
  commutes' r := by
    rw [show TrivSqZeroExt.fst (algebraMap R (OddVariableExtension (exteriorGrade R M) 1) r)
        = algebraMap R (ExteriorAlgebra R M) r from rfl,
      show (TrivSqZeroExt.snd
        (algebraMap R (OddVariableExtension (exteriorGrade R M) 1) r) :
          ExteriorAlgebra R M) = 0 from rfl]
    simp [AlgHom.commutes]

/-- The comparison map on an element `a + bT`. -/
public theorem hom_apply (x : OddVariableExtension (exteriorGrade R M) 1) :
    hom x = incl (TrivSqZeroExt.fst x) + incl (TrivSqZeroExt.snd x) * gen := rfl

/-- The comparison map on the image of a coefficient is the first inclusion. -/
@[simp]
public theorem hom_inclusion (a : ExteriorAlgebra R M) :
    hom (OddVariableExtension.inclusion (exteriorGrade R M) 1 a) = incl a := by
  rw [hom_apply,
    show TrivSqZeroExt.fst (OddVariableExtension.inclusion (exteriorGrade R M) 1 a) = a from rfl,
    show (TrivSqZeroExt.snd (OddVariableExtension.inclusion (exteriorGrade R M) 1 a) :
      ExteriorAlgebra R M) = 0 from rfl]
  simp

/-- The comparison map sends the odd variable to the adjoined generator. -/
@[simp]
public theorem hom_generator :
    hom (OddVariableExtension.generator (exteriorGrade R M) 1) = gen := by
  rw [hom_apply,
    show TrivSqZeroExt.fst (OddVariableExtension.generator (exteriorGrade R M) 1) = 0 from rfl,
    show (TrivSqZeroExt.snd (OddVariableExtension.generator (exteriorGrade R M) 1) :
      ExteriorAlgebra R M) = 1 from rfl]
  simp

/-- The comparison map preserves the grading. -/
public theorem hom_mem_exteriorPower (m : ℕ) (x : OddVariableExtension (exteriorGrade R M) 1)
    (hx : x ∈ OddVariableExtension.grade (exteriorGrade R M) 1 m) :
    hom x ∈ ⋀[R]^m (M × R) := by
  rw [OddVariableExtension.mem_grade_iff] at hx
  obtain ⟨hfst, hsnd⟩ := hx
  rw [hom_apply]
  refine Submodule.add_mem _ (incl_mem hfst) ?_
  rcases m with _ | k
  · rw [show (TrivSqZeroExt.snd x : ExteriorAlgebra R M) = 0 by simpa using hsnd]
    simp
  · have hk : (TrivSqZeroExt.snd x : ExteriorAlgebra R M) ∈ ⋀[R]^k M := by simpa using hsnd
    exact SetLike.mul_mem_graded (incl_mem hk) gen_mem

/-- The comparison map is surjective. -/
public theorem hom_surjective : Function.Surjective (hom (R := R) (M := M)) := by
  have hι : ∀ p : M × R, ∃ w, hom w = ExteriorAlgebra.ι R p := by
    intro p
    refine ⟨OddVariableExtension.inclusion (exteriorGrade R M) 1 (ExteriorAlgebra.ι R p.1) +
      p.2 • OddVariableExtension.generator (exteriorGrade R M) 1, ?_⟩
    rw [_root_.map_add, _root_.map_smul, hom_inclusion, hom_generator, incl_apply_ι, gen,
      ← (ExteriorAlgebra.ι R (M := M × R)).map_smul,
      ← (ExteriorAlgebra.ι R (M := M × R)).map_add]
    congr 1
    simp
  intro y
  show y ∈ (hom (R := R) (M := M)).range
  induction y using CliffordAlgebra.left_induction with
  | algebraMap r => exact Subalgebra.algebraMap_mem _ r
  | add x y hx hy => exact Subalgebra.add_mem _ hx hy
  | ι_mul x p hx => exact Subalgebra.mul_mem _ (hι p) hx

/-- The comparison map is injective. -/
public theorem hom_injective : Function.Injective (hom (R := R) (M := M)) := by
  refine (injective_iff_map_eq_zero _).mpr fun x hx ↦ ?_
  rw [hom_apply] at hx
  have hfst : TrivSqZeroExt.fst x = 0 := by
    have h := congrArg proj hx
    rwa [_root_.map_add, _root_.map_mul, proj_incl, proj_incl, proj_gen, mul_zero, add_zero,
      _root_.map_zero] at h
  rw [hfst, _root_.map_zero, zero_add, incl_mul_gen] at hx
  have h := congrArg contr hx
  rw [contr_gen_mul, contr_incl, mul_zero, sub_zero, _root_.map_zero] at h
  have hsnd : sgn (TrivSqZeroExt.snd x : ExteriorAlgebra R M) = 0 :=
    incl_injective (by rw [h, _root_.map_zero])
  apply TrivSqZeroExt.ext
  · rw [hfst]; simp
  · rw [show (TrivSqZeroExt.snd (0 : OddVariableExtension (exteriorGrade R M) 1) :
      ExteriorAlgebra R M) = 0 from rfl,
      ← sgn_sgn (TrivSqZeroExt.snd x : ExteriorAlgebra R M), hsnd, _root_.map_zero]

/-- The odd-variable extension of `⋀[R] M` is `⋀[R] (M × R)`. -/
@[stacks 09PH "exterior algebra as an iterated odd variable extension"]
public noncomputable def equiv :
    OddVariableExtension (exteriorGrade R M) 1 ≃ₐ[R] ExteriorAlgebra R (M × R) :=
  AlgEquiv.ofBijective hom ⟨hom_injective, hom_surjective⟩

/-- The identification is the comparison map. -/
@[simp]
public theorem equiv_apply (x : OddVariableExtension (exteriorGrade R M) 1) :
    equiv x = hom x := rfl

/-- Multiplication of two elements written in the normal form `a + bT`. -/
public theorem incl_add_mul_gen_mul (u₁ u₂ v₁ v₂ : ExteriorAlgebra R M) :
    (incl u₁ + incl u₂ * gen) * (incl v₁ + incl v₂ * gen) =
      incl (u₁ * v₁) + incl (u₁ * v₂ + u₂ * sgn v₁) * gen := by
  simp only [_root_.map_mul, _root_.map_add, add_mul, mul_add, mul_assoc,
    gen_mul_incl_mul_gen, gen_mul_incl, mul_zero, add_zero]
  abel

/-- Multiplication by the image of a scalar, in the normal form `a + bT`. -/
public theorem incl_mul_algebraMap (u : ExteriorAlgebra R M) (c : R) :
    incl u * algebraMap R (ExteriorAlgebra R (M × R)) c = incl (c • u) := by
  rw [_root_.map_smul, Algebra.smul_def, ← Algebra.commutes c (incl u)]

/-- The identification matches the two gradings. -/
public theorem mem_grade_iff (m : ℕ) (x : OddVariableExtension (exteriorGrade R M) 1) :
    x ∈ OddVariableExtension.grade (exteriorGrade R M) 1 m ↔ equiv x ∈ ⋀[R]^m (M × R) :=
  mem_grade_iff_of_mapsTo (OddVariableExtension.grade (exteriorGrade R M) 1)
    (exteriorGrade R (M × R)) equiv hom_mem_exteriorPower m x

end ExteriorOddVariable

section Construction

open ExteriorOddVariable

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- Divided powers on `⋀[R] (M × R)`, obtained from divided powers on `⋀[R] M` by adjoining one
odd variable of degree one. -/
public noncomputable def exteriorProdDividedPowerStructure
    (γ : DividedPowerStructure (exteriorGrade R M)) :
    DividedPowerStructure (exteriorGrade R (M × R)) :=
  (oddVariableDividedPowerStructure (exteriorGrade R M) γ 1 Nat.one_pos odd_one).transport
    equiv (mem_grade_iff (R := R) (M := M))

/-- The divided powers of `⋀[R] (M × R)` on an element written `a + bT`. -/
public theorem exteriorProdDividedPowerStructure_dpow
    (γ : DividedPowerStructure (exteriorGrade R M)) {n : ℕ} (hn : n ≠ 0)
    {a b : ExteriorAlgebra R M} (ha : a ∈ positiveEvenPart (exteriorGrade R M))
    (hb : b ∈ oddPart (exteriorGrade R M)) :
    (exteriorProdDividedPowerStructure γ).dpow n (incl a + incl b * gen) =
      incl (γ.dpow n a) + incl (γ.dpow (n - 1) a * b) * gen := by
  have hnorm : incl a + incl b * gen =
      equiv (OddVariableExtension.inclusion (exteriorGrade R M) 1 a +
        OddVariableExtension.inclusion (exteriorGrade R M) 1 b *
          OddVariableExtension.generator (exteriorGrade R M) 1) := by
    rw [_root_.map_add, _root_.map_mul, equiv_apply, equiv_apply, equiv_apply, hom_inclusion,
      hom_inclusion, hom_generator]
  have hdef : ∀ (k : ℕ) (z : ExteriorAlgebra R (M × R)),
      (exteriorProdDividedPowerStructure γ).dpow k z =
        equiv ((oddVariableDividedPowerStructure (exteriorGrade R M) γ 1 Nat.one_pos
          odd_one).dpow k (equiv.symm z)) := fun _ _ => rfl
  rw [hnorm, hdef, AlgEquiv.symm_apply_apply,
    oddVariableDividedPowerStructure_dpow (exteriorGrade R M) γ 1 Nat.one_pos odd_one n hn a b
      ha hb, _root_.map_add, _root_.map_mul, equiv_apply, equiv_apply, equiv_apply,
    hom_inclusion, hom_inclusion, hom_generator]

end Construction

section Fin

variable (R : Type u) [CommRing R]

/-- Splitting off the last coordinate, as a linear equivalence. -/
public def finSuccLinearEquiv (r : ℕ) :
    ((Fin r → R) × R) ≃ₗ[R] (Fin (r + 1) → R) :=
  (LinearEquiv.prodComm R (Fin r → R) R).trans
    (Fin.consLinearEquiv R (fun _ : Fin (r + 1) => R))

/-- The positive even part of the exterior algebra of a subsingleton module vanishes. -/
public theorem positiveEvenPart_exteriorGrade_eq_bot
    (M : Type v) [AddCommGroup M] [Module R M] [Subsingleton M] :
    positiveEvenPart (exteriorGrade R M) = ⊥ := by
  refine le_antisymm (iSup_le fun d => ?_) bot_le
  rw [show 2 * (d + 1) = 2 * d + 1 + 1 by ring]
  exact le_of_eq (ExteriorAlgebra.exteriorPower_eq_bot (2 * d + 1))

/-- Divided powers on the exterior algebra of a finite free module, obtained by adjoining the
degree-one generators one at a time. -/
public noncomputable def exteriorDividedPowerStructure :
    ∀ r : ℕ, DividedPowerStructure (exteriorGrade R (Fin r → R))
  | 0 =>
    dividedPowerStructureOfPositiveEvenPartEqBot (exteriorGrade R (Fin 0 → R))
      (positiveEvenPart_exteriorGrade_eq_bot R (Fin 0 → R))
  | (r + 1) =>
    (exteriorProdDividedPowerStructure (exteriorDividedPowerStructure r)).transport
      (ExteriorAlgebra.mapAlgEquiv (finSuccLinearEquiv R r))
      (fun m x => mem_grade_iff_of_mapsTo (exteriorGrade R ((Fin r → R) × R))
        (exteriorGrade R (Fin (r + 1) → R))
        (ExteriorAlgebra.mapAlgEquiv (finSuccLinearEquiv R r))
        (fun _ _ h => ExteriorAlgebra.map_mem_exteriorPower _ h) m x)

/-- The divided powers on the exterior algebra of the zero module. -/
public theorem exteriorDividedPowerStructure_zero :
    exteriorDividedPowerStructure R 0 =
      dividedPowerStructureOfPositiveEvenPartEqBot (exteriorGrade R (Fin 0 → R))
        (positiveEvenPart_exteriorGrade_eq_bot R (Fin 0 → R)) := rfl

/-- The divided powers on `⋀[R] (Fin (r + 1) → R)` are those of `⋀[R] ((Fin r → R) × R)`,
transported along the splitting off of the last coordinate. -/
public theorem exteriorDividedPowerStructure_succ (r : ℕ) :
    exteriorDividedPowerStructure R (r + 1) =
      (exteriorProdDividedPowerStructure (exteriorDividedPowerStructure R r)).transport
        (ExteriorAlgebra.mapAlgEquiv (finSuccLinearEquiv R r))
        (fun m x => mem_grade_iff_of_mapsTo (exteriorGrade R ((Fin r → R) × R))
          (exteriorGrade R (Fin (r + 1) → R))
          (ExteriorAlgebra.mapAlgEquiv (finSuccLinearEquiv R r))
          (fun _ _ h => ExteriorAlgebra.map_mem_exteriorPower _ h) m x) := rfl

end Fin

end DividedPowers.TateResolution

end
