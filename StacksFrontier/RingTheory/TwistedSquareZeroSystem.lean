module

public import StacksFrontier.LinearAlgebra.TwistedCoherentLimit
public import StacksFrontier.RingTheory.Nilpotent.Ideal
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The twisted system of square-zero extensions

This file turns the twisted system of
`StacksFrontier.LinearAlgebra.TwistedCoherentLimit` into the two systems of rings which present the
counterexample of Stacks 0CBE — the second sense of the warning of Stacks 0AN7, that the source
of a representable morphism of affine formal algebraic spaces whose target is McQuillan need not
itself be McQuillan.

Over the index `I` of that file, the stage rings `StageRing b = ℚ ⊕ Stage b` built there are the
stages of the **target**, and `Lam I = ℚ ⊕ (I →₀ ℚ)` is one fixed ring surjecting compatibly
onto all of them: that is McQuillan's criterion for the target, and it needs nothing about the
twist.

The **source** is presented by the dual numbers `DualStage b = StageRing b ⊕ StageRing b` over
each stage ring. Its transition map is the untwisted `stageRingMap` on the ring component and
the twisted `twMap` on the module component. Four facts make that legitimate and are proved
here:

* `twMap_mul` — the twisted map is semilinear over the untwisted ring map, so the pair of the two
  is a ring homomorphism `dualMap`;
* `dualMap_comp` — those ring homomorphisms compose, which is the cocycle identity of the twist;
* `twMap_eq_zero_iff` — the twisted map vanishes exactly on the kernel of the untwisted one,
  which with `twMap_surjective` says `M_b = M_a / J_b M_a`: the ring-level form of
  representability;
* `nilpotent_ker_dualMap` — a transition of the source system has square-zero kernel, so the
  induced morphism of spectra is a thickening.

## Main definitions

* `TrivSqZeroExt.mapRingHom`: a linear map of modules induces a ring homomorphism of their
  trivial square-zero extensions.
* `Stacks.Coherent.Lam`, `Stacks.Coherent.DualStage`: the fixed presenting ring of the target and
  the stage rings of the source.
* `Stacks.Coherent.lamProj`, `Stacks.Coherent.stageRingMap`, `Stacks.Coherent.dualMap`: the
  surjection from the fixed ring, the transition of the target system and the transition of the
  source system.
* `Stacks.Coherent.DualSection`: a compatible family for the source system.

## Main results

* `Stacks.Coherent.lamProj_surjective` and `Stacks.Coherent.stageRingMap_comp_lamProj`: one fixed
  ring surjects compatibly onto every stage of the target.
* `Stacks.Coherent.nilpotent_ker_stageRingMap` and `Stacks.Coherent.nilpotent_ker_dualMap`: the
  transitions of both systems have square-zero kernels.
* `Stacks.Coherent.twMap_mul`, `Stacks.Coherent.dualMap_comp`,
  `Stacks.Coherent.dualMap_surjective` and `Stacks.Coherent.mem_ker_dualMap_iff`: the source
  system is an inverse system of surjections, and each stage is the previous one modulo the
  ideal of the target, which is representability.
* `Stacks.Coherent.not_surjective_dualSection`: **no projection out of the limit of the source
  system is surjective** — the source is not McQuillan.

## Implementation notes

`TrivSqZeroExt R M` is by definition `R × M`, so a stage of the twisted system *is* a stage
ring and `twMap` is reused verbatim as the module component of `dualMap`; nothing is
transported. What has to be checked is semilinearity, and `twMap_mul` is that check: both sides
have first component the product of the first components, and on second components the twist
contributes the product of the first components times the cocycle either way.

Every nilpotency statement reduces to `TrivSqZeroExt.mul_eq_zero_of_fst_eq_zero`: two elements
of a trivial square-zero extension whose first components vanish multiply to zero. Each kernel
in sight consists of such elements, which is why each is square zero and not merely locally
nilpotent.

The non-surjectivity of the source's limit projections is inherited from the twisted system
rather than reproved: the second components of a compatible family of dual numbers are a
compatible family for the twisted system, and `TrivSqZeroExt.inr` puts an arbitrary element of a
stage into the second component, so surjectivity would descend.
-/

@[expose] public noncomputable section

namespace TrivSqZeroExt

universe u v w

/-- Two elements of a trivial square-zero extension whose first components vanish multiply to
zero. -/
@[ega "0 18.2.3" "square-zero kernel of f"]
theorem mul_eq_zero_of_fst_eq_zero {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M]
    [Module R M] [Module Rᵐᵒᵖ M] {x y : TrivSqZeroExt R M} (hx : x.fst = 0) (hy : y.fst = 0) :
    x * y = 0 := by
  refine TrivSqZeroExt.ext ?_ ?_
  · rw [fst_mul, hx, zero_mul, fst_zero]
  · rw [snd_mul, hx, hy, zero_smul, MulOpposite.op_zero, zero_smul, add_zero, snd_zero]

variable {R : Type u} {M : Type v} {N : Type w} [CommRing R] [AddCommGroup M] [AddCommGroup N]
  [Module R M] [Module R N] [Module Rᵐᵒᵖ M] [Module Rᵐᵒᵖ N] [IsCentralScalar R M]
  [IsCentralScalar R N]

/-- The underlying function of `TrivSqZeroExt.mapRingHom`: apply the linear map to the module
component and leave the ring component alone. -/
def mapFun (f : M →ₗ[R] N) (x : TrivSqZeroExt R M) : TrivSqZeroExt R N :=
  inl x.fst + inr (f x.snd)

omit [Module Rᵐᵒᵖ M] [Module Rᵐᵒᵖ N] [IsCentralScalar R M] [IsCentralScalar R N] in
/-- The ring component of `TrivSqZeroExt.mapFun f x` is that of `x`. -/
@[simp]
theorem fst_mapFun (f : M →ₗ[R] N) (x : TrivSqZeroExt R M) : (mapFun f x).fst = x.fst := by
  rw [mapFun, fst_add, fst_inl, fst_inr, add_zero]

omit [Module Rᵐᵒᵖ M] [Module Rᵐᵒᵖ N] [IsCentralScalar R M] [IsCentralScalar R N] in
/-- The module component of `TrivSqZeroExt.mapFun f x` is `f` applied to that of `x`. -/
@[simp]
theorem snd_mapFun (f : M →ₗ[R] N) (x : TrivSqZeroExt R M) : (mapFun f x).snd = f x.snd := by
  rw [mapFun, snd_add, snd_inl, snd_inr, zero_add]

/-- A linear map of modules induces a ring homomorphism of their trivial square-zero extensions,
acting as the identity on the ring component. -/
@[ega "0 18.2.9"]
def mapRingHom (f : M →ₗ[R] N) : TrivSqZeroExt R M →+* TrivSqZeroExt R N where
  toFun := mapFun f
  map_one' := TrivSqZeroExt.ext (by rw [fst_mapFun, fst_one, fst_one])
    (by rw [snd_mapFun, snd_one, map_zero, snd_one])
  map_mul' x y := TrivSqZeroExt.ext
    (by rw [fst_mapFun, fst_mul, fst_mul, fst_mapFun, fst_mapFun])
    (by
      rw [snd_mapFun, snd_mul, snd_mul, fst_mapFun, fst_mapFun, snd_mapFun, snd_mapFun, map_add,
        op_smul_eq_smul, op_smul_eq_smul, map_smul, map_smul])
  map_zero' := TrivSqZeroExt.ext (by rw [fst_mapFun, fst_zero, fst_zero])
    (by rw [snd_mapFun, snd_zero, map_zero, snd_zero])
  map_add' x y := TrivSqZeroExt.ext
    (by rw [fst_mapFun, fst_add, fst_add, fst_mapFun, fst_mapFun])
    (by rw [snd_mapFun, snd_add, snd_add, snd_mapFun, snd_mapFun, map_add])

/-- The ring component of `TrivSqZeroExt.mapRingHom f x` is that of `x`. -/
@[simp, ega "0 18.2.9" "partial"]
theorem fst_mapRingHom (f : M →ₗ[R] N) (x : TrivSqZeroExt R M) :
    (mapRingHom f x).fst = x.fst := fst_mapFun f x

/-- The module component of `TrivSqZeroExt.mapRingHom f x` is `f` applied to that of `x`. -/
@[simp, ega "0 18.2.9" "partial"]
theorem snd_mapRingHom (f : M →ₗ[R] N) (x : TrivSqZeroExt R M) :
    (mapRingHom f x).snd = f x.snd := snd_mapFun f x

/-- The induced ring homomorphism is surjective when the linear map is. -/
theorem surjective_mapRingHom {f : M →ₗ[R] N} (hf : Function.Surjective f) :
    Function.Surjective (mapRingHom f) := by
  intro y
  obtain ⟨m, hm⟩ := hf y.snd
  refine ⟨inl y.fst + inr m, TrivSqZeroExt.ext ?_ ?_⟩
  · rw [fst_mapRingHom, fst_add, fst_inl, fst_inr, add_zero]
  · rw [snd_mapRingHom, snd_add, snd_inl, snd_inr, zero_add, hm]

end TrivSqZeroExt

namespace Stacks.Coherent

open TrivSqZeroExt

universe u

variable {I : Type u} [LinearOrder I] [WellFoundedLT I]

/-! ### The target: one fixed ring surjecting onto every stage -/

/-- The fixed presenting ring of the target: the square-zero extension of `ℚ` by the whole fixed
space. -/
abbrev Lam (I : Type u) [LinearOrder I] [WellFoundedLT I] := TrivSqZeroExt ℚ (Amb I)

/-- The surjection of the fixed presenting ring onto a stage ring. -/
def lamProj (b : I) : Lam I →+* StageRing b := mapRingHom (van b).mkQ

/-- The transition map of the target system, untwisted. -/
def stageRingMap {a b : I} (h : b ≤ a) : StageRing a →+* StageRing b := mapRingHom (stageMap h)

omit [WellFoundedLT I] in
/-- The ring component of `stageRingMap h x` is that of `x`. -/
@[simp]
theorem fst_stageRingMap {a b : I} (h : b ≤ a) (x : StageRing a) :
    (stageRingMap h x).fst = x.fst := fst_mapRingHom _ x

omit [WellFoundedLT I] in
/-- The module component of `stageRingMap h x` is `stageMap h` applied to that of `x`. -/
@[simp]
theorem snd_stageRingMap {a b : I} (h : b ≤ a) (x : StageRing a) :
    (stageRingMap h x).snd = stageMap h x.snd := snd_mapRingHom _ x

/-- The fixed presenting ring surjects onto every stage ring. -/
theorem lamProj_surjective (b : I) : Function.Surjective (lamProj b) :=
  surjective_mapRingHom (van b).mkQ_surjective

omit [WellFoundedLT I] in
/-- The transition maps of the target system are surjective. -/
theorem stageRingMap_surjective {a b : I} (h : b ≤ a) : Function.Surjective (stageRingMap h) :=
  surjective_mapRingHom (stageMap_surjective h)

/-- **The surjections from the fixed ring are compatible.** With `lamProj_surjective` this is
McQuillan's criterion for the target: one fixed ring surjects compatibly onto every stage of its
presentation. -/
theorem stageRingMap_comp_lamProj {a b : I} (h : b ≤ a) (x : Lam I) :
    stageRingMap h (lamProj a x) = lamProj b x := by
  refine TrivSqZeroExt.ext ?_ ?_
  · rw [fst_stageRingMap, lamProj, lamProj, fst_mapRingHom, fst_mapRingHom]
  · rw [snd_stageRingMap, lamProj, lamProj, snd_mapRingHom, snd_mapRingHom, stageMap_mk]

omit [WellFoundedLT I] in
/-- The transition maps of the target system compose. -/
theorem stageRingMap_comp {a b c : I} (hab : b ≤ a) (hbc : c ≤ b) (x : StageRing a) :
    stageRingMap hbc (stageRingMap hab x) = stageRingMap (hbc.trans hab) x := by
  refine TrivSqZeroExt.ext ?_ ?_
  · rw [fst_stageRingMap, fst_stageRingMap, fst_stageRingMap]
  · rw [snd_stageRingMap, snd_stageRingMap, snd_stageRingMap, stageMap_comp]

omit [WellFoundedLT I] in
/-- The transition of the target system along the identity is the identity. -/
@[simp]
theorem stageRingMap_refl {a : I} (x : StageRing a) : stageRingMap (le_refl a) x = x := by
  refine TrivSqZeroExt.ext ?_ ?_
  · rw [fst_stageRingMap]
  · rw [snd_stageRingMap, stageMap_refl]

omit [WellFoundedLT I] in
/-- An element of the kernel of a transition of the target system has vanishing ring
component. -/
theorem fst_eq_zero_of_mem_ker_stageRingMap {a b : I} {h : b ≤ a} {x : StageRing a}
    (hx : x ∈ RingHom.ker (stageRingMap h)) : x.fst = 0 := by
  have hz := RingHom.mem_ker.mp hx
  rw [← fst_stageRingMap h x, hz, fst_zero]

omit [WellFoundedLT I] in
/-- **Two elements killed by a transition of the target system multiply to zero.** -/
theorem mul_eq_zero_of_stageRingMap_eq_zero {a b : I} (h : b ≤ a) (x y : StageRing a)
    (hx : stageRingMap h x = 0) (hy : stageRingMap h y = 0) : x * y = 0 := by
  exact mul_eq_zero_of_fst_eq_zero (fst_eq_zero_of_mem_ker_stageRingMap (RingHom.mem_ker.mpr hx))
    (fst_eq_zero_of_mem_ker_stageRingMap (RingHom.mem_ker.mpr hy))

/-- The kernel of a ring homomorphism is square zero if any two elements of it multiply to zero. -/
private theorem nilpotent_ker_of_mul_eq_zero {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : ∀ x y, f x = 0 → f y = 0 → x * y = 0) : Ideal.Nilpotent (RingHom.ker f) := by
  refine ⟨2, le_antisymm ?_ bot_le⟩
  rw [pow_two]
  refine Ideal.mul_le.mpr fun r hr s hs ↦ ?_
  rw [Ideal.mem_bot]
  exact hf r s (RingHom.mem_ker.mp hr) (RingHom.mem_ker.mp hs)

omit [WellFoundedLT I] in
/-- **The transitions of the target system have square-zero kernels.** -/
theorem nilpotent_ker_stageRingMap {a b : I} (h : b ≤ a) :
    Ideal.Nilpotent (RingHom.ker (stageRingMap h)) :=
  nilpotent_ker_of_mul_eq_zero _ (mul_eq_zero_of_stageRingMap_eq_zero h)

omit [WellFoundedLT I] in
/-- The transitions of the target system have locally nilpotent kernels. -/
theorem locallyNilpotent_ker_stageRingMap {a b : I} (h : b ≤ a) :
    (RingHom.ker (stageRingMap h)).LocallyNilpotent :=
  (nilpotent_ker_stageRingMap h).locallyNilpotent

/-! ### The twisted map is semilinear -/

/-- **The twisted map is semilinear over the untwisted ring map.** -/
theorem twMap_mul (hcnt : ∀ a : I, (Set.Iio a).Countable) {a b : I} (h : b ≤ a)
    (s m : StageRing a) :
    twMap hcnt h (s * m) = stageRingMap h s * twMap hcnt h m := by
  refine TrivSqZeroExt.ext ?_ ?_
  · rw [twMap_fst, fst_mul, fst_mul, fst_stageRingMap, twMap_fst]
  · rw [twMap_snd, snd_mul, snd_mul, fst_mul, fst_stageRingMap, snd_stageRingMap, twMap_fst,
      twMap_snd, op_smul_eq_smul, op_smul_eq_smul, map_add, map_smul,
      map_smul, smul_add, smul_smul, add_right_comm]

/-- The twisted map vanishes at zero. -/
@[simp]
theorem twMap_zero (hcnt : ∀ a : I, (Set.Iio a).Countable) {a b : I} (h : b ≤ a) :
    twMap hcnt h (0 : StageRing a) = 0 := by
  refine TrivSqZeroExt.ext ?_ ?_
  · rw [twMap_fst, fst_zero, fst_zero]
  · rw [twMap_snd, snd_zero, map_zero, fst_zero, zero_smul, add_zero, snd_zero]

/-- The twisted map is additive. -/
theorem twMap_add (hcnt : ∀ a : I, (Set.Iio a).Countable) {a b : I} (h : b ≤ a)
    (x y : StageRing a) :
    twMap hcnt h (x + y) = twMap hcnt h x + twMap hcnt h y := by
  refine TrivSqZeroExt.ext ?_ ?_
  · rw [twMap_fst, fst_add, fst_add, twMap_fst, twMap_fst]
  · rw [twMap_snd, snd_add, snd_add, fst_add, twMap_snd, twMap_snd, map_add, add_smul,
      add_add_add_comm]

/-- **The twisted map vanishes exactly on the kernel of the untwisted one.** With
`Stacks.Coherent.twMap_surjective` this says that a stage of the source system is the previous
one modulo the ideal cutting out the stage of the target, which is representability at the level
of rings. -/
theorem twMap_eq_zero_iff (hcnt : ∀ a : I, (Set.Iio a).Countable) {a b : I} (h : b ≤ a)
    (m : StageRing a) :
    twMap hcnt h m = 0 ↔ m ∈ RingHom.ker (stageRingMap h) := by
  constructor
  · intro hm
    have hfst : m.fst = 0 := by rw [← twMap_fst hcnt h m, hm, fst_zero]
    have hsnd : stageMap h m.snd = 0 := by
      have hz : (twMap hcnt h m).snd = 0 := by rw [hm, snd_zero]
      rwa [twMap_snd, hfst, zero_smul, add_zero] at hz
    exact RingHom.mem_ker.mpr (TrivSqZeroExt.ext (by rw [fst_stageRingMap, hfst, fst_zero])
      (by rw [snd_stageRingMap, hsnd, snd_zero]))
  · intro hm
    have hfst : m.fst = 0 := fst_eq_zero_of_mem_ker_stageRingMap hm
    have hsnd : stageMap h m.snd = 0 := by
      rw [← snd_stageRingMap h m, RingHom.mem_ker.mp hm, snd_zero]
    refine TrivSqZeroExt.ext ?_ ?_
    · rw [twMap_fst, hfst, fst_zero]
    · rw [twMap_snd, hsnd, hfst, zero_smul, add_zero, snd_zero]

/-- **The twist of `1`.** The twisted map does not preserve `1`: it sends it to `1` plus the
cocycle in the square-zero part. -/
theorem twMap_one (hcnt : ∀ a : I, (Set.Iio a).Countable) {a b : I} (h : b ≤ a) :
    twMap hcnt h (1 : StageRing a)
      = 1 + TrivSqZeroExt.inr ((van b).mkQ (cocy hcnt h)) := by
  refine TrivSqZeroExt.ext ?_ ?_
  · rw [twMap_fst, fst_one, fst_add, fst_one, fst_inr, add_zero]
  · rw [twMap_snd, snd_one, map_zero, fst_one, one_smul, zero_add, snd_add, snd_one, snd_inr,
      zero_add]

/-- **The twist of `1` is a unit.** -/
theorem isUnit_twMap_one (hcnt : ∀ a : I, (Set.Iio a).Countable) {a b : I} (h : b ≤ a) :
    IsUnit (twMap hcnt h (1 : StageRing a)) := by
  rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, twMap_fst, fst_one]
  exact isUnit_one

/-! ### The source system -/

/-- A stage ring of the source: the dual numbers over a stage ring of the target, that is the
stage ring with a square-zero copy of itself adjoined. -/
abbrev DualStage (b : I) := TrivSqZeroExt (StageRing b) (StageRing b)

/-- The underlying function of `dualMap`: `stageRingMap` on the ring component and `twMap` on
the module component. -/
def dualFun (hcnt : ∀ a : I, (Set.Iio a).Countable) {a b : I} (h : b ≤ a) (x : DualStage a) :
    DualStage b :=
  TrivSqZeroExt.inl (stageRingMap h x.fst) + TrivSqZeroExt.inr (twMap hcnt h x.snd)

/-- The ring component of `dualFun hcnt h x` is `stageRingMap h` applied to that of `x`. -/
@[simp]
theorem fst_dualFun (hcnt : ∀ a : I, (Set.Iio a).Countable) {a b : I} (h : b ≤ a)
    (x : DualStage a) : (dualFun hcnt h x).fst = stageRingMap h x.fst := by
  rw [dualFun, fst_add, fst_inl, fst_inr, add_zero]

/-- The module component of `dualFun hcnt h x` is `twMap hcnt h` applied to that of `x`. -/
@[simp]
theorem snd_dualFun (hcnt : ∀ a : I, (Set.Iio a).Countable) {a b : I} (h : b ≤ a)
    (x : DualStage a) : (dualFun hcnt h x).snd = twMap hcnt h x.snd := by
  rw [dualFun, snd_add, snd_inl, snd_inr, zero_add]

/-- The transition map of the source system: untwisted on the ring component, twisted on the
module component. -/
def dualMap (hcnt : ∀ a : I, (Set.Iio a).Countable) {a b : I} (h : b ≤ a) :
    DualStage a →+* DualStage b where
  toFun := dualFun hcnt h
  map_one' := TrivSqZeroExt.ext (by rw [fst_dualFun, fst_one, fst_one, map_one])
    (by rw [snd_dualFun, snd_one, twMap_zero, snd_one])
  map_mul' x y := TrivSqZeroExt.ext
    (by rw [fst_dualFun, fst_mul, fst_mul, fst_dualFun, fst_dualFun, map_mul])
    (by
      rw [snd_dualFun, snd_mul, snd_mul, fst_dualFun, fst_dualFun, snd_dualFun, snd_dualFun,
        smul_eq_mul, smul_eq_mul, op_smul_eq_smul, op_smul_eq_smul,
        smul_eq_mul, smul_eq_mul, twMap_add, twMap_mul, twMap_mul])
  map_zero' := TrivSqZeroExt.ext (by rw [fst_dualFun, fst_zero, fst_zero, map_zero])
    (by rw [snd_dualFun, snd_zero, twMap_zero, snd_zero])
  map_add' x y := TrivSqZeroExt.ext
    (by rw [fst_dualFun, fst_add, fst_add, fst_dualFun, fst_dualFun, map_add])
    (by rw [snd_dualFun, snd_add, snd_add, snd_dualFun, snd_dualFun, twMap_add])

/-- The ring component of `dualMap hcnt h x` is `stageRingMap h` applied to that of `x`. -/
@[simp]
theorem fst_dualMap (hcnt : ∀ a : I, (Set.Iio a).Countable) {a b : I} (h : b ≤ a)
    (x : DualStage a) : (dualMap hcnt h x).fst = stageRingMap h x.fst := fst_dualFun hcnt h x

/-- The module component of `dualMap hcnt h x` is `twMap hcnt h` applied to that of `x`. -/
@[simp]
theorem snd_dualMap (hcnt : ∀ a : I, (Set.Iio a).Countable) {a b : I} (h : b ≤ a)
    (x : DualStage a) : (dualMap hcnt h x).snd = twMap hcnt h x.snd := snd_dualFun hcnt h x

/-- A transition of the source system carries the ring component into the ring component: the
twist moves nothing there, since the module component of `TrivSqZeroExt.inl` is zero. -/
@[simp]
theorem dualMap_inl (hcnt : ∀ a : I, (Set.Iio a).Countable) {a b : I} (h : b ≤ a)
    (s : StageRing a) :
    dualMap hcnt h (TrivSqZeroExt.inl s) = TrivSqZeroExt.inl (stageRingMap h s) := by
  refine TrivSqZeroExt.ext ?_ ?_
  · rw [fst_dualMap, fst_inl, fst_inl]
  · rw [snd_dualMap, snd_inl, snd_inl, twMap_zero]

/-- A transition of the source system carries the square-zero part to the square-zero part, by
the twisted map. With `Stacks.Coherent.dualMap_inl` this determines it completely. -/
@[simp]
theorem dualMap_inr (hcnt : ∀ a : I, (Set.Iio a).Countable) {a b : I} (h : b ≤ a)
    (x : StageRing a) :
    dualMap hcnt h (TrivSqZeroExt.inr x) = TrivSqZeroExt.inr (twMap hcnt h x) := by
  refine TrivSqZeroExt.ext ?_ ?_
  · rw [fst_dualMap, fst_inr, map_zero, fst_inr]
  · rw [snd_dualMap, snd_inr, snd_inr]

/-- **The transitions of the source system compose.** On the module component this is the
cocycle identity of the twist. -/
theorem dualMap_comp (hcnt : ∀ a : I, (Set.Iio a).Countable) {a b c : I} (hab : b ≤ a)
    (hbc : c ≤ b) (x : DualStage a) :
    dualMap hcnt hbc (dualMap hcnt hab x) = dualMap hcnt (hbc.trans hab) x := by
  refine TrivSqZeroExt.ext ?_ ?_
  · rw [fst_dualMap, fst_dualMap, fst_dualMap, stageRingMap_comp]
  · rw [snd_dualMap, snd_dualMap, snd_dualMap, twMap_comp]

/-- The transition of the source system along the identity is the identity. -/
@[simp]
theorem dualMap_refl (hcnt : ∀ a : I, (Set.Iio a).Countable) {a : I} (x : DualStage a) :
    dualMap hcnt (le_refl a) x = x := by
  refine TrivSqZeroExt.ext ?_ ?_
  · rw [fst_dualMap, stageRingMap_refl]
  · rw [snd_dualMap, twMap_refl]

/-- The transitions of the source system are surjective. -/
theorem dualMap_surjective (hcnt : ∀ a : I, (Set.Iio a).Countable) {a b : I} (h : b ≤ a) :
    Function.Surjective (dualMap hcnt h) := by
  intro y
  obtain ⟨r, hr⟩ := stageRingMap_surjective h y.fst
  obtain ⟨m, hm⟩ := twMap_surjective hcnt h y.snd
  refine ⟨TrivSqZeroExt.inl r + TrivSqZeroExt.inr m, TrivSqZeroExt.ext ?_ ?_⟩
  · rw [fst_dualMap, fst_add, fst_inl, fst_inr, add_zero, hr]
  · rw [snd_dualMap, snd_add, snd_inl, snd_inr, zero_add, hm]

/-- **A stage of the source is the previous one modulo the ideal of the target.** The kernel of a
transition of the source system consists of the dual numbers both of whose components lie in the
kernel of the corresponding transition of the target, which is that kernel extended to the dual
numbers. With `dualMap_surjective` this is representability at the level of rings. -/
theorem mem_ker_dualMap_iff (hcnt : ∀ a : I, (Set.Iio a).Countable) {a b : I} (h : b ≤ a)
    (x : DualStage a) :
    x ∈ RingHom.ker (dualMap hcnt h) ↔
      x.fst ∈ RingHom.ker (stageRingMap h) ∧ x.snd ∈ RingHom.ker (stageRingMap h) := by
  rw [RingHom.mem_ker]
  constructor
  · intro hx
    refine ⟨RingHom.mem_ker.mpr ?_, (twMap_eq_zero_iff hcnt h x.snd).mp ?_⟩
    · rw [← fst_dualMap hcnt h x, hx, fst_zero]
    · rw [← snd_dualMap hcnt h x, hx, snd_zero]
  · intro ⟨h1, h2⟩
    refine TrivSqZeroExt.ext ?_ ?_
    · rw [fst_dualMap, RingHom.mem_ker.mp h1, fst_zero]
    · rw [snd_dualMap, (twMap_eq_zero_iff hcnt h x.snd).mpr h2, snd_zero]

/-- **Two elements killed by a transition of the source system multiply to zero.** -/
theorem mul_eq_zero_of_dualMap_eq_zero (hcnt : ∀ a : I, (Set.Iio a).Countable) {a b : I}
    (h : b ≤ a) (x y : DualStage a) (hx : dualMap hcnt h x = 0) (hy : dualMap hcnt h y = 0) :
    x * y = 0 := by
  obtain ⟨hx1, hx2⟩ := (mem_ker_dualMap_iff hcnt h x).mp (RingHom.mem_ker.mpr hx)
  obtain ⟨hy1, hy2⟩ := (mem_ker_dualMap_iff hcnt h y).mp (RingHom.mem_ker.mpr hy)
  replace hx1 := RingHom.mem_ker.mp hx1
  replace hy1 := RingHom.mem_ker.mp hy1
  replace hx2 := RingHom.mem_ker.mp hx2
  replace hy2 := RingHom.mem_ker.mp hy2
  refine TrivSqZeroExt.ext ?_ ?_
  · rw [fst_mul, fst_zero]
    exact mul_eq_zero_of_stageRingMap_eq_zero h _ _ hx1 hy1
  · rw [snd_mul, snd_zero, smul_eq_mul, op_smul_eq_smul, smul_eq_mul,
      mul_eq_zero_of_stageRingMap_eq_zero h _ _ hx1 hy2,
      mul_eq_zero_of_stageRingMap_eq_zero h _ _ hy1 hx2, add_zero]

/-- **The transitions of the source system have square-zero kernels**, so the morphisms of
spectra they induce are thickenings. -/
theorem nilpotent_ker_dualMap (hcnt : ∀ a : I, (Set.Iio a).Countable) {a b : I} (h : b ≤ a) :
    Ideal.Nilpotent (RingHom.ker (dualMap hcnt h)) :=
  nilpotent_ker_of_mul_eq_zero _ (mul_eq_zero_of_dualMap_eq_zero hcnt h)

/-- A compatible family for the source system: an element of its inverse limit. -/
abbrev DualSection (hcnt : ∀ a : I, (Set.Iio a).Countable) : Type u :=
  {s : ∀ b : I, DualStage b // ∀ (a b : I) (h : b ≤ a), dualMap hcnt h (s a) = s b}

/-- **No projection out of the limit of the source system is surjective**, so the source of the
morphism fails McQuillan's criterion. -/
theorem not_surjective_dualSection [Uncountable I] (hcnt : ∀ a : I, (Set.Iio a).Countable)
    (b₀ : I) :
    ¬ Function.Surjective (fun s : DualSection hcnt ↦ s.1 b₀) := by
  intro hsurj
  refine not_surjective_twSection hcnt b₀ fun y ↦ ?_
  obtain ⟨s, hs⟩ := hsurj (TrivSqZeroExt.inr y)
  refine ⟨⟨fun b ↦ (s.val b).snd, fun a b h ↦ ?_⟩, ?_⟩
  · exact (snd_dualMap hcnt h (s.val a)).symm.trans (congrArg TrivSqZeroExt.snd (s.property a b h))
  · exact (congrArg TrivSqZeroExt.snd hs).trans (TrivSqZeroExt.snd_inr _ y)

end Stacks.Coherent

end
