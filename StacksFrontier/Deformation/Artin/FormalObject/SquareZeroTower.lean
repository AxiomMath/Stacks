module

public import StacksFrontier.AlgebraicGeometry.Smooth.ThickeningRestriction
public import StacksFrontier.Deformation.Artin.Infinitesimal.TangentFunctor

/-!
# The ring of sequences with a common base in a tower of square-zero thickenings

Let `⋯ → R₂ → R₁ → R₀` be a tower of commutative rings with surjective transition maps, and
write `A = R₀` and `Mₙ = Ker(Rₙ → A)`. Assume each `Mₙ` has square zero, so that it is an
`A`-module. The ring
`R̃ = {(r₀, r₁, r₂, …) ∈ ∏ Rₙ | all rₙ have the same image in A}`
maps onto `A` with kernel `M = ∏ Mₙ`, again of square zero. The *difference map*
`R̃ → A[M]`, `(rₙ) ↦ (r₀, (rₙ₊₁|_{Rₙ} − rₙ)ₙ)` is a surjective ring map whose kernel is the
inverse limit `lim Rₙ`, the sequences with `rₙ₊₁|_{Rₙ} = rₙ`. Hence `lim Rₙ` is the fibre
product `R̃ ×_{A[M]} A`. This is the presentation of the limit used in the proof of
Stacks 0CYF.

## Main definitions

* `Deformation.Artin.SquareZeroTower.toBase` — the composite `Rₙ → R₀`.
* `Deformation.Artin.SquareZeroTower.sameBase` — the ring `R̃`.
* `Deformation.Artin.SquareZeroTower.limit` — the inverse limit, as a subring of `∏ Rₙ`.
* `Deformation.Artin.SquareZeroTower.kernelProduct` — the `A`-module `M = ∏ Mₙ`.
* `Deformation.Artin.SquareZeroTower.difference` — the difference map `R̃ → A[M]`.

## Main results

* `Deformation.Artin.SquareZeroTower.base_surjective`,
  `Deformation.Artin.SquareZeroTower.ker_base_sq` — `R̃ → A` is a square-zero surjection.
* `Deformation.Artin.SquareZeroTower.difference_surjective`,
  `Deformation.Artin.SquareZeroTower.ker_difference_sq` — so is `R̃ → A[M]`.
* `Deformation.Artin.SquareZeroTower.difference_eq_inl_iff` — a sequence of `R̃` has trivial
  difference exactly when it lies in the inverse limit.

## Implementation notes

The tower is indexed by `ℕ` with base `R₀`, where the source indexes from `R₁`. Only the
kernels of the maps to the base are assumed square-zero; this is the case `n = 1` of the
source's assumption that every `Ker(R_m → R_n)` has square zero.

## References

* [Stacks Project, Tag 0CYF](https://stacks.math.columbia.edu/tag/0CYF)
-/

@[expose] public noncomputable section

universe u

namespace Deformation.Artin.SquareZeroTower

variable {R : ℕ → Type u} [∀ n, CommRing (R n)] (f : ∀ n, R (n + 1) →+* R n)

/-- The composite `Rₙ → R₀` of the transition maps. -/
public def toBase : ∀ n, R n →+* R 0
  | 0 => RingHom.id _
  | n + 1 => (toBase n).comp (f n)

@[simp] public theorem toBase_zero (r : R 0) : toBase f 0 r = r := rfl

@[simp] public theorem toBase_succ (n : ℕ) (r : R (n + 1)) :
    toBase f (n + 1) r = toBase f n (f n r) := rfl

/-- With surjective transition maps, every composite `Rₙ → R₀` is surjective. -/
public theorem toBase_surjective (hf : ∀ n, Function.Surjective (f n)) :
    ∀ n, Function.Surjective (toBase f n)
  | 0 => Function.surjective_id
  | n + 1 => (toBase_surjective hf n).comp (hf n)

/-- The ring `R̃` of sequences `(rₙ) ∈ ∏ Rₙ` all of whose terms have the same image in `R₀`. -/
public def sameBase : Subring (∀ n, R n) where
  carrier := {r | ∀ n, toBase f n (r n) = r 0}
  mul_mem' {a b} ha hb n := by
    simp only [Set.mem_setOf_eq, Pi.mul_apply, map_mul] at ha hb ⊢
    rw [ha n, hb n]
  one_mem' n := by simp
  add_mem' {a b} ha hb n := by
    simp only [Set.mem_setOf_eq, Pi.add_apply, map_add] at ha hb ⊢
    rw [ha n, hb n]
  zero_mem' n := by simp
  neg_mem' {a} ha n := by
    simp only [Set.mem_setOf_eq, Pi.neg_apply, map_neg] at ha ⊢
    rw [ha n]

public theorem mem_sameBase {r : ∀ n, R n} : r ∈ sameBase f ↔ ∀ n, toBase f n (r n) = r 0 :=
  Iff.rfl

/-- The inverse limit of the tower, as the subring of compatible sequences of `∏ Rₙ`. -/
public def limit : Subring (∀ n, R n) where
  carrier := {r | ∀ n, f n (r (n + 1)) = r n}
  mul_mem' {a b} ha hb n := by
    simp only [Set.mem_setOf_eq, Pi.mul_apply, map_mul] at ha hb ⊢
    rw [ha n, hb n]
  one_mem' n := by simp
  add_mem' {a b} ha hb n := by
    simp only [Set.mem_setOf_eq, Pi.add_apply, map_add] at ha hb ⊢
    rw [ha n, hb n]
  zero_mem' n := by simp
  neg_mem' {a} ha n := by
    simp only [Set.mem_setOf_eq, Pi.neg_apply, map_neg] at ha ⊢
    rw [ha n]

public theorem mem_limit {r : ∀ n, R n} : r ∈ limit f ↔ ∀ n, f n (r (n + 1)) = r n :=
  Iff.rfl

/-- A compatible sequence has a common image in `R₀`. -/
public theorem limit_le_sameBase : limit f ≤ sameBase f := by
  intro r hr n
  induction n with
  | zero => rfl
  | succ n ih => rw [toBase_succ, hr n, ih]

/-- The map `R̃ → R₀`. -/
public def base : sameBase f →+* R 0 := (Pi.evalRingHom R 0).comp (sameBase f).subtype

/-- The projection `R̃ → Rₙ`. -/
public def proj (n : ℕ) : sameBase f →+* R n := (Pi.evalRingHom R n).comp (sameBase f).subtype

@[simp] public theorem base_apply (r : sameBase f) : base f r = (r : ∀ n, R n) 0 := rfl

@[simp] public theorem proj_apply (n : ℕ) (r : sameBase f) :
    proj f n r = (r : ∀ n, R n) n := rfl

/-- Each projection `R̃ → Rₙ` lies over the base. -/
public theorem toBase_comp_proj (n : ℕ) : (toBase f n).comp (proj f n) = base f :=
  RingHom.ext fun r => r.2 n

/-- `R̃ → R₀` is surjective. -/
public theorem base_surjective (hf : ∀ n, Function.Surjective (f n)) :
    Function.Surjective (base f) := by
  intro a
  choose s hs using fun n => toBase_surjective f hf n a
  exact ⟨⟨s, fun n => (hs n).trans (hs 0).symm⟩, hs 0⟩

public theorem mem_ker_base {r : sameBase f} :
    r ∈ RingHom.ker (base f) ↔ ∀ n, (r : ∀ n, R n) n ∈ RingHom.ker (toBase f n) := by
  rw [RingHom.mem_ker, base_apply]
  exact ⟨fun h n => by rw [RingHom.mem_ker, r.2 n, h], fun h => h 0⟩

/-- Two elements of a square-zero ideal multiply to zero. -/
public theorem mul_eq_zero_of_sq {T : Type*} [CommRing T] {I : Ideal T} (hI : I ^ 2 = ⊥)
    {a b : T} (ha : a ∈ I) (hb : b ∈ I) : a * b = 0 := by
  have h : a * b ∈ I ^ 2 := by
    rw [pow_two]
    exact Ideal.mul_mem_mul ha hb
  rwa [hI] at h

/-! ### Twisting by the kernel of a square-zero surjection -/

section Twist

variable {D A : Type u} [CommRing D] [CommRing A] (π : D →+* A) (hπ : Function.Surjective π)
  (hsq : RingHom.ker π ^ 2 = ⊥)

/-- The kernel of a square-zero surjection `π : D → A`, as an `A`-module. -/
public def kerObj : ModuleCat.{u} A :=
  letI := Stacks.Smooth.kerModule hπ hsq
  ModuleCat.of A (RingHom.ker π)

/-- The element of `D` underlying an element of the kernel module. -/
public def kerVal (m : kerObj π hπ hsq) : D := (show RingHom.ker π from m).1

/-- The element of the kernel module given by an element of `D` killed by `π`. -/
public def kerMk (d : D) (hd : π d = 0) : kerObj π hπ hsq :=
  show RingHom.ker π from ⟨d, hd⟩

@[simp] public theorem kerVal_kerMk (d : D) (hd : π d = 0) :
    kerVal π hπ hsq (kerMk π hπ hsq d hd) = d := rfl

public theorem kerVal_injective : Function.Injective (kerVal π hπ hsq) :=
  fun _ _ h => Subtype.ext h

public theorem map_kerVal (m : kerObj π hπ hsq) : π (kerVal π hπ hsq m) = 0 :=
  (show RingHom.ker π from m).2

@[simp] public theorem kerVal_add (m m' : kerObj π hπ hsq) :
    kerVal π hπ hsq (m + m') = kerVal π hπ hsq m + kerVal π hπ hsq m' := rfl

@[simp] public theorem kerVal_zero : kerVal π hπ hsq 0 = 0 := rfl

public theorem kerVal_smul (d : D) (m : kerObj π hπ hsq) :
    kerVal π hπ hsq (π d • m) = d * kerVal π hπ hsq m := by
  let := Stacks.Smooth.kerModule hπ hsq
  exact congrArg Subtype.val (Stacks.Smooth.kerModule_smul hπ hsq d (show RingHom.ker π from m))

public theorem kerVal_op_smul (d : D) (m : kerObj π hπ hsq) :
    kerVal π hπ hsq (MulOpposite.op (π d) • m) = d * kerVal π hπ hsq m :=
  kerVal_smul π hπ hsq d m

public theorem sub_mem_ker {s t : D} (h : π s = π t) : π (s - t) = 0 := by
  rw [map_sub, h, sub_self]

/-- The difference map `D ×_A D → A[I]`, `(s, t) ↦ (s̄, s − t)`, for the kernel `I` of a
square-zero surjection `π : D → A`. -/
public def diffHom : π.pullback π →+* squareZeroRing A (kerObj π hπ hsq) where
  toFun z := (π z.1.1, kerMk π hπ hsq (z.1.1 - z.1.2) (sub_mem_ker π z.2))
  map_one' := by
    refine Prod.ext (map_one π) (kerVal_injective π hπ hsq ?_)
    change (1 : D) - 1 = 0
    rw [sub_self]
  map_mul' z w := by
    refine Prod.ext (map_mul π _ _) (kerVal_injective π hπ hsq ?_)
    change z.1.1 * w.1.1 - z.1.2 * w.1.2 =
      kerVal π hπ hsq (π z.1.1 • kerMk π hπ hsq (w.1.1 - w.1.2) (sub_mem_ker π w.2) +
        MulOpposite.op (π w.1.1) • kerMk π hπ hsq (z.1.1 - z.1.2) (sub_mem_ker π z.2))
    rw [kerVal_add, kerVal_smul, kerVal_op_smul, kerVal_kerMk, kerVal_kerMk]
    have h := mul_eq_zero_of_sq hsq (a := z.1.1 - z.1.2) (b := w.1.1 - w.1.2)
      (sub_mem_ker π z.2) (sub_mem_ker π w.2)
    linear_combination -h
  map_zero' := by
    refine Prod.ext (map_zero π) (kerVal_injective π hπ hsq ?_)
    change (0 : D) - 0 = 0
    rw [sub_self]
  map_add' z w := by
    refine Prod.ext (map_add π _ _) (kerVal_injective π hπ hsq ?_)
    change (z.1.1 + w.1.1) - (z.1.2 + w.1.2) = (z.1.1 - z.1.2) + (w.1.1 - w.1.2)
    ring

@[simp] public theorem diffHom_fst (z : π.pullback π) : (diffHom π hπ hsq z).fst = π z.1.1 := rfl

@[simp] public theorem diffHom_snd (z : π.pullback π) :
    kerVal π hπ hsq (diffHom π hπ hsq z).snd = z.1.1 - z.1.2 := rfl

/-- The map `D ×_A D → D ×_A A[I]`, `(s, t) ↦ (s, (s̄, t − s))`. -/
public def untwistHom :
    π.pullback π →+* π.pullback (TrivSqZeroExt.fstHom A A (kerObj π hπ hsq)).toRingHom where
  toFun z := ⟨(z.1.1, (π z.1.1, kerMk π hπ hsq (z.1.2 - z.1.1) (sub_mem_ker π z.2.symm))), rfl⟩
  map_one' := by
    refine Subtype.ext (Prod.ext rfl (Prod.ext (map_one π) (kerVal_injective π hπ hsq ?_)))
    change (1 : D) - 1 = 0
    rw [sub_self]
  map_mul' z w := by
    refine Subtype.ext (Prod.ext rfl (Prod.ext (map_mul π _ _) (kerVal_injective π hπ hsq ?_)))
    change z.1.2 * w.1.2 - z.1.1 * w.1.1 =
      kerVal π hπ hsq (π z.1.1 • kerMk π hπ hsq (w.1.2 - w.1.1) (sub_mem_ker π w.2.symm) +
        MulOpposite.op (π w.1.1) • kerMk π hπ hsq (z.1.2 - z.1.1) (sub_mem_ker π z.2.symm))
    rw [kerVal_add, kerVal_smul, kerVal_op_smul, kerVal_kerMk, kerVal_kerMk]
    have h := mul_eq_zero_of_sq hsq (a := z.1.2 - z.1.1) (b := w.1.2 - w.1.1)
      (sub_mem_ker π z.2.symm) (sub_mem_ker π w.2.symm)
    linear_combination h
  map_zero' := by
    refine Subtype.ext (Prod.ext rfl (Prod.ext (map_zero π) (kerVal_injective π hπ hsq ?_)))
    change (0 : D) - 0 = 0
    rw [sub_self]
  map_add' z w := by
    refine Subtype.ext (Prod.ext rfl (Prod.ext (map_add π _ _) (kerVal_injective π hπ hsq ?_)))
    change (z.1.2 + w.1.2) - (z.1.1 + w.1.1) = (z.1.2 - z.1.1) + (w.1.2 - w.1.1)
    ring

@[simp] public theorem untwistHom_fst (z : π.pullback π) : (untwistHom π hπ hsq z).1.1 = z.1.1 :=
  rfl

@[simp] public theorem untwistHom_snd_fst (z : π.pullback π) :
    (untwistHom π hπ hsq z).1.2.fst = π z.1.1 := rfl

@[simp] public theorem untwistHom_snd_snd (z : π.pullback π) :
    kerVal π hπ hsq (untwistHom π hπ hsq z).1.2.snd = z.1.2 - z.1.1 := rfl

variable {M : ModuleCat.{u} A} (ι : M →+ D) (hιπ : ∀ m, π (ι m) = 0)
  (hιsmul : ∀ (d : D) (m : M), ι (π d • m) = d * ι m) (hιmul : ∀ m m', ι m * ι m' = 0)

/-- The twisting map `D ×_A A[M] → D`, `(s, (a, m)) ↦ s + ι(m)`, for an additive map
`ι : M → D` into the kernel of `π` which is `A`-linear through `π` and has square zero. -/
public def twistHom : π.pullback (TrivSqZeroExt.fstHom A A M).toRingHom →+* D where
  toFun z := z.1.1 + ι z.1.2.snd
  map_one' := by
    change (1 : D) + ι 0 = 1
    rw [map_zero, add_zero]
  map_mul' z w := by
    have hz : π z.1.1 = z.1.2.fst := z.2
    have hw : π w.1.1 = w.1.2.fst := w.2
    change z.1.1 * w.1.1 + ι (z.1.2.fst • w.1.2.snd + MulOpposite.op w.1.2.fst • z.1.2.snd) =
      (z.1.1 + ι z.1.2.snd) * (w.1.1 + ι w.1.2.snd)
    rw [map_add, ← hz, ← hw]
    change z.1.1 * w.1.1 + (ι (π z.1.1 • w.1.2.snd) + ι (π w.1.1 • z.1.2.snd)) = _
    rw [hιsmul, hιsmul]
    have h := hιmul z.1.2.snd w.1.2.snd
    linear_combination -h
  map_zero' := by
    change (0 : D) + ι 0 = 0
    rw [map_zero, add_zero]
  map_add' z w := by
    change (z.1.1 + w.1.1) + ι (z.1.2.snd + w.1.2.snd) =
      (z.1.1 + ι z.1.2.snd) + (w.1.1 + ι w.1.2.snd)
    rw [map_add]
    ring

@[simp] public theorem twistHom_apply (z : π.pullback (TrivSqZeroExt.fstHom A A M).toRingHom) :
    twistHom π ι hιsmul hιmul z = z.1.1 + ι z.1.2.snd := rfl

include hιπ in
/-- Twisting does not change the image in `A`. -/
public theorem map_twistHom (z : π.pullback (TrivSqZeroExt.fstHom A A M).toRingHom) :
    π (twistHom π ι hιsmul hιmul z) = π z.1.1 := by
  rw [twistHom_apply, map_add, hιπ, add_zero]

/-- Twisting by zero is the first projection. -/
public theorem twistHom_eq_of_snd_eq_zero
    (z : π.pullback (TrivSqZeroExt.fstHom A A M).toRingHom) (h : z.1.2.snd = 0) :
    twistHom π ι hιsmul hιmul z = z.1.1 := by
  rw [twistHom_apply, h, map_zero, add_zero]

end Twist

/-- The kernel `∏ Mₙ` of `R̃ → R₀` has square zero. -/
public theorem ker_base_sq (hsq : ∀ n, RingHom.ker (toBase f n) ^ 2 = ⊥) :
    RingHom.ker (base f) ^ 2 = ⊥ := by
  rw [eq_bot_iff, pow_two, Ideal.mul_le]
  intro a ha b hb
  rw [Ideal.mem_bot]
  refine Subtype.ext (funext fun n => ?_)
  exact mul_eq_zero_of_sq (hsq n) ((mem_ker_base f).1 ha n) ((mem_ker_base f).1 hb n)

variable (hf : ∀ n, Function.Surjective (f n)) (hsq : ∀ n, RingHom.ker (toBase f n) ^ 2 = ⊥)

/-- The `R₀`-module `Mₙ = Ker(Rₙ → R₀)`. -/
@[instance_reducible]
public def kernelModule (n : ℕ) : Module (R 0) (RingHom.ker (toBase f n)) :=
  Stacks.Smooth.kerModule (toBase_surjective f hf n) (hsq n)

/-- The `R₀`-module `M = ∏ Mₙ`. -/
public def kernelProduct : ModuleCat.{u} (R 0) :=
  letI := kernelModule f hf hsq
  ModuleCat.of (R 0) (∀ n, RingHom.ker (toBase f n))

/-- The difference `rₙ₊₁|_{Rₙ} − rₙ` of consecutive terms of a sequence of `R̃`, an element
of `Mₙ`. -/
public def step (r : sameBase f) (n : ℕ) : RingHom.ker (toBase f n) :=
  ⟨f n ((r : ∀ n, R n) (n + 1)) - (r : ∀ n, R n) n, by
    rw [RingHom.mem_ker, map_sub, ← toBase_succ, r.2 (n + 1), r.2 n, sub_self]⟩

@[simp] public theorem step_coe (r : sameBase f) (n : ℕ) :
    (step f r n : R n) = f n ((r : ∀ n, R n) (n + 1)) - (r : ∀ n, R n) n := rfl

private theorem smul_kernel (n : ℕ) (r : sameBase f) (m : RingHom.ker (toBase f n)) :
    letI := kernelModule f hf hsq n
    ((((r : ∀ n, R n) 0 • m : RingHom.ker (toBase f n)) : R n)) = (r : ∀ n, R n) n * m := by
  let := kernelModule f hf hsq n
  have h := Stacks.Smooth.kerModule_smul (toBase_surjective f hf n) (hsq n)
    ((r : ∀ n, R n) n) m
  rw [r.2 n] at h
  exact congrArg Subtype.val h

/-- The difference map `R̃ → A[M]`, `(rₙ) ↦ (r₀, (rₙ₊₁|_{Rₙ} − rₙ)ₙ)`. -/
public def difference : sameBase f →+* squareZeroRing (R 0) (kernelProduct f hf hsq) where
  toFun r := ((r : ∀ n, R n) 0, step f r)
  map_one' := by
    refine Prod.ext rfl (funext fun n => Subtype.ext ?_)
    change f n 1 - 1 = (0 : R n)
    rw [map_one, sub_self]
  map_mul' a b := by
    let := kernelModule f hf hsq
    refine Prod.ext rfl (funext fun n => Subtype.ext ?_)
    change (step f (a * b) n : R n) =
      ((((a : ∀ n, R n) 0 • step f b n : RingHom.ker (toBase f n)) : R n)) +
        ((((b : ∀ n, R n) 0 • step f a n : RingHom.ker (toBase f n)) : R n))
    rw [smul_kernel f hf hsq n a, smul_kernel f hf hsq n b]
    have hzero := mul_eq_zero_of_sq (hsq n) (step f a n).2 (step f b n).2
    simp only [step_coe] at hzero ⊢
    change f n ((a : ∀ n, R n) (n + 1) * (b : ∀ n, R n) (n + 1)) -
      (a : ∀ n, R n) n * (b : ∀ n, R n) n = _
    rw [map_mul]
    linear_combination hzero
  map_zero' := by
    refine Prod.ext rfl (funext fun n => Subtype.ext ?_)
    change f n 0 - 0 = (0 : R n)
    rw [map_zero, sub_self]
  map_add' a b := by
    refine Prod.ext rfl (funext fun n => Subtype.ext ?_)
    change f n ((a : ∀ n, R n) (n + 1) + (b : ∀ n, R n) (n + 1)) -
      ((a : ∀ n, R n) n + (b : ∀ n, R n) n) =
      (f n ((a : ∀ n, R n) (n + 1)) - (a : ∀ n, R n) n) +
        (f n ((b : ∀ n, R n) (n + 1)) - (b : ∀ n, R n) n)
    rw [map_add]
    ring

@[simp] public theorem difference_fst (r : sameBase f) :
    (difference f hf hsq r).fst = (r : ∀ n, R n) 0 := rfl

@[simp] public theorem difference_snd (r : sameBase f) :
    (difference f hf hsq r).snd = step f r := rfl

/-- The difference map is surjective: a sequence with prescribed base and prescribed
differences is built term by term, lifting along the surjective transition maps. -/
public theorem difference_surjective : Function.Surjective (difference f hf hsq) := by
  intro y
  let m : ∀ n, RingHom.ker (toBase f n) := y.snd
  let s : ∀ n, R n := fun n => Nat.rec (motive := fun n => R n) y.fst
    (fun n rn => (hf n (rn + (m n : R n))).choose) n
  have hs : ∀ n, f n (s (n + 1)) = s n + (m n : R n) := fun n =>
    (hf n (s n + (m n : R n))).choose_spec
  have hbase : ∀ n, toBase f n (s n) = y.fst := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [toBase_succ, hs n, map_add, ih, (RingHom.mem_ker).1 (m n).2, add_zero]
  refine ⟨⟨s, fun n => (hbase n).trans (hbase 0).symm⟩, ?_⟩
  refine TrivSqZeroExt.ext rfl (funext fun n => Subtype.ext ?_)
  rw [difference_snd, step_coe]
  show f n (s (n + 1)) - s n = (m n : R n)
  rw [hs n]
  ring

/-- A sequence of `R̃` has trivial difference exactly when it is compatible. -/
public theorem difference_eq_inl_iff (r : sameBase f) :
    difference f hf hsq r = TrivSqZeroExt.inl (base f r) ↔ (r : ∀ n, R n) ∈ limit f := by
  refine ⟨fun h n => ?_, fun h => ?_⟩
  · have h' := congrArg (fun z => ((z.snd : ∀ n, RingHom.ker (toBase f n)) n : R n)) h
    simp only [difference_snd, step_coe, TrivSqZeroExt.snd_inl] at h'
    exact sub_eq_zero.1 h'
  · refine TrivSqZeroExt.ext (by simp) (funext fun n => Subtype.ext ?_)
    rw [difference_snd, step_coe, h n, sub_self]
    rfl

/-- The kernel of the difference map has square zero. -/
public theorem ker_difference_sq : RingHom.ker (difference f hf hsq) ^ 2 = ⊥ := by
  refine eq_bot_iff.2 (le_trans (Ideal.pow_right_mono ?_ 2) (ker_base_sq f hsq).le)
  intro r hr
  rw [RingHom.mem_ker] at hr ⊢
  have h := congrArg TrivSqZeroExt.fst hr
  rw [difference_fst] at h
  exact h

end Deformation.Artin.SquareZeroTower
