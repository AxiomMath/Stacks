module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Module.IPowerTorsion

/-!
# Resolutions of ideal-power torsion modules

An `I`-power torsion module over a commutative ring has a resolution whose terms are direct sums
of quotients of the ring by positive powers of `I`. Each element `x` of such a module is killed by
some `I^n`, so it is hit by a map `R ⧸ I^n → M`; assembling one such quotient for every element
gives a surjection from a direct sum, and iterating on the kernel — which is again `I`-power
torsion — produces the resolution.

## Main results

* `exists_directSum_quotient_resolution`: an `I`-power torsion module admits an exact resolution
  by direct sums of modules of the form `R ⧸ I ^ n` with `n > 0`.

## Implementation notes

The terms of the resolution are the standard external direct sums, and exactness of the augmented
complex is expressed with `Function.Exact`. The iteration is carried by an auxiliary `Stage`
structure bundling a module with its `I`-power torsion witness, so that the kernel at each step
can be fed back in; a `ULift` puts the given module and the successive kernels in one universe.

## References

* [The Stacks Project, Tag 05E8](https://stacks.math.columbia.edu/tag/05E8)
-/

@[expose] public section

universe u v w

open scoped DirectSum

section

variable (R : Type u) [CommRing R] (I : Ideal R)
variable {N : Type w} [AddCommGroup N] [Module R N]

private noncomputable def exponent (hN : IsIPowerTorsion R N I) (x : N) : ℕ :=
  (hN x).choose

private lemma exponent_pos (hN : IsIPowerTorsion R N I) (x : N) :
    0 < exponent R I hN x :=
  (hN x).choose_spec.1

private noncomputable def cyclicMap (x : N) : R →ₗ[R] N where
  toFun r := r • x
  map_add' r s := add_smul r s x
  map_smul' r s := by simp [mul_smul]

private lemma pow_le_ker_cyclicMap (hN : IsIPowerTorsion R N I) (x : N) :
    I ^ exponent R I hN x ≤ LinearMap.ker (cyclicMap R x) :=
  fun r hr ↦ (hN x).choose_spec.2 r hr

private noncomputable def quotientMap (hN : IsIPowerTorsion R N I) (x : N) :
    R ⧸ I ^ exponent R I hN x →ₗ[R] N :=
  Submodule.liftQ (I ^ exponent R I hN x) (cyclicMap R x)
    (pow_le_ker_cyclicMap R I hN x)

private noncomputable def presentationMap (hN : IsIPowerTorsion R N I) :
    DirectSum N (fun x ↦ R ⧸ I ^ exponent R I hN x) →ₗ[R] N :=
  let := Classical.decEq N
  DirectSum.toModule R N N (quotientMap R I hN)

private lemma presentationMap_surjective (hN : IsIPowerTorsion R N I) :
    Function.Surjective (presentationMap R I hN) := by
  classical
  intro x
  refine ⟨DirectSum.lof R N (fun y ↦ R ⧸ I ^ exponent R I hN y) x
    (Submodule.Quotient.mk (1 : R)), ?_⟩
  rw [presentationMap, DirectSum.toModule_lof]
  show (I ^ exponent R I hN x).liftQ (cyclicMap R x) _
      (Submodule.Quotient.mk (1 : R)) = x
  rw [Submodule.liftQ_apply]
  simp [cyclicMap]

private lemma quotient_smul_eq_zero {n : ℕ} (r : R) (hr : r ∈ I ^ n)
    (x : R ⧸ I ^ n) : r • x = 0 := by
  obtain ⟨s, rfl⟩ := x.exists_rep
  show Ideal.Quotient.mk (I ^ n) (r * s) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact (I ^ n).mul_mem_right s hr

private lemma directSum_isIPowerTorsion (hN : IsIPowerTorsion R N I) :
    IsIPowerTorsion R
      (DirectSum N (fun x ↦ R ⧸ I ^ exponent R I hN x)) I := by
  classical
  intro x
  let k := 1 + x.support.sum (exponent R I hN)
  refine ⟨k, by simp [k], fun r hr ↦ ?_⟩
  ext j
  by_cases hj : j ∈ x.support
  · have hjle : exponent R I hN j ≤ x.support.sum (exponent R I hN) :=
      Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hj
    exact quotient_smul_eq_zero R I r
      (Ideal.pow_le_pow_right (hjle.trans (Nat.le_add_left _ 1)) hr) (x j)
  · have hxj : x j = 0 := by simpa [DFinsupp.mem_support_iff] using hj
    show r • x j = 0
    simp [hxj]

/-- `I`-power torsion passes to a module admitting an injective linear map into a torsion one. -/
private lemma isIPowerTorsion_of_injective {P : Type*} [AddCommGroup P] [Module R P]
    (f : N →ₗ[R] P) (hf : Function.Injective f) (hP : IsIPowerTorsion R P I) :
    IsIPowerTorsion R N I := fun x ↦ by
  obtain ⟨n, hn, hx⟩ := hP (f x)
  exact ⟨n, hn, fun r hr ↦ hf (by rw [map_smul, hx r hr, map_zero])⟩

private def uliftDown (M : Type v) [AddCommGroup M] [Module R M] :
    ULift.{max u v} M →ₗ[R] M where
  toFun x := x.down
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private lemma uliftDown_injective (M : Type v) [AddCommGroup M] [Module R M] :
    Function.Injective (uliftDown R M) := fun _ _ h ↦ ULift.ext h

private structure Stage where
  carrier : Type (max u v)
  addCommGroup : AddCommGroup carrier
  module : Module R carrier
  torsion : IsIPowerTorsion R carrier I

attribute [local instance] Stage.addCommGroup Stage.module

private noncomputable def Stage.next (s : Stage R I) : Stage R I where
  carrier := LinearMap.ker (presentationMap R I s.torsion)
  addCommGroup := inferInstance
  module := inferInstance
  torsion := isIPowerTorsion_of_injective R I (LinearMap.ker _).subtype
    (Submodule.injective_subtype _) (directSum_isIPowerTorsion R I s.torsion)

private noncomputable def stages (M : Type v) [AddCommGroup M] [Module R M]
    (hM : IsIPowerTorsion R M I) : ℕ → Stage R I
  | 0 =>
      { carrier := ULift.{max u v} M
        addCommGroup := ULift.addCommGroup
        module := ULift.module'
        torsion := isIPowerTorsion_of_injective R I (uliftDown R M) (uliftDown_injective R M) hM }
  | n + 1 => (stages M hM n).next

/-- **Stacks 05E8.** An `I`-power torsion module admits an exact resolution whose terms are
direct sums of quotients of the ring by positive powers of `I`. -/
@[stacks 05E8]
public theorem exists_directSum_quotient_resolution
    (R : Type u) [CommRing R] (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (hM : IsIPowerTorsion R M I) :
    ∃ (α : ℕ → Type (max u v)) (n : ∀ i, α i → ℕ),
      (∀ i a, 0 < n i a) ∧
        ∃ (d : ∀ i,
            DirectSum (α (i + 1)) (fun a ↦ R ⧸ I ^ n (i + 1) a) →ₗ[R]
              DirectSum (α i) (fun a ↦ R ⧸ I ^ n i a))
          (ε : DirectSum (α 0) (fun a ↦ R ⧸ I ^ n 0 a) →ₗ[R] M),
          Function.Surjective ε ∧ Function.Exact (d 0) ε ∧
            ∀ i, Function.Exact (d (i + 1)) (d i) := by
  classical
  let S := stages R I M hM
  let α : ℕ → Type (max u v) := fun i ↦ (S i).carrier
  let n : ∀ i, α i → ℕ := fun i ↦ exponent R I (S i).torsion
  let p : ∀ i, DirectSum (α i) (fun a ↦ R ⧸ I ^ n i a) →ₗ[R] (S i).carrier :=
    fun i ↦ presentationMap R I (S i).torsion
  let e : ∀ i, (S (i + 1)).carrier →ₗ[R] LinearMap.ker (p i) := fun i ↦
    { toFun x := ⟨x.1, x.2⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  have he : ∀ i, Function.Surjective (e i) := fun i x ↦ ⟨⟨x.1, x.2⟩, Subtype.ext rfl⟩
  let d : ∀ i, DirectSum (α (i + 1)) (fun a ↦ R ⧸ I ^ n (i + 1) a) →ₗ[R]
      DirectSum (α i) (fun a ↦ R ⧸ I ^ n i a) :=
    fun i ↦ (LinearMap.ker (p i)).subtype ∘ₗ e i ∘ₗ p (i + 1)
  let ε : DirectSum (α 0) (fun a ↦ R ⧸ I ^ n 0 a) →ₗ[R] M :=
    uliftDown R M ∘ₗ p 0
  have hd : ∀ i, d i = ((LinearMap.ker (p i)).subtype ∘ₗ e i) ∘ₗ p (i + 1) := fun _ ↦ rfl
  have hdp : ∀ i, Function.Exact (d i) (p i) := fun i ↦ by
    rw [hd i,
      (presentationMap_surjective R I (S (i + 1)).torsion).comp_exact_iff_exact,
      (he i).comp_exact_iff_exact]
    exact LinearMap.exact_subtype_ker_map (p i)
  refine ⟨α, n, fun i a ↦ exponent_pos R I (S i).torsion a, d, ε, ?_, ?_, fun i ↦ ?_⟩
  · intro x
    obtain ⟨y, hy⟩ := presentationMap_surjective R I (S 0).torsion (ULift.up x)
    exact ⟨y, congrArg ULift.down hy⟩
  · exact (uliftDown_injective R M).comp_exact_iff_exact.mpr (hdp 0)
  · have hei : Function.Injective ((LinearMap.ker (p i)).subtype ∘ₗ e i) :=
      (LinearMap.ker (p i)).subtype_injective.comp
        (fun _ _ h ↦ Subtype.ext (congrArg Subtype.val h))
    rw [hd i, hei.comp_exact_iff_exact]
    exact hdp (i + 1)

end

end
