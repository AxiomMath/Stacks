module

public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Valuation.ValuationRing
public import StacksCore.Tactic.StacksAttribute

/-!
# The valuative criterion for the Quot functor: the affine chart (Stacks 0DM4)

Stacks 0DM4 says that for `X ⟶ B` proper and of finite presentation and `F` quasi-coherent of
finite type the morphism `Quot_{F/X/B} ⟶ B` satisfies the existence part of the valuative
criterion of Stacks 03IX. This file proves the corresponding statement on an affine chart over a
valuation ring, together with its uniqueness.

Let `R` be a valuation ring, `A` an `R`-algebra and `M` a finite `A`-module. Let `M_K` be the
generic fibre of `M`, that is, the localization of `M` at the nonzero elements of `R`, with
localization map `ι : M ⟶ M_K`, and let `P ⊆ M_K` be the kernel of a prescribed quotient of `M_K`.
Then

* the *generic kernel* `L = {x ∈ M | ι x ∈ P}` is an `A`-submodule of `M`;
* `M / L` is torsion free over `R`, hence flat over `R` because `R` is a valuation ring — this
  is Stacks 0539;
* `M / L` is a finite `A`-module, and its generic fibre is the prescribed quotient, in that the
  localization of `L` at the nonzero elements of `R` is `P`;
* `L` is the *only* `A`-submodule of `M` with those properties.

In Lean the generic kernel of `P` is `Submodule.comap ι P`, and the generic fibre of a submodule
`L` of `M` is `Submodule.localized₀`, whose members are the fractions `x / s` with `x ∈ L` and `s`
a nonzero element of `R`.

The hypothesis on `P` is that it is an `A`-submodule of `M_K` saturated for the nonzero
elements of `R`, which for a submodule of `M_K` is the same as being a submodule over
`A ⊗_R K`: `mem_of_nonzero_smul_mem` derives the saturation from stability under the scalars of
any fraction field of `R` acting on `M_K`.

## Main results

* `StacksDraft.GenericFibre.existsUnique_submodule_flat_quotient`: **Stacks 0DM4** on an affine
  chart over a valuation ring — the generic kernel is the unique `A`-submodule whose quotient is
  flat over `R`, finite over `A`, and has the prescribed generic fibre.
* `StacksDraft.GenericFibre.isTorsionFree_quotient_comap`: the quotient by the generic kernel is
  torsion free over `R`.
* `StacksDraft.GenericFibre.flat_of_isTorsionFree`: Stacks 0539, a torsion free module over a
  valuation ring is flat.
* `StacksDraft.GenericFibre.localized₀_restrictScalars_comap`: the generic fibre of the generic
  kernel is the prescribed submodule `P`.
* `StacksDraft.GenericFibre.comap_eq_of_isTorsionFree_of_localized₀_eq` and
  `StacksDraft.GenericFibre.eq_of_isTorsionFree_of_localized₀_eq`: a submodule whose quotient is
  torsion free over `R` is determined by its generic fibre.
* `StacksDraft.GenericFibre.le_of_forall_mem_localized₀`: a submodule `L₁` whose image lies in
  the generic fibre of a submodule `L₂` with torsion free quotient is contained in `L₂`.

## References

* [Stacks Project, Tag 0DM4](https://stacks.math.columbia.edu/tag/0DM4)
* [Stacks Project, Tag 03IX](https://stacks.math.columbia.edu/tag/03IX)
* [Stacks Project, Tag 0539](https://stacks.math.columbia.edu/tag/0539)
* [Stacks Project, Tag 03M3](https://stacks.math.columbia.edu/tag/03M3)
* [Stacks Project, Tag 0DLR](https://stacks.math.columbia.edu/tag/0DLR)
-/

@[expose] public section

open scoped nonZeroDivisors

namespace StacksDraft.GenericFibre

universe u v w x

/-- **Stacks 0539.** A torsion free module over a valuation ring is flat. -/
@[ega "0 6.3.4" "converse when A is a DVR", sga "1 IV 1.3" "(ii)"]
theorem flat_of_isTorsionFree {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
    (N : Type w) [AddCommGroup N] [Module R N] (h : Module.IsTorsionFree R N) :
    Module.Flat R N := by
  rwa [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout,
    ← Submodule.isTorsionFree_iff_torsion_eq_bot]

variable {R : Type u} [CommRing R] [IsDomain R]
  {A : Type v} [CommRing A] [Algebra R A]
  {M : Type w} [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
  {MK : Type x} [AddCommGroup MK] [Module R MK] [Module A MK] [IsScalarTower R A MK]
  {ι : M →ₗ[A] MK} [IsLocalizedModule R⁰ (ι.restrictScalars R)] {P : Submodule A MK}

omit [IsDomain R] [Algebra R A] [IsScalarTower R A MK]
  [IsLocalizedModule R⁰ (ι.restrictScalars R)] in
/-- A submodule of the generic fibre stable under the scalars of a fraction field `K` of `R` is
saturated for the nonzero elements of `R`: if `s ≠ 0` and `s • y` lies in it, so does `y`. -/
theorem mem_of_nonzero_smul_mem (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    [Module K MK] [IsScalarTower R K MK]
    (hPK : ∀ (c : K) {y : MK}, y ∈ P → c • y ∈ P) {s : R} (hs : s ≠ 0) {y : MK}
    (hy : s • y ∈ P) : y ∈ P := by
  have hs' : algebraMap R K s ≠ 0 := fun h => hs (IsFractionRing.to_map_eq_zero_iff.mp h)
  have h := hPK (algebraMap R K s)⁻¹ hy
  rwa [← algebraMap_smul K s y, smul_smul, inv_mul_cancel₀ hs', one_smul] at h

omit [IsLocalizedModule R⁰ (ι.restrictScalars R)] in
/-- If `P` is saturated for the nonzero elements of `R`, the quotient of `M` by the generic kernel
of `P` is torsion free over `R`. -/
theorem isTorsionFree_quotient_comap
    (hP : ∀ (s : R) {y : MK}, s ≠ 0 → s • y ∈ P → y ∈ P) :
    Module.IsTorsionFree R (M ⧸ P.comap ι) := by
  rw [Module.isTorsionFree_iff_smul_eq_zero]
  intro r m hrm
  rcases eq_or_ne r 0 with h | h
  · exact Or.inl h
  refine Or.inr ?_
  induction m using Submodule.Quotient.induction_on with
  | _ y =>
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
      LinearMap.map_smul_of_tower] at hrm
    exact (Submodule.Quotient.mk_eq_zero _).2 (hP r h hrm)

/-- If `P` is saturated for the nonzero elements of `R`, the generic fibre of the generic kernel
of `P` is `P` itself. -/
theorem localized₀_restrictScalars_comap
    (hP : ∀ (s : R) {y : MK}, s ≠ 0 → s • y ∈ P → y ∈ P) :
    Submodule.localized₀ R⁰ (ι.restrictScalars R) ((P.comap ι).restrictScalars R)
      = P.restrictScalars R := by
  refine le_antisymm ?_ ?_
  · rintro - ⟨z, hz, s, rfl⟩
    refine hP (s : R) (nonZeroDivisors.coe_ne_zero s) ?_
    rwa [← Submonoid.smul_def, IsLocalizedModule.mk'_cancel']
  · intro y hy
    obtain ⟨⟨z, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective R⁰ (ι.restrictScalars R) y
    refine ⟨z, ?_, s, rfl⟩
    have key : (s : R) • IsLocalizedModule.mk' (ι.restrictScalars R) z s = ι z := by
      rw [← Submonoid.smul_def, IsLocalizedModule.mk'_cancel']
      rfl
    change ι z ∈ P
    rw [← key]
    exact (P.restrictScalars R).smul_mem _ hy

/-- Let `L₂` be an `A`-submodule of `M` with quotient torsion free over `R`. If `ι z` lies in the
generic fibre of `L₂` for every `z ∈ L₁`, then `L₁ ≤ L₂`. -/
theorem le_of_forall_mem_localized₀ (L₁ L₂ : Submodule A M)
    (htf : Module.IsTorsionFree R (M ⧸ L₂))
    (h : ∀ z ∈ L₁, ι z ∈ Submodule.localized₀ R⁰ (ι.restrictScalars R) (L₂.restrictScalars R)) :
    L₁ ≤ L₂ := by
  rw [Module.isTorsionFree_iff_smul_eq_zero] at htf
  intro z hz
  obtain ⟨m, hm, s, hms⟩ := h z hz
  have h1 : (ι.restrictScalars R) m = (s : R) • (ι.restrictScalars R) z := by
    rw [IsLocalizedModule.mk'_eq_iff.mp hms, Submonoid.smul_def]
    rfl
  obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff R⁰ (ι.restrictScalars R)
    (m := m - (s : R) • z)).1 (by
      rw [map_sub, h1, (ι.restrictScalars R).map_smul, sub_self])
  have h2 : (t : R) • m = (t : R) • ((s : R) • z) := by
    have h3 : (t : R) • (m - (s : R) • z) = 0 := by simpa [Submonoid.smul_def] using ht
    rwa [smul_sub, sub_eq_zero] at h3
  have hmem : ((t : R) * (s : R)) • z ∈ L₂ := by
    rw [mul_smul, ← h2]
    exact (L₂.restrictScalars R).smul_mem _ hm
  rcases htf ((t : R) * (s : R)) (Submodule.Quotient.mk z)
    ((Submodule.Quotient.mk_smul _ _ _).symm.trans
      ((Submodule.Quotient.mk_eq_zero _).2 hmem)) with h | h
  · exact absurd h (mul_ne_zero (nonZeroDivisors.coe_ne_zero t)
      (nonZeroDivisors.coe_ne_zero s))
  · exact (Submodule.Quotient.mk_eq_zero _).1 h

/-- If the generic fibre of `L₁` is contained in that of `L₂` and `M / L₂` is torsion free over `R`,
then `L₁ ≤ L₂`. -/
private theorem le_of_localized₀_le (L₁ L₂ : Submodule A M) (htf : Module.IsTorsionFree R (M ⧸ L₂))
    (h : Submodule.localized₀ R⁰ (ι.restrictScalars R) (L₁.restrictScalars R)
      ≤ Submodule.localized₀ R⁰ (ι.restrictScalars R) (L₂.restrictScalars R)) :
    L₁ ≤ L₂ :=
  le_of_forall_mem_localized₀ L₁ L₂ htf fun _ hz =>
    h (Submodule.map_le_localized₀ R⁰ (ι.restrictScalars R) _ ⟨_, hz, rfl⟩)

/-- An `A`-submodule `L` of `M` whose quotient is torsion free over `R` is determined by its
generic fibre: if that generic fibre is `P` then `L` is the generic kernel of `P`. -/
theorem comap_eq_of_isTorsionFree_of_localized₀_eq (L : Submodule A M)
    (htf : Module.IsTorsionFree R (M ⧸ L))
    (hL : Submodule.localized₀ R⁰ (ι.restrictScalars R) (L.restrictScalars R)
      = P.restrictScalars R) :
    L = P.comap ι := by
  refine le_antisymm (fun z hz => ?_)
    (le_of_forall_mem_localized₀ _ L htf (fun z hz => by rwa [hL]))
  have h : ι z ∈ Submodule.localized₀ R⁰ (ι.restrictScalars R) (L.restrictScalars R) :=
    Submodule.map_le_localized₀ R⁰ (ι.restrictScalars R) _ ⟨z, hz, rfl⟩
  rwa [hL] at h

/-- Two `A`-submodules of `M` whose quotients are torsion free over `R` and which have the same
generic fibre coincide. -/
@[ega "IV 2.8.1.1" "Uniqueness clause"]
theorem eq_of_isTorsionFree_of_localized₀_eq (L₁ L₂ : Submodule A M)
    (h₁ : Module.IsTorsionFree R (M ⧸ L₁)) (h₂ : Module.IsTorsionFree R (M ⧸ L₂))
    (h : Submodule.localized₀ R⁰ (ι.restrictScalars R) (L₁.restrictScalars R)
      = Submodule.localized₀ R⁰ (ι.restrictScalars R) (L₂.restrictScalars R)) :
    L₁ = L₂ := by
  exact le_antisymm (le_of_localized₀_le (ι := ι) L₁ L₂ h₂ h.le)
    (le_of_localized₀_le (ι := ι) L₂ L₁ h₁ h.ge)

/-- **Stacks 0DM4, on an affine chart over a valuation ring.**  Let `R` be a valuation ring, `A`
an `R`-algebra, `M` a finite `A`-module and `M_K` the generic fibre of `M`, that is, its
localization at the nonzero elements of `R`.  Let `P` be the kernel of a prescribed quotient of
`M_K`, an `A`-submodule saturated for the nonzero elements of `R`.  Then there is exactly one
`A`-submodule `L` of `M` such that `M / L` is flat over `R` and finite over `A` and the generic
fibre of `L` is `P`; it is the generic kernel `{x ∈ M | ι x ∈ P}`. -/
@[stacks 0DM4 "the affine-chart case: over a valuation ring a quotient of the generic fibre of \
a finite module extends uniquely to a quotient flat over the valuation ring and finite over the \
chart, the extension being the generic-kernel quotient and its flatness Stacks 0539; the etale \
gluing of Stacks 03M3, the proper support, and the finite presentation of Stacks 0DLR are not \
covered", ega "IV 2.8.1.1" "special case"]
theorem existsUnique_submodule_flat_quotient [ValuationRing R] [Module.Finite A M]
    (hP : ∀ (s : R) {y : MK}, s ≠ 0 → s • y ∈ P → y ∈ P) :
    ∃! L : Submodule A M, (Module.Flat R (M ⧸ L) ∧ Module.Finite A (M ⧸ L)) ∧
      Submodule.localized₀ R⁰ (ι.restrictScalars R) (L.restrictScalars R)
        = P.restrictScalars R := by
  refine ⟨P.comap ι, ⟨⟨flat_of_isTorsionFree _ (isTorsionFree_quotient_comap hP),
    inferInstance⟩, localized₀_restrictScalars_comap hP⟩, ?_⟩
  rintro L ⟨⟨hflat, -⟩, hL⟩
  have : Module.Flat R (M ⧸ L) := hflat
  exact comap_eq_of_isTorsionFree_of_localized₀_eq L Module.Flat.isTorsionFree hL

/-! ### The hypotheses are satisfiable

The standing hypotheses are those of a localization of a module at the nonzero elements of `R`,
and they are met by Mathlib's localized module. -/

example (N : Type w) [AddCommGroup N] [Module R N] :
    IsLocalizedModule R⁰ ((LocalizedModule.mkLinearMap R⁰ N).restrictScalars R) :=
  inferInstanceAs (IsLocalizedModule R⁰ (LocalizedModule.mkLinearMap R⁰ N))

end StacksDraft.GenericFibre

end
