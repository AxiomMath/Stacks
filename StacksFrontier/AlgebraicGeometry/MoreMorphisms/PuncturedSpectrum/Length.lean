module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Order.Lattice.Nat
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Length

/-!
# Length of the cokernel of multiplication by a locally nilpotent scalar

Let `Q` be a module over a commutative ring `R` and let `f : R` act locally nilpotently on `Q`,
meaning that every element of `Q` is killed by some power of `f`. The main result of this file
bounds the length of `Q ⧸ f • Q` by the length of the `f`-torsion submodule of `Q`:

`Module.length R (Q ⧸ LinearMap.range (LinearMap.lsmul R Q f)) ≤
  Module.length R (LinearMap.ker (LinearMap.lsmul R Q f))`.

In particular `Q ⧸ f • Q` has finite length as soon as the `f`-torsion does, even though `Q`
itself is typically not finitely generated. This is the module-theoretic heart of the criterion
for affineness of a punctured spectrum.

## Main results

* `Stacks.PuncturedSpectrum.length_quotient_range_lsmul_le` is the length bound.
* `Stacks.PuncturedSpectrum.length_ne_top_of_maximalIdeal_pow_smul_eq_zero`: a finitely generated
  module over a Noetherian local ring that is annihilated by a power of the maximal ideal has
  finite length.

## Implementation notes

Write `Kₙ` for the kernel of multiplication by `fⁿ` on `Q`. The two exact sequences
`0 → K₁ → Kₙ₊₁ → f • Kₙ₊₁ → 0` and `0 → Kₙ ⊓ f • Q → Kₙ → Kₙ/(Kₙ ⊓ f • Q) → 0`, together with
the identity `Kₙ ⊓ f • Q = f • Kₙ₊₁`, bound the length of the image of `Kₙ` in `Q ⧸ f • Q` by the
length of `K₁`, uniformly in `n`. Local nilpotence makes those images exhaust `Q ⧸ f • Q`, and a
monotone family of submodules of uniformly bounded finite length is eventually constant, so the
bound passes to the whole quotient.

Lengths are taken in `ℕ∞` via `Module.length`, and the comparison of a submodule's length with
`Order.height` in the lattice of submodules (`Module.length_submodule`) is what makes the
"eventually constant" step short.
-/

@[expose] public section

universe u v w

namespace Stacks.PuncturedSpectrum

section General

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- The length of a module is the length of the kernel plus the length of the image of any
linear map out of it. -/
theorem length_eq_length_ker_add_length_range {N : Type w} [AddCommGroup N] [Module R N]
    (g : M →ₗ[R] N) :
    Module.length R M =
      Module.length R ↥(LinearMap.ker g) + Module.length R ↥(LinearMap.range g) := by
  refine Module.length_eq_add_of_exact (LinearMap.ker g).subtype g.rangeRestrict
    (Submodule.subtype_injective _) (LinearMap.surjective_rangeRestrict g) ?_
  have h := LinearMap.exact_subtype_ker_map g.rangeRestrict
  rwa [LinearMap.ker_rangeRestrict] at h

/-- Length is monotone in submodules. -/
theorem length_le_length_of_le {p q : Submodule R M} (h : p ≤ q) :
    Module.length R ↥p ≤ Module.length R ↥q := by
  rw [Module.length_submodule, Module.length_submodule]
  exact Order.height_mono h

/-- The preimage of a submodule in another one has the length of their intersection. -/
theorem length_comap_subtype (p q : Submodule R M) :
    Module.length R ↥(q.comap p.subtype) = Module.length R ↥(p ⊓ q) := by
  rw [show q.comap p.subtype = (p ⊓ q).comap p.subtype by
    rw [Submodule.comap_inf, Submodule.comap_subtype_self, top_inf_eq]]
  exact (Submodule.comapSubtypeEquivOfLe (inf_le_left (a := p) (b := q))).length_eq

/-- The length of a submodule is that of its intersection with the kernel of a linear map plus
that of its image. -/
private theorem length_eq_length_inf_ker_add_length_map {N : Type w} [AddCommGroup N] [Module R N]
    (g : M →ₗ[R] N) (p : Submodule R M) :
    Module.length R ↥p =
      Module.length R ↥(p ⊓ LinearMap.ker g) + Module.length R ↥(Submodule.map g p) := by
  have h := length_eq_length_ker_add_length_range (g ∘ₗ p.subtype)
  rwa [LinearMap.ker_comp, LinearMap.range_comp, Submodule.range_subtype,
    length_comap_subtype] at h

/-- A submodule of the same finite length as a submodule containing it is equal to it. -/
theorem eq_of_le_of_length_eq {p q : Submodule R M} (hpq : p ≤ q)
    (hlen : Module.length R ↥p = Module.length R ↥q) (hfin : Module.length R ↥q ≠ ⊤) : p = q := by
  by_contra hne
  have hp : Order.height p = Module.length R ↥p := Module.length_submodule.symm
  have hq : Order.height q = Module.length R ↥q := Module.length_submodule.symm
  have hlt : Order.height p < Order.height q :=
    Order.height_strictMono (lt_of_le_of_ne hpq hne)
      (by rwa [hp, hlen, lt_top_iff_ne_top])
  rw [hp, hq, hlen] at hlt
  exact hlt.false

/-- A monotone sequence of submodules whose lengths share a finite bound attains its supremum. -/
private theorem exists_forall_le_of_monotone_of_length_le {I : ℕ → Submodule R M} (hI : Monotone I)
    {C : ℕ∞} (hC : C ≠ ⊤) (hle : ∀ n, Module.length R ↥(I n) ≤ C) :
    ∃ N, ∀ n, I n ≤ I N := by
  have hfin : ∀ n, Module.length R ↥(I n) ≠ ⊤ := fun n => ne_top_of_le_ne_top hC (hle n)
  have hcoe : ∀ n, ((Module.length R ↥(I n)).toNat : ℕ∞) = Module.length R ↥(I n) :=
    fun n => ENat.natCast_toNat (hfin n)
  have hmono : Monotone fun n => (Module.length R ↥(I n)).toNat := by
    intro a b hab
    have h := length_le_length_of_le (hI hab)
    rwa [← hcoe a, ← hcoe b, Nat.cast_le] at h
  have hbdd : BddAbove (Set.range fun n => (Module.length R ↥(I n)).toNat) := by
    refine ⟨C.toNat, ?_⟩
    rintro m ⟨n, rfl⟩
    have h := hle n
    rwa [← hcoe n, ← ENat.natCast_toNat hC, Nat.cast_le] at h
  obtain ⟨N, hN⟩ := Nat.sSup_mem (Set.range_nonempty _) hbdd
  have hN' : (Module.length R ↥(I N)).toNat =
      sSup (Set.range fun n => (Module.length R ↥(I n)).toNat) := hN
  have hmax : ∀ n, (Module.length R ↥(I n)).toNat ≤ (Module.length R ↥(I N)).toNat := by
    intro n
    rw [hN']
    exact le_csSup hbdd ⟨n, rfl⟩
  refine ⟨N, fun n => ?_⟩
  have h : I N = I (max n N) := by
    refine eq_of_le_of_length_eq (hI (le_max_right n N)) ?_ (hfin _)
    rw [← hcoe N, ← hcoe (max n N), le_antisymm (hmax (max n N)) (hmono (le_max_right n N))]
  exact (hI (le_max_left n N)).trans_eq h.symm

end General

section LocallyNilpotent

variable {R : Type u} [CommRing R] {Q : Type v} [AddCommGroup Q] [Module R Q] (f : R)

/-- The kernel of multiplication by `f ^ n` on `Q`. -/
private def smulKer (n : ℕ) : Submodule R Q := LinearMap.ker (LinearMap.lsmul R Q (f ^ n))

/-- Membership in `smulKer f n` is the vanishing of `f ^ n • ·`, by definition of the kernel. -/
private lemma mem_smulKer {n : ℕ} {q : Q} : q ∈ smulKer (Q := Q) f n ↔ f ^ n • q = 0 :=
  LinearMap.mem_ker

private lemma smulKer_one : smulKer (Q := Q) f 1 = LinearMap.ker (LinearMap.lsmul R Q f) := by
  rw [smulKer, pow_one]

private lemma smulKer_zero : smulKer (Q := Q) f 0 = ⊥ := by
  ext q
  simp [mem_smulKer]

private lemma smulKer_mono : Monotone (smulKer (Q := Q) f) := by
  intro m n hmn q hq
  rw [mem_smulKer] at hq ⊢
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [pow_add, mul_comm, mul_smul, hq, smul_zero]

/-- The `fⁿ`-torsion inside `f • Q` is exactly `f • (fⁿ⁺¹-torsion)`. -/
private lemma smulKer_inf_range (n : ℕ) :
    smulKer (Q := Q) f n ⊓ LinearMap.range (LinearMap.lsmul R Q f) =
      Submodule.map (LinearMap.lsmul R Q f) (smulKer f (n + 1)) := by
  ext x
  simp only [Submodule.mem_inf, LinearMap.mem_range, Submodule.mem_map, LinearMap.lsmul_apply,
    mem_smulKer]
  constructor
  · rintro ⟨hx, y, hy⟩
    refine ⟨y, ?_, hy⟩
    rwa [pow_succ, mul_smul, hy]
  · rintro ⟨y, hy, rfl⟩
    refine ⟨?_, y, rfl⟩
    rwa [← mul_smul, ← pow_succ]

private lemma length_smulKer_succ (n : ℕ) :
    Module.length R ↥(smulKer (Q := Q) f (n + 1)) =
      Module.length R ↥(smulKer (Q := Q) f 1) +
        Module.length R ↥(smulKer (Q := Q) f n ⊓ LinearMap.range (LinearMap.lsmul R Q f)) := by
  rw [length_eq_length_inf_ker_add_length_map (LinearMap.lsmul R Q f), ← smulKer_one,
    inf_eq_right.mpr (smulKer_mono f (Nat.le_add_left 1 n)), ← smulKer_inf_range]

private lemma length_smulKer_ne_top (hl : Module.length R ↥(smulKer (Q := Q) f 1) ≠ ⊤) (n : ℕ) :
    Module.length R ↥(smulKer (Q := Q) f n) ≠ ⊤ := by
  induction n with
  | zero =>
    rw [smulKer_zero]
    simp
  | succ n ih =>
    rw [length_smulKer_succ]
    exact WithTop.add_ne_top.mpr ⟨hl, ne_top_of_le_ne_top ih (length_le_length_of_le inf_le_left)⟩

/-- The image of the `fⁿ`-torsion in `Q ⧸ f • Q` has length at most that of the `f`-torsion,
uniformly in `n`. -/
private lemma length_map_mkQ_le (hl : Module.length R ↥(smulKer (Q := Q) f 1) ≠ ⊤) (n : ℕ) :
    Module.length R ↥(Submodule.map (LinearMap.range (LinearMap.lsmul R Q f)).mkQ
        (smulKer (Q := Q) f n)) ≤ Module.length R ↥(smulKer (Q := Q) f 1) := by
  have key := length_eq_length_inf_ker_add_length_map
    (LinearMap.range (LinearMap.lsmul R Q f)).mkQ (smulKer (Q := Q) f n)
  rw [Submodule.ker_mkQ] at key
  have h2 : Module.length R ↥(smulKer (Q := Q) f n) ≤
      Module.length R ↥(smulKer (Q := Q) f (n + 1)) :=
    length_le_length_of_le (smulKer_mono f (Nat.le_succ n))
  have hc : Module.length R ↥(smulKer (Q := Q) f n ⊓ LinearMap.range (LinearMap.lsmul R Q f))
      ≠ ⊤ :=
    ne_top_of_le_ne_top (length_smulKer_ne_top f hl n) (length_le_length_of_le inf_le_left)
  rw [key, length_smulKer_succ, add_comm (Module.length R ↥(smulKer (Q := Q) f 1))] at h2
  exact (WithTop.add_le_add_iff_left hc).mp h2

/-- **The length bound.** If `f` acts locally nilpotently on `Q`, then `Q ⧸ f • Q` has length at
most the length of the `f`-torsion submodule of `Q`. -/
theorem length_quotient_range_lsmul_le (hnil : ∀ q : Q, ∃ n : ℕ, f ^ n • q = 0) :
    Module.length R (Q ⧸ LinearMap.range (LinearMap.lsmul R Q f)) ≤
      Module.length R ↥(LinearMap.ker (LinearMap.lsmul R Q f)) := by
  rw [← smulKer_one f]
  by_cases hl : Module.length R ↥(smulKer (Q := Q) f 1) = ⊤
  · simp [hl]
  obtain ⟨N, hN⟩ := exists_forall_le_of_monotone_of_length_le
    (I := fun n => Submodule.map (LinearMap.range (LinearMap.lsmul R Q f)).mkQ
      (smulKer (Q := Q) f n))
    (fun _ _ h => Submodule.map_mono (smulKer_mono f h)) hl (length_map_mkQ_le f hl)
  have htop : Submodule.map (LinearMap.range (LinearMap.lsmul R Q f)).mkQ
      (smulKer (Q := Q) f N) = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ?_
    obtain ⟨q, rfl⟩ := (LinearMap.range (LinearMap.lsmul R Q f)).mkQ_surjective x
    obtain ⟨n, hn⟩ := hnil q
    exact hN n ⟨q, hn, rfl⟩
  have h := length_map_mkQ_le f hl N
  rwa [htop, Module.length_top] at h

end LocallyNilpotent

section FiniteLength

/-- A finitely generated module over a Noetherian local ring that is annihilated by a power of
the maximal ideal has finite length. -/
theorem length_ne_top_of_maximalIdeal_pow_smul_eq_zero (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M] {n : ℕ}
    (hn : n ≠ 0) (h : ∀ a ∈ IsLocalRing.maximalIdeal A ^ n, ∀ x : M, a • x = 0) :
    Module.length A M ≠ ⊤ := by
  have hmin : IsLocalRing.maximalIdeal A ∈ (IsLocalRing.maximalIdeal A ^ n).minimalPrimes := by
    refine ⟨⟨inferInstance, Ideal.pow_le_self hn⟩, fun b hb _ x hx => ?_⟩
    exact hb.1.mem_of_pow_mem n (hb.2 (Ideal.pow_mem_pow hx n))
  have _ : IsArtinianRing (A ⧸ IsLocalRing.maximalIdeal A ^ n) :=
    IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing _ hmin
  have hT : Module.IsTorsionBySet A M ((IsLocalRing.maximalIdeal A ^ n : Ideal A) : Set A) :=
    fun {x a} => h a.1 a.2 x
  let := hT.module
  have _ : Module.Finite (A ⧸ IsLocalRing.maximalIdeal A ^ n) M :=
    Module.Finite.of_restrictScalars_finite A (A ⧸ IsLocalRing.maximalIdeal A ^ n) M
  have _ : IsNoetherian (A ⧸ IsLocalRing.maximalIdeal A ^ n) M :=
    isNoetherian_of_tower A inferInstance
  rw [Module.length_eq_of_surjective (S := A) (R := A ⧸ IsLocalRing.maximalIdeal A ^ n)
    Ideal.Quotient.mk_surjective]
  exact Module.length_ne_top

end FiniteLength

end Stacks.PuncturedSpectrum
