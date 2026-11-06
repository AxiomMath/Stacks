module

public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Localization.Integral

/-!
# Adjoining a root commutes with passing to the fraction field

Let `R` be a domain with fraction field `K` and let `p ∈ R[X]` be monic whose image in `K[X]` is
irreducible. Then `K[X] ⧸ (p)` is a fraction field of `R[X] ⧸ (p)`, and of any ring presenting
`R[X] ⧸ (p)` whose structure map is the comparison map read through the presentation.

## Main definitions

* `Stacks.AdjoinRootFraction.toMapAdjoinRoot`: the comparison map
  `AdjoinRoot p → AdjoinRoot (p.map (algebraMap R K))`, the identity on the adjoined root and
  the inclusion `R ⊆ K` on coefficients.

## Main results

* `Stacks.AdjoinRootFraction.toMapAdjoinRoot_injective`: the comparison map is injective for
  monic `p`.
* `Stacks.AdjoinRootFraction.isDomain_of_ringEquiv`: a ring presenting `AdjoinRoot p` is a
  domain.
* `Stacks.AdjoinRootFraction.isFractionRing_adjoinRoot`: `AdjoinRoot (p.map (algebraMap R K))`
  is a fraction field of `AdjoinRoot p`, and of any ring presenting it.
-/

@[expose] public noncomputable section

open Polynomial

universe u v w

namespace Stacks.AdjoinRootFraction

variable {R : Type u} [CommRing R] [IsDomain R] (K : Type v) [Field K] [Algebra R K]
  [IsFractionRing R K] {p : R[X]} {q : K[X]}

/-- **The comparison map `AdjoinRoot p → AdjoinRoot q`**, for `q` the polynomial `p` read over
the fraction field: the adjoined root goes to the adjoined root, and a coefficient goes to its
image in `K`. -/
def toMapAdjoinRoot (hq : q = p.map (algebraMap R K)) : AdjoinRoot p →+* AdjoinRoot q :=
  AdjoinRoot.lift ((AdjoinRoot.of q).comp (algebraMap R K)) (AdjoinRoot.root q)
    (by subst hq; rw [← Polynomial.eval₂_map]; exact AdjoinRoot.eval₂_root _)

omit [IsDomain R] [IsFractionRing R K] in
/-- The comparison map sends the class of `r ∈ R[X]` to the class of its image in `K[X]`. -/
@[simp] theorem toMapAdjoinRoot_mk (hq : q = p.map (algebraMap R K)) (r : R[X]) :
    toMapAdjoinRoot K hq (AdjoinRoot.mk p r) =
      AdjoinRoot.mk q (r.map (algebraMap R K)) := by
  rw [toMapAdjoinRoot, AdjoinRoot.lift_mk, ← Polynomial.eval₂_map, ← AdjoinRoot.algebraMap_eq,
    ← Polynomial.aeval_def, AdjoinRoot.aeval_eq]

omit [IsDomain R] [IsFractionRing R K] in
/-- The comparison map sends the adjoined root to the adjoined root. -/
@[simp] theorem toMapAdjoinRoot_root (hq : q = p.map (algebraMap R K)) :
    toMapAdjoinRoot K hq (AdjoinRoot.root p) = AdjoinRoot.root q := by
  rw [← AdjoinRoot.mk_X, toMapAdjoinRoot_mk, Polynomial.map_X, AdjoinRoot.mk_X]

omit [IsDomain R] [IsFractionRing R K] in
/-- The comparison map sends a coefficient `r ∈ R` to its image in `K`. -/
@[simp] theorem toMapAdjoinRoot_of (hq : q = p.map (algebraMap R K)) (r : R) :
    toMapAdjoinRoot K hq (AdjoinRoot.of p r) = AdjoinRoot.of q (algebraMap R K r) := by
  rw [AdjoinRoot.of, RingHom.comp_apply, toMapAdjoinRoot_mk, Polynomial.map_C, AdjoinRoot.of,
    RingHom.comp_apply]

/-- **The comparison map is injective when `p` is monic.** -/
theorem toMapAdjoinRoot_injective (hq : q = p.map (algebraMap R K)) (hp : p.Monic) :
    Function.Injective (toMapAdjoinRoot K hq) := by
  subst hq
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hmapinj : Function.Injective (Polynomial.map (algebraMap R K)) :=
    Polynomial.map_injective _ hinj
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨r, rfl⟩ := AdjoinRoot.mk_surjective x
  rw [toMapAdjoinRoot_mk, AdjoinRoot.mk_eq_zero] at hx
  rw [AdjoinRoot.mk_eq_zero, ← Polynomial.modByMonic_eq_zero_iff_dvd hp]
  have hsplit : (r %ₘ p).map (algebraMap R K) =
      r.map (algebraMap R K) - (p.map (algebraMap R K)) * ((r /ₘ p).map (algebraMap R K)) := by
    have h2 := congrArg (Polynomial.map (algebraMap R K)) (Polynomial.modByMonic_add_div r p)
    rw [Polynomial.map_add, Polynomial.map_mul] at h2
    rw [← h2]
    ring
  have hdvd : p.map (algebraMap R K) ∣ (r %ₘ p).map (algebraMap R K) := by
    rw [hsplit]
    exact dvd_sub hx (dvd_mul_right _ _)
  by_cases hr0 : (r %ₘ p).map (algebraMap R K) = 0
  · exact hmapinj (by rw [hr0, Polynomial.map_zero])
  · have h1 := Polynomial.degree_le_of_dvd hdvd hr0
    rw [hp.degree_map (algebraMap R K)] at h1
    exact absurd (h1.trans Polynomial.degree_map_le) (Polynomial.degree_modByMonic_lt r hp).not_ge

variable {A : Type w} [CommRing A]

/-- The comparison map read through a presentation `A ≃+* AdjoinRoot p` is injective. -/
private theorem comp_toMapAdjoinRoot_injective (hq : q = p.map (algebraMap R K))
    (e : A ≃+* AdjoinRoot p) (hp : p.Monic) :
    Function.Injective ((toMapAdjoinRoot K hq).comp (e : A →+* AdjoinRoot p)) :=
  (toMapAdjoinRoot_injective K hq hp).comp e.injective

/-- A ring presenting `AdjoinRoot p` is a domain, `p` being monic with irreducible image. -/
theorem isDomain_of_ringEquiv (hq : q = p.map (algebraMap R K)) (e : A ≃+* AdjoinRoot p)
    (hp : p.Monic) [Fact (Irreducible q)] : IsDomain A :=
  Function.Injective.isDomain _ (comp_toMapAdjoinRoot_injective K hq e hp)

/-- **`K[Y] ⧸ (p)` is a fraction field of `R[Y] ⧸ (p)`**, for `p ∈ R[Y]` monic whose image in
`K[Y]` is irreducible — and of any ring `A` presenting `R[Y] ⧸ (p)` whose structure map is the
comparison map read through the presentation. -/
theorem isFractionRing_adjoinRoot (hq : q = p.map (algebraMap R K)) (e : A ≃+* AdjoinRoot p)
    (hp : p.Monic) [Fact (Irreducible q)] [Algebra A (AdjoinRoot q)]
    (halg : algebraMap A (AdjoinRoot q) =
      (toMapAdjoinRoot K hq).comp (e : A →+* AdjoinRoot p)) :
    IsFractionRing A (AdjoinRoot q) := by
  have hinj : Function.Injective (algebraMap A (AdjoinRoot q)) := by
    rw [halg]
    exact comp_toMapAdjoinRoot_injective K hq e hp
  have hmap (x : AdjoinRoot p) :
      algebraMap A (AdjoinRoot q) (e.symm x) = toMapAdjoinRoot K hq x := by
    rw [halg]
    simp
  let := isDomain_of_ringEquiv K hq e hp
  refine ⟨⟨fun y => ?_, fun z => ?_, fun {_ _} h => ⟨1, by rw [hinj h]⟩⟩⟩
  · exact isUnit_iff_ne_zero.mpr fun hy =>
      nonZeroDivisors.ne_zero y.2 (hinj (by rw [hy, map_zero]))
  · obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective z
    obtain ⟨b, hb, hbg⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) g
    have hbne : algebraMap R K b ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    have hcne : e.symm (AdjoinRoot.of p b) ≠ 0 := fun hc => by
      refine hbne ?_
      have hz := hmap (AdjoinRoot.of p b)
      rw [hc, map_zero, toMapAdjoinRoot_of] at hz
      exact (map_eq_zero_iff _ (algebraMap K (AdjoinRoot q)).injective).mp hz.symm
    refine ⟨⟨e.symm (AdjoinRoot.mk p (IsLocalization.integerNormalization (nonZeroDivisors R) g)),
      ⟨e.symm (AdjoinRoot.of p b), mem_nonZeroDivisors_iff_ne_zero.mpr hcne⟩⟩, ?_⟩
    simp only [hmap, toMapAdjoinRoot_of, toMapAdjoinRoot_mk, hbg]
    rw [AdjoinRoot.of, RingHom.comp_apply, ← map_mul]
    congr 1
    rw [mul_comm, ← Polynomial.smul_eq_C_mul, algebraMap_smul]

end Stacks.AdjoinRootFraction

end
