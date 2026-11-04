module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import StacksCore.Tactic.StacksAttribute

/-!
# Fixed points of a Frobenius-semilinear endomorphism

Let `k` be a field of characteristic `p > 0`, let `V` be a finite-dimensional `k`-vector space,
and let `F : V →+ V` be additive and Frobenius-semilinear. The fixed points of `F` form a
finite-dimensional vector space over the prime field `ZMod p`, of dimension at most the
dimension of `V` over `k`. This is the bound on the kernel in the Artin–Schreier sequence.

## Main results

* `fixedPoints_finiteDimensional_of_frobenius_semilinear` proves that the fixed points are
  finite-dimensional over the prime field.
* `finrank_fixedPoints_le_of_frobenius_semilinear` bounds their dimension by the dimension of
  the original space.

## Implementation notes

The fixed points are represented by the kernel of `F - AddMonoidHom.id V`. Their canonical
`ZMod p`-module structure is obtained by restricting scalars along the canonical map
`ZMod p → k`. Although the source assumes that `k` is algebraically closed, this hypothesis is
not needed for either conclusion. The two independent conclusions in the source are stated
separately. The key step is that a family of fixed vectors which is linearly independent over
the prime field stays linearly independent over `k`: a shortest `k`-linear relation can be
normalised to have a coefficient `1`, and applying `F` shows the coefficients satisfy
`c ^ p = c`, hence lie in the prime field.

## References

* [Stacks Project, Tag 0A3L](https://stacks.math.columbia.edu/tag/0A3L)
-/

@[expose] public section

universe u v

variable (p : ℕ) [Fact p.Prime]
  (k : Type u) [Field k] [CharP k p]
  (V : Type v) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  (F : V →+ V)
private theorem frobenius_fixed_linearIndependent_fintype
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
    (V : Type v) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (F : V →+ V) (hF : ∀ (c : k) (x : V), F (c • x) = c ^ p • F x)
    {ι : Type*} [Finite ι] (u : ι → V) (hu : ∀ i, F (u i) = u i)
    (hind : letI : Module (ZMod p) V := Module.compHom V (ZMod.castHom (dvd_refl p) k)
      LinearIndependent (ZMod p) u) : LinearIndependent k u := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  let phi : ZMod p →+* k := ZMod.castHom (dvd_refl p) k
  let : Module (ZMod p) V := Module.compHom V phi
  by_contra hli
  have hex : ∃ n : ℕ, ∃ a : ι → k,
      (∑ i, a i • u i = 0) ∧ (∃ i, a i ≠ 0) ∧
        (Finset.univ.filter fun i => a i ≠ 0).card = n := by
    obtain ⟨a, ha, ⟨i, hi⟩⟩ := (Fintype.not_linearIndependent_iff.mp hli)
    exact ⟨_, a, ha, ⟨i, hi⟩, rfl⟩
  let n := Nat.find hex
  obtain ⟨a, ha, ⟨i₀, hi₀⟩, hcard⟩ := Nat.find_spec hex
  let f : ι → k := fun i => a i / a i₀
  have hf₀ : f i₀ = 1 := by simp [f, hi₀]
  have hfc : (Finset.univ.filter fun i => f i ≠ 0).card = n := by
    simpa [f, hi₀] using hcard
  have hfrel : ∑ i, f i • u i = 0 := by
    have h := congrArg (fun x : V => (a i₀)⁻¹ • x) ha
    convert h using 1 <;> simp [f, div_eq_mul_inv, Finset.smul_sum, smul_smul,
      mul_comm]
  have hfrob : ∑ i, f i ^ p • u i = 0 := by
    simpa only [map_sum, hF, hu, map_zero] using congrArg F hfrel
  let d : ι → k := fun i => f i ^ p - f i
  have hdrel : ∑ i, d i • u i = 0 := by
    simp only [d, sub_smul, Finset.sum_sub_distrib, hfrob, hfrel, sub_self]
  have hdi₀ : d i₀ = 0 := by simp [d, hf₀]
  have hdsub : (Finset.univ.filter fun i => d i ≠ 0) ⊆
      (Finset.univ.filter fun i => f i ≠ 0) := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    intro hjf
    apply hj
    simp [d, hjf, (Fact.out : Nat.Prime p).ne_zero]
  have hdstrict : (Finset.univ.filter fun i => d i ≠ 0) ⊂
      (Finset.univ.filter fun i => f i ≠ 0) :=
    (Finset.ssubset_iff_of_subset hdsub).2 ⟨i₀, by simp [hf₀], by simp [hdi₀]⟩
  have hdcard : (Finset.univ.filter fun i => d i ≠ 0).card < n :=
    (Finset.card_lt_card hdstrict).trans_eq hfc
  have hdzero : ∀ i, d i = 0 := by
    by_contra h
    push Not at h
    have hle := Nat.find_min' hex
      (m := (Finset.univ.filter fun i => d i ≠ 0).card) ⟨d, hdrel, h, rfl⟩
    omega
  have hrange : ∀ j, f j ∈ phi.fieldRange := fun j => by
    rw [show phi.fieldRange = ⊥ from ZMod.fieldRange_castHom_eq_bot p]
    exact (Subfield.mem_bot_iff_pow_eq_self k p).2 (sub_eq_zero.mp (hdzero j))
  choose z hz using fun j => (RingHom.mem_fieldRange.mp (hrange j))
  have hzrel : ∑ i, z i • u i = 0 :=
    (Finset.sum_congr rfl fun j _ => by rw [← hz j]; rfl).trans hfrel
  simpa [Fintype.linearIndependent_iff.mp hind z hzrel i₀, hf₀] using hz i₀

private theorem frobenius_fixed_linearIndependent
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
    (V : Type v) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (F : V →+ V) (hF : ∀ (c : k) (x : V), F (c • x) = c ^ p • F x)
    {ι : Type*} (u : ι → V) (hu : ∀ i, F (u i) = u i)
    (hind : letI : Module (ZMod p) V := Module.compHom V (ZMod.castHom (dvd_refl p) k)
      LinearIndependent (ZMod p) u) : LinearIndependent k u := by
  classical
  let : Module (ZMod p) V := Module.compHom V (ZMod.castHom (dvd_refl p) k)
  rw [linearIndependent_iff_finset_linearIndependent]
  intro s
  let : Fintype s := s.finite_toSet.fintype
  exact frobenius_fixed_linearIndependent_fintype p k V F hF (u ∘ Subtype.val)
    (fun i => hu i.val) (hind.comp Subtype.val Subtype.val_injective)

private theorem fixedPoints_basis_linearIndependent
    (hF : ∀ (c : k) (x : V), F (c • x) = c ^ p • F x) :
    letI : Module (ZMod p) V := Module.compHom V (ZMod.castHom (dvd_refl p) k)
    LinearIndependent k
      (fun i : Module.Basis.ofVectorSpaceIndex (ZMod p)
          (AddMonoidHom.ker (F - AddMonoidHom.id V)) =>
        ((Module.Basis.ofVectorSpace (ZMod p)
          (AddMonoidHom.ker (F - AddMonoidHom.id V))) i : V)) := by
  classical
  let : Module (ZMod p) V := Module.compHom V (ZMod.castHom (dvd_refl p) k)
  let K := AddMonoidHom.ker (F - AddMonoidHom.id V)
  let b := Module.Basis.ofVectorSpace (ZMod p) K
  let incl : K →ₗ[ZMod p] V :=
    { toFun := fun x => x.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact frobenius_fixed_linearIndependent p k V F hF (fun i => incl (b i))
    (fun i => sub_eq_zero.mp ((AddMonoidHom.mem_ker).1 (b i).property))
    (b.linearIndependent.map' incl (LinearMap.ker_eq_bot'.2 fun _ hx => Subtype.ext hx))

/-- The fixed points of a Frobenius-semilinear additive endomorphism of a
finite-dimensional vector space are finite-dimensional over the prime field. -/
@[stacks 0A3L "kernel_bound"]
theorem fixedPoints_finiteDimensional_of_frobenius_semilinear
    (hF : ∀ (c : k) (x : V), F (c • x) = c ^ p • F x) :
    letI : Module (ZMod p) V :=
      Module.compHom V (ZMod.castHom (dvd_refl p) k)
    FiniteDimensional (ZMod p) (AddMonoidHom.ker (F - AddMonoidHom.id V)) := by
  classical
  let : Module (ZMod p) V := Module.compHom V (ZMod.castHom (dvd_refl p) k)
  have := (fixedPoints_basis_linearIndependent p k V F hF).finite
  exact (Module.Basis.ofVectorSpace (ZMod p) _).finiteDimensional_of_finite

/-- The dimension over the prime field of the fixed points of a
Frobenius-semilinear additive endomorphism is at most the dimension of the
original vector space. -/
@[stacks 0A3L "kernel_bound"]
theorem finrank_fixedPoints_le_of_frobenius_semilinear
    (hF : ∀ (c : k) (x : V), F (c • x) = c ^ p • F x) :
    letI : Module (ZMod p) V :=
      Module.compHom V (ZMod.castHom (dvd_refl p) k)
    Module.finrank (ZMod p) (AddMonoidHom.ker (F - AddMonoidHom.id V)) ≤
      Module.finrank k V := by
  classical
  let : Module (ZMod p) V := Module.compHom V (ZMod.castHom (dvd_refl p) k)
  let K := AddMonoidHom.ker (F - AddMonoidHom.id V)
  have : FiniteDimensional (ZMod p) K :=
    fixedPoints_finiteDimensional_of_frobenius_semilinear p k V F hF
  let : Fintype (Module.Basis.ofVectorSpaceIndex (ZMod p) K) := Fintype.ofFinite _
  exact (Module.finrank_eq_card_basis (Module.Basis.ofVectorSpace (ZMod p) K)).trans_le
    (fixedPoints_basis_linearIndependent p k V F hF).fintype_card_le_finrank

