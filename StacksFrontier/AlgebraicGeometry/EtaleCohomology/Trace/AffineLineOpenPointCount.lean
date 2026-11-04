module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FieldValuedPointCount
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ConstantSheafCurve
public import Mathlib.FieldTheory.Finite.Extension

/-!
# Points of an open of the affine line over a finite field

For an open `V` of `𝔸¹_k`, `k` a finite field with `q` elements, the number of points of `V` over
the extension of degree `N` of `k`, `∑_{deg y ∣ N} deg y`, is at most `q ^ N`: `V(k_N)` embeds
into `𝔸¹(k_N) = k_N` (a `k`-morphism `Spec k_N → 𝔸¹` is the image of `X` in `k_N`).

## Main results

* `Stacks.EtaleCohomology.finsum_residueDegree_le_of_isOpenImmersion_affineLine`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

variable {k : Type u} [Field k] [Fintype k]

omit [Fintype k] in
/-- `k`-points of `𝔸¹` with values in a field `K` are determined by the image of `X`. -/
theorem injective_fieldValuedPoints_affineLine (K : Type u) [Field K] [Algebra k K] :
    Function.Injective fun v : fieldValuedPoints
        (Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k)))) K =>
      (Spec.preimage v.1).hom Polynomial.X := by
  intro v w hvw
  have hk : ∀ u : fieldValuedPoints (Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k)))) K,
      CommRingCat.ofHom (algebraMap k (Polynomial k)) ≫ Spec.preimage u.1 =
        CommRingCat.ofHom (algebraMap k K) := fun u => by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage]
    exact u.2
  have hφ : Spec.preimage v.1 = Spec.preimage w.1 := by
    ext1
    refine Polynomial.ringHom_ext (fun a => ?_) hvw
    have h1 := congrArg (fun φ => φ.hom a) (hk v)
    have h2 := congrArg (fun φ => φ.hom a) (hk w)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom,
      Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply] at h1 h2
    rw [h1, h2]
  apply Subtype.ext
  rw [← Spec.map_preimage v.1, ← Spec.map_preimage w.1, hφ]

omit [Fintype k] in
/-- A finite field has an extension of every degree `N > 0` in its own universe: the image of
`FiniteField.Extension` in an algebraic closure. -/
theorem exists_finite_extension_finrank_eq [Finite k] (p : ℕ) [Fact p.Prime] [CharP k p] (N : ℕ)
    (hN : 0 < N) : ∃ (K : Type u) (_ : Field K) (_ : Algebra k K), Finite K ∧
      Module.finrank k K = N := by
  have : NeZero N := ⟨hN.ne'⟩
  let φ : FiniteField.Extension k p N →ₐ[k] AlgebraicClosure k := IsAlgClosed.lift
  let e : FiniteField.Extension k p N ≃ₐ[k] φ.fieldRange.toSubalgebra :=
    (AlgEquiv.ofInjectiveField φ).trans
      (Subalgebra.equivOfEq _ _ (AlgHom.fieldRange_toSubalgebra φ).symm)
  have hrank : Module.finrank k φ.fieldRange = N := by
    have := e.toLinearEquiv.finrank_eq
    rw [FiniteField.finrank_extension] at this
    exact this.symm
  have : Module.Finite k φ.fieldRange :=
    Module.finite_of_finrank_pos (by rwa [hrank])
  exact ⟨φ.fieldRange, inferInstance, inferInstance, Module.finite_of_finite k, hrank⟩

/-- **Points of an open of the affine line.**  For `V ⊆ 𝔸¹_k` open, `∑_{deg y ∣ N} deg y ≤ q ^ N`
for every `N > 0`, `q = #k`. -/
public theorem finsum_residueDegree_le_of_isOpenImmersion_affineLine (p : ℕ) [Fact p.Prime]
    [CharP k p] {V : Scheme.{u}} (f : V ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f]
    (e : V ⟶ Spec (.of (Polynomial k))) [IsOpenImmersion e]
    (he : e ≫ Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))) = f) (N : ℕ)
    (hN : 0 < N) :
    (∑ᶠ (y : closedPoints V) (_ : residueDegree f y.1 ∣ N), (residueDegree f y.1 : ℝ)) ≤
      (Fintype.card k : ℝ) ^ N := by
  classical
  obtain ⟨K, _, _, _, hfin⟩ := exists_finite_extension_finrank_eq (k := k) p N hN
  have hS : {y : closedPoints V | residueDegree f y.1 ∣ N}.Finite :=
    (finite_setOf_closedPoints_residueDegree_le f N).subset fun y hy => Nat.le_of_dvd hN hy
  show ∑ᶠ y ∈ {y : closedPoints V | residueDegree f y.1 ∣ N}, (residueDegree f y.1 : ℝ) ≤ _
  rw [finsum_mem_eq_finite_toFinset_sum _ hS]
  have hset : hS.toFinset = (closedPointsDegreeLE f (Module.finrank k K)).filter
      (fun x => residueDegree f x.1 ∣ Module.finrank k K) := by
    ext y
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Finset.mem_filter, closedPointsDegreeLE,
      hfin]
    exact ⟨fun h => ⟨Nat.le_of_dvd hN h, h⟩, fun h => h.2⟩
  rw [hset, ← Nat.cast_sum, ← natCard_fieldValuedPoints f K]
  have hinjV : Function.Injective fun u : fieldValuedPoints f K =>
      (⟨u.1 ≫ e, by rw [Category.assoc, he]; exact u.2⟩ : fieldValuedPoints
        (Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k)))) K) :=
    fun u u' h => Subtype.ext ((cancel_mono e).1 (congrArg Subtype.val h))
  have hinjA := injective_fieldValuedPoints_affineLine (k := k) K
  have hfinA : Finite (fieldValuedPoints
      (Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k)))) K) := Finite.of_injective _ hinjA
  have h3 : Nat.card K = Fintype.card k ^ N := by
    have : Module.Finite k K := Module.Finite.of_finite
    rw [Module.natCard_eq_pow_finrank (K := k) (V := K), hfin, Nat.card_eq_fintype_card]
  exact_mod_cast (@Nat.card_le_card_of_injective _ _ hfinA _ hinjV).trans
    ((Nat.card_le_card_of_injective _ hinjA).trans h3.le)

end Stacks.EtaleCohomology

end
