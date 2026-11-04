module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniGenericLine
public import StacksFrontier.FieldTheory.PrimitiveHypersurfaceModel
public import StacksFrontier.RingTheory.GeometricallyIntegral.GenericPointIrreducible
public import StacksFrontier.RingTheory.Polynomial.MinpolyAbsolutelyIrreducible
public import StacksFrontier.RingTheory.Polynomial.PlaneCurvePointAvoiding
public import StacksFrontier.RingTheory.Polynomial.PlaneCurveSpecialization
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Points of every large degree on a geometrically irreducible variety over a finite field

The remark Stacks Tag 0BA7 needs the following consequence of the Lang–Weil estimates. Let `A` be
a geometrically irreducible algebra of finite type over a finite field `k`. Then for `n ≫ 0` there
is a `k`-algebra map `A → k'` with `[k' : k] = n`.

This module reduces that statement to the Weil lower bound for absolutely irreducible plane
curves, in the uniform form "over every finite field with enough elements, every absolutely
irreducible `f` of degree at most `d` has a point off any `g` of degree at most `e` that `f` does
not divide". The reduction runs as follows.

1. Replace `A` by its reduction and pass to `K = Frac(A_red)(X)`, a finitely generated,
   geometrically irreducible, non-algebraic extension of `k`
   (`Algebra.exists_transcendental_field_model`).
2. `K` is the function field of a hypersurface `P(t₀, …, tₙ, Y) = 0`, with `t` a separating
   transcendence basis, and `A` maps into the localization of its coordinate ring at some
   `g ∈ k[t]` (`StacksFrontier.FieldTheory.PrimitiveHypersurfaceModel`).
3. The preimage of the generic line `tᵢ = (ξᵢ + x₁ᵢ t₀)/x₀ᵢ` is a geometrically irreducible curve
   over the parameter field `E` (Stacks Tag 0G4D, in
   `StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniGenericLine`). Its fibre coordinate is
   separable, so its minimal polynomial over `E[t₀]` is absolutely irreducible
   (`StacksFrontier.RingTheory.Polynomial.MinpolyAbsolutelyIrreducible`).
4. Away from a nonzero `h` in the parameter ring every specialization stays absolutely irreducible
   of bounded degree (Stacks Tag 0557,
   `StacksFrontier.RingTheory.Polynomial.PlaneCurveSpecialization`).
   Over a finite field with more elements than `deg h`, Schwartz–Zippel gives parameters avoiding
   `h`.
5. The Weil bound gives a point on the specialized curve off `g`, hence a point of `A`.

## Main results

* `MvPolynomial.exists_eval_ne_zero_of_totalDegree_lt_card`: Schwartz–Zippel, in the form "a
  nonzero polynomial has a non-root over a large finite domain".
* `Algebra.exists_transcendental_field_model`: step 1.
* `Algebra.exists_forall_nonempty_algHom_of_isGeometricallyIrreducible_of_planeCurve`: **the
  reduction.** Points of every large degree on absolutely irreducible plane curves, uniformly in
  the degrees, give points of every large degree on `A`.
* `Algebra.exists_forall_nonempty_algHom_of_isGeometricallyIrreducible`: **the result**, the
  reduction applied to the Weil lower bound
  `MvPolynomial.exists_eval_eq_zero_and_eval_ne_zero_of_irreducible_map_algebraicClosure`.

## References

* [Stacks Project, Tag 0BA7](https://stacks.math.columbia.edu/tag/0BA7)
* [Stacks Project, Tag 0G4D](https://stacks.math.columbia.edu/tag/0G4D)
* [Stacks Project, Tag 0557](https://stacks.math.columbia.edu/tag/0557)
* S. Lang, A. Weil, *Number of points of varieties in finite fields*, Amer. J. Math. 76 (1954).
-/

@[expose] public section

universe u

open Polynomial

namespace MvPolynomial

/-- **A nonzero polynomial has a non-root once the field is large.** Over a finite domain `R` with
more elements than the total degree of `p ≠ 0`, some point of `R^σ` is not a root of `p`. This is
the Schwartz–Zippel lemma. -/
@[sga "3 XXIV 3.9.1" "special case"]
theorem exists_eval_ne_zero_of_totalDegree_lt_card {σ R : Type*} [Finite σ] [CommRing R]
    [IsDomain R] [Fintype R] {p : MvPolynomial σ R} (hp : p ≠ 0)
    (hdeg : p.totalDegree < Fintype.card R) : ∃ x : σ → R, eval x p ≠ 0 := by
  classical
  obtain ⟨N, ⟨e⟩⟩ := Finite.exists_equiv_fin σ
  set p' := renameEquiv R e p
  have hp' : p' ≠ 0 := (map_ne_zero_iff _ (renameEquiv R e).injective).mpr hp
  have hdeg' : p'.totalDegree < Fintype.card R := by
    rwa [totalDegree_renameEquiv]
  by_contra! h
  have hall : ∀ x : Fin N → R, eval x p' = 0 := fun x => by
    simpa [p', eval_rename] using h (x ∘ e)
  have hsz := schwartz_zippel_totalDegree hp' Finset.univ
  rw [Finset.filter_true_of_mem (fun x _ => hall x), Fintype.piFinset_univ, Finset.card_univ,
    Fintype.card_fun, Fintype.card_fin, Finset.card_univ] at hsz
  have hq : (0 : ℚ≥0) < Fintype.card R := by exact_mod_cast Fintype.card_pos
  rw [Nat.cast_pow, div_self (pow_ne_zero _ hq.ne'), le_div_iff₀ hq, one_mul] at hsz
  exact absurd (by exact_mod_cast hsz : Fintype.card R ≤ p'.totalDegree) (not_le.mpr hdeg')

end MvPolynomial

/-- An algebraically independent family `t` on `Fin (n + 1)` stays algebraically independent when
reindexed by `Option (Fin n ⊕ PEmpty)`, sending `none` to `t 0` and `some i` to `t i.succ`. -/
private theorem AlgebraicIndependent.option_elim_zero_succ {k K : Type*} [CommRing k] [CommRing K]
    [Algebra k K] {n : ℕ} {t : Fin (n + 1) → K} (ht : AlgebraicIndependent k t) :
    AlgebraicIndependent k fun o : Option (Fin n ⊕ PEmpty.{u + 1}) =>
      o.elim (t 0) (Sum.elim (t ∘ Fin.succ) PEmpty.elim) := by
  let f : Option (Fin n ⊕ PEmpty.{u + 1}) → Fin (n + 1) := fun o =>
    o.elim 0 (Sum.elim Fin.succ PEmpty.elim)
  have hf : Function.Injective f := by
    rintro (_ | _ | ⟨⟨⟩⟩) (_ | _ | ⟨⟨⟩⟩) <;> simp [f, Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm]
  convert ht.comp f hf using 1
  funext o
  rcases o with _ | _ | ⟨⟨⟩⟩ <;> rfl

namespace Algebra

/-- A geometrically irreducible algebra has an irreducible spectrum. -/
theorem IsGeometricallyIrreducible.irreducibleSpace (k A : Type u) [Field k] [CommRing A]
    [Algebra k A] (hA : Algebra.IsGeometricallyIrreducible k A) :
    IrreducibleSpace (PrimeSpectrum A) := by
  have := (isGeometricallyIrreducible_iff_irreducibleSpace_primeSpectrum_tensorProduct k A).mp
    hA k
  exact irreducibleSpace_primeSpectrum_of_injective
    (Algebra.TensorProduct.rid k k A).symm.toRingHom
    (Algebra.TensorProduct.rid k k A).symm.injective

/-- **A transcendental field model.** A geometrically irreducible algebra `A` of finite type over a
field `k` maps to a finitely generated subalgebra of a finitely generated, geometrically
irreducible, non-algebraic field extension `K` of `k`. One may take `K = Frac(A_red)(X)`. -/
theorem exists_transcendental_field_model (k A : Type u) [Field k] [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] (hA : Algebra.IsGeometricallyIrreducible k A) :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K), Algebra.EssFiniteType k K ∧
      Algebra.IsGeometricallyIrreducible k K ∧ (∃ z : K, Transcendental k z) ∧
      ∃ B : Subalgebra k K, Algebra.FiniteType k B ∧ Nonempty (A →ₐ[k] B) := by
  classical
  set A₀ := A ⧸ nilradical A
  have hA₀ : Algebra.IsGeometricallyIrreducible k A₀ :=
    (isGeometricallyIrreducible_iff_quotient_of_le_nilradical k A (nilradical A) le_rfl).mp hA
  have hirr := IsGeometricallyIrreducible.irreducibleSpace k A hA
  have hprime : (nilradical A).IsPrime := by
    rw [show nilradical A = (⊥ : Ideal A).radical from rfl,
      ← PrimeSpectrum.isIrreducible_zeroLocus_iff, PrimeSpectrum.zeroLocus_bot]
    exact hirr.isIrreducible_univ
  have : IsDomain A₀ := Ideal.Quotient.isDomain _
  set K₀ := FractionRing A₀
  have hK₀ : Algebra.IsGeometricallyIrreducible k K₀ :=
    (isGeometricallyIrreducible_iff_isFractionRing k A₀ K₀).mp hA₀
  set K := FractionRing (Polynomial K₀)
  have hKK₀ : Algebra.IsGeometricallyIrreducible K₀ K :=
    (isGeometricallyIrreducible_iff_isFractionRing K₀ (Polynomial K₀) K).mp
      (Algebra.isGeometricallyIrreducible_polynomial K₀)
  have hK : Algebra.IsGeometricallyIrreducible k K :=
    Algebra.IsGeometricallyIrreducible.trans k K₀ K
  have : Algebra.EssFiniteType k (Polynomial K₀) := Algebra.EssFiniteType.comp k K₀ (Polynomial K₀)
  refine ⟨K, inferInstance, inferInstance, inferInstance, hK, ⟨algebraMap (Polynomial K₀) K X, ?_⟩,
    (IsScalarTower.toAlgHom k A₀ K).range, ?_, ?_⟩
  · have h1 : Transcendental K₀ (algebraMap (Polynomial K₀) K X) :=
      (transcendental_algebraMap_iff (IsFractionRing.injective (Polynomial K₀) K)).mpr
        (Polynomial.transcendental_X K₀)
    exact h1.restrictScalars (algebraMap k K₀).injective
  · exact Algebra.FiniteType.of_surjective (IsScalarTower.toAlgHom k A₀ K).rangeRestrict
      (AlgHom.rangeRestrict_surjective _)
  · exact ⟨(IsScalarTower.toAlgHom k A₀ K).rangeRestrict.comp (Ideal.Quotient.mkₐ k _)⟩

/-- A fraction field generated by an algebraically independent family is a fraction field of the
polynomial ring on that family. -/
theorem isFractionRing_mvPolynomial_of_adjoin_eq_top {k E σ : Type*} [Field k] [Field E]
    [Algebra k E] {p : σ → E} (hind : AlgebraicIndependent k p)
    (hgen : IntermediateField.adjoin k (Set.range p) = ⊤) [Algebra (MvPolynomial σ k) E]
    (h : ∀ f, algebraMap (MvPolynomial σ k) E f = MvPolynomial.aeval p f) :
    IsFractionRing (MvPolynomial σ k) E := by
  have hinj : Function.Injective (algebraMap (MvPolynomial σ k) E) := by
    intro a b hab
    rw [h, h] at hab
    exact hind hab
  have : FaithfulSMul (MvPolynomial σ k) E :=
    (faithfulSMul_iff_algebraMap_injective _ E).mpr hinj
  refine IsFractionRing.of_field _ E fun w => ?_
  have hw : w ∈ IntermediateField.adjoin k (Set.range p) := hgen ▸ IntermediateField.mem_top
  obtain ⟨r, hr, q, hq, rfl⟩ := IntermediateField.mem_adjoin_iff_div.mp hw
  rw [Algebra.adjoin_range_eq_range_aeval] at hr hq
  obtain ⟨a, rfl⟩ := hr
  obtain ⟨b, rfl⟩ := hq
  exact ⟨a, b, by rw [h, h]; rfl⟩

section GenericLine

variable {k K E L : Type*} [Field k] [Field K] [Field E] [Field L] [Algebra k K] [Algebra k E]
  [Algebra E L] [Algebra k L] [Algebra K L] [IsScalarTower k E L] [IsScalarTower k K L]

/-- **The generic line as a substitution.** If `t i.succ = (p i 2 + p i 1 t₀) / p i 0` in `L`, then
evaluating at `t₀` after substituting `Λ = (X, p i 2 / p i 0 + (p i 1 / p i 0) X)` for the
variables agrees with evaluating at `t`. -/
private theorem aeval_aeval_eq_of_genericLine {n : ℕ} {t : Fin (n + 1) → K} {p : Fin n → Fin 3 → E}
    {Λ : Fin (n + 1) → E[X]} (hp : ∀ i, p i 0 ≠ 0) (hΛ₀ : Λ 0 = Polynomial.X)
    (hΛ : ∀ i, Λ i.succ = C (p i 2 / p i 0) + C (p i 1 / p i 0) * Polynomial.X)
    (hrel : ∀ i, algebraMap K L (t i.succ) * algebraMap E L (p i 0) =
      algebraMap E L (p i 2) + algebraMap E L (p i 1) * algebraMap K L (t 0))
    (f : MvPolynomial (Fin (n + 1)) k) :
    aeval (algebraMap K L (t 0)) (MvPolynomial.aeval Λ f) =
      algebraMap K L (MvPolynomial.aeval t f) := by
  have key : ((aeval (algebraMap K L (t 0))).restrictScalars k).comp (MvPolynomial.aeval Λ) =
      (IsScalarTower.toAlgHom k K L).comp (MvPolynomial.aeval t) := by
    apply MvPolynomial.algHom_ext
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [hΛ₀]
    · simp only [AlgHom.comp_apply, MvPolynomial.aeval_X, hΛ, AlgHom.restrictScalars_apply,
        map_add, map_mul, aeval_C, aeval_X, IsScalarTower.coe_toAlgHom', map_div₀]
      rw [div_mul_eq_mul_div, ← add_div,
        div_eq_iff ((map_ne_zero_iff _ (algebraMap E L).injective).mpr (hp j)), hrel j]
  exact DFunLike.congr_fun key f

/-- If `L` is generated over `E` by the image of `K = k(t, y)`, and every `t i` is a polynomial
over `E` in `τ`, then `L` is generated over `E` by `τ` and the image of `y`. -/
private theorem adjoin_pair_eq_top_of_forall_eq_aeval {n : ℕ} {t : Fin n → K} {y : K}
    (hgen : IntermediateField.adjoin k (Set.range t ∪ {y}) = ⊤)
    (hLgen : IntermediateField.adjoin E (Set.range (algebraMap K L)) = ⊤) {τ : L}
    (hτ : ∀ i, ∃ q : E[X], algebraMap K L (t i) = aeval τ q) :
    IntermediateField.adjoin E {τ, algebraMap K L y} = ⊤ := by
  refine adjoin_eq_top_of_image_subset hgen hLgen ?_
  rintro _ ⟨w, hw, rfl⟩
  rcases hw with ⟨i, rfl⟩ | hw
  · obtain ⟨q, hq⟩ := hτ i
    rw [hq]
    exact IntermediateField.algebra_adjoin_le_adjoin E _
      (Algebra.adjoin_mono (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))
        (Polynomial.aeval_mem_adjoin_singleton E τ))
  · rw [Set.mem_singleton_iff.mp hw]
    exact IntermediateField.subset_adjoin E _ (Set.mem_insert_of_mem _ rfl)

end GenericLine

/-- **Points of every large degree, from a specialization.** Suppose absolutely irreducible plane
curves have points over all large finite fields, uniformly in the degrees, and that every
`k`-algebra map `φ : k[σ] → F` with `φ h ≠ 0` yields such a curve of degrees at most `d, e` whose
points off `g'` give `k`-algebra maps `ψ : k[t][Y] → F` killing `P` but not `g`. Then such a `ψ`
exists to every large finite extension of the finite field `k`. -/
private theorem exists_forall_exists_algHom_of_specialization
    (hW : ∀ d e : ℕ, ∃ N : ℕ, ∀ (F : Type u) [Field F] [Fintype F], N < Fintype.card F →
      ∀ f g : MvPolynomial (Fin 2) F, f.totalDegree ≤ d → g.totalDegree ≤ e →
        Irreducible (f.map (algebraMap F (AlgebraicClosure F))) → ¬ f ∣ g →
          ∃ x : Fin 2 → F, MvPolynomial.eval x f = 0 ∧ MvPolynomial.eval x g ≠ 0)
    {k : Type u} [Field k] [Finite k] {σ τ : Type*} [Finite σ] {P : Polynomial (MvPolynomial τ k)}
    {g : MvPolynomial τ k} {h : MvPolynomial σ k} (hh0 : h ≠ 0) {d e : ℕ}
    (hspec : ∀ (F : Type u) [Field F] [Algebra k F] (φ : MvPolynomial σ k →ₐ[k] F), φ h ≠ 0 →
      ∃ f g' : MvPolynomial (Fin 2) F, f.totalDegree ≤ d ∧ g'.totalDegree ≤ e ∧
        Irreducible (f.map (algebraMap F (AlgebraicClosure F))) ∧ ¬ f ∣ g' ∧
        ∀ x : Fin 2 → F, MvPolynomial.eval x f = 0 → MvPolynomial.eval x g' ≠ 0 →
          ∃ ψ : Polynomial (MvPolynomial τ k) →ₐ[k] F, ψ P = 0 ∧ ψ (C g) ≠ 0) :
    ∃ N : ℕ, ∀ (k' : Type u) [Field k'] [Algebra k k'] [Finite k'], N < Nat.card k' →
      ∃ ψ : Polynomial (MvPolynomial τ k) →ₐ[k] k', ψ P = 0 ∧ ψ (C g) ≠ 0 := by
  obtain ⟨NW, hNW⟩ := hW d e
  refine ⟨max NW h.totalDegree, fun k' _ _ _ hcard => ?_⟩
  have : Fintype k' := Fintype.ofFinite k'
  rw [Nat.card_eq_fintype_card] at hcard
  have hh' : h.map (algebraMap k k') ≠ 0 := fun h0 =>
    hh0 (MvPolynomial.map_injective _ (algebraMap k k').injective (by rw [h0, map_zero]))
  obtain ⟨v, hv⟩ := MvPolynomial.exists_eval_ne_zero_of_totalDegree_lt_card hh'
    ((MvPolynomial.totalDegree_map_le _ _).trans_lt ((le_max_right _ _).trans_lt hcard))
  obtain ⟨f, g', hfd, hge, hfirr, hndvd, hpt⟩ := hspec k' (MvPolynomial.aeval v)
    (by rwa [MvPolynomial.eval_map, ← MvPolynomial.aeval_def] at hv)
  obtain ⟨x, hx0, hx1⟩ := hNW k' ((le_max_left _ _).trans_lt hcard) f g' hfd hge hfirr hndvd
  exact hpt x hx0 hx1

/-- **Points of every large degree on a hypersurface model.** Let `K` be a finitely generated,
geometrically irreducible extension of a finite field `k`, the function field of the hypersurface
`P(t, Y) = 0`, and let `g(t) ≠ 0`. If absolutely irreducible plane curves have points over all
large finite fields, uniformly in the degrees, then every large finite extension `k'` of `k`
carries a point `ψ` of the hypersurface off `g = 0`. -/
private theorem exists_forall_exists_algHom_of_hypersurface_model
    (hW : ∀ d e : ℕ, ∃ N : ℕ, ∀ (F : Type u) [Field F] [Fintype F], N < Fintype.card F →
      ∀ f g : MvPolynomial (Fin 2) F, f.totalDegree ≤ d → g.totalDegree ≤ e →
        Irreducible (f.map (algebraMap F (AlgebraicClosure F))) → ¬ f ∣ g →
          ∃ x : Fin 2 → F, MvPolynomial.eval x f = 0 ∧ MvPolynomial.eval x g ≠ 0)
    {k K : Type u} [Field k] [Finite k] [Field K] [Algebra k K] [Algebra.EssFiniteType k K]
    [Algebra.IsGeometricallyIrreducible k K] {n : ℕ} {t : Fin (n + 1) → K} {y : K}
    {P : Polynomial (MvPolynomial (Fin (n + 1)) k)} (ht : AlgebraicIndependent k t) (hPm : P.Monic)
    (hker : ∀ f, eval₂ (MvPolynomial.aeval t).toRingHom y f = 0 ↔ P ∣ f)
    (hder : eval₂ (MvPolynomial.aeval t).toRingHom y (derivative P) ≠ 0)
    (hgen : IntermediateField.adjoin k (Set.range t ∪ {y}) = ⊤)
    {g : MvPolynomial (Fin (n + 1)) k} (hg : MvPolynomial.aeval t g ≠ 0) :
    ∃ N : ℕ, ∀ (k' : Type u) [Field k'] [Algebra k k'] [Finite k'], N < Nat.card k' →
      ∃ ψ : Polynomial (MvPolynomial (Fin (n + 1)) k) →ₐ[k] k', ψ P = 0 ∧ ψ (C g) ≠ 0 := by
  classical
  obtain ⟨E, L, _, _, _, _, _, _, _, _, p, hpind, hpgen, hLgi, hLgen, hsw, hrel⟩ :=
    exists_isGeometricallyIrreducible_genericLine k K
      (IntermediateField.fg_top_iff.mpr inferInstance) n (t 0) (t ∘ Fin.succ) PEmpty.elim
      ht.option_elim_zero_succ
  set τ := algebraMap K L (t 0)
  set η := algebraMap K L y
  let : Algebra E[X] L := (Polynomial.aeval τ).toRingHom.toAlgebra
  have hτX : algebraMap E[X] L X = τ := by simp [RingHom.algebraMap_toAlgebra]
  have : IsScalarTower E E[X] L := IsScalarTower.of_algebraMap_eq fun c => by
    simp [RingHom.algebraMap_toAlgebra]
  have hτ : Transcendental E τ :=
    (algebraicIndependent_singleton_iff (none : Option PEmpty.{u + 1})).mp hsw
  let Λ : Fin (n + 1) → E[X] :=
    Fin.cons Polynomial.X fun i => C (p i 2 / p i 0) + C (p i 1 / p i 0) * Polynomial.X
  have hΛ : ∀ f : MvPolynomial (Fin (n + 1)) k,
      aeval τ (MvPolynomial.aeval Λ f) = algebraMap K L (MvPolynomial.aeval t f) :=
    aeval_aeval_eq_of_genericLine (fun i => hpind.ne_zero (i, 0)) (Fin.cons_zero _ _)
      (fun i => Fin.cons_succ _ _ i) hrel
  have hev : ∀ f : Polynomial (MvPolynomial (Fin (n + 1)) k),
      aeval η (f.map (MvPolynomial.aeval Λ).toRingHom) =
        algebraMap K L (eval₂ (MvPolynomial.aeval t).toRingHom y f) := by
    intro f
    rw [aeval_def, eval₂_map, hom_eval₂]
    congr 1
    exact RingHom.ext hΛ
  set Q := P.map (MvPolynomial.aeval Λ).toRingHom
  have hQ : aeval η Q = 0 := by rw [hev, (hker P).mpr dvd_rfl, map_zero]
  have hQ' : aeval η (derivative Q) ≠ 0 := by
    rw [derivative_map, hev]
    exact (map_ne_zero_iff _ (algebraMap K L).injective).mpr hder
  have hηint : IsIntegral E[X] η := ⟨Q, hPm.map _, hQ⟩
  have hgenL : IntermediateField.adjoin E {algebraMap E[X] L X, η} = ⊤ := by
    rw [hτX]
    exact adjoin_pair_eq_top_of_forall_eq_aeval hgen hLgen fun i =>
      ⟨Λ i, by simpa using (hΛ (MvPolynomial.X i)).symm⟩
  have hdom := isDomain_tensorProduct_algebraicClosure_of_separable_root (hτX ▸ hτ) hgenL hQ hQ'
  have : Module.IsTorsionFree E[X] L := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    exact transcendental_iff_injective.mp hτ
  have hR := Polynomial.irreducible_map_equivMvPolynomial_minpoly (AlgebraicClosure E) hηint
  let D := MvPolynomial (Fin n × Fin 3) k
  let : Algebra D E := (MvPolynomial.aeval fun q : Fin n × Fin 3 => p q.1 q.2).toAlgebra
  have : IsScalarTower k D E := IsScalarTower.of_algebraMap_eq fun c => by
    simp [RingHom.algebraMap_toAlgebra]
  have : IsFractionRing D E := isFractionRing_mvPolynomial_of_adjoin_eq_top hpind hpgen fun _ => rfl
  obtain ⟨h, hh0, d, e, hspec⟩ := Polynomial.exists_specialization_planeCurve.{u} (D := D) P g Λ
    (minpoly.monic hηint) (minpoly.natDegree_pos hηint) (minpoly.isIntegrallyClosed_dvd hηint hQ)
    hR fun h0 => hg ((algebraMap K L).injective (by rw [← hΛ g, h0, map_zero, map_zero]))
  exact exists_forall_exists_algHom_of_specialization hW hh0 hspec

/-- **Points of every large degree, from points on plane curves.** Suppose that absolutely
irreducible plane curves have points over all large finite fields, uniformly in the degrees: for
all `d, e` there is `N` such that over every finite field `F` with more than `N` elements, every
`f, g ∈ F[x, y]` of total degrees at most `d` and `e`, with `f` irreducible over an algebraic
closure of `F` and `f ∤ g`, have a common point with `f = 0` and `g ≠ 0`.

Then a geometrically irreducible algebra `A` of finite type over a finite field `k` has a
`k`-algebra map to every finite extension `k'` of `k` with more than some `N` elements, hence to
the extension of degree `n` for every `n ≫ 0`. -/
theorem exists_forall_nonempty_algHom_of_isGeometricallyIrreducible_of_planeCurve
    (hW : ∀ d e : ℕ, ∃ N : ℕ, ∀ (F : Type u) [Field F] [Fintype F], N < Fintype.card F →
      ∀ f g : MvPolynomial (Fin 2) F, f.totalDegree ≤ d → g.totalDegree ≤ e →
        Irreducible (f.map (algebraMap F (AlgebraicClosure F))) → ¬ f ∣ g →
          ∃ x : Fin 2 → F, MvPolynomial.eval x f = 0 ∧ MvPolynomial.eval x g ≠ 0)
    (k A : Type u) [Field k] [Finite k] [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    (hA : Algebra.IsGeometricallyIrreducible k A) :
    ∃ N : ℕ, ∀ (k' : Type u) [Field k'] [Algebra k k'] [Finite k'], N < Nat.card k' →
      Nonempty (A →ₐ[k] k') := by
  obtain ⟨K, _, _, hKfin, hK, ⟨z, hz⟩, B, hBft, ⟨toB⟩⟩ := exists_transcendental_field_model k A hA
  obtain ⟨n, t, y, P, ht, hPm, hker, hder, hgen⟩ := Field.exists_primitive_hypersurface_model k K hz
  obtain ⟨g, hg, hlift⟩ := Field.exists_nonempty_algHom_of_hypersurface_model ht hPm hker hgen B
  obtain ⟨N, hN⟩ := exists_forall_exists_algHom_of_hypersurface_model hW ht hPm hker hder hgen hg
  refine ⟨N, fun k' _ _ _ hcard => ?_⟩
  obtain ⟨ψ, hψP, hψg⟩ := hN k' hcard
  exact (hlift k' ψ hψP hψg).map (·.comp toB)

/-- **Points of every large degree on a geometrically irreducible variety over a finite field.**
A geometrically irreducible algebra `A` of finite type over a finite field `k` has a `k`-algebra
map to every finite extension `k'` of `k` with more than some `N` elements. Since
`#k' = #k ^ [k' : k]`, this gives a `k`-algebra map `A → k'` with `[k' : k] = n` for every `n ≫ 0`,
the consequence of the estimates of Lang and Weil used in the remark Stacks Tag 0BA7. -/
theorem exists_forall_nonempty_algHom_of_isGeometricallyIrreducible (k A : Type u) [Field k]
    [Finite k] [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    (hA : Algebra.IsGeometricallyIrreducible k A) :
    ∃ N : ℕ, ∀ (k' : Type u) [Field k'] [Algebra k k'] [Finite k'], N < Nat.card k' →
      Nonempty (A →ₐ[k] k') :=
  exists_forall_nonempty_algHom_of_isGeometricallyIrreducible_of_planeCurve
    MvPolynomial.exists_eval_eq_zero_and_eval_ne_zero_of_irreducible_map_algebraicClosure k A hA

end Algebra
