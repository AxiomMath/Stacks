module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.FieldTheory.PolynomialGaloisGroup
import Mathlib.RingTheory.Polynomial.RationalRoot
public import StacksFrontier.RingTheory.Polynomial.GaloisResolvent

/-!
# The factors of the Galois resolvent and the twisted count

Let `K` be a field and `f ∈ K[X][Y]` monic of `Y`-degree `m`, irreducible and separable over
`K(X)`. Let `fr` be a ring automorphism of `K` fixing `f` (coefficientwise) and the coefficients
`c` of a linear form whose resolvent discriminant does not vanish. The Galois resolvent of `f`
factors over `K[X]` into the minimal polynomials `Ψ` of the values `t(π)`, one for each orbit of
the Galois group `G` of `f` over `K(X)`. Twisting by `fr` permutes the roots of `f` by a
permutation `π_σ`, and

* the permutations `τ` with `Ψ ∣ Ψ^{fr}(R_τ / Δ)` number `m !` in total, `|G|` for each factor;
* their fixed points number `m !` in total, by a twisted Burnside count.

## Main results

* `Polynomial.GaloisResolventFactors.sum_card_fixed_mul`: twisted Burnside.
* `Polynomial.exists_factors_galoisResolvent`: the factorization and the two counts.
-/

@[expose] public section

open Polynomial Finset Nat

namespace Polynomial

namespace GaloisResolventFactors

/-- Conjugating a permutation does not change its number of fixed points. -/
theorem card_fixed_conj {n : ℕ} (α ρ : Equiv.Perm (Fin n)) :
    (univ.filter fun i => (ρ⁻¹ * α * ρ) i = i).card = (univ.filter fun i => α i = i).card := by
  refine Finset.card_bij (fun i _ ↦ ρ i) (fun i hi ↦ ?_) (fun i _ j _ h ↦ ρ.injective h)
    (fun j hj ↦ ⟨ρ⁻¹ j, ?_, by simp⟩)
  · have hi' := (Finset.mem_filter.mp hi).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    simpa [Equiv.Perm.mul_apply] using congrArg ρ hi'
  · have hj' := (Finset.mem_filter.mp hj).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    simp [Equiv.Perm.mul_apply, hj']

/-- **Twisted Burnside.** If a finite group acts transitively on `Fin n` (`n > 0`) through `σ`,
then for every permutation `π` the elements `π σ(h)` have `|H|` fixed points in total. -/
theorem sum_card_fixed_mul {H : Type*} [Group H] [Fintype H] {n : ℕ} (hn : 0 < n)
    (σ : H →* Equiv.Perm (Fin n)) (htrans : ∀ i j, ∃ h, σ h i = j) (π : Equiv.Perm (Fin n)) :
    ∑ h : H, (univ.filter fun i => (π * σ h) i = i).card = Fintype.card H := by
  classical
  have hfib : ∀ i j, n * (univ.filter fun h : H ↦ σ h i = j).card = Fintype.card H := by
    intro i j
    have hsize : ∀ j', (univ.filter fun h : H ↦ σ h i = j').card =
        (univ.filter fun h : H ↦ σ h i = i).card := by
      intro j'
      obtain ⟨g, hg⟩ := htrans i j'
      refine Finset.card_bij (fun h _ ↦ g⁻¹ * h) (fun h hh ↦ ?_) (fun a _ b _ hab ↦ ?_)
        (fun h hh ↦ ⟨g * h, ?_, by simp⟩)
      · have hh' := (Finset.mem_filter.mp hh).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        rw [map_mul, Equiv.Perm.mul_apply, hh', ← hg, map_inv]
        simp [Equiv.Perm.inv_def]
      · simpa using hab
      · have hh' := (Finset.mem_filter.mp hh).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        rw [map_mul, Equiv.Perm.mul_apply, hh', hg]
    have htot : ∑ j' : Fin n, (univ.filter fun h : H ↦ σ h i = j').card = Fintype.card H := by
      rw [← Finset.card_univ, ← Finset.card_eq_sum_card_fiberwise (f := fun h : H ↦ σ h i)
        (fun _ _ ↦ Finset.mem_univ _)]
    simp only [hsize, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at htot
    rw [hsize j, htot]
  have hswap : ∑ h : H, (univ.filter fun i ↦ (π * σ h) i = i).card =
      ∑ i : Fin n, (univ.filter fun h : H ↦ σ h i = π⁻¹ i).card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun h _ ↦ ?_
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.eq_inv_iff_eq]
    congr
  rw [hswap]
  have : ∀ i : Fin n, (univ.filter fun h : H ↦ σ h i = π⁻¹ i).card = Fintype.card H / n :=
    fun i ↦ by rw [← hfib i (π⁻¹ i), Nat.mul_div_cancel_left _ hn]
  simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have h0 := hfib ⟨0, hn⟩ ⟨0, hn⟩
  rw [← h0, Nat.mul_div_cancel_left _ hn]

variable {K : Type*} [Field K]

/-- An element `x` of `L` lies in the root set of `p` exactly when it is a root of the image of
`p` in `L[X]`. -/
theorem mem_rootSet_iff_mem_roots_map {F L : Type*} [Field F] [Field L] [Algebra F L]
    (p : F[X]) (x : L) : x ∈ p.rootSet L ↔ x ∈ (p.map (algebraMap F L)).roots := by
  classical
  rw [rootSet_def, Finset.mem_coe, aroots_def, Multiset.mem_toFinset]

/-- The roots of a monic separable `f ∈ K[X][Y]` in the splitting field of its image over `K(X)`,
labelled by `Fin m`. -/
theorem exists_roots_labelling {m : ℕ} (f : K[X][X]) (hf : f.Monic) (hm : f.natDegree = m)
    (hsep : (f.map (algebraMap K[X] (FractionRing K[X]))).Separable) :
    ∃ e : Fin m ≃ (f.map (algebraMap K[X] (FractionRing K[X]))).rootSet
        (f.map (algebraMap K[X] (FractionRing K[X]))).SplittingField,
      f.map (algebraMap K[X] (f.map (algebraMap K[X] (FractionRing K[X]))).SplittingField) =
        ∏ i, (X - C (e i : (f.map (algebraMap K[X] (FractionRing K[X]))).SplittingField)) := by
  classical
  set F := FractionRing K[X]
  set fF := f.map (algebraMap K[X] F)
  set L := fF.SplittingField
  have hsplit : Splits (fF.map (algebraMap F L)) := SplittingField.splits fF
  have hfL : f.map (algebraMap K[X] L) = fF.map (algebraMap F L) := by
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
  have hmon : (f.map (algebraMap K[X] L)).Monic := hf.map _
  have hcard : Fintype.card (fF.rootSet L) = m := by
    rw [card_rootSet_eq_natDegree hsep hsplit, hf.natDegree_map, hm]
  let e : Fin m ≃ fF.rootSet L := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨e, ?_⟩
  have hnodup : (fF.map (algebraMap F L)).roots.Nodup := nodup_roots hsep.map
  rw [hfL, hsplit.eq_prod_roots_of_monic ((hf.map (algebraMap K[X] F)).map (algebraMap F L))]
  rw [show (fF.map (algebraMap F L)).roots = (fF.map (algebraMap F L)).roots.toFinset.val by
    rw [Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnodup], ← Finset.prod_eq_multiset_prod]
  refine (Finset.prod_bij (fun x hx ↦ e.symm ⟨x, ?_⟩) (fun _ _ ↦ Finset.mem_univ _)
    (fun a ha b hb h ↦ by simpa using congrArg (fun i ↦ ((e i : _) : L)) h)
    (fun i _ ↦ ⟨(e i : L), ?_, by simp⟩) (fun x hx ↦ by simp)).trans rfl
  · exact (mem_rootSet_iff_mem_roots_map fF x).mpr (Multiset.mem_toFinset.mp hx)
  · exact Multiset.mem_toFinset.mpr ((mem_rootSet_iff_mem_roots_map fF _).mp (e i).2)

/-- `L` with its `F`-algebra structure twisted by a ring endomorphism `tw` of `F`. -/
def TwistedField (F L : Type*) [Field F] [Field L] [Algebra F L] (_tw : F →+* F) : Type _ := L

/-- `TwistedField F L tw` is a field, namely `L`. -/
instance {F L : Type*} [Field F] [Field L] [Algebra F L] (tw : F →+* F) :
    Field (TwistedField F L tw) := inferInstanceAs (Field L)

/-- The `F`-algebra structure on `TwistedField F L tw` given by `algebraMap F L ∘ tw`. -/
instance {F L : Type*} [Field F] [Field L] [Algebra F L] (tw : F →+* F) :
    Algebra F (TwistedField F L tw) := ((algebraMap F L).comp tw).toAlgebra

/-- A ring endomorphism of `F` fixing `p` extends to the splitting field of `p`. -/
theorem exists_ringHom_extend {F L : Type*} [Field F] [Field L] [Algebra F L] (p : F[X])
    [IsSplittingField F L p] (tw : F →+* F) (hp : p.map tw = p) :
    ∃ σt : L →+* L, ∀ x, σt (algebraMap F L x) = algebraMap F L (tw x) := by
  have hspl : Splits (p.map (algebraMap F (TwistedField F L tw))) := by
    change Splits (p.map ((algebraMap F L).comp tw))
    rw [← Polynomial.map_map, hp]
    exact IsSplittingField.splits L p
  let l : L →ₐ[F] TwistedField F L tw := IsSplittingField.lift L p hspl
  exact ⟨l.toRingHom, fun x ↦ l.commutes x⟩

end GaloisResolventFactors

open GaloisResolventFactors in
open scoped Classical in
/-- Let `f ∈ K[X][Y]` be monic of `Y`-degree `m`, irreducible, and separable over `K(X)`, let
`fr` be a ring automorphism of `K` fixing `f` and the coefficients `c`, and suppose
`resolventDisc f c ≠ 0`. Then `galoisResolvent f c` is the product of a finite set `𝒪` of monic
irreducible polynomials `Ψ`, the permutations `τ` with
`Ψ ∣ twistedComp fr Ψ (resolventPerm f c τ) (resolventDisc f c)` number `m !` in total over
`Ψ ∈ 𝒪`, and the fixed points of these permutations also number `m !` in total. -/
theorem exists_factors_galoisResolvent {K : Type*} [Field K] {m : ℕ} (f : K[X][X])
    (hf : f.Monic) (hm : f.natDegree = m) (hirr : Irreducible f)
    (hsep : (f.map (algebraMap K[X] (FractionRing K[X]))).Separable)
    (fr : K ≃+* K) (hfr : f.map (mapRingHom (fr : K →+* K)) = f) (c : Fin m → K)
    (hc : ∀ i, fr (c i) = c i) (hΔ : resolventDisc f (fun i => C (c i)) ≠ 0) :
    ∃ 𝒪 : Finset K[X][X], (∀ Ψ ∈ 𝒪, Ψ.Monic ∧ Irreducible Ψ) ∧
      ∏ Ψ ∈ 𝒪, Ψ = galoisResolvent f (fun i => C (c i)) ∧
      ∑ Ψ ∈ 𝒪, (Finset.univ.filter fun τ : Equiv.Perm (Fin m) =>
        Ψ ∣ twistedComp (fr : K →+* K) Ψ (resolventPerm f (fun i => C (c i)) τ)
          (resolventDisc f (fun i => C (c i)))).card = m ! ∧
      ∑ Ψ ∈ 𝒪, ∑ τ ∈ (Finset.univ.filter fun τ : Equiv.Perm (Fin m) =>
        Ψ ∣ twistedComp (fr : K →+* K) Ψ (resolventPerm f (fun i => C (c i)) τ)
          (resolventDisc f (fun i => C (c i)))),
        (Finset.univ.filter fun i => τ i = i).card = m ! := by
  classical
  set c' : Fin m → K[X] := fun i ↦ C (c i)
  set F := FractionRing K[X]
  set fF := f.map (algebraMap K[X] F)
  set L := fF.SplittingField
  set ψ := algebraMap K[X] L
  have hψ : Function.Injective ψ := by
    rw [show ψ = (algebraMap F L).comp (algebraMap K[X] F) from IsScalarTower.algebraMap_eq _ _ _]
    exact (algebraMap F L).injective.comp (IsFractionRing.injective K[X] F)
  have : IsGalois F L := IsGalois.of_separable_splitting_field hsep
  have hm0 : 0 < m := by
    rw [← hm]; exact Nat.pos_of_ne_zero fun h ↦ hirr.not_isUnit (by
      rw [eq_one_of_monic_natDegree_zero hf h]; exact isUnit_one)
  obtain ⟨e, hb⟩ := exists_roots_labelling f hf hm hsep
  set b : Fin m → L := fun i ↦ (e i : L)
  have hbinj : Function.Injective b := fun i j h ↦ e.injective (Subtype.ext h)
  have hirrF : Irreducible fF :=
    (hf.irreducible_iff_irreducible_map_fraction_map).mp hirr
  let G := fF.Gal
  have hbroot : ∀ i, b i ∈ fF.rootSet L := fun i ↦ (e i).2
  let σ : G →* Equiv.Perm (Fin m) :=
    (Equiv.permCongrHom e.symm).toMonoidHom.comp (MulAction.toPermHom G (fF.rootSet L))
  have hσ : ∀ g i, b (σ g i) = g (b i) := fun g i ↦ by
    simp [σ, b, Equiv.permCongrHom_coe, Equiv.permCongr_apply]; rfl
  have hσinj : Function.Injective σ := by
    intro g g' h
    refine Gal.ext fF fun x hx ↦ ?_
    have h1 := hσ g (e.symm ⟨x, hx⟩)
    have h2 := hσ g' (e.symm ⟨x, hx⟩)
    simp only [b, Equiv.apply_symm_apply] at h1 h2
    rw [← h1, ← h2, h]
  have hroot : ∀ i, Polynomial.aeval (b i) fF = 0 := fun i ↦
    (Polynomial.mem_rootSet.mp (hbroot i)).2
  have htrans : ∀ i j, ∃ g, σ g i = j := by
    intro i j
    have hi := minpoly.eq_of_irreducible hirrF (hroot i)
    have hj := minpoly.eq_of_irreducible hirrF (hroot j)
    obtain ⟨g, hg⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := F) (E := L)).mp (hj.symm.trans hi)
    exact ⟨g, hbinj ((hσ g i).trans hg)⟩
  let t : Equiv.Perm (Fin m) → L := fun π ↦ ∑ i, ψ (c' i) * b (π i)
  have hgψ : ∀ (g : G) (x : K[X]), g (ψ x) = ψ x := fun g x ↦ by
    rw [IsScalarTower.algebraMap_apply K[X] F L]; exact g.commutes _
  have htg : ∀ (g : G) π, g (t π) = t (σ g * π) := fun g π ↦ by
    simp only [t, map_sum, map_mul, hgψ, Equiv.Perm.mul_apply, hσ]
  have hΔψ : ψ (resolventDisc f c') ≠ 0 := by
    rw [ne_eq, ← map_zero ψ]; exact fun h0 ↦ hΔ (hψ h0)
  have htinj : Function.Injective t := by
    intro π π' h
    by_contra hne
    have hspec := (galoisResolvent_spec f c' ψ b hb).2.1
    rw [hspec] at hΔψ
    exact (Finset.prod_ne_zero_iff.mp (Finset.prod_ne_zero_iff.mp hΔψ π (Finset.mem_univ _)) π'
      (Finset.mem_erase.mpr ⟨Ne.symm hne, Finset.mem_univ _⟩)) (sub_eq_zero.mpr h)
  have hΦ : (galoisResolvent f c').map ψ = ∏ π, (X - C (t π)) :=
    (galoisResolvent_spec f c' ψ b hb).1
  let frX : K[X] ≃+* K[X] := Polynomial.mapEquiv fr
  let frF : F ≃+* F := IsFractionRing.ringEquivOfRingEquiv frX
  have hfrF : ∀ x : K[X], frF (algebraMap K[X] F x) = algebraMap K[X] F (frX x) :=
    fun x ↦ IsFractionRing.ringEquivOfRingEquiv_algebraMap frX x
  have hfF : fF.map (frF : F →+* F) = fF := by
    simp only [fF, Polynomial.map_map]
    have : (frF : F →+* F).comp (algebraMap K[X] F) =
        (algebraMap K[X] F).comp (frX : K[X] →+* K[X]) :=
      RingHom.ext hfrF
    rw [this, ← Polynomial.map_map]
    congr 1
  obtain ⟨σt, hσtF⟩ := exists_ringHom_extend (L := L) fF (frF : F →+* F) hfF
  have hσtψ : ∀ x : K[X], σt (ψ x) = ψ (frX x) := fun x ↦ by
    rw [IsScalarTower.algebraMap_apply K[X] F L, hσtF]
    change algebraMap F L (frF (algebraMap K[X] F x)) = _
    rw [hfrF, ← IsScalarTower.algebraMap_apply]
  have hσtroot : ∀ i, σt (b i) ∈ fF.rootSet L := by
    intro i
    rw [Polynomial.mem_rootSet]
    refine ⟨(hf.map _).ne_zero, ?_⟩
    have h0 := hroot i
    rw [Polynomial.aeval_def] at h0 ⊢
    have hcomp : σt.comp (algebraMap F L) = (algebraMap F L).comp (frF : F →+* F) :=
      RingHom.ext hσtF
    have := congrArg σt h0
    rwa [map_zero, Polynomial.hom_eval₂, hcomp, ← Polynomial.eval₂_map, hfF] at this
  have hπinj : Function.Injective fun i ↦ e.symm ⟨σt (b i), hσtroot i⟩ := by
    intro i j h
    have := congrArg (fun x ↦ ((e x : fF.rootSet L) : L)) h
    simp only [Equiv.apply_symm_apply] at this
    exact hbinj (σt.injective this)
  let πσ : Equiv.Perm (Fin m) := Equiv.ofBijective _ (Finite.injective_iff_bijective.mp hπinj)
  have hσtb : ∀ i, σt (b i) = b (πσ i) := fun i ↦ by
    simp [πσ, b, Equiv.ofBijective_apply]
  have hσtt : ∀ π, σt (t π) = t (πσ * π) := fun π ↦ by
    simp only [t, map_sum, map_mul, hσtψ, hσtb, Equiv.Perm.mul_apply]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    congr 2
    simp [frX, c', hc]
  have hΦmon : (galoisResolvent f c').Monic := galoisResolvent_monic f c'
  have hint : ∀ π, IsIntegral K[X] (t π) := fun π ↦ ⟨_, hΦmon, by
    rw [← Polynomial.eval_map, hΦ, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ π) (by simp)⟩
  have : Module.IsTorsionFree K[X] L := Module.isTorsionFree_iff_algebraMap_injective.mpr hψ
  let Ψ : Equiv.Perm (Fin m) → K[X][X] := fun π ↦ minpoly K[X] (t π)
  have hΨmon : ∀ π, (Ψ π).Monic := fun π ↦ minpoly.monic (hint π)
  have hΨirr : ∀ π, Irreducible (Ψ π) := fun π ↦
    (minpoly.prime_of_isIntegrallyClosed (hint π)).irreducible
  have hΨF : ∀ π, (Ψ π).map (algebraMap K[X] F) = minpoly F (t π) := fun π ↦
    (minpoly.isIntegrallyClosed_eq_field_fractions' F (hint π)).symm
  have hΨL : ∀ π, (Ψ π).map ψ = ∏ g : G, (X - C (t (σ g * π))) := by
    intro π
    set P : L[X] := ∏ g : G, (X - C (t (σ g * π)))
    have hPmon : P.Monic := monic_prod_of_monic _ _ fun g _ ↦ monic_X_sub_C _
    have hN : (Ψ π).map ψ = (minpoly F (t π)).map (algebraMap F L) := by
      rw [← hΨF, Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
    have hNmon : ((Ψ π).map ψ).Monic := (hΨmon π).map ψ
    have hinjG : Function.Injective fun g : G ↦ t (σ g * π) := fun g g' h ↦
      hσinj (mul_right_cancel (htinj h))
    have hdvd : P ∣ (Ψ π).map ψ := by
      have hle : (Finset.univ.val.map fun g : G ↦ t (σ g * π)) ≤ ((Ψ π).map ψ).roots := by
        refine (Multiset.le_iff_subset (Multiset.Nodup.map hinjG Finset.univ.nodup)).mpr ?_
        intro x hx
        obtain ⟨g, -, rfl⟩ := Multiset.mem_map.mp hx
        rw [mem_roots hNmon.ne_zero, IsRoot, hN, ← htg, eval_map, ← aeval_def]
        rw [show (g : L ≃ₐ[F] L) (t π) = (g : L ≃ₐ[F] L).toAlgHom (t π) from rfl,
          aeval_algHom_apply, minpoly.aeval, map_zero]
      have := (Multiset.prod_X_sub_C_dvd_iff_le_roots hNmon.ne_zero _).mpr hle
      rwa [Multiset.map_map] at this
    have hfix : ∀ n (h : G), (h : L ≃ₐ[F] L) (P.coeff n) = P.coeff n := by
      intro n h
      have : P.map ((h : L ≃ₐ[F] L) : L →+* L) = P := by
        simp only [P, Polynomial.map_prod, Polynomial.map_sub, map_X, map_C]
        refine Fintype.prod_equiv (Equiv.mulLeft h) _ _ fun g ↦ ?_
        simp only [Equiv.coe_mulLeft, RingHom.coe_coe, htg, map_mul, mul_assoc]
      simpa using congrArg (fun Q ↦ Q.coeff n) this
    have hlifts : P ∈ Polynomial.lifts (algebraMap F L) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      exact fun n ↦ (IsGalois.mem_range_algebraMap_iff_fixed (P.coeff n)).mpr fun h ↦ hfix n h
    obtain ⟨Q, hQ, hQdeg, hQmon⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts hPmon
    have hQroot : Polynomial.aeval (t π) Q = 0 := by
      rw [aeval_def, eval₂_eq_eval_map, hQ, eval_prod]
      refine Finset.prod_eq_zero (Finset.mem_univ 1) ?_
      simp
    have hdeg : ((Ψ π).map ψ).natDegree ≤ P.natDegree := by
      rw [hN, (minpoly.monic (hint π).tower_top).natDegree_map, ← hQdeg]
      exact natDegree_le_of_dvd (minpoly.dvd F (t π) hQroot) hQmon.ne_zero
    exact eq_of_monic_of_dvd_of_natDegree_le hPmon hNmon hdvd hdeg
  have hfibre : ∀ π π', Ψ π' = Ψ π ↔ ∃ g : G, π' = σ g * π := by
    intro π π'
    constructor
    · intro h
      have h0 : ((Ψ π).map ψ).eval (t π') = 0 := by
        rw [← h, eval_map, ← aeval_def]; exact minpoly.aeval _ _
      rw [hΨL, eval_prod] at h0
      obtain ⟨g, -, hg⟩ := Finset.prod_eq_zero_iff.mp h0
      exact ⟨g, htinj (sub_eq_zero.mp (by simpa using hg))⟩
    · rintro ⟨g, rfl⟩
      simp only [Ψ, ← htg]
      exact minpoly.algEquiv_eq ((g : L ≃ₐ[F] L).restrictScalars K[X]) (t π)
  have hfibre_eq : ∀ π, (Finset.univ.filter fun π' ↦ Ψ π' = Ψ π) =
      Finset.univ.image fun g : G ↦ σ g * π := by
    intro π
    ext π'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, hfibre π π']
    exact ⟨fun ⟨g, hg⟩ ↦ ⟨g, hg.symm⟩, fun ⟨g, hg⟩ ↦ ⟨g, hg.symm⟩⟩
  have hσπinj : ∀ π, Function.Injective fun g : G ↦ σ g * π := fun π g g' h ↦
    hσinj (mul_right_cancel h)
  have hfibre_card : ∀ π, (Finset.univ.filter fun π' ↦ Ψ π' = Ψ π).card = Fintype.card G := by
    intro π
    rw [hfibre_eq, Finset.card_image_of_injective _ (hσπinj π), Finset.card_univ]
  set 𝒪 := Finset.univ.image Ψ with h𝒪
  have hrep : ∀ Ψ₀ ∈ 𝒪, ∃ π, Ψ π = Ψ₀ := fun Ψ₀ h ↦ by
    obtain ⟨π, -, hπ⟩ := Finset.mem_image.mp h; exact ⟨π, hπ⟩
  have hconst : ∀ F : K[X][X] → ℕ, (∀ π, F (Ψ π) = Fintype.card G) →
      ∑ Ψ₀ ∈ 𝒪, F Ψ₀ = m ! := fun F hF ↦ by
    have := Finset.card_eq_sum_card_fiberwise (f := Ψ) (s := Finset.univ) (t := 𝒪)
      (fun π _ ↦ Finset.mem_image_of_mem _ (Finset.mem_univ π))
    rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin] at this
    rw [this]
    refine Finset.sum_congr rfl fun Ψ₀ h ↦ ?_
    obtain ⟨π, rfl⟩ := hrep Ψ₀ h
    rw [hF, hfibre_card]
  have hprod : ∏ Ψ₀ ∈ 𝒪, Ψ₀ = galoisResolvent f c' := by
    apply Polynomial.map_injective ψ hψ
    rw [Polynomial.map_prod, hΦ, ← Finset.prod_fiberwise_of_maps_to (g := Ψ) (t := 𝒪)
      (fun π _ ↦ Finset.mem_image_of_mem _ (Finset.mem_univ π))]
    refine Finset.prod_congr rfl fun Ψ₀ h ↦ ?_
    obtain ⟨π, rfl⟩ := hrep Ψ₀ h
    rw [hΨL, hfibre_eq, Finset.prod_image fun g _ g' _ hg ↦ hσπinj π hg]
  have hcomp : ψ.comp (frX : K[X] →+* K[X]) = σt.comp ψ := RingHom.ext fun x ↦ (hσtψ x).symm
  have hTC : ∀ π₀ τ, Polynomial.aeval (t π₀) (twistedComp (fr : K →+* K) (Ψ π₀)
      (resolventPerm f c' τ) (resolventDisc f c')) =
      ψ (resolventDisc f c') ^ (Ψ π₀).natDegree *
        (((Ψ π₀).map ψ).map σt).eval (t (π₀ * τ)) := by
    intro π₀ τ
    have hR : Polynomial.aeval (t π₀) (resolventPerm f c' τ) =
        ψ (resolventDisc f c') * t (π₀ * τ) := by
      rw [aeval_def, eval₂_eq_eval_map]
      exact (galoisResolvent_spec f c' ψ b hb).2.2 τ π₀
    have hmap : ((Ψ π₀).map ψ).map σt = ((Ψ π₀).map (frX : K[X] →+* K[X])).map ψ := by
      rw [Polynomial.map_map, Polynomial.map_map, hcomp]
    have hdeg : (((Ψ π₀).map (frX : K[X] →+* K[X])).map ψ).natDegree < (Ψ π₀).natDegree + 1 :=
      Nat.lt_succ_of_le (natDegree_map_le.trans natDegree_map_le)
    rw [hmap, eval_eq_sum_range' hdeg, twistedComp]
    simp only [map_sum, map_mul, aeval_C, map_pow, hR]
    conv_rhs => rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k ≤ (Ψ π₀).natDegree := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    rw [coeff_map, coeff_map]
    have : ((Ψ π₀).coeff k).map (fr : K →+* K) = frX ((Ψ π₀).coeff k) := rfl
    rw [show algebraMap K[X] L = ψ from rfl, this, mul_pow,
      show ψ (resolventDisc f c') ^ (Ψ π₀).natDegree =
          ψ (resolventDisc f c') ^ ((Ψ π₀).natDegree - k) * ψ (resolventDisc f c') ^ k by
        rw [← pow_add, Nat.sub_add_cancel hk']]
    simp only [RingEquiv.coe_toRingHom]
    ring
  have hT : ∀ π₀, (Finset.univ.filter fun τ : Equiv.Perm (Fin m) ↦
      Ψ π₀ ∣ twistedComp (fr : K →+* K) (Ψ π₀) (resolventPerm f c' τ) (resolventDisc f c')) =
      Finset.univ.image fun g : G ↦ π₀⁻¹ * (πσ * (σ g * π₀)) := by
    intro π₀
    ext τ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    rw [← minpoly.isIntegrallyClosed_dvd_iff (hint π₀), hTC]
    refine Iff.trans (mul_eq_zero.trans (or_iff_right (pow_ne_zero _ hΔψ))) ?_
    rw [hΨL, Polynomial.map_prod, eval_prod]
    simp only [Polynomial.map_sub, map_X, map_C, eval_sub, eval_X, eval_C, hσtt]
    rw [Finset.prod_eq_zero_iff]
    simp only [Finset.mem_univ, true_and, sub_eq_zero]
    constructor
    · rintro ⟨g, hg⟩
      refine ⟨g, ?_⟩
      rw [← htinj hg]; group
    · rintro ⟨g, rfl⟩
      refine ⟨g, congrArg t ?_⟩
      group
  have hTinj : ∀ π₀, Function.Injective fun g : G ↦ π₀⁻¹ * (πσ * (σ g * π₀)) := by
    intro π₀ g g' h
    simp only [mul_left_cancel_iff, mul_right_cancel_iff] at h
    exact hσinj h
  refine ⟨𝒪, fun Ψ₀ h ↦ ?_, hprod, ?_, ?_⟩
  · obtain ⟨π, rfl⟩ := hrep Ψ₀ h
    exact ⟨hΨmon π, hΨirr π⟩
  · refine hconst _ fun π ↦ ?_
    rw [hT, Finset.card_image_of_injective _ (hTinj π), Finset.card_univ]
  · refine hconst _ fun π ↦ ?_
    rw [hT, Finset.sum_image fun g _ g' _ hg ↦ hTinj π hg, ← sum_card_fixed_mul hm0 σ htrans πσ]
    refine Finset.sum_congr rfl fun g _ ↦ ?_
    simpa only [mul_assoc] using card_fixed_conj (πσ * σ g) π

end Polynomial
