module

public import Mathlib.Algebra.MvPolynomial.Cardinal
public import Mathlib.SetTheory.Cardinal.Arithmetic
public import StacksFrontier.RingTheory.Henselian.FiniteEtale
public import StacksFrontier.RingTheory.Henselian.UnramifiedAlgHomExt
public import StacksFrontier.RingTheory.Henselian.Henselization.Defs

/-!
# The cardinality of a henselization

Let `(R, 𝔪)` be a local ring and `Rh` a henselization of `R` with residue field `L`
(`IsLocalRing.IsHenselization R L Rh`), in the same universe as `R`. Then

`#Rh ≤ max (max #R #κ(Rh)) ℵ₀`.

## Main results

* `IsLocalRing.IsHenselization.cardinalMk_le_max` — the bound above.
-/

@[expose] public section

open Cardinal IsLocalRing CategoryTheory

universe u v

namespace IsLocalRing.IsHenselization

variable {R : Type u} [CommRing R] [IsLocalRing R] {L : Type v} [Field L]
  [Algebra (ResidueField R) L] {Rh : Type u} [CommRing Rh] [IsLocalRing Rh] [Algebra R Rh]

/-- The data which determine an element of a henselization: a number `n` of variables, a finite
set of relations among them, the residues of the values of the variables, and a polynomial. -/
private abbrev Code (R : Type u) [CommRing R] (K : Type u) :=
  Σ n : ULift.{u} ℕ, Finset (MvPolynomial (Fin n.down) R) × (Fin n.down → K) ×
    MvPolynomial (Fin n.down) R

/-- An element `r` of `Rh` is *presented* by a code `(n, G, w, Q)` if the quotient of the
polynomial ring in `n` variables by `G` is étale and some values `v` of the variables, with
residues `w`, annihilate `G` and evaluate `Q` to `r`. -/
private def Presents (R : Type u) [CommRing R] (Rh : Type u) [CommRing Rh] [IsLocalRing Rh]
    [Algebra R Rh] (r : Rh) (c : Code R (ResidueField Rh)) : Prop :=
  Algebra.Etale R (MvPolynomial (Fin c.1.down) R ⧸
      Ideal.span (↑c.2.1 : Set (MvPolynomial (Fin c.1.down) R))) ∧
    ∃ v : Fin c.1.down → Rh, (∀ i, residue Rh (v i) = c.2.2.1 i) ∧
      (∀ g ∈ c.2.1, MvPolynomial.aeval v g = 0) ∧ MvPolynomial.aeval v c.2.2.2 = r

/-- Every element of a henselization is presented by some code. -/
private theorem exists_presents [IsHenselization R L Rh] (r : Rh) : ∃ c, Presents R Rh r c := by
  obtain ⟨J, _, _, pres, hP⟩ := ind_etale_of_universe_le (R := R) (L := L) (Rh := Rh)
  obtain ⟨j, y, hy⟩ := CommAlgCat.exists_app_eq pres.isColimit r
  have hC : Algebra.Etale R (pres.diag.obj j) := hP j
  obtain ⟨n, π, hπ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType R (pres.diag.obj j))
  obtain ⟨G, hG⟩ := Algebra.FinitePresentation.ker_fG_of_surjective π hπ
  let ψ : pres.diag.obj j →ₐ[R] Rh := (pres.ι.app j).hom
  obtain ⟨Q, hQ⟩ := hπ y
  refine ⟨⟨⟨n⟩, G, fun i => residue Rh (ψ (π (MvPolynomial.X i))), Q⟩, ?_, ?_⟩
  · exact .of_equiv
      ((Ideal.quotientEquivAlgOfEq R hG).trans (Ideal.quotientKerAlgEquivOfSurjective hπ)).symm
  · have haeval : (MvPolynomial.aeval fun i => ψ (π (MvPolynomial.X i)) :
        MvPolynomial (Fin n) R →ₐ[R] Rh) = ψ.comp π :=
      MvPolynomial.algHom_ext fun i => by simp
    refine ⟨fun i => ψ (π (MvPolynomial.X i)), fun i => rfl, fun g hg => ?_, ?_⟩
    · have hgk : g ∈ RingHom.ker π.toRingHom := hG ▸ Ideal.subset_span hg
      rw [haeval, AlgHom.comp_apply, show π g = 0 from hgk, map_zero]
    · rwa [haeval, AlgHom.comp_apply, hQ]

/-- A code presents at most one element of a henselization. -/
private theorem eq_of_presents {r r' : Rh} {c : Code R (ResidueField Rh)}
    (h : Presents R Rh r c) (h' : Presents R Rh r' c) : r = r' := by
  obtain ⟨hét, v, hv, hvG, hvQ⟩ := h
  obtain ⟨-, v', hv', hv'G, hv'Q⟩ := h'
  set I := Ideal.span (↑c.2.1 : Set (MvPolynomial (Fin c.1.down) R))
  let Φ (w : Fin c.1.down → Rh) (hw : ∀ g ∈ c.2.1, MvPolynomial.aeval w g = 0) :
      (MvPolynomial (Fin c.1.down) R ⧸ I) →ₐ[R] Rh :=
    Ideal.Quotient.liftₐ I (MvPolynomial.aeval w) fun a ha =>
      Ideal.span_le (I := RingHom.ker (MvPolynomial.aeval w : _ →ₐ[R] Rh)).mpr hw ha
  have hres : (Ideal.Quotient.mkₐ R (maximalIdeal Rh)).comp (Φ v hvG) =
      (Ideal.Quotient.mkₐ R (maximalIdeal Rh)).comp (Φ v' hv'G) := by
    refine Ideal.Quotient.algHom_ext R (MvPolynomial.algHom_ext fun i => ?_)
    show residue Rh (MvPolynomial.aeval v (MvPolynomial.X i)) =
      residue Rh (MvPolynomial.aeval v' (MvPolynomial.X i))
    rw [MvPolynomial.aeval_X, MvPolynomial.aeval_X]
    exact (hv i).trans (hv' i).symm
  have hΦ : Φ v hvG = Φ v' hv'G :=
    Stacks.Henselian.FiniteEtaleEquivalence.algHom_ext_of_le_jacobson R
      (I := maximalIdeal Rh) (maximalIdeal_le_jacobson _) fun s =>
        AlgHom.congr_fun hres s
  rw [← hvQ, ← hv'Q]
  exact AlgHom.congr_fun hΦ (Ideal.Quotient.mk I c.2.2.2)

/-- The number of codes is at most `max (max #R #K) ℵ₀`. -/
private theorem cardinalMk_code_le (K : Type u) :
    #(Code R K) ≤ max (max #R #K) ℵ₀ := by
  classical
  set κ := max (max #R #K) ℵ₀
  have hκ : ℵ₀ ≤ κ := le_max_right _ _
  have hlist (α : Type u) (h : #α ≤ κ) : #(List α) ≤ κ := (mk_list_le_max α).trans (max_le hκ h)
  have hpoly : ∀ n : ℕ, #(MvPolynomial (Fin n) R) ≤ κ := fun n => by
    refine (MvPolynomial.cardinalMk_le_max_lift).trans (max_le (max_le ?_ ?_) hκ)
    · rw [lift_uzero]
      exact (le_max_left _ _).trans (le_max_left _ _)
    · exact (lift_le_aleph0.mpr (lt_aleph0_of_finite (Fin n)).le).trans hκ
  have hfin : ∀ n : ℕ, #(Finset (MvPolynomial (Fin n) R)) ≤ κ := fun n =>
    (mk_le_of_surjective (f := fun l : List (MvPolynomial (Fin n) R) => l.toFinset)
      fun s => ⟨s.toList, s.toList_toFinset⟩).trans
      (hlist _ (hpoly n))
  have hfun : ∀ n : ℕ, #(Fin n → K) ≤ κ := fun n =>
    (mk_le_of_injective (f := fun w : Fin n → K => List.ofFn w) List.ofFn_injective).trans
      (hlist _ ((le_max_right _ _).trans (le_max_left _ _)))
  have hfib : ∀ n : ULift.{u} ℕ, #(Finset (MvPolynomial (Fin n.down) R) × (Fin n.down → K) ×
      MvPolynomial (Fin n.down) R) ≤ κ := fun n => by
    rw [mk_prod, mk_prod, lift_id, lift_id, lift_id, lift_id]
    calc _ ≤ κ * (κ * κ) := mul_le_mul' (hfin _) (mul_le_mul' (hfun _) (hpoly _))
      _ = κ := by rw [mul_eq_self hκ, mul_eq_self hκ]
  rw [Code, mk_sigma]
  calc _ ≤ #(ULift.{u} ℕ) * ⨆ n, #(Finset (MvPolynomial (Fin n.down) R) ×
        (Fin n.down → K) × MvPolynomial (Fin n.down) R) := sum_le_mk_mul_iSup _
    _ ≤ κ * κ := mul_le_mul' (by simpa using hκ) (ciSup_le' hfib)
    _ = κ := mul_eq_self hκ

/-- A henselization `Rh` of a local ring `R`, in the same universe, has cardinality at most
`max (max #R #κ(Rh)) ℵ₀`. -/
theorem cardinalMk_le_max [IsHenselization R L Rh] :
    #Rh ≤ max (max #R #(ResidueField Rh)) ℵ₀ := by
  classical
  choose c hc using fun r : Rh => exists_presents (R := R) (L := L) (Rh := Rh) r
  refine (mk_le_of_injective (f := c) fun r r' h => ?_).trans (cardinalMk_code_le _)
  exact eq_of_presents (hc r) (h ▸ hc r')

end IsLocalRing.IsHenselization
