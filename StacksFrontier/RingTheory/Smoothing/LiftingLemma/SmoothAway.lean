module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.RingTheory.Smooth.Locus
public import Mathlib.RingTheory.Smooth.Flat
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Ideal.Annihilator.FlatBaseChange
public import StacksFrontier.RingTheory.Noetherian.Spec
public import StacksFrontier.RingTheory.Smooth.NaiveCotangentCriterion
public import StacksFrontier.RingTheory.Smoothing.BaseChangeOfPresentation
public import StacksFrontier.RingTheory.Smoothing.StandardElementAtSmoothPrime

/-!
# Lifting lemma: smoothness after inverting the element

Auxiliary results for `Stacks.Smoothing.exists_finitePresentation_lift_smoothAt`
(Stacks Project, Tag 07CP): a quotient of a polynomial ring by relations linear in
the new variables becomes a polynomial ring, hence smooth, once the coefficient
`π` is inverted.
-/

@[expose] public section

namespace Stacks.Smoothing

open Stacks.Smooth.NaiveCotangentCriterion

open scoped Pointwise

universe u v w

private noncomputable def quotient_linear_variables_algEquiv
    {A σ τ : Type*} [CommRing A] (u : Aˣ)
    (G : τ → MvPolynomial σ A) :
    (MvPolynomial (σ ⊕ τ) A ⧸
      Ideal.span (Set.range fun j : τ =>
        MvPolynomial.rename Sum.inl (G j) -
          MvPolynomial.C (u : A) * MvPolynomial.X (Sum.inr j))) ≃ₐ[A]
      MvPolynomial σ A := by
  let S := MvPolynomial (σ ⊕ τ) A
  let J : Ideal S := Ideal.span (Set.range fun j : τ =>
    MvPolynomial.rename Sum.inl (G j) -
      MvPolynomial.C (u : A) * MvPolynomial.X (Sum.inr j))
  let e : S →ₐ[A] MvPolynomial σ A := MvPolynomial.aeval fun
    | Sum.inl i => MvPolynomial.X i
    | Sum.inr j => MvPolynomial.C ((u⁻¹ : Aˣ) : A) * G j
  have heRename (p : MvPolynomial σ A) :
      e (MvPolynomial.rename Sum.inl p) = p := by
    change (MvPolynomial.aeval (fun x : σ ⊕ τ =>
      match x with
      | Sum.inl i => MvPolynomial.X i
      | Sum.inr j => MvPolynomial.C ((u⁻¹ : Aˣ) : A) * G j))
        (MvPolynomial.rename Sum.inl p) = p
    rw [MvPolynomial.aeval_rename]
    change MvPolynomial.aeval MvPolynomial.X p = p
    exact MvPolynomial.aeval_X_left_apply p
  have heInl (i : σ) : e (MvPolynomial.X (Sum.inl i)) = MvPolynomial.X i :=
    MvPolynomial.aeval_X _ (Sum.inl i)
  have heInr (j : τ) :
      e (MvPolynomial.X (Sum.inr j)) = MvPolynomial.C ((u⁻¹ : Aˣ) : A) * G j :=
    MvPolynomial.aeval_X _ (Sum.inr j)
  have hker : J ≤ RingHom.ker e.toRingHom := by
    apply Ideal.span_le.mpr
    rintro y ⟨j, rfl⟩
    apply (RingHom.mem_ker).mpr
    change e (MvPolynomial.rename Sum.inl (G j) -
      MvPolynomial.C (u : A) * MvPolynomial.X (Sum.inr j)) = 0
    rw [map_sub, map_mul, heRename]
    have hC : e (MvPolynomial.C (u : A)) = MvPolynomial.C (u : A) := e.commutes _
    rw [hC, heInr, ← mul_assoc, ← map_mul]
    simp
  let f : (S ⧸ J) →ₐ[A] MvPolynomial σ A :=
    Ideal.Quotient.liftₐ J e (fun y hy => (RingHom.mem_ker).mp (hker hy))
  let g : MvPolynomial σ A →ₐ[A] (S ⧸ J) :=
    MvPolynomial.aeval fun i => Ideal.Quotient.mk J (MvPolynomial.X (Sum.inl i))
  have hgRename (p : MvPolynomial σ A) :
      g p = Ideal.Quotient.mk J (MvPolynomial.rename Sum.inl p) := by
    have hh : g = (Ideal.Quotient.mkₐ A J).comp (MvPolynomial.rename Sum.inl) := by
      apply MvPolynomial.algHom_ext
      intro i
      change g (MvPolynomial.X i) =
        Ideal.Quotient.mk J (MvPolynomial.rename Sum.inl (MvPolynomial.X i))
      rw [MvPolynomial.aeval_X, MvPolynomial.rename_X]
    exact congrArg (fun h : MvPolynomial σ A →ₐ[A] S ⧸ J => h p) hh
  apply AlgEquiv.ofAlgHom f g
  · apply MvPolynomial.algHom_ext
    intro i
    change f (g (MvPolynomial.X i)) = MvPolynomial.X i
    rw [show g (MvPolynomial.X i) =
      Ideal.Quotient.mk J (MvPolynomial.X (Sum.inl i)) from MvPolynomial.aeval_X _ i]
    exact heInl i
  · apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro x
    rcases x with i | j
    · change g (f (Ideal.Quotient.mk J (MvPolynomial.X (Sum.inl i)))) =
        Ideal.Quotient.mk J (MvPolynomial.X (Sum.inl i))
      change g (e (MvPolynomial.X (Sum.inl i))) = _
      rw [heInl]
      exact MvPolynomial.aeval_X _ i
    · have hj : MvPolynomial.rename Sum.inl (G j) -
          MvPolynomial.C (u : A) * MvPolynomial.X (Sum.inr j) ∈ J :=
        Ideal.subset_span ⟨j, rfl⟩
      have hh : Ideal.Quotient.mk J (MvPolynomial.rename Sum.inl (G j)) =
          (algebraMap A (S ⧸ J) (u : A)) *
            Ideal.Quotient.mk J (MvPolynomial.X (Sum.inr j)) := by
        have hz := (Ideal.Quotient.eq_zero_iff_mem).mpr hj
        change Ideal.Quotient.mk J (MvPolynomial.rename Sum.inl (G j)) =
          Ideal.Quotient.mk J (MvPolynomial.C (u : A)) *
            Ideal.Quotient.mk J (MvPolynomial.X (Sum.inr j))
        simpa only [map_sub, map_mul, sub_eq_zero] using hz
      change g (e (MvPolynomial.X (Sum.inr j))) =
        Ideal.Quotient.mk J (MvPolynomial.X (Sum.inr j))
      rw [heInr, map_mul, MvPolynomial.C_eq_algebraMap, g.commutes, hgRename, hh,
        ← mul_assoc, ← map_mul]
      simp

private lemma smooth_quotient_linear_variables
    {A σ τ : Type*} [CommRing A] [Finite σ] (u : Aˣ)
    (G : τ → MvPolynomial σ A) :
    Algebra.Smooth A
      (MvPolynomial (σ ⊕ τ) A ⧸
        Ideal.span (Set.range fun j : τ =>
          MvPolynomial.rename Sum.inl (G j) -
            MvPolynomial.C (u : A) * MvPolynomial.X (Sum.inr j))) := by
  let : Algebra.Smooth A (MvPolynomial σ A) :=
    ⟨inferInstance, inferInstance⟩
  exact Algebra.Smooth.of_equiv (quotient_linear_variables_algEquiv u G).symm

private noncomputable def polynomial_away_algEquiv
    {R σ : Type*} [CommRing R] (π : R) :
    Localization.Away (MvPolynomial.C π : MvPolynomial σ R) ≃ₐ[R]
      MvPolynomial σ (Localization.Away π) := by
  letI : Algebra (MvPolynomial σ R) (MvPolynomial σ (Localization.Away π)) :=
    (MvPolynomial.map (algebraMap R (Localization.Away π))).toAlgebra
  letI : IsLocalization (Submonoid.powers (MvPolynomial.C π : MvPolynomial σ R))
      (MvPolynomial σ (Localization.Away π)) := by
    rw [← Submonoid.map_powers]
    exact MvPolynomial.isLocalization (Submonoid.powers π) (Localization.Away π)
  letI : IsScalarTower R (MvPolynomial σ R) (MvPolynomial σ (Localization.Away π)) :=
    IsScalarTower.of_algebraMap_eq' (by
      apply RingHom.ext
      intro x
      change MvPolynomial.C ((algebraMap R (Localization.Away π)) x) =
        MvPolynomial.map (algebraMap R (Localization.Away π)) (MvPolynomial.C x)
      simp)
  exact (IsLocalization.algEquiv (Submonoid.powers (MvPolynomial.C π : MvPolynomial σ R))
    (Localization.Away (MvPolynomial.C π : MvPolynomial σ R))
    (MvPolynomial σ (Localization.Away π))).restrictScalars R

private lemma polynomial_away_algEquiv_map
    {R σ : Type*} [CommRing R] (π : R) (p : MvPolynomial σ R) :
    polynomial_away_algEquiv π
        (algebraMap (MvPolynomial σ R)
          (Localization.Away (MvPolynomial.C π : MvPolynomial σ R)) p) =
      MvPolynomial.map (algebraMap R (Localization.Away π)) p := by
  let : Algebra (MvPolynomial σ R) (MvPolynomial σ (Localization.Away π)) :=
    (MvPolynomial.map (algebraMap R (Localization.Away π))).toAlgebra
  let : IsLocalization (Submonoid.powers (MvPolynomial.C π : MvPolynomial σ R))
      (MvPolynomial σ (Localization.Away π)) := by
    rw [← Submonoid.map_powers]
    exact MvPolynomial.isLocalization (Submonoid.powers π) (Localization.Away π)
  exact (IsLocalization.algEquiv _ _ (MvPolynomial σ (Localization.Away π))).commutes p

private lemma polynomial_away_algEquiv_rename
    {R σ τ : Type*} [CommRing R] (π : R) (G : MvPolynomial σ R) :
    polynomial_away_algEquiv (σ := σ ⊕ τ) π
        (algebraMap (MvPolynomial (σ ⊕ τ) R)
          (Localization.Away (MvPolynomial.C π : MvPolynomial (σ ⊕ τ) R))
          (MvPolynomial.rename Sum.inl G)) =
      MvPolynomial.rename Sum.inl
        (MvPolynomial.map (algebraMap R (Localization.Away π)) G) := by
  rw [polynomial_away_algEquiv_map, MvPolynomial.map_rename]

private noncomputable def quotient_away_algEquiv
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal S) (s : S) :
    Localization.Away (Ideal.Quotient.mk I s) ≃ₐ[R]
      (Localization.Away s ⧸ I.map (algebraMap S (Localization.Away s))) := by
  let f : (S ⧸ I) →+*
      (Localization.Away s ⧸ I.map (algebraMap S (Localization.Away s))) :=
    Ideal.quotientMap _ (algebraMap S (Localization.Away s)) Ideal.le_comap_map
  letI : Algebra (S ⧸ I)
      (Localization.Away s ⧸ I.map (algebraMap S (Localization.Away s))) := f.toAlgebra
  have hloc : IsLocalization (Submonoid.powers (Ideal.Quotient.mk I s))
      (Localization.Away s ⧸ I.map (algebraMap S (Localization.Away s))) := by
    rw [← Submonoid.map_powers]
    exact IsLocalization.of_surjective (Submonoid.powers s) (Localization.Away s)
      (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
      (Ideal.Quotient.mk (I.map (algebraMap S (Localization.Away s))))
      Ideal.Quotient.mk_surjective rfl (by simp)
  letI := hloc
  letI : IsScalarTower R (S ⧸ I)
      (Localization.Away s ⧸ I.map (algebraMap S (Localization.Away s))) :=
    IsScalarTower.of_algebraMap_eq' (by
      apply RingHom.ext
      intro r
      change Ideal.Quotient.mk _ (algebraMap S (Localization.Away s)
        (algebraMap R S r)) =
          f (Ideal.Quotient.mk I (algebraMap R S r))
      rfl)
  exact (IsLocalization.algEquiv (Submonoid.powers (Ideal.Quotient.mk I s))
    (Localization.Away (Ideal.Quotient.mk I s))
    (Localization.Away s ⧸ I.map (algebraMap S (Localization.Away s)))).restrictScalars R

private lemma quotient_away_algEquiv_mk
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal S) (s x : S) :
    quotient_away_algEquiv (R := R) I s
        (algebraMap (S ⧸ I) (Localization.Away (Ideal.Quotient.mk I s))
          (Ideal.Quotient.mk I x)) =
      Ideal.Quotient.mk (I.map (algebraMap S (Localization.Away s)))
        (algebraMap S (Localization.Away s) x) := by
  let f : (S ⧸ I) →+*
      (Localization.Away s ⧸ I.map (algebraMap S (Localization.Away s))) :=
    Ideal.quotientMap _ (algebraMap S (Localization.Away s)) Ideal.le_comap_map
  let : Algebra (S ⧸ I)
      (Localization.Away s ⧸ I.map (algebraMap S (Localization.Away s))) := f.toAlgebra
  have hloc : IsLocalization (Submonoid.powers (Ideal.Quotient.mk I s))
      (Localization.Away s ⧸ I.map (algebraMap S (Localization.Away s))) := by
    rw [← Submonoid.map_powers]
    exact IsLocalization.of_surjective (Submonoid.powers s) (Localization.Away s)
      (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
      (Ideal.Quotient.mk (I.map (algebraMap S (Localization.Away s))))
      Ideal.Quotient.mk_surjective rfl (by simp)
  let := hloc
  exact (IsLocalization.algEquiv (Submonoid.powers (Ideal.Quotient.mk I s)) _ _).commutes _

private lemma polynomial_away_linear_relation_ideal
    {R σ τ : Type*} [CommRing R] (π : R)
    (G : τ → MvPolynomial σ R) :
    let S := MvPolynomial (σ ⊕ τ) R
    let T := Localization.Away π
    let e := polynomial_away_algEquiv (σ := σ ⊕ τ) π
    (Ideal.span (Set.range fun j : τ =>
      MvPolynomial.rename Sum.inl (G j) -
        MvPolynomial.C π * MvPolynomial.X (Sum.inr j))).map
        (algebraMap S (Localization.Away (MvPolynomial.C π : S))) |>.map e.toRingHom =
      Ideal.span (Set.range fun j : τ =>
        MvPolynomial.rename Sum.inl
            (MvPolynomial.map (algebraMap R T) (G j)) -
          MvPolynomial.C (algebraMap R T π) * MvPolynomial.X (Sum.inr j)) := by
  dsimp only
  rw [Ideal.map_span, ← Set.range_comp', Ideal.map_span, ← Set.range_comp']
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext j
  simp only [map_sub, map_mul]
  let S := MvPolynomial (σ ⊕ τ) R
  let L := Localization.Away (MvPolynomial.C π : S)
  change polynomial_away_algEquiv π
      (algebraMap S L (MvPolynomial.rename Sum.inl (G j))) -
      polynomial_away_algEquiv π (algebraMap S L (MvPolynomial.C π)) *
        polynomial_away_algEquiv π (algebraMap S L (MvPolynomial.X (Sum.inr j))) = _
  rw [polynomial_away_algEquiv_rename, polynomial_away_algEquiv_map,
    polynomial_away_algEquiv_map]
  simp

private noncomputable def linear_relation_away_algEquiv
    {R σ τ : Type*} [CommRing R] (π : R)
    (G : τ → MvPolynomial σ R) :
    let S := MvPolynomial (σ ⊕ τ) R
    let I : Ideal S := Ideal.span (Set.range fun j : τ =>
      MvPolynomial.rename Sum.inl (G j) -
        MvPolynomial.C π * MvPolynomial.X (Sum.inr j))
    Localization.Away (Ideal.Quotient.mk I (MvPolynomial.C π)) ≃ₐ[R]
      MvPolynomial σ (Localization.Away π) := by
  let S := MvPolynomial (σ ⊕ τ) R
  let T := Localization.Away π
  let I : Ideal S := Ideal.span (Set.range fun j : τ =>
    MvPolynomial.rename Sum.inl (G j) -
      MvPolynomial.C π * MvPolynomial.X (Sum.inr j))
  let u : Tˣ := (IsLocalization.Away.algebraMap_isUnit π).unit
  let G' : τ → MvPolynomial σ T := fun j =>
    MvPolynomial.map (algebraMap R T) (G j)
  let K : Ideal (MvPolynomial (σ ⊕ τ) T) := Ideal.span (Set.range fun j : τ =>
    MvPolynomial.rename Sum.inl (G' j) -
      MvPolynomial.C (u : T) * MvPolynomial.X (Sum.inr j))
  let e := polynomial_away_algEquiv (σ := σ ⊕ τ) π
  have hK : K = (I.map (algebraMap S (Localization.Away (MvPolynomial.C π : S)))).map
      e.toRingHom := by
    simpa only [K, I, G', u, IsUnit.unit_spec] using
      (polynomial_away_linear_relation_ideal π G).symm
  let e₁ := quotient_away_algEquiv (R := R) I (MvPolynomial.C π)
  let e₂ := Ideal.quotientEquivAlg (R₁ := R)
    (I.map (algebraMap S (Localization.Away (MvPolynomial.C π : S)))) K e hK
  let e₃ := quotient_linear_variables_algEquiv u G'
  exact e₁.trans (e₂.trans (e₃.restrictScalars R))

private lemma smooth_linear_relation_away
    {R σ τ : Type*} [CommRing R] [Finite σ] (π : R)
    (G : τ → MvPolynomial σ R) :
    let S := MvPolynomial (σ ⊕ τ) R
    let I : Ideal S := Ideal.span (Set.range fun j : τ =>
      MvPolynomial.rename Sum.inl (G j) -
        MvPolynomial.C π * MvPolynomial.X (Sum.inr j))
    Algebra.Smooth R
      (Localization.Away (Ideal.Quotient.mk I (MvPolynomial.C π))) := by
  let T := Localization.Away π
  let : Algebra.Smooth R T := Algebra.Smooth.of_isLocalization_Away π
  let : Algebra.Smooth T (MvPolynomial σ T) := ⟨inferInstance, inferInstance⟩
  let : Algebra.Smooth R (MvPolynomial σ T) :=
    Algebra.Smooth.comp R T (MvPolynomial σ T)
  exact Algebra.Smooth.of_equiv (linear_relation_away_algEquiv π G).symm

lemma smooth_away_of_linear_relation_ideal_eq
    {R σ τ : Type*} [CommRing R] [Finite σ] (π : R)
    (G : τ → MvPolynomial σ R)
    (J : Ideal (MvPolynomial (σ ⊕ τ) R))
    (hJ : J.map (algebraMap (MvPolynomial (σ ⊕ τ) R)
        (Localization.Away (MvPolynomial.C π : MvPolynomial (σ ⊕ τ) R))) =
      (Ideal.span (Set.range fun j : τ =>
        MvPolynomial.rename Sum.inl (G j) -
          MvPolynomial.C π * MvPolynomial.X (Sum.inr j))).map
        (algebraMap (MvPolynomial (σ ⊕ τ) R)
          (Localization.Away (MvPolynomial.C π : MvPolynomial (σ ⊕ τ) R)))) :
    Algebra.Smooth R (Localization.Away (Ideal.Quotient.mk J (MvPolynomial.C π))) := by
  let S := MvPolynomial (σ ⊕ τ) R
  let I : Ideal S := Ideal.span (Set.range fun j : τ =>
    MvPolynomial.rename Sum.inl (G j) -
      MvPolynomial.C π * MvPolynomial.X (Sum.inr j))
  let eJ := quotient_away_algEquiv (R := R) J (MvPolynomial.C π)
  let eI := quotient_away_algEquiv (R := R) I (MvPolynomial.C π)
  let eEq : (Localization.Away (MvPolynomial.C π : S) ⧸
      J.map (algebraMap S (Localization.Away (MvPolynomial.C π : S)))) ≃ₐ[R]
      (Localization.Away (MvPolynomial.C π : S) ⧸
        I.map (algebraMap S (Localization.Away (MvPolynomial.C π : S)))) :=
    Ideal.quotientEquivAlgOfEq R hJ
  have hI : Algebra.Smooth R
      (Localization.Away (Ideal.Quotient.mk I (MvPolynomial.C π))) :=
    smooth_linear_relation_away π G
  let := hI
  exact Algebra.Smooth.of_equiv (eJ.trans (eEq.trans eI.symm)).symm

lemma smooth_away_of_algEquiv
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (e : A ≃ₐ[R] B) (a : A)
    (h : Algebra.Smooth R (Localization.Away a)) :
    Algebra.Smooth R (Localization.Away (e a)) := by
  let := h
  have H : Submonoid.map e (Submonoid.powers a) = Submonoid.powers (e a) :=
    Submonoid.map_powers e a
  exact Algebra.Smooth.of_equiv
    (IsLocalization.algEquivOfAlgEquiv (Localization.Away a)
      (Localization.Away (e a)) e H)

end Stacks.Smoothing

end
