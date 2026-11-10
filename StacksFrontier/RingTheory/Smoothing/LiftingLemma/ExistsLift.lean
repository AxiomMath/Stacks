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
public import StacksFrontier.RingTheory.Smoothing.LiftingLemma.SmoothAtCriteria
public import StacksFrontier.RingTheory.Smoothing.LiftingLemma.SmoothAway
public import StacksFrontier.RingTheory.Smoothing.LiftingLemma.Charts

/-!
# Lifting lemma: the lift modulo the square of an element

The lifting lemma `Stacks.Smoothing.exists_finitePresentation_lift_smoothAt`
(Stacks Project, Tag 07CP).
-/

@[expose] public section

namespace Stacks.Smoothing

open Stacks.Smooth.NaiveCotangentCriterion

open scoped Pointwise

universe u v w

/-- **Stacks Project, Tag 07CP.** A finitely presented algebra modulo `π²`
admits a lift modulo `π` with the asserted smoothness properties. -/
@[stacks 07CP]
public theorem exists_finitePresentation_lift_smoothAt
    (R : Type u) (Λ : Type v) (C : Type w)
    [CommRing R] [CommRing Λ] [CommRing C] [IsNoetherianRing R]
    [Algebra R Λ] (π : R)
    (hR : ∀ r : R, r * π = 0 ↔ r * π ^ 2 = 0)
    (hΛ : ∀ x : Λ,
      x * algebraMap R Λ π = 0 ↔ x * (algebraMap R Λ π) ^ 2 = 0)
    [Algebra (R ⧸ Ideal.span {π ^ 2}) C]
    [Algebra.FinitePresentation (R ⧸ Ideal.span {π ^ 2}) C]
    [Algebra (R ⧸ Ideal.span {π ^ 2})
      (Λ ⧸ Ideal.span {(algebraMap R Λ π) ^ 2})]
    (hquot : ∀ x : R, algebraMap (R ⧸ Ideal.span {π ^ 2})
      (Λ ⧸ Ideal.span {(algebraMap R Λ π) ^ 2})
        (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (algebraMap R Λ x))
    (f : C →ₐ[R ⧸ Ideal.span {π ^ 2}]
      Λ ⧸ Ideal.span {(algebraMap R Λ π) ^ 2}) :
    ∃ (D : Type (max u v w)) (_ : CommRing D) (_ : Algebra R D)
      (_ : Algebra.FinitePresentation R D) (g : D →ₐ[R] Λ)
      (c : C →+* D ⧸ Ideal.span {algebraMap R D π})
      (reduceΛ : (Λ ⧸ Ideal.span {(algebraMap R Λ π) ^ 2}) →+*
        Λ ⧸ Ideal.span {algebraMap R Λ π})
      (reduceD : (D ⧸ Ideal.span {algebraMap R D π}) →+*
        Λ ⧸ Ideal.span {algebraMap R Λ π})
      (_ : Algebra (C ⧸ Ideal.span {
        algebraMap (R ⧸ Ideal.span {π ^ 2}) C
          (Ideal.Quotient.mk (Ideal.span {π ^ 2}) π)})
        (D ⧸ Ideal.span {algebraMap R D π})),
      (∀ x : Λ, reduceΛ (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ x) ∧
      (∀ x : D, reduceD (Ideal.Quotient.mk _ x) =
        Ideal.Quotient.mk _ (g x)) ∧
      (∀ x : C, reduceD (c x) = reduceΛ (f x)) ∧
      (∀ x : R, c (algebraMap (R ⧸ Ideal.span {π ^ 2}) C
          (Ideal.Quotient.mk _ x)) = Ideal.Quotient.mk _ (algebraMap R D x)) ∧
      (∀ x : C, algebraMap
          (C ⧸ Ideal.span {
            algebraMap (R ⧸ Ideal.span {π ^ 2}) C
              (Ideal.Quotient.mk (Ideal.span {π ^ 2}) π)})
          (D ⧸ Ideal.span {algebraMap R D π}) (Ideal.Quotient.mk _ x) = c x) ∧
      (∀ (q : Ideal D) [q.IsPrime], algebraMap R D π ∉ q →
        Algebra.IsSmoothAt R q) ∧
      (∀ (q : Ideal D) [q.IsPrime], algebraMap R D π ∈ q →
        (∃ (p : Ideal C) (_ : p.IsPrime),
          Algebra.IsSmoothAt (R ⧸ Ideal.span {π ^ 2}) p ∧
          p = Ideal.comap c (Ideal.map
            (Ideal.Quotient.mk (Ideal.span {algebraMap R D π})) q)) →
        Algebra.IsSmoothAt R q) ∧
      ∀ (q : Ideal (D ⧸ Ideal.span {algebraMap R D π})) [q.IsPrime],
        (∃ (p : Ideal C) (_ : p.IsPrime),
          Algebra.IsSmoothAt (R ⧸ Ideal.span {π ^ 2}) p ∧
          p = Ideal.comap c q) →
        Algebra.IsSmoothAt
          (C ⧸ Ideal.span {
            algebraMap (R ⧸ Ideal.span {π ^ 2}) C
              (Ideal.Quotient.mk (Ideal.span {π ^ 2}) π)}) q := by
  classical
  obtain ⟨n, φ, hφ, hker⟩ :=
    Algebra.FinitePresentation.out (R := R ⧸ Ideal.span {π ^ 2}) (A := C)
  obtain ⟨m, F, hF⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hker
  have hmapLift (p : MvPolynomial (Fin n) (R ⧸ Ideal.span {π ^ 2})) :
      ∃ q : MvPolynomial (Fin n) R,
        MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {π ^ 2})) q = p :=
    MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective p
  have hlift : ∀ i : Fin n, ∃ x : Λ,
      Ideal.Quotient.mk (Ideal.span {(algebraMap R Λ π) ^ 2}) x =
        f (φ (MvPolynomial.X i)) := by
    intro i
    exact Ideal.Quotient.mk_surjective _
  have hF' : Ideal.span (Set.range F) = RingHom.ker φ := hF
  let P : Presentation (R ⧸ Ideal.span {π ^ 2}) C :=
    { n := n
      m := m
      f := F
      iso := ((Ideal.quotientEquivAlgOfEq (R ⧸ Ideal.span {π ^ 2}) hF').trans
        (Ideal.quotientKerAlgEquivOfSurjective hφ)).symm }
  have hP_lift (p : MvPolynomial (Fin n) (R ⧸ Ideal.span {π ^ 2})) :
      P.lift p = φ p := by
    change (Ideal.quotientKerAlgEquivOfSurjective hφ)
      ((Ideal.quotientEquivAlgOfEq (R ⧸ Ideal.span {π ^ 2}) hF')
        (Ideal.Quotient.mk (Ideal.span (Set.range F)) p)) = φ p
    rw [Ideal.quotientEquivAlgOfEq_mk, Ideal.quotientKerAlgEquivOfSurjective_mk]
  have hNoeth : TopologicalSpace.NoetherianSpace (PrimeSpectrum C) := by
    let : IsNoetherianRing C :=
      Algebra.FiniteType.isNoetherianRing (R ⧸ Ideal.span {π ^ 2}) C
    infer_instance
  have hCompact : IsCompact (Algebra.smoothLocus (R ⧸ Ideal.span {π ^ 2}) C) :=
    @TopologicalSpace.NoetherianSpace.isCompact _ _ hNoeth _
  let pointData := fun (q : Ideal C) [q.IsPrime]
      (hq : Algebra.IsSmoothAt (R ⧸ Ideal.span {π ^ 2}) q) =>
    Stacks.Smoothing.exists_strictly_standard_element P q
      (smoothAt_of_isSmoothAt q hq)
  let idx := {x : PrimeSpectrum C //
    x ∈ Algebra.smoothLocus (R ⧸ Ideal.span {π ^ 2}) C}
  let a : idx → C := fun x => (pointData x.1.asIdeal x.2).choose
  have ha (x : idx) : a x ∉ x.1.asIdeal :=
    (pointData x.1.asIdeal x.2).choose_spec.1
  let U : idx → Set (PrimeSpectrum C) := fun x => ↑(PrimeSpectrum.basicOpen (a x))
  have hCover : Algebra.smoothLocus (R ⧸ Ideal.span {π ^ 2}) C ⊆
      ⋃ x, U x := by
    intro x hx
    rw [Set.mem_iUnion]
    refine ⟨⟨x, hx⟩, ?_⟩
    exact (PrimeSpectrum.mem_basicOpen _ _).2 (ha ⟨x, hx⟩)
  obtain ⟨t, ht⟩ := hCompact.elim_finite_subcover U
    (fun i => PrimeSpectrum.isOpen_basicOpen) hCover
  let r := t.card
  let k : Fin r → idx := fun i => ((Finset.equivFin t).symm i).1
  let ak : Fin r → C := fun i => a (k i)
  have hCoverFinite (x : PrimeSpectrum C)
      (hx : x ∈ Algebra.smoothLocus (R ⧸ Ideal.span {π ^ 2}) C) :
      ∃ i ∈ t, a i ∉ x.asIdeal := by
    have hx' := ht hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx'
    obtain ⟨hit, hmem⟩ := Set.mem_iUnion.mp hi
    exact ⟨i, hit, (PrimeSpectrum.mem_basicOpen _ _).mp hmem⟩
  have hCoverFin (x : PrimeSpectrum C)
      (hx : x ∈ Algebra.smoothLocus (R ⧸ Ideal.span {π ^ 2}) C) :
      ∃ i : Fin r, ak i ∉ x.asIdeal := by
    obtain ⟨i, hi, hai⟩ := hCoverFinite x hx
    let j : Fin r := Finset.equivFin t ⟨i, hi⟩
    refine ⟨j, ?_⟩
    have hj : k j = i := by simp [k, j]
    simpa [ak, hj] using hai
  have hStd (x : idx) := (pointData x.1.asIdeal x.2).choose_spec.2
  choose cRows UCols VRows hcn hcm hU hV aMinor hMinor hRel using hStd
  have haLift (x : idx) : ∃ p : MvPolynomial (Fin n) (R ⧸ Ideal.span {π ^ 2}),
      φ p = a x := hφ (a x)
  choose aBar haBar using haLift
  have hCongr (x : idx) (ℓ : Fin m) :
      aBar x * F ℓ ∈
        Presentation.selectedRelIdeal P (VRows x) + P.relIdeal ^ 2 := by
    apply hRel x ℓ (aBar x)
    change P.lift (aBar x) = a x
    rw [hP_lift, haBar]
  have hSelected (x : idx) (ℓ : Fin m) :
      ∃ (h : (VRows x) →
          MvPolynomial (Fin n) (R ⧸ Ideal.span {π ^ 2}))
        (t : MvPolynomial (Fin n) (R ⧸ Ideal.span {π ^ 2})),
        t ∈ P.relIdeal ^ 2 ∧
        aBar x * F ℓ = (∑ j, h j * F j.1) + t := by
    rcases Submodule.mem_sup.mp (hCongr x ℓ) with ⟨s, hs, t, ht, heq⟩
    change s ∈ Ideal.span (Set.range fun j : (VRows x) => F j.1) at hs
    obtain ⟨h, hh⟩ := Ideal.mem_span_range_iff_exists_fun.mp hs
    refine ⟨h, t, ht, ?_⟩
    rw [← heq, hh]
  choose H T hT hEq using hSelected
  choose HC hHC using fun (x : idx) (ℓ : Fin m) (j : VRows x) => hmapLift (H x ℓ j)
  have hQuadratic (x : idx) (ℓ : Fin m) :
      ∃ Q : Fin m × Fin m → MvPolynomial (Fin n) (R ⧸ Ideal.span {π ^ 2}),
        T x ℓ = ∑ ij, Q ij * (F ij.1 * F ij.2) := by
    have hRange : (Set.range F) * (Set.range F) =
        Set.range (fun ij : Fin m × Fin m => F ij.1 * F ij.2) := by
      ext z
      constructor
      · rintro ⟨a, ⟨i, rfl⟩, b, ⟨j, rfl⟩, rfl⟩
        exact ⟨(i, j), rfl⟩
      · rintro ⟨⟨i, j⟩, rfl⟩
        exact ⟨F i, ⟨i, rfl⟩, F j, ⟨j, rfl⟩, rfl⟩
    have ht' : T x ℓ ∈ Ideal.span
        (Set.range (fun ij : Fin m × Fin m => F ij.1 * F ij.2)) := by
      have htx := hT x ℓ
      change T x ℓ ∈ (Ideal.span (Set.range F)) ^ 2 at htx
      simpa only [pow_two, Ideal.span_mul_span, hRange] using htx
    obtain ⟨Q, hQ⟩ := Ideal.mem_span_range_iff_exists_fun.mp ht'
    exact ⟨Q, hQ.symm⟩
  choose Q hQ using hQuadratic
  choose QC hQC using fun (x : idx) (ℓ : Fin m) (ij : Fin m × Fin m) => hmapLift (Q x ℓ ij)
  choose aPoly haPoly using fun x : idx => hmapLift (aBar x)
  choose G hG using fun j : Fin m => hmapLift (F j)
  have hExactRelation (x : idx) (ℓ : Fin m) :
      ∃ E : MvPolynomial (Fin n) R,
        aPoly x * G ℓ - (∑ j : VRows x, HC x ℓ j * G j.1) -
          (∑ ij : Fin m × Fin m, QC x ℓ ij * (G ij.1 * G ij.2)) =
          MvPolynomial.C (π ^ 2) * E := by
    let e : MvPolynomial (Fin n) R :=
      aPoly x * G ℓ - (∑ j : VRows x, HC x ℓ j * G j.1) -
        (∑ ij : Fin m × Fin m, QC x ℓ ij * (G ij.1 * G ij.2))
    have he : MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {π ^ 2})) e = 0 := by
      simp only [e, map_sub, map_mul, map_sum, haPoly, hG, hHC, hQC]
      rw [hEq x ℓ, hQ x ℓ]
      ring
    exact mvPolynomial_divisible_of_map_quotient_zero (π ^ 2) e he
  choose E hE using hExactRelation
  have hQuadraticInSquare (x : idx) (ℓ : Fin m) :
      (∑ ab : Fin m × Fin m,
        QC x ℓ ab * (G ab.1 * G ab.2)) ∈
        (Ideal.span (Set.range G)) ^ 2 := by
    apply Ideal.sum_mem
    intro ab _
    rw [pow_two]
    apply Ideal.mul_mem_left
    exact Ideal.mul_mem_mul
      (Ideal.subset_span ⟨ab.1, rfl⟩)
      (Ideal.subset_span ⟨ab.2, rfl⟩)
  have hDerivative (x : idx) (ℓ : Fin m) (i : Fin n) :
      aPoly x * MvPolynomial.pderiv i (G ℓ) -
        (∑ j : VRows x,
          HC x ℓ j * MvPolynomial.pderiv i (G j.1)) ∈
          Ideal.span (Set.range G) ⊔
            Ideal.span {MvPolynomial.C π} :=
    pderiv_relation_mod_pi π G (VRows x) (aPoly x)
      (HC x ℓ) ℓ _ (E x ℓ) (hQuadraticInSquare x ℓ) (hE x ℓ) i
  let jacLift (x : idx) : MvPolynomial (Fin n) R :=
    Matrix.det fun (j i : Fin (cRows x)) =>
      MvPolynomial.pderiv
        ((UCols x).orderIsoOfFin (hU x) i).1
        (G ((VRows x).orderIsoOfFin (hV x) j).1)
  have hJacLift (x : idx) :
      MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {π ^ 2})) (jacLift x) =
        Presentation.jacobianMinorOn P (cRows x)
          (UCols x) (VRows x) (hU x) (hV x) := by
    let M : Matrix (Fin (cRows x)) (Fin (cRows x))
        (MvPolynomial (Fin n) R) := fun j i =>
      MvPolynomial.pderiv
        ((UCols x).orderIsoOfFin (hU x) i).1
        (G ((VRows x).orderIsoOfFin (hV x) j).1)
    change (MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {π ^ 2}))) M.det =
      Matrix.det (fun j i =>
        MvPolynomial.pderiv
          ((UCols x).orderIsoOfFin (hU x) i).1
          (F ((VRows x).orderIsoOfFin (hV x) j).1))
    rw [RingHom.map_det (MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {π ^ 2}))) M]
    congr 1
    apply Matrix.ext
    intro j i
    change MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {π ^ 2}))
      (MvPolynomial.pderiv ((UCols x).orderIsoOfFin (hU x) i).1
        (G ((VRows x).orderIsoOfFin (hV x) j).1)) = _
    rw [← MvPolynomial.pderiv_map, hG]
  choose lam hLam using hlift
  have hEval :
      (Ideal.Quotient.mk (Ideal.span {(algebraMap R Λ π) ^ 2})).comp
          (MvPolynomial.aeval lam).toRingHom =
        (f.toRingHom.comp φ.toRingHom).comp
          (MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {π ^ 2}))) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [hquot]
    · intro i
      simpa using hLam i
  have hFzero (j : Fin m) : φ (F j) = 0 := by
    have hj : F j ∈ RingHom.ker φ.toRingHom := by
      rw [← hF]
      exact Ideal.subset_span ⟨j, rfl⟩
    exact (RingHom.mem_ker).mp hj
  have hGzero (j : Fin m) :
      Ideal.Quotient.mk (Ideal.span {(algebraMap R Λ π) ^ 2})
        ((MvPolynomial.aeval lam) (G j)) = 0 := by
    have hj := RingHom.congr_fun hEval (G j)
    simpa [hG j, hFzero j] using hj
  have hmu (j : Fin m) : ∃ μ : Λ,
      (MvPolynomial.aeval lam) (G j) = (algebraMap R Λ π) ^ 2 * μ := by
    have hj : (MvPolynomial.aeval lam) (G j) ∈
        Ideal.span {(algebraMap R Λ π) ^ 2} :=
      (Ideal.Quotient.eq_zero_iff_mem).mp (hGzero j)
    obtain ⟨μ, hμ⟩ := Ideal.mem_span_singleton.mp hj
    exact ⟨μ, by simpa [mul_comm] using hμ⟩
  choose μ hμ using hmu
  have hExactRelationEval (x : idx) (ℓ : Fin m) :
      (MvPolynomial.aeval lam) (aPoly x) * (MvPolynomial.aeval lam) (G ℓ) -
        (∑ j : VRows x,
          (MvPolynomial.aeval lam) (HC x ℓ j) *
            (MvPolynomial.aeval lam) (G j.1)) -
        (∑ ij : Fin m × Fin m,
          (MvPolynomial.aeval lam) (QC x ℓ ij) *
            ((MvPolynomial.aeval lam) (G ij.1) *
              (MvPolynomial.aeval lam) (G ij.2))) =
          (algebraMap R Λ π) ^ 2 * (MvPolynomial.aeval lam) (E x ℓ) := by
    have hh := congrArg (MvPolynomial.aeval lam) (hE x ℓ)
    simpa only [map_sub, map_mul, map_sum, MvPolynomial.aeval_C, map_pow] using hh
  let reduceΛ :
      (Λ ⧸ Ideal.span {(algebraMap R Λ π) ^ 2}) →+*
        Λ ⧸ Ideal.span {algebraMap R Λ π} :=
    Ideal.Quotient.factor (by
      apply Ideal.span_le.mpr
      intro x hx
      have hx : x = (algebraMap R Λ π) ^ 2 := by simpa using hx
      subst x
      exact Ideal.mem_span_singleton.mpr
        ⟨algebraMap R Λ π, by ring⟩)
  have hreduceΛ (x : Λ) :
      reduceΛ (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ x :=
    Ideal.Quotient.factor_mk _ _
  let S := MvPolynomial (Fin n ⊕ Fin m) R
  let liftX : MvPolynomial (Fin n) R →ₐ[R] S := MvPolynomial.rename Sum.inl
  let z : Fin m → S := fun j => MvPolynomial.X (Sum.inr j)
  let relation : Fin m → S := fun j =>
    liftX (G j) - MvPolynomial.C π * z j
  have hExactInS (x : idx) (ℓ : Fin m) :
      liftX (aPoly x) * liftX (G ℓ) -
        (∑ j : VRows x, liftX (HC x ℓ j) * liftX (G j.1)) -
        (∑ ab : Fin m × Fin m,
          liftX (QC x ℓ ab) * (liftX (G ab.1) * liftX (G ab.2))) =
          (MvPolynomial.C π : S) ^ 2 * liftX (E x ℓ) := by
    have hh := congrArg liftX (hE x ℓ)
    have hC : liftX (MvPolynomial.C π) = (MvPolynomial.C π : S) :=
      liftX.commutes π
    simpa only [map_sub, map_mul, map_sum, map_pow, hC] using hh
  let chartRelation : Fin r × Fin m → S := fun ij =>
    if ij.2 ∈ VRows (k ij.1) then 0 else
      liftX (aPoly (k ij.1)) * z ij.2 -
        (∑ j : VRows (k ij.1), liftX (HC (k ij.1) ij.2 j) * z j.1) -
        MvPolynomial.C π * (liftX (E (k ij.1) ij.2) +
          ∑ ab : Fin m × Fin m,
            liftX (QC (k ij.1) ij.2 ab) * (z ab.1 * z ab.2))
  have hPiChart (ij : Fin r × Fin m) (hij : ij.2 ∉ VRows (k ij.1)) :
      (MvPolynomial.C π : S) * chartRelation ij =
        -liftX (aPoly (k ij.1)) * relation ij.2 +
          (∑ j : VRows (k ij.1),
            liftX (HC (k ij.1) ij.2 j) * relation j.1) +
          (∑ ab : Fin m × Fin m,
            liftX (QC (k ij.1) ij.2 ab) *
              (relation ab.1 * liftX (G ab.2) +
                MvPolynomial.C π * z ab.1 * relation ab.2)) := by
    simpa only [relation, chartRelation, ite_eq_right hij] using
      (chart_relation_identity
        (p := (MvPolynomial.C π : S))
        (a := liftX (aPoly (k ij.1)))
        (e := liftX (E (k ij.1) ij.2))
        (G := fun j : Fin m => liftX (G j))
        (z := z)
        (H := fun j : VRows (k ij.1) => liftX (HC (k ij.1) ij.2 j))
        (Q := fun ab : Fin m × Fin m => liftX (QC (k ij.1) ij.2 ab))
        (row := fun j : VRows (k ij.1) => j.1)
        (fst := Prod.fst) (snd := Prod.snd) (l := ij.2)
        (hExactInS (k ij.1) ij.2))
  let Jrel : Ideal S := Ideal.span (Set.range relation)
  have hRelMem (j : Fin m) : relation j ∈ Jrel :=
    Ideal.subset_span ⟨j, rfl⟩
  have hPiChartMem (ij : Fin r × Fin m) :
      (MvPolynomial.C π : S) * chartRelation ij ∈ Jrel := by
    by_cases hij : ij.2 ∈ VRows (k ij.1)
    · simp only [chartRelation, ite_eq_left hij, mul_zero]
      exact Jrel.zero_mem
    rw [hPiChart ij hij]
    apply Ideal.add_mem
    · apply Ideal.add_mem
      · have heq : -liftX (aPoly (k ij.1)) * relation ij.2 =
            -(liftX (aPoly (k ij.1)) * relation ij.2) := by ring
        rw [heq]
        exact Jrel.neg_mem
          (Jrel.mul_mem_left (liftX (aPoly (k ij.1))) (hRelMem ij.2))
      · apply Jrel.sum_mem
        intro j _
        exact Jrel.mul_mem_left _ (hRelMem j.1)
    · apply Jrel.sum_mem
      intro ab _
      apply Jrel.mul_mem_left
      apply Ideal.add_mem
      · exact Jrel.mul_mem_right _ (hRelMem ab.1)
      · exact Jrel.mul_mem_left _ (hRelMem ab.2)
  let J : Ideal S := Ideal.span (Set.range relation ∪ Set.range chartRelation)
  have hJrelJ : Jrel ≤ J := by
    apply Ideal.span_le.mpr
    intro y hy
    exact Ideal.subset_span (Or.inl hy)
  have hJcolon : J ≤ Jrel.colon {(MvPolynomial.C π : S)} := by
    apply Ideal.span_le.mpr
    intro y hy
    apply (Submodule.mem_colon_singleton).2
    simp only [smul_eq_mul]
    rcases hy with ⟨j, rfl⟩ | ⟨ij, rfl⟩
    · exact Jrel.mul_mem_right _ (hRelMem j)
    · rw [mul_comm (chartRelation ij) (MvPolynomial.C π)]
      exact hPiChartMem ij
  have hAwayIdeals :
      Jrel.map (algebraMap S (Localization.Away (MvPolynomial.C π : S))) =
        J.map (algebraMap S (Localization.Away (MvPolynomial.C π : S))) := by
    apply map_ideal_eq_of_le_colon_of_isUnit
      (algebraMap S (Localization.Away (MvPolynomial.C π : S)))
      Jrel J (MvPolynomial.C π : S) hJrelJ hJcolon
    exact IsLocalization.Away.algebraMap_isUnit _
  have hJfg : J.FG :=
    Submodule.fg_span ((Set.finite_range relation).union
      (Set.finite_range chartRelation))
  let D₀ := S ⧸ J
  have hD₀fp : Algebra.FinitePresentation R D₀ :=
    Algebra.FinitePresentation.quotient hJfg
  let values : Fin n ⊕ Fin m → Λ := fun
    | Sum.inl i => lam i
    | Sum.inr j => algebraMap R Λ π * μ j
  let evS : S →ₐ[R] Λ := MvPolynomial.aeval values
  have hEvLiftX (p : MvPolynomial (Fin n) R) :
      evS (liftX p) = (MvPolynomial.aeval lam) p := by
    have h : evS.comp liftX = MvPolynomial.aeval lam := by
      ext i
      change (MvPolynomial.aeval values)
        ((MvPolynomial.rename (R := R) (fun j : Fin n => (Sum.inl j : Fin n ⊕ Fin m)))
          (MvPolynomial.X i)) = (MvPolynomial.aeval lam) (MvPolynomial.X i)
      simp only [MvPolynomial.rename_X, MvPolynomial.aeval_X, values]
    exact congrArg (fun f : MvPolynomial (Fin n) R →ₐ[R] Λ => f p) h
  have hEvZ (j : Fin m) : evS (z j) = algebraMap R Λ π * μ j := by
    change (MvPolynomial.aeval values) (MvPolynomial.X (Sum.inr j)) = _
    rw [MvPolynomial.aeval_X]
  have hRelationZero (j : Fin m) : evS (relation j) = 0 := by
    simp only [relation, map_sub, map_mul]
    rw [hEvLiftX, hEvZ, show evS (MvPolynomial.C π) = algebraMap R Λ π from
      evS.commutes π, hμ]
    ring
  have hChartBracketZero (x : idx) (ℓ : Fin m) :
      (algebraMap R Λ π) *
        ((MvPolynomial.aeval lam) (aPoly x) * μ ℓ -
          (∑ j : VRows x, (MvPolynomial.aeval lam) (HC x ℓ j) * μ j.1) -
          (MvPolynomial.aeval lam) (E x ℓ) -
          (algebraMap R Λ π) ^ 2 *
            (∑ ab : Fin m × Fin m,
              (MvPolynomial.aeval lam) (QC x ℓ ab) * (μ ab.1 * μ ab.2))) = 0 := by
    let tπ := algebraMap R Λ π
    let A := (MvPolynomial.aeval lam) (aPoly x)
    let B : VRows x → Λ := fun j => (MvPolynomial.aeval lam) (HC x ℓ j)
    let Q : Fin m × Fin m → Λ := fun ab => (MvPolynomial.aeval lam) (QC x ℓ ab)
    let E₀ := (MvPolynomial.aeval lam) (E x ℓ)
    have he : A * (tπ ^ 2 * μ ℓ) -
        (∑ j : VRows x, B j * (tπ ^ 2 * μ j.1)) -
        (∑ ab : Fin m × Fin m,
          Q ab * ((tπ ^ 2 * μ ab.1) * (tπ ^ 2 * μ ab.2))) =
        tπ ^ 2 * E₀ := by
      simpa only [A, B, Q, E₀, tπ, hμ] using hExactRelationEval x ℓ
    have hsq :
        (A * μ ℓ - (∑ j : VRows x, B j * μ j.1) - E₀ -
          tπ ^ 2 * (∑ ab : Fin m × Fin m, Q ab * (μ ab.1 * μ ab.2))) *
          tπ ^ 2 = 0 := by
      calc
        _ = A * (tπ ^ 2 * μ ℓ) -
            (∑ j : VRows x, B j * (tπ ^ 2 * μ j.1)) -
            (∑ ab : Fin m × Fin m,
              Q ab * ((tπ ^ 2 * μ ab.1) * (tπ ^ 2 * μ ab.2))) -
            tπ ^ 2 * E₀ := by
              simp only [sub_mul, Finset.sum_mul, Finset.mul_sum]
              ring_nf
        _ = 0 := sub_eq_zero.mpr he
    have hlin := (hΛ _).mpr hsq
    change tπ * (A * μ ℓ - (∑ j : VRows x, B j * μ j.1) - E₀ -
      tπ ^ 2 * (∑ ab : Fin m × Fin m, Q ab * (μ ab.1 * μ ab.2))) = 0
    simpa only [mul_comm tπ] using hlin
  have hChartRelationZero (ij : Fin r × Fin m) :
      evS (chartRelation ij) = 0 := by
    by_cases hij : ij.2 ∈ VRows (k ij.1)
    · simp only [chartRelation, ite_eq_left hij, map_zero]
    have hh := hChartBracketZero (k ij.1) ij.2
    simp only [chartRelation, ite_eq_right hij, map_sub, map_mul, map_add, map_sum]
    simp_rw [hEvLiftX, hEvZ]
    rw [show evS (MvPolynomial.C π) = algebraMap R Λ π from evS.commutes π]
    calc
      _ = (algebraMap R Λ π) *
          ((MvPolynomial.aeval lam) (aPoly (k ij.1)) * μ ij.2 -
            (∑ j : VRows (k ij.1),
              (MvPolynomial.aeval lam) (HC (k ij.1) ij.2 j) * μ j.1) -
            (MvPolynomial.aeval lam) (E (k ij.1) ij.2) -
            (algebraMap R Λ π) ^ 2 *
              (∑ ab : Fin m × Fin m,
                (MvPolynomial.aeval lam) (QC (k ij.1) ij.2 ab) *
                  (μ ab.1 * μ ab.2))) := by
            simp only [mul_sub, mul_add, Finset.mul_sum]
            ring_nf
      _ = 0 := hh
  have hJker : J ≤ RingHom.ker evS.toRingHom := by
    apply Ideal.span_le.mpr
    intro y hy
    rcases hy with ⟨j, rfl⟩ | ⟨ij, rfl⟩
    · exact (RingHom.mem_ker).mpr (hRelationZero j)
    · exact (RingHom.mem_ker).mpr (hChartRelationZero ij)
  let g₀ : D₀ →ₐ[R] Λ :=
    Ideal.Quotient.liftₐ J evS (fun y hy => (RingHom.mem_ker).mp (hJker hy))
  let D := ULift.{max u v w} D₀
  let : Algebra.FinitePresentation R D :=
    Algebra.FinitePresentation.equiv
      (ULift.algEquiv (R := R) (A := D₀)).symm
  let g : D →ₐ[R] Λ :=
    g₀.comp (ULift.algEquiv (R := R) (A := D₀)).toAlgHom
  let reduceD : (D ⧸ Ideal.span {algebraMap R D π}) →+*
      Λ ⧸ Ideal.span {algebraMap R Λ π} :=
    Ideal.Quotient.lift (Ideal.span {algebraMap R D π})
      ((Ideal.Quotient.mk _).comp g.toRingHom) (by
      intro d hd
      obtain ⟨e, he⟩ := Ideal.mem_span_singleton.mp hd
      change Ideal.Quotient.mk _ (g d) = 0
      apply (Ideal.Quotient.eq_zero_iff_mem).2
      rw [he, map_mul]
      exact Ideal.mem_span_singleton.mpr
        ⟨g e, by rw [g.commutes]⟩)
  have hreduceD (d : D) :
      reduceD (Ideal.Quotient.mk _ d) = Ideal.Quotient.mk _ (g d) := rfl
  have hbase : Ideal.span {π ^ 2} ≤
      Ideal.comap (algebraMap R D)
        (Ideal.span {algebraMap R D π}) := by
    apply Ideal.span_le.mpr
    intro x hx
    have hx : x = π ^ 2 := by simpa using hx
    subst x
    change algebraMap R D (π ^ 2) ∈ Ideal.span {algebraMap R D π}
    rw [map_pow]
    exact Ideal.mem_span_singleton.mpr
      ⟨algebraMap R D π, by ring⟩
  let : Algebra (R ⧸ Ideal.span {π ^ 2})
      (D ⧸ Ideal.span {algebraMap R D π}) :=
    Ideal.Quotient.algebraQuotientOfLEComap hbase
  let xD : Fin n → D ⧸ Ideal.span {algebraMap R D π} := fun i =>
    Ideal.Quotient.mk _ (ULift.up (Ideal.Quotient.mk J (liftX (MvPolynomial.X i))))
  let ψ : MvPolynomial (Fin n) (R ⧸ Ideal.span {π ^ 2}) →ₐ[R ⧸ Ideal.span {π ^ 2}]
      (D ⧸ Ideal.span {algebraMap R D π}) := MvPolynomial.aeval xD
  let evalD : MvPolynomial (Fin n) R →ₐ[R]
      (D ⧸ Ideal.span {algebraMap R D π}) :=
    (Ideal.Quotient.mkₐ R (Ideal.span {algebraMap R D π})).comp
      ((ULift.algEquiv (R := R) (A := D₀)).symm.toAlgHom.comp
        ((Ideal.Quotient.mkₐ R J).comp liftX))
  have hψEvalD (p : MvPolynomial (Fin n) R) :
      ψ (MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {π ^ 2})) p) =
        evalD p := by
    have hh : ψ.toRingHom.comp
        (MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {π ^ 2}))) =
        evalD.toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro s
        simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply,
          MvPolynomial.map_C, MvPolynomial.algHom_C, ULift.algEquiv, RingEquiv.toEquiv_eq_coe,
          AlgEquiv.symm_mk, ψ, xD, evalD]
        change (Ideal.quotientMap (Ideal.span {algebraMap R D π})
          (algebraMap R D) hbase) (Ideal.Quotient.mk _ s) =
            Ideal.Quotient.mk _ (algebraMap R D s)
        exact Ideal.quotientMap_mk
      · intro i
        simp [ψ, evalD, xD, ULift.algEquiv]
        congr 1
    exact RingHom.congr_fun hh p
  have hRelationJ (j : Fin m) :
      (Ideal.Quotient.mk J (liftX (G j)) : D₀) =
        (algebraMap R D₀ π) * Ideal.Quotient.mk J (z j) := by
    have hj : relation j ∈ J := Ideal.subset_span (Or.inl ⟨j, rfl⟩)
    have hz : (Ideal.Quotient.mk J (relation j) : D₀) = 0 :=
      (Ideal.Quotient.eq_zero_iff_mem).2 hj
    change (Ideal.Quotient.mk J
      (liftX (G j) - MvPolynomial.C π * z j) : D₀) = 0 at hz
    have hC : (Ideal.Quotient.mk J (MvPolynomial.C π) : D₀) =
        algebraMap R D₀ π := rfl
    simpa only [map_sub, map_mul, hC, sub_eq_zero] using hz
  have hψF (j : Fin m) : ψ (F j) = 0 := by
    rw [← hG j, hψEvalD]
    change Ideal.Quotient.mk _
      (ULift.up (Ideal.Quotient.mk J (liftX (G j)))) = 0
    rw [hRelationJ j]
    apply (Ideal.Quotient.eq_zero_iff_mem).2
    exact Ideal.mem_span_singleton.mpr
      ⟨ULift.up (Ideal.Quotient.mk J (z j)), by
        apply ULift.ext
        rfl⟩
  have hKerψ : RingHom.ker φ ≤ RingHom.ker ψ.toRingHom := by
    have hs : Ideal.span (Set.range F) ≤ RingHom.ker ψ.toRingHom := by
      apply Ideal.span_le.mpr
      intro y hy
      obtain ⟨j, rfl⟩ := hy
      exact (RingHom.mem_ker).2 (hψF j)
    simpa only [hF'] using hs
  let ψbar : (MvPolynomial (Fin n) (R ⧸ Ideal.span {π ^ 2}) ⧸
      RingHom.ker φ) →ₐ[R ⧸ Ideal.span {π ^ 2}]
      (D ⧸ Ideal.span {algebraMap R D π}) :=
    Ideal.Quotient.liftₐ (RingHom.ker φ) ψ
      (fun y hy => (RingHom.mem_ker).1 (hKerψ hy))
  let cAlg : C →ₐ[R ⧸ Ideal.span {π ^ 2}]
      (D ⧸ Ideal.span {algebraMap R D π}) :=
    ψbar.comp (Ideal.quotientKerAlgEquivOfSurjective hφ).symm.toAlgHom
  let c : C →+* D ⧸ Ideal.span {algebraMap R D π} := cAlg.toRingHom
  have hcφ (p : MvPolynomial (Fin n) (R ⧸ Ideal.span {π ^ 2})) :
      c (φ p) = ψ p := by
    simp [c, cAlg, ψbar, Ideal.quotientKerAlgEquivOfSurjective_symm_apply]
    rfl
  have hcπ : c (algebraMap (R ⧸ Ideal.span {π ^ 2}) C
      (Ideal.Quotient.mk (Ideal.span {π ^ 2}) π)) = 0 := by
    change cAlg (algebraMap (R ⧸ Ideal.span {π ^ 2}) C
      (Ideal.Quotient.mk (Ideal.span {π ^ 2}) π)) = 0
    rw [cAlg.commutes]
    change Ideal.Quotient.mk _ (algebraMap R D π) = 0
    exact (Ideal.Quotient.eq_zero_iff_mem).2 (Ideal.subset_span (Set.mem_singleton _))
  let cQuotAlg : (C ⧸ Ideal.span {
      algebraMap (R ⧸ Ideal.span {π ^ 2}) C
        (Ideal.Quotient.mk (Ideal.span {π ^ 2}) π)}) →ₐ[R ⧸ Ideal.span {π ^ 2}]
      (D ⧸ Ideal.span {algebraMap R D π}) :=
    Ideal.Quotient.liftₐ _ cAlg (by
      intro y hy
      obtain ⟨z, hz⟩ := Ideal.mem_span_singleton.mp hy
      have hcπAlg : cAlg (algebraMap (R ⧸ Ideal.span {π ^ 2}) C
          (Ideal.Quotient.mk (Ideal.span {π ^ 2}) π)) = 0 := hcπ
      rw [hz, map_mul, hcπAlg]
      exact zero_mul (cAlg z))
  let cQuot : (C ⧸ Ideal.span {
      algebraMap (R ⧸ Ideal.span {π ^ 2}) C
        (Ideal.Quotient.mk (Ideal.span {π ^ 2}) π)}) →+*
      (D ⧸ Ideal.span {algebraMap R D π}) := cQuotAlg.toRingHom
  let : Algebra (C ⧸ Ideal.span {
      algebraMap (R ⧸ Ideal.span {π ^ 2}) C
        (Ideal.Quotient.mk (Ideal.span {π ^ 2}) π)})
      (D ⧸ Ideal.span {algebraMap R D π}) :=
    RingHom.toAlgebra' cQuot (fun a b => by
      exact (Ideal.Quotient.commSemiring _).mul_comm (cQuot a) b)
  let : CommSemiring (C ⧸ Ideal.span {
      algebraMap (R ⧸ Ideal.span {π ^ 2}) C
        (Ideal.Quotient.mk (Ideal.span {π ^ 2}) π)}) := Ideal.Quotient.commSemiring _
  let : Semiring (D ⧸ Ideal.span {algebraMap R D π}) := Ideal.Quotient.semiring _
  have hcR (x : R) : c (algebraMap (R ⧸ Ideal.span {π ^ 2}) C
      (Ideal.Quotient.mk _ x)) = Ideal.Quotient.mk _ (algebraMap R D x) := by
    change cAlg (algebraMap (R ⧸ Ideal.span {π ^ 2}) C
      (Ideal.Quotient.mk _ x)) = _
    rw [cAlg.commutes]
    exact Ideal.quotientMap_mk
  have hcQuot (x : C) : algebraMap
      (C ⧸ Ideal.span {
        algebraMap (R ⧸ Ideal.span {π ^ 2}) C
          (Ideal.Quotient.mk (Ideal.span {π ^ 2}) π)})
      (D ⧸ Ideal.span {algebraMap R D π}) (Ideal.Quotient.mk _ x) = c x := by
    change cQuot (Ideal.Quotient.mk _ x) = c x
    rfl
  have hcompatX (i : Fin n) :
      reduceD (ψ (MvPolynomial.X i)) =
        reduceΛ (f (φ (MvPolynomial.X i))) := by
    simp only [ψ, MvPolynomial.aeval_X]
    rw [show f (φ (MvPolynomial.X i)) =
      Ideal.Quotient.mk _ (lam i) from (hLam i).symm, hreduceΛ]
    change reduceD (Ideal.Quotient.mk _
      (ULift.up (Ideal.Quotient.mk J (liftX (MvPolynomial.X i))))) = _
    rw [hreduceD]
    congr 1
    change g₀ (Ideal.Quotient.mk J (liftX (MvPolynomial.X i))) = lam i
    change evS (liftX (MvPolynomial.X i)) = lam i
    rw [hEvLiftX]
    simp
  have hcompatC (s : R ⧸ Ideal.span {π ^ 2}) :
      reduceD (ψ (MvPolynomial.C s)) =
        reduceΛ (f (φ (MvPolynomial.C s))) := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective s
    simp only [MvPolynomial.C_eq_algebraMap, ψ.commutes, φ.commutes, f.commutes]
    rw [hquot, hreduceΛ]
    change reduceD (Ideal.Quotient.mk _ (algebraMap R D x)) = _
    rw [hreduceD, g.commutes]
  have hcompatPoly : reduceD.comp ψ.toRingHom =
      reduceΛ.comp (f.toRingHom.comp φ.toRingHom) := by
    apply MvPolynomial.ringHom_ext
    · exact hcompatC
    · exact hcompatX
  have hCompat (x : C) : reduceD (c x) = reduceΛ (f x) := by
    obtain ⟨p, rfl⟩ := hφ x
    rw [hcφ]
    exact RingHom.congr_fun hcompatPoly p
  have hcak (i : Fin r) :
      c (ak i) = Ideal.Quotient.mk (Ideal.span {algebraMap R D π})
        (ULift.up (Ideal.Quotient.mk J (liftX (aPoly (k i))))) := by
    change c (a (k i)) = _
    rw [← haBar (k i), hcφ, ← haPoly (k i), hψEvalD]
    rfl
  have hJacFactor (i : Fin r) :
      Ideal.Quotient.mk (Ideal.span {algebraMap R D π})
        (ULift.up (Ideal.Quotient.mk J (liftX (aPoly (k i))))) =
      c (aMinor (k i)) *
        Ideal.Quotient.mk (Ideal.span {algebraMap R D π})
          (ULift.up (Ideal.Quotient.mk J (liftX (jacLift (k i))))) := by
    rw [← hcak i]
    change c (a (k i)) = _
    dsimp only [a]
    rw [hMinor (k i), map_mul, hP_lift, hcφ,
      ← hJacLift (k i), hψEvalD]
    rfl
  have hChartFromC
      (q : Ideal D) [q.IsPrime] (p : Ideal C) [p.IsPrime]
      (hp : Algebra.IsSmoothAt (R ⧸ Ideal.span {π ^ 2}) p)
      (hpc : p = Ideal.comap c
        (Ideal.map (Ideal.Quotient.mk (Ideal.span {algebraMap R D π})) q)) :
      ∃ i : Fin r,
        ULift.up (Ideal.Quotient.mk J (liftX (aPoly (k i)))) ∉ q := by
    obtain ⟨i, hi⟩ := hCoverFin ⟨p, ‹p.IsPrime›⟩ hp
    refine ⟨i, ?_⟩
    intro hdi
    apply hi
    change ak i ∈ p
    rw [hpc]
    change c (ak i) ∈ Ideal.map
      (Ideal.Quotient.mk (Ideal.span {algebraMap R D π})) q
    rw [hcak]
    exact Ideal.mem_map_of_mem _ hdi
  have hAwayD₀ : Algebra.Smooth R
      (Localization.Away (Ideal.Quotient.mk J (MvPolynomial.C π))) := by
    apply smooth_away_of_linear_relation_ideal_eq π G J
    simpa only [Jrel, relation, liftX, z] using hAwayIdeals.symm
  have hAwayD : Algebra.Smooth R
      (Localization.Away (algebraMap R D π)) :=
    smooth_away_of_algEquiv
      (ULift.algEquiv (R := R) (A := D₀)).symm
      (Ideal.Quotient.mk J (MvPolynomial.C π)) hAwayD₀
  have hAwayAt : ∀ (q : Ideal D) [q.IsPrime], algebraMap R D π ∉ q →
      Algebra.IsSmoothAt R q := by
    intro q _ hq
    exact isSmoothAt_of_smooth_away q hq hAwayD
  let selectedCols (i : Fin r) : VRows (k i) ↪ Fin n :=
    ⟨fun j => (((UCols (k i)).orderIsoOfFin (hU (k i)))
      (((VRows (k i)).orderIsoOfFin (hV (k i))).symm j)).1,
      fun x y h => ((VRows (k i)).orderIsoOfFin (hV (k i))).symm.injective
        (((UCols (k i)).orderIsoOfFin (hU (k i))).injective
          (Subtype.val_injective h))⟩
  have hJacSelected (i : Fin r) :
      (Matrix.det fun d e : VRows (k i) =>
        MvPolynomial.pderiv (selectedCols i e) (G d.1)) = jacLift (k i) := by
    let M : Matrix (Fin (cRows (k i))) (Fin (cRows (k i)))
        (MvPolynomial (Fin n) R) := fun d e =>
      MvPolynomial.pderiv (((UCols (k i)).orderIsoOfFin (hU (k i))) e).1
        (G (((VRows (k i)).orderIsoOfFin (hV (k i))) d).1)
    have hM := Matrix.det_submatrix_equiv_self
      ((VRows (k i)).orderIsoOfFin (hV (k i))).toEquiv.symm M
    change (Matrix.det fun d e : VRows (k i) =>
      MvPolynomial.pderiv (selectedCols i e)
        (G (((VRows (k i)).orderIsoOfFin (hV (k i)))
          (((VRows (k i)).orderIsoOfFin (hV (k i))).symm d)).1)) = _ at hM
    simpa only [OrderIso.apply_symm_apply] using hM
  have hliftXeq : ∀ b, liftX b = MvPolynomial.rename Sum.inl b := fun _ => rfl
  have hzeq : ∀ j, z j = MvPolynomial.X (Sum.inr j) := fun _ => rfl
  have hreleq : ∀ j, relation j = liftX (G j) - MvPolynomial.C π * z j := fun _ => rfl
  have hcrelzero : ∀ ij : Fin r × Fin m,
      ij.2 ∈ VRows (k ij.1) → chartRelation ij = 0 := fun _ hij => ite_eq_left hij
  have hcreleq : ∀ ij : Fin r × Fin m, ij.2 ∉ VRows (k ij.1) →
      chartRelation ij = liftX (aPoly (k ij.1)) * z ij.2 -
        (∑ j : VRows (k ij.1), liftX (HC (k ij.1) ij.2 j) * z j.1) -
        MvPolynomial.C π * (liftX (E (k ij.1) ij.2) +
          ∑ ab : Fin m × Fin m,
            liftX (QC (k ij.1) ij.2 ab) * (z ab.1 * z ab.2)) :=
    fun _ hij => ite_eq_right hij
  have hJeq : J = Ideal.span (Set.range relation ∪ Set.range chartRelation) := rfl
  have hDeriveq : ∀ (x : Fin r) (l : Fin m) (d : Fin n),
      aPoly (k x) * MvPolynomial.pderiv d (G l) -
        (∑ j : VRows (k x), HC (k x) l j * MvPolynomial.pderiv d (G j.1)) ∈
        Ideal.span (Set.range G) ⊔ Ideal.span {MvPolynomial.C π} :=
    fun x => hDerivative (k x)
  let eD : D₀ ≃ₐ[R] D := (ULift.algEquiv (R := R) (A := D₀)).symm
  let Apush := C ⧸ Ideal.span {
    algebraMap (R ⧸ Ideal.span {π ^ 2}) C
      (Ideal.Quotient.mk (Ideal.span {π ^ 2}) π)}
  let dpush : MvPolynomial (Fin n) R →+* Apush := (Ideal.Quotient.mk _).comp
    (φ.toRingHom.comp (MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {π ^ 2}))))
  have hdpush (b : MvPolynomial (Fin n) R) :
      algebraMap Apush (D ⧸ Ideal.span {algebraMap R D π}) (dpush b) =
        Ideal.Quotient.mk (Ideal.span {algebraMap R D π})
          (eD (Ideal.Quotient.mk J (liftX b))) := by
    rw [show dpush b = Ideal.Quotient.mk _
      (φ (MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {π ^ 2})) b)) from rfl,
      hcQuot, hcφ, hψEvalD]
    rfl
  have hdpushπ : dpush (MvPolynomial.C π) = 0 := by
    change Ideal.Quotient.mk _ (φ (MvPolynomial.map
      (Ideal.Quotient.mk (Ideal.span {π ^ 2})) (MvPolynomial.C π))) = 0
    rw [MvPolynomial.map_C, show φ (MvPolynomial.C
      (Ideal.Quotient.mk (Ideal.span {π ^ 2}) π)) =
      algebraMap (R ⧸ Ideal.span {π ^ 2}) C
        (Ideal.Quotient.mk (Ideal.span {π ^ 2}) π) from φ.commutes _]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  have hdpushG (l : Fin m) : dpush (G l) = 0 := by
    change Ideal.Quotient.mk _ (φ (MvPolynomial.map _ (G l))) = 0
    rw [hG, hFzero, map_zero]
  have hdpushsurj : Function.Surjective dpush := by
    intro a
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := hφ x
    obtain ⟨b, rfl⟩ := hmapLift b
    exact ⟨b, rfl⟩
  have hSmoothD (q : Ideal D) [q.IsPrime]
      (hπq : algebraMap R D π ∈ q)
      (p : Ideal C) [p.IsPrime]
      (hp : Algebra.IsSmoothAt (R ⧸ Ideal.span {π ^ 2}) p)
      (hpc : p = Ideal.comap c
        (Ideal.map (Ideal.Quotient.mk (Ideal.span {algebraMap R D π})) q)) :
      Algebra.IsSmoothAt R q := by
    obtain ⟨i, hai⟩ := hChartFromC q p hp hpc
    have hj : ULift.up (Ideal.Quotient.mk J (liftX (jacLift (k i)))) ∉ q := by
      intro hj
      have hh := hJacFactor i
      have hmem : Ideal.Quotient.mk (Ideal.span {algebraMap R D π})
          (ULift.up (Ideal.Quotient.mk J (liftX (aPoly (k i))))) ∈
          Ideal.map (Ideal.Quotient.mk (Ideal.span {algebraMap R D π})) q := by
        rw [hh]
        exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hj)
      have hle : Ideal.span {algebraMap R D π} ≤ q := by
        apply Ideal.span_le.mpr
        rintro _ (rfl : _ = _)
        exact hπq
      have hcomap := Ideal.comap_map_of_surjective
        (Ideal.Quotient.mk (Ideal.span {algebraMap R D π}))
        Ideal.Quotient.mk_surjective q
      rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hle] at hcomap
      apply hai
      change _ ∈ Ideal.comap (Ideal.Quotient.mk (Ideal.span {algebraMap R D π}))
        (Ideal.map (Ideal.Quotient.mk (Ideal.span {algebraMap R D π})) q) at hmem
      simpa only [hcomap] using hmem
    apply isSmoothAt_of_surjective_of_localized_kernel eD.toAlgHom eD.surjective q
    · exact isSmoothAt_of_chart π hR G (fun i => VRows (k i)) (fun i => aPoly (k i))
        (fun i => HC (k i)) (fun i => QC (k i)) (fun i => E (k i)) liftX hliftXeq z hzeq
        relation hreleq chartRelation hcrelzero hcreleq hPiChart hPiChartMem selectedCols
        (fun i => jacLift (k i)) hJacSelected hDeriveq hJeq hRelationJ i
        (q.comap eD.toRingHom) hπq hai hj
    · intro x hx
      have hx0 : x = 0 := eD.injective (by simpa using hx)
      simp [hx0]
  refine ⟨D, inferInstance, inferInstance, inferInstance,
    g, c, reduceΛ, reduceD, inferInstance,
    hreduceΛ, hreduceD, hCompat, hcR, hcQuot, hAwayAt, ?_, ?_⟩
  · rintro q hq hπq ⟨p, hp, hsm, hpc⟩
    exact hSmoothD q hπq p hsm hpc
  · rintro q hq ⟨p, hp, hsm, hpc⟩
    obtain ⟨i, hai⟩ := hCoverFin ⟨p, hp⟩ hsm
    have haρ : Ideal.Quotient.mk (Ideal.span {algebraMap R D π})
        (eD (Ideal.Quotient.mk J (liftX (aPoly (k i))))) ∉ q := by
      intro hh
      apply hai
      change ak i ∈ p
      rw [hpc]
      change c (ak i) ∈ q
      rw [hcak]
      exact hh
    have hjρ : Ideal.Quotient.mk (Ideal.span {algebraMap R D π})
        (eD (Ideal.Quotient.mk J (liftX (jacLift (k i))))) ∉ q := by
      intro hh
      apply haρ
      change Ideal.Quotient.mk _ (ULift.up (Ideal.Quotient.mk J
        (liftX (aPoly (k i))))) ∈ q
      rw [hJacFactor]
      exact q.mul_mem_left _ hh
    exact isSmoothAt_reduction_of_chart π G (fun i => VRows (k i)) (fun i => aPoly (k i))
      (fun i => HC (k i)) (fun i => QC (k i)) (fun i => E (k i)) liftX hliftXeq z hzeq
      relation hreleq chartRelation hcrelzero hcreleq selectedCols
      (fun i => jacLift (k i)) hJacSelected hDeriveq hJeq eD dpush hdpushsurj hdpush
      hdpushπ hdpushG q i haρ hjρ

end Stacks.Smoothing

end
