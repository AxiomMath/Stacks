module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Ideal.Operations
public import StacksFrontier.RingTheory.Norm.Projective
public import StacksFrontier.RingTheory.Spectrum.Prime.Integral

/-!
# Preliminaries for the points of the spectrum of an invariant ring

The ring-theoretic and scheme-theoretic lemmas used to describe the points of the spectrum of
the ring of invariant functions of a groupoid scheme with affine object and arrow schemes:
lifting of homomorphisms along an integral extension into an algebraically closed field, prime
avoidance for maximal ideals, the dichotomy between units and nilpotents forced by a descended
linear polynomial, the determinant of multiplication on a fibre, and the identification of a
morphism out of the spectrum of a ring with its map on global functions.

## Main results

* `AlgebraicGeometry.exists_ringHom_comp_eq_of_isIntegral`: homomorphisms into an algebraically
  closed field extend along an injective integral ring map.
* `AlgebraicGeometry.isUnit_or_isNilpotent_of_map_eq_pow_X_sub_C`: an element whose linear
  polynomial has a power descending to an algebraically closed subfield is a unit or nilpotent.
* `AlgebraicGeometry.algebraMap_det_lmul` and
  `AlgebraicGeometry.det_lmul_ne_zero_iff_isUnit`: the determinant of multiplication by an
  element, on a fibre of a finite projective algebra and over a field.
* `AlgebraicGeometry.eq_specMap_appTop`: a morphism between spectra of rings is the spectrum of
  its map on global functions.
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-! ### Ring-theoretic preliminaries -/

/-- An injective integral ring map allows every homomorphism to an algebraically closed field
to be extended. -/
theorem exists_ringHom_comp_eq_of_isIntegral {C A k : Type u} [CommRing C] [CommRing A]
    [Field k] [IsAlgClosed k] (f : C →+* A) (hf : f.IsIntegral) (hinj : Function.Injective f)
    (c : C →+* k) : ∃ h : A →+* k, h.comp f = c := by
  let _ : Algebra C A := f.toAlgebra
  have hp : (RingHom.ker c).IsPrime := RingHom.ker_isPrime c
  obtain ⟨q, hq⟩ := integral_overring_surjective f hf hinj ⟨RingHom.ker c, hp⟩
  have hcomap : q.asIdeal.comap f = RingHom.ker c := by
    simpa [PrimeSpectrum.comap_asIdeal] using congrArg PrimeSpectrum.asIdeal hq
  let cbar : (C ⧸ q.asIdeal.comap f) →+* k :=
    Ideal.Quotient.lift _ c fun x hx ↦ RingHom.mem_ker.mp (by simpa [hcomap] using hx)
  let _ : Algebra (C ⧸ q.asIdeal.comap f) (A ⧸ q.asIdeal) :=
    (Ideal.quotientMap q.asIdeal f le_rfl).toAlgebra
  let _ : Algebra (C ⧸ q.asIdeal.comap f) k := cbar.toAlgebra
  have _ : q.asIdeal.IsPrime := q.2
  let _ : IsDomain (A ⧸ q.asIdeal) := Ideal.Quotient.isDomain q.asIdeal
  let _ : IsDomain (C ⧸ q.asIdeal.comap f) := Ideal.Quotient.isDomain (q.asIdeal.comap f)
  let _ : Algebra.IsIntegral (C ⧸ q.asIdeal.comap f) (A ⧸ q.asIdeal) :=
    ⟨RingHom.IsIntegral.quotient f hf⟩
  let _ : Module.IsTorsionFree (C ⧸ q.asIdeal.comap f) (A ⧸ q.asIdeal) :=
    Module.isTorsionFree_iff_algebraMap_injective.2
      (Ideal.algebraMap_quotient_injective (R := C) (A := A) (I := q.asIdeal))
  have hcbar : Function.Injective cbar := by
    intro x y hxy
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine Ideal.Quotient.eq.mpr ?_
    rw [hcomap]
    rw [RingHom.mem_ker, map_sub, sub_eq_zero]
    simpa only [cbar, Ideal.Quotient.lift_mk] using hxy
  let _ : Module.IsTorsionFree (C ⧸ q.asIdeal.comap f) k :=
    Module.isTorsionFree_iff_algebraMap_injective.2 hcbar
  let φ : (A ⧸ q.asIdeal) →ₐ[C ⧸ q.asIdeal.comap f] k := IsAlgClosed.lift
  refine ⟨φ.toRingHom.comp (Ideal.Quotient.mk q.asIdeal), RingHom.ext fun x ↦ ?_⟩
  show φ (algebraMap (C ⧸ q.asIdeal.comap f) (A ⧸ q.asIdeal)
    (Ideal.Quotient.mk (q.asIdeal.comap f) x)) = c x
  rw [AlgHom.commutes]
  exact congrArg (fun z ↦ z) (Ideal.Quotient.lift_mk _ _ _)

/-- A maximal ideal of a finite algebra over an algebraically closed field is the kernel of a
retraction onto that field. -/
theorem exists_ringHom_to_algClosed_of_maximal {k D : Type u} [Field k] [IsAlgClosed k]
    [CommRing D] [Algebra k D] [Module.Finite k D] (m : MaximalSpectrum D) :
    ∃ β : D →+* k, β.comp (algebraMap k D) = RingHom.id k ∧ ∀ x ∈ m.asIdeal, β x = 0 := by
  have _ : Nontrivial (D ⧸ m.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr m.isMaximal.ne_top
  let _ : Algebra.IsIntegral k (D ⧸ m.asIdeal) := Algebra.IsIntegral.of_finite k (D ⧸ m.asIdeal)
  obtain ⟨g, hg⟩ := exists_ringHom_comp_eq_of_isIntegral (algebraMap k (D ⧸ m.asIdeal))
    (fun x ↦ Algebra.IsIntegral.isIntegral (R := k) (A := D ⧸ m.asIdeal) x)
    (RingHom.injective _) (RingHom.id k)
  refine ⟨g.comp (Ideal.Quotient.mk m.asIdeal), RingHom.ext fun x ↦ ?_, fun x hx ↦ ?_⟩
  · simpa using RingHom.congr_fun hg x
  · show g (Ideal.Quotient.mk m.asIdeal x) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]

/-- An element of a ring over an algebraically closed field whose linear polynomial has a
descended power is a unit or nilpotent. -/
theorem isUnit_or_isNilpotent_of_map_eq_pow_X_sub_C {k R : Type u} [Field k]
    [IsAlgClosed k] [CommRing R] (φ : k →+* R) (hφ : Function.Injective φ) (x : R) (n : ℕ)
    (hn : 0 < n) (P : Polynomial k)
    (hP : Polynomial.map φ P = (Polynomial.X - Polynomial.C x) ^ n) :
    IsUnit x ∨ IsNilpotent x := by
  have _ : Nontrivial R := Function.Injective.nontrivial hφ
  have hnatP : P.natDegree = n := by
    calc
      P.natDegree = (Polynomial.map φ P).natDegree :=
        (Polynomial.natDegree_map_eq_of_injective hφ P).symm
      _ = n := by
        rw [hP, Polynomial.Monic.natDegree_pow (Polynomial.monic_X_sub_C x),
          Polynomial.natDegree_sub_C, Polynomial.natDegree_X]
        omega
  have hdeg : P.degree ≠ 0 :=
    (Polynomial.natDegree_pos_iff_degree_pos.mp (hnatP ▸ hn)).ne'
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root P hdeg
  have hnil : IsNilpotent (φ a - x) := by
    refine ⟨n, ?_⟩
    have h := congrArg (fun Q : Polynomial R ↦ Q.eval (φ a)) hP
    rw [Polynomial.eval_map_apply, ha] at h
    simpa only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
      map_zero] using h.symm
  by_cases hzero : a = 0
  · exact Or.inr (by simpa using (show IsNilpotent (-x) by simpa [hzero] using hnil).neg)
  · refine Or.inl ?_
    have hunit := hnil.neg.isUnit_add_left_of_commute ((isUnit_iff_ne_zero.mpr hzero).map φ)
      (Commute.all _ _)
    convert hunit using 1
    ring

/-- Prime avoidance: a maximal ideal distinct from each of finitely many maximal ideals
contains an element lying in none of them. -/
theorem exists_mem_notMem_of_ne {R : Type u} [CommRing R] (m : Ideal R) (hm : m.IsMaximal)
    (s : Finset (MaximalSpectrum R)) (hne : ∀ p ∈ s, p.asIdeal ≠ m) :
    ∃ f ∈ m, ∀ p ∈ s, f ∉ p.asIdeal := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · exact ⟨0, m.zero_mem, by simp⟩
  by_contra hcon
  push Not at hcon
  have hsub : (m : Set R) ⊆ ⋃ p ∈ (s : Set (MaximalSpectrum R)), p.asIdeal := by
    intro x hx
    obtain ⟨p, hp, hxp⟩ := hcon x hx
    exact Set.mem_biUnion hp hxp
  obtain ⟨p, hps, hle⟩ :=
    (Ideal.subset_union_prime a a fun i _ _ _ ↦ i.isMaximal.isPrime).mp hsub
  exact hne p hps (hm.eq_of_le p.isMaximal.ne_top hle).symm

/-- Two retractions of a field onto a ring with the same kernel and a common section are
equal. -/
theorem ringHom_eq_of_ker_eq_of_comp_eq {A k : Type u} [CommRing A] [Field k]
    (ι : k →+* A) (f g : A →+* k) (hf : f.comp ι = RingHom.id k) (hg : g.comp ι = RingHom.id k)
    (hker : RingHom.ker f = RingHom.ker g) : f = g := by
  refine RingHom.ext fun x ↦ ?_
  have hf' : f (ι (f x)) = f x := RingHom.congr_fun hf _
  have hg' : g (ι (f x)) = f x := RingHom.congr_fun hg _
  have hx : x - ι (f x) ∈ RingHom.ker g := by
    rw [← hker, RingHom.mem_ker, map_sub, hf']
    simp
  have heq := RingHom.mem_ker.mp hx
  rw [map_sub, hg'] at heq
  exact (sub_eq_zero.mp heq).symm

/-- The determinant of multiplication by an element of a finite projective algebra, evaluated
at a point of the base valued in a field, is the determinant of multiplication on the fibre. -/
theorem algebraMap_det_lmul {R B k : Type u} [CommRing R] [CommRing B] [Field k]
    [Algebra R B] [Algebra R k] [Module.Finite R B] [Module.Projective R B] (x : B) :
    (algebraMap R k) (ProjectiveDeterminant.det (Algebra.lmul R B x)) =
      LinearMap.det (Algebra.lmul k (k ⊗[R] B) (Algebra.TensorProduct.includeRight x)) := by
  let _ : Module.Finite k (k ⊗[R] B) := Module.Finite.base_change R k B
  let _ : Module.Projective k (k ⊗[R] B) := inferInstance
  rw [← Algebra.projectiveNorm_apply, ← Algebra.projectiveNorm_baseChange,
    Algebra.projectiveNorm_apply]
  exact ProjectiveDeterminant.det_eq_linearMap_det_of_basis
    (Module.finBasis k (k ⊗[R] B)) _

/-- Multiplication by an element of a finite-dimensional algebra over a field has nonzero
determinant exactly when the element is a unit. -/
theorem det_lmul_ne_zero_iff_isUnit {k F : Type u} [Field k] [CommRing F] [Algebra k F]
    [FiniteDimensional k F] (x : F) :
    LinearMap.det (Algebra.lmul k F x) ≠ 0 ↔ IsUnit x := by
  rw [← isUnit_iff_ne_zero, ← LinearMap.isUnit_iff_isUnit_det, Algebra.lmul_isUnit_iff]

/-! ### Scheme-theoretic preliminaries -/

/-- Two points of an affine scheme valued in a ring agree as soon as they agree on global
functions. -/
theorem ext_of_appTop_eq {k : Type u} [CommRing k] {X : Scheme.{u}} [IsAffine X]
    (x y : Spec (.of k) ⟶ X)
    (h : (x.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).hom).hom =
      (y.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).hom).hom) : x = y := by
  refine AlgebraicGeometry.ext_of_isAffine ?_
  exact (cancel_mono (Scheme.ΓSpecIso (CommRingCat.of k)).hom).1 (CommRingCat.hom_ext h)

/-- A morphism between spectra of rings is the spectrum of its map on global functions. -/
theorem eq_specMap_appTop {R k : Type u} [CommRing R] [CommRing k]
    (x : Spec (.of k) ⟶ Spec (.of R)) :
    x = Spec.map (CommRingCat.ofHom
      ((Scheme.ΓSpecIso (.of R)).inv ≫ x.appTop ≫ (Scheme.ΓSpecIso (.of k)).hom).hom) := by
  refine AlgebraicGeometry.ext_of_isAffine ?_
  calc
    x.appTop = (Scheme.ΓSpecIso (.of R)).hom ≫ CommRingCat.ofHom
        ((Scheme.ΓSpecIso (.of R)).inv ≫ x.appTop ≫ (Scheme.ΓSpecIso (.of k)).hom).hom ≫
        (Scheme.ΓSpecIso (.of k)).inv := by
      refine (cancel_mono (Scheme.ΓSpecIso (.of k)).hom).1 ?_
      simp [Category.assoc]
    _ = (Scheme.ΓSpecIso (.of R)).hom ≫ ((Scheme.ΓSpecIso (.of R)).inv ≫
        (Spec.map (CommRingCat.ofHom ((Scheme.ΓSpecIso (.of R)).inv ≫ x.appTop ≫
          (Scheme.ΓSpecIso (.of k)).hom).hom)).appTop) := by
      rw [Scheme.ΓSpecIso_inv_naturality]
    _ = _ := by simp only [Iso.hom_inv_id_assoc]

end AlgebraicGeometry

end
