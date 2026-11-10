module

public import StacksFrontier.Deformation.Examples.Geometric.Smoothing.SingularIncidenceLocus
import all StacksFrontier.Deformation.Examples.Geometric.Smoothing.SingularIncidenceLocus
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Etale.Descent
public import Mathlib.RingTheory.Extension.Presentation.Submersive
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.RingTheory.RingHom.LocallyStandardSmooth
public import Mathlib.RingTheory.Smooth.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.FinitePresentation.ColimitsII
public import StacksFrontier.RingTheory.Artinian.Basic
public import StacksFrontier.RingTheory.Artinian.TFAE
public import StacksFrontier.RingTheory.CompleteIntersection.Basic
public import StacksFrontier.RingTheory.CompleteIntersection.Defs
public import StacksFrontier.RingTheory.CompleteIntersection.LocalRing
public import StacksFrontier.RingTheory.Henselian.Criteria
public import StacksFrontier.RingTheory.Henselian.QuasiFinite
public import StacksFrontier.RingTheory.Henselian.TFAE
public import StacksFrontier.RingTheory.Nagata.PowerSeries
public import StacksFrontier.RingTheory.QuasiFinite.Basic
public import StacksFrontier.RingTheory.Smooth.Localization
public import StacksFrontier.RingTheory.Smooth.Reduced
public import StacksFrontier.RingTheory.Syntomic.RelativeGlobalCompleteIntersection
public import StacksFrontier.RingTheory.Localization.AtPrimeQuotient

/-!
# Generic smoothness of the universal affine-linear deformation

The projection from the closed subscheme `Y` cut out by the universal affine-linear perturbation
of `f 1, …, f c` to the parameter affine space is smooth over a nonempty Zariski open subset of
the parameter space. Over the open where the Jacobian has rank `c` at every zero, a maximal
minor is invertible; the minors are the Jacobians of the naive submersive presentations and they
generate the unit ideal, which makes the localized algebra smooth.

## Main results

* `Deformation.Examples.Smoothing.exists_nonempty_open_smooth_projection`: the projection to
  the parameter affine space is smooth over a nonempty open subset.

## Implementation notes

The morphism in the conclusion of the main result is the base change of the projection to the
indicated open subscheme, written with `Scheme.Hom.resLE`.

## References

* [Stacks Project, Tag 0E7U](https://stacks.math.columbia.edu/tag/0E7U)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

universe u v w

namespace Deformation.Examples.Smoothing

private noncomputable def deformationPresentation {k : Type u} [Field k]
    {n c : ℕ} (f : Fin c → MvPolynomial (Fin n) k)
    (a : Fin c → Fin n) (ha : Function.Injective a) :
    Algebra.PreSubmersivePresentation (parameterRing k n c)
      (deformedCoordinateRing k n c f) (Fin n) (Fin c) :=
  Algebra.PreSubmersivePresentation.naive (R := parameterRing k n c) a ha

private abbrev injectiveColumnSelections (n c : ℕ) :=
  {a : Fin c → Fin n // Function.Injective a}

private theorem evaluation_of_quotient_eq {k F : Type u} [Field k] [Field F]
    {n c : ℕ} (f : Fin c → MvPolynomial (Fin n) k)
    [Algebra k (parameterRing k n c)] [Algebra (parameterRing k n c) F]
    [Algebra k F] [IsScalarTower k (parameterRing k n c) F]
    (θ : parameterRing k n c →ₐ[k] F)
    (φ : deformedCoordinateRing k n c f →ₐ[parameterRing k n c] F)
    (hθ : θ = IsScalarTower.toAlgHom k (parameterRing k n c) F)
    (x : Fin n → F)
    (hx : ∀ i, x i = φ (Ideal.Quotient.mkₐ (parameterRing k n c)
      (Ideal.span (Set.range (deformedEquation k n c f))) (MvPolynomial.X i)))
    (q : MvPolynomial (Fin n) (parameterRing k n c)) :
    MvPolynomial.aeval x (MvPolynomial.map θ.toRingHom q) =
      φ (Ideal.Quotient.mkₐ (parameterRing k n c)
        (Ideal.span (Set.range (deformedEquation k n c f))) q) := by
  have hhom : MvPolynomial.eval₂Hom θ.toRingHom x =
      (φ.toRingHom.comp (Ideal.Quotient.mk (Ideal.span (Set.range
        (deformedEquation k n c f))))) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      calc
        MvPolynomial.eval₂Hom θ.toRingHom x (MvPolynomial.C a) = θ a := by simp
        _ = algebraMap (parameterRing k n c) F a := by rw [hθ]; rfl
        _ = φ (Ideal.Quotient.mk (Ideal.span (Set.range
          (deformedEquation k n c f))) (MvPolynomial.C a)) := by
          change algebraMap (parameterRing k n c) F a =
            φ (algebraMap (parameterRing k n c)
              (deformedCoordinateRing k n c f) a)
          exact (AlgHom.commutes φ a).symm
    · intro i
      simpa using hx i
  simpa [MvPolynomial.aeval_def, MvPolynomial.eval₂_map] using
    congrArg (fun g : MvPolynomial (Fin n) (parameterRing k n c) →+* F => g q) hhom

private theorem deformationPresentation_jacobian_eval {k F : Type u} [Field k] [Field F]
    {n c : ℕ} (f : Fin c → MvPolynomial (Fin n) k)
    [Algebra k (parameterRing k n c)] [Algebra (parameterRing k n c) F]
    [Algebra k F] [IsScalarTower k (parameterRing k n c) F]
    (θ : parameterRing k n c →ₐ[k] F)
    (φ : deformedCoordinateRing k n c f →ₐ[parameterRing k n c] F)
    (hθ : θ = IsScalarTower.toAlgHom k (parameterRing k n c) F)
    (x : Fin n → F)
    (hx : ∀ i, x i = φ (Ideal.Quotient.mkₐ (parameterRing k n c)
      (Ideal.span (Set.range (deformedEquation k n c f))) (MvPolynomial.X i)))
    (a : Fin c → Fin n) (ha : Function.Injective a) :
    φ (deformationPresentation f a ha).jacobian =
      (Matrix.of fun j i => MvPolynomial.aeval x
        (MvPolynomial.map θ.toRingHom (MvPolynomial.pderiv (a i)
          (deformedEquation k n c f j)))).det := by
  classical
  let eval : MvPolynomial (Fin n) (parameterRing k n c) →+* F :=
    MvPolynomial.eval₂Hom θ.toRingHom x
  have heval (q : MvPolynomial (Fin n) (parameterRing k n c)) :
      eval q = φ (Ideal.Quotient.mkₐ (parameterRing k n c)
        (Ideal.span (Set.range (deformedEquation k n c f))) q) := by
    simpa [eval, MvPolynomial.aeval_def, MvPolynomial.eval₂_map, hθ,
      IsScalarTower.algebraMap_eq k (parameterRing k n c) F] using
      evaluation_of_quotient_eq f θ φ hθ x hx q
  let P := deformationPresentation f a ha
  calc
    φ P.jacobian = eval P.jacobiMatrix.det := by
      rw [P.jacobian_eq_jacobiMatrix_det]
      change φ (Ideal.Quotient.mkₐ (parameterRing k n c)
        (Ideal.span (Set.range (deformedEquation k n c f))) P.jacobiMatrix.det) = _
      rw [← heval]
    _ = (eval.mapMatrix P.jacobiMatrix).det := RingHom.map_det eval P.jacobiMatrix
    _ = (Matrix.of fun j i => MvPolynomial.aeval x
        (MvPolynomial.map θ.toRingHom (MvPolynomial.pderiv (a i)
          (deformedEquation k n c f j)))).det := by
      have hmat : P.jacobiMatrix.map eval =
          (Matrix.of fun j i => MvPolynomial.aeval x
            (MvPolynomial.map θ.toRingHom (MvPolynomial.pderiv (a i)
              (deformedEquation k n c f j)))).transpose := by
        ext i j
        simp [eval, P, deformationPresentation,
          Algebra.PreSubmersivePresentation.jacobiMatrix_naive,
          MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
      have heq : eval.mapMatrix P.jacobiMatrix = P.jacobiMatrix.map eval := by
        ext i j
        rfl
      rw [heq, hmat, Matrix.det_transpose]

private theorem deformation_minors_span_good_open {k : Type u} [Field k]
    {n c : ℕ} (hc : 1 ≤ c) (_hcn : c ≤ n)
    (f : Fin c → MvPolynomial (Fin n) k) :
    let R := parameterRing k n c
    let S := deformedCoordinateRing k n c f
    letI : Algebra R S := inferInstance
    letI : CommSemiring R := inferInstance
    letI : CommSemiring S := inferInstance
    let p := singularParameterPolynomial hc f
    let _q : S := algebraMap R S p
    let M : Submonoid S := Algebra.algebraMapSubmonoid S (Submonoid.powers p)
    let T : Type u := Localization M
    letI : Algebra S T := inferInstance
    Ideal.span (Set.range fun a : injectiveColumnSelections n c =>
      algebraMap (deformedCoordinateRing k n c f) T
        (deformationPresentation f a.1 a.2).jacobian) = ⊤ := by
  classical
  dsimp
  let R := parameterRing k n c
  let A0 := MvPolynomial (Fin n) R
  let I : Ideal A0 := Ideal.span (Set.range (deformedEquation k n c f))
  let S := A0 ⧸ I
  let : CommRing R := inferInstance
  let : CommRing S := inferInstance
  let : CommSemiring R := inferInstance
  let : CommSemiring S := inferInstance
  let p := singularParameterPolynomial hc f
  let q : S := algebraMap R S p
  let M : Submonoid S := Algebra.algebraMapSubmonoid S (Submonoid.powers p)
  let T : Type u := Localization M
  let : Algebra R S := inferInstance
  let : Algebra S T := inferInstance
  let : IsLocalization.Away (algebraMap R S p) T := by
    simp only [IsLocalization.Away, ← Algebra.algebraMapSubmonoid_powers]
    exact Localization.isLocalization
  let : CommRing T := inferInstance
  let : IsScalarTower R S T := inferInstance
  let JI : Ideal T := Ideal.span (Set.range fun a : injectiveColumnSelections n c =>
    algebraMap S T (deformationPresentation f a.1 a.2).jacobian)
  by_contra htop
  have hproper : JI ≠ ⊤ := by simpa [JI] using htop
  obtain ⟨m, hmmax, hle⟩ := Ideal.exists_le_maximal JI hproper
  let F := T ⧸ m
  let : Field (T ⧸ m) :=
    @Ideal.Quotient.field T (inferInstance : CommRing T) m hmmax
  let : Algebra T F := (Ideal.Quotient.mk m).toAlgebra
  let : Algebra R T := inferInstance
  have hRSTmap : algebraMap R T = (algebraMap S T).comp (algebraMap R S) :=
    IsScalarTower.algebraMap_eq R S T
  let : Algebra S F := inferInstance
  let : SMul S T := Algebra.toSMul
  let hSTF : IsScalarTower S T F := .of_algebraMap_eq fun _ => rfl
  let : Algebra R F := ((algebraMap S F).comp (algebraMap R S)).toAlgebra
  let : SMul R S := Algebra.toSMul
  let : SMul R F := Algebra.toSMul
  let : IsScalarTower R S F := .of_algebraMap_eq' rfl
  have hRSFmap : algebraMap R F = (algebraMap S F).comp (algebraMap R S) :=
    @IsScalarTower.algebraMap_eq R S F _ _ _ _ _ _ ‹IsScalarTower R S F›
  let : Algebra k R := inferInstance
  let : Algebra k F := ((algebraMap R F).comp (algebraMap k R)).toAlgebra
  let : SMul k F := Algebra.toSMul
  let : IsScalarTower k R F := .of_algebraMap_eq' rfl
  let : SMul R T := Algebra.toSMul
  have hSTFmap : algebraMap S F = (algebraMap T F).comp (algebraMap S T) :=
    @IsScalarTower.algebraMap_eq S T F _ _ _ _ _ _ hSTF
  have hRTFmap : algebraMap R F = (algebraMap T F).comp (algebraMap R T) := by
    rw [hRSFmap, hSTFmap, RingHom.comp_assoc, ← hRSTmap]
  let hRTF : IsScalarTower R T F := .of_algebraMap_eq' hRTFmap
  let θ : R →ₐ[k] F := IsScalarTower.toAlgHom k R F
  let φ : S →ₐ[R] F := IsScalarTower.toAlgHom R S F
  let x : Fin n → F := fun i => φ (Ideal.Quotient.mkₐ R I (MvPolynomial.X i))
  have hx : ∀ i, x i = φ (Ideal.Quotient.mkₐ R I (MvPolynomial.X i)) := fun _ => rfl
  have hgood : θ p ≠ 0 := by
    have hu : IsUnit (algebraMap R T p) :=
      IsLocalization.Away.algebraMap_isUnit (algebraMap R S p)
    have hu' : IsUnit (algebraMap T F (algebraMap R T p)) := hu.map (algebraMap T F)
    have hθ : θ p = algebraMap T F (algebraMap R T p) := by
      change algebraMap R F p = ((algebraMap T F).comp (algebraMap R T)) p
      rw [@IsScalarTower.algebraMap_eq R T F _ _ _ _ _ _ hRTF]
    rw [hθ]
    exact hu'.ne_zero
  have hzero : ∀ j, MvPolynomial.aeval x
      (MvPolynomial.map θ.toRingHom (deformedEquation k n c f j)) = 0 := by
    intro j
    rw [evaluation_of_quotient_eq f θ φ (by rfl) x hx]
    have hmem : deformedEquation k n c f j ∈ I :=
      Ideal.subset_span ⟨j, rfl⟩
    simp [I]
  have hrank := jacobian_full_rank_at_good_parameter hc f θ hgood x hzero
  let J : Matrix (Fin c) (Fin n) F := fun j i =>
    MvPolynomial.aeval x (MvPolynomial.pderiv i
      (MvPolynomial.map θ.toRingHom (deformedEquation k n c f j)))
  change J.rank = c at hrank
  obtain ⟨a, ha, hdet⟩ := exists_injective_columns_det_ne_zero J hrank
  let a' : injectiveColumnSelections n c := ⟨a, ha⟩
  have hvan : algebraMap S T (deformationPresentation f a ha).jacobian ∈ m :=
    hle (Ideal.subset_span ⟨a', rfl⟩)
  have hzeroMinor : φ (deformationPresentation f a ha).jacobian = 0 := by
    have hq : algebraMap T F (algebraMap S T
        (deformationPresentation f a ha).jacobian) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hvan
    change algebraMap S F (deformationPresentation f a ha).jacobian = 0
    rwa [@IsScalarTower.algebraMap_apply S T F _ _ _ _ _ _ hSTF]
  have hdet' : φ (deformationPresentation f a ha).jacobian = (J.submatrix id a).det := by
    have hmat : J.submatrix id a = Matrix.of fun j i =>
        MvPolynomial.aeval x (MvPolynomial.map θ.toRingHom
          (MvPolynomial.pderiv (a i) (deformedEquation k n c f j))) := by
      ext j i
      change MvPolynomial.aeval x
          (MvPolynomial.pderiv (a i)
            (MvPolynomial.map θ.toRingHom (deformedEquation k n c f j))) =
        MvPolynomial.aeval x (MvPolynomial.map θ.toRingHom
          (MvPolynomial.pderiv (a i) (deformedEquation k n c f j)))
      rw [MvPolynomial.pderiv_map]
    rw [hmat]
    exact deformationPresentation_jacobian_eval f θ φ (by rfl) x hx a ha
  exact hdet (hdet'.symm.trans hzeroMinor)

private theorem smooth_of_preSubmersive_family_jacobians_span {R S : Type u}
    [CommRing R] [CommRing S] [Algebra R S]
    {ι σ τ : Type} [Finite ι] [Finite σ] [Finite τ]
    (P : τ → Algebra.PreSubmersivePresentation R S ι σ)
    (hspan : Ideal.span (Set.range fun i => (P i).jacobian) = ⊤) :
    RingHom.Smooth (algebraMap R S) := by
  have hloc : RingHom.Locally RingHom.IsStandardSmooth (algebraMap R S) := by
    refine ⟨Set.range (fun i => (P i).jacobian), hspan, ?_⟩
    rintro _ ⟨i, rfl⟩
    let T := Localization.Away ((P i).jacobian)
    let : Algebra S T := inferInstance
    let : IsLocalization.Away ((P i).jacobian) T := inferInstance
    let : Algebra R T := inferInstance
    let : IsScalarTower R S T := inferInstance
    let Q : Algebra.SubmersivePresentation S T Unit Unit :=
      Algebra.SubmersivePresentation.localizationAway T ((P i).jacobian)
    let P' := Q.toPreSubmersivePresentation.comp (P i)
    have hunit : IsUnit P'.jacobian := by
      rw [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
        Algebra.smul_def]
      exact (IsLocalization.Away.algebraMap_isUnit ((P i).jacobian)).mul Q.jacobian_isUnit
    let Q' : Algebra.SubmersivePresentation R T (Unit ⊕ ι) (Unit ⊕ σ) :=
      ⟨P', hunit⟩
    change RingHom.IsStandardSmooth ((algebraMap S T).comp (algebraMap R S))
    rw [← IsScalarTower.algebraMap_eq R S T]
    exact (RingHom.isStandardSmooth_algebraMap).mpr Q'.isStandardSmooth
  exact (RingHom.smooth_iff_locally_isStandardSmooth).2 hloc

private theorem localized_deformation_algebra_smooth {k : Type u} [Field k]
    {n c : ℕ} (hc : 1 ≤ c) (hcn : c ≤ n)
    (f : Fin c → MvPolynomial (Fin n) k) :
    let R := parameterRing k n c
    let A := deformedCoordinateRing k n c f
    letI : CommRing R := inferInstance
    letI : Algebra R A := inferInstance
    letI : CommRing A := inferInstance
    let p := singularParameterPolynomial hc f
    let Q := Localization (Submonoid.powers p)
    let _q : A := algebraMap R A p
    let T : Type u := Localization (Algebra.algebraMapSubmonoid A (Submonoid.powers p))
    letI : Algebra R Q := inferInstance
    letI : Algebra A T := inferInstance
    letI : IsLocalization.Away (algebraMap R A p) T := by
      simp only [IsLocalization.Away, ← Algebra.algebraMapSubmonoid_powers]
      exact Localization.isLocalization
    letI : IsScalarTower R A T := .of_algebraMap_eq fun _ => rfl
    letI : IsLocalization.Away p Q := inferInstance
    let hp : IsUnit (algebraMap R T p) := by
      rw [IsScalarTower.algebraMap_apply R A T]
      exact IsLocalization.Away.algebraMap_isUnit (algebraMap R A p)
    let g : Q →+* T := IsLocalization.Away.lift p hp
    letI : Algebra Q T := g.toAlgebra
    RingHom.Smooth (algebraMap Q T) := by
  classical
  dsimp
  let R := parameterRing k n c
  let A := deformedCoordinateRing k n c f
  let : CommRing R := inferInstance
  let : Algebra R A := inferInstance
  let : CommRing A := inferInstance
  let p := singularParameterPolynomial hc f
  let Q := Localization (Submonoid.powers p)
  let q : A := algebraMap R A p
  let T : Type u := Localization (Algebra.algebraMapSubmonoid A (Submonoid.powers p))
  let : Algebra R Q := inferInstance
  let : Algebra A T := inferInstance
  let : IsLocalization.Away (algebraMap R A p) T := by
    simp only [IsLocalization.Away, ← Algebra.algebraMapSubmonoid_powers]
    exact Localization.isLocalization
  let : IsScalarTower R A T := .of_algebraMap_eq fun _ => rfl
  let : IsLocalization.Away p Q := inferInstance
  let hp : IsUnit (algebraMap R T p) := by
    rw [IsScalarTower.algebraMap_apply R A T]
    exact IsLocalization.Away.algebraMap_isUnit (algebraMap R A p)
  let g : Q →+* T := IsLocalization.Away.lift p hp
  let : Algebra Q T := g.toAlgebra
  let : IsScalarTower R Q T := .of_algebraMap_eq fun r => by
    exact (IsLocalization.Away.lift_eq p hp r).symm
  let e : (Q ⊗[R] A) ≃ₐ[Q] T :=
    Localization.tensorRightAlgEquiv (Submonoid.powers p) A
  let P : injectiveColumnSelections n c →
      Algebra.PreSubmersivePresentation Q T (Fin n) (Fin c) := fun i =>
    ((deformationPresentation f i.1 i.2).baseChange Q).ofAlgEquiv e
  have hspan : Ideal.span (Set.range fun i : injectiveColumnSelections n c =>
      (P i).jacobian) = ⊤ := by
    have h := deformation_minors_span_good_open hc hcn f
    have hjac (i : injectiveColumnSelections n c) :
        (P i).jacobian = algebraMap A T (deformationPresentation f i.1 i.2).jacobian := by
      calc
        (P i).jacobian = e ((deformationPresentation f i.1 i.2).baseChange Q).jacobian :=
          Algebra.PreSubmersivePresentation.jacobian_ofAlgEquiv _ e
        _ = e (1 ⊗ₜ[R] (deformationPresentation f i.1 i.2).jacobian) := by
          rw [Algebra.PreSubmersivePresentation.baseChange_jacobian]
        _ = algebraMap A T (deformationPresentation f i.1 i.2).jacobian :=
          Localization.tensorRightAlgEquiv_apply_one_tmul
            (Submonoid.powers p) (deformationPresentation f i.1 i.2).jacobian
    have hset : Set.range (fun i : injectiveColumnSelections n c => (P i).jacobian) =
        Set.range (fun i : injectiveColumnSelections n c =>
          algebraMap A T (deformationPresentation f i.1 i.2).jacobian) := by
      ext z
      constructor
      · rintro ⟨i, hi⟩
        exact ⟨i, (hjac i).symm.trans hi⟩
      · rintro ⟨i, hi⟩
        exact ⟨i, (hjac i).trans hi⟩
    rw [hset]
    simpa [R, A, T] using h
  exact smooth_of_preSubmersive_family_jacobians_span P hspan

private noncomputable def localizedAwayMapRingHom {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (r : R) : Localization.Away r →+* Localization.Away (f r) where
  toFun := Localization.awayMap f r
  map_one' := by simp [Localization.awayMap]
  map_mul' := by simp [Localization.awayMap]
  map_zero' := by simp [Localization.awayMap]
  map_add' := by simp [Localization.awayMap]

private theorem localized_deformation_awayMap_smooth {k : Type u} [Field k]
    {n c : ℕ} (hc : 1 ≤ c) (hcn : c ≤ n)
    (f : Fin c → MvPolynomial (Fin n) k) :
    let R := parameterRing k n c
    let A := deformedCoordinateRing k n c f
    letI : CommRing R := inferInstance
    letI : CommRing A := inferInstance
    (localizedAwayMapRingHom (algebraMap R A)
      (singularParameterPolynomial hc f)).Smooth := by
  classical
  let R := parameterRing k n c
  let A := deformedCoordinateRing k n c f
  let : CommRing R := inferInstance
  let : Algebra R A := inferInstance
  let : CommRing A := inferInstance
  let p := singularParameterPolynomial hc f
  let Q := Localization (Submonoid.powers p)
  let q : A := algebraMap R A p
  let T : Type u := Localization (Algebra.algebraMapSubmonoid A (Submonoid.powers p))
  let : Algebra R Q := inferInstance
  let : Algebra A T := inferInstance
  let : IsLocalization.Away (algebraMap R A p) T := by
    simp only [IsLocalization.Away, ← Algebra.algebraMapSubmonoid_powers]
    exact Localization.isLocalization
  let : IsScalarTower R A T := .of_algebraMap_eq fun _ => rfl
  let : IsLocalization.Away p Q := inferInstance
  let hp : IsUnit (algebraMap R T p) := by
    rw [IsScalarTower.algebraMap_apply R A T]
    exact IsLocalization.Away.algebraMap_isUnit (algebraMap R A p)
  let g : Q →+* T := IsLocalization.Away.lift p hp
  let : Algebra Q T := g.toAlgebra
  let : IsScalarTower R Q T := .of_algebraMap_eq fun r => by
    exact (IsLocalization.Away.lift_eq p hp r).symm
  have hlocal : RingHom.Smooth (algebraMap Q T) := by
    simpa [R, A, Q, T, p] using localized_deformation_algebra_smooth hc hcn f
  let T' := Localization.Away (algebraMap R A p)
  let : Algebra A T' := inferInstance
  let : IsLocalization (Submonoid.powers (algebraMap R A p)) T' := inferInstance
  let hp' : IsUnit (algebraMap R T' p) := by
    rw [IsScalarTower.algebraMap_apply R A T']
    exact IsLocalization.Away.algebraMap_isUnit (algebraMap R A p)
  let g' : Q →+* T' := IsLocalization.Away.lift p hp'
  let : Algebra Q T' := g'.toAlgebra
  let : IsScalarTower R Q T' := .of_algebraMap_eq fun r => by
    exact (IsLocalization.Away.lift_eq p hp' r).symm
  let e : T ≃ₐ[A] T' :=
    IsLocalization.algEquiv (Submonoid.powers (algebraMap R A p)) T T'
  have hcomp : e.toRingEquiv.toRingHom.comp (algebraMap Q T) =
      localizedAwayMapRingHom (algebraMap R A) p := by
    change e.toRingEquiv.toRingHom.comp (algebraMap Q T) =
      IsLocalization.Away.map Q T' (algebraMap R A) p
    have hmap' : IsLocalization.Away.map Q T' (algebraMap R A) p =
        algebraMap Q T' := by
      simpa [IsLocalization.Away.map] using
        (IsLocalization.algebraMap_eq_map_map_submonoid
          (Submonoid.powers p) A Q T').symm
    rw [hmap']
    apply IsLocalization.ringHom_ext (Submonoid.powers p)
    apply RingHom.ext
    intro r
    calc
      e (algebraMap Q T (algebraMap R Q r)) = e (algebraMap R T r) := by
        rw [IsScalarTower.algebraMap_apply R Q T]
      _ = algebraMap R T' r := by
        rw [IsScalarTower.algebraMap_apply R A T]
        exact e.commutes (algebraMap R A r)
      _ = algebraMap Q T' (algebraMap R Q r) := by
        rw [IsScalarTower.algebraMap_apply R Q T']
  have hsmoothComp : (e.toRingEquiv.toRingHom.comp (algebraMap Q T)).Smooth :=
    RingHom.Smooth.respectsIso.1 (algebraMap Q T) e.toRingEquiv hlocal
  rw [hcomp] at hsmoothComp
  simpa [R, A, p, Q, T'] using hsmoothComp

/-- The generic affine-linear deformation is smooth over some nonempty open in
the affine space of its coefficients. -/
@[stacks 0E7U]
public theorem exists_nonempty_open_smooth_projection
    (k : Type u) [Field k] (n c : ℕ) (hc : 1 ≤ c) (hcn : c ≤ n)
    (f : Fin c → MvPolynomial (Fin n) k) :
    let R := parameterRing k n c
    let A := deformedCoordinateRing k n c f
    let π : Spec (.of A) ⟶ Spec (.of R) :=
      Spec.map (CommRingCat.ofHom (algebraMap R A))
    ∃ U : (Spec (.of R)).Opens,
      U ≠ ⊥ ∧ Smooth (π.resLE U (π ⁻¹ᵁ U) le_rfl) := by
  classical
  dsimp
  let R := parameterRing k n c
  let A := deformedCoordinateRing k n c f
  let : CommRing R := inferInstance
  let : CommRing A := inferInstance
  let π : Spec (.of A) ⟶ Spec (.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R A))
  let p := singularParameterPolynomial hc f
  let U : (Spec (.of R)).Opens := PrimeSpectrum.basicOpen p
  refine ⟨U, ?_, ?_⟩
  · exact singularParameter_open_ne_bot hc f
  · have hring : (localizedAwayMapRingHom (algebraMap R A) p).Smooth := by
      simpa [R, A, p] using localized_deformation_awayMap_smooth hc hcn f
    have hcat : (CommRingCat.ofHom (Localization.awayMap (algebraMap R A) p)).hom =
        localizedAwayMapRingHom (algebraMap R A) p := by
      ext x
      rfl
    have hspec : Smooth (Spec.map (CommRingCat.ofHom (Localization.awayMap
        (algebraMap R A) p))) := by
      rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
      rw [hcat]
      exact hring
    have hrestrict : Smooth (π ∣_ U) := by
      let : MorphismProperty.RespectsIso (@Smooth) :=
        MorphismProperty.IsStableUnderBaseChange.respectsIso
      exact (MorphismProperty.arrow_mk_iso_iff (P := @Smooth)
        (SpecMapRestrictBasicOpenIso
          (CommRingCat.ofHom (algebraMap R A)) p)).mpr hspec
    change Smooth (π.resLE U (π ⁻¹ᵁ U) le_rfl)
    rw [Scheme.Hom.resLE_eq_morphismRestrict]
    exact hrestrict

end Deformation.Examples.Smoothing

end
