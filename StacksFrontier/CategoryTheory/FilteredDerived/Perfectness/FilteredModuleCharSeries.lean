module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
public import Mathlib.Data.Int.Interval
public import Mathlib.Order.SuccPred.Int
public import StacksFrontier.Algebra.Module.Projective.Determinant.CharSeries
public import StacksFrontier.CategoryTheory.FilteredDerived.Category.Projective

/-!
# Multiplicativity of the characteristic series along a finite filtration

The characteristic series `det(1 - f T ^ d)` of an endomorphism of a filtered finite projective
module over a commutative ring is the product of the characteristic series of the induced
endomorphisms on its graded pieces. This is the determinant analogue of
`CategoryTheory.FilteredDerived.projectiveModuleTrace_eq_sum_grP` (Stacks 03TL).

## Main results

* `CategoryTheory.FilteredDerived.charSeries_eq_prod_grP`: multiplicativity along a finite
  filtration.
-/

@[expose] public section

open CategoryTheory Opposite
open scoped BigOperators

universe u v

namespace CategoryTheory.FilteredDerived

variable (R : Type u) [CommRing R]

/-- The characteristic series of any endomorphism of a trivial module is `1`. -/
private theorem charSeries_eq_one_of_subsingleton {S : Type*} [CommRing S] {M : Type*}
    [AddCommGroup M] [Module S M] [Module.Finite S M] [Module.Projective S M] [Subsingleton M]
    (φ : M →ₗ[S] M) (d : ℕ) : ProjectiveDeterminant.charSeries φ d = 1 := by
  rw [show φ = 0 from LinearMap.ext fun x => Subsingleton.elim _ _,
    ProjectiveDeterminant.charSeries_zero]

/-- A zero object of `ModuleCat S` is finite and projective. -/
private theorem finite_and_projective_of_isZero {S : Type*} [CommRing S] {X : ModuleCat S}
    (hX : Limits.IsZero X) : Module.Finite S X ∧ Projective X := by
  have := ModuleCat.subsingleton_of_isZero hX
  exact ⟨inferInstance, hX.projective⟩

/-- **Multiplicativity along a finite filtration.** The characteristic series of a filtered
endomorphism of a filtered finite projective module is the product of the characteristic series
on its graded pieces. -/
public theorem charSeries_eq_prod_grP
    (P : FiniteFilteredObject (ModuleCat.{max u v} R))
    (hP : IsFilteredFiniteProjective P)
    (f : P ⟶ P) (d : ℕ) :
    (letI : Module.Finite R ((FiniteFilteredObject.forget
          (𝒜 := ModuleCat.{max u v} R)).obj P) :=
        hP.finite_projective_forget.1;
      letI : Module.Projective R ((FiniteFilteredObject.forget
          (𝒜 := ModuleCat.{max u v} R)).obj P) :=
        hP.finite_projective_forget.2;
      ProjectiveDeterminant.charSeries
        ((FiniteFilteredObject.forget (𝒜 := ModuleCat.{max u v} R)).map f).hom d) =
      ∏ᶠ p : ℤ,
        (letI : Projective ((FiniteFilteredObject.grP
            (𝒜 := ModuleCat.{max u v} R) p).obj P) := (hP p).2;
          letI : Module.Finite R ((FiniteFilteredObject.grP
              (𝒜 := ModuleCat.{max u v} R) p).obj P) := (hP p).1;
          letI : Module.Projective R ((FiniteFilteredObject.grP
              (𝒜 := ModuleCat.{max u v} R) p).obj P) := inferInstance;
          ProjectiveDeterminant.charSeries
            ((FiniteFilteredObject.grP (𝒜 := ModuleCat.{max u v} R) p).map f).hom d) := by
  classical
  let : Module.Finite R P.obj.X := hP.finite_projective_forget.1
  let : Module.Projective R P.obj.X := hP.finite_projective_forget.2
  obtain ⟨a, ha⟩ := P.property.exists_isIso_ι
  obtain ⟨b, hb⟩ := P.property.exists_isZero_obj
  let q := max a b
  have hzeroQ : Limits.IsZero (P.obj.filtration.obj (op q)) :=
    P.obj.filtration.isZero_obj_of_le (le_max_right a b) hb
  have hstep (p : ℤ) :
      (Module.Finite R (P.obj.filtration.obj (op (p + 1))) ∧
        Projective (P.obj.filtration.obj (op (p + 1)))) →
      Module.Finite R (P.obj.filtration.obj (op p)) ∧
        Projective (P.obj.filtration.obj (op p)) := by
    rintro ⟨hfin, hproj⟩
    let S := FilteredObject.stepShortComplex (FilteredObject.succHom p) P.obj
    have : Module.Finite R S.X₁ := hfin
    have : Projective S.X₁ := hproj
    have : Module.Finite R S.X₃ := (hP p).1
    have : Projective S.X₃ := (hP p).2
    have hS : S.ShortExact := FilteredObject.stepShortComplex_shortExact _ P.obj
    let e := hS.splittingOfProjective.isoBinaryBiproduct
    have hprod : Module.Finite R ((S.X₁ ⊞ S.X₃) : ModuleCat R) :=
      Module.Finite.equiv (ModuleCat.biprodIsoProd S.X₁ S.X₃).symm.toLinearEquiv
    exact ⟨Module.Finite.equiv e.symm.toLinearEquiv,
      Projective.of_iso e.symm inferInstance⟩
  have hbase : Module.Finite R (P.obj.filtration.obj (op q)) ∧
      Projective (P.obj.filtration.obj (op q)) := by
    exact finite_and_projective_of_isZero hzeroQ
  have hall : ∀ p ≤ q, Module.Finite R (P.obj.filtration.obj (op p)) ∧
      Projective (P.obj.filtration.obj (op p)) :=
    Int.leInductionDown hbase fun p _ h => hstep (p - 1) (by rwa [sub_add_cancel])
  have hmodules (p : ℤ) :
      Module.Finite R (P.obj.filtration.obj (op p)) ∧
        Projective (P.obj.filtration.obj (op p)) := by
    by_cases hp : p ≤ q
    · exact hall p hp
    · exact finite_and_projective_of_isZero <| P.obj.filtration.isZero_obj_of_le
        (le_trans (le_max_right a b) (le_of_lt (lt_of_not_ge hp))) hb
  let U : ℤ → PowerSeries R := fun p =>
    (let : Module.Finite R (P.obj.filtration.obj (op p)) := (hmodules p).1;
     let : Projective (P.obj.filtration.obj (op p)) := (hmodules p).2;
     let : Module.Projective R (P.obj.filtration.obj (op p)) := inferInstance;
     ProjectiveDeterminant.charSeries ((f.hom.natTrans.app (op p)).hom) d)
  let G : ℤ → PowerSeries R := fun p =>
    (let : Projective ((FiniteFilteredObject.grP
        (𝒜 := ModuleCat.{max u v} R) p).obj P) := (hP p).2;
     let : Module.Finite R ((FiniteFilteredObject.grP
        (𝒜 := ModuleCat.{max u v} R) p).obj P) := (hP p).1;
     let : Module.Projective R ((FiniteFilteredObject.grP
        (𝒜 := ModuleCat.{max u v} R) p).obj P) := inferInstance;
     ProjectiveDeterminant.charSeries
       (((FiniteFilteredObject.grP (𝒜 := ModuleCat.{max u v} R) p).map f).hom) d)
  have hrec (p : ℤ) : U p = U (p + 1) * G p := by
    let S := FilteredObject.stepShortComplex (FilteredObject.succHom p) P.obj
    let θ := FilteredObject.stepShortComplexMap (FilteredObject.succHom p) f.hom
    have hS : S.ShortExact := FilteredObject.stepShortComplex_shortExact _ P.obj
    let : Module.Finite R S.X₁ := (hmodules (p + 1)).1
    let : Projective S.X₁ := (hmodules (p + 1)).2
    let : Module.Projective R S.X₁ := inferInstance
    let : Module.Finite R S.X₂ := (hmodules p).1
    let : Projective S.X₂ := (hmodules p).2
    let : Module.Projective R S.X₂ := inferInstance
    let : Projective S.X₃ := (hP p).2
    let : Module.Finite R S.X₃ := (hP p).1
    let : Module.Projective R S.X₃ := inferInstance
    have hα : θ.τ₂.hom.comp S.f.hom = S.f.hom.comp θ.τ₁.hom := by
      simpa using (congrArg (fun q => q.hom) θ.comm₁₂).symm
    have hγ : S.g.hom.comp θ.τ₂.hom = θ.τ₃.hom.comp S.g.hom := by
      simpa using congrArg (fun q => q.hom) θ.comm₂₃
    have h := ProjectiveDeterminant.charSeries_of_exact (i := S.f.hom) (q := S.g.hom)
      hS.moduleCat_injective_f
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).1 hS.exact)
      hS.moduleCat_surjective_g θ.τ₁.hom θ.τ₂.hom θ.τ₃.hom hα hγ d
    simpa [U, G, S, θ, FiniteFilteredObject.grP, FilteredObject.stepShortComplex,
      FilteredObject.stepShortComplexMap, FilteredObject.gr] using h
  let i := P.obj.filtration.ι.app (op a)
  let iso := asIso i
  let e := iso.toLinearEquiv
  let M := P.obj.filtration.obj (op a)
  let fM : Module.End R M := (f.hom.natTrans.app (op a)).hom
  let fN : Module.End R P.obj.X :=
    ((FiniteFilteredObject.forget (𝒜 := ModuleCat.{max u v} R)).map f).hom
  let : Module.Finite R M := (hmodules a).1
  let : Projective (ModuleCat.of R M) := (hmodules a).2
  let : Module.Projective R M := inferInstance
  let : Module.Finite R (((Functor.const ℤᵒᵖ).obj P.obj.X).obj (op a)) :=
    hP.finite_projective_forget.1
  let : Module.Projective R (((Functor.const ℤᵒᵖ).obj P.obj.X).obj (op a)) :=
    hP.finite_projective_forget.2
  have hcomm : i.hom.comp fM = fN.comp i.hom := congrArg (fun k => k.hom) (f.hom.comm (op a))
  have hconj : e.toLinearMap.comp (fM.comp e.symm.toLinearMap) = fN := by
    ext x
    exact (congrArg (fun k => k (e.symm x)) hcomm).trans (congrArg fN (e.apply_symm_apply x))
  have hchar : ProjectiveDeterminant.charSeries fN d = U a := by
    calc
      _ = ProjectiveDeterminant.charSeries
          (e.toLinearMap.comp (fM.comp e.symm.toLinearMap)) d := by rw [hconj]
      _ = ProjectiveDeterminant.charSeries fM d := by
        simpa [LinearEquiv.conj_apply, LinearMap.comp_assoc] using
          ProjectiveDeterminant.charSeries_conj e fM d
      _ = U a := rfl
  have hUzero (p : ℤ) (hz : Limits.IsZero (P.obj.filtration.obj (op p))) : U p = 1 := by
    let : Module.Finite R (P.obj.filtration.obj (op p)) := (hmodules p).1
    let : Projective (P.obj.filtration.obj (op p)) := (hmodules p).2
    let : Module.Projective R (P.obj.filtration.obj (op p)) := inferInstance
    let : Subsingleton (P.obj.filtration.obj (op p)) := ModuleCat.subsingleton_of_isZero hz
    exact charSeries_eq_one_of_subsingleton _ d
  have hGzero (p : ℤ) (hz : Limits.IsZero ((FiniteFilteredObject.grP
      (𝒜 := ModuleCat.{max u v} R) p).obj P)) : G p = 1 := by
    let : Projective ((FiniteFilteredObject.grP
        (𝒜 := ModuleCat.{max u v} R) p).obj P) := (hP p).2
    let : Module.Finite R ((FiniteFilteredObject.grP
        (𝒜 := ModuleCat.{max u v} R) p).obj P) := (hP p).1
    let : Module.Projective R ((FiniteFilteredObject.grP
        (𝒜 := ModuleCat.{max u v} R) p).obj P) := inferInstance
    let : Subsingleton ((FiniteFilteredObject.grP
        (𝒜 := ModuleCat.{max u v} R) p).obj P) := ModuleCat.subsingleton_of_isZero hz
    exact charSeries_eq_one_of_subsingleton _ d
  have hGzeroLow (p : ℤ) (hp : p < a) : G p = 1 :=
    hGzero p (FilteredObject.isZero_gr_obj_of_isIso_ι_app P.obj (by omega) ha)
  have hGzeroHigh (p : ℤ) (hp : b ≤ p) : G p = 1 :=
    hGzero p (FilteredObject.isZero_gr_obj_of_isZero P.obj hp hb)
  have htel : ∀ c, a ≤ c → U a = U c * ∏ p ∈ Finset.Ico a c, G p := by
    intro c hac
    induction c, hac using Int.leInduction with
    | base => simp
    | succ c hac ih =>
        rw [← Finset.prod_Ico_mul_eq_prod_Ico_add_one hac G, ih, hrec c]
        ring
  change ProjectiveDeterminant.charSeries fN d = ∏ᶠ p : ℤ, G p
  rw [hchar]
  by_cases hab : a ≤ b
  · have hsupport : Function.mulSupport G ⊆ (Finset.Ico a b : Set ℤ) := fun p hp =>
      Finset.mem_coe.2 (Finset.mem_Ico.2 ⟨not_lt.1 fun h => hp (hGzeroLow p h),
        not_le.1 fun h => hp (hGzeroHigh p h)⟩)
    rw [finprod_eq_prod_of_mulSupport_subset G hsupport, htel b hab, hUzero b hb, one_mul]
  · rw [hUzero a (P.obj.filtration.isZero_obj_of_le (le_of_not_ge hab) hb),
      finprod_eq_one_of_forall_eq_one fun p => if hp : p < a then hGzeroLow p hp
        else hGzeroHigh p (by omega)]

end CategoryTheory.FilteredDerived
