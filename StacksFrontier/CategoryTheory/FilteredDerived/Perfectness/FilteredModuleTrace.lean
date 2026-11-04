module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.SuccPred
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.FilteredDerived.Category.Projective
public import StacksFrontier.CategoryTheory.FilteredDerived.Perfectness.ProjectiveTrace

/-!
# Additivity of trace along a finite filtration of a finite projective module

The trace of an endomorphism of a filtered finite projective module is the sum of the traces of
the induced endomorphisms on its graded pieces.

## Main results

* `CategoryTheory.FilteredDerived.projectiveModuleTrace_eq_sum_grP`: for an endomorphism `f` of
  a finitely filtered module whose graded pieces are finite projective, the trace of `f` is the
  sum over `p : ℤ` of the traces of the endomorphisms `f` induces on the graded pieces.

## References

* [Stacks Project, Tag 03TL](https://stacks.math.columbia.edu/tag/03TL)
-/

@[expose] public section

open CategoryTheory Opposite
open scoped BigOperators

universe u v w

namespace CategoryTheory.FilteredDerived

/-- The trace of `f` on the `p`-th step of the filtration is its trace on the `(p + 1)`-th step
plus its trace on the `p`-th graded piece. -/
@[sga "4½ Rapport 4.2" "Two-step case of (4.2.2)", sga "5 IIIB 5.6" "special case"]
private lemma filtered_step_projectiveTrace_add (R : Type u) [Ring R]
    (P : FiniteFilteredObject (ModuleCat.{max u v} R))
    (hP : IsFilteredFiniteProjective P)
    (f : P ⟶ P) (p : ℤ)
    [Module.Finite R (P.obj.filtration.obj (op (p + 1)))]
    [Module.Projective R (P.obj.filtration.obj (op (p + 1)))]
    [Module.Finite R (P.obj.filtration.obj (op p))]
    [Module.Projective R (P.obj.filtration.obj (op p))] :
    Stacks.Trace.projectiveModuleTrace R (P.obj.filtration.obj (op p))
        ((f.hom.natTrans.app (op p)).hom) =
      Stacks.Trace.projectiveModuleTrace R (P.obj.filtration.obj (op (p + 1)))
          ((f.hom.natTrans.app (op (p + 1))).hom) +
      (letI : Projective ((FiniteFilteredObject.grP
          (𝒜 := ModuleCat.{max u v} R) p).obj P) := (hP p).2;
       letI : Module.Finite R ((FiniteFilteredObject.grP
          (𝒜 := ModuleCat.{max u v} R) p).obj P) := (hP p).1;
       letI : Module.Projective R ((FiniteFilteredObject.grP
          (𝒜 := ModuleCat.{max u v} R) p).obj P) := inferInstance;
       Stacks.Trace.projectiveModuleTrace R
          ((FiniteFilteredObject.grP (𝒜 := ModuleCat.{max u v} R) p).obj P)
          (((FiniteFilteredObject.grP (𝒜 := ModuleCat.{max u v} R) p).map f).hom)) := by
  classical
  let S := FilteredObject.stepShortComplex (FilteredObject.succHom p) P.obj
  let θ := FilteredObject.stepShortComplexMap (FilteredObject.succHom p) f.hom
  have hS : S.ShortExact := FilteredObject.stepShortComplex_shortExact _ P.obj
  let : Projective S.X₃ := (hP p).2
  let : Module.Finite R S.X₃ := (hP p).1
  let : Module.Projective R S.X₃ := inferInstance
  let : Module.Finite R S.X₁ := ‹Module.Finite R (P.obj.filtration.obj (op (p + 1)))›
  let : Module.Projective R S.X₁ := ‹Module.Projective R (P.obj.filtration.obj (op (p + 1)))›
  let : Module.Finite R S.X₂ := ‹Module.Finite R (P.obj.filtration.obj (op p))›
  let : Module.Projective R S.X₂ := ‹Module.Projective R (P.obj.filtration.obj (op p))›
  let t := hS.splittingOfProjective
  have hfs : S.f.hom.comp t.r.hom + t.s.hom.comp S.g.hom = LinearMap.id :=
    congrArg (fun q : S.X₂ ⟶ S.X₂ => q.hom) t.id
  have hfr_apply (x : S.X₁) : t.r.hom (S.f.hom x) = x := by
    exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom t.f_r) x
  have hsg_apply (y : S.X₃) : S.g.hom (t.s.hom y) = y := by
    exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom t.s_g) y
  have hgf_apply (x : S.X₁) : S.g.hom (S.f.hom x) = 0 := by simp
  have hrs (y : S.X₃) : t.r.hom (t.s.hom y) = 0 := by
    apply (ModuleCat.mono_iff_injective S.f).mp hS.mono_f
    have h : S.f.hom (t.r.hom (t.s.hom y)) + t.s.hom y = t.s.hom y := by
      simpa [hsg_apply y] using congrArg (fun k : Module.End R S.X₂ => k (t.s.hom y)) hfs
    rw [add_eq_right.mp h, map_zero]
  have hgsum (x : S.X₁) (y : S.X₃) : S.g.hom (S.f.hom x + t.s.hom y) = y := by
    rw [map_add, hgf_apply, hsg_apply, zero_add]
  let e : (S.X₁ × S.X₃) ≃ₗ[R] S.X₂ := {
    toFun z := S.f.hom z.1 + t.s.hom z.2
    invFun z := (t.r.hom z, S.g.hom z)
    left_inv z := by
      rcases z with ⟨x, y⟩
      apply Prod.ext
      · show t.r.hom (S.f.hom x + t.s.hom y) = x
        rw [map_add, hfr_apply, hrs, add_zero]
      · exact hgsum x y
    right_inv z := by simpa using congrArg (fun k : Module.End R S.X₂ => k z) hfs
    map_add' x y := by
      simp
      abel
    map_smul' r x := by simp [smul_add] }
  have he : e.toLinearMap.comp (LinearMap.inl R S.X₁ S.X₃) = S.f.hom := by
    ext x
    simp [e, LinearMap.comp_apply]
  have hg : S.g.hom.comp e.toLinearMap = LinearMap.snd R S.X₁ S.X₃ := by
    apply LinearMap.ext
    rintro ⟨x, y⟩
    exact hgsum x y
  have hα : θ.τ₂.hom.comp S.f.hom = S.f.hom.comp θ.τ₁.hom := by
    simpa using (congrArg (fun q => q.hom) θ.comm₁₂).symm
  have hγ : S.g.hom.comp θ.τ₂.hom = θ.τ₃.hom.comp S.g.hom := by
    simpa using congrArg (fun q => q.hom) θ.comm₂₃
  simpa [S, θ, FiniteFilteredObject.grP, FilteredObject.stepShortComplex,
    FilteredObject.stepShortComplexMap, FilteredObject.gr, LinearMap.comp_apply] using
    (projectiveModuleTrace_splitExact R e S.f.hom S.g.hom θ.τ₁.hom θ.τ₂.hom θ.τ₃.hom
      he hg hα hγ)

/-- A sequence of elements of an abelian group satisfying `u p = u (p + 1) + g p` telescopes:
`u a` is `u b` plus the sum of `g` over the interval `[a, b)`. -/
private lemma int_telescoping_sum {M : Type*} [AddCommGroup M]
    (u g : ℤ → M) (a b : ℤ) (hab : a ≤ b)
    (hstep : ∀ p, u p = u (p + 1) + g p) :
    u a = u b + Finset.sum (Finset.Ico a b) g := by
  induction b, hab using Int.leInduction with
  | base => simp
  | succ b hab ih =>
      rw [← Finset.sum_Ico_add_eq_sum_Ico_add_one hab g, ih, hstep b]
      abel

/-- The trace of a filtered endomorphism of a finite projective module is the sum of the traces on
its associated graded pieces. -/
@[stacks 03TL, sga "4½ Rapport 4.2" "(4.2.2) ungraded", sga "5 IIIB 5.6" "special case"]
public theorem projectiveModuleTrace_eq_sum_grP (R : Type u) [Ring R]
    (P : FiniteFilteredObject (ModuleCat.{max u v} R))
    (hP : IsFilteredFiniteProjective P)
    (f : P ⟶ P) :
    (letI : Module.Finite R ((FiniteFilteredObject.forget
          (𝒜 := ModuleCat.{max u v} R)).obj P) :=
        hP.finite_projective_forget.1;
      letI : Module.Projective R ((FiniteFilteredObject.forget
          (𝒜 := ModuleCat.{max u v} R)).obj P) :=
        hP.finite_projective_forget.2;
      Stacks.Trace.projectiveModuleTrace R
        ((FiniteFilteredObject.forget (𝒜 := ModuleCat.{max u v} R)).obj P)
        ((FiniteFilteredObject.forget (𝒜 := ModuleCat.{max u v} R)).map f).hom) =
      ∑ᶠ p : ℤ,
        (letI : Projective ((FiniteFilteredObject.grP
            (𝒜 := ModuleCat.{max u v} R) p).obj P) := (hP p).2;
          letI : Module.Finite R ((FiniteFilteredObject.grP
              (𝒜 := ModuleCat.{max u v} R) p).obj P) := (hP p).1;
          letI : Module.Projective R ((FiniteFilteredObject.grP
              (𝒜 := ModuleCat.{max u v} R) p).obj P) := inferInstance;
          Stacks.Trace.projectiveModuleTrace R
            ((FiniteFilteredObject.grP (𝒜 := ModuleCat.{max u v} R) p).obj P)
            ((FiniteFilteredObject.grP (𝒜 := ModuleCat.{max u v} R) p).map f).hom) := by
  classical
  let : Module.Finite R P.obj.X := hP.finite_projective_forget.1
  let : Module.Projective R P.obj.X := hP.finite_projective_forget.2
  show Stacks.Trace.projectiveModuleTrace R P.obj.X
      ((FiniteFilteredObject.forget (𝒜 := ModuleCat.{max u v} R)).map f).hom =
    ∑ᶠ p : ℤ,
      (have : Projective ((FiniteFilteredObject.grP
          (𝒜 := ModuleCat.{max u v} R) p).obj P) := (hP p).2;
       have : Module.Finite R ((FiniteFilteredObject.grP
          (𝒜 := ModuleCat.{max u v} R) p).obj P) := (hP p).1;
       have : Module.Projective R ((FiniteFilteredObject.grP
          (𝒜 := ModuleCat.{max u v} R) p).obj P) := inferInstance;
       Stacks.Trace.projectiveModuleTrace R
         ((FiniteFilteredObject.grP (𝒜 := ModuleCat.{max u v} R) p).obj P)
         (((FiniteFilteredObject.grP (𝒜 := ModuleCat.{max u v} R) p).map f).hom))
  obtain ⟨a, ha⟩ := P.property.exists_isIso_ι
  obtain ⟨b, hb⟩ := P.property.exists_isZero_obj
  let q := max a b
  have hzeroQ : Limits.IsZero (P.obj.filtration.obj (op q)) :=
    P.obj.filtration.isZero_obj_of_le (le_max_right a b) hb
  have hzero_fp (p : ℤ) (hz : Limits.IsZero (P.obj.filtration.obj (op p))) :
      Module.Finite R (P.obj.filtration.obj (op p)) ∧
        Projective (P.obj.filtration.obj (op p)) := by
    have := ModuleCat.subsingleton_of_isZero hz
    exact ⟨inferInstance, hz.projective⟩
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
  have hall : ∀ p ≤ q, Module.Finite R (P.obj.filtration.obj (op p)) ∧
      Projective (P.obj.filtration.obj (op p)) := by
    refine Int.leInductionDown (hzero_fp q hzeroQ) fun p _ h => hstep (p - 1) ?_
    rwa [sub_add_cancel]
  have hmodules (p : ℤ) :
      Module.Finite R (P.obj.filtration.obj (op p)) ∧
        Projective (P.obj.filtration.obj (op p)) := by
    by_cases hp : p ≤ q
    · exact hall p hp
    · exact hzero_fp p (P.obj.filtration.isZero_obj_of_le
        (le_trans (le_max_right a b) (le_of_lt (lt_of_not_ge hp))) hb)
  let U : ℤ → AdditiveCommutatorQuotient R := fun p =>
    (have : Module.Finite R (P.obj.filtration.obj (op p)) := (hmodules p).1;
     have : Projective (P.obj.filtration.obj (op p)) := (hmodules p).2;
     have : Module.Projective R (P.obj.filtration.obj (op p)) := inferInstance;
     Stacks.Trace.projectiveModuleTrace R (P.obj.filtration.obj (op p))
       ((f.hom.natTrans.app (op p)).hom))
  let G : ℤ → AdditiveCommutatorQuotient R := fun p =>
    (have : Projective ((FiniteFilteredObject.grP
        (𝒜 := ModuleCat.{max u v} R) p).obj P) := (hP p).2;
     have : Module.Finite R ((FiniteFilteredObject.grP
        (𝒜 := ModuleCat.{max u v} R) p).obj P) := (hP p).1;
     have : Module.Projective R ((FiniteFilteredObject.grP
        (𝒜 := ModuleCat.{max u v} R) p).obj P) := inferInstance;
     Stacks.Trace.projectiveModuleTrace R
       ((FiniteFilteredObject.grP (𝒜 := ModuleCat.{max u v} R) p).obj P)
       (((FiniteFilteredObject.grP (𝒜 := ModuleCat.{max u v} R) p).map f).hom))
  have hrec (p : ℤ) : U p = U (p + 1) + G p := by
    let : Module.Finite R (P.obj.filtration.obj (op (p + 1))) := (hmodules (p + 1)).1
    let : Projective (P.obj.filtration.obj (op (p + 1))) := (hmodules (p + 1)).2
    let : Module.Projective R (P.obj.filtration.obj (op (p + 1))) := inferInstance
    let : Module.Finite R (P.obj.filtration.obj (op p)) := (hmodules p).1
    let : Projective (P.obj.filtration.obj (op p)) := (hmodules p).2
    let : Module.Projective R (P.obj.filtration.obj (op p)) := inferInstance
    simpa [U] using filtered_step_projectiveTrace_add R P hP f p
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
    have hx := congrArg (fun k : M →ₗ[R] P.obj.X => k (e.symm x)) hcomm
    change i.hom (fM (e.symm x)) = fN (i.hom (e.symm x)) at hx
    calc
      e.toLinearMap (fM (e.symm x)) = i.hom (fM (e.symm x)) := rfl
      _ = fN (i.hom (e.symm x)) := hx
      _ = fN x := by
        congr 1
        show e (e.symm x) = x
        exact e.apply_symm_apply x
  have htrace : Stacks.Trace.projectiveModuleTrace R P.obj.X fN = U a := by
    calc
      _ = Stacks.Trace.projectiveModuleTrace R P.obj.X
          (e.toLinearMap.comp (fM.comp e.symm.toLinearMap)) := by rw [hconj]
      _ = Stacks.Trace.projectiveModuleTrace R M fM := by
        simpa [iso, i, M] using projectiveModuleTrace_conj R e fM
      _ = U a := by rfl
  have hUzero (p : ℤ) (hz : Limits.IsZero (P.obj.filtration.obj (op p))) : U p = 0 := by
    let : Module.Finite R (P.obj.filtration.obj (op p)) := (hmodules p).1
    let : Projective (P.obj.filtration.obj (op p)) := (hmodules p).2
    let : Module.Projective R (P.obj.filtration.obj (op p)) := inferInstance
    let : Subsingleton (P.obj.filtration.obj (op p)) := ModuleCat.subsingleton_of_isZero hz
    simpa [U] using projectiveModuleTrace_eq_zero_of_subsingleton R _
      ((f.hom.natTrans.app (op p)).hom)
  have hGzero (p : ℤ) (hz : Limits.IsZero ((FiniteFilteredObject.grP
      (𝒜 := ModuleCat.{max u v} R) p).obj P)) : G p = 0 := by
    let : Projective ((FiniteFilteredObject.grP
        (𝒜 := ModuleCat.{max u v} R) p).obj P) := (hP p).2
    let : Module.Finite R ((FiniteFilteredObject.grP
        (𝒜 := ModuleCat.{max u v} R) p).obj P) := (hP p).1
    let : Module.Projective R ((FiniteFilteredObject.grP
        (𝒜 := ModuleCat.{max u v} R) p).obj P) := inferInstance
    let : Subsingleton ((FiniteFilteredObject.grP
        (𝒜 := ModuleCat.{max u v} R) p).obj P) := ModuleCat.subsingleton_of_isZero hz
    simpa [G] using
      (projectiveModuleTrace_eq_zero_of_subsingleton R _
        (((FiniteFilteredObject.grP (𝒜 := ModuleCat.{max u v} R) p).map f).hom))
  have hGzeroLow (p : ℤ) (hp : p < a) : G p = 0 :=
    hGzero p (FilteredObject.isZero_gr_obj_of_isIso_ι_app P.obj (by omega) ha)
  have hGzeroHigh (p : ℤ) (hp : b ≤ p) : G p = 0 :=
    hGzero p (FilteredObject.isZero_gr_obj_of_isZero P.obj hp hb)
  by_cases hab : a ≤ b
  · have hsupport : Function.support G ⊆ (Finset.Ico a b : Set ℤ) := fun p hp =>
      Finset.mem_Ico.mpr ⟨not_lt.mp fun h => hp (hGzeroLow p h),
        not_le.mp fun h => hp (hGzeroHigh p h)⟩
    rw [htrace, finsum_eq_finsetSum_of_support_subset G hsupport,
      int_telescoping_sum U G a b hab hrec, hUzero b hb, zero_add]
  · have hzeroA : Limits.IsZero (P.obj.filtration.obj (op a)) :=
      P.obj.filtration.isZero_obj_of_le (le_of_not_ge hab) hb
    have hGall (p : ℤ) : G p = 0 := by
      by_cases hp : p < a
      · exact hGzeroLow p hp
      · exact hGzeroHigh p (le_trans (le_of_not_ge hab) (le_of_not_gt hp))
    rw [htrace, hUzero a hzeroA, finsum_congr hGall, finsum_zero]

end CategoryTheory.FilteredDerived
