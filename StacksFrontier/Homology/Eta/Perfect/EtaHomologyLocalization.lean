module

public import StacksFrontier.Homology.Eta.Perfect.DeterminantalIdeal
public import StacksFrontier.Homology.Eta.Complex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.RingTheory.Flat.Basic

/-!
# The cohomology of the décalage at a prime where the cohomology is free

Let `A` be a ring, `f ∈ A` a nonzerodivisor and `M^•` a bounded complex of finite free
`A`-modules.  More on Algebra, Tag 0F7P identifies `H^i(η_f M^•)` with `H^i(M^•) / H^i(M^•)[f]`.
Consequently, at a prime `p` of `A` at which `H^i(M^•)_p` is a free `A_p`-module, the
localizations `H^i(η_f M^•)_p` and `H^i(M^•)_p` agree: the `f`-torsion of a free module over
`A_p` vanishes.  This is the module-theoretic content of Cohomology, Tag 0GTA, read on the
complex of an affine chart.

## Main results

* `ShortComplex.moduleCatHomologyLinearEquiv`: the homology of a short complex of modules is the
  quotient `Ker(g) / (Im(f) ∩ Ker(g))`.
* `Stacks.Decalage.Cohomology.homologyLinearEquivHcohom` and `etaHomologyLinearEquivHeta`: the
  homology modules of `M^•` and of `η_f M^•`, in the spelling of
  `Stacks.Decalage.Cohomology.tag_0F7P`.
* `Stacks.Decalage.Cohomology.nonempty_localizedEtaHomologyEquiv`: `H^n(η_f M^•)_p ≅ H^n(M^•)_p`
  when `H^n(M^•)_p` is free.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v

namespace CategoryTheory.ShortComplex

variable {R : Type u} [Ring R] (S : ShortComplex (ModuleCat.{v} R))

/-- **The homology of a short complex of modules**, as the quotient of the kernel of `g` by the
part of the image of `f` lying in it. -/
def moduleCatHomologyLinearEquiv :
    S.homology ≃ₗ[R] (LinearMap.ker S.g.hom ⧸
      (LinearMap.range S.f.hom).submoduleOf (LinearMap.ker S.g.hom)) :=
  S.moduleCatLeftHomologyData.homologyIso.toLinearEquiv.trans
    (Submodule.quotEquivOfEq _ _ (by
      ext x
      simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply,
        LinearMap.mem_range]
      constructor
      · rintro ⟨y, rfl⟩
        exact ⟨y, rfl⟩
      · rintro ⟨y, hy⟩
        exact ⟨y, Subtype.ext hy⟩))

end CategoryTheory.ShortComplex


namespace Stacks.Decalage.Cohomology

open EtaPow EtaComplex

variable {A : Type u} [CommRing A] (M : BoundedComplex A) {f : A}

/-- A bounded complex of finite free modules, read as a complex of `f`-torsion-free modules in
the sense of `Stacks.Decalage.Cohomology.FTFComplex`, for a nonzerodivisor `f`. -/
def boundedFTFComplex (hf : IsRegular f) : FTFComplex A f where
  M i := Fin (M.rank i) → A
  d i := (M.d i).mulVecLin
  d_comp_d i := by rw [← Matrix.mulVecLin_mul, M.dd, Matrix.mulVecLin_zero]
  tf _ := Module.Flat.isSMulRegular_of_isRegular hf

/-- The differentials of the cochain complex of a bounded complex, as linear maps. -/
theorem toCochainComplex_d_hom (i : ℤ) :
    (M.toCochainComplex.d i (i + 1)).hom = (M.d i).mulVecLin :=
  congrArg ModuleCat.Hom.hom (M.toCochainComplex_d i)

/-- **The cohomology of a bounded complex of finite free modules** in the spelling of
`Stacks.Decalage.Cohomology.tag_0F7P`. -/
def homologyLinearEquivHcohom (hf : IsRegular f) (j : ℤ) :
    M.toCochainComplex.homology (j + 1) ≃ₗ[A] Hcohom (boundedFTFComplex M hf) j :=
  (M.toCochainComplex.homologyIsoSc' j (j + 1) (j + 1 + 1) (by simp) (by simp)).toLinearEquiv.trans
    (((M.toCochainComplex.sc' j (j + 1) (j + 1 + 1)).moduleCatHomologyLinearEquiv).trans
      (Submodule.Quotient.equiv _ _ (LinearEquiv.ofEq _ _ (by
          change LinearMap.ker (M.toCochainComplex.d (j + 1) (j + 1 + 1)).hom = _
          rw [toCochainComplex_d_hom]
          rfl)) (by
        ext x
        simp only [Submodule.mem_map, Submodule.submoduleOf, Submodule.mem_comap,
          Submodule.subtype_apply, LinearMap.mem_range]
        constructor
        · rintro ⟨y, ⟨z, hz⟩, rfl⟩
          refine ⟨z, ?_⟩
          change (M.d j).mulVecLin z = y.1
          rwa [← toCochainComplex_d_hom]
        · rintro ⟨z, hz⟩
          refine ⟨⟨x.1, ?_⟩, ⟨z, ?_⟩, rfl⟩
          · have h := x.2
            change (M.d (j + 1)).mulVecLin x.1 = 0 at h
            change (M.toCochainComplex.d (j + 1) (j + 1 + 1)).hom x.1 = 0
            rwa [toCochainComplex_d_hom]
          · change (M.toCochainComplex.d j (j + 1)).hom z = x.1
            rwa [toCochainComplex_d_hom])))

/-- The décalage terms of the cochain complex of a bounded complex are the décalage terms of the
matrices of its differentials. -/
theorem term_toCochainComplex_eq (i : ℤ) :
    term f M.toCochainComplex i = fetaTerm f (M.d i).mulVecLin i :=
  congrArg (fun dd => fetaTerm f dd i) (toCochainComplex_d_hom M i)

/-- The cycles of the décalage, in the two spellings. -/
def etaCyclesEquivZeta (hf : IsRegular f) (j : ℤ) :
    LinearMap.ker ((etaObject f M.toCochainComplex).sc' j (j + 1) (j + 1 + 1)).g.hom ≃ₗ[A]
      Zeta (boundedFTFComplex M hf) j where
  toFun x := ⟨x.1.1, by
    refine ⟨term_toCochainComplex_eq M (j + 1) ▸ x.1.2, ?_⟩
    have h := x.2
    change ((etaObject f M.toCochainComplex).d (j + 1) (j + 1 + 1)).hom x.1 = 0 at h
    rw [etaObject_d] at h
    have h' := congrArg Subtype.val h
    change EtaPow.fLoc f (M.toCochainComplex.d (j + 1) (j + 1 + 1)).hom x.1.1 = 0 at h'
    rwa [toCochainComplex_d_hom] at h'⟩
  invFun z := ⟨⟨z.1, (term_toCochainComplex_eq M (j + 1)).symm ▸ z.2.1⟩, by
    change ((etaObject f M.toCochainComplex).d (j + 1) (j + 1 + 1)).hom _ = 0
    rw [etaObject_d]
    refine Subtype.ext ?_
    change EtaPow.fLoc f (M.toCochainComplex.d (j + 1) (j + 1 + 1)).hom z.1 = 0
    rw [toCochainComplex_d_hom]
    exact z.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **The cohomology of the décalage of a bounded complex of finite free modules** in the
spelling of `Stacks.Decalage.Cohomology.tag_0F7P`. -/
def etaHomologyLinearEquivHeta (hf : IsRegular f) (j : ℤ) :
    (etaObject f M.toCochainComplex).homology (j + 1) ≃ₗ[A] Heta (boundedFTFComplex M hf) j :=
  ((etaObject f M.toCochainComplex).homologyIsoSc' j (j + 1) (j + 1 + 1) (by simp)
      (by simp)).toLinearEquiv.trans
    ((((etaObject f M.toCochainComplex).sc' j (j + 1)
        (j + 1 + 1)).moduleCatHomologyLinearEquiv).trans
      (Submodule.Quotient.equiv _ _ (etaCyclesEquivZeta M hf j) (by
        ext x
        simp only [Submodule.mem_map, Submodule.submoduleOf, Submodule.mem_comap,
          Submodule.subtype_apply, LinearMap.mem_range, LinearEquiv.coe_coe]
        constructor
        · rintro ⟨y, ⟨w, hw⟩, rfl⟩
          refine ⟨w.1, (term_toCochainComplex_eq M j) ▸ w.2, ?_⟩
          have h := congrArg Subtype.val hw
          change (((etaObject f M.toCochainComplex).d j (j + 1)).hom w).1 = _ at h
          rw [etaObject_d] at h
          change EtaPow.fLoc f (M.toCochainComplex.d j (j + 1)).hom w.1 = _ at h
          rwa [toCochainComplex_d_hom] at h
        · rintro ⟨w, hw, hwx⟩
          refine ⟨(etaCyclesEquivZeta M hf j).symm x,
            ⟨⟨w, (term_toCochainComplex_eq M j).symm ▸ hw⟩, Subtype.ext ?_⟩,
            LinearEquiv.apply_symm_apply _ _⟩
          change (((etaObject f M.toCochainComplex).d j (j + 1)).hom _).1 = x.1
          rw [etaObject_d]
          change EtaPow.fLoc f (M.toCochainComplex.d j (j + 1)).hom w = x.1
          rwa [toCochainComplex_d_hom])))

/-- A surjective linear map whose kernel is killed by `f` becomes bijective after localizing at a
prime `p` at which `f` acts injectively on the source. -/
theorem bijective_localizedModule_map_of_ker_smul_eq_zero {N₁ N₂ : Type*} [AddCommGroup N₁]
    [Module A N₁] [AddCommGroup N₂] [Module A N₂] (p : Ideal A) [p.IsPrime] {Ψ : N₁ →ₗ[A] N₂}
    (hsurj : Function.Surjective Ψ) (hker : ∀ ξ, Ψ ξ = 0 → f • ξ = 0)
    (hreg : IsSMulRegular (LocalizedModule p.primeCompl N₁)
      (algebraMap A (Localization.AtPrime p) f)) :
    Function.Bijective (LocalizedModule.map p.primeCompl Ψ) := by
  refine ⟨fun x y hxy => ?_, LocalizedModule.map_surjective _ Ψ hsurj⟩
  rw [← sub_eq_zero, ← map_sub] at hxy
  rw [← sub_eq_zero]
  generalize x - y = z at hxy ⊢
  induction z using LocalizedModule.induction_on with
  | h m s =>
    rw [LocalizedModule.map_mk, ← LocalizedModule.zero_mk s, LocalizedModule.mk_eq] at hxy
    obtain ⟨t, ht⟩ := hxy
    rw [Submonoid.smul_def, Submonoid.smul_def, smul_zero, smul_zero] at ht
    refine hreg ?_
    change algebraMap A (Localization.AtPrime p) f • LocalizedModule.mk m s =
      algebraMap A (Localization.AtPrime p) f • 0
    rw [smul_zero, algebraMap_smul, LocalizedModule.smul'_mk, ← LocalizedModule.zero_mk 1,
      LocalizedModule.mk_eq]
    refine ⟨t * s, ?_⟩
    simp only [smul_zero]
    rw [Submonoid.smul_def, Submonoid.smul_def, OneMemClass.coe_one, one_smul,
      Submonoid.coe_mul, smul_comm]
    exact hker _ (by rwa [map_smul, mul_smul])

/-- **The localized cohomology of the décalage at a prime where the cohomology is free.**  Let
`M^•` be a bounded complex of finite free `A`-modules and `p` a prime of `A` at which
`H^n(M^•)_p` is a free `A_p`-module.  Then `H^n(η_f M^•)_p ≅ H^n(M^•)_p`.

By More on Algebra, Tag 0F7P, multiplication by `f^n` is a surjection
`H^n(M^•) → H^n(η_f M^•)` whose kernel is the `f`-torsion.  Localizing at `p` keeps it surjective,
and makes it injective because the `f`-torsion of the free `A_p`-module `H^n(M^•)_p` vanishes,
`f` being a nonzerodivisor of `A_p`. -/
theorem nonempty_localizedEtaHomologyEquiv (hf : IsRegular f) (p : Ideal A) [p.IsPrime] (n : ℤ)
    (hfree : Module.Free (Localization.AtPrime p)
      (LocalizedModule p.primeCompl (M.toCochainComplex.homology n))) :
    Nonempty (LocalizedModule p.primeCompl ((etaObject f M.toCochainComplex).homology n) ≃ₗ[
      Localization.AtPrime p] LocalizedModule p.primeCompl (M.toCochainComplex.homology n)) := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  let C := boundedFTFComplex M hf
  let Ψ : M.toCochainComplex.homology (j + 1) →ₗ[A]
      (etaObject f M.toCochainComplex).homology (j + 1) :=
    (etaHomologyLinearEquivHeta M hf j).symm.toLinearMap ∘ₗ etaCohomologyMap C j ∘ₗ
      (homologyLinearEquivHcohom M hf j).toLinearMap
  have hsurj : Function.Surjective Ψ :=
    (etaHomologyLinearEquivHeta M hf j).symm.surjective.comp
      ((etaCohomologyMap_surjective C j).comp (homologyLinearEquivHcohom M hf j).surjective)
  have hker : ∀ ξ, Ψ ξ = 0 → f • ξ = 0 := by
    intro ξ hξ
    have h1 : etaCohomologyMap C j (homologyLinearEquivHcohom M hf j ξ) = 0 := by
      simpa [Ψ] using congrArg (etaHomologyLinearEquivHeta M hf j) hξ
    apply (homologyLinearEquivHcohom M hf j).injective
    rw [map_smul, (etaCohomologyMap_eq_zero_iff C j _).mp h1, map_zero]
  have hreg : IsSMulRegular (LocalizedModule p.primeCompl (M.toCochainComplex.homology (j + 1)))
      (algebraMap A (Localization.AtPrime p) f) := by
    have : Module.Flat (Localization.AtPrime p)
        (LocalizedModule p.primeCompl (M.toCochainComplex.homology (j + 1))) :=
      Module.Flat.of_free
    have : Module.Flat A (LocalizedModule p.primeCompl (M.toCochainComplex.homology (j + 1))) :=
      Module.Flat.trans A (Localization.AtPrime p) _
    intro a b hab
    exact Module.Flat.isSMulRegular_of_isRegular hf (by simpa [algebraMap_smul] using hab)
  exact ⟨(LinearEquiv.ofBijective _
    (bijective_localizedModule_map_of_ker_smul_eq_zero p hsurj hker hreg)).symm⟩

end Stacks.Decalage.Cohomology

end
