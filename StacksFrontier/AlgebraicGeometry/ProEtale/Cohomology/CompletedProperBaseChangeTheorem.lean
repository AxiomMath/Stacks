module

public import StacksFrontier.AlgebraicGeometry.ProEtale.Cohomology.CompletedProperBaseChange
public import StacksFrontier.AlgebraicGeometry.ProEtale.Cohomology.SuccUniverseCoefficients
public import StacksFrontier.AlgebraicGeometry.ProEtale.Cohomology.ModuleTorsionBaseChange
public import StacksFrontier.Homology.Perfect.Defs

/-!
# Proper base change for derived complete pro-étale complexes

Let `f : X ⟶ Y` be a proper morphism of schemes and `g : Y' ⟶ Y` a morphism, with base change
`f' : X' ⟶ Y'`, `g' : X' ⟶ X`. Let `Λ` be a Noetherian ring and `I ⊆ Λ` an ideal with `Λ/I`
torsion. For `K ∈ D(X_proétale, Λ)` derived complete, with every `K ⊗^L_Λ Λ/Iⁿ` bounded below
with cohomology sheaves coming from `X_étale`, and every `Λ/Iⁿ` perfect, the base change map
`Lg^*_comp Rf_* K ⟶ Rf'_* L(g')^*_comp K` is an isomorphism (Stacks 09C9).

The proof follows the source: the completed base change map is invertible as soon as the base
change map is invertible modulo `I`
(`AlgebraicGeometry.ProEtale.isIso_proetaleCompletedBaseChangeMap_of_isIso_baseChange`, by derived
Nakayama, the projection formula for the perfect module `Λ/I` and the compatibility of the base
change map with `- ⊗^L Λ/I`); modulo `I` the complex `K ⊗^L Λ/I` is bounded below, killed by a
positive integer (`Λ/I` is torsion) and has cohomology sheaves coming from `X_étale`, so the base
change map there is invertible
(`AlgebraicGeometry.ProEtale.isIso_proetaleModuleDerivedBaseChange_app_of_isGE`: dévissage to
sheaves, Stacks 09B1, 09A6 and the proper base change theorem Stacks 095T).

## Main results

* `AlgebraicGeometry.ProEtale.isIso_proetaleCompletedBaseChangeMap_of_isProper`: Stacks 09C9.

## References

* [Stacks Project, Tag 09C9](https://stacks.math.columbia.edu/tag/09C9)

Standard model: uses `AlgebraicGeometry.ProEtale.proetaleCompletedBaseChangeMap`, which exists
only there.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.ProEtale

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] hasSheafify_proEt_moduleCat_succ
  isGrothendieckAbelian_proetaleModuleSheaf_succ

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The multiplication by a positive integer `m` killing `Λ/I` kills `K ⊗_Λ P` in the derived
category, for `P` a K-projective complex representing `Λ/I`. -/
theorem nsmul_id_Qh_totRight_eq_zero (I : Ideal Λ) (X : Scheme.{u}) (m : ℕ)
    (hm : m • (1 : Λ ⧸ I) = 0) (P : CochainComplex (ModuleCat.{u + 1} Λ) ℤ) [P.IsKProjective]
    (eP : (DerivedCategory.singleFunctor (ModuleCat.{u + 1} Λ) 0).obj (ModuleCat.of Λ (Λ ⧸ I)) ≅
      DerivedCategory.Q.obj P)
    (K : CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) ℤ) :
    m • 𝟙 (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj
      ((Stacks.DerivedTensor.totRight (Stacks.ConstantModuleTensor.sheafTensor
        (Scheme.ProEt.topology X) Λ) P).obj K))) = 0 := by
  have hM : m • 𝟙 (ModuleCat.of Λ (Λ ⧸ I)) = 0 := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    simpa using (show m • x = 0 by rw [nsmul_eq_mul, ← nsmul_one, hm, zero_mul])
  have hP : ((m : ℕ) : Λ) • 𝟙 (DerivedCategory.Q.obj P) = 0 := by
    rw [Nat.cast_smul_eq_nsmul]
    have : m • 𝟙 (DerivedCategory.Q.obj P) =
        eP.inv ≫ (DerivedCategory.singleFunctor (ModuleCat.{u + 1} Λ) 0).map
          (m • 𝟙 (ModuleCat.of Λ (Λ ⧸ I))) ≫ eP.hom := by
      simp
    rw [this, hM]
    simp
  have hz := Stacks.ConstantModuleTensor.Q_map_totRight_smul_eq_zero (Scheme.ProEt.topology X) Λ
    P ((m : ℕ) : Λ) hP K
  rw [Stacks.ConstantModuleTensor.totRight_map_smul_id, Functor.map_smul,
    CategoryTheory.Functor.map_id, Nat.cast_smul_eq_nsmul] at hz
  have e := (DerivedCategory.quotientCompQhIso
    (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))).app
      ((Stacks.DerivedTensor.totRight (Stacks.ConstantModuleTensor.sheafTensor
        (Scheme.ProEt.topology X) Λ) P).obj K)
  have : m • 𝟙 (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj
      ((Stacks.DerivedTensor.totRight (Stacks.ConstantModuleTensor.sheafTensor
        (Scheme.ProEt.topology X) Λ) P).obj K))) = e.hom ≫ (m • 𝟙 _) ≫ e.inv := by
    simp
  rw [this, hz]
  simp

/-- **Stacks 09C9 (proper base change for derived complete complexes).** Let `f : X ⟶ Y` be a
proper morphism of schemes and `g : Y' ⟶ Y` a morphism, with base change square
`sq : IsPullback g' f' f g`. Let `Λ` be a Noetherian ring and `I ⊆ Λ` an ideal such that `Λ/I` is
torsion. Let `K` be an object of `D(X_proétale, Λ)` such that
1. `K` is derived complete,
2. `K ⊗^L_Λ Λ/Iⁿ` is bounded below with cohomology sheaves coming from `X_étale`, and
3. `Λ/Iⁿ` is a perfect `Λ`-module,
for every `n ≥ 1`. Then the base change map `Lg^*_comp Rf_* K ⟶ Rf'_* L(g')^*_comp K` is an
isomorphism. -/
@[stacks 09C9]
theorem isIso_proetaleCompletedBaseChangeMap_of_isProper [IsNoetherianRing Λ] (I : Ideal Λ)
    (hI : IsAddTorsion (Λ ⧸ I))
    {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (sq : IsPullback g' f' f g)
    (K : ProetaleDerivedCategory Λ X)
    (hbdd : ∀ n : ℕ, 1 ≤ n → ∃ a : ℤ, ((proetaleDerivedReduction Λ I X n).obj K).IsGE a)
    (het : ∀ n : ℕ, 1 ≤ n → ∀ q : ℤ, (Scheme.etaleInverseImage.{u, 0, u + 1} X Λ).essImage
      ((DerivedCategory.homologyFunctor _ q).obj ((proetaleDerivedReduction Λ I X n).obj K)))
    (hperf : ∀ n : ℕ, 1 ≤ n → StacksDraft.Perfect.IsPerfectModule (R := Λ) (Λ ⧸ I ^ n)) :
    IsIso (proetaleCompletedBaseChangeMap Λ I f g f' g' sq.w.symm K) := by
  obtain ⟨m, hm, hm1⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.1 (hI (1 : Λ ⧸ I))
  obtain ⟨P, a, b, hPa, hPb, hfin, hproj, ⟨eP₁⟩⟩ := hperf 1 le_rfl
  let eQ : ModuleCat.of Λ (Λ ⧸ I) ≅ ModuleCat.of Λ (Λ ⧸ I ^ 1) :=
    (Submodule.quotEquivOfEq I (I ^ 1) (pow_one I).symm).toModuleIso
  let eP := (DerivedCategory.singleFunctor (ModuleCat.{u + 1} Λ) 0).mapIso eQ ≪≫ eP₁
  have : P.IsKProjective := CochainComplex.isKProjective_of_projective P b
  obtain ⟨K', hK', ⟨eK⟩⟩ :=
    Stacks.ConstantModuleTensor.exists_iso_Qh_obj_quotient_obj_of_isKInjective
      Stacks.Injectives.exists_kInjective_resolution_of_grothendieck K
  refine isIso_proetaleCompletedBaseChangeMap_of_isIso_baseChange Λ I f g f' g' sq.w.symm K P a b
    eP K' hK' eK.symm ?_
  let R := Stacks.ConstantModuleTensor.resolution Λ (ModuleCat.of Λ (Λ ⧸ I ^ 1))
  have : R.IsKProjective := CochainComplex.isKProjective_of_projective R 0
  have := isKFlat_proEt_of_projective Λ X P b
  let eQPR : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj R :=
    eP₁.symm ≪≫ (DerivedCategory.singleFunctorIsoCompQ _ 0).app _ ≪≫
      (asIso (DerivedCategory.Q.map
        (CategoryTheory.projectiveResolution (ModuleCat.of Λ (Λ ⧸ I ^ 1))).π')).symm
  obtain ⟨e₃⟩ := Stacks.ConstantModuleTensor.nonempty_derivedTensor_obj_iso
    (Scheme.ProEt.topology X) P R eQPR K
  let T := Stacks.DerivedTensor.derivedTensor
    (Stacks.ConstantModuleTensor.sheafTensor (Scheme.ProEt.topology X) Λ) P
  let eE : DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj
        ((Stacks.DerivedTensor.totRight (Stacks.ConstantModuleTensor.sheafTensor
          (Scheme.ProEt.topology X) Λ) P).obj K')) ≅
      (proetaleDerivedReduction Λ I X 1).obj K :=
    ((Stacks.DerivedTensor.derivedTensorIso _ P).app ((HomotopyCategory.quotient _ _).obj K') ≪≫
      DerivedCategory.Qh.mapIso
        ((Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiRFactors _ P).app K')).symm ≪≫
      T.mapIso eK.symm ≪≫ e₃
  have htors : m • 𝟙 ((proetaleDerivedReduction Λ I X 1).obj K) = 0 := by
    have : m • 𝟙 ((proetaleDerivedReduction Λ I X 1).obj K) = eE.inv ≫ (m • 𝟙 _) ≫ eE.hom := by
      simp
    rw [this, nsmul_id_Qh_totRight_eq_zero Λ I X m hm1 P eP K']
    simp
  obtain ⟨a', ha'⟩ := hbdd 1 le_rfl
  exact (NatTrans.isIso_app_iff_of_iso _ eE).2 <|
    isIso_proetaleModuleDerivedBaseChange_app_of_isGE Λ f g g' f' sq
      ((proetaleDerivedReduction Λ I X 1).obj K) a' ha' (het 1 le_rfl) m hm htors

end AlgebraicGeometry.ProEtale

end
