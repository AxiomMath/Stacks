module

public import StacksFrontier.CategoryTheory.Abelian.InverseSystemModuleCat
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.DerivedTensorSingle
public import StacksFrontier.RingTheory.AdicCompletion.QuotientRestrictScalars
public import StacksFrontier.RingTheory.Module.AdicSystem.PseudoCoherentHomology
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Mittag-Leffler for the cohomology of the adic reductions of a complex of finite modules

Let `A` be a Noetherian ring, `I ⊆ A` an ideal and `P` a complex of finite `A`-modules. In each
degree `i` the inverse system `n ↦ Hⁱ(P ⊗_A A/Iⁿ)` of the cohomology of the termwise tensor
products with the adic quotients `A/Iⁿ` satisfies the Mittag-Leffler condition. The termwise
tensor product `P ⊗_A A/Iⁿ` is the degreewise reduction `P/IⁿP`, whose cohomology is
Mittag-Leffler by the Artin–Rees lemma.

## Main definitions

* `Stacks.PseudoCoherent.AdicCompletion.rowComplexAdicQuotientIso`: the termwise tensor product
  of `P` with `A/𝔞` is the degreewise reduction `P/𝔞P`.

## Main results

In the namespace `Stacks.PseudoCoherent.AdicCompletion`:

* `isMittagLefflerCategorical_adicQuotient_rowFunctor_homology`: in each degree, the cohomology
  of `n ↦ P ⊗_A A/Iⁿ` is Mittag-Leffler.

## References

* [Stacks Project, Tag 0EGV](https://stacks.math.columbia.edu/tag/0EGV)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Opposite LiftAcyclic CochainComplex.KFlatBifunctor
open scoped TensorProduct

universe u

namespace Stacks.PseudoCoherent.AdicCompletion

open Stacks.AdicSystem.DerivedReductionProIso (reductionNatTrans reducedHomologyConcreteEquiv
  reducedHomologyConcreteEquiv_ideal_naturality concreteHomologyIdealTransition)

variable {A : Type u} [CommRing A]

/-- `N ⊗_A A/𝔞 ≅ N/𝔞N`, with the quotient `A/𝔞` written as the quotient of the module `A` by
the submodule `𝔞 • A`. -/
def tensorAdicQuotientEquiv (N : ModuleCat.{u} A) (𝔞 : Ideal A) :
    N ⊗[A] (A ⧸ (𝔞 • ⊤ : Submodule A A)) ≃ₗ[A] N ⧸ (𝔞 • ⊤ : Submodule A N) :=
  (TensorProduct.tensorQuotEquivQuotSMul N (𝔞 • ⊤ : Ideal A)).trans
    (Submodule.quotEquivOfEq _ _ (by rw [Ideal.smul_eq_mul, Ideal.mul_top]))

/-- `tensorAdicQuotientEquiv` sends `x ⊗ r̄` to the class of `r • x`. -/
theorem tensorAdicQuotientEquiv_tmul (N : ModuleCat.{u} A) (𝔞 : Ideal A)
    (x : N) (r : A) :
    tensorAdicQuotientEquiv N 𝔞 (x ⊗ₜ[A] Submodule.Quotient.mk r) =
      Submodule.Quotient.mk (r • x) := by
  rw [tensorAdicQuotientEquiv, LinearEquiv.trans_apply]
  exact congrArg (Submodule.quotEquivOfEq _ _ _)
    (TensorProduct.tensorQuotEquivQuotSMul_tmul_mk (𝔞 • ⊤ : Ideal A) x r)

/-- **The termwise tensor product with `A/Iⁿ` is the degreewise reduction modulo `Iⁿ`.** -/
@[ega "IV 12.3.3.5" "more general"]
def rowComplexAdicQuotientIso (I : Ideal A) (n : ℕ) (P : CochainComplex (ModuleCat.{u} A) ℤ) :
    rowComplex (curriedTensor (ModuleCat.{u} A)) P
        ((AlgebraicGeometry.ProEtale.adicQuotientModuleSystem A I (ModuleCat.of A A)).obj (op n)) ≅
      (reduceComplex (I ^ n)).obj P :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p => (tensorAdicQuotientEquiv (P.X p) (I ^ n)).toModuleIso)
    (fun p q _ => by
      apply ModuleCat.hom_ext
      apply TensorProduct.ext'
      intro x y
      obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      change ((redFunctor (I ^ n)).map (P.d p q)).hom
          (tensorAdicQuotientEquiv (P.X p) (I ^ n) (x ⊗ₜ[A] Submodule.Quotient.mk r)) =
        tensorAdicQuotientEquiv (P.X q) (I ^ n) ((P.d p q).hom x ⊗ₜ[A] Submodule.Quotient.mk r)
      rw [tensorAdicQuotientEquiv_tmul, tensorAdicQuotientEquiv_tmul]
      exact (redMap_apply_mk (I ^ n) (P.d p q) (r • x)).trans
        (congrArg Submodule.Quotient.mk (map_smul (P.d p q).hom r x)))

/-- The comparison `rowComplexAdicQuotientIso` is compatible with the transition maps. -/
theorem rowComplexAdicQuotientIso_naturality (I : Ideal A) {m n : ℕ} (h : m ≤ n)
    (P : CochainComplex (ModuleCat.{u} A) ℤ) :
    rowComplexMapRight (curriedTensor (ModuleCat.{u} A)) P
        ((AlgebraicGeometry.ProEtale.adicQuotientModuleSystem A I (ModuleCat.of A A)).map
          (homOfLE h).op) ≫
        (rowComplexAdicQuotientIso I m P).hom =
      (rowComplexAdicQuotientIso I n P).hom ≫
        (NatTrans.mapHomologicalComplex (reductionNatTrans (Ideal.pow_le_pow_right h))
          (ComplexShape.up ℤ)).app P := by
  have hY (r : A) :
      ((AlgebraicGeometry.ProEtale.adicQuotientModuleSystem A I (ModuleCat.of A A)).map
        (homOfLE h).op).hom (Submodule.Quotient.mk r) =
        (Submodule.Quotient.mk r : A ⧸ (I ^ m • ⊤ : Submodule A A)) :=
    LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
      (AlgebraicGeometry.ProEtale.adicQuotientModuleSystem_map I (ModuleCat.of A A) h))
      (Submodule.Quotient.mk r)
  ext p : 2
  apply TensorProduct.ext'
  intro x y
  obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  change tensorAdicQuotientEquiv (P.X p) (I ^ m) (x ⊗ₜ[A]
      ((AlgebraicGeometry.ProEtale.adicQuotientModuleSystem A I (ModuleCat.of A A)).map
        (homOfLE h).op).hom (Submodule.Quotient.mk r)) =
    ((reductionNatTrans (Ideal.pow_le_pow_right h)).app (P.X p)).hom
      (tensorAdicQuotientEquiv (P.X p) (I ^ n) (x ⊗ₜ[A] Submodule.Quotient.mk r))
  rw [hY]
  exact (tensorAdicQuotientEquiv_tmul (P.X p) (I ^ m) x r).trans
    (congrArg ((reductionNatTrans (Ideal.pow_le_pow_right h)).app (P.X p)).hom
      (tensorAdicQuotientEquiv_tmul (P.X p) (I ^ n) x r)).symm

/-- The identification of the cohomology of the reduction with its concrete model is compatible
with the transition maps. -/
theorem homologyMap_reductionNatTrans_comp_concreteEquiv_symm {J K : Ideal A} (hJK : J ≤ K)
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ) :
    HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex (reductionNatTrans hJK) (ComplexShape.up ℤ)).app M) i ≫
        ModuleCat.ofHom (reducedHomologyConcreteEquiv K M i).symm.toLinearMap =
      ModuleCat.ofHom (reducedHomologyConcreteEquiv J M i).symm.toLinearMap ≫
        ModuleCat.ofHom (concreteHomologyIdealTransition hJK (M.sc i).f (M.sc i).g
          (M.sc i).zero) := by
  ext y
  obtain ⟨x, rfl⟩ := (reducedHomologyConcreteEquiv J M i).surjective y
  change (reducedHomologyConcreteEquiv K M i).symm
      ((HomologicalComplex.homologyMap ((NatTrans.mapHomologicalComplex (reductionNatTrans hJK)
        (ComplexShape.up ℤ)).app M) i).hom (reducedHomologyConcreteEquiv J M i x)) =
    concreteHomologyIdealTransition hJK (M.sc i).f (M.sc i).g (M.sc i).zero
      ((reducedHomologyConcreteEquiv J M i).symm (reducedHomologyConcreteEquiv J M i x))
  rw [reducedHomologyConcreteEquiv_ideal_naturality, LinearEquiv.symm_apply_apply,
    LinearEquiv.symm_apply_apply]

/-- The inverse system of the concrete cohomology modules `Zⁱ(P/IⁿP) / Bⁱ(P/IⁿP)` of the
reductions of `P` modulo the powers of `I`, with the transition maps induced by `Iⁿ⁺¹ ≤ Iⁿ`. -/
def adicReductionHomologySystem (I : Ideal A) (P : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ) :
    ℕᵒᵖ ⥤ ModuleCat.{u} A :=
  Functor.ofOpSequence
    (X := fun n => ModuleCat.of A
      (((I ^ n • (⊤ : Submodule A (P.sc i).X₃)).comap (P.sc i).g.hom) ⧸
        (LinearMap.range (P.sc i).f.hom ⊔ I ^ n • (⊤ : Submodule A (P.sc i).X₂)).comap
          ((I ^ n • (⊤ : Submodule A (P.sc i).X₃)).comap (P.sc i).g.hom).subtype))
    (fun n => ModuleCat.ofHom (concreteHomologyIdealTransition
      (Ideal.pow_le_pow_right (Nat.le_succ n) : I ^ (n + 1) ≤ I ^ n)
      (P.sc i).f (P.sc i).g (P.sc i).zero))

/-- The component at `n` of `adicQuotientRowHomologyIso`. -/
def adicQuotientRowHomologyIsoApp (I : Ideal A) (P : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ)
    (n : ℕ) :
    (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) i).obj
        (rowComplex (curriedTensor (ModuleCat.{u} A)) P
          ((AlgebraicGeometry.ProEtale.adicQuotientModuleSystem A I (ModuleCat.of A A)).obj
            (op n))) ≅
      (adicReductionHomologySystem I P i).obj (op n) :=
  (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) i).mapIso
      (rowComplexAdicQuotientIso I n P) ≪≫
    (reducedHomologyConcreteEquiv (I ^ n) P i).symm.toModuleIso

/-- The cohomology of `P ⊗_A A/Iⁿ`, as an inverse system over `n`, is the concrete system of the
cohomology of the reductions `P/IⁿP`. -/
def adicQuotientRowHomologyIso (I : Ideal A) (P : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ) :
    AlgebraicGeometry.ProEtale.adicQuotientModuleSystem A I (ModuleCat.of A A) ⋙
        rowFunctor (curriedTensor (ModuleCat.{u} A)) P ⋙
          HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) i ≅
      adicReductionHomologySystem I P i :=
  NatIso.ofComponents (fun n => adicQuotientRowHomologyIsoApp I P i n.unop) (fun {_ _} f =>
    (NatTrans.ofOpSequence (F := AlgebraicGeometry.ProEtale.adicQuotientModuleSystem A I
        (ModuleCat.of A A) ⋙ rowFunctor (curriedTensor (ModuleCat.{u} A)) P ⋙
          HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) i)
      (G := adicReductionHomologySystem I P i)
      (fun n => (adicQuotientRowHomologyIsoApp I P i n).hom) (fun n => by
        have hc : (adicReductionHomologySystem I P i).map (homOfLE (Nat.le_succ n)).op =
            ModuleCat.ofHom (concreteHomologyIdealTransition
              (Ideal.pow_le_pow_right (Nat.le_succ n) : I ^ (n + 1) ≤ I ^ n)
              (P.sc i).f (P.sc i).g (P.sc i).zero) :=
          Functor.ofOpSequence_map_homOfLE_succ _ n
        have h1 : HomologicalComplex.homologyMap (rowComplexMapRight (curriedTensor _) P
              ((AlgebraicGeometry.ProEtale.adicQuotientModuleSystem A I (ModuleCat.of A A)).map
                (homOfLE (Nat.le_succ n)).op)) i ≫
              HomologicalComplex.homologyMap (rowComplexAdicQuotientIso I n P).hom i =
            HomologicalComplex.homologyMap (rowComplexAdicQuotientIso I (n + 1) P).hom i ≫
              HomologicalComplex.homologyMap ((NatTrans.mapHomologicalComplex
                (reductionNatTrans (Ideal.pow_le_pow_right (Nat.le_succ n) :
                  I ^ (n + 1) ≤ I ^ n)) (ComplexShape.up ℤ)).app P) i :=
          (HomologicalComplex.homologyMap_comp _ _ i).symm.trans
            ((congrArg (HomologicalComplex.homologyMap · i)
              (rowComplexAdicQuotientIso_naturality I (Nat.le_succ n) P)).trans
                (HomologicalComplex.homologyMap_comp _ _ i))
        have h2 := homologyMap_reductionNatTrans_comp_concreteEquiv_symm
          (Ideal.pow_le_pow_right (Nat.le_succ n) : I ^ (n + 1) ≤ I ^ n) P i
        rw [hc]
        exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h1).trans
          ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h2).trans
            (Category.assoc _ _ _).symm))))).naturality f)

/-- **Mittag-Leffler for the cohomology of the adic reductions of a complex of finite modules.**
For a complex `P` of finite modules over a Noetherian ring `A` and an ideal `I`, in each degree
`i` the inverse system `n ↦ Hⁱ(P ⊗_A A/Iⁿ)` satisfies the Mittag-Leffler condition. -/
theorem isMittagLefflerCategorical_adicQuotient_rowFunctor_homology [IsNoetherianRing A]
    (I : Ideal A) (P : CochainComplex (ModuleCat.{u} A) ℤ) (hP : ∀ n, Module.Finite A (P.X n))
    (i : ℤ) :
    IsMittagLefflerCategorical
      (AlgebraicGeometry.ProEtale.adicQuotientModuleSystem A I (ModuleCat.of A A) ⋙
        rowFunctor (curriedTensor (ModuleCat.{u} A)) P ⋙
          HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) i) :=
  IsMittagLefflerCategorical.of_natIso (adicQuotientRowHomologyIso I P i)
    (isMittagLefflerCategorical_of_isMittagLeffler_forget _
      (isMittagLeffler_concreteReductionHomology I P hP i))

end Stacks.PseudoCoherent.AdicCompletion

end
