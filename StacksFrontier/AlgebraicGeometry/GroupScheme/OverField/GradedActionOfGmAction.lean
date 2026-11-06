module

public import Mathlib.RingTheory.TensorProduct.MonoidAlgebra
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.GradedAction

/-!
# Actions of the multiplicative group on affine schemes

Every action of the multiplicative group scheme on an affine scheme comes from an integer
grading of its coordinate ring: the coefficients of the Laurent coaction are mutually
orthogonal projections and so decompose the ring.  Under the affine presentation, the given
action is the action associated to that grading.

## Main results

* `AlgebraicGeometry.gradingOfGmAction` identifies any multiplicative-group action on an affine
  scheme with the action associated to an integer grading of its global sections.

## Implementation notes

The canonical affine presentation is `X.isoSpec : X ≅ Spec Γ(X, ⊤)`.  The output includes a
`GradedRing` structure on additive subgroups of `Γ(X, ⊤)` and equality of the transported action
with the action constructed from that grading in Tag 0EKJ.  The fixed integral base uses the
universe-polymorphic model of the multiplicative group, so the affine scheme may lie in any
universe.

The action is pulled back from schemes to the opposite category of algebras along the fully
faithful strong monoidal functor `algSpec`, which is what turns it into a coaction on the
coordinate ring.

## References

* [Stacks Project, Tag 0EKK](https://stacks.math.columbia.edu/tag/0EKK)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open MonoidalCategory MonObj
open scoped DirectSum

namespace AlgebraicGeometry

universe u

attribute [local instance 100] ULift.algebra'

/-- Iterating a finite-support coefficient map twice and summing the resulting diagonal
coefficients evaluates the coefficient map at a coefficient. -/
private lemma sum_sum_single_apply {A : Type*} [AddCommGroup A]
    (c : A →+ ℤ →₀ A) (a : A) (i j : ℤ) :
    ((c a).sum fun n b => (c b).sum fun m d => Finsupp.single (n,m) d) (i,j) =
      c (c a i) j := by
  classical
  simp [Finsupp.sum, Finsupp.single_apply, ite_and]
  split_ifs with h <;> simp_all

/-- Pushing a finitely supported family forward along the diagonal of `ℤ` concentrates it on the
diagonal. -/
private lemma mapDomain_diag_apply {A : Type*} [AddCommGroup A] (f : ℤ →₀ A) (i j : ℤ) :
    Finsupp.mapDomain (fun n : ℤ => (n,n)) f (i,j) =
      Finsupp.single i (f i) j := by
  classical
  by_cases h : i = j
  · subst j
    rw [Finsupp.mapDomain_apply_of_injective (show Function.Injective (fun n : ℤ => (n,n)) from
      fun a b h => congrArg Prod.fst h)]
    simp
  · rw [Finsupp.mapDomain_of_notMem_range]
    · simp [h]
    · rintro ⟨n, hn⟩
      exact h ((congrArg Prod.fst hn).symm.trans (congrArg Prod.snd hn))

/-- Mutually orthogonal finite-support projections give an internal direct sum. -/
private noncomputable abbrev decompositionOfCoefficients {A : Type*} [AddCommGroup A]
    (c : A →+ ℤ →₀ A) (𝒜 : ℤ → AddSubgroup A)
    (hc : ∀ a n, c a n ∈ 𝒜 n)
    (hp : ∀ n a, a ∈ 𝒜 n → c a = Finsupp.single n a)
    (hs : ∀ a, (c a).sum (fun _ b => b) = a) : DirectSum.Decomposition 𝒜 := by
  classical
  let d : A →+ ⨁ n, 𝒜 n :=
    { toFun := fun a => ⟨fun n => ⟨c a n, hc a n⟩,
        Trunc.mk ⟨(c a).support.val, fun n => by
          by_cases hn : n ∈ (c a).support
          · exact Or.inl hn
          · exact Or.inr (Subtype.ext (Finsupp.notMem_support_iff.mp hn))⟩⟩
      map_zero' := by ext n; simp
      map_add' := fun a b => by ext n; simp }
  have hd (a : A) (n : ℤ) : (d a n : A) = c a n := rfl
  apply DirectSum.Decomposition.ofAddHom 𝒜 d
  · ext a
    change DirectSum.coeAddMonoidHom 𝒜 (d a) = a
    rw [DirectSum.coeAddMonoidHom_eq_dfinsuppSum]
    have hsupport : (d a).support = (c a).support := by
      ext n
      simp only [DFinsupp.mem_support_toFun, Finsupp.mem_support_iff]
      exact not_congr (Subtype.ext_iff)
    simpa only [DFinsupp.sum, hsupport, hd, Finsupp.sum] using hs a
  · apply DirectSum.addHom_ext
    intro n a
    change d (DirectSum.coeAddMonoidHom 𝒜 (DirectSum.of (fun n => 𝒜 n) n a)) = _
    rw [DirectSum.coeAddMonoidHom_of]
    ext m
    change c (a : A) m = _
    rw [hp n a a.property]
    by_cases h : n = m <;> simp [DirectSum.coe_of_apply, h]

/-- Pull an action back along a fully faithful strong monoidal functor. -/
@[implicit_reducible]
private noncomputable def pullModObj
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D)
    [F.Monoidal] [F.Full] [F.Faithful]
    (M : C) [MonObj M]
    (X : C) (M' : MonObj (F.obj M))
    (hone : Functor.LaxMonoidal.ε F ≫ F.map (MonObj.one (X := M)) = M'.one)
    (hmul : Functor.LaxMonoidal.μ F M M ≫ F.map (MonObj.mul (X := M)) = M'.mul)
    (act : letI : MonoidalLeftAction D
              D := MonoidalCategory.selfLeftAction _
           letI : MonObj (F.obj M) := M'; ModObj (F.obj M) (F.obj X)) :
    letI : MonoidalLeftAction C
        C := MonoidalCategory.selfLeftAction _
    ModObj M X := by
  let : MonoidalLeftAction C
      C := MonoidalCategory.selfLeftAction _
  let : MonoidalLeftAction D
      D := MonoidalCategory.selfLeftAction _
  let : MonObj (F.obj M) := M'
  let smul : M ⊗ X ⟶ X := F.preimage
    (Functor.OplaxMonoidal.δ F M X ≫ act.smul)
  have key {Z : D} {Y : C} (u : Z ⟶ F.obj Y) (f : Y ⟶ M) :
      (u ▷ F.obj X ≫ Functor.LaxMonoidal.μ F Y X) ≫
        F.map (f ▷ X) ≫ Functor.OplaxMonoidal.δ F M X ≫ act.smul =
      (u ≫ F.map f) ▷ F.obj X ≫ act.smul := by
    have hn := (Functor.LaxMonoidal.μ_natural_left_assoc F f X
      (Functor.OplaxMonoidal.δ F M X ≫ act.smul)).symm
    simpa [Category.assoc, MonoidalCategory.comp_whiskerRight] using congrArg
      (fun g => u ▷ F.obj X ≫ g) hn
  refine ⟨smul, ?_, ?_⟩
  · apply F.map_injective
    change F.map (MonObj.one (X := M) ▷ X ≫ smul) = F.map (λ_ X).hom
    simp only [Functor.map_comp, smul, F.map_preimage]
    rw [← cancel_epi (Functor.LaxMonoidal.ε F ▷ F.obj X ≫
      Functor.LaxMonoidal.μ F (𝟙_ C) X)]
    calc
      (Functor.LaxMonoidal.ε F ▷ F.obj X ≫ Functor.LaxMonoidal.μ F (𝟙_ C) X) ≫
          F.map (MonObj.one (X := M) ▷ X) ≫ Functor.OplaxMonoidal.δ F M X ≫ act.smul =
        (M'.one ▷ F.obj X) ≫ act.smul := by rw [key, hone]
      _ = (λ_ (F.obj X)).hom := act.one_smul
      _ = (Functor.LaxMonoidal.ε F ▷ F.obj X ≫
          Functor.LaxMonoidal.μ F (𝟙_ C) X) ≫ F.map (λ_ X).hom := by
        simp
  · apply F.map_injective
    change F.map (MonObj.mul (X := M) ▷ X ≫ smul) =
      F.map ((α_ M M X).hom ≫ M ◁ smul ≫ smul)
    simp only [Functor.map_comp, smul, F.map_preimage]
    rw [← cancel_epi (Functor.LaxMonoidal.μ F M M ▷ F.obj X ≫
      Functor.LaxMonoidal.μ F (M ⊗ M) X)]
    change (Functor.LaxMonoidal.μ F M M ▷ F.obj X ≫ Functor.LaxMonoidal.μ F (M ⊗ M) X) ≫
        F.map (MonObj.mul (X := M) ▷ X) ≫ Functor.OplaxMonoidal.δ F M X ≫ act.smul =
      (Functor.LaxMonoidal.μ F M M ▷ F.obj X ≫ Functor.LaxMonoidal.μ F (M ⊗ M) X) ≫
        F.map (α_ M M X).hom ≫ F.map (M ◁ smul) ≫
          Functor.OplaxMonoidal.δ F M X ≫ act.smul
    calc
      (Functor.LaxMonoidal.μ F M M ▷ F.obj X ≫ Functor.LaxMonoidal.μ F (M ⊗ M) X) ≫
          F.map (MonObj.mul (X := M) ▷ X) ≫ Functor.OplaxMonoidal.δ F M X ≫ act.smul =
        (M'.mul ▷ F.obj X) ≫ act.smul := by rw [key, hmul]
      _ = (α_ (F.obj M) (F.obj M) (F.obj X)).hom ≫
            F.obj M ◁ act.smul ≫ act.smul := act.mul_smul
      _ = (Functor.LaxMonoidal.μ F M M ▷ F.obj X ≫ Functor.LaxMonoidal.μ F (M ⊗ M) X) ≫
            F.map (α_ M M X).hom ≫ F.map (M ◁ smul) ≫
              Functor.OplaxMonoidal.δ F M X ≫ act.smul := by
          symm
          calc
            (Functor.LaxMonoidal.μ F M M ▷ F.obj X ≫ Functor.LaxMonoidal.μ F (M ⊗ M) X) ≫
                F.map (α_ M M X).hom ≫ F.map (M ◁ smul) ≫
                  Functor.OplaxMonoidal.δ F M X ≫ act.smul =
              (α_ (F.obj M) (F.obj M) (F.obj X)).hom ≫ F.obj M ◁
                  Functor.LaxMonoidal.μ F M X ≫ Functor.LaxMonoidal.μ F M (M ⊗ X) ≫
                    F.map (M ◁ smul) ≫ Functor.OplaxMonoidal.δ F M X ≫ act.smul := by
                simp [Category.assoc]
            _ = (α_ (F.obj M) (F.obj M) (F.obj X)).hom ≫ F.obj M ◁
                  Functor.LaxMonoidal.μ F M X ≫ Functor.LaxMonoidal.μ F M (M ⊗ X) ≫
                    Functor.OplaxMonoidal.δ F M (M ⊗ X) ≫
                    F.obj M ◁ (Functor.OplaxMonoidal.δ F M X ≫ act.smul) ≫
                    Functor.LaxMonoidal.μ F M X ≫
                      Functor.OplaxMonoidal.δ F M X ≫ act.smul := by
                rw [Functor.Monoidal.map_whiskerLeft]
                simp only [smul, F.map_preimage]
                cat_disch
            _ = (α_ (F.obj M) (F.obj M) (F.obj X)).hom ≫
                  F.obj M ◁ act.smul ≫ act.smul := by
                rw [MonoidalCategory.whiskerLeft_comp]
                repeat' rw [Category.assoc]
                rw [Functor.Monoidal.μ_δ_assoc, Functor.Monoidal.whiskerLeft_μ_δ_assoc,
                  Functor.Monoidal.μ_δ_assoc]

/-- The coefficients of a Laurent coaction form an integer grading. -/
@[ega "II 8.3.9" "special case"]
private noncomputable def gradingOfLaurentCoaction
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (φ : A →ₐ[R] TensorProduct R (LaurentPolynomial R) A)
    (hunit : (Algebra.TensorProduct.map
      (Bialgebra.counitAlgHom R (LaurentPolynomial R)) (AlgHom.id R A)).comp φ =
      (Algebra.TensorProduct.lid R A).symm.toAlgHom)
    (hmul : (Algebra.TensorProduct.map
      (Bialgebra.comulAlgHom R (LaurentPolynomial R)) (AlgHom.id R A)).comp φ =
      (Algebra.TensorProduct.assoc R R R (LaurentPolynomial R)
        (LaurentPolynomial R) A).symm.toAlgHom.comp
        ((Algebra.TensorProduct.map (AlgHom.id R (LaurentPolynomial R)) φ).comp φ)) :
    Σ (𝒜 : ℤ → AddSubgroup A),
      {_graded : GradedRing 𝒜 // ∀ n a, a ∈ 𝒜 n → φ a = LaurentPolynomial.T n ⊗ₜ[R] a} := by
  classical
  let mulLeft := (Algebra.TensorProduct.map
    (Bialgebra.comulAlgHom R (LaurentPolynomial R)) (AlgHom.id R A)).comp φ
  let mulRight := (Algebra.TensorProduct.assoc R R R (LaurentPolynomial R)
    (LaurentPolynomial R) A).symm.toAlgHom.comp
      ((Algebra.TensorProduct.map (AlgHom.id R (LaurentPolynomial R)) φ).comp φ)
  let coefs : A →ₗ[R] ℤ →₀ A := {
    toFun := fun a => (TensorProduct.finsuppScalarLeft R A ℤ)
      ((AddMonoidAlgebra.coeffLinearEquiv R).rTensor A (φ a))
    map_add' := fun a b => by simp
    map_smul' := by
      intro z a
      change (TensorProduct.finsuppScalarLeft R A ℤ)
          ((AddMonoidAlgebra.coeffLinearEquiv R).rTensor A (φ (z • a))) = _
      rw [map_smul φ z a, map_smul]
      exact map_smul (TensorProduct.finsuppScalarLeft R A ℤ) z
        ((AddMonoidAlgebra.coeffLinearEquiv R).rTensor A (φ a)) }
  let coeffEquiv : TensorProduct R (LaurentPolynomial R) A ≃ₗ[R] ℤ →₀ A :=
    ((AddMonoidAlgebra.coeffLinearEquiv R).rTensor A).trans
      (TensorProduct.finsuppScalarLeft R A ℤ)
  have hcoeffEquiv_tmul (n : ℤ) (a : A) :
      coeffEquiv (LaurentPolynomial.T n ⊗ₜ[R] a) = Finsupp.single n a := by
    change TensorProduct.finsuppScalarLeft R A ℤ
      ((AddMonoidAlgebra.coeffLinearEquiv R) (LaurentPolynomial.T n) ⊗ₜ[R] a) = _
    rw [show (AddMonoidAlgebra.coeffLinearEquiv R) (LaurentPolynomial.T n) =
        Finsupp.single n (1 : R) by rfl, TensorProduct.finsuppScalarLeft_apply_tmul]
    simp
  have hcoeffEquiv_symm (n : ℤ) (a : A) :
      coeffEquiv.symm (Finsupp.single n a) = LaurentPolynomial.T n ⊗ₜ[R] a := by
    apply coeffEquiv.injective
    rw [LinearEquiv.apply_symm_apply, hcoeffEquiv_tmul]
  have hcoeffEquiv_sum (f : ℤ →₀ A) :
      coeffEquiv.symm f = f.sum fun n a => LaurentPolynomial.T n ⊗ₜ[R] a := by
    conv_lhs => rw [← Finsupp.sum_single f]
    rw [map_finsuppSum]
    simp_rw [hcoeffEquiv_symm]
  have hphi_repr (a : A) :
      φ a = (coefs a).sum fun n b => LaurentPolynomial.T n ⊗ₜ[R] b := by
    simpa only [show coeffEquiv (φ a) = coefs a by rfl, hcoeffEquiv_sum] using
      (coeffEquiv.symm_apply_apply (φ a)).symm
  have hmulLeft_repr (a : A) :
      mulLeft a = (coefs a).sum fun n b =>
        (LaurentPolynomial.T n ⊗ₜ[R] LaurentPolynomial.T n) ⊗ₜ[R] b := by
    change (Algebra.TensorProduct.map (Bialgebra.comulAlgHom R (LaurentPolynomial R))
      (AlgHom.id R A)) (φ a) = _
    rw [hphi_repr, map_finsuppSum]
    congr 1
    funext n b
    simp [Bialgebra.comulAlgHom]
  have hmulRight_repr (a : A) :
      mulRight a = (coefs a).sum fun n b =>
        (coefs b).sum fun m c =>
          (LaurentPolynomial.T n ⊗ₜ[R] LaurentPolynomial.T m) ⊗ₜ[R] c := by
    change (Algebra.TensorProduct.assoc R R R (LaurentPolynomial R)
        (LaurentPolynomial R) A).symm.toAlgHom
        ((Algebra.TensorProduct.map (AlgHom.id R (LaurentPolynomial R)) φ) (φ a)) = _
    rw [hphi_repr a]
    let step : TensorProduct R (LaurentPolynomial R) A →+
        TensorProduct R (TensorProduct R (LaurentPolynomial R) (LaurentPolynomial R)) A :=
      ((Algebra.TensorProduct.assoc R R R (LaurentPolynomial R)
        (LaurentPolynomial R) A).symm.toAlgHom.toRingHom.toAddMonoidHom).comp
        ((Algebra.TensorProduct.map (AlgHom.id R (LaurentPolynomial R))
          φ).toRingHom.toAddMonoidHom)
    change step ((coefs a).sum fun n b => LaurentPolynomial.T n ⊗ₜ[R] b) = _
    rw [map_finsuppSum step]
    simp only [Finsupp.sum]
    refine Finset.sum_congr rfl ?_
    intro n hn
    change (Algebra.TensorProduct.assoc R R R (LaurentPolynomial R)
      (LaurentPolynomial R) A).symm.toAlgHom
      ((Algebra.TensorProduct.map (AlgHom.id R (LaurentPolynomial R)) φ)
        (LaurentPolynomial.T n ⊗ₜ[R] coefs a n)) = _
    rw [Algebra.TensorProduct.map_tmul, hphi_repr (coefs a n)]
    let lift : TensorProduct R (LaurentPolynomial R) A →+
        TensorProduct R (TensorProduct R (LaurentPolynomial R)
          (LaurentPolynomial R)) A := {
      toFun := fun z => (Algebra.TensorProduct.assoc R R R (LaurentPolynomial R)
        (LaurentPolynomial R) A).symm (LaurentPolynomial.T n ⊗ₜ[R] z)
      map_zero' := by simp
      map_add' := fun z w => by simp [TensorProduct.tmul_add] }
    change lift ((coefs (coefs a n)).sum fun m c => LaurentPolynomial.T m ⊗ₜ[R] c) = _
    rw [map_finsuppSum lift]
    simp only [Finsupp.sum]
    refine Finset.sum_congr rfl ?_
    intro m hm
    simp [lift]
  let doubleCoeff :
      TensorProduct R (TensorProduct R (LaurentPolynomial R) (LaurentPolynomial R)) A
        ≃ₗ[R] (ℤ × ℤ) →₀ A :=
    (((AddMonoidAlgebra.tensorEquiv R).rTensor A).trans
      ((AddMonoidAlgebra.coeffLinearEquiv R).rTensor A)).trans
      (TensorProduct.finsuppScalarLeft R A (ℤ × ℤ))
  let doubleCoeffAdd :
      TensorProduct R (TensorProduct R (LaurentPolynomial R) (LaurentPolynomial R)) A →+
        (ℤ × ℤ) →₀ A := doubleCoeff.toAddMonoidHom
  have hdoubleCoeff_tmul (i j : ℤ) (b : A) :
      doubleCoeff ((LaurentPolynomial.T i ⊗ₜ[R] LaurentPolynomial.T j) ⊗ₜ[R] b) =
        Finsupp.single (i, j) b := by
    change TensorProduct.finsuppScalarLeft R A (ℤ × ℤ)
      ((AddMonoidAlgebra.coeffLinearEquiv R)
        ((AddMonoidAlgebra.tensorEquiv R)
          (LaurentPolynomial.T i ⊗ₜ[R] LaurentPolynomial.T j)) ⊗ₜ[R] b) = _
    rw [show LaurentPolynomial.T i = AddMonoidAlgebra.single i (1 : R) by rfl,
      show LaurentPolynomial.T j = AddMonoidAlgebra.single j (1 : R) by rfl,
      AddMonoidAlgebra.tensorEquiv_single_tmul_single,
      AddMonoidAlgebra.coeffLinearEquiv_apply]
    change TensorProduct.finsuppScalarLeft R A (ℤ × ℤ)
      ((Finsupp.single (i, j) (1 * 1 : R)) ⊗ₜ[R] b) = _
    rw [TensorProduct.finsuppScalarLeft_apply_tmul]
    simp
  have hmulLeft_coeff (a : A) :
      doubleCoeff (mulLeft a) =
        Finsupp.mapDomain (fun n : ℤ => (n, n)) (coefs a) := by
    rw [hmulLeft_repr]
    change doubleCoeffAdd ((coefs a).sum fun n b =>
      (LaurentPolynomial.T n ⊗ₜ[R] LaurentPolynomial.T n) ⊗ₜ[R] b) = _
    rw [map_finsuppSum doubleCoeffAdd]
    change ((coefs a).sum fun n b =>
      doubleCoeff ((LaurentPolynomial.T n ⊗ₜ[R] LaurentPolynomial.T n) ⊗ₜ[R] b)) = _
    simp_rw [hdoubleCoeff_tmul]
    rfl
  have hmulRight_coeff (a : A) (i j : ℤ) :
      doubleCoeff (mulRight a) (i, j) = coefs (coefs a i) j := by
    rw [hmulRight_repr]
    change doubleCoeffAdd ((coefs a).sum fun n b =>
      (coefs b).sum fun m c =>
        (LaurentPolynomial.T n ⊗ₜ[R] LaurentPolynomial.T m) ⊗ₜ[R] c) (i, j) = _
    simp only [map_finsuppSum doubleCoeffAdd]
    change ((coefs a).sum fun n b => (coefs b).sum fun m c =>
      doubleCoeff ((LaurentPolynomial.T n ⊗ₜ[R] LaurentPolynomial.T m) ⊗ₜ[R] c)) (i,j) = _
    simp_rw [hdoubleCoeff_tmul]
    exact sum_sum_single_apply coefs.toAddMonoidHom a i j
  let 𝒜 : ℤ → AddSubgroup A := fun n =>
    { carrier := {a | coefs a = Finsupp.single n a}
      zero_mem' := by simp [coefs]
      neg_mem' := by
        intro a ha
        simp only [Set.mem_ofPred_eq] at ha ⊢
        rw [map_neg, ha, Finsupp.single_neg]
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        rw [map_add, ha, hb, Finsupp.single_add] }
  have hpure (a : A) (n : ℤ) : coefs a n ∈ 𝒜 n := by
    change coefs (coefs a n) = Finsupp.single n (coefs a n)
    ext m
    rw [← hmulRight_coeff, ← (show mulLeft = mulRight from hmul), hmulLeft_coeff]
    exact mapDomain_diag_apply (coefs a) n m
  have hsum (a : A) : (coefs a).sum (fun _ b => b) = a := by
    have h := congrArg (fun f => (Algebra.TensorProduct.lid R A) (f a)) hunit
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply] at h
    rw [hphi_repr] at h
    simpa [map_finsuppSum] using h
  have hhomogeneous (n : ℤ) (a : A) :
      a ∈ 𝒜 n ↔ φ a = LaurentPolynomial.T n ⊗ₜ[R] a := by
    change coefs a = Finsupp.single n a ↔ _
    rw [← hcoeffEquiv_tmul]
    exact coeffEquiv.injective.eq_iff
  let : SetLike.GradedMonoid 𝒜 :=
    { one_mem := by
        apply (hhomogeneous 0 1).mpr
        simp [Algebra.TensorProduct.one_def]
      mul_mem := by
        intro i j a b ha hb
        apply (hhomogeneous (i+j) (a*b)).mpr
        rw [map_mul, (hhomogeneous i a).mp ha, (hhomogeneous j b).mp hb,
          Algebra.TensorProduct.tmul_mul_tmul, ← LaurentPolynomial.T_add] }
  let : DirectSum.Decomposition 𝒜 :=
    decompositionOfCoefficients coefs.toAddMonoidHom 𝒜 hpure (fun _ _ ha => ha) hsum
  exact ⟨𝒜, ⟨{}, fun n a ha => (hhomogeneous n a).mp ha⟩⟩

/-- **Stacks Project, Tag 0EKK.** An action of the multiplicative group scheme on
an affine scheme determines an integer grading of its coordinate ring, and is
the action associated to that grading. -/
@[stacks 0EKK, ega "II 8.3.9" "special case"]
noncomputable def gradingOfGmAction (X : Scheme.{u}) [IsAffine X]
    [X.Over (Spec (.of (ULift.{u} ℤ)))]
    (action : ModObj
      (multiplicativeGroupULift.asOver (Spec (.of (ULift.{u} ℤ))))
      (X.asOver (Spec (.of (ULift.{u} ℤ))))) :
    Σ (𝒜 : ℤ → AddSubgroup Γ(X, ⊤)),
      {graded : GradedRing 𝒜 //
        (letI := action
         letI : X.isoSpec.hom.IsOver (Spec (.of (ULift.{u} ℤ))) :=
           ⟨specULiftZIsTerminal.hom_ext _ _⟩
         letI : IsMonHom
             (Iso.refl (multiplicativeGroupULift.asOver (Spec (.of (ULift.{u} ℤ))))).hom :=
           ⟨by exact Category.comp_id _, by simp⟩
         ModObj.ofIso (Iso.refl (multiplicativeGroupULift.asOver (Spec (.of (ULift.{u} ℤ)))))
           (X.isoSpec.asOver (Spec (.of (ULift.{u} ℤ))))) =
          (letI := graded; (gradedGmAction 𝒜).action)} := Classical.choice <| by
  classical
  let R := ULift.{u} ℤ
  let A := Γ(X, ⊤)
  let F := algSpec (CommRingCat.of R)
  let : F.Full := algSpec.instFull
  let : F.Faithful := algSpec.instFaithful
  let : F.Braided := AlgebraicGeometry.braidedAlgSpec
  let : F.Monoidal := Functor.Braided.toMonoidal
  let Msrc : Mon ((CommAlgCat (CommRingCat.of R))ᵒᵖ) :=
    ⟨Opposite.op (CommAlgCat.of R (LaurentPolynomial R))⟩
  let Xsrc := Opposite.op (CommAlgCat.of R A)
  let M' : MonObj (F.obj Msrc.X) := by
    change MonObj (multiplicativeGroupULift.asOver (Spec (.of R)))
    infer_instance
  have hone : Functor.LaxMonoidal.ε F ≫ F.map (MonObj.one (X := Msrc.X)) = M'.one := by
    apply Over.OverMorphism.ext
    rfl
  have hmul : Functor.LaxMonoidal.μ F Msrc.X Msrc.X ≫
      F.map (MonObj.mul (X := Msrc.X)) = M'.mul := by
    apply Over.OverMorphism.ext
    rfl
  let : ModObj (multiplicativeGroupULift.asOver (Spec (.of R)))
      (X.asOver (Spec (.of R))) := action
  let : X.isoSpec.hom.IsOver (Spec (.of R)) :=
    ⟨specULiftZIsTerminal.hom_ext _ _⟩
  let : IsMonHom (Iso.refl (multiplicativeGroupULift.asOver (Spec (.of R)))).hom :=
    ⟨by exact Category.comp_id _, by simp⟩
  let actOver := ModObj.ofIso
    (Iso.refl (multiplicativeGroupULift.asOver (Spec (.of R))))
    (X.isoSpec.asOver (Spec (.of R)))
  let actAlg : ModObj Msrc.X Xsrc := pullModObj F Msrc.X Xsrc M' hone hmul actOver
  let φ : A →ₐ[R] TensorProduct R (LaurentPolynomial R) A := actAlg.smul.unop.hom
  have hu' := congrArg (fun f => f.unop.hom) actAlg.one_smul
  have hm' := congrArg (fun f => f.unop.hom) actAlg.mul_smul
  obtain ⟨𝒜, graded, hφ⟩ := gradingOfLaurentCoaction φ
    (by exact hu') (by exact hm')
  let := graded
  refine ⟨⟨𝒜, graded, ?_⟩⟩
  have heq : φ.toRingHom =
      (Algebra.TensorProduct.comm R A (LaurentPolynomial R)).toRingEquiv.toRingHom.comp
        ((gradedActionTensorMap A).comp (gradedGmAction 𝒜).μ) := by
    apply ringHom_eq_of_homogeneous 𝒜
    intro n a
    change φ a = _
    rw [hφ n a a.property]
    simp [(gradedGmAction 𝒜).μ_homogeneous n a a.property, R]
  apply ModObj.ext
  apply Over.OverMorphism.ext
  change actOver.smul.left = (gradedGmAction 𝒜).action.smul.left
  rw [(gradedGmAction 𝒜).action_eq_spec_map, ← heq]
  have hf : Functor.LaxMonoidal.μ F Msrc.X Xsrc ≫ F.map actAlg.smul =
      actOver.smul := by
    rw [show F.map actAlg.smul =
      Functor.OplaxMonoidal.δ F Msrc.X Xsrc ≫ actOver.smul from F.map_preimage _]
    exact Functor.Monoidal.μ_δ_assoc F Msrc.X Xsrc actOver.smul
  exact (congrArg (fun f => f.left) hf).symm

end AlgebraicGeometry

end
