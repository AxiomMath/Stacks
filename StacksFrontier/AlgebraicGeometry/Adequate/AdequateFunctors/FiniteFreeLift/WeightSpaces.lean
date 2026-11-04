module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.FiniteFreeLift.UniversalSolutionAlgebra

/-!
# Weight spaces of module-valued functors at Laurent polynomial algebras

This file is the second part of
`StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.FiniteFreeLift`. It describes the
image of `B ⊗[A] M` in the graded weight spaces coming from the graded Laurent map of a
symmetric algebra, and shows that an element of weight one is a tensor of degree-one elements.

## References

* [Stacks Project, Tag 06V0](https://stacks.math.columbia.edu/tag/06V0)
-/

@[expose] public section

open CategoryTheory
universe w v u z u₁ v₁

namespace AdequateFunctor


open scoped DirectSum
open TensorProduct

/-- Extension of scalars on `B ⊗[A] M` along a map of algebras, for a module and algebras all
in the ring's own universe. -/
noncomputable def smallModuleExtensionMap (A : Type u) [CommRing A]
    (M : Type u) [AddCommGroup M] [Module A M]
    {B C : CommAlgCat.{u} A} (f : B ⟶ C) :
    ModuleCat.of B (TensorProduct A (B : Type u) M) ⟶
      (ModuleCat.restrictScalars f.hom.toRingHom).obj
        (ModuleCat.of C (TensorProduct A (C : Type u) M)) := by
  refine ModuleCat.ofHom (X := ModuleCat.of B (TensorProduct A (B : Type u) M))
    (Y := (ModuleCat.restrictScalars f.hom.toRingHom).obj
      (ModuleCat.of C (TensorProduct A (C : Type u) M)))
    { toFun := TensorProduct.map f.hom.toLinearMap LinearMap.id
      map_add' := map_add _
      map_smul' := ?_ }
  intro b x
  induction x using TensorProduct.induction_on with
  | zero => change (0 : TensorProduct A (C : Type u) M) = 0; rfl
  | tmul c m =>
    rw [TensorProduct.smul_tmul', TensorProduct.map_tmul]
    change f.hom (b * c) ⊗ₜ[A] m = (f.hom b * f.hom c) ⊗ₜ[A] m
    rw [map_mul]
  | add x y hx hy =>
    rw [smul_add, map_add, hx, hy, map_add]
    exact (smul_add b _ _).symm

/-- Extension of scalars along the identity is the canonical restriction identification. -/
private lemma smallModuleExtensionMap_id (A : Type u) [CommRing A]
    (M : Type u) [AddCommGroup M] [Module A M] (B : CommAlgCat.{u} A) :
    smallModuleExtensionMap A M (𝟙 B) =
      (ModuleCat.restrictScalarsId' (𝟙 B : B ⟶ B).hom.toRingHom
        (congrArg CommRingCat.Hom.hom
          ((forget₂ (CommAlgCat.{u} A) CommRingCat.{u}).map_id B))).inv.app _ := by
  ext x
  induction x using TensorProduct.induction_on with
  | zero => change (0 : TensorProduct A (B : Type u) M) = 0; rfl
  | tmul b m => change b ⊗ₜ[A] m = b ⊗ₜ[A] m; rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The module-valued functor `B ↦ B ⊗[A] M` for a module in the ring's own universe. -/
noncomputable def smallModuleExtension (A : Type u) [CommRing A]
    (M : Type u) [AddCommGroup M] [Module A M] : Laurent.ModuleValuedFunctor A where
  obj X := ModuleCat.of X.unop.unop (TensorProduct A (X.unop.unop : Type u) M)
  map {X Y} f := smallModuleExtensionMap A M f.unop.unop
  map_id X := by
    apply smallModuleExtensionMap_id
  map_comp f g := by
    ext x
    induction x using TensorProduct.induction_on with
    | zero => change 0 = 0; rfl
    | tmul b m =>
      change g.unop.unop.hom (f.unop.unop.hom b) ⊗ₜ[A] m =
        g.unop.unop.hom (f.unop.unop.hom b) ⊗ₜ[A] m
      rfl
    | add x y hx hy => simp only [map_add, hx, hy]

/-- Extension of scalars sends a coordinate tuple to the coordinate tuple of its images. -/
private lemma moduleExtensionMap_tupleTensor {n : ℕ} (A B C : Type u)
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    (f : B →ₐ[A] C) (x : Fin n → B) :
    smallModuleExtensionMap A (Fin n → A) (CommAlgCat.ofHom f) (tupleTensor A B x) =
      tupleTensor A C (fun i => f (x i)) := by
  show (TensorProduct.map f.toLinearMap LinearMap.id)
      (∑ i, x i ⊗ₜ[A] Pi.single i 1) = _
  simp [tupleTensor]

/-- Scaling every entry of a tuple scales the corresponding tensor. -/
private lemma tupleTensor_smul {n : ℕ} (A C : Type u)
    [CommRing A] [CommRing C] [Algebra A C] (t : C) (x : Fin n → C) :
    tupleTensor A C (fun i => t * x i) = t • tupleTensor A C x := by
  simp [tupleTensor, Finset.smul_sum, TensorProduct.smul_tmul']

/-- On a homogeneous element of degree `d` of the symmetric algebra the graded Laurent map
multiplies by `T ^ d`. -/
lemma gradedLaurentMap_symmetricPower_mem (A V : Type u) [CommRing A]
    [AddCommGroup V] [Module A V] (d : ℕ) (x : SymmetricAlgebra A V)
    (hx : x ∈ symmetricPower A V d) :
    Laurent.gradedLaurentMap A (SymmetricAlgebra A V) (symmetricPower A V) x =
      LaurentPolynomial.C x * LaurentPolynomial.T (d : ℤ) := by
  show (DirectSum.liftRingHom _) (DirectSum.decompose (symmetricPower A V) x) = _
  rw [DirectSum.decompose_of_mem (symmetricPower A V) hx]
  simp [DirectSum.liftRingHom_apply]

/-- The image of `B ⊗[A] M` in the graded weight space of degree `d` consists of the
homogeneous elements of that degree. -/
private lemma moduleExtension_range_weightSpace (A B M : Type u)
    [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M]
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜]
    (d : ℕ)
    (hg : ∀ x, x ∈ 𝒜 d →
      Laurent.gradedLaurentMap A B 𝒜 x =
        LaurentPolynomial.C x * LaurentPolynomial.T (d : ℤ))
    (z : TensorProduct A B M)
    (hz : z ∈ LinearMap.range ((𝒜 d).subtype.rTensor M)) :
    z ∈ Laurent.weightSpace A B (smallModuleExtension A M) 𝒜 (d : ℤ) := by
  obtain ⟨w, rfl⟩ := hz
  show (LaurentPolynomial.T (d : ℤ) : LaurentPolynomial B) •
      (smallModuleExtension A M).map
        ((CommAlgCat.ofHom (Laurent.constantLaurentMap A B)).op.op)
        ((𝒜 d).subtype.rTensor M w) =
    (smallModuleExtension A M).map
      ((CommAlgCat.ofHom (Laurent.gradedLaurentMap A B 𝒜)).op.op)
      ((𝒜 d).subtype.rTensor M w)
  induction w using TensorProduct.induction_on with
  | zero =>
      show (LaurentPolynomial.T (d : ℤ) : LaurentPolynomial B) •
          (TensorProduct.map (Laurent.constantLaurentMap A B).toLinearMap LinearMap.id) 0 =
        (TensorProduct.map (Laurent.gradedLaurentMap A B 𝒜).toLinearMap LinearMap.id) 0
      simp
  | tmul x m =>
      show (LaurentPolynomial.T (d : ℤ) : LaurentPolynomial B) •
          (TensorProduct.map (Laurent.constantLaurentMap A B).toLinearMap LinearMap.id)
            ((x : B) ⊗ₜ[A] m) =
        (TensorProduct.map (Laurent.gradedLaurentMap A B 𝒜).toLinearMap LinearMap.id)
          ((x : B) ⊗ₜ[A] m)
      rw [TensorProduct.map_tmul, TensorProduct.map_tmul]
      show (LaurentPolynomial.T (d : ℤ) : LaurentPolynomial B) •
          (Laurent.constantLaurentMap A B (x : B) ⊗ₜ[A] m) =
        Laurent.gradedLaurentMap A B 𝒜 (x : B) ⊗ₜ[A] m
      rw [hg x.val x.property]
      rw [TensorProduct.smul_tmul']
      rw [mul_comm]
      rw [smul_eq_mul]
      show (LaurentPolynomial.T (d : ℤ) * LaurentPolynomial.C (x : B)) ⊗ₜ[A] m =
        (LaurentPolynomial.T (d : ℤ) * LaurentPolynomial.C (x : B)) ⊗ₜ[A] m
      rfl
  | add w₁ w₂ h₁ h₂ =>
      have hr : (𝒜 d).subtype.rTensor M (w₁ + w₂) =
          (𝒜 d).subtype.rTensor M w₁ + (𝒜 d).subtype.rTensor M w₂ := map_add _ _ _
      rw [hr]
      show (LaurentPolynomial.T (d : ℤ) : LaurentPolynomial B) •
          (TensorProduct.map (Laurent.constantLaurentMap A B).toLinearMap LinearMap.id)
            ((𝒜 d).subtype.rTensor M w₁ + (𝒜 d).subtype.rTensor M w₂) =
        (TensorProduct.map (Laurent.gradedLaurentMap A B 𝒜).toLinearMap LinearMap.id)
          ((𝒜 d).subtype.rTensor M w₁ + (𝒜 d).subtype.rTensor M w₂)
      have h₁' : (LaurentPolynomial.T (d : ℤ) : LaurentPolynomial B) •
          (TensorProduct.map (Laurent.constantLaurentMap A B).toLinearMap LinearMap.id)
            ((𝒜 d).subtype.rTensor M w₁) =
        (TensorProduct.map (Laurent.gradedLaurentMap A B 𝒜).toLinearMap LinearMap.id)
          ((𝒜 d).subtype.rTensor M w₁) := h₁
      have h₂' : (LaurentPolynomial.T (d : ℤ) : LaurentPolynomial B) •
          (TensorProduct.map (Laurent.constantLaurentMap A B).toLinearMap LinearMap.id)
            ((𝒜 d).subtype.rTensor M w₂) =
        (TensorProduct.map (Laurent.gradedLaurentMap A B 𝒜).toLinearMap LinearMap.id)
          ((𝒜 d).subtype.rTensor M w₂) := h₂
      rw [map_add, map_add, smul_add, h₁', h₂']

/-- The weight-space description of the image of `B ⊗[A] M`, with independent universes. -/
public lemma moduleExtension_range_weightSpace_large (A : Type u) (B : Type v)
    (M : Type z) [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M]
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] (d : ℕ)
    (hg : ∀ x, x ∈ 𝒜 d →
      gradedLaurentMapLarge A B 𝒜 x =
        LaurentPolynomial.C x * LaurentPolynomial.T (d : ℤ))
    (y : TensorProduct A B M)
    (hy : y ∈ LinearMap.range ((𝒜 d).subtype.rTensor M)) :
    (LaurentPolynomial.T (d : ℤ) : LaurentPolynomial B) •
        (TensorProduct.map (constantLaurentMapLarge A B).toLinearMap LinearMap.id) y =
      (TensorProduct.map (gradedLaurentMapLarge A B 𝒜).toLinearMap LinearMap.id) y := by
  obtain ⟨w, rfl⟩ := hy
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul x m =>
      show (LaurentPolynomial.T (d : ℤ) : LaurentPolynomial B) •
          (constantLaurentMapLarge A B x.1 ⊗ₜ[A] m) =
        gradedLaurentMapLarge A B 𝒜 x.1 ⊗ₜ[A] m
      rw [hg x.1 x.2, TensorProduct.smul_tmul', mul_comm, smul_eq_mul]
      rfl
  | add w w' hw hw' =>
      simp only [map_add, smul_add]
      rw [hw, hw']

/-- A decomposed element is the sum of a finitely supported family indexed by `ℤ`, whose value
at `d : ℕ` is its degree-`d` component and which vanishes at negative integers. -/
private lemma exists_finsupp_decompose_eq_sum {A N : Type*} [CommRing A] [AddCommGroup N]
    [Module A N] (E : ℕ → Submodule A N) [DirectSum.Decomposition E] (y : N) :
    ∃ w : ℤ →₀ N, (∀ d : ℕ, w (d : ℤ) = (DirectSum.decompose E y d : N)) ∧
      (∀ k : ℤ, (∀ d : ℕ, (d : ℤ) ≠ k) → w k = 0) ∧ w.sum (fun _ z => z) = y := by
  classical
  let G : (⨁ d, E d) →+ (ℤ →₀ N) := DirectSum.toAddMonoid
    (fun d : ℕ => (Finsupp.singleAddHom (d : ℤ)).comp (E d).subtype.toAddMonoidHom)
  let S : (ℤ →₀ N) →ₗ[A] N := Finsupp.lsum A (fun _ : ℤ => LinearMap.id)
  have hGof (d : ℕ) (x : E d) :
      G (DirectSum.of (fun d : ℕ => E d) d x) = Finsupp.single (d : ℤ) (x : N) := by
    show DirectSum.toAddMonoid
      (fun e : ℕ => (Finsupp.singleAddHom (e : ℤ)).comp
        (E e).subtype.toAddMonoidHom)
      (DirectSum.of (fun d : ℕ => E d) d x) = _
    rw [DirectSum.toAddMonoid_of]
    rfl
  have hGval (z : ⨁ d, E d) (d : ℕ) : G z (d : ℤ) = (z d : N) := by
    induction z using DirectSum.induction_on with
    | zero => simp [G]
    | of e x =>
        rw [hGof]
        by_cases h : e = d
        · subst d
          simp []
        · have hd : d ≠ e := Ne.symm h
          simp [DirectSum.of_eq_of_ne, hd]
    | add z z' hz hz' => simp [G, hz, hz']
  have hGneg (z : ⨁ d, E d) (k : ℤ) (hk : ∀ d : ℕ, (d : ℤ) ≠ k) : G z k = 0 := by
    induction z using DirectSum.induction_on with
    | zero => simp [G]
    | of d x => rw [hGof]; simp [hk d]
    | add z z' hz hz' => simp [G, hz, hz']
  have hcomp (z : ⨁ d, E d) : S (G z) = DirectSum.coeAddMonoidHom E z := by
    induction z using DirectSum.induction_on with
    | zero => simp [G, S]
    | of d x => rw [hGof]; simp [S]
    | add z z' hz hz' => simp only [map_add, hz, hz']
  refine ⟨G (DirectSum.decompose E y), fun d => hGval _ _,
    fun k hk => hGneg _ _ hk, ?_⟩
  show S (G (DirectSum.decompose E y)) = y
  rw [hcomp]
  exact DirectSum.Decomposition.left_inv (ℳ := E) y

/-- An element of `B ⊗[A] M` of weight one is a tensor of degree-one elements. -/
lemma moduleExtension_weightOne_mem_degreeOne (A B M : Type u)
    [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M]
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜]
    (hg : ∀ d x, x ∈ 𝒜 d →
      Laurent.gradedLaurentMap A B 𝒜 x =
        LaurentPolynomial.C x * LaurentPolynomial.T (d : ℤ))
    (hF : Laurent.PreservesFlatBaseChange A (smallModuleExtension A M))
    (y : TensorProduct A B M)
    (hy : y ∈ Laurent.weightSpace A B (smallModuleExtension A M) 𝒜 1) :
    y ∈ DirectSum.decomposeTensor 𝒜 M 1 := by
  classical
  let E : ℕ → Submodule A (TensorProduct A B M) := DirectSum.decomposeTensor 𝒜 M
  let : DirectSum.Decomposition E := DirectSum.tensorDecomposition 𝒜 M
  obtain ⟨w, hval, hneg, hsum⟩ := exists_finsupp_decompose_eq_sum E y
  have hw : ∀ k, w k ∈ Laurent.weightSpace A B (smallModuleExtension A M) 𝒜 k := by
    intro k
    by_cases hk : ∃ d : ℕ, (d : ℤ) = k
    · obtain ⟨d, rfl⟩ := hk
      rw [hval]
      apply moduleExtension_range_weightSpace A B M 𝒜 d (hg d)
      rw [← DirectSum.decomposeTensor_apply]
      exact (DirectSum.decompose E y d).property
    · rw [hneg k fun d hd => hk ⟨d, hd⟩]
      show (LaurentPolynomial.T k : LaurentPolynomial B) •
          (0 : TensorProduct A (LaurentPolynomial B) M) = 0
      simp
  let w₁ : ℤ →₀ (TensorProduct A B M) := Finsupp.single 1 y
  have hw₁ : ∀ k, w₁ k ∈ Laurent.weightSpace A B (smallModuleExtension A M) 𝒜 k := by
    intro k
    by_cases hk : k = 1
    · subst k
      simpa [w₁] using hy
    · have hzero : w₁ k = 0 := by simp [w₁, hk]
      rw [hzero]
      show (LaurentPolynomial.T k : LaurentPolynomial B) •
          (0 : TensorProduct A (LaurentPolynomial B) M) = 0
      simp
  have hsum₁ : w₁.sum (fun _ z => z) = y := by simp [w₁]
  obtain ⟨_, _, huniq⟩ :=
    Laurent.existsUnique_finsupp_weightSpace_eq A B (smallModuleExtension A M) hF 𝒜 y
  have heq : w = w₁ := (huniq w ⟨hw, hsum⟩).trans (huniq w₁ ⟨hw₁, hsum₁⟩).symm
  have hdecomp : (DirectSum.decompose E y 1 : TensorProduct A B M) = y :=
    ((hval 1).symm.trans (congrArg (fun z : ℤ →₀ TensorProduct A B M => z 1) heq)).trans
      (by simp [w₁])
  rw [← hdecomp]
  exact (DirectSum.decompose E y 1).property

/-- The weight-one description of elements of `B ⊗[A] M`, with independent universes. -/
public lemma moduleExtension_weightOne_mem_degreeOne_large
    (A : Type u) (B : Type v) (M : Type z)
    [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M]
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜]
    (hg : ∀ d x, x ∈ 𝒜 d →
      gradedLaurentMapLarge A B 𝒜 x =
        LaurentPolynomial.C x * LaurentPolynomial.T (d : ℤ))
    (y : TensorProduct A B M)
    (hy : (LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial B) •
        (TensorProduct.map (constantLaurentMapLarge A B).toLinearMap LinearMap.id) y =
      (TensorProduct.map (gradedLaurentMapLarge A B 𝒜).toLinearMap LinearMap.id) y) :
    y ∈ DirectSum.decomposeTensor 𝒜 M 1 := by
  classical
  let E : ℕ → Submodule A (TensorProduct A B M) := DirectSum.decomposeTensor 𝒜 M
  let : DirectSum.Decomposition E := DirectSum.tensorDecomposition 𝒜 M
  obtain ⟨w, hval, hneg, hsum⟩ := exists_finsupp_decompose_eq_sum E y
  have hw : ∀ k, (LaurentPolynomial.T k : LaurentPolynomial B) •
      (TensorProduct.map (constantLaurentMapLarge A B).toLinearMap LinearMap.id (w k)) =
      (TensorProduct.map (gradedLaurentMapLarge A B 𝒜).toLinearMap LinearMap.id (w k)) := by
    intro k
    by_cases hk : ∃ d : ℕ, (d : ℤ) = k
    · obtain ⟨d, rfl⟩ := hk
      rw [hval]
      apply moduleExtension_range_weightSpace_large A B M 𝒜 d (hg d)
      rw [← DirectSum.decomposeTensor_apply]
      exact (DirectSum.decompose E y d).property
    · rw [hneg k fun d hd => hk ⟨d, hd⟩]
      simp
  let w₁ : ℤ →₀ (TensorProduct A B M) := Finsupp.single 1 y
  have hrepr : (TensorProduct.map (gradedLaurentMapLarge A B 𝒜).toLinearMap LinearMap.id) y =
      w.sum (fun k t => (LaurentPolynomial.T k : LaurentPolynomial B) •
        (TensorProduct.map (constantLaurentMapLarge A B).toLinearMap LinearMap.id) t) := by
    rw [← hsum]
    simp only [Finsupp.sum, map_sum]
    apply Finset.sum_congr rfl
    intro k hk
    exact (hw k).symm
  have hrepr₁ : (TensorProduct.map (gradedLaurentMapLarge A B 𝒜).toLinearMap LinearMap.id) y =
      w₁.sum (fun k t => (LaurentPolynomial.T k : LaurentPolynomial B) •
        (TensorProduct.map (constantLaurentMapLarge A B).toLinearMap LinearMap.id) t) := by
    rw [hy.symm]
    simp only [w₁]
    rw [Finsupp.sum_single_index]
    · simp
  have hweighted := hrepr.symm.trans hrepr₁
  have hcoeff (t : ℤ →₀ TensorProduct A B M) :
      laurentTensorCoefficientsLarge A B M
        (t.sum (fun k x => (LaurentPolynomial.T k : LaurentPolynomial B) •
          (TensorProduct.map (constantLaurentMapLarge A B).toLinearMap LinearMap.id) x)) = t := by
    classical
    ext k
    simp only [Finsupp.sum, map_sum, laurentTensorCoefficientsLarge_weightedConstant]
    exact congrArg (fun q : ℤ →₀ TensorProduct A B M => q k) (Finsupp.sum_single t)
  have hwEq : w = w₁ := by
    calc
      w = laurentTensorCoefficientsLarge A B M
          (w.sum (fun k x => (LaurentPolynomial.T k : LaurentPolynomial B) •
            (TensorProduct.map (constantLaurentMapLarge A B).toLinearMap LinearMap.id) x)) :=
        (hcoeff w).symm
      _ = laurentTensorCoefficientsLarge A B M
          (w₁.sum (fun k x => (LaurentPolynomial.T k : LaurentPolynomial B) •
            (TensorProduct.map (constantLaurentMapLarge A B).toLinearMap LinearMap.id) x)) :=
        congrArg (laurentTensorCoefficientsLarge A B M) hweighted
      _ = w₁ := hcoeff w₁
  have hdecomp : (DirectSum.decompose E y 1 : TensorProduct A B M) = y := by
    calc
      (DirectSum.decompose E y 1 : TensorProduct A B M) = w 1 := (hval 1).symm
      _ = w₁ 1 := congrArg (fun t : ℤ →₀ TensorProduct A B M => t 1) hwEq
      _ = y := by simp [w₁]
  rw [← hdecomp]
  exact (DirectSum.decompose E y 1).property

end AdequateFunctor
