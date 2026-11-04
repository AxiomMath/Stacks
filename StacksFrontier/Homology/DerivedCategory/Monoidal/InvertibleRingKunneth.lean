module

public import StacksFrontier.Homology.DerivedCategory.Monoidal.InvertibleRingSplitting

/-!
# The cohomology of a tensor inverse

Let `R` be a commutative ring and let `Z`, `Z'` be complexes of `R`-modules with zero
differentials. Then `Z ⊗ Z'` has zero differentials, so its cohomology is its underlying graded
module: `H^k(Z ⊗ Z') = ⨁_{p + q = k} Z^p ⊗ Z'^q`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe u

namespace DerivedCategory.Invertible

variable {R : Type u} [CommRing R]

/-- The total complex of two complexes with zero differentials has zero differentials. -/
public theorem mapBifunctor_d_eq_zero (F F' : ℤ → ModuleCat.{u} R) (i j : ℤ) :
    (HomologicalComplex.mapBifunctor (CochainComplex.zeroDifferentialComplex F)
      (CochainComplex.zeroDifferentialComplex F') (curriedTensor (ModuleCat.{u} R))
      (ComplexShape.up ℤ)).d i j = 0 := by
  refine HomologicalComplex.mapBifunctor.hom_ext fun p q h => ?_
  rw [Limits.comp_zero, HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
    HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
    HomologicalComplex.mapBifunctor.d₁_eq' _ _ _ _ (rfl : (ComplexShape.up ℤ).Rel p (p + 1)),
    HomologicalComplex.mapBifunctor.d₂_eq' _ _ _ _ _ (rfl : (ComplexShape.up ℤ).Rel q (q + 1))]
  simp only [CochainComplex.zeroDifferentialComplex, Functor.map_zero, NatTrans.app_zero,
    Limits.zero_comp]
  exact (congrArg₂ (· + ·) (smul_zero _) (smul_zero _)).trans (add_zero 0)

/-- The tensor product of two complexes with zero differentials has zero differentials. -/
public theorem tensorObj_d_eq_zero (F F' : ℤ → ModuleCat.{u} R) (i j : ℤ) :
    (CochainComplex.zeroDifferentialComplex F ⊗ CochainComplex.zeroDifferentialComplex F').d i j
      = 0 :=
  mapBifunctor_d_eq_zero F F' i j

/-- A complex with zero differentials is its own cohomology. -/
public def homologyIsoXOfDEqZero {C : Type*} [Category* C] [Abelian C] (K : CochainComplex C ℤ)
    (hd : ∀ i j, K.d i j = 0) (i : ℤ) : K.homology i ≅ K.X i :=
  (K.isoHomologyπ (i - 1) i (by simp) (hd _ _)).symm ≪≫ K.iCyclesIso i (i + 1) (by simp) (hd _ _)

/-- Multiplication by a scalar commutes with every linear map. -/
@[reassoc]
public theorem scalarNatTrans_naturality (r : R) {A B : ModuleCat.{u} R} (g : A ⟶ B) :
    (scalarNatTrans r).app A ≫ g = g ≫ (scalarNatTrans r).app B :=
  ((scalarNatTrans r).naturality g).symm

/-- Multiplication by a product of scalars on a tensor product is the tensor product of the
multiplications. -/
public theorem scalarNatTrans_app_tensorObj (a b : R) (A B : ModuleCat.{u} R) :
    (scalarNatTrans (a * b)).app (A ⊗ B) =
      (scalarNatTrans a).app A ⊗ₘ (scalarNatTrans b).app B := by
  refine ModuleCat.hom_ext (TensorProduct.ext' fun x y => ?_)
  show (a * b) • (x ⊗ₜ[R] y) = (a • x) ⊗ₜ[R] (b • y)
  rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', mul_comm, mul_smul,
    ← TensorProduct.smul_tmul']

/-- **Orthogonality of the idempotents of a complex and of its tensor inverse.** Let `Z` and `Z'`
be complexes with zero differentials, let `f_n` act on `Z^k` and `g_m` on `Z'^k` as the identity
for `k = n`, respectively `k = m`, and as zero otherwise, and suppose the degree-zero part of
`Z ⊗ Z'` is isomorphic to `R`. Then `f_n g_m = 0` unless `m = -n`. -/
public theorem mul_eq_zero_of_ne_neg (F F' : ℤ → ModuleCat.{u} R) (f g : ℤ → R)
    (hf : ∀ n k, (scalarNatTrans (f n)).app (F k) = if k = n then 𝟙 _ else 0)
    (hg : ∀ n k, (scalarNatTrans (g n)).app (F' k) = if k = n then 𝟙 _ else 0)
    (Φ : (HomologicalComplex.mapBifunctor (CochainComplex.zeroDifferentialComplex F)
      (CochainComplex.zeroDifferentialComplex F') (curriedTensor (ModuleCat.{u} R))
      (ComplexShape.up ℤ)).X 0 ≅ ModuleCat.of R R) {n m : ℤ} (hnm : m ≠ -n) :
    f n * g m = 0 := by
  have h0 : (scalarNatTrans (f n * g m)).app ((HomologicalComplex.mapBifunctor
      (CochainComplex.zeroDifferentialComplex F) (CochainComplex.zeroDifferentialComplex F')
      (curriedTensor (ModuleCat.{u} R)) (ComplexShape.up ℤ)).X 0) = 0 := by
    refine HomologicalComplex.mapBifunctor.hom_ext fun p q hpq => ?_
    rw [Limits.comp_zero, ← scalarNatTrans_naturality]
    have hpq' : p + q = 0 := hpq
    have : (scalarNatTrans (f n * g m)).app (F p ⊗ F' q) = 0 := by
      rw [scalarNatTrans_app_tensorObj, hf n p, hg m q]
      split_ifs with h1 h2
      · exact absurd (by omega) hnm
      · exact MonoidalPreadditive.tensor_zero _
      · exact MonoidalPreadditive.zero_tensor _
      · exact MonoidalPreadditive.zero_tensor _
    exact this ▸ Limits.zero_comp
  have h1 : (scalarNatTrans (f n * g m)).app (ModuleCat.of R R) = 0 := by
    rw [scalarNatTrans_app_eq_of_iso _ Φ.symm h0, Limits.zero_comp, Limits.comp_zero]
  have := congrArg (fun φ : ModuleCat.of R R ⟶ ModuleCat.of R R => φ.hom (1 : R)) h1
  rw [scalarNatTrans_app_apply] at this
  simpa using this

/-- The degree-zero part of the tensor product of two complexes with zero differentials which is
homotopy equivalent to the unit. -/
public def degreeZeroIsoOfHomotopyEquiv (F F' : ℤ → ModuleCat.{u} R)
    (h : HomotopyEquiv (CochainComplex.zeroDifferentialComplex F ⊗
      CochainComplex.zeroDifferentialComplex F') (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ))) :
    (HomologicalComplex.mapBifunctor (CochainComplex.zeroDifferentialComplex F)
      (CochainComplex.zeroDifferentialComplex F') (curriedTensor (ModuleCat.{u} R))
      (ComplexShape.up ℤ)).X 0 ≅ ModuleCat.of R R :=
  (homologyIsoXOfDEqZero _ (mapBifunctor_d_eq_zero F F') 0).symm ≪≫ h.toHomologyIso 0 ≪≫
    HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat.{u} R))

/-- **The idempotents of a complex and of its tensor inverse correspond.** In the situation of
`mul_eq_zero_of_ne_neg`, if both families are complete then `g_{-n} = f_n`. -/
public theorem eq_neg_of_complete (F F' : ℤ → ModuleCat.{u} R) (f g : ℤ → R) (S S' : Finset ℤ)
    (hfS : ∀ n ∉ S, f n = 0) (hgS : ∀ n ∉ S', g n = 0) (hf1 : ∑ n ∈ S, f n = 1)
    (hg1 : ∑ n ∈ S', g n = 1)
    (hf : ∀ n k, (scalarNatTrans (f n)).app (F k) = if k = n then 𝟙 _ else 0)
    (hg : ∀ n k, (scalarNatTrans (g n)).app (F' k) = if k = n then 𝟙 _ else 0)
    (Φ : (HomologicalComplex.mapBifunctor (CochainComplex.zeroDifferentialComplex F)
      (CochainComplex.zeroDifferentialComplex F') (curriedTensor (ModuleCat.{u} R))
      (ComplexShape.up ℤ)).X 0 ≅ ModuleCat.of R R) (n : ℤ) :
    g (-n) = f n := by
  have hz : ∀ m p, p ≠ -m → f m * g p = 0 := fun m p h =>
    mul_eq_zero_of_ne_neg F F' f g hf hg Φ h
  have h1 : f n = f n * g (-n) := by
    calc f n = f n * ∑ p ∈ S', g p := by rw [hg1, mul_one]
      _ = ∑ p ∈ S', f n * g p := Finset.mul_sum _ _ _
      _ = f n * g (-n) := Finset.sum_eq_single _ (fun p _ hp => hz n p hp) fun hm => by
        rw [hgS _ hm, mul_zero]
  have h2 : g (-n) = f n * g (-n) := by
    calc g (-n) = (∑ m ∈ S, f m) * g (-n) := by rw [hf1, one_mul]
      _ = ∑ m ∈ S, f m * g (-n) := Finset.sum_mul _ _ _
      _ = f n * g (-n) := Finset.sum_eq_single _
        (fun m _ hmn => hz m (-n) fun h => hmn (neg_inj.mp h.symm)) fun hm => by
        rw [hfS _ hm, zero_mul]
  rw [h2, ← h1]

/-- The image of an idempotent is invariant under isomorphisms intertwining the idempotents. -/
public def splitObjIsoOfIso {C : Type*} [Category* C] [Preadditive C] [HasKernels C] {A B : C}
    (φ : A ≅ B) {p : A ⟶ A} {q : B ⟶ B} (h : φ.hom ≫ q = p ≫ φ.hom) :
    Stacks.Cohomology.InvertibleDerived.splitObj p ≅
      Stacks.Cohomology.InvertibleDerived.splitObj q :=
  kernel.mapIso _ _ φ φ (by rw [Preadditive.comp_sub, Preadditive.sub_comp, Category.comp_id,
    Category.id_comp, h])

section Summand

variable (F F' : ℤ → ModuleCat.{u} R) (n : ℤ)

/-- The total complex of two complexes with zero differentials, in the bifunctor spelling. -/
public abbrev zeroDiffTotal : CochainComplex (ModuleCat.{u} R) ℤ :=
  HomologicalComplex.mapBifunctor (CochainComplex.zeroDifferentialComplex F)
    (CochainComplex.zeroDifferentialComplex F') (curriedTensor (ModuleCat.{u} R))
    (ComplexShape.up ℤ)

public theorem π_neg : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
    (ComplexShape.up ℤ) (n, -n) = 0 := add_neg_cancel n

/-- The inclusion of the summand `F^n ⊗ F'^{-n}` into the degree-zero part. -/
public abbrev summandι : F n ⊗ F' (-n) ⟶ (zeroDiffTotal F F').X 0 :=
  HomologicalComplex.ιMapBifunctor (CochainComplex.zeroDifferentialComplex F)
    (CochainComplex.zeroDifferentialComplex F') (curriedTensor (ModuleCat.{u} R))
    (ComplexShape.up ℤ) n (-n) 0 (π_neg n)

/-- The projection of the degree-zero part onto the summand `F^n ⊗ F'^{-n}`. -/
public def summandπ : (zeroDiffTotal F F').X 0 ⟶ F n ⊗ F' (-n) :=
  HomologicalComplex.mapBifunctorDesc fun p q h =>
    if hp : p = n then eqToHom (by
      subst hp
      have hq : q = -p := by
        have h' : p + q = 0 := h
        omega
      subst hq
      rfl) else 0

public theorem summandι_summandπ : summandι F F' n ≫ summandπ F F' n = 𝟙 _ := by
  refine (HomologicalComplex.ι_mapBifunctorDesc (i₁ := n) (i₂ := -n) (h := π_neg n) ..).trans ?_
  rw [dif_pos rfl]
  exact eqToHom_refl _ _

end Summand

/-- Multiplication by a scalar on a tensor product is multiplication on the left factor. -/
public theorem scalarNatTrans_app_tensorObj_left (a : R) (A B : ModuleCat.{u} R) :
    (scalarNatTrans a).app (A ⊗ B) = (scalarNatTrans a).app A ▷ B := by
  refine ModuleCat.hom_ext (TensorProduct.ext' fun x y => ?_)
  show a • (x ⊗ₜ[R] y) = (a • x) ⊗ₜ[R] y
  rw [TensorProduct.smul_tmul']

section Summand

variable (F F' : ℤ → ModuleCat.{u} R) (n : ℤ)

/-- **The projection onto the summand `F^n ⊗ F'^{-n}` is multiplication by `f_n`**, when `f_n`
acts on `F^k` as the identity for `k = n` and as zero otherwise. -/
public theorem summandπ_summandι (f : ℤ → R)
    (hf : ∀ n k, (scalarNatTrans (f n)).app (F k) = if k = n then 𝟙 _ else 0) :
    summandπ F F' n ≫ summandι F F' n = (scalarNatTrans (f n)).app ((zeroDiffTotal F F').X 0) := by
  refine HomologicalComplex.mapBifunctor.hom_ext fun p q hpq => ?_
  rw [← scalarNatTrans_naturality]
  refine ((HomologicalComplex.ι_mapBifunctorDesc_assoc (i₁ := p) (i₂ := q) (h := hpq) ..).trans
    ?_).trans (congrArg (· ≫ _) (scalarNatTrans_app_tensorObj_left (f n) (F p) (F' q))).symm
  rw [hf n p]
  by_cases hp : p = n
  · subst hp
    have hq : q = -p := by
      have h' : p + q = 0 := hpq
      omega
    subst hq
    rw [dif_pos rfl, if_pos rfl, MonoidalCategory.id_whiskerRight]
    exact (Category.id_comp _).trans (Category.id_comp _).symm
  · rw [dif_neg hp, if_neg hp, MonoidalPreadditive.zero_whiskerRight, Limits.zero_comp]
    exact Limits.zero_comp.symm

end Summand

section Summand

variable (F F' : ℤ → ModuleCat.{u} R) (n : ℤ) (f : ℤ → R)
  (hf : ∀ n k, (scalarNatTrans (f n)).app (F k) = if k = n then 𝟙 _ else 0)

include hf in
/-- **The summand `F^n ⊗ F'^{-n}` is the image of `f_n`.** -/
public def summandIsoSplitObj :
    F n ⊗ F' (-n) ≅ Stacks.Cohomology.InvertibleDerived.splitObj
      ((scalarNatTrans (f n)).app ((zeroDiffTotal F F').X 0)) where
  hom := kernel.lift _ (summandι F F' n) (by
    rw [Preadditive.comp_sub, Category.comp_id, ← summandπ_summandι F F' n f hf,
      ← Category.assoc, summandι_summandπ, Category.id_comp, sub_self])
  inv := Stacks.Cohomology.InvertibleDerived.splitι _ ≫ summandπ F F' n
  hom_inv_id := by
    rw [← Category.assoc, kernel.lift_ι, summandι_summandπ]
  inv_hom_id := by
    rw [← cancel_mono (Stacks.Cohomology.InvertibleDerived.splitι _), Category.assoc,
      kernel.lift_ι, Category.assoc, summandπ_summandι F F' n f hf, Category.id_comp]
    exact Stacks.Cohomology.InvertibleDerived.splitι_comp (by
      rw [← summandπ_summandι F F' n f hf, Category.assoc, ← Category.assoc (summandι F F' n),
        summandι_summandπ, Category.id_comp])

include hf in
/-- **The cohomology of a complex in degree `n` tensored with that of its tensor inverse in degree
`-n` is the factor `f_n R` of `R`.** -/
public def tensorIsoSplitObjOfIso (Φ : (zeroDiffTotal F F').X 0 ≅ ModuleCat.of R R) :
    F n ⊗ F' (-n) ≅ Stacks.Cohomology.InvertibleDerived.splitObj
      ((scalarNatTrans (f n)).app (ModuleCat.of R R)) :=
  summandIsoSplitObj F F' n f hf ≪≫
    splitObjIsoOfIso Φ (scalarNatTrans_naturality (f n) Φ.hom).symm


end Summand

end DerivedCategory.Invertible

end
