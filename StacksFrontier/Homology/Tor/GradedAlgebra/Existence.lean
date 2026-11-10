module

public import StacksFrontier.Homology.Tor.GradedAlgebra.Defs
public import StacksFrontier.Homology.Tor.GradedAlgebra.ResolutionProduct

/-!
# The graded Tor algebra: existence and uniqueness

Base change of tensor products of resolutions along `R → A`, and the existence and uniqueness of
the unital associative graded algebra structure on Tor, `GradedTor.existsUnique_algebra`.
-/

universe u uR uA v

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CochainComplex.DerivedTensor
open scoped MonoidalCategory
open TorCrossProduct (extC)

section

variable {R : Type u} [CommRing R]

section

variable (R : Type uR) (A : Type uA) [CommRing R] [CommRing A] (f : R →+* A)

set_option backward.isDefEq.respectTransparency false in
private theorem zeroBaseChange_naturality
    {M N M' N' : ModuleCat.{max uR uA v} R} (g : M ⟶ M') (h : N ⟶ N') :
    (TorCrossProduct.moduleTensorMap.{uR, uA, v}
      ((extensionScalars.{uR, uA, v} f).map g)
      ((extensionScalars.{uR, uA, v} f).map h)) ≫
      TorCrossProduct.zeroBaseChange.{uR, uA, v} R A f M' N' =
    TorCrossProduct.zeroBaseChange.{uR, uA, v} R A f M N ≫
      (extensionScalars.{uR, uA, v} f).map
        (TorCrossProduct.moduleTensorMap.{uA, uR, v} g h) := by
  let := f.toAlgebra
  apply ModuleCat.hom_ext
  dsimp only [extensionScalars, ModuleCat.extendScalars,
    ModuleCat.ExtendScalars.obj', ModuleCat.ExtendScalars.map',
    TorCrossProduct.zeroBaseChange, TorCrossProduct.moduleTensorMap,
    ModuleCat.moduleTensorLarge]
  apply TensorProduct.AlgebraTensorModule.ext
  intro x y
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => simp only [TensorProduct.add_tmul, map_add, hx, hx']
  | tmul a x =>
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' => simp only [TensorProduct.tmul_add, map_add, hy, hy']
    | tmul b y =>
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom]
      change (TensorProduct.AlgebraTensorModule.distribBaseChange R A M' N').symm
          ((a ⊗ₜ[R] g x) ⊗ₜ[A] (b ⊗ₜ[R] h y)) =
        (LinearMap.baseChange A ((h.hom.lTensor M').comp (g.hom.rTensor N)))
          ((TensorProduct.AlgebraTensorModule.distribBaseChange R A M N).symm
            ((a ⊗ₜ[R] x) ⊗ₜ[A] (b ⊗ₜ[R] y)))
      simp only [TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul,
        LinearMap.baseChange_tmul, LinearMap.comp_apply,
        LinearMap.lTensor_tmul, LinearMap.rTensor_tmul]

private def scalarTensorX
    (K L : ChainComplex (ModuleCat.{max uR uA v} R) ℕ) (n : ℕ) :
    letI : MonoidalCategory (ModuleCat.{max uR uA v} R) :=
      ModuleCat.liftedModuleMonoidal.{uR, max uA v}
    letI : MonoidalCategory (ModuleCat.{max uR uA v} A) :=
      ModuleCat.liftedModuleMonoidal.{uA, max uR v}
    (extC.{uR, uA, v} f K ⊗ extC.{uR, uA, v} f L).X n ⟶
      (extC.{uR, uA, v} f (K ⊗ L)).X n :=
  letI : MonoidalCategory (ModuleCat.{max uR uA v} R) :=
      ModuleCat.liftedModuleMonoidal.{uR, max uA v}
  letI : MonoidalCategory (ModuleCat.{max uR uA v} A) :=
      ModuleCat.liftedModuleMonoidal.{uA, max uR v}
  HomologicalComplex.mapBifunctorDesc (fun p q h =>
    TorCrossProduct.zeroBaseChange.{uR, uA, v} R A f (K.X p) (L.X q) ≫
      (extensionScalars.{uR, uA, v} f).map
        (HomologicalComplex.ιTensorObj K L p q n h))
private theorem scalarTensorX_ι
    (K L : ChainComplex (ModuleCat.{max uR uA v} R) ℕ) (p q n : ℕ) (h : p + q = n) :
    letI : MonoidalCategory (ModuleCat.{max uR uA v} R) :=
      ModuleCat.liftedModuleMonoidal.{uR, max uA v}
    letI : MonoidalCategory (ModuleCat.{max uR uA v} A) :=
      ModuleCat.liftedModuleMonoidal.{uA, max uR v}
    HomologicalComplex.ιTensorObj (extC.{uR, uA, v} f K) (extC.{uR, uA, v} f L) p q n h ≫
      scalarTensorX R A f K L n =
    TorCrossProduct.zeroBaseChange.{uR, uA, v} R A f (K.X p) (L.X q) ≫
      (extensionScalars.{uR, uA, v} f).map
        (HomologicalComplex.ιTensorObj K L p q n h) := by
  apply HomologicalComplex.ι_mapBifunctorDesc

private theorem scalarTensorX_eq_of_ι
    (K L : ChainComplex (ModuleCat.{max uR uA v} R) ℕ) (n : ℕ) :
    letI : MonoidalCategory (ModuleCat.{max uR uA v} R) :=
      ModuleCat.liftedModuleMonoidal.{uR, max uA v}
    letI : MonoidalCategory (ModuleCat.{max uR uA v} A) :=
      ModuleCat.liftedModuleMonoidal.{uA, max uR v}
    ∀ (φ : (extC.{uR, uA, v} f K ⊗ extC.{uR, uA, v} f L).X n ⟶
        (extC.{uR, uA, v} f (K ⊗ L)).X n),
      (∀ (p q : ℕ) (h : p + q = n),
        HomologicalComplex.ιTensorObj (extC.{uR, uA, v} f K) (extC.{uR, uA, v} f L) p q n h ≫ φ =
          TorCrossProduct.zeroBaseChange.{uR, uA, v} R A f (K.X p) (L.X q) ≫
            (extensionScalars.{uR, uA, v} f).map
              (HomologicalComplex.ιTensorObj K L p q n h)) →
        φ = scalarTensorX R A f K L n := by
  intro φ hφ
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  exact (hφ p q h).trans (scalarTensorX_ι R A f K L p q n h).symm

set_option maxHeartbeats 2000000 in
-- The total-complex comparison involves the two lifted monoidal structures.
set_option backward.isDefEq.respectTransparency false in
private theorem scalarTensorX_d
    (K L : ChainComplex (ModuleCat.{max uR uA v} R) ℕ) (n : ℕ) :
    letI : MonoidalCategory (ModuleCat.{max uR uA v} R) :=
      ModuleCat.liftedModuleMonoidal.{uR, max uA v}
    letI : MonoidalCategory (ModuleCat.{max uR uA v} A) :=
      ModuleCat.liftedModuleMonoidal.{uA, max uR v}
    scalarTensorX R A f K L (n + 1) ≫
        (extC.{uR, uA, v} f (K ⊗ L)).d (n + 1) n =
      (extC.{uR, uA, v} f K ⊗ extC.{uR, uA, v} f L).d (n + 1) n ≫
        scalarTensorX R A f K L n := by
  let : MonoidalCategory (ModuleCat.{max uR uA v} R) :=
    ModuleCat.liftedModuleMonoidal.{uR, max uA v}
  let : MonoidalCategory (ModuleCat.{max uR uA v} A) :=
    ModuleCat.liftedModuleMonoidal.{uA, max uR v}
  let F := extensionScalars.{uR, uA, v} f
  let FK := extC.{uR, uA, v} f K
  let FL := extC.{uR, uA, v} f L
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  change HomologicalComplex.ιTensorObj FK FL p q (n + 1) hpq ≫ _ = _
  erw [← Category.assoc, scalarTensorX_ι, Category.assoc, ← F.map_comp]
  change _ = HomologicalComplex.ιTensorObj FK FL p q (n + 1) hpq ≫
    (FK ⊗ FL).d (n + 1) n ≫ _
  erw [HomologicalComplex.mapBifunctor.d_eq K L,
    HomologicalComplex.mapBifunctor.d_eq FK FL,
    Preadditive.comp_add, HomologicalComplex.mapBifunctor.ι_D₁,
    HomologicalComplex.mapBifunctor.ι_D₂,
    F.map_add, Preadditive.comp_add, Preadditive.add_comp, Preadditive.comp_add,
    ← Category.assoc, HomologicalComplex.mapBifunctor.ι_D₁,
    ← Category.assoc, HomologicalComplex.mapBifunctor.ι_D₂]
  congr 1
  · cases p with
    | zero =>
      rw [HomologicalComplex.mapBifunctor.d₁_eq_zero _ _ _ _ _ _ _ (by simp),
        HomologicalComplex.mapBifunctor.d₁_eq_zero _ _ _ _ _ _ _ (by simp),
        F.map_zero, comp_zero, zero_comp]
    | succ p =>
      have hp : (ComplexShape.down ℕ).Rel (p + 1) p := rfl
      have h : p + q = n := by change p + 1 + q = n + 1 at hpq; lia
      rw [HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _ hp q n h,
        HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _ hp q n h,
        F.map_units_smul, Linear.comp_units_smul, Linear.units_smul_comp,
        Category.assoc, scalarTensorX_ι, F.map_comp]
      congr 1
      rw [← Category.assoc, ← Category.assoc]
      congr 1
      have hn := (zeroBaseChange_naturality R A f (K.d (p + 1) p) (𝟙 (L.X q))).symm
      rw [CategoryTheory.Functor.map_id] at hn
      dsimp only [TorCrossProduct.moduleTensorMap] at hn
      rw [CategoryTheory.Functor.map_id, Category.comp_id,
        CategoryTheory.Functor.map_id, Category.comp_id] at hn
      exact hn
  · cases q with
    | zero =>
      rw [HomologicalComplex.mapBifunctor.d₂_eq_zero _ _ _ _ _ _ _ (by simp),
        HomologicalComplex.mapBifunctor.d₂_eq_zero _ _ _ _ _ _ _ (by simp),
        F.map_zero, comp_zero, zero_comp]
    | succ q =>
      have hq : (ComplexShape.down ℕ).Rel (q + 1) q := rfl
      have h : p + q = n := by change p + (q + 1) = n + 1 at hpq; lia
      rw [HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ p hq n h,
        HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ p hq n h,
        F.map_units_smul, Linear.comp_units_smul, Linear.units_smul_comp,
        Category.assoc, scalarTensorX_ι, F.map_comp]
      congr 1
      rw [← Category.assoc, ← Category.assoc]
      congr 1
      have hn := (zeroBaseChange_naturality R A f (𝟙 (K.X p)) (L.d (q + 1) q)).symm
      rw [CategoryTheory.Functor.map_id] at hn
      dsimp only [TorCrossProduct.moduleTensorMap] at hn
      rw [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp,
        CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp] at hn
      exact hn

private noncomputable def scalarTensorComplexMap
    (K L : ChainComplex (ModuleCat.{max uR uA v} R) ℕ) :
    letI : MonoidalCategory (ModuleCat.{max uR uA v} R) :=
      ModuleCat.liftedModuleMonoidal.{uR, max uA v}
    letI : MonoidalCategory (ModuleCat.{max uR uA v} A) :=
      ModuleCat.liftedModuleMonoidal.{uA, max uR v}
    extC.{uR, uA, v} f K ⊗ extC.{uR, uA, v} f L ⟶
      extC.{uR, uA, v} f (K ⊗ L) := by
  letI : MonoidalCategory (ModuleCat.{max uR uA v} R) :=
    ModuleCat.liftedModuleMonoidal.{uR, max uA v}
  letI : MonoidalCategory (ModuleCat.{max uR uA v} A) :=
    ModuleCat.liftedModuleMonoidal.{uA, max uR v}
  exact {
  f := scalarTensorX R A f K L
  comm' i j h := by
    have h : i = j + 1 := h.symm
    subst i
    exact scalarTensorX_d R A f K L j }

set_option backward.isDefEq.respectTransparency false in
private theorem scalarTensorX_tmul
    (K L : ChainComplex (ModuleCat.{max uR uA v} R) ℕ)
    (p q n : ℕ) (h : p + q = n) (a b : A) (x : K.X p) (y : L.X q) :
    letI := f.toAlgebra
    letI : MonoidalCategory (ModuleCat.{max uR uA v} R) :=
      ModuleCat.liftedModuleMonoidal.{uR, max uA v}
    letI : MonoidalCategory (ModuleCat.{max uR uA v} A) :=
      ModuleCat.liftedModuleMonoidal.{uA, max uR v}
    scalarTensorX R A f K L n
      (HomologicalComplex.ιTensorObj (extC.{uR, uA, v} f K) (extC.{uR, uA, v} f L)
        p q n h ((a ⊗ₜ[R] x) ⊗ₜ[A] (b ⊗ₜ[R] y))) =
      (a * b) ⊗ₜ[R] (HomologicalComplex.ιTensorObj K L p q n h (x ⊗ₜ[R] y)) := by
  let := f.toAlgebra
  let : MonoidalCategory (ModuleCat.{max uR uA v} R) :=
    ModuleCat.liftedModuleMonoidal.{uR, max uA v}
  let : MonoidalCategory (ModuleCat.{max uR uA v} A) :=
    ModuleCat.liftedModuleMonoidal.{uA, max uR v}
  have hι := congrArg (fun t => t ((a ⊗ₜ[R] x) ⊗ₜ[A] (b ⊗ₜ[R] y)))
    (scalarTensorX_ι R A f K L p q n h)
  change _ = ((extensionScalars f).map
    (HomologicalComplex.ιTensorObj K L p q n h))
    ((TensorProduct.AlgebraTensorModule.distribBaseChange R A (K.X p) (L.X q)).symm
      ((a ⊗ₜ[R] x) ⊗ₜ[A] (b ⊗ₜ[R] y))) at hι
  rw [TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul] at hι
  exact hι
private abbrev scalarComplexMap
    {K L : ChainComplex (ModuleCat.{max uR uA v} R) ℕ} (g : K ⟶ L) :=
  ((extensionScalars.{uR, uA, v} f).mapHomologicalComplex
    (ComplexShape.down ℕ)).map g

private abbrev scalarTensorSummand
    (K L : ChainComplex (ModuleCat.{max uR uA v} R) ℕ)
    (p q n : ℕ) (h : p + q = n) :
    ((ModuleCat.moduleTensorLarge.{uA, max uR v} A).obj ((extC.{uR, uA, v} f K).X p)).obj
        ((extC.{uR, uA, v} f L).X q) ⟶
      (extC.{uR, uA, v} f (TorCrossProduct.chainTensor.{uA, uR, v} K L)).X n :=
  HomologicalComplex.ιMapBifunctor (extC.{uR, uA, v} f K) (extC.{uR, uA, v} f L)
    (ModuleCat.moduleTensorLarge.{uA, max uR v} A) (ComplexShape.down ℕ) p q n h ≫
      scalarTensorX R A f K L n

private abbrev scalarProductMap
    {K : ChainComplex (ModuleCat.{max uR uA v} R) ℕ}
    (μ : TorCrossProduct.chainTensor.{uA, uR, v} K K ⟶ K)
    (p q n : ℕ) (h : p + q = n) :
    ((ModuleCat.moduleTensorLarge.{uA, max uR v} A).obj ((extC.{uR, uA, v} f K).X p)).obj
        ((extC.{uR, uA, v} f K).X q) ⟶ (extC.{uR, uA, v} f K).X n :=
  scalarTensorSummand R A f K K p q n h ≫ (scalarComplexMap R A f μ).f n

private lemma scalarTensorSummand_tmul
    (K L : ChainComplex (ModuleCat.{max uR uA v} R) ℕ)
    (p q n : ℕ) (h : p + q = n) (a b : A) (x : K.X p) (y : L.X q) :
    letI := f.toAlgebra
    scalarTensorSummand R A f K L p q n h ((a ⊗ₜ[R] x) ⊗ₜ[A] (b ⊗ₜ[R] y)) =
      (a * b) ⊗ₜ[R] (HomologicalComplex.ιMapBifunctor K L
        (ModuleCat.moduleTensorLarge.{uR, max uA v} R) (ComplexShape.down ℕ) p q n h
        (x ⊗ₜ[R] y)) :=
  scalarTensorX_tmul R A f K L p q n h a b x y

private lemma scalarProductMap_tmul
    {K : ChainComplex (ModuleCat.{max uR uA v} R) ℕ}
    (μ : TorCrossProduct.chainTensor.{uA, uR, v} K K ⟶ K)
    (p q n : ℕ) (h : p + q = n) (a b : A) (x : K.X p) (y : K.X q) :
    letI := f.toAlgebra
    scalarProductMap R A f μ p q n h ((a ⊗ₜ[R] x) ⊗ₜ[A] (b ⊗ₜ[R] y)) =
      (a * b) ⊗ₜ[R] μ.f n (HomologicalComplex.ιMapBifunctor K K
        (ModuleCat.moduleTensorLarge.{uR, max uA v} R) (ComplexShape.down ℕ) p q n h
        (x ⊗ₜ[R] y)) := by
  let := f.toAlgebra
  change (scalarComplexMap R A f μ).f n
    (scalarTensorSummand R A f K K p q n h ((a ⊗ₜ[R] x) ⊗ₜ[A] (b ⊗ₜ[R] y))) = _
  rw [scalarTensorSummand_tmul]
  rfl

-- Naturality is checked on the homogeneous summands of the tensor complex.
set_option backward.isDefEq.respectTransparency false in
private theorem scalarTensorComplexMap_naturality
    {K L K' L' : ChainComplex (ModuleCat.{max uR uA v} R) ℕ}
    (g : K ⟶ K') (h : L ⟶ L') :
    letI : MonoidalCategory (ModuleCat.{max uR uA v} R) :=
      ModuleCat.liftedModuleMonoidal.{uR, max uA v}
    letI : MonoidalCategory (ModuleCat.{max uR uA v} A) :=
      ModuleCat.liftedModuleMonoidal.{uA, max uR v}
    (scalarComplexMap R A f g ⊗ₘ scalarComplexMap R A f h) ≫
        scalarTensorComplexMap R A f K' L' =
      scalarTensorComplexMap R A f K L ≫ scalarComplexMap R A f (g ⊗ₘ h) := by
  let : MonoidalCategory (ModuleCat.{max uR uA v} R) :=
    ModuleCat.liftedModuleMonoidal.{uR, max uA v}
  let : MonoidalCategory (ModuleCat.{max uR uA v} A) :=
    ModuleCat.liftedModuleMonoidal.{uA, max uR v}
  let F := extensionScalars.{uR,uA,v} f
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  change HomologicalComplex.ιTensorObj (extC.{uR, uA, v} f K) (extC.{uR, uA, v} f L)
    p q n hpq ≫ (scalarComplexMap R A f g ⊗ₘ scalarComplexMap R A f h).f n ≫
      scalarTensorX R A f K' L' n =
    HomologicalComplex.ιTensorObj (extC.{uR, uA, v} f K) (extC.{uR, uA, v} f L)
      p q n hpq ≫ scalarTensorX R A f K L n ≫ F.map ((g ⊗ₘ h).f n)
  erw [← Category.assoc, HomologicalComplex.ι_mapBifunctorMap,
    Category.assoc, Category.assoc, scalarTensorX_ι]
  conv_rhs => rw [← Category.assoc, scalarTensorX_ι, Category.assoc, ← F.map_comp]
  rw [← Category.assoc]
  change TorCrossProduct.moduleTensorMap.{uR,uA,v} (F.map (g.f p)) (F.map (h.f q)) ≫
    TorCrossProduct.zeroBaseChange R A f (K'.X p) (L'.X q) ≫
      F.map (HomologicalComplex.ιTensorObj K' L' p q n hpq) = _
  rw [← Category.assoc, zeroBaseChange_naturality, Category.assoc, ← F.map_comp]
  congr 1
  apply congrArg F.map
  exact (HomologicalComplex.ι_mapBifunctorMap g h (curriedTensor (ModuleCat.{max uR uA v} R))
    (ComplexShape.down ℕ) p q n hpq).symm

private lemma scalarComplexMap_tmul
    {K L : ChainComplex (ModuleCat.{max uR uA v} R) ℕ} (g : K ⟶ L)
    (n : ℕ) (a : A) (x : K.X n) :
    letI := f.toAlgebra
    (scalarComplexMap R A f g).f n (a ⊗ₜ[R] x) = a ⊗ₜ[R] g.f n x := rfl

-- The scalar-extended unit comparison is linear in its input.
set_option backward.isDefEq.respectTransparency false in
private lemma scalarProductMap_one_left
    (K : ChainComplex (ModuleCat.{max uR uA v} R) ℕ) :
    letI := f.toAlgebra
    letI : MonoidalCategory (ModuleCat.{max uR uA v} R) :=
      ModuleCat.liftedModuleMonoidal.{uR, max uA v}
    ∀ (μ : K ⊗ K ⟶ K)
      (η : 𝟙_ (ChainComplex (ModuleCat.{max uR uA v} R) ℕ) ⟶ K)
      (n : ℕ) (x : (extC.{uR, uA, v} f K).X n),
    scalarProductMap R A f μ 0 n n (zero_add n)
      (((1 : A) ⊗ₜ[R] η.f 0 (ULift.up 1)) ⊗ₜ[A] x) =
      (scalarComplexMap R A f ((λ_ K).inv ≫ (η ⊗ₘ 𝟙 K) ≫ μ)).f n x := by
  let := f.toAlgebra
  let : MonoidalCategory (ModuleCat.{max uR uA v} R) :=
    ModuleCat.liftedModuleMonoidal.{uR, max uA v}
  intro μ η n x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp_all only [TensorProduct.tmul_add, map_add]
  | tmul a x =>
    rw [scalarProductMap_tmul, one_mul, scalarComplexMap_tmul]
    change _ = a ⊗ₜ[R] μ.f n ((η ⊗ₘ 𝟙 K).f n ((λ_ K).inv.f n x))
    rw [leftUnitor_inv_f_apply.{uR, max uA v}, tensorHom_ι_apply.{uR, max uA v}]
    rfl

-- The scalar-extended unit comparison is linear in its input.
set_option backward.isDefEq.respectTransparency false in
private lemma scalarProductMap_one_right
    (K : ChainComplex (ModuleCat.{max uR uA v} R) ℕ) :
    letI := f.toAlgebra
    letI : MonoidalCategory (ModuleCat.{max uR uA v} R) :=
      ModuleCat.liftedModuleMonoidal.{uR, max uA v}
    ∀ (μ : K ⊗ K ⟶ K)
      (η : 𝟙_ (ChainComplex (ModuleCat.{max uR uA v} R) ℕ) ⟶ K)
      (n : ℕ) (x : (extC.{uR, uA, v} f K).X n),
    scalarProductMap R A f μ n 0 n (add_zero n)
      (x ⊗ₜ[A] ((1 : A) ⊗ₜ[R] η.f 0 (ULift.up 1))) =
      (scalarComplexMap R A f ((ρ_ K).inv ≫ (𝟙 K ⊗ₘ η) ≫ μ)).f n x := by
  let := f.toAlgebra
  let : MonoidalCategory (ModuleCat.{max uR uA v} R) :=
    ModuleCat.liftedModuleMonoidal.{uR, max uA v}
  intro μ η n x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp_all only [TensorProduct.add_tmul, map_add]
  | tmul a x =>
    rw [scalarProductMap_tmul, mul_one, scalarComplexMap_tmul]
    change _ = a ⊗ₜ[R] μ.f n ((𝟙 K ⊗ₘ η).f n ((ρ_ K).inv.f n x))
    rw [rightUnitor_inv_f_apply.{uR, max uA v}, tensorHom_ι_apply.{uR, max uA v}]
    rfl


set_option maxHeartbeats 2000000 in
-- The comparison is trilinear; pure tensors reduce it to the tensor-map formula.
set_option backward.isDefEq.respectTransparency false in
private lemma scalarProductMap_assoc_left
    (K : ChainComplex (ModuleCat.{max uR uA v} R) ℕ) :
    letI : MonoidalCategory (ModuleCat.{max uR uA v} R) :=
      ModuleCat.liftedModuleMonoidal.{uR, max uA v}
    ∀ (μ : K ⊗ K ⟶ K) (p q r t : ℕ) (h : p + q + r = t)
      (x : (extC.{uR, uA, v} f K).X p) (y : (extC.{uR, uA, v} f K).X q)
      (z : (extC.{uR, uA, v} f K).X r),
    scalarProductMap R A f μ (p+q) r t h
        (scalarProductMap R A f μ p q (p+q) rfl (x ⊗ₜ[A] y) ⊗ₜ[A] z) =
      (scalarComplexMap R A f ((μ ⊗ₘ 𝟙 K) ≫ μ)).f t
        (scalarTensorSummand R A f (K ⊗ K) K (p+q) r t h
          (scalarTensorSummand R A f K K p q (p+q) rfl (x ⊗ₜ[A] y) ⊗ₜ[A] z)) := by
  let := f.toAlgebra
  let : MonoidalCategory (ModuleCat.{max uR uA v} R) :=
    ModuleCat.liftedModuleMonoidal.{uR, max uA v}
  intro μ p q r t h x y z
  subst t
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => simp_all only [TensorProduct.add_tmul, map_add]
  | tmul a x =>
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' => simp_all only [TensorProduct.tmul_add, TensorProduct.add_tmul, map_add]
    | tmul b y =>
      induction z using TensorProduct.inductionOn with
      | add z z' hz hz' => simp_all only [TensorProduct.tmul_add, map_add]
      | tmul c z =>
        rw [scalarProductMap_tmul, scalarProductMap_tmul,
          scalarTensorSummand_tmul, scalarTensorSummand_tmul, scalarComplexMap_tmul]
        change _ = _ ⊗ₜ[R] μ.f (p+q+r)
          ((μ ⊗ₘ 𝟙 K).f (p+q+r)
            (HomologicalComplex.ιTensorObj (K ⊗ K) K (p+q) r (p+q+r) rfl
              (HomologicalComplex.ιTensorObj K K p q (p+q) rfl (x ⊗ₜ[R] y) ⊗ₜ[R] z)))
        rw [tensorHom_ι_apply.{uR, max uA v}]
        rfl

set_option maxHeartbeats 2000000 in
-- Trilinearity reduces associator coherence to homogeneous pure tensors.
set_option backward.isDefEq.respectTransparency false in
private lemma scalarProductMap_assoc_right
    (K : ChainComplex (ModuleCat.{max uR uA v} R) ℕ) :
    letI : MonoidalCategory (ModuleCat.{max uR uA v} R) :=
      ModuleCat.liftedModuleMonoidal.{uR, max uA v}
    ∀ (μ : K ⊗ K ⟶ K) (p q r t : ℕ) (h : p + q + r = t)
      (x : (extC.{uR, uA, v} f K).X p) (y : (extC.{uR, uA, v} f K).X q)
      (z : (extC.{uR, uA, v} f K).X r),
    scalarProductMap R A f μ p (q+r) t ((Nat.add_assoc p q r).symm.trans h)
        (x ⊗ₜ[A] scalarProductMap R A f μ q r (q+r) rfl (y ⊗ₜ[A] z)) =
      (scalarComplexMap R A f ((α_ K K K).hom ≫ (𝟙 K ⊗ₘ μ) ≫ μ)).f t
        (scalarTensorSummand R A f (K ⊗ K) K (p+q) r t h
          (scalarTensorSummand R A f K K p q (p+q) rfl (x ⊗ₜ[A] y) ⊗ₜ[A] z)) := by
  let := f.toAlgebra
  let : MonoidalCategory (ModuleCat.{max uR uA v} R) :=
    ModuleCat.liftedModuleMonoidal.{uR, max uA v}
  intro μ p q r t h x y z
  subst t
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => simp_all only [TensorProduct.add_tmul, map_add]
  | tmul a x =>
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' => simp_all only [TensorProduct.tmul_add, TensorProduct.add_tmul, map_add]
    | tmul b y =>
      induction z using TensorProduct.inductionOn with
      | add z z' hz hz' => simp_all only [TensorProduct.tmul_add, map_add]
      | tmul c z =>
        change A at a b c
        rw [scalarProductMap_tmul R A f μ q r (q+r) rfl b c y z]
        erw [scalarProductMap_tmul R A f μ p (q+r) (p+q+r)
          (Nat.add_assoc p q r).symm a (b*c) x
          (μ.f (q+r) (HomologicalComplex.ιTensorObj K K q r (q+r) rfl (y ⊗ₜ[R] z)))]
        rw [scalarTensorSummand_tmul R A f K K p q (p+q) rfl a b x y]
        erw [scalarTensorSummand_tmul R A f (K ⊗ K) K (p+q) r (p+q+r) rfl
          (a*b) c (HomologicalComplex.ιTensorObj K K p q (p+q) rfl (x ⊗ₜ[R] y)) z]
        rw [scalarComplexMap_tmul]
        change _ = _ ⊗ₜ[R] μ.f (p+q+r)
          ((𝟙 K ⊗ₘ μ).f (p+q+r) ((α_ K K K).hom.f (p+q+r)
            (HomologicalComplex.ιTensorObj (K ⊗ K) K (p+q) r (p+q+r) rfl
              (HomologicalComplex.ιTensorObj K K p q (p+q) rfl (x ⊗ₜ[R] y) ⊗ₜ[R] z))))
        have hα := associator_ι_apply.{uR, max uA v} K K K p q r x y z
        have ht := tensorHom_ι_apply.{uR, max uA v} (𝟙 K) μ p (q+r) (p+q+r)
          (Nat.add_assoc p q r).symm x
          (HomologicalComplex.ιTensorObj K K q r (q+r) rfl (y ⊗ₜ[R] z))
        rw [hα, ht]
        rw [mul_assoc]
        rfl

end

end

namespace GradedTor

variable (R : Type uR) (A : Type uA) [CommRing R] [CommRing A] [_root_.Algebra R A]

private lemma torPiece_neg_subsingleton (B : AlgCat.{v, uR} R) (n : ℕ) :
    Subsingleton (torPiece.{uR, uA, v} R A B (Int.negSucc n)) := by
  change Subsingleton (ULift (Fin 0 → A))
  infer_instance

private noncomputable def gradedMul (B : AlgCat.{v, uR} R) (i j : ℤ) :
    moduleTensor.{uA, max uR v} A (torPiece R A B i) (torPiece R A B j) ⟶
      torPiece R A B (i + j) :=
  match i, j with
  | .ofNat n, .ofNat m => torMultiplication R A B n m
  | .ofNat _, .negSucc _ => 0
  | .negSucc _, _ => 0
private theorem torPiece_cast_zero (B : AlgCat.{v, uR} R) {i j : ℤ} (h : i = j) :
    cast (congrArg (fun k => (torPiece R A B k : Type (max uR uA v))) h) (0 : torPiece R A B i) =
      (0 : torPiece R A B j) := by
  subst j
  rfl
private theorem algebra_exists_of_nonneg
    (B : AlgCat.{v, uR} R) (one : torPiece R A B 0)
    (hleft : ∀ (n : ℕ) (x : torPiece R A B n),
      cast (by rw [zero_add]) (gradedMul R A B 0 n (one ⊗ₜ[A] x)) = x)
    (hright : ∀ (n : ℕ) (x : torPiece R A B n),
      cast (by rw [add_zero]) (gradedMul R A B n 0 (x ⊗ₜ[A] one)) = x)
    (hassoc : ∀ (n m k : ℕ) (x : torPiece R A B n) (y : torPiece R A B m)
      (z : torPiece R A B k),
      cast (by rw [add_assoc])
        (gradedMul R A B ((n : ℤ) + m) k (gradedMul R A B n m (x ⊗ₜ[A] y) ⊗ₜ[A] z)) =
        gradedMul R A B n ((m : ℤ) + k) (x ⊗ₜ[A] gradedMul R A B m k (y ⊗ₜ[A] z))) :
    Nonempty (Algebra.{uR, uA, v} R A B) := by
  refine ⟨{
    one := one
    mul := gradedMul R A B
    one_mul := ?_
    mul_one := ?_
    mul_assoc := ?_
    mul_ofNat := fun _ _ => rfl }⟩
  · intro i x
    cases i with
    | ofNat n => exact hleft n x
    | negSucc n =>
      have := torPiece_neg_subsingleton R A B n
      exact Subsingleton.elim _ _
  · intro i x
    cases i with
    | ofNat n => exact hright n x
    | negSucc n =>
      have := torPiece_neg_subsingleton R A B n
      exact Subsingleton.elim _ _
  · intro i j k x y z
    cases i with
    | negSucc n =>
      have := torPiece_neg_subsingleton R A B n
      have hx : x = 0 := Subsingleton.elim _ _
      rw [hx, TensorProduct.zero_tmul, map_zero, TensorProduct.zero_tmul,
        map_zero]
      exact torPiece_cast_zero R A B (add_assoc _ _ _)
    | ofNat n =>
      cases j with
      | negSucc m =>
        have := torPiece_neg_subsingleton R A B m
        have hy : y = 0 := Subsingleton.elim _ _
        rw [hy, TensorProduct.tmul_zero, map_zero, TensorProduct.zero_tmul, map_zero,
          TensorProduct.zero_tmul, map_zero, TensorProduct.tmul_zero, map_zero]
        exact torPiece_cast_zero R A B (add_assoc _ _ _)
      | ofNat m =>
        cases k with
        | ofNat k => exact hassoc n m k x y z
        | negSucc k =>
          have := torPiece_neg_subsingleton R A B k
          have hz : z = 0 := Subsingleton.elim _ _
          simp only [hz, TensorProduct.tmul_zero, map_zero, TensorProduct.tmul_zero, map_zero]
          exact torPiece_cast_zero R A B (add_assoc _ _ _)

/-- Maps out of a tensor product with a subsingleton factor are equal. -/
private lemma hom_eq_of_subsingleton {M N T : ModuleCat.{max uA v} A}
    (f g : moduleTensor.{uA, v} A M N ⟶ T)
    (h : Subsingleton M ∨ Subsingleton N) : f = g := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  have hz : z = 0 := by
    induction z using TensorProduct.inductionOn with
    | tmul x y =>
      rcases h with h | h
      · rw [Subsingleton.elim x 0, TensorProduct.zero_tmul]
      · rw [Subsingleton.elim y 0, TensorProduct.tmul_zero]
    | add x y hx hy => rw [hx, hy, add_zero]
  rw [hz, map_zero, map_zero]

private theorem algebra_subsingleton (B : AlgCat.{v, uR} R) :
    Subsingleton (Algebra.{uR, uA, v} R A B) := by
  constructor
  intro X Y
  have hmul : X.mul = Y.mul := by
    funext i j
    cases i with
    | ofNat n =>
      cases j with
      | ofNat m => exact (X.mul_ofNat n m).trans (Y.mul_ofNat n m).symm
      | negSucc m =>
        have := torPiece_neg_subsingleton R A B m
        exact hom_eq_of_subsingleton.{uA, max uR v} A _ _ (Or.inr this)
    | negSucc n =>
      have := torPiece_neg_subsingleton R A B n
      exact hom_eq_of_subsingleton.{uA, max uR v} A _ _ (Or.inl this)
  have hone : X.one = Y.one := by
    have h₁ := X.one_mul 0 Y.one
    have h₂ := Y.mul_one 0 X.one
    rw [hmul] at h₁
    exact h₂.symm.trans h₁
  cases X
  cases Y
  simp_all only


private abbrev multiplicationMap (B : AlgCat.{v, uR} R) :
    (RingTheory.TorProducts.tensorBifunctor.{uR, max uA v} R).obj
      (liftedModule R A B, liftedModule R A B) ⟶ liftedModule R A B :=
  ModuleCat.ofHom (TensorProduct.lift (LinearMap.mul R (liftedAlgebra R A B)))

private def torRep (B : AlgCat.{v, uR} R)
    (P : ProjectiveResolution (liftedModule R A B)) (n : ℕ)
    (a : torPiece R A B n) (x : (extC.{uR, uA, v} (algebraMap R A) P.complex).X n) : Prop :=
  homologyRep.{uA, max uR v} (extC.{uR, uA, v} (algebraMap R A) P.complex) n
    ((P.isoLeftDerivedObj (extensionScalars (algebraMap R A)) n).hom a) x

private lemma torRep_exists (B : AlgCat.{v, uR} R)
    (P : ProjectiveResolution (liftedModule R A B)) (n : ℕ) (a : torPiece R A B n) :
    ∃ x, torRep R A B P n a x :=
  homologyRep_exists.{uA, max uR v} _ _ _

private lemma torRep_eq (B : AlgCat.{v, uR} R)
    (P : ProjectiveResolution (liftedModule R A B)) {n : ℕ} {a b : torPiece R A B n}
    {x : (extC.{uR, uA, v} (algebraMap R A) P.complex).X n}
    (ha : torRep R A B P n a x) (hb : torRep R A B P n b x) : a = b := by
  apply (P.isoLeftDerivedObj
    (extensionScalars (algebraMap R A)) n).toLinearEquiv.injective
  exact homologyRep_eq.{uA, max uR v} ha hb

private lemma torRep_of_cycle (B : AlgCat.{v, uR} R)
    (P : ProjectiveResolution (liftedModule R A B)) (n : ℕ)
    (x : (extC.{uR, uA, v} (algebraMap R A) P.complex).X n)
    (hx : (extC.{uR, uA, v} (algebraMap R A) P.complex).d n
      ((ComplexShape.down ℕ).next n) x = 0) : ∃ a, torRep R A B P n a x := by
  obtain ⟨a, ha⟩ := homologyRep_of_cycle.{uA, max uR v} x hx
  let e := P.isoLeftDerivedObj (extensionScalars (algebraMap R A)) n
  refine ⟨e.inv a, ?_⟩
  change homologyRep.{uA, max uR v} _ n (e.hom (e.inv a)) x
  have he : e.hom (e.inv a) = a := congrArg (fun t => t a) e.inv_hom_id
  rw [he]
  exact ha

set_option backward.isDefEq.respectTransparency false in
private lemma resolution_multiplication_exists (B : AlgCat.{v, uR} R)
    (P : ProjectiveResolution (liftedModule R A B)) :
    ∃ μ : TorCrossProduct.chainTensor.{uA, uR, v} P.complex P.complex ⟶ P.complex,
      HomologicalComplex.ιMapBifunctor P.complex P.complex
          (ModuleCat.moduleTensorLarge.{uR, max uA v} R) (ComplexShape.down ℕ) 0 0 0 rfl ≫
        μ.f 0 ≫ P.π.f 0 =
      TorCrossProduct.moduleTensorMap.{uA, uR, v} (P.π.f 0) (P.π.f 0) ≫
        multiplicationMap R A B := by
  let M := liftedModule R A B
  let T := projectiveResolution
    ((RingTheory.TorProducts.tensorBifunctor.{uR, max uA v} R).obj (M, M))
  obtain ⟨c⟩ := RingTheory.TorProducts.torProduct_resolution R A 0 0 M M P P T
  refine ⟨c.μ ≫ ProjectiveResolution.lift (multiplicationMap R A B) T P, ?_⟩
  change _ ≫ (c.μ.f 0 ≫ (ProjectiveResolution.lift (multiplicationMap R A B) T P).f 0) ≫
    P.π.f 0 = _
  rw [Category.assoc, ProjectiveResolution.lift_commutes_zero]
  simpa only [Category.assoc] using congrArg (fun t => t ≫ multiplicationMap R A B) c.μ_zero


end GradedTor

namespace GradedTor
variable (R : Type uR) (A : Type uA) [CommRing R] [CommRing A] [_root_.Algebra R A]
-- The resolution formula identifies the canonical product with its cycle representative.
set_option backward.isDefEq.respectTransparency false in
private lemma torRep_product (B : AlgCat.{v, uR} R)
    (P : ProjectiveResolution (liftedModule R A B))
    (μ : TorCrossProduct.chainTensor.{uA, uR, v} P.complex P.complex ⟶ P.complex)
    (hμ : HomologicalComplex.ιMapBifunctor P.complex P.complex
        (ModuleCat.moduleTensorLarge.{uR, max uA v} R) (ComplexShape.down ℕ) 0 0 0 rfl ≫
        μ.f 0 ≫ P.π.f 0 =
      TorCrossProduct.moduleTensorMap.{uA, uR, v} (P.π.f 0) (P.π.f 0) ≫ multiplicationMap R A B)
    (p q n : ℕ) (h : p + q = n)
    {a : torPiece R A B p} {b : torPiece R A B q}
    {x : (extC.{uR, uA, v} (algebraMap R A) P.complex).X p}
    {y : (extC.{uR, uA, v} (algebraMap R A) P.complex).X q}
    (ha : torRep R A B P p a x) (hb : torRep R A B P q b y) :
    torRep R A B P n
      (cast (congrArg (fun i : ℕ => (torPiece R A B (i : ℤ) : Type (max uR uA v))) h)
        (torMultiplication R A B p q (a ⊗ₜ[A] b)))
      (scalarProductMap R A (algebraMap R A) μ p q n h (x ⊗ₜ[A] y)) := by
  subst n
  let M := liftedModule R A B
  let T := projectiveResolution
    ((RingTheory.TorProducts.tensorBifunctor.{uR, max uA v} R).obj (M, M))
  let F := extensionScalars.{uR,uA,v} (algebraMap R A)
  obtain ⟨c⟩ := RingTheory.TorProducts.torProduct_resolution.{uR, uA, v} R A p q M M P P T
  have hbc : c.baseChange.f (p+q) =
      scalarTensorX R A (algebraMap R A) P.complex P.complex (p+q) := by
    apply scalarTensorX_eq_of_ι
    intro i j hij
    exact c.baseChange_ι i j (p+q) hij
  have he := congrArg (fun t => t (a ⊗ₜ[A] b))
    (product_comp_map_resolution_of_normalized.{uR, uA, v} R A p q M M M (multiplicationMap R A B)
      P P T P c μ hμ)
  change (P.isoLeftDerivedObj F (p+q)).hom (torMultiplication R A B p q (a ⊗ₜ[A] b)) =
    HomologicalComplex.homologyMap (c.baseChange ≫ scalarComplexMap R A (algebraMap R A) μ) (p+q)
      (c.cohomologyProduct.map
        ((P.isoLeftDerivedObj F p).hom a ⊗ₜ[A] (P.isoLeftDerivedObj F q).hom b)) at he
  change homologyRep.{uA, max uR v} _ (p+q) _ _
  erw [he]
  have ht := homologyRep_map.{uA, max uR v} (c.baseChange ≫ scalarComplexMap R A (algebraMap R A) μ)
    (homologyRep_product.{uR, uA, v} c.cohomologyProduct ha hb)
  change homologyRep.{uA, max uR v} _ (p+q) _
    ((scalarComplexMap R A (algebraMap R A) μ).f (p+q)
      (c.baseChange.f (p+q) (HomologicalComplex.ιMapBifunctor _ _
        (ModuleCat.moduleTensorLarge.{uA, max uR v} A) (ComplexShape.down ℕ) p q (p+q) rfl
        (x ⊗ₜ[A] y)))) at ht
  rw [hbc] at ht
  exact ht
set_option maxHeartbeats 4000000 in
-- Transporting the three resolution homotopies compares iterated tensor representatives.
-- The lifted module categories and tensor complexes have nested monoidal instances.
set_option backward.isDefEq.respectTransparency false in
private theorem algebra_exists_of_resolution (B : AlgCat.{v, uR} R)
    (P : ProjectiveResolution (liftedModule R A B))
    (μ : TorCrossProduct.chainTensor.{uA, uR, v} P.complex P.complex ⟶ P.complex)
    (hμ : HomologicalComplex.ιMapBifunctor P.complex P.complex
        (ModuleCat.moduleTensorLarge.{uR, max uA v} R) (ComplexShape.down ℕ) 0 0 0 rfl ≫
        μ.f 0 ≫ P.π.f 0 =
      TorCrossProduct.moduleTensorMap.{uA, uR, v} (P.π.f 0) (P.π.f 0) ≫ multiplicationMap R A B) :
    letI : MonoidalCategory (ModuleCat.{max uR uA v} R) :=
      ModuleCat.liftedModuleMonoidal.{uR, max uA v}
    ∀ (η : 𝟙_ (ChainComplex (ModuleCat.{max uR uA v} R) ℕ) ⟶ P.complex),
      P.π.f 0 (η.f 0 (ULift.up 1)) = (1 : liftedAlgebra R A B) →
      Nonempty (Algebra.{uR,uA,v} R A B) := by
  let f := algebraMap R A
  let : MonoidalCategory (ModuleCat.{max uR uA v} R) :=
    ModuleCat.liftedModuleMonoidal.{uR, max uA v}
  let : MonoidalCategory (ModuleCat.{max uR uA v} A) :=
    ModuleCat.liftedModuleMonoidal.{uA, max uR v}
  intro η hη
  let F := extensionScalars.{uR,uA,v} (algebraMap R A)
  let K := P.complex
  let FK := extC.{uR, uA, v} (algebraMap R A) K
  have hμe (x y : K.X 0) :
      P.π.f 0 (μ.f 0 (HomologicalComplex.ιTensorObj K K 0 0 0 rfl (x ⊗ₜ[R] y))) =
        @HMul.hMul (liftedAlgebra R A B) (liftedAlgebra R A B) (liftedAlgebra R A B)
          inferInstance (P.π.f 0 x) (P.π.f 0 y) :=
    congrArg (fun t => t (x ⊗ₜ[R] y)) hμ
  obtain ⟨Hl⟩ := resolution_one_mul.{uR, max uA v} (liftedAlgebra R A B) P μ hμe η hη
  obtain ⟨Hr⟩ := resolution_mul_one.{uR, max uA v} (liftedAlgebra R A B) P μ hμe η hη
  obtain ⟨Ha⟩ := resolution_mul_assoc.{uR, max uA v} (liftedAlgebra R A B) P μ hμe
  have hF {g : K ⟶ K} (H : Homotopy g (𝟙 K)) :
      Homotopy (scalarComplexMap R A (algebraMap R A) g) (𝟙 FK) := by
    simpa only [CategoryTheory.Functor.map_id] using F.mapHomotopy H
  let e : FK.X 0 := by
    let := f.toAlgebra
    exact (1 : A) ⊗ₜ[R] η.f 0 (ULift.up (1 : R))
  obtain ⟨one, hone⟩ := torRep_of_cycle R A B P 0 e (by simp)
  apply algebra_exists_of_nonneg R A B one
  · intro n a
    obtain ⟨x, hx⟩ := torRep_exists R A B P n a
    have hp := torRep_product R A B P μ hμ 0 n n (zero_add n) hone hx
    dsimp only [e] at hp
    rw [scalarProductMap_one_left] at hp
    apply (P.isoLeftDerivedObj F n).toLinearEquiv.injective
    exact homologyRep_homotopy.{uA, max uR v} (hF Hl) x (homologyRep_d.{uA, max uR v} hx _) hp hx
  · intro n a
    obtain ⟨x, hx⟩ := torRep_exists R A B P n a
    have hp := torRep_product R A B P μ hμ n 0 n (add_zero n) hx hone
    dsimp only [e] at hp
    rw [scalarProductMap_one_right] at hp
    apply (P.isoLeftDerivedObj F n).toLinearEquiv.injective
    exact homologyRep_homotopy.{uA, max uR v} (hF Hr) x (homologyRep_d.{uA, max uR v} hx _) hp hx
  · intro p q r a b c
    obtain ⟨x, hx⟩ := torRep_exists R A B P p a
    obtain ⟨y, hy⟩ := torRep_exists R A B P q b
    obtain ⟨z, hz⟩ := torRep_exists R A B P r c
    have hxy := torRep_product R A B P μ hμ p q (p+q) rfl hx hy
    have hyz := torRep_product R A B P μ hμ q r (q+r) rfl hy hz
    have hl := torRep_product R A B P μ hμ (p+q) r (p+(q+r)) (Nat.add_assoc p q r) hxy hz
    have hr := torRep_product R A B P μ hμ p (q+r) (p+(q+r)) rfl hx hyz
    rw [scalarProductMap_assoc_left] at hl
    rw [scalarProductMap_assoc_right R A (algebraMap R A) K μ p q r (p+(q+r))
      (Nat.add_assoc p q r) x y z] at hr
    let M := liftedModule R A B
    let T := projectiveResolution
      ((RingTheory.TorProducts.tensorBifunctor.{uR, max uA v} R).obj (M, M))
    obtain ⟨C⟩ := RingTheory.TorProducts.torProduct_resolution.{uR, uA, v} R A p q M M P P T
    have hi := homologyRep_map.{uA, max uR v} (scalarTensorComplexMap R A (algebraMap R A) K K)
      (homologyRep_product.{uR, uA, v} C.cohomologyProduct hx hy)
    let w := HomologicalComplex.ιTensorObj (extC.{uR, uA, v} (algebraMap R A) (K ⊗ K)) FK
      (p+q) r (p+(q+r)) (Nat.add_assoc p q r)
      (scalarTensorSummand R A (algebraMap R A) K K p q (p+q) rfl (x ⊗ₜ[A] y) ⊗ₜ[A] z)
    have hw : (extC.{uR, uA, v} (algebraMap R A) (K ⊗ K) ⊗ FK).d
        (p+(q+r)) ((ComplexShape.down ℕ).next (p+(q+r))) w = 0 :=
      homologyRep_tensor_cycle.{uA, max uR v} hi hz _ _ (Nat.add_assoc p q r)
    obtain ⟨d, hd⟩ := homologyRep_of_cycle.{uA, max uR v} w hw
    have hs := homologyRep_map.{uA, max uR v}
      (scalarTensorComplexMap R A (algebraMap R A) (K ⊗ K) K) hd
    apply (P.isoLeftDerivedObj F (p+(q+r))).toLinearEquiv.injective
    exact homologyRep_homotopy.{uA, max uR v} (F.mapHomotopy Ha) _
      (homologyRep_d.{uA, max uR v} hs _) hl hr

end GradedTor

/-- For each `R`-algebra there is a unique unital associative graded algebra structure on Tor
whose multiplication in nonnegative degrees is the Tor cross product followed by
multiplication on the algebra. -/
@[sga "6 VII 2.1" "partial"]
public theorem GradedTor.existsUnique_algebra (R : Type uR) (A : Type uA)
    [CommRing R] [CommRing A] [_root_.Algebra R A] (B : AlgCat.{v, uR} R) :
    ∃! _ : GradedTor.Algebra.{uR, uA, v} R A B, True := by
  let P := projectiveResolution (GradedTor.liftedModule R A B)
  obtain ⟨μ, hμ⟩ := GradedTor.resolution_multiplication_exists R A B P
  obtain ⟨η, hη⟩ := resolution_unit_exists.{uR, max uA v} (GradedTor.liftedAlgebra R A B) P
  obtain ⟨X⟩ := GradedTor.algebra_exists_of_resolution R A B P μ hμ η hη
  have := GradedTor.algebra_subsingleton R A B
  exact ⟨X, trivial, fun Y _ => Subsingleton.elim Y X⟩

end
