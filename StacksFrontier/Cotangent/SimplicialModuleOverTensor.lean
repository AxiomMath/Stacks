module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import StacksFrontier.AlgebraicTopology.SimplicialTensorConnectivity

/-!
# Simplicial modules over a simplicial ring, and their degreewise tensor product

Let `P_•` be a simplicial commutative `A`-algebra. A *simplicial module over `P_•`* is a family of
`Pₙ`-modules `Mₙ` with simplicial operators `θ^* : Mₙ → Mₘ` which are semilinear along the
operators of `P_•`. Such an object has an underlying simplicial `A`-module, and two of them have a
degreewise tensor product `n ↦ Mₙ ⊗_{Pₙ} Nₙ`, again a simplicial module over `P_•`. On the
standard resolution `P_• → B` this is how the sheaves of `𝒪`-modules of the site `C_{B/A}`, and
their tensor products over `𝒪`, are evaluated (Stacks, Tag 08PS).

## Main definitions

* `Stacks.Cotangent.SimplicialModuleOver`: a simplicial module over `P_•`.
* `Stacks.Cotangent.SimplicialModuleOver.toSimplicial`: its underlying simplicial `A`-module.
* `Stacks.Cotangent.SimplicialModuleOver.tensor`: the degreewise tensor product over `P_•`.
* `Stacks.Cotangent.SimplicialModuleOver.Hom.lTensor`: a morphism tensored on the left.

## Main results

* `Stacks.Cotangent.SimplicialModuleOver.isZero_homology_zero_tensor`: if the Moore complex of
  `M` has vanishing `H₀`, so has that of `M ⊗_{P_•} N`, for any `N`.
* `Stacks.Cotangent.isZero_homology_zero_iff_exists_δ_sub_δ`: `H₀` of the Moore complex of a
  simplicial module vanishes exactly when every `0`-simplex is `δ₀ u - δ₁ u`.

## Implementation notes

The structure carries its algebraic structure as instance fields, made instances only in the
`SimplicialModuleOver` scope: as global instances they would be tried, through the projection
`SimplicialModuleOver.obj`, on every module of the library. Concrete simplicial modules are
declared as `abbrev`s, so that the projections of their fields reduce and the instances of their
terms are the usual ones. The tensor product's operator `SimplicialModuleOver.tensorMap` is
stated on the raw tensor products, so that lemmas about it are rewritable against them.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial AlgebraicTopology
open scoped TensorProduct

universe u w

namespace Stacks.Cotangent

variable {A : Type u} [CommRing A] (P : SimplicialObject (CommAlgCat.{w} A))

/-- A simplicial module over the simplicial commutative `A`-algebra `P`. -/
structure SimplicialModuleOver where
  /-- The term in each simplicial degree. -/
  obj : SimplexCategoryᵒᵖ → Type w
  [addCommGroup (n : SimplexCategoryᵒᵖ) : AddCommGroup (obj n)]
  [module (n : SimplexCategoryᵒᵖ) : Module (P.obj n) (obj n)]
  [moduleBase (n : SimplexCategoryᵒᵖ) : Module A (obj n)]
  [isScalarTower (n : SimplexCategoryᵒᵖ) : IsScalarTower A (P.obj n) (obj n)]
  /-- The simplicial operators. -/
  map {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) : obj n →+ obj m
  map_smul {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) (p : P.obj n) (x : obj n) :
    map f (p • x) = (P.map f).hom p • map f x
  map_id (n : SimplexCategoryᵒᵖ) (x : obj n) : map (𝟙 n) x = x
  map_comp {n m k : SimplexCategoryᵒᵖ} (f : n ⟶ m) (g : m ⟶ k) (x : obj n) :
    map (f ≫ g) x = map g (map f x)

namespace SimplicialModuleOver

attribute [scoped instance] addCommGroup module moduleBase isScalarTower

variable {P} (M N : SimplicialModuleOver P)

/-- The simplicial operators are `A`-linear. -/
theorem map_smul_base {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) (a : A) (x : M.obj n) :
    M.map f (a • x) = a • M.map f x := by
  rw [← algebraMap_smul (P.obj n) a x, M.map_smul, ← algebraMap_smul (P.obj m) a (M.map f x)]
  congr 1
  exact (P.map f).hom.commutes a

/-- A simplicial operator, as an `A`-linear map. -/
def mapLinear {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) : M.obj n →ₗ[A] M.obj m where
  toFun := M.map f
  map_add' := map_add (M.map f)
  map_smul' := M.map_smul_base f

/-- `mapLinear` is the simplicial operator. -/
@[simp]
theorem mapLinear_apply {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) (x : M.obj n) :
    M.mapLinear f x = M.map f x := rfl

/-- The underlying simplicial `A`-module. -/
def toSimplicial : SimplicialObject (ModuleCat.{w} A) where
  obj n := ModuleCat.of A (M.obj n)
  map f := ModuleCat.ofHom (M.mapLinear f)
  map_id n := by
    ext x
    exact M.map_id n x
  map_comp f g := by
    ext x
    exact M.map_comp f g x

/-- The simplicial operators of the underlying simplicial `A`-module. -/
@[simp]
theorem toSimplicial_map_apply {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) (x : M.obj n) :
    (M.toSimplicial.map f).hom x = M.map f x := rfl

/-- A morphism of simplicial modules over `P`. -/
@[ext]
structure Hom where
  /-- The component in each degree. -/
  app (n : SimplexCategoryᵒᵖ) : M.obj n →ₗ[P.obj n] N.obj n
  naturality {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) (x : M.obj n) :
    app m (M.map f x) = N.map f (app n x)

variable {M N}

/-- The underlying morphism of simplicial `A`-modules. -/
def Hom.toSimplicial (g : M.Hom N) : M.toSimplicial ⟶ N.toSimplicial where
  app n := ModuleCat.ofHom ((g.app n).restrictScalars A)
  naturality _ _ f := by
    ext x
    exact g.naturality f x

/-- The components of the underlying morphism of simplicial `A`-modules. -/
@[simp]
theorem Hom.toSimplicial_app_apply (g : M.Hom N) (n : SimplexCategoryᵒᵖ) (x : M.obj n) :
    (g.toSimplicial.app n).hom x = g.app n x := rfl

variable (M N)

/-- The simplicial operator of the degreewise tensor product, before bundling. -/
def tensorMap {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) :
    M.obj n ⊗[P.obj n] N.obj n →+ M.obj m ⊗[P.obj m] N.obj m :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (fun y => M.map f x ⊗ₜ N.map f y)
      (fun y y' => by rw [map_add, TensorProduct.tmul_add]))
      (fun x x' => by ext y; simp [map_add, TensorProduct.add_tmul]))
    (fun p x y => by
      simp only [AddMonoidHom.mk'_apply]
      rw [M.map_smul, N.map_smul, TensorProduct.smul_tmul])

/-- The simplicial operator of the tensor product on a pure tensor. -/
@[simp]
theorem tensorMap_tmul {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) (x : M.obj n) (y : N.obj n) :
    tensorMap M N f (x ⊗ₜ y) = M.map f x ⊗ₜ N.map f y := rfl

/-- The degreewise tensor product `n ↦ Mₙ ⊗_{Pₙ} Nₙ` of two simplicial modules over `P`. -/
abbrev tensor : SimplicialModuleOver P where
  obj n := M.obj n ⊗[P.obj n] N.obj n
  map f := tensorMap M N f
  map_smul f p t := by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      rw [TensorProduct.smul_tmul', tensorMap_tmul, tensorMap_tmul, M.map_smul,
        TensorProduct.smul_tmul']
    | add s t hs ht => rw [smul_add, map_add, map_add, hs, ht, smul_add]
  map_id n t := by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => rw [tensorMap_tmul, M.map_id, N.map_id]
    | add s t hs ht => rw [map_add, hs, ht]
  map_comp f g t := by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => rw [tensorMap_tmul, tensorMap_tmul, tensorMap_tmul, M.map_comp, N.map_comp]
    | add s t hs ht => rw [map_add, hs, ht, map_add, map_add]

/-- The simplicial operators of the tensor product commute with tensoring a morphism in the
second factor. -/
theorem lTensor_tensorMap {N' : SimplicialModuleOver P} (g : N.Hom N') {n m : SimplexCategoryᵒᵖ}
    (f : n ⟶ m) (t : M.obj n ⊗[P.obj n] N.obj n) :
    LinearMap.lTensor (M.obj m) (g.app m) (tensorMap M N f t) =
      tensorMap M N' f (LinearMap.lTensor (M.obj n) (g.app n) t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    rw [tensorMap_tmul, LinearMap.lTensor_tmul, LinearMap.lTensor_tmul, tensorMap_tmul,
      g.naturality]
  | add s t hs ht => rw [map_add, map_add, hs, ht, map_add, map_add]

/-- A morphism in the second factor, tensored on the left with `M`. -/
def Hom.lTensor {N' : SimplicialModuleOver P} (g : N.Hom N') :
    (M.tensor N).Hom (M.tensor N') where
  app n := LinearMap.lTensor (M.obj n) (g.app n)
  naturality f t := lTensor_tensorMap M N g f t

/-- A morphism tensored on the left, on a pure tensor. -/
@[simp]
theorem Hom.lTensor_app_tmul {N' : SimplicialModuleOver P} (g : N.Hom N')
    (n : SimplexCategoryᵒᵖ) (x : M.obj n) (y : N.obj n) :
    (Hom.lTensor M N g).app n (x ⊗ₜ y) = x ⊗ₜ g.app n y := rfl

/-- The zeroth degeneracy is a section of both faces from degree one to degree zero. -/
theorem map_δ_map_σ_zero (i : Fin 2) (y : N.obj (op ⦋0⦌)) :
    N.map (SimplexCategory.δ i).op (N.map (SimplexCategory.σ (0 : Fin 1)).op y) = y := by
  rw [← N.map_comp, ← op_comp]
  have h : SimplexCategory.δ i ≫ SimplexCategory.σ (0 : Fin 1) = 𝟙 _ := by
    fin_cases i
    · exact SimplexCategory.δ_comp_σ_self
    · exact SimplexCategory.δ_comp_σ_succ
  rw [h, op_id, N.map_id]

/-- **`H₀` of a degreewise tensor product vanishes as soon as `H₀` of one factor does**, read
on elements: if every `0`-simplex of `M` is `δ₀ u - δ₁ u` for a `1`-simplex `u`, the same holds
for `M ⊗_P N`. A pure tensor `x ⊗ y` is `δ₀ v - δ₁ v` for `v = u ⊗ σ₀ y`. -/
theorem exists_tensor_δ_sub_δ
    (hM : ∀ x : M.obj (op ⦋0⦌), ∃ u : M.obj (op ⦋1⦌),
      M.map (SimplexCategory.δ 0).op u - M.map (SimplexCategory.δ 1).op u = x)
    (t : M.obj (op ⦋0⦌) ⊗[P.obj (op ⦋0⦌)] N.obj (op ⦋0⦌)) :
    ∃ v : M.obj (op ⦋1⦌) ⊗[P.obj (op ⦋1⦌)] N.obj (op ⦋1⦌),
      tensorMap M N (SimplexCategory.δ 0).op v - tensorMap M N (SimplexCategory.δ 1).op v = t := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul x y =>
    obtain ⟨u, hu⟩ := hM x
    refine ⟨u ⊗ₜ N.map (SimplexCategory.σ (0 : Fin 1)).op y, ?_⟩
    rw [tensorMap_tmul, tensorMap_tmul, map_δ_map_σ_zero, map_δ_map_σ_zero,
      ← TensorProduct.sub_tmul, hu]
  | add s t hs ht =>
    obtain ⟨v, hv⟩ := hs
    obtain ⟨v', hv'⟩ := ht
    refine ⟨v + v', ?_⟩
    rw [map_add, map_add, ← hv, ← hv']
    abel

end SimplicialModuleOver

/-- `H₀` of the Moore complex of a simplicial module vanishes exactly when every `0`-simplex is
`δ₀ u - δ₁ u` for some `1`-simplex `u`. -/
theorem isZero_homology_zero_iff_exists_δ_sub_δ (X : SimplicialObject (ModuleCat.{w} A)) :
    IsZero (((alternatingFaceMapComplex (ModuleCat.{w} A)).obj X).homology 0) ↔
      ∀ x : X.obj (op ⦋0⦌), ∃ u : X.obj (op ⦋1⦌),
        (X.δ (0 : Fin 2)).hom u - (X.δ (1 : Fin 2)).hom u = x := by
  let D := (alternatingFaceMapComplex (ModuleCat.{w} A)).obj X
  change IsZero (D.homology 0) ↔ _
  rw [← D.exactAt_iff_isZero_homology,
    D.exactAt_iff' 1 0 ((ComplexShape.down ℕ).next 0) (by simp) rfl,
    ShortComplex.exact_iff_epi _ (by
      change D.d 0 _ = 0
      exact D.shape _ _ (by simp)),
    ModuleCat.epi_iff_surjective]
  change Function.Surjective ((AlternatingFaceMapComplex.obj X).d 1 0).hom ↔ _
  rw [AlternatingFaceMapComplex.obj_d_eq X 0]
  simp [Fin.sum_univ_two, sub_eq_add_neg, Function.Surjective]

/-- The totally degenerate map `P₀ → Pₙ`, induced by the unique map `⦋n⦌ → ⦋0⦌`. -/
def degenerateMap (n : SimplexCategoryᵒᵖ) : P.obj (op ⦋0⦌) →ₐ[A] P.obj n :=
  (P.map (SimplexCategory.const n.unop ⦋0⦌ 0).op).hom

/-- The totally degenerate maps are compatible with the simplicial operators. -/
theorem map_degenerateMap {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) (r : P.obj (op ⦋0⦌)) :
    (P.map f).hom (degenerateMap P n r) = degenerateMap P m r := by
  have h : f.unop ≫ SimplexCategory.const n.unop ⦋0⦌ 0 = SimplexCategory.const m.unop ⦋0⦌ 0 := by
    ext i
    exact congrArg Fin.val (Subsingleton.elim (α := Fin 1) _ _)
  have h' : (SimplexCategory.const n.unop ⦋0⦌ 0).op ≫ f =
      (SimplexCategory.const m.unop ⦋0⦌ 0).op := by
    rw [← h]
    rfl
  change (P.map (SimplexCategory.const n.unop ⦋0⦌ 0).op ≫ P.map f).hom r = _
  rw [← P.map_comp, h']
  rfl

namespace SimplicialModuleOver

variable {P} (M N : SimplicialModuleOver P)

/-- The term of `M` in degree `n`, to be read as a `P₀`-module through the totally degenerate
map `P₀ → Pₙ`. -/
def ObjZero (n : SimplexCategoryᵒᵖ) : Type w := M.obj n

/-- The term read over `P₀` is the same abelian group. -/
instance (n : SimplexCategoryᵒᵖ) : AddCommGroup (M.ObjZero n) :=
  inferInstanceAs (AddCommGroup (M.obj n))

/-- `P₀` acts through the totally degenerate map `P₀ → Pₙ`. -/
instance (n : SimplexCategoryᵒᵖ) : Module (P.obj (op ⦋0⦌)) (M.ObjZero n) :=
  Module.compHom (M.obj n) (degenerateMap P n).toRingHom

/-- The identification of a term read over `P₀` with the term itself. -/
def objZeroEquiv (n : SimplexCategoryᵒᵖ) : M.ObjZero n ≃ M.obj n := Equiv.refl _

/-- The action of `P₀` on a term is the action of its totally degenerate image. -/
theorem objZeroEquiv_smul (n : SimplexCategoryᵒᵖ) (r : P.obj (op ⦋0⦌)) (x : M.ObjZero n) :
    M.objZeroEquiv n (r • x) = degenerateMap P n r • M.objZeroEquiv n x := rfl

/-- A simplicial operator, as a `P₀`-linear map. -/
def mapLinearZero {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) :
    M.ObjZero n →ₗ[P.obj (op ⦋0⦌)] M.ObjZero m where
  toFun := M.map f
  map_add' := map_add (M.map f)
  map_smul' r x := by
    change M.map f ((degenerateMap P n r) • M.objZeroEquiv n x) =
      (degenerateMap P m r) • M.map f (M.objZeroEquiv n x)
    rw [M.map_smul, map_degenerateMap]

/-- The underlying simplicial `P₀`-module: every term is a `P₀`-module through the totally
degenerate map, and the simplicial operators are `P₀`-linear. -/
def toSimplicialZero : SimplicialObject (ModuleCat.{w} (P.obj (op ⦋0⦌))) where
  obj n := ModuleCat.of _ (M.ObjZero n)
  map f := ModuleCat.ofHom (M.mapLinearZero f)
  map_id n := by
    ext x
    exact M.map_id n x
  map_comp f g := by
    ext x
    exact M.map_comp f g x

variable {M N} in
/-- A morphism, as a `P₀`-linear map in one degree. -/
def Hom.appZero (g : M.Hom N) (n : SimplexCategoryᵒᵖ) :
    M.ObjZero n →ₗ[P.obj (op ⦋0⦌)] N.ObjZero n where
  toFun := g.app n
  map_add' := map_add (g.app n)
  map_smul' r x := (g.app n).map_smul (degenerateMap P n r) x

variable {M N} in
/-- The underlying morphism of simplicial `P₀`-modules. -/
def Hom.toSimplicialZero (g : M.Hom N) : M.toSimplicialZero ⟶ N.toSimplicialZero where
  app n := ModuleCat.ofHom (g.appZero n)
  naturality _ _ f := by
    ext x
    exact g.naturality f x

/-- **`H₀(M ⊗_P N) = 0` as soon as `H₀(M) = 0`.** -/
theorem isZero_homology_zero_tensor
    (hM : IsZero (((alternatingFaceMapComplex (ModuleCat.{w} A)).obj M.toSimplicial).homology 0)) :
    IsZero (((alternatingFaceMapComplex (ModuleCat.{w} A)).obj
      (M.tensor N).toSimplicial).homology 0) := by
  rw [isZero_homology_zero_iff_exists_δ_sub_δ] at hM ⊢
  exact exists_tensor_δ_sub_δ M N hM

end SimplicialModuleOver

/-- Vanishing of the homology of the Moore complex of a simplicial module can be read after
forgetting to abelian groups. -/
theorem isZero_homology_iff_forget₂ {R : Type*} [Ring R] (X : SimplicialObject (ModuleCat.{w} R))
    (n : ℕ) :
    IsZero (((alternatingFaceMapComplex (ModuleCat.{w} R)).obj X).homology n) ↔
      IsZero (((alternatingFaceMapComplex AddCommGrpCat.{w}).obj
        (X ⋙ forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w})).homology n) := by
  let F := forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w}
  have e : ((alternatingFaceMapComplex AddCommGrpCat.{w}).obj (X ⋙ F)).homology n ≅
      F.obj (((alternatingFaceMapComplex (ModuleCat.{w} R)).obj X).homology n) :=
    ((HomologicalComplex.homologyFunctor _ _ n).mapIso
        ((alternatingFaceMapComplexCompMapHomologicalComplexIso F).app X)).symm ≪≫
      (((alternatingFaceMapComplex (ModuleCat.{w} R)).obj X).sc n).mapHomologyIso F
  rw [e.isZero_iff, ModuleCat.isZero_iff_subsingleton, AddCommGrpCat.isZero_iff_subsingleton]
  rfl

namespace SimplicialModuleOver

variable {P} (M : SimplicialModuleOver P)

/-- The homology of the Moore complex of a simplicial module over `P` vanishes over `P₀` exactly
when it vanishes over `A`: both are read on the same abelian groups. -/
theorem isZero_homology_toSimplicialZero_iff (n : ℕ) :
    IsZero (((alternatingFaceMapComplex (ModuleCat.{w} (P.obj (op ⦋0⦌)))).obj
      M.toSimplicialZero).homology n) ↔
      IsZero (((alternatingFaceMapComplex (ModuleCat.{w} A)).obj M.toSimplicial).homology n) := by
  rw [isZero_homology_iff_forget₂, isZero_homology_iff_forget₂]
  rfl

end SimplicialModuleOver

end Stacks.Cotangent
