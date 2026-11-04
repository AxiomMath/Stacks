module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.LinearCupProduct

/-!
# Naturality of the Čech cup product

The Čech cup product of [Stacks, Tag 07MB] is natural in the coefficient complexes: for cochain
maps `f : K ⟶ K'`, `g : L ⟶ L'`, `h : M ⟶ M'` carrying a pairing `D` of `(K, L)` into `M` to a
pairing `D'` of `(K', L')` into `M'`, the square

```
Tot(Tot(Č(W,K)) ⊗ Tot(Č(W,L))) ── cup D ──→ Tot(Č(W,M))
        │                                       │
        ↓                                       ↓
Tot(Tot(Č(W,K')) ⊗ Tot(Č(W,L'))) ── cup D' ─→ Tot(Č(W,M'))
```

commutes.

## Main results

* `Stacks.Cech.LinearCupProduct.ιTotalCechTo_totalCechComplexFunctor_map`: the total Čech complex
  on a summand of a cochain map.
* `Stacks.Cech.LinearCupProduct.cechCupProduct_natural_of_pairing_hom`: **the naturality.**
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite
open Stacks.CategoryTheory.CechComplex
open Stacks.Cech.CupProduct (tensorModules tensorModulesMap tensorModulesMap_comp cupProductSign)
open scoped TensorProduct

universe w uR uC vC u

namespace Stacks.Cech.LinearCupProduct

attribute [local instance] ModuleCat.hasLimitsOfSize ModuleCat.hasColimitsOfSize

variable {C : Type uC} [Category.{vC} C] [HasFiniteProducts C] {ι : Type w} [UnivLE.{w, u}]
  (W : ι → C) (R : Type u) [CommRing R]

omit [UnivLE.{w, u}] in
private theorem paste_extend {D : Type*} [Category* D] {x y z z' y' x' : D} (ei : x ⟶ y)
    (eh : y ⟶ x) (hinv : ei ≫ eh = 𝟙 x) (ιT : y ⟶ z) (tm : z ⟶ z') (φ : y ⟶ y') (ιT' : y' ⟶ z')
    (h1 : ιT ≫ tm = φ ≫ ιT') (c : x ⟶ x') (ei' : x' ⟶ y') (h2 : φ = eh ≫ c ≫ ei') :
    (ei ≫ ιT) ≫ tm = c ≫ ei' ≫ ιT' := by
  rw [Category.assoc, h1, h2]
  simp only [Category.assoc, reassoc_of% hinv]

/-- **The total Čech complex of a cochain map on a summand** is the map of Čech cochains in that
coefficient degree. -/
theorem ιTotalCechTo_totalCechComplexFunctor_map
    {K K' : CochainComplex (PresheafModules.{u} C R) ℤ} (f : K ⟶ K') (p : ℕ) (a n : ℤ)
    (h : (p : ℤ) + a = n) :
    ιTotalCechTo W R K p a n h ≫ ((totalCechComplexFunctor W R).map f).f n =
      cechCochainsMap W R (f.f a) p ≫ ιTotalCechTo W R K' p a n h := by
  have hmap : (totalCechComplexFunctor W R).map f =
      HomologicalComplex₂.total.map ((HomologicalComplex₂.flipFunctor (ModuleCat.{u} R) (up ℤ)
        (up ℤ)).map (((cechComplexFunctorInt W R).mapHomologicalComplex (up ℤ)).map f)) (up ℤ) :=
    rfl
  have hf := cechExtendMap_f W R (f.f a) p (rfl : (p : ℤ) = p)
  rw [hmap]
  exact paste_extend _ _ (Iso.inv_hom_id _) _ _ _ _
    (HomologicalComplex₂.ιTotal_map _ _ _ _ _ _ _ h) _ _ hf

variable {K L M K' L' M' : CochainComplex (PresheafModules.{u} C R) ℤ}

omit [HasFiniteProducts C] [UnivLE.{w, u}] in
private theorem tm_comp {M₁ M₂ M₃ N₁ N₂ N₃ : ModuleCat.{u} R} (a : M₁ ⟶ M₂) (b : N₁ ⟶ N₂)
    (c : M₂ ⟶ M₃) (d : N₂ ⟶ N₃) :
    tensorModulesMap R a b ≫ ((tensorModules R).map c).app N₂ ≫ ((tensorModules R).obj M₃).map d =
      tensorModulesMap R (a ≫ c) (b ≫ d) := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  rfl

/-- The source of the Čech cup product on a homogeneous summand, after cochain maps in both
coefficient complexes. -/
theorem ιTensorSource_mapBifunctorMap (f : K ⟶ K') (g : L ⟶ L') (r s : ℕ) (a b n : ℤ)
    (h : ((r : ℤ) + a) + ((s : ℤ) + b) = n) :
    ιTensorSource W R K L r s a b n h ≫
        (HomologicalComplex.mapBifunctorMap ((totalCechComplexFunctor W R).map f)
          ((totalCechComplexFunctor W R).map g) (tensorModules R) (up ℤ)).f n =
      tensorModulesMap R (cechCochainsMap W R (f.f a) r) (cechCochainsMap W R (g.f b) s) ≫
        ιTensorSource W R K' L' r s a b n h := by
  rw [ιTensorSource, Category.assoc, HomologicalComplex.ι_mapBifunctorMap, ιTensorSource,
    ← Category.assoc, ← Category.assoc, Category.assoc (tensorModulesMap _ _ _), tm_comp,
    ← Category.assoc, tensorModulesMap_comp]
  congr 2 <;> apply ιTotalCechTo_totalCechComplexFunctor_map

/-- **The Čech cup product of [Stacks, Tag 07MB] is natural in the coefficient complexes**: for
cochain maps `f`, `g`, `h` carrying the pairing `D` to the pairing `D'`, the cup product of `D`
followed by `h` on total Čech complexes is the tensor product of the maps induced by `f` and `g`
followed by the cup product of `D'`. -/
theorem cechCupProduct_natural_of_pairing_hom (D : ComplexPairing R K L M)
    (D' : ComplexPairing R K' L' M')
    (f : K ⟶ K') (g : L ⟶ L') (h : M ⟶ M')
    (hD : ∀ (a b n : ℤ) (hab : a + b = n),
      ((tensorPresheafModules.{u} R).map (f.f a)).app (L.X b) ≫
          ((tensorPresheafModules.{u} R).obj (K'.X a)).map (g.f b) ≫ D'.μ a b n hab =
        D.μ a b n hab ≫ h.f n) :
    HomologicalComplex.mapBifunctorMap ((totalCechComplexFunctor W R).map f)
        ((totalCechComplexFunctor W R).map g) (tensorModules R) (up ℤ) ≫ cechCupProduct W R D' =
      cechCupProduct W R D ≫ (totalCechComplexFunctor W R).map h := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  refine ιTensorSource_hom_ext W R K L fun r s a b hn => ?_
  simp only [HomologicalComplex.comp_f]
  rw [reassoc_of% ιTensorSource_mapBifunctorMap W R f g r s a b n hn]
  show _ ≫ ιTensorSource W R K' L' r s a b n hn ≫ cechCupProductDegree W R D' n =
    (ιTensorSource W R K L r s a b n hn ≫ cechCupProductDegree W R D n) ≫ _
  rw [ιTensorSource_cechCupProductDegree, ιTensorSource_cechCupProductDegree,
    cechCupProductSummand_eq, cechCupProductSummand_eq, Preadditive.comp_zsmul,
    Preadditive.zsmul_comp]
  congr 1
  rw [← ιPairingTarget_eq W R D r s (r + s) a b (a + b) n rfl rfl (by push_cast; omega),
    ← ιPairingTarget_eq W R D' r s (r + s) a b (a + b) n rfl rfl (by push_cast; omega),
    Category.assoc, ιTotalCechTo_totalCechComplexFunctor_map, ← Category.assoc,
    ← Category.assoc, cechAlexanderWhitneyTo_comp_cechCochainsMap, ← hD a b (a + b) rfl,
    cechAlexanderWhitneyTo_naturality_left, cechAlexanderWhitneyTo_naturality_right,
    ← Category.assoc, tensorModulesMap_comp, Category.comp_id, Category.id_comp]

end Stacks.Cech.LinearCupProduct
