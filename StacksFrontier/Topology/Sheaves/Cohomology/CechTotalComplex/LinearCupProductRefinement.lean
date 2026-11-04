module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.LinearCupProduct
public import StacksFrontier.Topology.Sheaves.Cohomology.CechRefinements.ModuleComplexRefinementMap
public import StacksFrontier.Topology.Sheaves.Cohomology.RecoveryC.TensorModulesAdditive

/-!
# Refinement and naturality of the linear Čech cup product

Let `C` be a thin category with finite products, `R` a commutative ring, and let `W : ι → C`
and `W' : ι' → C` be two families of objects with a refinement `c : ι' → ι`,
`W' j ⟶ W (c j)`.  For complexes of presheaves of `R`-modules on `C` the refinement induces a
morphism of total Čech complexes `Tot(Č(W, K)) ⟶ Tot(Č(W', K))`, natural in `K`, and the
Alexander--Whitney cup product of `Stacks.Cech.LinearCupProduct.cechCupProduct` commutes with
it.  The cup product is moreover natural in the coefficient complexes and their pairing.

## Main definitions

* `Stacks.Cech.LinearCupProduct.refinementInter`: the maps of intersections induced by a
  refinement.
* `Stacks.Cech.LinearCupProduct.cechRefinement`: the map of Čech complexes of a refinement.
* `Stacks.Cech.LinearCupProduct.totalCechRefinement`: the induced natural transformation of
  total Čech complexes.

## Main results

* `Stacks.Cech.LinearCupProduct.ιTotalCech_totalCechRefinement`: the refinement map on a
  homogeneous summand of the total complex.
* `Stacks.Cech.LinearCupProduct.cechCupProduct_refinement`: the cup product commutes with
  refinement.
* `Stacks.Cech.LinearCupProduct.cechCupProduct_naturality`: the cup product is natural in a
  pair of morphisms of coefficient complexes compatible with two pairings.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite
open Stacks.CategoryTheory.CechComplex
open Stacks.Cech.CupProduct (tensorModules tensorModulesMap tensorModulesMap_comp
  cupProductSign)

universe u w uC vC uR

namespace Stacks.Cech.LinearCupProduct

attribute [local instance] ModuleCat.hasLimitsOfSize ModuleCat.hasColimitsOfSize

attribute [local implicit_reducible] CategoryTheory.cechComplexFunctor
  HomologicalComplex₂.ofGradedObject
  HomologicalComplex₂.flip
  HomologicalComplex₂.flipFunctor
  ComplexShape.Embedding.extendFunctor
  CategoryTheory.Functor.mapBifunctorHomologicalComplex
  CategoryTheory.Functor.mapBifunctorHomologicalComplexObj
  CategoryTheory.GradedObject.mapBifunctor
  HomologicalComplex₂.totalFunctor

section Tensor

variable {R : Type uR} [CommRing R]

/-- The action of the tensor bifunctor on a pair of morphisms is `tensorModulesMap`. -/
@[reassoc]
theorem tensorModules_map_app_comp_map {M M' : ModuleCat.{u} R} {N N' : ModuleCat.{u} R}
    (f : M ⟶ M') (g : N ⟶ N') :
    ((tensorModules R).map f).app N ≫ ((tensorModules R).obj M').map g = tensorModulesMap R f g :=
  ModuleCat.hom_ext (TensorProduct.ext' fun _ _ => rfl)

/-- A morphism of tensor products of complexes on a homogeneous pure tensor. -/
@[reassoc]
theorem tensorModulesMap_ιMapBifunctor_mapBifunctorMap {i j : ℤ}
    {K K' L L' : CochainComplex (ModuleCat.{u} R) ℤ}
    [HomologicalComplex.HasMapBifunctor K L (tensorModules R) (up ℤ)]
    [HomologicalComplex.HasMapBifunctor K' L' (tensorModules R) (up ℤ)]
    (φ : K ⟶ K') (ψ : L ⟶ L') {M N : ModuleCat.{u} R} (f : M ⟶ K.X i) (g : N ⟶ L.X j)
    (n : ℤ) (h : i + j = n) :
    tensorModulesMap R f g ≫ HomologicalComplex.ιMapBifunctor K L (tensorModules R) (up ℤ) i j n h ≫
        (HomologicalComplex.mapBifunctorMap φ ψ (tensorModules R) (up ℤ)).f n =
      tensorModulesMap R (f ≫ φ.f i) (g ≫ ψ.f j) ≫
        HomologicalComplex.ιMapBifunctor K' L' (tensorModules R) (up ℤ) i j n h := by
  rw [HomologicalComplex.ι_mapBifunctorMap, tensorModules_map_app_comp_map_assoc, ← Category.assoc,
    tensorModulesMap_comp]

end Tensor

/-- `eqToHom` between two degrees of a complex commutes with the components of a morphism. -/
theorem eqToHom_comp_f {D : Type*} [Category D] [HasZeroMorphisms D] {K L : CochainComplex D ℤ}
    (φ : K ⟶ L) {n n' : ℤ} (h : n = n') :
    eqToHom (congrArg K.X h) ≫ φ.f n' = φ.f n ≫ eqToHom (congrArg L.X h) := by
  subst h
  simp

section Refinement

variable {C : Type uC} [Category.{vC} C] [HasFiniteProducts C] [Quiver.IsThin C]
  {ι ι' : Type w} [UnivLE.{w, u}] (W : ι → C) (W' : ι' → C) (R : Type uR) [CommRing R]
  (c : ι' → ι) (ρ : ∀ j, W' j ⟶ W (c j))

/-- The maps of formal intersections induced by a refinement `c`, `W' j ⟶ W (c j)`. -/
noncomputable def refinementInter (n : ℕ) (x : Fin (n + 1) → ι') :
    inter W' x ⟶ inter W (c ∘ x) :=
  Pi.lift fun a => interπ W' x a ≫ ρ (x a)

/-- The coefficient presheaf, read as a map to its composite with the identity functor. -/
def idCoeff (P : PresheafModules.{u} C R) : P ⟶ (𝟭 C).op ⋙ P where
  app _ := 𝟙 _

/-- **The map of Čech complexes of a refinement**: on the factor indexed by
`x : Fin (n + 1) → ι'` it is the factor indexed by `c ∘ x`, restricted along
`refinementInter`. -/
noncomputable def cechRefinement (P : PresheafModules.{u} C R) :
    (CategoryTheory.cechComplexFunctor W).obj P ⟶ (CategoryTheory.cechComplexFunctor W').obj P :=
  refinementMap W' W (𝟭 C) P P (idCoeff R P) c (refinementInter W W' c ρ)

/-- The component of `cechRefinement` at the factor indexed by `x` is the projection to the
factor indexed by `c ∘ x` followed by restriction along `refinementInter`. -/
@[reassoc (attr := simp)]
theorem cechRefinement_f_comp_π (P : PresheafModules.{u} C R) (n : ℕ) (x : Fin (n + 1) → ι') :
    (cechRefinement W W' R c ρ P).f n ≫ π W' P n x =
      π W P n (c ∘ x) ≫ P.map (refinementInter W W' c ρ n x).op := by
  rw [cechRefinement, refinementMap_comp_π]
  simp only [idCoeff, Category.id_comp]

/-- The refinement map of Čech complexes is natural in the coefficient presheaf. -/
theorem cechRefinement_naturality {P Q : PresheafModules.{u} C R} (f : P ⟶ Q) :
    (CategoryTheory.cechComplexFunctor W).map f ≫ cechRefinement W W' R c ρ Q =
      cechRefinement W W' R c ρ P ≫ (CategoryTheory.cechComplexFunctor W').map f :=
  refinementMap_naturality W' W (𝟭 C) P P (idCoeff R P) c
    (refinementInter W W' c ρ) (idCoeff R Q) f f
    (fun _ => (Category.comp_id _).trans (Category.id_comp _).symm)

/-- The refinement map of Čech complexes, as a natural transformation. -/
noncomputable def cechRefinementNatTrans :
    (CategoryTheory.cechComplexFunctor W :
        PresheafModules.{u} C R ⥤ CochainComplex (ModuleCat.{u} R) ℕ) ⟶
      CategoryTheory.cechComplexFunctor W' where
  app P := cechRefinement W W' R c ρ P
  naturality _ _ f := cechRefinement_naturality W W' R c ρ f

/-- The refinement map of the integer-indexed Čech complexes. -/
noncomputable def cechIntRefinement : cechComplexFunctorInt W R ⟶ cechComplexFunctorInt W' R :=
  Functor.whiskerRight (cechRefinementNatTrans W W' R c ρ)
    (embeddingUpNat.extendFunctor (ModuleCat.{u} R))

/-- **The refinement map of total Čech complexes**, natural in the complex of coefficient
presheaves. -/
noncomputable def totalCechRefinement :
    totalCechComplexFunctor W R ⟶ totalCechComplexFunctor W' R :=
  Functor.whiskerRight
    (Functor.whiskerRight (NatTrans.mapHomologicalComplex (cechIntRefinement W W' R c ρ) (up ℤ))
      (HomologicalComplex₂.flipFunctor (ModuleCat.{u} R) (up ℤ) (up ℤ)))
    (HomologicalComplex₂.totalFunctor (ModuleCat.{u} R) (up ℤ) (up ℤ) (up ℤ))

/-- The refinement map of total Čech complexes on a summand of the total complex, at an arbitrary
total degree. -/
@[reassoc]
theorem ιTotal_totalCechRefinement (K : CochainComplex (PresheafModules.{u} C R) ℤ)
    (p a n : ℤ) (h : p + a = n) :
    (totalCechBicomplex W R K).ιTotal (up ℤ) p a n h ≫
        ((totalCechRefinement W W' R c ρ).app K).f n =
      ((cechIntRefinement W W' R c ρ).app (K.X a)).f p ≫
        (totalCechBicomplex W' R K).ιTotal (up ℤ) p a n h :=
  HomologicalComplex₂.ιTotal_map (φ := (HomologicalComplex₂.flipFunctor
      (ModuleCat.{u} R) (up ℤ) (up ℤ)).map
      ((NatTrans.mapHomologicalComplex (cechIntRefinement W W' R c ρ) (up ℤ)).app K))
    (c₁₂ := up ℤ) (i₁ := p) (i₂ := a) (i₁₂ := n) (h := h)

/-- The refinement map of the integer-indexed Čech complexes in a nonnegative degree. -/
theorem cechIntRefinement_app_f (P : PresheafModules.{u} C R) (p : ℕ) :
    ((cechIntRefinement W W' R c ρ).app P).f (p : ℤ) =
      (cechExtendXIso W R P p rfl).hom ≫ (cechRefinement W W' R c ρ P).f p ≫
        (cechExtendXIso W' R P p rfl).inv :=
  HomologicalComplex.extendMap_f (cechRefinement W W' R c ρ P) embeddingUpNat rfl

/-- **The refinement map on a homogeneous summand of the total Čech complex** is the refinement
map of the Čech cochains of the coefficient in that degree. -/
@[reassoc]
theorem ιTotalCech_totalCechRefinement (K : CochainComplex (PresheafModules.{u} C R) ℤ)
    (p : ℕ) (a : ℤ) :
    ιTotalCech W R K p a ≫ ((totalCechRefinement W W' R c ρ).app K).f ((p : ℤ) + a) =
      (cechRefinement W W' R c ρ (K.X a)).f p ≫ ιTotalCech W' R K p a := by
  have hmap := HomologicalComplex₂.ιTotal_map
    (φ := (HomologicalComplex₂.flipFunctor (ModuleCat.{u} R) (up ℤ) (up ℤ)).map
      ((NatTrans.mapHomologicalComplex (cechIntRefinement W W' R c ρ) (up ℤ)).app K))
    (c₁₂ := up ℤ) (i₁ := (p : ℤ)) (i₂ := a) (i₁₂ := (p : ℤ) + a) (h := rfl)
  have hext : (((HomologicalComplex₂.flipFunctor (ModuleCat.{u} R) (up ℤ) (up ℤ)).map
      ((NatTrans.mapHomologicalComplex (cechIntRefinement W W' R c ρ) (up ℤ)).app K)).f
        (p : ℤ)).f a =
      (cechExtendXIso W R (K.X a) p rfl).hom ≫ (cechRefinement W W' R c ρ (K.X a)).f p ≫
        (cechExtendXIso W' R (K.X a) p rfl).inv :=
    HomologicalComplex.extendMap_f (cechRefinement W W' R c ρ (K.X a)) embeddingUpNat rfl
  dsimp only [ιTotalCech]
  refine (Category.assoc _ _ _).trans ?_
  refine (whisker_eq _ hmap).trans ?_
  rw [hext]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rfl

/-- **The Alexander--Whitney map commutes with refinement**: refining both cochains and then
taking the front/back product is taking the product and then refining. -/
@[reassoc]
theorem cechAlexanderWhitney_refinement {P Q T : PresheafModules.{u} C R}
    (μ : Pairing.{u} R P Q T) (r s : ℕ) :
    tensorModulesMap R ((cechRefinement W W' R c ρ P).f r) ((cechRefinement W W' R c ρ Q).f s) ≫
        cechAlexanderWhitney W' R μ r s =
      cechAlexanderWhitney W R μ r s ≫ (cechRefinement W W' R c ρ T).f (r + s) := by
  refine hom_ext W' T fun t => ?_
  rw [Category.assoc, cechAlexanderWhitney_comp_π, Category.assoc, cechRefinement_f_comp_π,
    ← Category.assoc, cechAlexanderWhitney_comp_π]
  dsimp only [awTerm, cechFaceRestriction]
  have hnat := μ.naturality (refinementInter W W' c ρ (r + s) t).op
  rw [tensorPresheafModules_map_app] at hnat
  rw [Category.assoc, ← hnat, ← Category.assoc, ← Category.assoc, tensorModulesMap_comp,
    tensorModulesMap_comp]
  congr 2
  · rw [← Category.assoc, cechRefinement_f_comp_π, Category.assoc, Category.assoc,
      ← P.map_comp, ← P.map_comp]
    exact whisker_eq _ (congrArg P.map (congrArg Quiver.Hom.op (Subsingleton.elim _ _)))
  · rw [← Category.assoc, cechRefinement_f_comp_π, Category.assoc, Category.assoc,
      ← Q.map_comp, ← Q.map_comp]
    exact whisker_eq _ (congrArg Q.map (congrArg Quiver.Hom.op (Subsingleton.elim _ _)))

/-- **The Čech cup product commutes with refinement**: refining the two factors and taking the
cup product for the finer family is taking the cup product and then refining. -/
theorem cechCupProduct_refinement {K L M : CochainComplex (PresheafModules.{u} C R) ℤ}
    (D : ComplexPairing R K L M) :
    HomologicalComplex.mapBifunctorMap ((totalCechRefinement W W' R c ρ).app K)
        ((totalCechRefinement W W' R c ρ).app L) (tensorModules R) (up ℤ) ≫
      cechCupProduct W' R D =
    cechCupProduct W R D ≫ (totalCechRefinement W W' R c ρ).app M := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  refine ιTensorSource_hom_ext W R K L fun r s a b h => ?_
  subst h
  have h₁ := cechCupProduct_ι W R D r s a b
  have h₂ := cechCupProduct_ι W' R D r s a b
  dsimp only [ιTensorSource]
  simp only [HomologicalComplex.comp_f, Category.assoc]
  have h₃ := tensorModulesMap_ιMapBifunctor_mapBifunctorMap_assoc (R := R)
    ((totalCechRefinement W W' R c ρ).app K) ((totalCechRefinement W W' R c ρ).app L)
    (ιTotalCech W R K r a) (ιTotalCech W R L s b) _ rfl ((cechCupProduct W' R D).f _)
  rw [h₃, ιTotalCech_totalCechRefinement,
    ιTotalCech_totalCechRefinement, ← tensorModulesMap_comp_assoc, h₂,
    reassoc_of% h₁, Preadditive.comp_zsmul, Preadditive.zsmul_comp]
  congr 1
  simp only [Category.assoc]
  rw [eqToHom_comp_f, ιTotalCech_totalCechRefinement_assoc, ← cechAlexanderWhitney_refinement_assoc]
  push_cast
  ring

end Refinement

section Naturality

variable {C : Type uC} [Category.{vC} C] [HasFiniteProducts C]
  {ι : Type w} [UnivLE.{w, u}] (W : ι → C) (R : Type uR) [CommRing R]

/-- The total Čech complex of a morphism on a homogeneous summand is the map of Čech cochains
induced by its component in that degree. -/
@[reassoc]
theorem ιTotalCech_map {K K' : CochainComplex (PresheafModules.{u} C R) ℤ} (f : K ⟶ K')
    (p : ℕ) (a : ℤ) :
    ιTotalCech W R K p a ≫ ((totalCechComplexFunctor W R).map f).f ((p : ℤ) + a) =
      cechCochainsMap W R (f.f a) p ≫ ιTotalCech W R K' p a := by
  have hmap := HomologicalComplex₂.ιTotal_map (φ := (HomologicalComplex₂.flipFunctor
      (ModuleCat.{u} R) (up ℤ) (up ℤ)).map
      (((cechComplexFunctorInt W R).mapHomologicalComplex (up ℤ)).map f))
    (c₁₂ := up ℤ) (i₁ := (p : ℤ)) (i₂ := a) (i₁₂ := (p : ℤ) + a) (h := rfl)
  have hext := cechExtendMap_f W R (f.f a) p (p' := (p : ℤ)) rfl
  dsimp only [ιTotalCech]
  refine (Category.assoc _ _ _).trans ?_
  refine (whisker_eq _ hmap).trans ?_
  refine (whisker_eq _ (eq_whisker hext _)).trans ?_
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rfl

/-- **The Čech cup product is natural in the coefficients.**  Let `f : K₁ ⟶ K₂` and
`g : L₂ ⟶ L₁` be morphisms of complexes of coefficient presheaves and `D₁`, `D₂` pairings of
`(K₁, L₁)` and `(K₂, L₂)` into `M` which agree on `K₁ ⊗ L₂`.  Then the two cup products agree
on `Tot(Č(W, K₁)) ⊗ Tot(Č(W, L₂))`. -/
theorem cechCupProduct_naturality {K₁ K₂ L₁ L₂ M : CochainComplex (PresheafModules.{u} C R) ℤ}
    (f : K₁ ⟶ K₂) (g : L₂ ⟶ L₁) (D₁ : ComplexPairing R K₁ L₁ M) (D₂ : ComplexPairing R K₂ L₂ M)
    (h : ∀ a b n (hn : a + b = n),
      ((tensorPresheafModules.{u} R).obj (K₁.X a)).map (g.f b) ≫ D₁.μ a b n hn =
        ((tensorPresheafModules.{u} R).map (f.f a)).app (L₂.X b) ≫ D₂.μ a b n hn) :
    HomologicalComplex.mapBifunctorMap (𝟙 _) ((totalCechComplexFunctor W R).map g)
        (tensorModules R) (up ℤ) ≫ cechCupProduct W R D₁ =
      HomologicalComplex.mapBifunctorMap ((totalCechComplexFunctor W R).map f) (𝟙 _)
        (tensorModules R) (up ℤ) ≫ cechCupProduct W R D₂ := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  refine ιTensorSource_hom_ext W R K₁ L₂ fun r s a b hn => ?_
  subst hn
  have h₁ := cechCupProduct_ι W R D₁ r s a b
  have h₂ := cechCupProduct_ι W R D₂ r s a b
  dsimp only [ιTensorSource]
  simp only [HomologicalComplex.comp_f, Category.assoc]
  have h₃ := tensorModulesMap_ιMapBifunctor_mapBifunctorMap_assoc (R := R)
    (𝟙 _) ((totalCechComplexFunctor W R).map g)
    (ιTotalCech W R K₁ r a) (ιTotalCech W R L₂ s b) _ rfl ((cechCupProduct W R D₁).f _)
  have h₄ := tensorModulesMap_ιMapBifunctor_mapBifunctorMap_assoc (R := R)
    ((totalCechComplexFunctor W R).map f) (𝟙 _)
    (ιTotalCech W R K₁ r a) (ιTotalCech W R L₂ s b) _ rfl ((cechCupProduct W R D₂).f _)
  rw [h₃, h₄, HomologicalComplex.id_f,
    HomologicalComplex.id_f, Category.comp_id, Category.comp_id, ιTotalCech_map, ιTotalCech_map]
  have e₁ : tensorModulesMap R (ιTotalCech W R K₁ r a)
      (cechCochainsMap W R (g.f b) s ≫ ιTotalCech W R L₁ s b) =
      tensorModulesMap R (𝟙 _) (cechCochainsMap W R (g.f b) s) ≫
        tensorModulesMap R (ιTotalCech W R K₁ r a) (ιTotalCech W R L₁ s b) := by
    rw [tensorModulesMap_comp, Category.id_comp]
  have e₂ : tensorModulesMap R (cechCochainsMap W R (f.f a) r ≫ ιTotalCech W R K₂ r a)
      (ιTotalCech W R L₂ s b) =
      tensorModulesMap R (cechCochainsMap W R (f.f a) r) (𝟙 _) ≫
        tensorModulesMap R (ιTotalCech W R K₂ r a) (ιTotalCech W R L₂ s b) := by
    rw [tensorModulesMap_comp, Category.id_comp]
  rw [reassoc_of% e₁, reassoc_of% e₂, h₁, h₂, Preadditive.comp_zsmul, Preadditive.comp_zsmul]
  congr 1
  rw [cechAlexanderWhitney, cechAlexanderWhitney, ← Category.assoc, ← Category.assoc,
    ← cechAlexanderWhitneyTo_naturality_right, h, cechAlexanderWhitneyTo_naturality_left,
    Category.assoc, Category.assoc]

end Naturality

end Stacks.Cech.LinearCupProduct

end
