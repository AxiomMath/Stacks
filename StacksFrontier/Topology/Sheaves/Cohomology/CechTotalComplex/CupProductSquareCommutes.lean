module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.CupProductSquareSections
public import
  StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.CupProductSquareFlasqueCancellation
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.CechCupProductNaturality
import StacksCore.Tactic.StacksAttribute

/-!
# The Čech cup product square commutes

Let `(X, 𝒪_X)` be a ringed space, `A = Γ(X, 𝒪_X)`, `𝒦^•`, `ℳ^•` bounded below complexes of
`𝒪_X`-modules and `𝒰 : X = ⋃ U i` an open covering.  [Stacks, Tag 0FKV]: the diagram

```
Tot(Č(𝒰,𝒦)) ⊗^𝐋_A Tot(Č(𝒰,ℳ)) ─────────→ RΓ(X,𝒦) ⊗^𝐋_A RΓ(X,ℳ)
            │                                        │ μ
            ↓                                        ↓
Tot(Tot(Č(𝒰,𝒦)) ⊗_A Tot(Č(𝒰,ℳ)))          RΓ(X, 𝒦 ⊗^𝐋_{𝒪_X} ℳ)
            │                                        │
            ↓                                        ↓
Tot(Č(𝒰, Tot(𝒦 ⊗_{𝒪_X} ℳ))) ─────────────→ RΓ(X, Tot(𝒦 ⊗_{𝒪_X} ℳ))
```

commutes in `D(A)`.

## Main results

* `Stacks.Cech.CupProductSquare.cechLeftLeg_naturality`,
  `Stacks.Cech.CupProductSquare.cechRightLeg_naturality`: both legs are natural in the pair of
  complexes.
* `Stacks.Cech.CupProductSquare.cechLeftLeg_eq_cechRightLeg_of_isFlasque`: the square commutes
  for a pair of bounded below complexes of flasque modules.
* `Stacks.Cech.CupProductSquare.cupProductSquareCommutes`: **[Stacks, Tag 0FKV].**

## References

* [Stacks Project, Tag 0FKV](https://stacks.math.columbia.edu/tag/0FKV)
-/

@[expose] public noncomputable section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open AlgebraicGeometry
open Stacks.Cohomology.CechSheaf (abSheaf coverObject)
open Stacks.Cohomology.GlobalKunneth (baseSections tensorBase)
open Stacks.SheafOfModules.Tensor (ringSheaf sheafTensor)
open Stacks.Cech.ModuleCupProduct (CoeffRing sectionsComplexFunctor totalCechComplexFunctorA)
open Stacks.Cech.CupProduct (tensorModules)
open scoped CategoryTheory.Prod

universe w uC vC uD vD u

namespace Stacks.Cech.LinearCupProduct

attribute [local instance] ModuleCat.hasLimitsOfSize ModuleCat.hasColimitsOfSize

/-- `cechCupProduct_natural_of_pairing_hom` for coefficient complexes given as the values of a
functor. -/
theorem cechCupProduct_naturality_comp {C : Type uC} [Category.{vC} C] [HasFiniteProducts C]
    {ι : Type w} [UnivLE.{w, u}] (W : ι → C) (R : Type u) [CommRing R]
    {𝒞 : Type uD} [Category.{vD} 𝒞] (T : 𝒞 ⥤ CochainComplex (PresheafModules.{u} C R) ℤ)
    {k l m k' l' m' : 𝒞} (D : ComplexPairing R (T.obj k) (T.obj l) (T.obj m))
    (D' : ComplexPairing R (T.obj k') (T.obj l') (T.obj m')) (f : k ⟶ k') (g : l ⟶ l')
    (h : m ⟶ m')
    (hD : ∀ (a b n : ℤ) (hab : a + b = n),
      ((tensorPresheafModules.{u} R).map ((T.map f).f a)).app ((T.obj l).X b) ≫
          ((tensorPresheafModules.{u} R).obj ((T.obj k').X a)).map ((T.map g).f b) ≫
            D'.μ a b n hab =
        D.μ a b n hab ≫ (T.map h).f n) :
    HomologicalComplex.mapBifunctorMap ((T ⋙ totalCechComplexFunctor W R).map f)
        ((T ⋙ totalCechComplexFunctor W R).map g) (tensorModules R) (up ℤ) ≫
      (cechCupProduct W R D' : HomologicalComplex.mapBifunctor
        ((T ⋙ totalCechComplexFunctor W R).obj k') ((T ⋙ totalCechComplexFunctor W R).obj l')
        (tensorModules R) (up ℤ) ⟶ (T ⋙ totalCechComplexFunctor W R).obj m') =
      (cechCupProduct W R D : HomologicalComplex.mapBifunctor
        ((T ⋙ totalCechComplexFunctor W R).obj k) ((T ⋙ totalCechComplexFunctor W R).obj l)
        (tensorModules R) (up ℤ) ⟶ (T ⋙ totalCechComplexFunctor W R).obj m) ≫
        (T ⋙ totalCechComplexFunctor W R).map h :=
  cechCupProduct_natural_of_pairing_hom W R D D' (T.map f) (T.map g) (T.map h) hD

end Stacks.Cech.LinearCupProduct

namespace Stacks.Cech.SheafTensorPairing

attribute [local instance] ModuleCat.hasLimitsOfSize ModuleCat.hasColimitsOfSize

variable {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  (V : Opens X) {ι : Type u} (U : ι → Opens X) (hU : V = ⨆ i, U i)
  {K L K' L' : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} O)) ℤ}

private theorem pairing_paste {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {p0 p1 p2 : D} {q0 q1 q2 q3 q4 : C} (tf : p0 ⟶ p1) (tg : p1 ⟶ p2) (s0 : p0 ⟶ F.obj q0)
    (s1 : p1 ⟶ F.obj q1) (s2 : p2 ⟶ F.obj q2) (af : q0 ⟶ q1) (ag : q1 ⟶ q2) (ι' : q2 ⟶ q3)
    (ι : q0 ⟶ q4) (m : q4 ⟶ q3) (h1 : tg ≫ s2 = s1 ≫ F.map ag) (h2 : tf ≫ s1 = s0 ≫ F.map af)
    (h3 : af ≫ ag ≫ ι' = ι ≫ m) :
    tf ≫ tg ≫ s2 ≫ F.map ι' = (s0 ≫ F.map ι) ≫ F.map m := by
  rw [reassoc_of% h1, reassoc_of% h2, ← F.map_comp, ← F.map_comp, h3, F.map_comp,
    Category.assoc]

/-- The sheaf-tensor coefficient pairing is natural in the two complexes. -/
theorem sheafTensorComplexPairing_naturality (f : K ⟶ K') (g : L ⟶ L') (a b n : ℤ)
    (hab : a + b = n) :
    ((Stacks.Cech.LinearCupProduct.tensorPresheafModules.{u} (CoeffRing O V)).map
          (((sectionsComplexFunctor O V).map f).f a)).app
            (((sectionsComplexFunctor O V).obj L).X b) ≫
        ((Stacks.Cech.LinearCupProduct.tensorPresheafModules.{u} (CoeffRing O V)).obj
          (((sectionsComplexFunctor O V).obj K').X a)).map
            (((sectionsComplexFunctor O V).map g).f b) ≫
          (sheafTensorComplexPairing O V K' L').μ a b n hab =
      (sheafTensorComplexPairing O V K L).μ a b n hab ≫
        ((sectionsComplexFunctor O V).map
          (HomologicalComplex.mapBifunctorMap f g (sheafTensor O) (up ℤ))).f n :=
  pairing_paste (Stacks.Cech.ModuleCupProduct.sectionsFunctor O V) _ _ _ _ _ _ _ _ _ _
    (sheafTensorPairing_naturality_right O V (K'.X a) (g.f b))
    (sheafTensorPairing_naturality_left O V (f.f a) (L.X b))
    (HomologicalComplex.ι_mapBifunctorMap f g (sheafTensor O) (up ℤ) a b n hab).symm

/-- **The Čech cup product at the sheaf-tensor coefficients is natural in the two complexes.** -/
theorem cechCupProductSheafTensor_naturality (f : K ⟶ K') (g : L ⟶ L') :
    HomologicalComplex.mapBifunctorMap ((totalCechComplexFunctorA O V U hU).map f)
        ((totalCechComplexFunctorA O V U hU).map g) (tensorModules (CoeffRing O V)) (up ℤ) ≫
      cechCupProductSheafTensor O V K' L' U hU =
    cechCupProductSheafTensor O V K L U hU ≫ (totalCechComplexFunctorA O V U hU).map
      (HomologicalComplex.mapBifunctorMap f g (sheafTensor O) (up ℤ)) :=
  Stacks.Cech.LinearCupProduct.cechCupProduct_naturality_comp (coverObject U hU) (CoeffRing O V)
    (sectionsComplexFunctor O V) (sheafTensorComplexPairing O V K L)
    (sheafTensorComplexPairing O V K' L') f g _ (sheafTensorComplexPairing_naturality O V f g)

end Stacks.Cech.SheafTensorPairing

namespace Stacks.Cech.CupProductSquare

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] ModuleCat.hasLimitsOfSize ModuleCat.hasColimitsOfSize

open CochainComplex.DerivedTensor.ToTotal (canonicalDerivedToTensorComp
  canonicalDerivedToTensorComp_paste)
open Stacks.Cohomology.DerivedGlobalCupProduct (globalCupProduct canonicalOnePointComparison
  globalCupProduct_naturality)
open Stacks.Cohomology.DerivedPullbackTensor (derivedToTensorNatTrans totalComplexPair
  totalComplexPair_map)

variable (S : RingedSpace.{u, u}) {I : Type u} (Ui : I → Opens S.carrier)
  (hU : (⊤ : Opens S.carrier) = ⨆ i, Ui i)
  {K M K₁ M₁ : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf))}

/-- `Tot(a ⊗ b)` of two maps of bounded below complexes, as a map of bounded below complexes. -/
abbrev tensorPlusMap (a : K ⟶ K₁) (b : M ⟶ M₁) : tensorPlus S K M ⟶ tensorPlus S K₁ M₁ :=
  ObjectProperty.homMk (HomologicalComplex.mapBifunctorMap a.hom b.hom (sheafTensor S.sheaf) (up ℤ))

/-- The naturality of the comparison of [Stacks, Tag 08BN], with its source written as the
total Čech complex of `Stacks.Cech.ModuleCupProduct.totalCechComplexFunctorA`. -/
theorem cechToBaseSections_naturality {T T₁ : CochainComplex.Plus
      (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf))} (f : T ⟶ T₁) :
    DerivedCategory.Q.map ((totalCechComplexFunctorA S.sheaf ⊤ Ui hU).map f.hom) ≫
        (cechToBaseSections S Ui hU).app T₁ =
      (cechToBaseSections S Ui hU).app T ≫
        (CochainComplex.Plus.ι _ ⋙ DerivedCategory.Q ⋙ baseSections S).map f :=
  (cechToBaseSections S Ui hU).naturality f

/-- **The left-hand leg of [Stacks, Tag 0FKV]'s square is natural in the pair of complexes.** -/
theorem cechLeftLeg_naturality (a : K ⟶ K₁) (b : M ⟶ M₁) :
    (Functor.uncurry.obj (tensorBase S)).map
          (DerivedCategory.Q.map ((totalCechComplexFunctorA S.sheaf ⊤ Ui hU).map a.hom) ×ₘ
            DerivedCategory.Q.map ((totalCechComplexFunctorA S.sheaf ⊤ Ui hU).map b.hom)) ≫
        cechLeftLeg S Ui hU K₁ M₁ =
      cechLeftLeg S Ui hU K M ≫
        (CochainComplex.Plus.ι _ ⋙ DerivedCategory.Q ⋙ baseSections S).map
          (tensorPlusMap S a b) := by
  have h1 : HomologicalComplex.mapBifunctorMap ((totalCechComplexFunctorA S.sheaf ⊤ Ui hU).map
        a.hom) ((totalCechComplexFunctorA S.sheaf ⊤ Ui hU).map b.hom)
          (tensorModules (CoeffRing.{u} S.sheaf ⊤)) (up ℤ) ≫
        Stacks.Cech.SheafTensorPairing.cechCupProductSheafTensor S.sheaf ⊤ K₁.1 M₁.1 Ui hU =
      Stacks.Cech.SheafTensorPairing.cechCupProductSheafTensor S.sheaf ⊤ K.1 M.1 Ui hU ≫
        (totalCechComplexFunctorA S.sheaf ⊤ Ui hU).map (tensorPlusMap S a b).hom :=
    Stacks.Cech.SheafTensorPairing.cechCupProductSheafTensor_naturality S.sheaf ⊤ Ui hU a.hom b.hom
  exact (canonicalDerivedToTensorComp_paste (CoeffRing.{u} S.sheaf ⊤)
    (Z := (totalCechComplexFunctorA S.sheaf ⊤ Ui hU).obj (tensorPlus S K M).1)
    (Z2 := (totalCechComplexFunctorA S.sheaf ⊤ Ui hU).obj (tensorPlus S K₁ M₁).1) _ _ _ _ _ h1 _ _
    (cechToBaseSections_naturality S Ui hU (tensorPlusMap S a b))).trans
      (Category.assoc _ _ _).symm

/-- A composite `F(α × β) ≫ κ ≫ G(δ)` is natural once each of its three factors is. -/
theorem bifunctor_comp_paste {C₁ : Type uC} [Category.{vC} C₁] {C₂ : Type uC} [Category.{vC} C₂]
    {D : Type uD} [Category.{vD} D] {E : Type uD} [Category.{vD} E]
    (F : C₁ × C₂ ⥤ D) (G : E ⥤ D)
    {x₁ x₁' y₁ y₁' : C₁} {x₂ x₂' y₂ y₂' : C₂}
    (f₁ : x₁ ⟶ x₁') (f₂ : x₂ ⟶ x₂') (α₁ : x₁ ⟶ y₁) (α₁' : x₁' ⟶ y₁') (α₂ : x₂ ⟶ y₂)
    (α₂' : x₂' ⟶ y₂') (g₁ : y₁ ⟶ y₁') (g₂ : y₂ ⟶ y₂')
    (h₁ : f₁ ≫ α₁' = α₁ ≫ g₁) (h₂ : f₂ ≫ α₂' = α₂ ≫ g₂)
    {e e' z z' : E} (κ : F.obj (y₁, y₂) ⟶ G.obj e) (κ' : F.obj (y₁', y₂') ⟶ G.obj e')
    (μ : e ⟶ e') (hκ : F.map (g₁ ×ₘ g₂) ≫ κ' = κ ≫ G.map μ)
    (δ : e ⟶ z) (δ' : e' ⟶ z') (t : z ⟶ z') (hδ : μ ≫ δ' = δ ≫ t) {r : G.obj z ⟶ G.obj z'}
    (ht : G.map t = r) :
    F.map (f₁ ×ₘ f₂) ≫ F.map (α₁' ×ₘ α₂') ≫ κ' ≫ G.map δ' =
      (F.map (α₁ ×ₘ α₂) ≫ κ ≫ G.map δ) ≫ r := by
  have hα : (f₁ ×ₘ f₂) ≫ (α₁' ×ₘ α₂') = (α₁ ×ₘ α₂) ≫ (g₁ ×ₘ g₂) := Prod.ext h₁ h₂
  rw [← ht, ← F.map_comp_assoc, hα, F.map_comp_assoc, reassoc_of% hκ, Category.assoc,
    Category.assoc, ← G.map_comp, hδ, G.map_comp]

/-- **The right-hand leg of [Stacks, Tag 0FKV]'s square is natural in the pair of complexes.** -/
theorem cechRightLeg_naturality (a : K ⟶ K₁) (b : M ⟶ M₁) :
    (Functor.uncurry.obj (tensorBase S)).map
          (DerivedCategory.Q.map ((totalCechComplexFunctorA S.sheaf ⊤ Ui hU).map a.hom) ×ₘ
            DerivedCategory.Q.map ((totalCechComplexFunctorA S.sheaf ⊤ Ui hU).map b.hom)) ≫
        cechRightLeg S Ui hU K₁ M₁ =
      cechRightLeg S Ui hU K M ≫
        (CochainComplex.Plus.ι _ ⋙ DerivedCategory.Q ⋙ baseSections S).map (tensorPlusMap S a b) :=
  bifunctor_comp_paste (Functor.uncurry.obj (tensorBase S)) (baseSections S) _ _ _ _ _ _ _ _
    (cechToBaseSections_naturality S Ui hU a) (cechToBaseSections_naturality S Ui hU b) _ _ _
    (globalCupProduct_naturality (globalCupProduct (canonicalOnePointComparison S))
      (DerivedCategory.Q.map a.hom) (DerivedCategory.Q.map b.hom)) _ _ _
    ((derivedToTensorNatTrans S).naturality (a.hom ×ₘ b.hom))
    (congrArg (fun t => (baseSections S).map (DerivedCategory.Q.map t))
      (totalComplexPair_map (sheafTensor S.sheaf) a.hom b.hom))

/-- A morphism `f = e ≫ g` with `e` an isomorphism becomes invertible under a functor once `g`
does. -/
theorem isIso_map_of_eq_hom_comp {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    (Q : C ⥤ D) {x y z : C} (e : x ≅ y) (g : y ⟶ z) (f : x ⟶ z) (h : f = e.hom ≫ g)
    (hg : IsIso (Q.map g)) : IsIso (Q.map f) := by
  rw [h, Q.map_comp]
  infer_instance

/-- Cancelling an isomorphism on the right of an equation of composites. -/
theorem eq_of_comp_isIso_eq {C : Type uC} [Category.{vC} C] {x y z : C} {g g' : x ⟶ y}
    (f : y ⟶ z) (hf : IsIso f) (h : g ≫ f = g' ≫ f) : g = g' := by
  have := hf
  exact (cancel_mono f).mp h

/-- **For a bounded below complex of flasque modules the Čech augmentation of
[Stacks, Tag 07M9] is invertible in `D(A)`**, in the spelling of
`Stacks.Cech.SheafTensorPairing.augmentationA`. -/
theorem isIso_Q_map_augmentationA (T : CochainComplex.Plus
      (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)))
    (hT : ∀ n : ℤ, (Stacks.Cohomology.CechSheaf.abSheaf (T.1.X n)).IsFlasque) :
    IsIso (DerivedCategory.Q.map (Stacks.Cech.SheafTensorPairing.augmentationA S.sheaf ⊤ Ui hU
      T.1)) :=
  isIso_map_of_eq_hom_comp DerivedCategory.Q _ _ _
    (Stacks.Cech.LinearCupProduct.cechAugmentationTotal_eq_sectionsToTotalCech S.sheaf ⊤ Ui hU T.1)
    (Stacks.Cech.Linear.isIso_sectionsToTotalCechDerived_of_isFlasque S.carrier
      (ringSheaf.{u, u, u} S.sheaf) ⊤ Ui hU T hT)

/-- **[Stacks, Tag 0FKV] for a pair of bounded below complexes of flasque modules.** -/
theorem cechLeftLeg_eq_cechRightLeg_of_isFlasque
    (hK : ∀ n : ℤ, (Stacks.Cohomology.CechSheaf.abSheaf (K.1.X n)).IsFlasque)
    (hM : ∀ n : ℤ, (Stacks.Cohomology.CechSheaf.abSheaf (M.1.X n)).IsFlasque) :
    cechLeftLeg S Ui hU K M = cechRightLeg S Ui hU K M :=
  eq_of_isIso_comp_eq _
    (isIso_map_mkHom (Functor.uncurry.obj (tensorBase S)) _ _
      (isIso_Q_map_augmentationA S Ui hU K hK) (isIso_Q_map_augmentationA S Ui hU M hM))
    ((augmentation_comp_cechLeftLeg S Ui hU K M).trans
      (augmentation_comp_cechRightLeg S Ui hU K M).symm)

/-- **[Stacks, Tag 0FKV].**  Let `(X, 𝒪_X)` be a ringed space, `A = Γ(X, 𝒪_X)`, `𝒦^•` and `ℳ^•`
bounded below complexes of `𝒪_X`-modules and `𝒰 : X = ⋃ Uᵢ` an open covering.  The diagram

```
Tot(Č(𝒰,𝒦)) ⊗^𝐋_A Tot(Č(𝒰,ℳ)) ─────────→ RΓ(X,𝒦) ⊗^𝐋_A RΓ(X,ℳ)
            │                                        │ μ
            ↓                                        ↓
Tot(Tot(Č(𝒰,𝒦)) ⊗_A Tot(Č(𝒰,ℳ)))          RΓ(X, 𝒦 ⊗^𝐋_{𝒪_X} ℳ)
            │                                        │
            ↓                                        ↓
Tot(Č(𝒰, Tot(𝒦 ⊗_{𝒪_X} ℳ))) ─────────────→ RΓ(X, Tot(𝒦 ⊗_{𝒪_X} ℳ))
```

commutes in `D(A)`: the left-hand leg `cechLeftLeg` (the canonical map to the total tensor
complex, then the Čech cup product of [Stacks, Tag 07MB], then the comparison of
[Stacks, Tag 08BN]) equals the right-hand leg `cechRightLeg` (the comparison of Tag 08BN in both
factors, then the global cup product `μ`, then `RΓ(X, -)` of the canonical map
`𝒦^• ⊗^𝐋 ℳ^• ⟶ Tot(𝒦^• ⊗ ℳ^•)`). -/
@[stacks 0FKV]
theorem cupProductSquareCommutes :
    cechLeftLeg S Ui hU K M = cechRightLeg S Ui hU K M := by
  obtain ⟨K₁, M₁, a, b, -, -, hK₁ge, hM₁ge, hK₁fl, hM₁fl, hiso⟩ :=
    Stacks.Cohomology.FlasqueReduction.exists_flasqueResolution_isIso_baseSections_map S K.1 M.1
      ((CochainComplex.plus_iff _ K.1).mp K.2) ((CochainComplex.plus_iff _ M.1).mp M.2)
  let K₂ : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) :=
    ⟨K₁, (CochainComplex.plus_iff _ K₁).mpr hK₁ge⟩
  let M₂ : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) :=
    ⟨M₁, (CochainComplex.plus_iff _ M₁).mpr hM₁ge⟩
  let a₂ : K ⟶ K₂ := ObjectProperty.homMk a
  let b₂ : M ⟶ M₂ := ObjectProperty.homMk b
  exact eq_of_comp_isIso_eq _ hiso ((cechLeftLeg_naturality S Ui hU a₂ b₂).symm.trans
    ((whisker_eq _ (cechLeftLeg_eq_cechRightLeg_of_isFlasque S Ui hU (K := K₂) (M := M₂)
      hK₁fl hM₁fl)).trans (cechRightLeg_naturality S Ui hU a₂ b₂)))

end Stacks.Cech.CupProductSquare
