module

public import StacksFrontier.Homology.Tor.ProductNaturality
public import StacksFrontier.Homology.Tor.DerivedTensorToTotalComplex

/-!
# The tensoring of classes of cocycles

Let `R` be a commutative ring and let `X`, `Y` be cochain complexes of `R`-modules.  The tensoring
of cohomology classes of Tag 068H, `RingTheory.TorProducts.cohomologyTensorProduct`, is a map
`Hⁱ(X) ⊗_R Hʲ(Y) ⟶ Hⁱ⁺ʲ(X ⊗^𝐋_R Y)`.  Followed by the canonical map
`X ⊗^𝐋_R Y ⟶ Tot(X ⊗_R Y)` to the ordinary total tensor complex, it sends the classes of two
cocycles `z` and `w` to the class of `z ⊗ w`, for *arbitrary* complexes `X` and `Y`, not only
K-flat ones.

## Main definitions

* `RingTheory.TorProducts.singleR`: the complex `R[-i]`.
* `RingTheory.TorProducts.cycleHom`: the chain map `R[-i] ⟶ X` attached to a cocycle.
* `RingTheory.TorProducts.cycleClass`: the class in `Hⁱ(X)`, read in `D(R)`, of a cocycle.
* `RingTheory.TorProducts.tensorGen`: the tensoring of the classes of the two generators of
  `Hⁱ(R[-i])` and `Hʲ(R[-j])`.

## Main results

* `RingTheory.TorProducts.cycleClass_eq`: the class of a cocycle is the image of the generator.
* `RingTheory.TorProducts.tensor_cycleClass_comp`: the tensoring of the images of two classes of
  cocycles under morphisms of `D(R)` is the image of `tensorGen`.
* `RingTheory.TorProducts.tensorGen_toTensor`: `tensorGen`, followed by the canonical map to the
  total tensor complex, is the class of the tensor product of the two generating cocycles.
* `RingTheory.TorProducts.cycleClass_tensor_toTensor`: the tensoring of the classes of two
  cocycles, followed by the canonical map to the total tensor complex, is the class of their
  tensor product.
* `RingTheory.TorProducts.tensor_cycleClass_naturality`: the tensoring of classes of cocycles is
  natural along arbitrary morphisms of `D(R)`.

## References

* [Stacks Project, Tag 068H](https://stacks.math.columbia.edu/tag/068H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CochainComplex.DerivedTensor CochainComplex.DerivedTensor.ToTotal
open scoped CategoryTheory.Prod

universe u

namespace RingTheory.TorProducts

attribute [local instance] HasDerivedCategory.standard

variable (R : Type u) [CommRing R]

/-- The single cochain complex `R[-i]`, the free module of rank one in degree `i`. -/
abbrev singleR (i : ℤ) : CochainComplex (ModuleCat.{u} R) ℤ :=
  (CochainComplex.singleFunctor (ModuleCat.{u} R) i).obj (ModuleCat.of R R)

/-- `R[-i]` is K-flat. -/
theorem kFlat_singleR (i : ℤ) : (singleR R i).KFlat := by
  have h (k : ℤ) : Module.Flat R ((singleR R i).X k) := by
    by_cases hk : k = i
    · exact Module.Flat.of_linearEquiv
        (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) i
          (ModuleCat.of R R) k hk).toLinearEquiv
    · exact Module.Flat.of_linearEquiv
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) i
          (ModuleCat.of R R) k hk).isoZero.toLinearEquiv
  exact CochainComplex.KFlat.kFlat_of_flat (singleR R i) i

/-- `R[-i]` is K-projective. -/
instance isKProjective_singleR (i : ℤ) : (singleR R i).IsKProjective := by
  have : Module.Projective R (ModuleCat.of R R) := inferInstanceAs (Module.Projective R R)
  have : Projective (ModuleCat.of R R) := ModuleCat.projective_of_categoryTheory_projective _
  have : ∀ n : ℤ, Projective ((singleR R i).X n) := fun n => by
    by_cases hn : n = i
    · exact Projective.of_iso
        (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) i
          (ModuleCat.of R R) n hn).symm inferInstance
    · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) i
        (ModuleCat.of R R) n hn).projective
  exact CochainComplex.isKProjective_of_projective (singleR R i) i

/-- The generating cocycle `1 ∈ Zⁱ(R[-i])`. -/
abbrev singleCycle (i : ℤ) : ModuleCat.of R R ⟶ (singleR R i).cycles i :=
  (HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) i (ModuleCat.of R R)).inv

variable {R}

/-- **The class of a family of cocycles**, read in `Hⁱ` of the derived category: a morphism
`z : M ⟶ Zⁱ(X)` followed by the projection to `Hⁱ(X)` and the identification of `Hⁱ(X)` with
`Hⁱ(Q X)`. -/
def cycleClass {M : ModuleCat.{u} R} {X : CochainComplex (ModuleCat.{u} R) ℤ} {i : ℤ}
    (z : M ⟶ X.cycles i) :
    M ⟶ (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj (DerivedCategory.Q.obj X) :=
  z ≫ X.homologyπ i ≫ (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) i).inv.app X

/-- `cycleClass z` is `z ≫ X.homologyπ i` followed by the identification of `Hⁱ(X)` with
`Hⁱ(Q X)`. -/
theorem cycleClass_def {M : ModuleCat.{u} R} {X : CochainComplex (ModuleCat.{u} R) ℤ} {i : ℤ}
    (z : M ⟶ X.cycles i) :
    cycleClass z =
      z ≫ X.homologyπ i ≫ (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) i).inv.app X :=
  rfl

/-- Precomposing a family of cocycles precomposes its class. -/
theorem comp_cycleClass {M N : ModuleCat.{u} R} {X : CochainComplex (ModuleCat.{u} R) ℤ} {i : ℤ}
    (a : N ⟶ M) (z : M ⟶ X.cycles i) : a ≫ cycleClass z = cycleClass (a ≫ z) := by
  simp only [cycleClass_def, Category.assoc]

/-- **The chain map `R[-i] ⟶ X` attached to a cocycle** `z ∈ Zⁱ(X)`: it sends `1` to `z`. -/
def cycleHom {X : CochainComplex (ModuleCat.{u} R) ℤ} {i : ℤ}
    (z : ModuleCat.of R R ⟶ X.cycles i) : singleR R i ⟶ X :=
  HomologicalComplex.mkHomFromSingle (z ≫ X.iCycles i) (fun k _ => by simp)

/-- The chain map attached to a cocycle sends the generating cocycle to it. -/
theorem singleCycle_cyclesMap {X : CochainComplex (ModuleCat.{u} R) ℤ} {i : ℤ}
    (z : ModuleCat.of R R ⟶ X.cycles i) :
    singleCycle R i ≫ HomologicalComplex.cyclesMap (cycleHom z) i = z := by
  rw [← cancel_mono (X.iCycles i), Category.assoc, HomologicalComplex.cyclesMap_i,
    ← Category.assoc]
  have h := HomologicalComplex.singleObjCyclesSelfIso_inv_iCycles (C := ModuleCat.{u} R)
    (ComplexShape.up ℤ) i (ModuleCat.of R R)
  refine (congrArg (· ≫ (cycleHom z).f i) h).trans ?_
  rw [cycleHom, HomologicalComplex.mkHomFromSingle_f, Iso.inv_hom_id_assoc]

variable (R)

/-- The class of the generating cocycle of `R[-i]`. -/
abbrev genClass (i : ℤ) :
    ModuleCat.of R R ⟶ (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
      (DerivedCategory.Q.obj (singleR R i)) :=
  cycleClass (singleCycle R i)

variable {R}

/-- The class of a family of cocycles pushed along a chain map is the class of its image. -/
theorem cycleClass_comp_map {M : ModuleCat.{u} R} {X Y : CochainComplex (ModuleCat.{u} R) ℤ}
    {i : ℤ} (z : M ⟶ X.cycles i) (c : X ⟶ Y) :
    cycleClass z ≫ (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).map
        (DerivedCategory.Q.map c) =
      cycleClass (z ≫ HomologicalComplex.cyclesMap c i) := by
  have hn := (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) i).inv.naturality c
  dsimp only [CategoryTheory.Functor.comp_map] at hn
  simp only [cycleClass_def, Category.assoc]
  refine congrArg (z ≫ ·) ?_
  refine (congrArg (X.homologyπ i ≫ ·) hn.symm).trans ?_
  exact HomologicalComplex.homologyπ_naturality_assoc c i _

/-- **The class of a cocycle is the image of the generator** under the chain map attached to the
cocycle. -/
theorem cycleClass_eq {X : CochainComplex (ModuleCat.{u} R) ℤ} {i : ℤ}
    (z : ModuleCat.of R R ⟶ X.cycles i) :
    cycleClass z = genClass R i ≫ (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).map
      (DerivedCategory.Q.map (cycleHom z)) := by
  rw [cycleClass_comp_map, singleCycle_cyclesMap]

variable (R)

/-- **The tensoring of the classes of the two generators** of `Hⁱ(R[-i])` and `Hʲ(R[-j])`. -/
abbrev tensorGen (i j : ℤ) :
    ModuleCat.of R R ⟶ (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (i + j)).obj
      (((canonicalDerivedTensorProductFunctor R).obj
        (DerivedCategory.Q.obj (singleR R i))).obj (DerivedCategory.Q.obj (singleR R j))) :=
  (λ_ (ModuleCat.of R R)).inv ≫ (genClass R i ⊗ₘ genClass R j) ≫
    (cohomologyTensorProduct (DerivedCategory.Q.obj (singleR R i))
      (DerivedCategory.Q.obj (singleR R j)) i j).map

variable {R}

/-- **The tensoring of the images of two classes of cocycles** under morphisms `f` and `g` of
`D(R)` is the image of `tensorGen` under the derived tensor product of the composites of `f` and
`g` with the chain maps attached to the cocycles. -/
theorem tensor_cycleClass_comp {X Y : CochainComplex (ModuleCat.{u} R) ℤ} {i j : ℤ}
    (z : ModuleCat.of R R ⟶ X.cycles i) (w : ModuleCat.of R R ⟶ Y.cycles j)
    {U V : DerivedCategory (ModuleCat.{u} R)} (f : DerivedCategory.Q.obj X ⟶ U)
    (g : DerivedCategory.Q.obj Y ⟶ V) :
    (λ_ (ModuleCat.of R R)).inv ≫
        ((cycleClass z ≫ (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).map f) ⊗ₘ
          (cycleClass w ≫ (DerivedCategory.homologyFunctor (ModuleCat.{u} R) j).map g)) ≫
        (cohomologyTensorProduct U V i j).map =
      tensorGen R i j ≫ (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (i + j)).map
        (((canonicalDerivedTensorProductFunctor R).map
            (DerivedCategory.Q.map (cycleHom z) ≫ f)).app (DerivedCategory.Q.obj (singleR R j)) ≫
          ((canonicalDerivedTensorProductFunctor R).obj U).map
            (DerivedCategory.Q.map (cycleHom w) ≫ g)) := by
  have hnat := cohomologyTensorProduct_naturality_of_isKProjective (singleR R i) (singleR R j)
    (kFlat_singleR R i) (kFlat_singleR R j) (DerivedCategory.Q.map (cycleHom z) ≫ f)
    (DerivedCategory.Q.map (cycleHom w) ≫ g) i j
  rw [cycleClass_eq z, cycleClass_eq w, Category.assoc, Category.assoc,
    ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    ← tensorHom_comp_tensorHom_assoc, hnat]
  simp only [tensorGen, Category.assoc]

/-- The case `f = 𝟙`, `g = 𝟙` of `tensor_cycleClass_comp`. -/
private theorem tensor_cycleClass_eq_tensorGen {X Y : CochainComplex (ModuleCat.{u} R) ℤ}
    {i j : ℤ} (z : ModuleCat.of R R ⟶ X.cycles i) (w : ModuleCat.of R R ⟶ Y.cycles j) :
    (λ_ (ModuleCat.of R R)).inv ≫ (cycleClass z ⊗ₘ cycleClass w) ≫
        (cohomologyTensorProduct (DerivedCategory.Q.obj X) (DerivedCategory.Q.obj Y) i j).map =
      tensorGen R i j ≫ (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (i + j)).map
        (((canonicalDerivedTensorProductFunctor R).map
            (DerivedCategory.Q.map (cycleHom z))).app (DerivedCategory.Q.obj (singleR R j)) ≫
          ((canonicalDerivedTensorProductFunctor R).obj (DerivedCategory.Q.obj X)).map
            (DerivedCategory.Q.map (cycleHom w))) := by
  have h1 := tensor_cycleClass_comp z w (𝟙 _) (𝟙 _)
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.comp_id,
    Category.comp_id, Category.comp_id, Category.comp_id] at h1
  exact h1

/-- A tensor product of two threefold composites of linear maps is the threefold composite of
the tensor products. -/
private lemma tensorHom_comp₃ {A B C D A' B' C' D' : ModuleCat.{u} R} (a : A ⟶ B) (b : B ⟶ C)
    (c : C ⟶ D) (a' : A' ⟶ B') (b' : B' ⟶ C') (c' : C' ⟶ D') :
    (a ≫ b ≫ c) ⊗ₘ (a' ≫ b' ≫ c') = (a ⊗ₘ a') ≫ (b ⊗ₘ b') ≫ (c ⊗ₘ c') := by
  rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]

/-- **`tensorGen`, followed by the canonical map to the total tensor complex, is the class of
the tensor product of the two generating cocycles** `1 ∈ Zⁱ(R[-i])` and `1 ∈ Zʲ(R[-j])`. -/
theorem tensorGen_toTensor (i j : ℤ)
    (z₀ : (singleR R i).cycles i ⊗ (singleR R j).cycles j ⟶
      (singleR R i ⊗ singleR R j).cycles (i + j))
    (hz₀ : z₀ ≫ (singleR R i ⊗ singleR R j).iCycles (i + j) =
      ((singleR R i).iCycles i ⊗ₘ (singleR R j).iCycles j) ≫
        HomologicalComplex.ιTensorObj (singleR R i) (singleR R j) i j (i + j) rfl) :
    tensorGen R i j ≫ (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (i + j)).map
        ((canonicalDerivedToTensorNatTrans R).app (singleR R i, singleR R j)) =
      (λ_ (ModuleCat.of R R)).inv ≫ (singleCycle R i ⊗ₘ singleCycle R j) ≫ cycleClass z₀ := by
  have hE := TorCrossProduct.cohomologyTensorProduct_map_eq_of_isKProjective
    (singleR R i) (singleR R j) (kFlat_singleR R i) (kFlat_singleR R j) i j z₀ hz₀
  rw [canonicalDerivedToTensorNatTrans_app_eq_comparison R _ _ (kFlat_singleR R i)
    (kFlat_singleR R j)]
  have key : ((singleR R i).homologyπ i ⊗ₘ (singleR R j).homologyπ j) ≫
      ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) i).inv.app (singleR R i) ⊗ₘ
        (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) j).inv.app (singleR R j)) ≫
      (cohomologyTensorProduct (DerivedCategory.Q.obj (singleR R i))
        (DerivedCategory.Q.obj (singleR R j)) i j).map ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (i + j)).map
        ((canonicalDerivedTensorProduct R).comparison (singleR R i) (singleR R j)
          (kFlat_singleR R i) (kFlat_singleR R j)).hom =
      z₀ ≫ (singleR R i ⊗ singleR R j).homologyπ (i + j) ≫
        (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) (i + j)).inv.app
          (singleR R i ⊗ singleR R j) := by
    have h2 := congrArg (· ≫ (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R)
      (i + j)).inv.app (singleR R i ⊗ singleR R j)) hE
    simp only [Category.assoc] at h2
    refine Eq.trans ?_ h2
    rw [Iso.hom_inv_id_app]
    exact (Category.comp_id _).symm
  have hsplit : (genClass R i ⊗ₘ genClass R j) =
      (singleCycle R i ⊗ₘ singleCycle R j) ≫ ((singleR R i).homologyπ i ⊗ₘ
        (singleR R j).homologyπ j) ≫
        ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) i).inv.app (singleR R i) ⊗ₘ
          (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) j).inv.app (singleR R j)) :=
    tensorHom_comp₃ _ _ _ _ _ _
  rw [tensorGen, hsplit, cycleClass_def]
  simp only [Category.assoc]
  exact congrArg (fun t => (λ_ (ModuleCat.of R R)).inv ≫ (singleCycle R i ⊗ₘ singleCycle R j) ≫ t)
    key

/-- The tensoring of cocycles is natural in chain maps. -/
theorem tensorCycles_naturality {X Y X' Y' : CochainComplex (ModuleCat.{u} R) ℤ} {i j : ℤ}
    (a : X ⟶ X') (b : Y ⟶ Y')
    (z₀ : X.cycles i ⊗ Y.cycles j ⟶ (X ⊗ Y).cycles (i + j))
    (hz₀ : z₀ ≫ (X ⊗ Y).iCycles (i + j) =
      (X.iCycles i ⊗ₘ Y.iCycles j) ≫ HomologicalComplex.ιTensorObj X Y i j (i + j) rfl)
    (z₁ : X'.cycles i ⊗ Y'.cycles j ⟶ (X' ⊗ Y').cycles (i + j))
    (hz₁ : z₁ ≫ (X' ⊗ Y').iCycles (i + j) =
      (X'.iCycles i ⊗ₘ Y'.iCycles j) ≫ HomologicalComplex.ιTensorObj X' Y' i j (i + j) rfl) :
    z₀ ≫ HomologicalComplex.cyclesMap (HomologicalComplex.tensorHom a b) (i + j) =
      (HomologicalComplex.cyclesMap a i ⊗ₘ HomologicalComplex.cyclesMap b j) ≫ z₁ := by
  rw [← cancel_mono ((X' ⊗ Y').iCycles (i + j)), Category.assoc, Category.assoc, hz₁]
  refine (congrArg (z₀ ≫ ·)
    (HomologicalComplex.cyclesMap_i (HomologicalComplex.tensorHom a b) (i + j))).trans ?_
  refine ((Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ (HomologicalComplex.tensorHom a b).f (i + j)) hz₀)).trans ?_
  rw [Category.assoc, tensorHom_comp_tensorHom_assoc, HomologicalComplex.cyclesMap_i,
    HomologicalComplex.cyclesMap_i, ← tensorHom_comp_tensorHom_assoc]
  congr 1
  refine (HomologicalComplex.ι_mapBifunctorMap a b _ _ i j (i + j) rfl).trans ?_
  simp [MonoidalCategory.tensorHom_def]

/-- **The tensoring of the classes of two cocycles, followed by the canonical map to the total
tensor complex, is the class of their tensor product**, for arbitrary cochain complexes `X` and
`Y` of `R`-modules. Here `z₀` is the tensoring of cocycles `Zⁱ(X) ⊗ Zʲ(Y) ⟶ Zⁱ⁺ʲ(Tot(X ⊗ Y))`. -/
theorem cycleClass_tensor_toTensor {X Y : CochainComplex (ModuleCat.{u} R) ℤ} {i j : ℤ}
    (z : ModuleCat.of R R ⟶ X.cycles i) (w : ModuleCat.of R R ⟶ Y.cycles j)
    (z₀ : X.cycles i ⊗ Y.cycles j ⟶ (X ⊗ Y).cycles (i + j))
    (hz₀ : z₀ ≫ (X ⊗ Y).iCycles (i + j) =
      (X.iCycles i ⊗ₘ Y.iCycles j) ≫ HomologicalComplex.ιTensorObj X Y i j (i + j) rfl) :
    (λ_ (ModuleCat.of R R)).inv ≫ (cycleClass z ⊗ₘ cycleClass w) ≫
        (cohomologyTensorProduct (DerivedCategory.Q.obj X) (DerivedCategory.Q.obj Y) i j).map ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (i + j)).map
          ((canonicalDerivedToTensorNatTrans R).app (X, Y)) =
      (λ_ (ModuleCat.of R R)).inv ≫ (z ⊗ₘ w) ≫ cycleClass z₀ := by
  obtain ⟨s₀, hs₀⟩ := exists_tensorCycles (singleR R i) (singleR R j) i j
  have h1 := tensor_cycleClass_eq_tensorGen z w
  have hnat : (((canonicalDerivedTensorProductFunctor R).map
          (DerivedCategory.Q.map (cycleHom z))).app (DerivedCategory.Q.obj (singleR R j)) ≫
        ((canonicalDerivedTensorProductFunctor R).obj (DerivedCategory.Q.obj X)).map
          (DerivedCategory.Q.map (cycleHom w))) ≫ (canonicalDerivedToTensorNatTrans R).app (X, Y) =
      (canonicalDerivedToTensorNatTrans R).app (singleR R i, singleR R j) ≫
        DerivedCategory.Q.map (HomologicalComplex.tensorHom (cycleHom z) (cycleHom w)) := by
    have h := (canonicalDerivedToTensorNatTrans R).naturality (X := (singleR R i, singleR R j))
      (Y := (X, Y)) (cycleHom z ×ₘ cycleHom w)
    simp only [CategoryTheory.Functor.comp_map] at h
    rwa [totalTensorPair_map] at h
  have h2 := tensorGen_toTensor i j s₀ hs₀ =≫ (DerivedCategory.homologyFunctor (ModuleCat.{u} R)
    (i + j)).map (DerivedCategory.Q.map (HomologicalComplex.tensorHom (cycleHom z) (cycleHom w)))
  have h3 := cycleClass_comp_map s₀ (HomologicalComplex.tensorHom (cycleHom z) (cycleHom w))
  have h4 := tensorCycles_naturality (cycleHom z) (cycleHom w) s₀ hs₀ z₀ hz₀
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} R) (i + j)
  let Ts := ((canonicalDerivedTensorProductFunctor R).map
          (DerivedCategory.Q.map (cycleHom z))).app (DerivedCategory.Q.obj (singleR R j)) ≫
        ((canonicalDerivedTensorProductFunctor R).obj (DerivedCategory.Q.obj X)).map
          (DerivedCategory.Q.map (cycleHom w))
  have e1 : (λ_ (ModuleCat.of R R)).inv ≫ (cycleClass z ⊗ₘ cycleClass w) ≫
        (cohomologyTensorProduct (DerivedCategory.Q.obj X) (DerivedCategory.Q.obj Y) i j).map ≫
        H.map ((canonicalDerivedToTensorNatTrans R).app (X, Y)) =
      tensorGen R i j ≫ H.map (Ts ≫ (canonicalDerivedToTensorNatTrans R).app (X, Y)) := by
    rw [H.map_comp, ← Category.assoc (tensorGen R i j), ← h1]
    simp only [Category.assoc]
  have e2 : tensorGen R i j ≫ H.map (Ts ≫ (canonicalDerivedToTensorNatTrans R).app (X, Y)) =
      (tensorGen R i j ≫ H.map ((canonicalDerivedToTensorNatTrans R).app
        (singleR R i, singleR R j))) ≫
        H.map (DerivedCategory.Q.map (HomologicalComplex.tensorHom (cycleHom z) (cycleHom w))) :=
    (congrArg (fun t => tensorGen R i j ≫ H.map t) hnat).trans
      ((congrArg (tensorGen R i j ≫ ·) (H.map_comp _ _)).trans (Category.assoc _ _ _).symm)
  refine e1.trans (e2.trans (h2.trans ?_))
  have h5 : (singleCycle R i ⊗ₘ singleCycle R j) ≫ cycleClass (s₀ ≫ HomologicalComplex.cyclesMap
        (HomologicalComplex.tensorHom (cycleHom z) (cycleHom w)) (i + j)) =
      (z ⊗ₘ w) ≫ cycleClass z₀ := by
    rw [h4, ← comp_cycleClass, ← Category.assoc, tensorHom_comp_tensorHom, singleCycle_cyclesMap,
      singleCycle_cyclesMap]
  exact (Category.assoc _ _ _).trans ((congrArg ((λ_ (ModuleCat.of R R)).inv ≫ ·)
    ((Category.assoc _ _ _).trans ((congrArg ((singleCycle R i ⊗ₘ singleCycle R j) ≫ ·)
      h3).trans h5))))

/-- **The tensoring of classes of cocycles is natural along arbitrary morphisms of `D(R)`**: for
classes of cocycles of complexes `X` and `Y` and morphisms `f : Q X ⟶ U` and `g : Q Y ⟶ V`,
tensoring the images is applying `f ⊗^𝐋 g` to the tensoring of the classes. No hypothesis on
`X`, `Y`, `U` or `V` is needed. -/
theorem tensor_cycleClass_naturality {X Y : CochainComplex (ModuleCat.{u} R) ℤ} {i j : ℤ}
    (z : ModuleCat.of R R ⟶ X.cycles i) (w : ModuleCat.of R R ⟶ Y.cycles j)
    {U V : DerivedCategory (ModuleCat.{u} R)} (f : DerivedCategory.Q.obj X ⟶ U)
    (g : DerivedCategory.Q.obj Y ⟶ V) :
    (λ_ (ModuleCat.of R R)).inv ≫
        ((cycleClass z ≫ (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).map f) ⊗ₘ
          (cycleClass w ≫ (DerivedCategory.homologyFunctor (ModuleCat.{u} R) j).map g)) ≫
        (cohomologyTensorProduct U V i j).map =
      (λ_ (ModuleCat.of R R)).inv ≫ (cycleClass z ⊗ₘ cycleClass w) ≫
        (cohomologyTensorProduct (DerivedCategory.Q.obj X) (DerivedCategory.Q.obj Y) i j).map ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (i + j)).map
          (((canonicalDerivedTensorProductFunctor R).map f).app (DerivedCategory.Q.obj Y) ≫
            ((canonicalDerivedTensorProductFunctor R).obj U).map g) := by
  have h1 := tensor_cycleClass_eq_tensorGen z w
  have hT : ((canonicalDerivedTensorProductFunctor R).map
        (DerivedCategory.Q.map (cycleHom z) ≫ f)).app (DerivedCategory.Q.obj (singleR R j)) ≫
        ((canonicalDerivedTensorProductFunctor R).obj U).map
          (DerivedCategory.Q.map (cycleHom w) ≫ g) =
      (((canonicalDerivedTensorProductFunctor R).map
          (DerivedCategory.Q.map (cycleHom z))).app (DerivedCategory.Q.obj (singleR R j)) ≫
        ((canonicalDerivedTensorProductFunctor R).obj (DerivedCategory.Q.obj X)).map
          (DerivedCategory.Q.map (cycleHom w))) ≫
        (((canonicalDerivedTensorProductFunctor R).map f).app (DerivedCategory.Q.obj Y) ≫
          ((canonicalDerivedTensorProductFunctor R).obj U).map g) := by
    simp only [CategoryTheory.Functor.map_comp, NatTrans.comp_app, Category.assoc]
    congr 1
    rw [← Category.assoc, ← Category.assoc]
    congr 1
    exact (((canonicalDerivedTensorProductFunctor R).map f).naturality _).symm
  rw [tensor_cycleClass_comp z w f g, hT, CategoryTheory.Functor.map_comp, ← Category.assoc,
    ← h1]
  simp only [Category.assoc]

end TorProducts

end RingTheory
