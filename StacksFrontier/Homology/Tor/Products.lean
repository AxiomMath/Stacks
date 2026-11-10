module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Monoidal.Limits.Cokernels
public import StacksFrontier.Homology.KFlat.Resolution
public import StacksFrontier.Homology.Tor.DerivedTensor
public import StacksCore.Tactic.StacksAttribute

@[expose] public noncomputable section

/-!
# Products on the cohomology of a derived tensor product

For two objects `K` and `L` of the derived category of modules over a commutative ring,
tensoring cocycle representatives gives a map from `Hⁱ(K) ⊗ Hʲ(L)` to `Hⁱ⁺ʲ(K ⊗ᴸ L)`.

## Main definitions

* `RingTheory.TorProducts.CohomologyTensorProduct` packages the cohomology product together
  with its value on pure tensors represented by cocycles.

## Main results

* `RingTheory.TorProducts.cohomologyTensorProduct` is the canonical product on the cohomology
  of any two objects of the derived category.
* `RingTheory.TorProducts.cohomologyTensorProduct_map_cocycles` gives its defining cocycle
  formula on suitable K-flat representatives.

## Implementation notes

The cocycle formula is recorded after choosing K-flat representatives of both derived objects.
This is a sufficient instance of the source's construction, which only requires one factor to be
K-flat, and allows the canonical comparison supplied by the derived tensor product to be used
directly. The statement makes one such choice and does not assert coherence across all choices.

## References

* [The Stacks Project, Tag 068H][stacks-project]
-/

open CategoryTheory MonoidalCategory Category CochainComplex.DerivedTensor

universe u

namespace RingTheory.TorProducts

attribute [local instance] HasDerivedCategory.standard

variable {R : Type u} [CommRing R]

/-- A map `Hⁱ(K) ⊗[R] Hʲ(L) ⟶ Hⁱ⁺ʲ(K ⊗ᴸ[R] L)`, together with K-flat
representatives on which it sends the tensor of two cocycle classes to the class of their
tensor. -/
public structure CohomologyTensorProduct
    (K L : DObj R) (i j : ℤ) where
  /-- The product map on cohomology. -/
  map :
    (DerivedCategory.homologyFunctor (ModuleCat R) i).obj K ⊗
        (DerivedCategory.homologyFunctor (ModuleCat R) j).obj L ⟶
      (DerivedCategory.homologyFunctor (ModuleCat R) (i + j)).obj
        (((canonicalDerivedTensorProductFunctor R).obj K).obj L)
  /-- There are K-flat representatives for which `map` is induced by tensoring cocycles. -/
  maps_cocycles :
    ∃ (P Q : CochainComplex (ModuleCat R) ℤ)
      (hP : P.KFlat) (hQ : Q.KFlat)
      (eP : DerivedCategory.Q.obj P ≅ K) (eQ : DerivedCategory.Q.obj Q ≅ L)
      (z : P.cycles i ⊗ Q.cycles j ⟶ (P ⊗ Q).cycles (i + j)),
      z ≫ (P ⊗ Q).iCycles (i + j) =
          (P.iCycles i ⊗ₘ Q.iCycles j) ≫
            HomologicalComplex.ιTensorObj P Q i j (i + j) rfl ∧
        (P.homologyπ i ⊗ₘ Q.homologyπ j) ≫
              ((DerivedCategory.homologyFunctorFactors (ModuleCat R) i).inv.app P ⊗ₘ
                (DerivedCategory.homologyFunctorFactors (ModuleCat R) j).inv.app Q) ≫
              ((DerivedCategory.homologyFunctor (ModuleCat R) i).map eP.hom ⊗ₘ
                (DerivedCategory.homologyFunctor (ModuleCat R) j).map eQ.hom) ≫
              map ≫
              (DerivedCategory.homologyFunctor (ModuleCat R) (i + j)).map
                (((canonicalDerivedTensorProductFunctor R).map eP.inv).app L ≫
                  ((canonicalDerivedTensorProductFunctor R).obj
                    (DerivedCategory.Q.obj P)).map eQ.inv ≫
                  ((canonicalDerivedTensorProduct R).comparison P Q hP hQ).hom) ≫
              (DerivedCategory.homologyFunctorFactors
                (ModuleCat R) (i + j)).hom.app (P ⊗ Q) =
            z ≫ (P ⊗ Q).homologyπ (i + j)

private lemma tensor_cycles_comp_d
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (i j : ℤ) :
    ((P.iCycles i ⊗ₘ Q.iCycles j) ≫
        HomologicalComplex.ιTensorObj P Q i j (i + j) rfl) ≫
      (P ⊗ Q).d (i + j) (i + j + 1) = 0 := by
  change ((P.iCycles i ⊗ₘ Q.iCycles j) ≫
    HomologicalComplex.ιMapBifunctor P Q (MonoidalCategory.curriedTensor _) (ComplexShape.up ℤ)
      i j (i + j) rfl) ≫
    (HomologicalComplex.mapBifunctor P Q (MonoidalCategory.curriedTensor _)
      (ComplexShape.up ℤ)).d (i + j) (i + j + 1) = 0
  rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add]
  simp only [Category.assoc, HomologicalComplex.mapBifunctor.ι_D₁,
    HomologicalComplex.mapBifunctor.ι_D₂]
  rw [HomologicalComplex.mapBifunctor.d₁_eq P Q (MonoidalCategory.curriedTensor _) _
    (show (ComplexShape.up ℤ).Rel i (i + 1) by simp) j (i + j + 1)
    (by change i + 1 + j = i + j + 1; omega),
    HomologicalComplex.mapBifunctor.d₂_eq P Q (MonoidalCategory.curriedTensor _) _
    i (show (ComplexShape.up ℤ).Rel j (j + 1) by simp) (i + j + 1)
    (by change i + (j + 1) = i + j + 1; omega)]
  simp [tensorHom_def, whisker_exchange_assoc, ← comp_whiskerRight_assoc,
    ← whiskerLeft_comp_assoc]

private noncomputable def tensorCycles
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (i j : ℤ) :
    P.cycles i ⊗ Q.cycles j ⟶ (P ⊗ Q).cycles (i + j) :=
  (P ⊗ Q).liftCycles
    ((P.iCycles i ⊗ₘ Q.iCycles j) ≫
      HomologicalComplex.ιTensorObj P Q i j (i + j) rfl)
    (i + j + 1) (by simp) (tensor_cycles_comp_d P Q i j)

private lemma tensorCycles_i
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (i j : ℤ) :
    tensorCycles P Q i j ≫ (P ⊗ Q).iCycles (i + j) =
      (P.iCycles i ⊗ₘ Q.iCycles j) ≫
        HomologicalComplex.ιTensorObj P Q i j (i + j) rfl :=
  HomologicalComplex.liftCycles_i _ _ _ _ _

/-- **The tensor product of two epimorphisms of modules is an epimorphism**, because the tensor
product of two surjective maps is surjective. -/
public lemma epi_tensorHom {M N M' N' : ModuleCat.{u} R} (f : M ⟶ N) (g : M' ⟶ N')
    [Epi f] [Epi g] : Epi (f ⊗ₘ g) := by
  have hf := (ModuleCat.epi_iff_surjective f).1 ‹Epi f›
  have hg := (ModuleCat.epi_iff_surjective g).1 ‹Epi g›
  rw [ModuleCat.epi_iff_surjective]
  exact TensorProduct.map_surjective hf hg

/-- **The tensoring of cocycles exists** for any two cochain complexes of modules: a map
`Zⁱ(P) ⊗_R Zʲ(Q) ⟶ Zⁱ⁺ʲ(P ⊗ Q)` whose composition with the inclusion of cocycles is the
tensoring of the two inclusions.  This is the datum whose existence the `maps_cocycles` field of
`RingTheory.TorProducts.CohomologyTensorProduct` asserts at a choice of K-flat representatives.
It is recorded on its own because it needs no flatness, and because a consumer holding its own
pair of complexes cannot reach the one that choice made. -/
public lemma exists_tensorCycles
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (i j : ℤ) :
    ∃ z : P.cycles i ⊗ Q.cycles j ⟶ (P ⊗ Q).cycles (i + j),
      z ≫ (P ⊗ Q).iCycles (i + j) =
        (P.iCycles i ⊗ₘ Q.iCycles j) ≫
          HomologicalComplex.ιTensorObj P Q i j (i + j) rfl :=
  ⟨tensorCycles P Q i j, tensorCycles_i P Q i j⟩

private lemma tensor_left_boundary_d
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (i j : ℤ) :
    ((𝟙 (P.X (i - 1)) ⊗ₘ Q.iCycles j) ≫
        HomologicalComplex.ιTensorObj P Q (i - 1) j (i + j - 1) (by omega)) ≫
      (P ⊗ Q).d (i + j - 1) (i + j) =
    (P.d (i - 1) i ⊗ₘ Q.iCycles j) ≫
      HomologicalComplex.ιTensorObj P Q i j (i + j) rfl := by
  change ((𝟙 (P.X (i - 1)) ⊗ₘ Q.iCycles j) ≫
      HomologicalComplex.ιMapBifunctor P Q (MonoidalCategory.curriedTensor _)
        (ComplexShape.up ℤ) (i - 1) j (i + j - 1) (by dsimp; omega)) ≫
    (HomologicalComplex.mapBifunctor P Q (MonoidalCategory.curriedTensor _)
      (ComplexShape.up ℤ)).d (i + j - 1) (i + j) = _
  rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add]
  simp only [Category.assoc, HomologicalComplex.mapBifunctor.ι_D₁,
    HomologicalComplex.mapBifunctor.ι_D₂]
  rw [HomologicalComplex.mapBifunctor.d₁_eq P Q (MonoidalCategory.curriedTensor _) _
    (show (ComplexShape.up ℤ).Rel (i - 1) i by simp) j (i + j)
    rfl,
    HomologicalComplex.mapBifunctor.d₂_eq P Q (MonoidalCategory.curriedTensor _) _
    (i - 1) (show (ComplexShape.up ℤ).Rel j (j + 1) by simp) (i + j)
    (by change i - 1 + (j + 1) = i + j; omega)]
  simp [tensorHom_def, whisker_exchange_assoc, ← whiskerLeft_comp_assoc]

private lemma tensorCycles_left_boundary
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (i j : ℤ) :
    (P.toCycles (i - 1) i ⊗ₘ 𝟙 (Q.cycles j)) ≫
      tensorCycles P Q i j ≫ (P ⊗ Q).homologyπ (i + j) = 0 := by
  let x : P.X (i - 1) ⊗ Q.cycles j ⟶ (P ⊗ Q).X (i + j - 1) :=
    (𝟙 (P.X (i - 1)) ⊗ₘ Q.iCycles j) ≫
      HomologicalComplex.ιTensorObj P Q (i - 1) j (i + j - 1) (by omega)
  have h : (P.toCycles (i - 1) i ⊗ₘ 𝟙 (Q.cycles j)) ≫
      tensorCycles P Q i j =
      x ≫ (P ⊗ Q).toCycles (i + j - 1) (i + j) := by
    rw [← cancel_mono ((P ⊗ Q).iCycles (i + j))]
    simp only [Category.assoc, tensorCycles_i, HomologicalComplex.toCycles_i]
    change (P.toCycles (i - 1) i ⊗ₘ 𝟙 (Q.cycles j)) ≫
      (P.iCycles i ⊗ₘ Q.iCycles j) ≫
        HomologicalComplex.ιTensorObj P Q i j (i + j) rfl =
      x ≫ (P ⊗ Q).d (i + j - 1) (i + j)
    rw [tensor_left_boundary_d]
    simp [tensorHom_def, ← comp_whiskerRight_assoc]
  rw [← Category.assoc, h, Category.assoc,
    HomologicalComplex.toCycles_comp_homologyπ, Limits.comp_zero]

private lemma tensor_right_boundary_d
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (i j : ℤ) :
    ((P.iCycles i ⊗ₘ 𝟙 (Q.X (j - 1))) ≫
        HomologicalComplex.ιTensorObj P Q i (j - 1) (i + j - 1) (by omega)) ≫
      (P ⊗ Q).d (i + j - 1) (i + j) =
    ComplexShape.ε₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      ⟨i, j - 1⟩ •
      ((P.iCycles i ⊗ₘ Q.d (j - 1) j) ≫
        HomologicalComplex.ιTensorObj P Q i j (i + j) rfl) := by
  change ((P.iCycles i ⊗ₘ 𝟙 (Q.X (j - 1))) ≫
      HomologicalComplex.ιMapBifunctor P Q (MonoidalCategory.curriedTensor _)
        (ComplexShape.up ℤ) i (j - 1) (i + j - 1) (by dsimp; omega)) ≫
    (HomologicalComplex.mapBifunctor P Q (MonoidalCategory.curriedTensor _)
      (ComplexShape.up ℤ)).d (i + j - 1) (i + j) = _
  rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add]
  simp only [Category.assoc, HomologicalComplex.mapBifunctor.ι_D₁,
    HomologicalComplex.mapBifunctor.ι_D₂]
  rw [HomologicalComplex.mapBifunctor.d₁_eq P Q (MonoidalCategory.curriedTensor _) _
    (show (ComplexShape.up ℤ).Rel i (i + 1) by simp) (j - 1) (i + j)
    (by dsimp; omega),
    HomologicalComplex.mapBifunctor.d₂_eq P Q (MonoidalCategory.curriedTensor _) _
    i (show (ComplexShape.up ℤ).Rel (j - 1) j by simp) (i + j)
    (by dsimp)]
  simp [tensorHom_def, ← comp_whiskerRight_assoc,
    Linear.comp_units_smul]

private lemma tensorCycles_right_boundary
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (i j : ℤ) :
    (𝟙 (P.cycles i) ⊗ₘ Q.toCycles (j - 1) j) ≫
      tensorCycles P Q i j ≫ (P ⊗ Q).homologyπ (i + j) = 0 := by
  let ε : ℤˣ := ComplexShape.ε₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ)
    (ComplexShape.up ℤ) ⟨i, j - 1⟩
  let x : P.cycles i ⊗ Q.X (j - 1) ⟶ (P ⊗ Q).X (i + j - 1) :=
    ε • ((P.iCycles i ⊗ₘ 𝟙 (Q.X (j - 1))) ≫
      HomologicalComplex.ιTensorObj P Q i (j - 1) (i + j - 1) (by omega))
  have h : (𝟙 (P.cycles i) ⊗ₘ Q.toCycles (j - 1) j) ≫
      tensorCycles P Q i j =
      x ≫ (P ⊗ Q).toCycles (i + j - 1) (i + j) := by
    rw [← cancel_mono ((P ⊗ Q).iCycles (i + j))]
    simp only [Category.assoc, tensorCycles_i, HomologicalComplex.toCycles_i]
    change (𝟙 (P.cycles i) ⊗ₘ Q.toCycles (j - 1) j) ≫
      (P.iCycles i ⊗ₘ Q.iCycles j) ≫
        HomologicalComplex.ιTensorObj P Q i j (i + j) rfl =
      (ε • ((P.iCycles i ⊗ₘ 𝟙 (Q.X (j - 1))) ≫
        HomologicalComplex.ιTensorObj P Q i (j - 1) (i + j - 1) (by omega))) ≫
          (P ⊗ Q).d (i + j - 1) (i + j)
    rw [Linear.units_smul_comp, tensor_right_boundary_d, smul_smul,
      Int.units_mul_self, one_smul]
    simp only [← Category.assoc, tensorHom_comp_tensorHom,
      Category.id_comp, HomologicalComplex.toCycles_i]
  rw [← Category.assoc, h, Category.assoc,
    HomologicalComplex.toCycles_comp_homologyπ, Limits.comp_zero]

/-- The tensor of cocycles kills the boundaries in each variable, so it descends to homology. -/
private lemma coprod_desc_tensorCycles_homologyπ
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (i j : ℤ) :
    Limits.coprod.desc (P.toCycles (i - 1) i ▷ Q.cycles j)
        (P.cycles i ◁ Q.toCycles (j - 1) j) ≫
      (tensorCycles P Q i j ≫ (P ⊗ Q).homologyπ (i + j)) = 0 := by
  apply Limits.coprod.hom_ext
  · simp [← tensorHom_id, tensorCycles_left_boundary]
  · simp [← id_tensorHom, tensorCycles_right_boundary]

private noncomputable def tensorHomology
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (i j : ℤ) :
    P.homology i ⊗ Q.homology j ⟶ (P ⊗ Q).homology (i + j) :=
  (Limits.CokernelCofork.isColimitTensor
    (P.homologyIsCokernel (i - 1) i (by simp))
    (Q.homologyIsCokernel (j - 1) j (by simp))).desc
      (Limits.CokernelCofork.ofπ _ (coprod_desc_tensorCycles_homologyπ P Q i j))

private lemma homologyπ_tensorHomology
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (i j : ℤ) :
    (P.homologyπ i ⊗ₘ Q.homologyπ j) ≫ tensorHomology P Q i j =
      tensorCycles P Q i j ≫ (P ⊗ Q).homologyπ (i + j) := by
  unfold tensorHomology
  let cP := Limits.CokernelCofork.ofπ (P.homologyπ i)
    (P.toCycles_comp_homologyπ (i - 1) i)
  let cQ := Limits.CokernelCofork.ofπ (Q.homologyπ j)
    (Q.toCycles_comp_homologyπ (j - 1) j)
  change (cP.tensor cQ).π ≫
    (Limits.CokernelCofork.isColimitTensor
      (P.homologyIsCokernel (i - 1) i (by simp))
      (Q.homologyIsCokernel (j - 1) j (by simp))).desc
        (Limits.CokernelCofork.ofπ _ (coprod_desc_tensorCycles_homologyπ P Q i j)) =
      tensorCycles P Q i j ≫ (P ⊗ Q).homologyπ (i + j)
  exact Limits.Cofork.IsColimit.π_desc
    (hs := Limits.CokernelCofork.isColimitTensor
      (P.homologyIsCokernel (i - 1) i (by simp))
      (Q.homologyIsCokernel (j - 1) j (by simp)))
    (t := Limits.CokernelCofork.ofπ _ (coprod_desc_tensorCycles_homologyπ P Q i j))

/-- **Stacks 068H.** For any two objects `K` and `L` of `D(R)`, tensoring cocycles gives the
canonical map
`Hⁱ(K) ⊗[R] Hʲ(L) ⟶ Hⁱ⁺ʲ(K ⊗ᴸ[R] L)`.

The representative witness in the result specifies the source's formula
`[p] ⊗ [q] ↦ [p ⊗ q]`. -/
@[stacks 068H, no_expose]
public noncomputable def cohomologyTensorProduct
    (K L : DObj R) (i j : ℤ) : CohomologyTensorProduct K L i j := by
  let P := Classical.choose (CochainComplex.KFlat.exists_kFlat_representative K)
  have hP := (Classical.choose_spec (CochainComplex.KFlat.exists_kFlat_representative K)).1
  let eP := Classical.choice
    (Classical.choose_spec (CochainComplex.KFlat.exists_kFlat_representative K)).2
  let Q := Classical.choose (CochainComplex.KFlat.exists_kFlat_representative L)
  have hQ := (Classical.choose_spec (CochainComplex.KFlat.exists_kFlat_representative L)).1
  let eQ := Classical.choice
    (Classical.choose_spec (CochainComplex.KFlat.exists_kFlat_representative L)).2
  let T := canonicalDerivedTensorProductFunctor R
  let c : ((T.obj K).obj L) ≅ DerivedCategory.Q.obj (P ⊗ Q) :=
    ((T.mapIso eP.symm).app L) ≪≫
      ((T.obj (DerivedCategory.Q.obj P)).mapIso eQ.symm) ≪≫
        (canonicalDerivedTensorProduct R).comparison P Q hP hQ
  let α : P.homology i ⊗ Q.homology j ≅
      (DerivedCategory.homologyFunctor (ModuleCat R) i).obj K ⊗
        (DerivedCategory.homologyFunctor (ModuleCat R) j).obj L :=
    (((DerivedCategory.homologyFunctorFactors (ModuleCat R) i).symm.app P) ≪≫
      (DerivedCategory.homologyFunctor (ModuleCat R) i).mapIso eP) ⊗ᵢ
    (((DerivedCategory.homologyFunctorFactors (ModuleCat R) j).symm.app Q) ≪≫
      (DerivedCategory.homologyFunctor (ModuleCat R) j).mapIso eQ)
  let β : (DerivedCategory.homologyFunctor (ModuleCat R) (i + j)).obj
      ((T.obj K).obj L) ≅ (P ⊗ Q).homology (i + j) :=
    (DerivedCategory.homologyFunctor (ModuleCat R) (i + j)).mapIso c ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat R) (i + j)).app (P ⊗ Q)
  refine ⟨α.inv ≫ tensorHomology P Q i j ≫ β.inv,
    P, Q, hP, hQ, eP, eQ, tensorCycles P Q i j,
    tensorCycles_i P Q i j, ?_⟩
  let f : P.homology i ⊗ Q.homology j ⟶
      (DerivedCategory.homologyFunctor (ModuleCat R) i).obj K ⊗
        (DerivedCategory.homologyFunctor (ModuleCat R) j).obj L :=
    ((DerivedCategory.homologyFunctorFactors (ModuleCat R) i).inv.app P ⊗ₘ
      (DerivedCategory.homologyFunctorFactors (ModuleCat R) j).inv.app Q) ≫
    ((DerivedCategory.homologyFunctor (ModuleCat R) i).map eP.hom ⊗ₘ
      (DerivedCategory.homologyFunctor (ModuleCat R) j).map eQ.hom)
  let g : (DerivedCategory.homologyFunctor (ModuleCat R) (i + j)).obj
      ((T.obj K).obj L) ⟶ (P ⊗ Q).homology (i + j) :=
    (DerivedCategory.homologyFunctor (ModuleCat R) (i + j)).map
      (((canonicalDerivedTensorProductFunctor R).map eP.inv).app L ≫
        ((canonicalDerivedTensorProductFunctor R).obj
          (DerivedCategory.Q.obj P)).map eQ.inv ≫
        ((canonicalDerivedTensorProduct R).comparison P Q hP hQ).hom) ≫
      (DerivedCategory.homologyFunctorFactors
        (ModuleCat R) (i + j)).hom.app (P ⊗ Q)
  have hα :
      ((DerivedCategory.homologyFunctorFactors (ModuleCat R) i).inv.app P ⊗ₘ
          (DerivedCategory.homologyFunctorFactors (ModuleCat R) j).inv.app Q) ≫
        ((DerivedCategory.homologyFunctor (ModuleCat R) i).map eP.hom ⊗ₘ
          (DerivedCategory.homologyFunctor (ModuleCat R) j).map eQ.hom) = α.hom := by
    simp only [α, tensorIso_hom, tensorHom_comp_tensorHom]
    rfl
  have hβ : g = β.hom := by
    dsimp [g, β, c, T]
    rfl
  have hf : f ≫ α.inv = 𝟙 _ := by rw [show f = α.hom from hα, Iso.hom_inv_id]
  have hg : β.inv ≫ g = 𝟙 _ := by rw [hβ, Iso.inv_hom_id]
  calc
    _ = (P.homologyπ i ⊗ₘ Q.homologyπ j) ≫
        (f ≫ α.inv) ≫ tensorHomology P Q i j ≫ (β.inv ≫ g) := by
          dsimp [f, g]
          simp only [Category.assoc]
          rfl
    _ = tensorCycles P Q i j ≫ (P ⊗ Q).homologyπ (i + j) := by
          simpa only [hf, hg, Category.comp_id, Category.id_comp] using
            homologyπ_tensorHomology P Q i j

/-- On the chosen K-flat representatives, the canonical cohomology product sends the tensor of
two cocycle classes to the class of their tensor. -/
public lemma cohomologyTensorProduct_map_cocycles
    (K L : DObj R) (i j : ℤ) :
    ∃ (P Q : CochainComplex (ModuleCat R) ℤ)
      (hP : P.KFlat) (hQ : Q.KFlat)
      (eP : DerivedCategory.Q.obj P ≅ K) (eQ : DerivedCategory.Q.obj Q ≅ L)
      (z : P.cycles i ⊗ Q.cycles j ⟶ (P ⊗ Q).cycles (i + j)),
      z ≫ (P ⊗ Q).iCycles (i + j) =
          (P.iCycles i ⊗ₘ Q.iCycles j) ≫
            HomologicalComplex.ιTensorObj P Q i j (i + j) rfl ∧
        (P.homologyπ i ⊗ₘ Q.homologyπ j) ≫
              ((DerivedCategory.homologyFunctorFactors (ModuleCat R) i).inv.app P ⊗ₘ
                (DerivedCategory.homologyFunctorFactors (ModuleCat R) j).inv.app Q) ≫
              ((DerivedCategory.homologyFunctor (ModuleCat R) i).map eP.hom ⊗ₘ
                (DerivedCategory.homologyFunctor (ModuleCat R) j).map eQ.hom) ≫
              (cohomologyTensorProduct K L i j).map ≫
              (DerivedCategory.homologyFunctor (ModuleCat R) (i + j)).map
                (((canonicalDerivedTensorProductFunctor R).map eP.inv).app L ≫
                  ((canonicalDerivedTensorProductFunctor R).obj
                    (DerivedCategory.Q.obj P)).map eQ.inv ≫
                  ((canonicalDerivedTensorProduct R).comparison P Q hP hQ).hom) ≫
              (DerivedCategory.homologyFunctorFactors
                (ModuleCat R) (i + j)).hom.app (P ⊗ Q) =
            z ≫ (P ⊗ Q).homologyπ (i + j) :=
  (cohomologyTensorProduct K L i j).maps_cocycles

end RingTheory.TorProducts

end
