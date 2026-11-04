module

public import StacksFrontier.Homology.Tor.ProductOfCycleClasses
public import StacksFrontier.Homology.TensorComplex.SingleBifunctorTensorDegrees
public import StacksFrontier.Algebra.Homology.DerivedCategory.ProjectiveCorepresents

/-!
# The tensoring of the two generators is the class of an isomorphism

Let `R` be a commutative ring. The tensoring of classes of Tag 068H sends the generators of
`Hⁱ(R[-i])` and `Hʲ(R[-j])` to a class `tensorGen R i j` in `Hⁱ⁺ʲ(R[-i] ⊗^𝐋_R R[-j])`. Since
`R[-i-j]` corepresents `Hⁱ⁺ʲ`, this class is the class of exactly one morphism
`R[-i-j] ⟶ R[-i] ⊗^𝐋_R R[-j]`. This file shows that this morphism is the canonical isomorphism:
on the K-flat representatives the total tensor complex of `R[-i]` and `R[-j]` is `(R ⊗_R R)[-i-j]`,
the tensor product of the two generating cocycles is the generating cocycle `1 ⊗ 1`, and
`R ⊗_R R = R` sends it to `1`.

## Implementation notes

standard model: uses `RingTheory.TorProducts.tensorGen` and
`RingTheory.TorProducts.cohomologyTensorProduct`, which exist only there.

## Main definitions

* `RingTheory.TorProducts.singleTensorSingleIso`: `Tot(R[-i] ⊗_R R[-j]) ≅ R[-i-j]`, as cochain
  complexes.
* `RingTheory.TorProducts.generatorSplitting`: the isomorphism `R[-i-j] ≅ R[-i] ⊗^𝐋_R R[-j]`.

## Main results

* `RingTheory.TorProducts.singleFunctorCompHomologyFunctorIso_inv_app_eq_genClass`: the generator
  of `Hⁱ(R[-i])` given by Tag 06XS is the class of the generating cocycle.
* `RingTheory.TorProducts.homologyFromSingle_generatorSplitting`: the class of
  `generatorSplitting` is `tensorGen`.
* `RingTheory.TorProducts.isIso_of_homologyFromSingle_eq_tensorGen`: **a morphism
  `R[-i-j] ⟶ R[-i] ⊗^𝐋_R R[-j]` whose class is the tensoring of the generators is an
  isomorphism.**

## References

* [Stacks Project, Tag 068H](https://stacks.math.columbia.edu/tag/068H)
* [Stacks Project, Tag 06XS](https://stacks.math.columbia.edu/tag/06XS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CochainComplex.DerivedTensor CochainComplex.DerivedTensor.ToTotal

universe u

namespace RingTheory.TorProducts

attribute [local instance] HasDerivedCategory.standard

variable (R : Type u) [CommRing R]

/-- **The generator of `Hⁱ(R[-i])` of Tag 06XS is the class of the generating cocycle `1`.** -/
theorem singleFunctorCompHomologyFunctorIso_inv_app_eq_genClass (i : ℤ) :
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} R) i).inv.app
        (ModuleCat.of R R) = genClass R i := by
  have h₁ : (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} R) i).inv.app
        (ModuleCat.of R R) =
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) i (ModuleCat.of R R)).inv ≫
        (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) i).inv.app
          ((CochainComplex.singleFunctor (ModuleCat.{u} R) i).obj (ModuleCat.of R R)) := by
    simp [DerivedCategory.singleFunctorCompHomologyFunctorIso,
      DerivedCategory.singleFunctorsPostcompQIso]
    rfl
  have h₂ := HomologicalComplex.singleObjCyclesSelfIso_inv_homologyπ (C := ModuleCat.{u} R)
    (ComplexShape.up ℤ) i (ModuleCat.of R R)
  refine h₁.trans ?_
  show _ = cycleClass (singleCycle R i)
  rw [cycleClass_def]
  refine Eq.trans ?_ (Category.assoc _ _ _)
  exact (congrArg (· ≫ (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R)
    i).inv.app (singleR R i)) h₂.symm)

/-- **`Tot(R[-i] ⊗_R R[-j]) ≅ R[-i-j]`** as cochain complexes: the total complex of two single
complexes is the single complex of the tensor product (`mapBifunctorSingleSingleIso`), and
`R ⊗_R R = R`. -/
def singleTensorSingleIso (i j : ℤ) : singleR R i ⊗ singleR R j ≅ singleR R (i + j) :=
  HomologicalComplex.mapBifunctorSingleSingleIso (curriedTensor (ModuleCat.{u} R))
      (ModuleCat.of R R) (ModuleCat.of R R) i j ≪≫
    (HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) (i + j)).mapIso
      (λ_ (ModuleCat.of R R))

/-- **The canonical isomorphism `R[-i-j] ≅ R[-i] ⊗^𝐋_R R[-j]`**: the inverse of
`singleTensorSingleIso` followed by the K-flat comparison of the derived tensor product. -/
def generatorSplitting (i j : ℤ) :
    DerivedCategory.Q.obj (singleR R (i + j)) ≅
      ((canonicalDerivedTensorProductFunctor R).obj (DerivedCategory.Q.obj (singleR R i))).obj
        (DerivedCategory.Q.obj (singleR R j)) :=
  DerivedCategory.Q.mapIso (singleTensorSingleIso R i j).symm ≪≫
    ((canonicalDerivedTensorProduct R).comparison (singleR R i) (singleR R j)
      (kFlat_singleR R i) (kFlat_singleR R j)).symm

/-- In degree `i + j`, the inverse of `singleTensorSingleIso` is the summand inclusion of
`(i, j)`, read through the identifications of the terms of the single complexes with `R`. -/
theorem singleObjXSelf_inv_singleTensorSingleIso_inv_f (i j : ℤ) :
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (i + j) (ModuleCat.of R R)).inv ≫
        (singleTensorSingleIso R i j).inv.f (i + j) =
      (λ_ (ModuleCat.of R R)).inv ≫
        ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) i (ModuleCat.of R R)).inv ⊗ₘ
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) j (ModuleCat.of R R)).inv) ≫
        HomologicalComplex.ιTensorObj (singleR R i) (singleR R j) i j (i + j) rfl := by
  have hι := HomologicalComplex.ι_mapBifunctorSingleSingleIso_hom_f
    (curriedTensor (ModuleCat.{u} R)) (ModuleCat.of R R) (ModuleCat.of R R) i j
  rw [show (singleTensorSingleIso R i j).inv.f (i + j) =
      (HomologicalComplex.Hom.isoApp (singleTensorSingleIso R i j) (i + j)).inv from rfl,
    Iso.comp_inv_eq, show (HomologicalComplex.Hom.isoApp (singleTensorSingleIso R i j)
      (i + j)).hom = (singleTensorSingleIso R i j).hom.f (i + j) from rfl]
  simp only [singleTensorSingleIso, Iso.trans_hom, HomologicalComplex.comp_f, Functor.mapIso_hom,
    Category.assoc]
  have hι' : HomologicalComplex.ιTensorObj (singleR R i) (singleR R j) i j (i + j) rfl ≫
      (HomologicalComplex.mapBifunctorSingleSingleIso (curriedTensor (ModuleCat.{u} R))
        (ModuleCat.of R R) (ModuleCat.of R R) i j).hom.f (i + j) =
      ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) i (ModuleCat.of R R)).hom ⊗ₘ
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) j (ModuleCat.of R R)).hom) ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (i + j)
          (ModuleCat.of R R ⊗ ModuleCat.of R R)).inv := by
    refine hι.trans ?_
    rw [MonoidalCategory.tensorHom_def, Category.assoc]
    rfl
  rw [reassoc_of% hι', tensorHom_comp_tensorHom_assoc, Iso.inv_hom_id, Iso.inv_hom_id,
    tensorHom_id, id_whiskerRight, Category.id_comp, HomologicalComplex.single_map_f_self]
  simp

/-- On the generating cocycle, the inverse of `singleTensorSingleIso` is the tensor product of
the two generating cocycles. -/
theorem singleCycle_cyclesMap_singleTensorSingleIso_inv (i j : ℤ)
    (z₀ : (singleR R i).cycles i ⊗ (singleR R j).cycles j ⟶
      (singleR R i ⊗ singleR R j).cycles (i + j))
    (hz₀ : z₀ ≫ (singleR R i ⊗ singleR R j).iCycles (i + j) =
      ((singleR R i).iCycles i ⊗ₘ (singleR R j).iCycles j) ≫
        HomologicalComplex.ιTensorObj (singleR R i) (singleR R j) i j (i + j) rfl) :
    singleCycle R (i + j) ≫
        HomologicalComplex.cyclesMap (singleTensorSingleIso R i j).inv (i + j) =
      (λ_ (ModuleCat.of R R)).inv ≫ (singleCycle R i ⊗ₘ singleCycle R j) ≫ z₀ := by
  have hs (n : ℤ) : singleCycle R n ≫ (singleR R n).iCycles n =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) n (ModuleCat.of R R)).inv :=
    HomologicalComplex.singleObjCyclesSelfIso_inv_iCycles (C := ModuleCat.{u} R)
      (ComplexShape.up ℤ) n (ModuleCat.of R R)
  rw [← cancel_mono ((singleR R i ⊗ singleR R j).iCycles (i + j)), Category.assoc,
    HomologicalComplex.cyclesMap_i, ← Category.assoc, hs, Category.assoc, Category.assoc, hz₀,
    tensorHom_comp_tensorHom_assoc, hs, hs]
  exact singleObjXSelf_inv_singleTensorSingleIso_inv_f R i j

/-- **The class of `generatorSplitting` is the tensoring of the two generators.** -/
theorem homologyFromSingle_generatorSplitting (i j : ℤ) :
    DerivedCategory.homologyFromSingleLinearEquiv (ModuleCat.of R R)
        (((canonicalDerivedTensorProductFunctor R).obj (DerivedCategory.Q.obj (singleR R i))).obj
          (DerivedCategory.Q.obj (singleR R j))) (i + j) R (generatorSplitting R i j).hom =
      tensorGen R i j := by
  obtain ⟨z₀, hz₀⟩ : ∃ z₀ : (singleR R i).cycles i ⊗ (singleR R j).cycles j ⟶
      (singleR R i ⊗ singleR R j).cycles (i + j),
      z₀ ≫ (singleR R i ⊗ singleR R j).iCycles (i + j) =
        ((singleR R i).iCycles i ⊗ₘ (singleR R j).iCycles j) ≫
          HomologicalComplex.ιTensorObj (singleR R i) (singleR R j) i j (i + j) rfl :=
    exists_tensorCycles (singleR R i) (singleR R j) i j
  rw [← cancel_mono ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) (i + j)).map
    ((canonicalDerivedTensorProduct R).comparison (singleR R i) (singleR R j)
      (kFlat_singleR R i) (kFlat_singleR R j)).hom)]
  have h₁ := tensorGen_toTensor (R := R) i j z₀ hz₀
  rw [canonicalDerivedToTensorNatTrans_app_eq_comparison R _ _ (kFlat_singleR R i)
    (kFlat_singleR R j)] at h₁
  refine Eq.trans ?_ h₁.symm
  rw [← DerivedCategory.homologyFromSingleLinearEquiv_comp, generatorSplitting,
    Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    DerivedCategory.homologyFromSingleLinearEquiv_apply,
    singleFunctorCompHomologyFunctorIso_inv_app_eq_genClass, Functor.mapIso_hom, Iso.symm_hom,
    cycleClass_comp_map, comp_cycleClass,
    singleCycle_cyclesMap_singleTensorSingleIso_inv R i j z₀ hz₀,
    comp_cycleClass]

/-- **A morphism `R[-i-j] ⟶ R[-i] ⊗^𝐋_R R[-j]` whose class is the tensoring of the two generators
is an isomorphism**: it is `generatorSplitting`, because `R[-i-j]` corepresents `Hⁱ⁺ʲ`. -/
theorem isIso_of_homologyFromSingle_eq_tensorGen (i j : ℤ)
    (χ : DerivedCategory.Q.obj (singleR R (i + j)) ⟶
      ((canonicalDerivedTensorProductFunctor R).obj (DerivedCategory.Q.obj (singleR R i))).obj
        (DerivedCategory.Q.obj (singleR R j)))
    (hχ : DerivedCategory.homologyFromSingleLinearEquiv (ModuleCat.of R R)
        (((canonicalDerivedTensorProductFunctor R).obj (DerivedCategory.Q.obj (singleR R i))).obj
          (DerivedCategory.Q.obj (singleR R j))) (i + j) R χ = tensorGen R i j) :
    IsIso χ := by
  obtain rfl : χ = (generatorSplitting R i j).hom :=
    (DerivedCategory.homologyFromSingleLinearEquiv (ModuleCat.of R R) _ (i + j) R).injective
      (hχ.trans (homologyFromSingle_generatorSplitting R i j).symm)
  infer_instance

end RingTheory.TorProducts

end
