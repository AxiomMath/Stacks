module

public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.ReductionTower
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.Slice
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.SliceExtension

/-!
# The tower of derived reductions and restriction to a slice site

Let `(C, J)` be a site, `Λ` a commutative ring, `I ⊆ Λ` an ideal and `V` an object of `C`. For
a K-flat complex `P` of sheaves of `Λ`-modules, restriction to the slice site `C/V` carries the
tower of derived reductions `n ↦ P ⊗_Λ^L \underline{Λ/Iⁿ}` to the tower of derived reductions of
the restriction `P|_V`, compatibly with the transition maps.

Both towers are computed termwise: for a left K-flat complex the derived tensor product with a
sheaf in degree zero is the termwise tensor product (`Stacks.ModuleSheaf.derivedTensorSingleIso`),
and `P|_V` is again K-flat (`Stacks.ModuleSheaf.kFlat_overPullback`). Restriction is exact and
monoidal, so it carries the termwise tensor product to the termwise tensor product of the
restrictions, and it carries constant sheaves to constant sheaves.

## Main definitions

* `Stacks.ModuleSheaf.overPullbackTensorIso`: restriction to `C/V` commutes with the tensor
  product, as an isomorphism of bifunctors.
* `Stacks.ModuleSheaf.derivedReductionTowerOverPullbackIso`: the isomorphism of towers
  `(P ⊗_Λ^L \underline{Λ/Iⁿ})|_V ≅ P|_V ⊗_Λ^L \underline{Λ/Iⁿ}` for K-flat `P`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CochainComplex.KFlatBifunctor

universe t t' w v u

namespace Stacks.ModuleSheaf

attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory monoidalClosed
  CochainComplex.braidedCategory derivedMonoidal

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (Λ : Type w) [CommRing Λ] [UnivLE.{max u v, w}] (V : C)

/-- **Restriction to a slice site commutes with the tensor product**, as an isomorphism of
bifunctors: `(M ⊗ N)|_V ≅ M|_V ⊗ N|_V`, the inverse of the monoidal structure of restriction. -/
def overPullbackTensorIso :
    curriedTensor (Sheaf J (ModuleCat.{w} Λ)) ⋙
        (Functor.whiskeringRight _ _ _).obj (J.overPullback (ModuleCat.{w} Λ) V) ≅
      J.overPullback (ModuleCat.{w} Λ) V ⋙ curriedTensor (Sheaf (J.over V) (ModuleCat.{w} Λ)) ⋙
        (Functor.whiskeringLeft _ _ _).obj (J.overPullback (ModuleCat.{w} Λ) V) :=
  letI := overPullbackMonoidal J Λ V
  NatIso.ofComponents (fun M => NatIso.ofComponents
      (fun N => (Functor.Monoidal.μIso (J.overPullback (ModuleCat.{w} Λ) V) M N).symm)
      (fun g => by simp))
    (fun f => by
      ext N : 2
      simp)

variable (I : Ideal Λ) [HasDerivedCategory.{t} (Sheaf J (ModuleCat.{w} Λ))]
  [HasDerivedCategory.{t'} (Sheaf (J.over V) (ModuleCat.{w} Λ))]

/-- **Restriction to a slice site commutes with the derived reductions of a K-flat complex**,
compatibly with the transition maps: for a K-flat complex `P` of sheaves of `Λ`-modules, the
restriction to `C/V` of the tower `n ↦ P ⊗_Λ^L \underline{Λ/Iⁿ}` is the tower of derived
reductions of `P|_V`. Both are the termwise tensor products with the constant sheaves
`\underline{Λ/Iⁿ}`, `P|_V` being K-flat. -/
def derivedReductionTowerOverPullbackIso {P : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ}
    (hP : KFlat (curriedTensor (Sheaf J (ModuleCat.{w} Λ))) P) :
    letI := preservesFiniteLimits_overPullback J Λ V
    letI := preservesFiniteColimits_overPullback J Λ V
    derivedReductionTower J Λ I (DerivedCategory.Q.obj P) ⋙
        (J.overPullback (ModuleCat.{w} Λ) V).mapDerivedCategory ≅
      derivedReductionTower (J.over V) Λ I (DerivedCategory.Q.obj
        (((J.overPullback (ModuleCat.{w} Λ) V).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          P)) :=
  letI := preservesFiniteLimits_overPullback J Λ V
  letI := preservesFiniteColimits_overPullback J Λ V
  let A := ModuleCat.{w} Λ
  let jV := J.overPullback A V
  let P' := (jV.mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  let q := AlgebraicGeometry.ProEtale.adicQuotientModuleSystem Λ I (ModuleCat.of Λ Λ)
  let cJ := constantSheaf J A
  let cV := constantSheaf (J.over V) A
  let sJ := HomologicalComplex.single (Sheaf J A) (ComplexShape.up ℤ) 0
  let sV := HomologicalComplex.single (Sheaf (J.over V) A) (ComplexShape.up ℤ) 0
  let hPL := CochainComplex.KFlatMonoidal.kFlatLeft_of_kFlat _ hP
  let hP'L := CochainComplex.KFlatMonoidal.kFlatLeft_of_kFlat _ (kFlat_overPullback V hP)
  let e₁ : derivedReductionTower J Λ I (DerivedCategory.Q.obj P) ⋙ jV.mapDerivedCategory ≅
      (q ⋙ cJ) ⋙ (sJ ⋙ DerivedCategory.Q ⋙ tensorLeft (DerivedCategory.Q.obj P)) ⋙
        jV.mapDerivedCategory :=
    Functor.isoWhiskerLeft (q ⋙ cJ) (Functor.isoWhiskerRight (Functor.isoWhiskerRight
      (DerivedCategory.singleFunctorIsoCompQ (Sheaf J A) 0) _) jV.mapDerivedCategory)
  let e₂ : (q ⋙ cJ) ⋙ (sJ ⋙ DerivedCategory.Q ⋙ tensorLeft (DerivedCategory.Q.obj P)) ⋙
        jV.mapDerivedCategory ≅
      (q ⋙ cJ) ⋙ (rowFunctor (curriedTensor _) P ⋙ DerivedCategory.Q) ⋙
        jV.mapDerivedCategory :=
    Functor.isoWhiskerLeft (q ⋙ cJ) (Functor.isoWhiskerRight (derivedTensorSingleIso hPL) _)
  let e₃ : (q ⋙ cJ) ⋙ (rowFunctor (curriedTensor _) P ⋙ DerivedCategory.Q) ⋙
        jV.mapDerivedCategory ≅
      (q ⋙ cJ) ⋙ (rowFunctor (curriedTensor _) P ⋙ jV.mapHomologicalComplex _) ⋙
        DerivedCategory.Q :=
    Functor.isoWhiskerLeft ((q ⋙ cJ) ⋙ rowFunctor (curriedTensor _) P)
      jV.mapDerivedCategoryFactors
  let e₄ : (q ⋙ cJ) ⋙ (rowFunctor (curriedTensor _) P ⋙ jV.mapHomologicalComplex _) ⋙
        DerivedCategory.Q ≅
      ((q ⋙ cJ) ⋙ jV) ⋙ rowFunctor (curriedTensor _) P' ⋙ DerivedCategory.Q :=
    Functor.isoWhiskerLeft (q ⋙ cJ) (Functor.isoWhiskerRight
      (mapRowFunctorIso (curriedTensor _) (curriedTensor _) (overPullbackTensorIso J Λ V) P)
      DerivedCategory.Q)
  let e₅ : ((q ⋙ cJ) ⋙ jV) ⋙ rowFunctor (curriedTensor _) P' ⋙ DerivedCategory.Q ≅
      (q ⋙ cV) ⋙ rowFunctor (curriedTensor _) P' ⋙ DerivedCategory.Q :=
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft q
      (Stacks.ConstantSheaf.overPullbackConstantSheafIso J A V).symm) _
  let e₆ : (q ⋙ cV) ⋙ rowFunctor (curriedTensor _) P' ⋙ DerivedCategory.Q ≅
      (q ⋙ cV) ⋙ sV ⋙ DerivedCategory.Q ⋙ tensorLeft (DerivedCategory.Q.obj P') :=
    Functor.isoWhiskerLeft (q ⋙ cV) (derivedTensorSingleIso hP'L).symm
  let e₇ : (q ⋙ cV) ⋙ sV ⋙ DerivedCategory.Q ⋙ tensorLeft (DerivedCategory.Q.obj P') ≅
      derivedReductionTower (J.over V) Λ I (DerivedCategory.Q.obj P') :=
    Functor.isoWhiskerLeft (q ⋙ cV) ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (DerivedCategory.singleFunctorIsoCompQ (Sheaf (J.over V) A) 0).symm
        (tensorLeft (DerivedCategory.Q.obj P')))
  e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄ ≪≫ e₅ ≪≫ e₆ ≪≫ e₇

end Stacks.ModuleSheaf

end
