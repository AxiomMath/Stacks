module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationDerivedPushforwardCriterion
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringBySimplicialObjectDerivedPushforward
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringSituationDescentAb
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringBySimplicialObjectDerivedPushforwardUnconditional

/-!
# The second input of Stacks 0D8L is the acyclicity predicate of the simplicial-site situation

Let `(C, J)` be a site with fibre products, `X` an object of `C` and `K` a simplicial object of
`SR(C, X) = FormalCoproduct (Over X)`, and let `a` be the augmentation of the total site of `K`.
Stacks 0D8L is the invertibility of the canonical map `E ⟶ Ra_* a^{-1} E` on `D(C/X)`. Its second
input, the `Ra_*`-acyclicity of `a^{-1}` of a K-injective complex, is stated in
`StacksFrontier/CategoryTheory/Sites/Simplicial/HypercoveringObjectDerivedPushforward.lean` for the
functors `abelianTotalInverseImageOver` and `derivedAbelianTotalPushforwardOver`, and for an
augmentation of a simplicial-site situation (Stacks 0D6Z, 0D70) as the predicate
`CategoryTheory.SimplicialSiteSituation.Augmentation.InverseImageComputesDerivedPushforward`.
This file shows that the predicate for the situation `situation (J.over X) K` implies the second
input of Stacks 0D8L, for an arbitrary simplicial object `K`.

## Main definitions

* `CategoryTheory.SimplicialSemiRepresentable.abelianTotalPushforwardOverIso`: the direct image
  `a_*` of the simplicial-site situation is the direct image along the localization functor
  `j_total`.
* `CategoryTheory.SimplicialSemiRepresentable.homotopyAbelianTotalPushforwardOverIso` and
  `.homotopyTotalPushforwardOverIso`: the same isomorphism degreewise on unbounded homotopy
  categories, and after localization.
* `CategoryTheory.SimplicialSemiRepresentable.inverseImageComplexOverIso`: the two inverse images
  `a^{-1}I` of a complex `I` are isomorphic.

## Main results

* `CategoryTheory.SimplicialSemiRepresentable`
  `.isIso_derivedAbelianTotalPushforwardOverUnit_app_inverseImage`: if
  `InverseImageComputesDerivedPushforward` holds for the simplicial-site situation over `X`, then
  the comparison `a_* ⟶ Ra_*` is invertible at `a^{-1}I` for every K-injective complex `I`.
* `CategoryTheory.SimplicialSemiRepresentable.isIso_derivedAugmentationUnitOver_of_situation`:
  Stacks 0D8L from the invertibility of the unit of `a^{-1} ⊣ a_*` on abelian sheaves and that
  predicate.
* `CategoryTheory.SimplicialSemiRepresentable`
  `.isIso_derivedAbelianTotalPushforwardOverUnit_app_iff`: at a complex `M` at which the
  augmentation unit is invertible, the comparison `a_* ⟶ Ra_*` is invertible at `a^{-1}M` if and
  only if the map `M ⟶ Ra_* a^{-1} M` is invertible.

## References

* [Stacks Project, Tag 0D8L](https://stacks.math.columbia.edu/tag/0D8L)
* [Stacks Project, Tag 0D8G](https://stacks.math.columbia.edu/tag/0D8G)
* [Stacks Project, Tag 0D8B](https://stacks.math.columbia.edu/tag/0D8B)
* [Stacks Project, Tag 0D70](https://stacks.math.columbia.edu/tag/0D70)
* [Stacks Project, Tag 070K](https://stacks.math.columbia.edu/tag/070K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.SimplicialSiteSituation

universe u

namespace CategoryTheory.SimplicialSemiRepresentable

attribute [local instance] HasDerivedCategory.standard additive_abelianTotalPushforwardOver
  additive_abelianTotalInverseImageOver preservesFiniteColimits_abelianTotalInverseImageOver
  hasPointwiseRightDerivedFunctor_homotopyAbelianTotalPushforwardOver
  hasRightDerivedFunctor_homotopyAbelianTotalPushforwardOver

variable {C : Type u} [SmallCategory C] [HasPullbacks C] (J : GrothendieckTopology C) (X : C)
  (K : SimplicialObject (FormalCoproduct.{u} (Over X)))

/-- The direct image of abelian sheaves along the total augmentation of Stacks 0D70, read at the
simplicial-site situation over `X`, is the direct image along the localization functor
`j_total`. -/
def abelianTotalPushforwardOverIso :
    Augmentation.abelianTotalPushforward (situation (J.over X) K) (Cat.of (Over X)) (J.over X)
        (situationAugmentation (J.over X) K) ≅ abelianTotalPushforwardOver J X K :=
  Adjunction.rightAdjointUniq
    (Augmentation.abelianTotalAdjunction (situation (J.over X) K) (Cat.of (Over X)) (J.over X)
      (situationAugmentation (J.over X) K))
    ((abelianTotalAdjunctionOver J X K).ofNatIsoLeft
      (situationTotalInverseImageAbIso (J.over X) K).symm)

/-- The isomorphism `abelianTotalPushforwardOverIso`, applied degreewise on unbounded homotopy
categories. -/
def homotopyAbelianTotalPushforwardOverIso :
    (Augmentation.abelianTotalPushforward (situation (J.over X) K) (Cat.of (Over X)) (J.over X)
        (situationAugmentation (J.over X) K)).mapHomotopyCategory (ComplexShape.up ℤ) ≅
      (abelianTotalPushforwardOver J X K).mapHomotopyCategory (ComplexShape.up ℤ) :=
  haveI hgen := Augmentation.additive_abelianTotalPushforward (situation (J.over X) K)
    (Cat.of (Over X)) (J.over X) (situationAugmentation (J.over X) K)
  haveI hover := additive_abelianTotalPushforwardOver J X K
  { hom := NatTrans.mapHomotopyCategory (abelianTotalPushforwardOverIso J X K).hom
      (ComplexShape.up ℤ)
    inv := NatTrans.mapHomotopyCategory (abelianTotalPushforwardOverIso J X K).inv
      (ComplexShape.up ℤ)
    hom_inv_id := by
      rw [← NatTrans.mapHomotopyCategory_comp, Iso.hom_inv_id, NatTrans.mapHomotopyCategory_id]
    inv_hom_id := by
      rw [← NatTrans.mapHomotopyCategory_comp, Iso.inv_hom_id, NatTrans.mapHomotopyCategory_id] }

/-- The isomorphism `homotopyAbelianTotalPushforwardOverIso` followed by the localization
`Qh`. -/
def homotopyTotalPushforwardOverIso :
    Augmentation.homotopyTotalPushforward (situation (J.over X) K) (Cat.of (Over X)) (J.over X)
        (situationAugmentation (J.over X) K) ≅ homotopyAbelianTotalPushforwardOver J X K :=
  Functor.isoWhiskerRight (homotopyAbelianTotalPushforwardOverIso J X K)
    (DerivedCategory.Qh (C := AbelianSheavesOver J X))

/-- If the degreewise direct image of the simplicial-site situation followed by localization
inverts a morphism `f`, then so does `homotopyAbelianTotalPushforwardOver`. -/
theorem isIso_homotopyAbelianTotalPushforwardOver_map
    {M N : HomotopyCategory (Sheaf ((situation (J.over X) K).totalTopology) AddCommGrpCat.{u})
      (ComplexShape.up ℤ)} (f : M ⟶ N)
    (hf : IsIso ((Augmentation.homotopyTotalPushforward (situation (J.over X) K)
      (Cat.of (Over X)) (J.over X) (situationAugmentation (J.over X) K)).map f)) :
    IsIso ((homotopyAbelianTotalPushforwardOver J X K).map f) :=
  (NatIso.isIso_map_iff (homotopyTotalPushforwardOverIso J X K) f).mp hf

/-- The comparison `a_*L ⟶ Ra_*L` is invertible at a complex `L` as soon as the degreewise
direct image inverts one quasi-isomorphism of `L` into a K-injective complex. -/
theorem isIso_derivedAbelianTotalPushforwardOverUnit_app_of_quasiIso
    {L Jc : CochainComplex (Sheaf ((situation (J.over X) K).totalTopology) AddCommGrpCat.{u}) ℤ}
    (hJc : Jc.IsKInjective)
    (q : L ⟶ Jc) (hq : QuasiIso q)
    (hF : IsIso ((homotopyAbelianTotalPushforwardOver J X K).map
      ((HomotopyCategory.quotient (Sheaf ((situation (J.over X) K).totalTopology) AddCommGrpCat.{u})
        (ComplexShape.up ℤ)).map q))) :
    IsIso ((derivedAbelianTotalPushforwardOverUnit J X K).app
      ((HomotopyCategory.quotient (Sheaf ((situation (J.over X) K).totalTopology) AddCommGrpCat.{u})
        (ComplexShape.up ℤ)).obj L)) :=
  Functor.isIso_rightDerivedUnit_app_of_quasiIso (homotopyAbelianTotalPushforwardOver J X K)
    Stacks.Cohomology.Localization.enoughKInjectives DerivedCategory.Qh
    (derivedAbelianTotalPushforwardOver J X K)
    (derivedAbelianTotalPushforwardOverUnit J X K) hJc q hq hF

/-- The inverse images of a complex `I` of abelian sheaves on `C/X` along
`abelianTotalInverseImageOver` and along `Augmentation.totalInverseImageAb` are isomorphic. -/
def inverseImageComplexOverIso (I : CochainComplex (AbelianSheavesOver J X) ℤ) :
    ((abelianTotalInverseImageOver J X K).mapHomologicalComplex (ComplexShape.up ℤ)).obj I ≅
      ((Augmentation.totalInverseImageAb (situation (J.over X) K) (Cat.of (Over X)) (J.over X)
        (situationAugmentation (J.over X) K)).mapHomologicalComplex (ComplexShape.up ℤ)).obj I :=
  haveI := Augmentation.additive_totalInverseImageAb (situation (J.over X) K)
    (Cat.of (Over X)) (J.over X) (situationAugmentation (J.over X) K)
  haveI := additive_abelianTotalInverseImageOver J X K
  haveI := Functor.preservesZeroMorphisms_of_additive
    (F := Augmentation.totalInverseImageAb (situation (J.over X) K) (Cat.of (Over X)) (J.over X)
      (situationAugmentation (J.over X) K))
  haveI := Functor.preservesZeroMorphisms_of_additive
    (F := abelianTotalInverseImageOver J X K)
  (NatIso.mapHomologicalComplex (situationTotalInverseImageAbIso (J.over X) K)
    (ComplexShape.up ℤ)).symm.app I

/-- If the degreewise direct image followed by localization inverts the class of a morphism `q`
out of `a⁻¹I`, it inverts the class of `(inverseImageComplexOverIso J X K I).hom ≫ q`. -/
theorem isIso_homotopyAbelianTotalPushforwardOver_map_quotient_comp
    (I : CochainComplex (AbelianSheavesOver J X) ℤ)
    {Jc : CochainComplex (Sheaf ((situation (J.over X) K).totalTopology) AddCommGrpCat.{u}) ℤ}
    (q : ((Augmentation.totalInverseImageAb (situation (J.over X) K) (Cat.of (Over X))
      (J.over X) (situationAugmentation (J.over X) K)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I ⟶ Jc)
    (hq : IsIso ((homotopyAbelianTotalPushforwardOver J X K).map
      ((HomotopyCategory.quotient (Sheaf ((situation (J.over X) K).totalTopology) AddCommGrpCat.{u})
        (ComplexShape.up ℤ)).map q))) :
    IsIso ((homotopyAbelianTotalPushforwardOver J X K).map
      ((HomotopyCategory.quotient (Sheaf ((situation (J.over X) K).totalTopology) AddCommGrpCat.{u})
        (ComplexShape.up ℤ)).map
        ((inverseImageComplexOverIso J X K I).hom ≫ q))) := by
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
  infer_instance

/-- If `InverseImageComputesDerivedPushforward` holds for the simplicial-site situation over
`X`, then for a K-injective complex `I` and a quasi-isomorphism `q` of `a⁻¹I` into a K-injective
complex, the degreewise direct image followed by localization inverts the class of `q`. -/
theorem isIso_homotopyTotalPushforward_map_quotient_of_inverseImageComputes
    (h : Augmentation.InverseImageComputesDerivedPushforward (situation (J.over X) K)
      (Cat.of (Over X)) (J.over X) (situationAugmentation (J.over X) K))
    (I : CochainComplex (AbelianSheavesOver J X) ℤ) (hI : I.IsKInjective)
    {Jc : CochainComplex (Sheaf ((situation (J.over X) K).totalTopology) AddCommGrpCat.{u}) ℤ}
    (hJc : Jc.IsKInjective)
    (q : ((Augmentation.totalInverseImageAb (situation (J.over X) K) (Cat.of (Over X))
      (J.over X) (situationAugmentation (J.over X) K)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I ⟶ Jc) (hqq : QuasiIso q) :
    IsIso ((Augmentation.homotopyTotalPushforward (situation (J.over X) K) (Cat.of (Over X))
      (J.over X) (situationAugmentation (J.over X) K)).map
        ((HomotopyCategory.quotient
          (Sheaf ((situation (J.over X) K).totalTopology) AddCommGrpCat.{u})
          (ComplexShape.up ℤ)).map q)) :=
  Augmentation.isIso_homotopyTotalPushforward_map_of_inverseImageComputesDerivedPushforward
    (situation (J.over X) K) (Cat.of (Over X)) (J.over X) (situationAugmentation (J.over X) K)
    h I hI hJc q hqq

/-- If `InverseImageComputesDerivedPushforward` holds for the simplicial-site situation over
`X`, then for a K-injective complex `I` and a quasi-isomorphism `q` of `a⁻¹I` into a K-injective
complex, `homotopyAbelianTotalPushforwardOver` inverts the class of `q`. -/
theorem isIso_homotopyAbelianTotalPushforwardOver_map_quotient_of_inverseImageComputes
    (h : Augmentation.InverseImageComputesDerivedPushforward (situation (J.over X) K)
      (Cat.of (Over X)) (J.over X) (situationAugmentation (J.over X) K))
    (I : CochainComplex (AbelianSheavesOver J X) ℤ) (hI : I.IsKInjective)
    {Jc : CochainComplex (Sheaf ((situation (J.over X) K).totalTopology) AddCommGrpCat.{u}) ℤ}
    (hJc : Jc.IsKInjective)
    (q : ((Augmentation.totalInverseImageAb (situation (J.over X) K) (Cat.of (Over X))
      (J.over X) (situationAugmentation (J.over X) K)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I ⟶ Jc) (hqq : QuasiIso q) :
    IsIso ((homotopyAbelianTotalPushforwardOver J X K).map
      ((HomotopyCategory.quotient (Sheaf ((situation (J.over X) K).totalTopology) AddCommGrpCat.{u})
        (ComplexShape.up ℤ)).map q)) :=
  isIso_homotopyAbelianTotalPushforwardOver_map J X K
    ((HomotopyCategory.quotient (Sheaf ((situation (J.over X) K).totalTopology) AddCommGrpCat.{u})
      (ComplexShape.up ℤ)).map q)
    (isIso_homotopyTotalPushforward_map_quotient_of_inverseImageComputes J X K h I hI hJc q hqq)

/-- If `CategoryTheory.SimplicialSiteSituation.Augmentation.InverseImageComputesDerivedPushforward`
holds for the simplicial-site situation over `X`, `I` is a K-injective complex and `q` is a
quasi-isomorphism of `a⁻¹I` into a K-injective complex, then the comparison `a_* ⟶ Ra_*` is
invertible at the class of the complex `a⁻¹I`. -/
theorem isIso_derivedAbelianTotalPushforwardOverUnit_app_quotient_of_quasiIso
    (h : Augmentation.InverseImageComputesDerivedPushforward (situation (J.over X) K)
      (Cat.of (Over X)) (J.over X) (situationAugmentation (J.over X) K))
    (I : CochainComplex (AbelianSheavesOver J X) ℤ) (hI : I.IsKInjective)
    {Jc : CochainComplex (Sheaf ((situation (J.over X) K).totalTopology) AddCommGrpCat.{u}) ℤ}
    (hJc : Jc.IsKInjective)
    (q : ((Augmentation.totalInverseImageAb (situation (J.over X) K) (Cat.of (Over X))
      (J.over X) (situationAugmentation (J.over X) K)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I ⟶ Jc) (hqq : QuasiIso q) :
    IsIso ((derivedAbelianTotalPushforwardOverUnit J X K).app
      ((HomotopyCategory.quotient (Sheaf ((situation (J.over X) K).totalTopology) AddCommGrpCat.{u})
        (ComplexShape.up ℤ)).obj
        (((abelianTotalInverseImageOver J X K).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I))) := by
  exact isIso_derivedAbelianTotalPushforwardOverUnit_app_of_quasiIso J X K hJc
    ((inverseImageComplexOverIso J X K I).hom ≫ q) inferInstance
    (isIso_homotopyAbelianTotalPushforwardOver_map_quotient_comp J X K I q
      (isIso_homotopyAbelianTotalPushforwardOver_map_quotient_of_inverseImageComputes
        J X K h I hI hJc q hqq))

/-- If `InverseImageComputesDerivedPushforward` holds for the simplicial-site situation over
`X`, then the comparison `a_* ⟶ Ra_*` is invertible at the class of the complex `a⁻¹I` for every
K-injective complex `I`. -/
theorem isIso_derivedAbelianTotalPushforwardOverUnit_app_quotient_inverseImage
    (h : Augmentation.InverseImageComputesDerivedPushforward (situation (J.over X) K)
      (Cat.of (Over X)) (J.over X) (situationAugmentation (J.over X) K))
    (I : CochainComplex (AbelianSheavesOver J X) ℤ) (hI : I.IsKInjective) :
    IsIso ((derivedAbelianTotalPushforwardOverUnit J X K).app
      ((HomotopyCategory.quotient (Sheaf ((situation (J.over X) K).totalTopology) AddCommGrpCat.{u})
        (ComplexShape.up ℤ)).obj
        (((abelianTotalInverseImageOver J X K).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I))) := by
  obtain ⟨Jc, q, hJc, hqq⟩ := Stacks.Cohomology.Localization.enoughKInjectives
    (((Augmentation.totalInverseImageAb (situation (J.over X) K) (Cat.of (Over X)) (J.over X)
      (situationAugmentation (J.over X) K)).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
  exact isIso_derivedAbelianTotalPushforwardOverUnit_app_quotient_of_quasiIso J X K h I hI
    hJc q hqq

/-- If `CategoryTheory.SimplicialSiteSituation.Augmentation.InverseImageComputesDerivedPushforward`
holds for the simplicial-site situation over `X`, then the comparison `a_* ⟶ Ra_*` is invertible
at `a⁻¹I` for every K-injective complex `I`. -/
theorem isIso_derivedAbelianTotalPushforwardOverUnit_app_inverseImage
    (h : Augmentation.InverseImageComputesDerivedPushforward (situation (J.over X) K)
      (Cat.of (Over X)) (J.over X) (situationAugmentation (J.over X) K))
    (I : CochainComplex (AbelianSheavesOver J X) ℤ) (hI : I.IsKInjective) :
    IsIso ((derivedAbelianTotalPushforwardOverUnit J X K).app
      (((abelianTotalInverseImageOver J X K).mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient (AbelianSheavesOver J X)
          (ComplexShape.up ℤ)).obj I))) :=
  (NatTrans.isIso_app_iff_of_iso (derivedAbelianTotalPushforwardOverUnit J X K)
    ((Functor.mapHomotopyCategoryFactors (abelianTotalInverseImageOver J X K)
      (ComplexShape.up ℤ)).app I)).mpr
    (isIso_derivedAbelianTotalPushforwardOverUnit_app_quotient_inverseImage J X K h I hI)

/-- Stacks 0D8L: the canonical map `E ⟶ Ra_* a^{-1} E` on `D(C/X)` is invertible if the unit of
`a^{-1} ⊣ a_*` on abelian sheaves is invertible and `InverseImageComputesDerivedPushforward` holds
for the simplicial-site situation over `X`. -/
theorem isIso_derivedAugmentationUnitOver_of_situation
    (hunit : IsIso (abelianTotalAdjunctionOver J X K).unit)
    (hacyclic : Augmentation.InverseImageComputesDerivedPushforward (situation (J.over X) K)
      (Cat.of (Over X)) (J.over X) (situationAugmentation (J.over X) K)) :
    IsIso (derivedAugmentationUnitOver J X K) :=
  isIso_derivedAugmentationUnitOver_of_isIso_unit J X K hunit
    (isIso_derivedAbelianTotalPushforwardOverUnit_app_inverseImage J X K hacyclic)

/-- Let `M` be a complex at which the augmentation unit on homotopy categories is invertible.
Then the comparison `a_* ⟶ Ra_*` is invertible at `a⁻¹M` if and only if the canonical map
`M ⟶ Ra_* a^{-1} M` is invertible. -/
theorem isIso_derivedAbelianTotalPushforwardOverUnit_app_iff
    (M : HomotopyCategory (AbelianSheavesOver J X) (ComplexShape.up ℤ))
    (hunit : IsIso ((homotopyAugmentationUnitOver J X K).app M)) :
    IsIso ((derivedAbelianTotalPushforwardOverUnit J X K).app
        (((abelianTotalInverseImageOver J X K).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj M)) ↔
      IsIso ((derivedAugmentationUnitOverQh J X K).app M) := by
  rw [derivedAugmentationUnitOverQh_app, isIso_comp_left_iff, isIso_comp_right_iff]

end CategoryTheory.SimplicialSemiRepresentable

end
