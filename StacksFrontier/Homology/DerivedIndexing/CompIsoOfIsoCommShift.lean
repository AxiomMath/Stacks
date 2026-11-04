module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedDirectImageComposition
public import StacksFrontier.Homology.DerivedIndexing.NatTransCommShift
public import StacksFrontier.Homology.DerivedIndexing.CompositeCommShift

/-!
# The comparison `RH ≅ RF ⋙ RG` attached to `F ⋙ G ≅ H` commutes with the shift

Let `F : 𝒜 ⥤ ℬ` and `G : ℬ ⥤ 𝒞` be additive functors, `F` preserving injective objects, and
`e : F ⋙ G ≅ H`. The comparison `RH ≅ RF ⋙ RG` of right derived functors on bounded below
derived categories (`Stacks.EtaleCohomology.rightDerivedFunctorPlusCompIsoOfIso`) commutes with
the shift by `ℤ`.

## Main results

* `Stacks.DerivedIndexing.rightDerivedFunctorPlusIsoOfCompIso_hom_eq`: the comparison
  `R(F ⋙ G) ≅ RH` induced by `e` is the morphism of right derived functors induced by `e.hom`.
* `Stacks.DerivedIndexing.natTransCommShift_rightDerivedFunctorPlusCompIsoOfIso_inv`: the
  comparison `RF ⋙ RG ⟶ RH` commutes with the shift.
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits

namespace Stacks.DerivedIndexing

attribute [local instance 2000]
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

attribute [local instance] commShiftRightDerivedFunctorPlus
  natTransCommShiftRightDerivedFunctorPlusUnit

variable {C : Type*} {D : Type*} {E : Type*} [Category* C] [Category* D] [Category* E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  [EnoughInjectives C] [EnoughInjectives D]
  (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E) [F.Additive] [G.Additive] [H.Additive]

omit [HasDerivedCategory D] [EnoughInjectives D] in
/-- **The comparison `R(F ⋙ G) ≅ RH` induced by `e : F ⋙ G ≅ H` is the morphism of right derived
functors induced by `e.hom`.** -/
theorem rightDerivedFunctorPlusIsoOfCompIso_hom_eq (e : F ⋙ G ≅ H) :
    (Stacks.EtaleCohomology.rightDerivedFunctorPlusIsoOfCompIso F G H e).hom =
      rightDerivedFunctorPlusNatTrans e.hom := by
  show Functor.rightDerivedNatTrans _ _ (F ⋙ G).rightDerivedFunctorPlusUnit
      H.rightDerivedFunctorPlusUnit (HomotopyCategory.Plus.quasiIso C)
      (Functor.whiskerRight (Stacks.EtaleCohomology.mapHomotopyCategoryPlusIsoOfCompIso F G H e).hom
        DerivedCategory.Plus.Qh) =
    Functor.rightDerivedNatTrans _ _ (F ⋙ G).rightDerivedFunctorPlusUnit
      H.rightDerivedFunctorPlusUnit (HomotopyCategory.Plus.quasiIso C)
      (Functor.whiskerRight (Functor.mapHomotopyCategoryPlusNatTrans e.hom) DerivedCategory.Plus.Qh)
  congr 2
  exact NatTrans.ext (funext fun K ↦ Category.id_comp _)

variable [F.PreservesInjectiveObjects]

/-- **The comparison `RH ≅ RF ⋙ RG` attached to `F ⋙ G ≅ H` commutes with the shift**, in the
direction `RF ⋙ RG ⟶ RH`. -/
instance natTransCommShift_rightDerivedFunctorPlusCompIsoOfIso_inv (e : F ⋙ G ≅ H) :
    NatTrans.CommShift
      (Stacks.EtaleCohomology.rightDerivedFunctorPlusCompIsoOfIso F G H e).inv ℤ := by
  have : NatTrans.CommShift (Functor.rightDerivedFunctorPlusCompIso F G).hom ℤ :=
    natTransCommShift_rightDerivedPlusCompTrans F G
  have : NatTrans.CommShift
      (Stacks.EtaleCohomology.rightDerivedFunctorPlusIsoOfCompIso F G H e).hom ℤ := by
    rw [rightDerivedFunctorPlusIsoOfCompIso_hom_eq]
    exact natTransCommShift_rightDerivedFunctorPlusNatTrans e.hom
  change NatTrans.CommShift ((Functor.rightDerivedFunctorPlusCompIso F G).inv ≫
    (Stacks.EtaleCohomology.rightDerivedFunctorPlusIsoOfCompIso F G H e).hom) ℤ
  infer_instance

end Stacks.DerivedIndexing

end
