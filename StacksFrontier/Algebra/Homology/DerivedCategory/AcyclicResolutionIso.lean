module

public import StacksFrontier.Algebra.Homology.DerivedCategory.CompositionOfRightDerivedFunctors

/-!
# Computing a right derived functor on an acyclic resolution

Let `G : C ⥤ D` be an additive functor of abelian categories, `C` with enough injectives, and
let `A[0] ⟶ R` be a quasi-isomorphism onto a bounded below complex whose terms are right acyclic
for `G` (Stacks 015E). Then `RG(A[0])` is `G(R)`: the unit of `RG` is invertible at `R`.

## Main definitions

* `CategoryTheory.Functor.rightDerivedFunctorPlusSingleIsoOfAcyclic`:
  `Q(G(R)) ≅ ι(RG(A[0]))` in the derived category of `D`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C] (G : C ⥤ D) [G.Additive]

/-- `Q(R) ≅ A[0]` in `D⁺(C)` for a quasi-isomorphism `A[0] ⟶ R` onto a bounded below `R`. -/
def plusQhObjIsoSingleOfQuasiIso (A : C) (R : CochainComplex C ℤ) (n₀ : ℤ) [R.IsStrictlyGE n₀]
    (q : (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj A ⟶ R) [hq : QuasiIso q] :
    DerivedCategory.Plus.Qh.obj (⟨(HomotopyCategory.quotient C _).obj R,
        (HomotopyCategory.plus_quotient_obj_iff R).2 ⟨n₀, inferInstance⟩⟩ :
          HomotopyCategory.Plus C) ≅
      (DerivedCategory.Plus.singleFunctor C 0).obj A :=
  (ObjectProperty.fullyFaithfulι _).preimageIso
    ((DerivedCategory.quotientCompQhIso C).app R ≪≫ (asIso (DerivedCategory.Q.map q)).symm)

/-- **`RG(A[0]) ≅ G(R)` for a `G`-acyclic resolution `A[0] ⟶ R`** (Stacks 015E), in the derived
category of `D`. -/
def rightDerivedFunctorPlusSingleIsoOfAcyclic (A : C) (R : CochainComplex C ℤ) (n₀ : ℤ)
    [R.IsStrictlyGE n₀]
    (q : (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj A ⟶ R) [hq : QuasiIso q]
    (hR : ∀ n, G.rightAcyclic (R.X n)) :
    DerivedCategory.Q.obj ((G.mapHomologicalComplex _).obj R) ≅
      DerivedCategory.Plus.ι.obj
        (G.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor C 0).obj A)) :=
  let Kp : HomotopyCategory.Plus C := ⟨(HomotopyCategory.quotient C _).obj R,
    (HomotopyCategory.plus_quotient_obj_iff R).2 ⟨n₀, inferInstance⟩⟩
  haveI := isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic G Kp hR
  (DerivedCategory.quotientCompQhIso D).symm.app _ ≪≫
    DerivedCategory.Qh.mapIso ((G.mapHomotopyCategoryFactors _).symm.app R) ≪≫
    DerivedCategory.Plus.ι.mapIso (asIso (G.rightDerivedFunctorPlusUnit.app Kp)) ≪≫
    DerivedCategory.Plus.ι.mapIso
      (G.rightDerivedFunctorPlus.mapIso (plusQhObjIsoSingleOfQuasiIso A R n₀ q))

end CategoryTheory.Functor

end
