module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BaseChangeCondition
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.AbelianBaseChangeMap

/-!
# An exact functor applied to a resolution

Let `E : 𝒜 ⥤ ℬ` be an exact additive functor between abelian categories, with `𝒜` having enough
injectives, and let `K` be a bounded below complex of `𝒜` whose image in `D⁺(𝒜)` is `F[0]`.  The
image of `K` under `E` applied degreewise then has image `(E F)[0]` in `D⁺(ℬ)`.

Both steps are the exactness of `E`: the derived-functor unit of `RE` is invertible, so the
degreewise image of `K` computes `RE` of its image in `D⁺(𝒜)`; and `RE` commutes with the
degree-zero embedding.  Neither step needs `K` to consist of injective objects.

## Main definitions

* `Stacks.AlgebraicGeometry.ModuleBaseChange.exactResolutionIso`: the resulting isomorphism
  `Qh(E K) ≅ (E F)[0]`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.AlgebraicGeometry.ModuleBaseChange

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- **An exact functor carries a resolution to a resolution.**  If the bounded below complex `K`
of `𝒜` has image `F[0]` in `D⁺(𝒜)`, then the degreewise image of `K` under an exact functor `E`
has image `(E F)[0]` in `D⁺(ℬ)`. -/
def exactResolutionIso {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [EnoughInjectives A] (E : A ⥤ B) [E.Additive]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E] (K : HomotopyCategory.Plus A) (F : A)
    (e : DerivedCategory.Plus.Qh.obj K ≅ (DerivedCategory.Plus.singleFunctor A 0).obj F) :
    DerivedCategory.Plus.Qh.obj (E.mapHomotopyCategoryPlus.obj K) ≅
      (DerivedCategory.Plus.singleFunctor B 0).obj (E.obj F) :=
  letI : IsIso E.rightDerivedFunctorPlusUnit := Stacks.Cohomology.BaseChange.exactUnit_isIso E
  letI : IsIso (E.rightDerivedFunctorPlusUnit.app K) := NatIso.isIso_app_of_isIso _ _
  asIso (E.rightDerivedFunctorPlusUnit.app K) ≪≫ E.rightDerivedFunctorPlus.mapIso e ≪≫
    ((Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso E 0).app F).symm

/-- **Every object of the bounded below derived category is the image of a bounded below complex
of injective objects.**  This is the essential surjectivity half of the injective derivability
structure of `K⁺(𝒜)`. -/
theorem exists_injectiveComplex_iso {A : Type*} [Category* A] [Abelian A] [EnoughInjectives A] :
    ∀ E : DerivedCategory.Plus A, ∃ K : HomotopyCategory.Plus A,
      (∀ n : ℤ, Injective (K.obj.as.X n)) ∧
        Nonempty (DerivedCategory.Plus.Qh.obj K ≅ E) := fun E =>
  ⟨(InjectiveObject.ι A).mapHomotopyCategoryPlus.obj
      (((InjectiveObject.ι A).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).objPreimage E),
    fun _ => inferInstance,
    ⟨((InjectiveObject.ι A).mapHomotopyCategoryPlus ⋙
      DerivedCategory.Plus.Qh).objObjPreimageIso E⟩⟩

end Stacks.AlgebraicGeometry.ModuleBaseChange

end
