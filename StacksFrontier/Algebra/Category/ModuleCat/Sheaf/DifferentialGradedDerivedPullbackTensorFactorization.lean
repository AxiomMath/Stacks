module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedPullbackTensorFunctorComposition
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedTensorPullbackFunctors

/-!
# The derived pullback-tensor functor factors as derived pullback then derived tensor product

The functor `ℳ ↦ f^*ℳ ⊗_𝒜 𝒩` of Tag 0FTE is the pullback followed by the tensor product with
the bimodule, so it is the composite of the two special cases of Tag 0FTG: the pullback is
`ℳ ↦ f^*ℳ ⊗_𝒜 {}_𝒜 𝒜_𝒜`, the case of the diagonal bimodule, and the tensor product is
`ℳ ↦ id^*ℳ ⊗_𝒜 𝒩`, the case of the identity morphism of ringed sites. This file proves that
factorization — on differential graded modules, on the homotopy categories, and then on the
derived categories, where it says that **derived pullback followed by the derived tensor
product is the derived pullback-tensor functor**.

The only thing to check at the level of modules is that the pullback along the identity
morphism of ringed sites is the identity functor, which is `idPullbackData_functor_eq`: it is
the identity on objects by construction, and on homomorphisms by `idPullbackData_map`. The
tensor product with the diagonal bimodule is the identity functor by construction.

On the derived categories the statement is not an equality but an isomorphism, and it is
Tag 0FTI applied to the factorization: the composite of the two derived extensions is the left
derived functor of the composite of the two functors of Tag 0FTE, that composite is the functor
of Tag 0FTE for the given morphism, and a left derived functor is determined by the functor it
derives up to a unique isomorphism compatible with the counits.

## Main results

* `SheafOfModules.DifferentialGradedModule.idPullbackData_functor_eq`: the pullback along the
  identity morphism of ringed sites is the identity functor of `Mod^dg(𝒜, d)`.
* `SheafOfModules.DifferentialGradedModule.pullbackTensorFunctor_comp_eq`: the pullback of
  Tag 0FTG(2) followed by the tensor product of Tag 0FTG(1) is the functor of Tag 0FTE.
* `SheafOfModules.DifferentialGradedModule.pullbackTensor_comp_eq`: the same on the homotopy
  categories.
* `SheafOfModules.DifferentialGradedModule.exists_iso_derivedPullback_comp_derivedTensor`:
  derived pullback followed by the derived tensor product is the derived pullback-tensor functor,
  by an isomorphism of functors of the derived categories carrying the composed counit to the
  counit, for a pullback and a tensor product given by their universal properties and exactness
  packages. Tag 0FTH itself, along a morphism of ringed topoi, is
  `exists_iso_derivedPullbackTensorRingedTopos_derivedPullbackRingedTopos_comp_topos` in
  `DifferentialGradedToposDerivedPullbackComp.lean`.

## Implementation notes

The hypothesis `hgood` of the last result is the goodness half of Tag 0FSI(2) — the pullback of
a good right differential graded module is good — which is a hypothesis because the notion of
goodness used for the resolutions is a parameter of `GoodResolutionData`; it is what Tag 0FTI
needs in order for the counit of the second derived extension to be invertible where the first
is.

## References

* [Stacks Project, Tag 0FTE](https://stacks.math.columbia.edu/tag/0FTE)
* [Stacks Project, Tag 0FTG](https://stacks.math.columbia.edu/tag/0FTG)
* [Stacks Project, Tag 0FTI](https://stacks.math.columbia.edu/tag/0FTI)
* [Stacks Project, Tag 0FSI](https://stacks.math.columbia.edu/tag/0FSI)
-/

@[expose] public section

open CategoryTheory

universe t a a₂ m m₃ s z v u v₂ u₂

namespace SheafOfModules

namespace DifferentialGradedModule

section Factorization

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {C₂ : Type u₂} [Category.{v₂} C₂] {J₂ : GrothendieckTopology C₂}
  {R₂ : Sheaf J₂ RingCat.{t}}
  [HasSheafify J AddCommGrpCat.{s}] [J.WEqualsLocallyBijective AddCommGrpCat.{s}]
  [HasSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
  [HasSheafify J₂ AddCommGrpCat.{m₃}] [J₂.WEqualsLocallyBijective AddCommGrpCat.{m₃}]
  {w₂ : C₂ ⥤ C} {σ₂ : R₂.obj ⟶ w₂.op ⋙ R.obj}
  {A A' : DifferentialGradedAlgebra.{t, a} R} {B₂ : DifferentialGradedAlgebra.{t, a₂} R₂}
  {φ₂ : DifferentialGradedAlgebra.SemilinearHom w₂ σ₂ B₂ A}
  {N : DifferentialGradedBimodule.{t, a, z} A A'}
  {D : TensorFunctorData.{t, a, m, z, s} A A' N}
  {P₂ : PullbackData.{t, a, m, v, u, a₂, m₃} φ₂}
  {g : GoodResolutionData.{t, a, m, v, u} A}
  {g₂ : GoodResolutionData.{t, a₂, m₃, v₂, u₂} B₂}

omit [HasSheafify J AddCommGrpCat.{s}] [J.WEqualsLocallyBijective AddCommGrpCat.{s}]
  [HasSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}] in
/-- **The pullback along the identity morphism of ringed sites is the identity functor** of
`Mod^dg(𝒜, d)`: it is the identity on objects by construction, and the pullback of a
homomorphism is the homomorphism. -/
theorem idPullbackData_functor_eq :
    (idPullbackData.{t, a, m} (A := A)).functor = 𝟭 (DifferentialGradedModule.{t, a, m} A) :=
  CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ ψ => by
    change (idPullbackData (A := A)).map ψ = 𝟙 _ ≫ ψ ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id]
    exact idPullbackData_map ψ)

omit [HasSheafify J AddCommGrpCat.{s}] [J.WEqualsLocallyBijective AddCommGrpCat.{s}]
  [HasSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
  [HasSheafify J₂ AddCommGrpCat.{m₃}] [J₂.WEqualsLocallyBijective AddCommGrpCat.{m₃}] in
/-- **The factorization of the functor of Tag 0FTE.** The pullback `f^*` of Tag 0FTG(2),
followed by the tensor product `- ⊗_𝒜 𝒩` of Tag 0FTG(1), is the functor `ℳ ↦ f^*ℳ ⊗_𝒜 𝒩`. -/
theorem pullbackTensorFunctor_comp_eq :
    pullbackTensorFunctor P₂ (tensorFunctorDataDiagonal.{t, a, m} A) ⋙
        pullbackTensorFunctor (idPullbackData.{t, a, m} (A := A)) D =
      pullbackTensorFunctor P₂ D := by
  rw [pullbackTensorFunctor, pullbackTensorFunctor, pullbackTensorFunctor,
    idPullbackData_functor_eq]
  rfl

omit [HasSheafify J AddCommGrpCat.{s}] [J.WEqualsLocallyBijective AddCommGrpCat.{s}]
  [HasSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
  [HasSheafify J₂ AddCommGrpCat.{m₃}] [J₂.WEqualsLocallyBijective AddCommGrpCat.{m₃}] in
/-- **The factorization of the functor of Tag 0FTE on the homotopy categories.** -/
theorem pullbackTensor_comp_eq (E₂ : P₂.HomotopyExtension) :
    HomotopyCategory.pullbackTensor E₂ (tensorFunctorDataDiagonal.{t, a, m} A) ⋙
        HomotopyCategory.pullbackTensor
          (idPullbackDataHomotopyExtension.{t, a, m} (A := A)) D =
      HomotopyCategory.pullbackTensor E₂ D := by
  refine HomotopyCategory.eq_pullbackTensor E₂ D _ ?_
  rw [← Functor.assoc, HomotopyCategory.quotient_comp_pullbackTensor, Functor.assoc,
    HomotopyCategory.quotient_comp_pullbackTensor, ← Functor.assoc,
    pullbackTensorFunctor_comp_eq]

variable [(quasiIsomorphisms.{t, a, m} A).HasRightCalculusOfFractions]
  [(quasiIsomorphisms.{t, a₂, m₃} B₂).HasRightCalculusOfFractions]

/-- The functor `D(ℬ, d) ⥤ D(𝒜', d)` of Tag 0FTF is `ℳ ↦ Lf^*ℳ ⊗^𝐋_𝒜 𝒩`, for a pullback and a
tensor product given by their universal properties: derived pullback followed by the derived
tensor product. The composite of
the two derived extensions is the left derived functor of the composite of the two functors of
Tag 0FTE, which is the functor of Tag 0FTE for the given morphism of ringed sites; a left
derived functor is determined up to a unique isomorphism compatible with the counits, and
`derivedPullbackTensor` is one. -/
theorem exists_iso_derivedPullback_comp_derivedTensor (E₂ : P₂.HomotopyExtension)
    (hE₂diag : PullbackTensorExactnessData P₂ (tensorFunctorDataDiagonal.{t, a, m} A) g₂)
    (hEid : PullbackTensorExactnessData (idPullbackData.{t, a, m} (A := A)) D g)
    (hE₂ : PullbackTensorExactnessData P₂ D g₂)
    (hgood : ∀ Q : DifferentialGradedModule.{t, a₂, m₃} B₂, g₂.IsGood Q →
      g.IsGood ((pullbackTensorFunctor P₂ (tensorFunctorDataDiagonal.{t, a, m} A)).obj Q)) :
    ∃ ε : derivedPullback E₂ hE₂diag ⋙ derivedTensor hEid ≅ derivedPullbackTensor E₂ hE₂,
      Functor.whiskerLeft (toDerivedCategory B₂) ε.hom ≫ derivedPullbackTensorCounit E₂ hE₂ =
        derivedPullbackTensorCompCounit idPullbackDataHomotopyExtension hEid E₂ hE₂diag ≫
          Functor.whiskerRight (eqToIso (pullbackTensor_comp_eq (D := D) E₂)).hom
            (toDerivedCategory.{t, a, s} A') :=
  exists_iso_derivedPullbackTensorComp idPullbackDataHomotopyExtension hEid E₂ hE₂diag hgood
    (HomotopyCategory.pullbackTensor E₂ D) (eqToIso (pullbackTensor_comp_eq (D := D) E₂))
    (derivedPullbackTensor E₂ hE₂) (derivedPullbackTensorCounit E₂ hE₂)
    (fun _ hQ => isIso_derivedPullbackTensorCounit_app_of_isGood E₂ hE₂ hQ)

end Factorization

end DifferentialGradedModule

end SheafOfModules

end
