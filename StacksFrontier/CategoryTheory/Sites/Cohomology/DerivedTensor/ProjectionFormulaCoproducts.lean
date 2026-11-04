module

public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ProjectionFormulaUnitInvertible
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.CanonicalBifunctorComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BraidingNatIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorHomAdjunction

/-!
# The projection formula on ringed topoi and direct sums

Let `f : (Sh(C), 𝒪_C) ⟶ (Sh(D), 𝒪_D)` be a morphism of ringed topoi presented by a morphism of
sites and `E ∈ D(𝒪_C)`. This file proves that the projection-formula map of
[Stacks, Tag 0B56], `Rf_*E ⊗^L K ⟶ Rf_*(E ⊗^L Lf^*K)`, is invertible at a direct sum `⊕ K_j` as
soon as it is invertible at every `K_j` and `Rf_*` commutes with the direct sum of the
`E ⊗^L Lf^*K_j`. This is the step of the proof of [Stacks, Tag 08IN] that passes from `K = 𝒪[n]`
to all of `D(𝒪_D)` through [Stacks, Tag 09PB].

## Main results

* `Stacks.Cohomology.ProjectionFormulaCoproducts.isIso_app_sigma_of_isIso_sigmaComparison`: a
  natural transformation between functors commuting with a direct sum is invertible at the sum
  when it is invertible at every summand.
* `Stacks.Cohomology.ProjectionFormulaCoproducts.preservesColimitsOfSize_tensor_flip_obj`,
  `preservesColimitsOfSize_tensor_obj`: the derived tensor product of a ringed site commutes with
  colimits in each variable, being a left adjoint ([Stacks, Tag 08J8]).
* `Stacks.Cohomology.ProjectionFormulaCoproducts.isIso_projectionFormulaMap_sigma`: the
  projection formula at a direct sum.

## References

* [Stacks Project, Tag 0B56](https://stacks.math.columbia.edu/tag/0B56)
* [Stacks Project, Tag 08IN](https://stacks.math.columbia.edu/tag/08IN)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.DerivedTensor.RingedSite

namespace Stacks.Cohomology.ProjectionFormulaCoproducts

universe u

attribute [local instance] HasDerivedCategory.standard

/-- **A natural transformation is invertible at a direct sum** when it is invertible at every
summand and both functors commute with the sum. -/
theorem isIso_app_sigma_of_isIso_sigmaComparison {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟]
    {F G : 𝒞 ⥤ 𝒟} (α : F ⟶ G) {J : Type*} (K : J → 𝒞) [HasCoproduct K]
    [HasCoproduct fun j => F.obj (K j)] [HasCoproduct fun j => G.obj (K j)]
    [IsIso (sigmaComparison F K)] [IsIso (sigmaComparison G K)] (h : ∀ j, IsIso (α.app (K j))) :
    IsIso (α.app (∐ K)) := by
  let e : (∐ fun j => F.obj (K j)) ≅ ∐ fun j => G.obj (K j) :=
    { hom := Limits.Sigma.desc fun j => α.app (K j) ≫ Limits.Sigma.ι (fun j => G.obj (K j)) j
      inv := Limits.Sigma.desc fun j => inv (α.app (K j)) ≫
        Limits.Sigma.ι (fun j => F.obj (K j)) j
      hom_inv_id := Limits.Sigma.hom_ext _ _ fun j => by simp
      inv_hom_id := Limits.Sigma.hom_ext _ _ fun j => by simp }
  have hsq : sigmaComparison F K ≫ α.app (∐ K) = e.hom ≫ sigmaComparison G K := by
    refine Limits.Sigma.hom_ext _ _ fun j => ?_
    rw [ι_comp_sigmaComparison_assoc, α.naturality]
    simp [e]
  have : IsIso (sigmaComparison F K ≫ α.app (∐ K)) := by
    rw [hsq]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ e.isIso_hom inferInstance
  exact IsIso.of_isIso_comp_left (sigmaComparison F K) (α.app (∐ K))

section Site

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K L : CochainComplex (Modules X.O) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- `- ⊗^L B` commutes with colimits: it is left adjoint to `RSheafHom(B, -)`. -/
theorem preservesColimitsOfSize_tensor_flip_obj (B : DerivedModules X.O) :
    PreservesColimitsOfSize.{u, u} ((derivedTensorProductFunctor X.O).flip.obj B) := by
  have : PreservesColimitsOfSize.{u, u} (RingedSite.derivedTensorRight X B) :=
    (RingedSite.derivedTensorHomAdjunction X B).leftAdjoint_preservesColimits
  exact preservesColimits_of_natIso
    (show RingedSite.derivedTensorRight X B ≅ (derivedTensorProductFunctor X.O).flip.obj B from
    NatIso.ofComponents (fun A => ((RingedSite.derivedTensorFunctorIso X).app A).app B)
      (fun g =>
        NatTrans.congr_app ((RingedSite.derivedTensorFunctorIso X).hom.naturality g) B))

/-- `A ⊗^L -` commutes with colimits, by the commutativity constraint. -/
theorem preservesColimitsOfSize_tensor_obj (A : DerivedModules X.O) :
    PreservesColimitsOfSize.{u, u} ((derivedTensorProductFunctor X.O).obj A) := by
  have := preservesColimitsOfSize_tensor_flip_obj X A
  exact preservesColimits_of_natIso
    (DerivedTensorProduct.tensorFlipSlotIso X (canonicalDerivedTensorProduct X.O) A).symm

end Site

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)]
  (f : RingedToposSiteHom X Y)
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ))]
  (hmos : f.u.IsMorphismOfSites Y.J X.J)

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)] in
include hmos in
/-- The target `K ↦ Rf_*(E ⊗^L Lf^*K)` of the projection formula commutes with a direct sum
`⊕ K_j` as soon as `Rf_*` commutes with the direct sum of the `E ⊗^L Lf^*K_j`. -/
theorem preservesColimit_projectionFormulaTarget
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {J : Type u} (K : J → DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    [PreservesColimit (Discrete.functor fun j =>
        ((derivedTensorProductFunctor X.O).obj E).obj ((derivedPullback f).obj (K j)))
      (derivedPushforward f)] :
    PreservesColimit (Discrete.functor K)
      (derivedPullback f ⋙ (derivedTensorProductFunctor X.O).obj E ⋙ derivedPushforward f) := by
  have : PreservesColimitsOfSize.{u, u} (derivedPullback f) :=
    (DerivedPullbackOnRingedTopoi.derivedAdjunction f hmos).leftAdjoint_preservesColimits
  have := preservesColimitsOfSize_tensor_obj ⟨X.C, X.J, X.O⟩ E
  have h3 : PreservesColimit ((Discrete.functor K ⋙ derivedPullback f) ⋙
      (derivedTensorProductFunctor X.O).obj E) (derivedPushforward f) :=
    preservesColimit_of_iso_diagram (derivedPushforward f)
      (K₁ := Discrete.functor fun j =>
        ((derivedTensorProductFunctor X.O).obj E).obj ((derivedPullback f).obj (K j)))
      (Discrete.natIso fun j => Iso.refl
        (((derivedTensorProductFunctor X.O).obj E).obj ((derivedPullback f).obj (K j.as))))
  infer_instance

/-- **The projection formula at a direct sum.** If the map
`Rf_*E ⊗^L K_j ⟶ Rf_*(E ⊗^L Lf^*K_j)` of [Stacks, Tag 0B56] is invertible for every `j` and `Rf_*`
commutes with the direct sum of the `E ⊗^L Lf^*K_j`, it is invertible at `⊕ K_j`. -/
theorem isIso_projectionFormulaMap_sigma
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {J : Type u} (K : J → DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) [HasCoproduct K]
    [HasCoproduct fun j =>
      ((derivedTensorProductFunctor Y.O).obj ((derivedPushforward f).obj E)).obj (K j)]
    [HasCoproduct fun j => (derivedPushforward f).obj
      (((derivedTensorProductFunctor X.O).obj E).obj ((derivedPullback f).obj (K j)))]
    [PreservesColimit (Discrete.functor fun j =>
        ((derivedTensorProductFunctor X.O).obj E).obj ((derivedPullback f).obj (K j)))
      (derivedPushforward f)]
    (h : ∀ j, IsIso (ProjectionFormulaOnRingedTopoi.projectionFormulaMap f hmos E (K j))) :
    IsIso (ProjectionFormulaOnRingedTopoi.projectionFormulaMap f hmos E (∐ K)) := by
  have := preservesColimitsOfSize_tensor_obj ⟨Y.C, Y.J, Y.O⟩ ((derivedPushforward f).obj E)
  have := preservesColimit_projectionFormulaTarget f hmos E K
  let α : (derivedTensorProductFunctor Y.O).obj ((derivedPushforward f).obj E) ⟶
      derivedPullback f ⋙ (derivedTensorProductFunctor X.O).obj E ⋙ derivedPushforward f :=
    { app := ProjectionFormulaOnRingedTopoi.projectionFormulaMap f hmos E
      naturality := fun _ _ k =>
        ProjectionFormulaOnRingedTopoi.projectionFormulaMap_naturality_target f hmos E k }
  have : HasCoproduct fun j => (derivedPullback f ⋙ (derivedTensorProductFunctor X.O).obj E ⋙
      derivedPushforward f).obj (K j) :=
    inferInstanceAs (HasCoproduct fun j => (derivedPushforward f).obj
      (((derivedTensorProductFunctor X.O).obj E).obj ((derivedPullback f).obj (K j))))
  exact isIso_app_sigma_of_isIso_sigmaComparison α K h

end Stacks.Cohomology.ProjectionFormulaCoproducts

end
