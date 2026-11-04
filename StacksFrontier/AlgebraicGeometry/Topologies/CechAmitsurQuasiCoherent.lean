module

public import StacksFrontier.AlgebraicGeometry.Topologies.CechVanishingStandardCovering

/-!
# The Čech complex of `Fᵃ` on a standard covering is the Amitsur complex

Let `S` be a scheme, `F` a quasi-coherent `𝒪_S`-module, `U` an object of `Over S` with affine
total space, and `f : W ⟶ U` a morphism of `Over S` with `W.left` affine.  Put
`R = Γ(U.left, 𝒪)`, `A = Γ(W.left, 𝒪)` and `M = Fᵃ(U)`.  Then there is an isomorphism of
complexes

  `Č^•({W → U}, Fᵃ) ≅ s((A/R)_• ⊗_R M)`.

The same holds for a standard `τ`-covering `{U_i → U}`, with `A = Γ((∐ U_i).left, 𝒪)`.

## Main definitions

* `AlgebraicGeometry.sliceCechCosimplicialObjectIsoAmitsurQuasiCoherent`: the isomorphism of
  cosimplicial `R`-modules, for the covering object presented as a relative spectrum.
* `AlgebraicGeometry.sliceCechComplexIsoAmitsurQuasiCoherent`: the isomorphism of complexes of
  `R`-modules, for the covering object presented as a relative spectrum.
* `AlgebraicGeometry.cechComplexIsoAmitsurQuasiCoherent`: the isomorphism of complexes of
  abelian groups for the one-member covering `{W → U}`.
* `AlgebraicGeometry.cechComplexIsoAmitsurStandardCovering`: the same for an arbitrary standard
  `τ`-covering.

## References

* [Stacks Project, Tag 03FJ](https://stacks.math.columbia.edu/tag/03FJ)
* [Stacks Project, Tag 03FI](https://stacks.math.columbia.edu/tag/03FI)
* [Stacks Project, Tag 023F](https://stacks.math.columbia.edu/tag/023F)
* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicTopology Stacks.CechSite Stacks.Descent
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {S : Scheme.{u}} (U : Over S) [IsAffine U.left]

/-! ### The isomorphism of complexes for a one-member covering by an affine object -/

/-- The Čech cosimplicial object of `Fᵃ` on the one-member covering of `U` by the relative
spectrum of `A = Γ(W.left, 𝒪)` is `(A/R)_• ⊗_R M`, where `R = Γ(U.left, 𝒪)` and `M = Fᵃ(U)`. -/
public def sliceCechCosimplicialObjectIsoAmitsurQuasiCoherent (F : S.Modules)
    [F.IsQuasicoherent] {W : Over S} (f : W ⟶ U) [IsAffine W.left] :
    letI := overAffineSliceAlgebra U f
    sliceCechCosimplicialObject
        (PreZeroHypercover.singleton.{u} ((overAffineAlgSpec U).obj
          (op (overAffineAlgObj U (Γ(W.left, ⊤) : Type u)))).hom)
        (Stacks.Sites.sliceAssociatedModuleCat F U) ≅
      (amitsurAugmentation (Γ(U.left, ⊤) : Type u) (Γ(W.left, ⊤) : Type u)
        (Stacks.Sites.coeffModule S F (𝟭 (Over S)) U)).right :=
  letI := overAffineSliceAlgebra U f
  sliceCechCosimplicialObjectIsoAmitsurOfAdjunction
    (Stacks.Sites.sliceAssociatedModuleCat F U) (overAffineAlgAdjunction U)
    (overAffineAlgObj U (Γ(W.left, ⊤) : Type u))
    (powerSectionsSliceAssociatedModuleIso S F U
      ((overAffineAlgSpec U).obj (op (overAffineAlgObj U (Γ(W.left, ⊤) : Type u))))
      (isAffine_cechNerveTerminalFrom_overAffineAlgSpec U
        (overAffineAlgObj U (Γ(W.left, ⊤) : Type u))))
    (sectionsTerminalArrowIsoAlgebraMapArrow U (Γ(W.left, ⊤) : Type u))

/-- The isomorphism `Č^•({Spec A → U}, Fᵃ) ≅ s((A/R)_• ⊗_R M)` of complexes of
`R = Γ(U.left, 𝒪)`-modules, where `A = Γ(W.left, 𝒪)` and `M = Fᵃ(U)`. -/
public def sliceCechComplexIsoAmitsurQuasiCoherent (F : S.Modules) [F.IsQuasicoherent]
    {W : Over S} (f : W ⟶ U) [IsAffine W.left] :
    letI := overAffineSliceAlgebra U f
    sliceCechComplex
        (PreZeroHypercover.singleton.{u} ((overAffineAlgSpec U).obj
          (op (overAffineAlgObj U (Γ(W.left, ⊤) : Type u)))).hom)
        (Stacks.Sites.sliceAssociatedModuleCat F U) ≅
      amitsurCochainComplex (Γ(U.left, ⊤) : Type u) (Γ(W.left, ⊤) : Type u)
        (Stacks.Sites.coeffModule S F (𝟭 (Over S)) U) :=
  letI := overAffineSliceAlgebra U f
  sliceCechComplexIsoAmitsurOfAdjunction (Stacks.Sites.sliceAssociatedModuleCat F U)
    (overAffineAlgAdjunction U) (overAffineAlgObj U (Γ(W.left, ⊤) : Type u))
    (powerSectionsSliceAssociatedModuleIso S F U
      ((overAffineAlgSpec U).obj (op (overAffineAlgObj U (Γ(W.left, ⊤) : Type u))))
      (isAffine_cechNerveTerminalFrom_overAffineAlgSpec U
        (overAffineAlgObj U (Γ(W.left, ⊤) : Type u))))
    (sectionsTerminalArrowIsoAlgebraMapArrow U (Γ(W.left, ⊤) : Type u))

/-- For `U` an object of `Over S` with affine total space and `f : W ⟶ U` with `W.left` affine,
the Čech complex of the presheaf `Fᵃ` on the one-member covering `{W → U}` is the complex
`s((A/R)_• ⊗_R M)`, where `R = Γ(U.left, 𝒪)`, `A = Γ(W.left, 𝒪)` and `M = Fᵃ(U)`, with its
`R`-module structure forgotten. -/
@[stacks 03FJ "the isomorphism of complexes, for the one-member covering 03FI reduces to"]
public def cechComplexIsoAmitsurQuasiCoherent (F : S.Modules) [F.IsQuasicoherent]
    {W : Over S} (f : W ⟶ U) [IsAffine W.left] :
    letI := overAffineSliceAlgebra U f
    cechComplex (PreZeroHypercover.singleton.{u} f) (quasiCoherentPresheafFunctor S F) ≅
      ((forget₂ (ModuleCat.{u} (Γ(U.left, ⊤) : Type u)) AddCommGrpCat.{u}).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj
        (amitsurCochainComplex (Γ(U.left, ⊤) : Type u) (Γ(W.left, ⊤) : Type u)
          (Stacks.Sites.coeffModule S F (𝟭 (Over S)) U)) :=
  letI := overAffineSliceAlgebra U f
  haveI := isIso_cechComplexMap_singleton.{u} f
    ((overAffineAlgSpec U).obj (op (overAffineAlgObj U (Γ(W.left, ⊤) : Type u)))).hom
    (mkIsoMkSpecOverAffineAlgObj U f) (quasiCoherentPresheafFunctor S F)
  (asIso (cechComplexMap (PreZeroHypercover.singleton.{u} f)
      (PreZeroHypercover.singleton.{u} ((overAffineAlgSpec U).obj
        (op (overAffineAlgObj U (Γ(W.left, ⊤) : Type u)))).hom)
      (singletonHomOver.{u} f _ (mkIsoMkSpecOverAffineAlgObj U f))
      (quasiCoherentPresheafFunctor S F))).symm ≪≫
    (sliceCechComplexCompCoefficientsIso
        (PreZeroHypercover.singleton.{u} ((overAffineAlgSpec U).obj
          (op (overAffineAlgObj U (Γ(W.left, ⊤) : Type u)))).hom)
        (forget₂ (ModuleCat.{u} (Γ(U.left, ⊤) : Type u)) AddCommGrpCat.{u})
        (Stacks.Sites.sliceAssociatedModuleCat F U)).symm ≪≫
      ((forget₂ (ModuleCat.{u} (Γ(U.left, ⊤) : Type u))
          AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℕ)).mapIso
        (sliceCechComplexIsoAmitsurQuasiCoherent U F f)

/-! ### An arbitrary standard covering -/

/-- For a standard `τ`-covering `𝒰 = {U_i → U}` of an object of `Over S` with affine total
space, the Čech complex of `Fᵃ` is `s((A/R)_• ⊗_R M)`, where `R = Γ(U.left, 𝒪)`,
`A = Γ((∐ U_i).left, 𝒪)` and `M = Fᵃ(U)`. -/
@[stacks 03FJ "the isomorphism of complexes, for an arbitrary standard covering"]
public def cechComplexIsoAmitsurStandardCovering (τ : CoveringTopology) (F : S.Modules)
    [F.IsQuasicoherent] (𝒱 : PreZeroHypercover.{u} U)
    (h : IsStandardCovering τ (fun i ↦ (𝒱.X i).left) (fun i ↦ (𝒱.f i).left)) :
    letI : Finite 𝒱.I₀ := h.finite_index
    letI : IsAffine (∐ 𝒱.X).left := h.isAffine_left_sigmaObj τ S 𝒱
    letI := overAffineSliceAlgebra U (Sigma.desc 𝒱.f)
    cechComplex 𝒱 (quasiCoherentPresheafFunctor S F) ≅
      ((forget₂ (ModuleCat.{u} (Γ(U.left, ⊤) : Type u))
            AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (amitsurCochainComplex (Γ(U.left, ⊤) : Type u) (Γ((∐ 𝒱.X).left, ⊤) : Type u)
          (Stacks.Sites.coeffModule S F (𝟭 (Over S)) U)) :=
  letI : Finite 𝒱.I₀ := h.finite_index
  letI : IsAffine (∐ 𝒱.X).left := h.isAffine_left_sigmaObj τ S 𝒱
  letI := overAffineSliceAlgebra U (Sigma.desc 𝒱.f)
  haveI : PreservesFiniteProducts (quasiCoherentPresheafFunctor S F) :=
    (Presheaf.isSheaf_iff_preservesFiniteProducts _).mp
      (Presheaf.IsSheaf.of_le
        ((extensiveTopology_over_le_zariskiTopology_over S).trans
          (fun _ _ hR ↦ by
            rw [GrothendieckTopology.mem_over_iff] at hR ⊢
            exact Scheme.zariskiTopology_le_grothendieckTopology τ _ hR))
        (isSheaf_over_quasiCoherentPresheafFunctor τ S F))
  haveI := isIso_cechComplexMap_of_preservesFiniteProducts 𝒱
    (quasiCoherentPresheafFunctor S F)
  (asIso (cechComplexMap 𝒱 (PreZeroHypercover.singleton.{u} (Sigma.desc 𝒱.f))
      (coproductRefinement 𝒱) (quasiCoherentPresheafFunctor S F))).symm ≪≫
    cechComplexIsoAmitsurQuasiCoherent U F (Sigma.desc 𝒱.f)

end AlgebraicGeometry

end
