module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineDualizingSlice
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinSchemes.DerivedTildeInvertible
public import StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.DerivedSheafHomSliceModel

/-!
# Invertibility in `D(𝒪_X)` is local on the scheme

An object of `D(𝒪_X)` is invertible, for the monoidal structure of [Stacks, Tag 0FPT], as soon as
its restriction along the inclusion of each member of an open cover of `X` is invertible in the
derived category of the open subscheme.

## Main results

* `Stacks.Duality.isInvertible_of_isInvertible_restrictFunctor`: invertibility glues along an
  open cover, restrictions being read on the open subschemes.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Duality

variable {X : Scheme.{u}}

section Standard

attribute [local instance 10000] HasDerivedCategory.standard

/-- **Invertibility in `D(𝒪_X)` is local on `X`**, at the standard model of the derived
categories: an object whose restriction to each member of an open cover is invertible is
invertible. The restrictions are carried to the slice sites by `overEquiv`, where the glueing of
`Stacks.Cohomology.SliceDerivedSheafHom.isInvertible_of_isInvertible_restriction` applies. -/
theorem isInvertible_of_isInvertible_restrictFunctor_standard {ι : Type*} (U : ι → X.Opens)
    (hU : iSup U = ⊤) (K : DerivedCategory X.Modules)
    (hK : ∀ i, letI := Scheme.Modules.derivedMonoidal (U i).toScheme
      MonoidalCategory.IsInvertible
        ((Scheme.Modules.restrictFunctor (U i).ι).mapDerivedCategory.obj K)) :
    letI := Scheme.Modules.derivedMonoidal X
    MonoidalCategory.IsInvertible K := by
  have hY : (Stacks.SheafOfModules.ringedSite X.sheaf).J.CoversTop U :=
    (Opens.coversTop_iff _ _).2 (TopologicalSpace.IsOpenCover.mk hU)
  have h := Stacks.Cohomology.SliceDerivedSheafHom.isInvertible_of_isInvertible_restriction
    (Stacks.SheafOfModules.ringedSite X.sheaf) hY K fun i =>
      Stacks.SheafOfModules.OverEquivTensor.isInvertible_derivedTensorMonoidal_of_iso X (U i)
        _ (hK i) ((Stacks.SheafOfModules.derivedOverFunctorEquiv (U i)).app K)
  exact @MonoidalCategory.isInvertible_of_tensorComparison_of_braided _ _
      (RingedSite.derivedTensorMonoidal (Stacks.SheafOfModules.ringedSite X.sheaf)) _ _
      (Scheme.Modules.derivedMonoidal X) (Scheme.Modules.derivedSymmetric X).toBraidedCategory
      (𝟭 _)
      (fun A B => (((Stacks.SheafOfModules.DerivedMonoidal.derivedTensorMonoidalIso X.sheaf
        (Stacks.SheafOfModules.DerivedTensorProduct.toRingedSiteDerivedTensorProduct.{u, u + 1}
          (Stacks.SheafOfModules.canonicalDerivedTensorProduct
            (Stacks.SheafOfModules.ringedSite X.sheaf)))).app A).app B).symm)
      (Stacks.SheafOfModules.DerivedMonoidal.canonicalUnitIso X.sheaf).symm K h

end Standard

/-- **Invertibility in `D(𝒪_X)` is local on `X`.** Let `U` be a family of opens covering `X`.
If the restriction of `K ∈ D(𝒪_X)` to each open subscheme `U i` is an invertible object of
`D(𝒪_{U i})`, then `K` is an invertible object of `D(𝒪_X)`, for the monoidal structure of
[Stacks, Tag 0FPT] on both sides. -/
theorem isInvertible_of_isInvertible_restrictFunctor {ι : Type*} (U : ι → X.Opens)
    (hU : iSup U = ⊤) (K : DerivedCategory X.Modules)
    (hK : ∀ i, letI := Scheme.Modules.derivedMonoidal (U i).toScheme
      MonoidalCategory.IsInvertible
        ((Scheme.Modules.restrictFunctor (U i).ι).mapDerivedCategory.obj K)) :
    letI := Scheme.Modules.derivedMonoidal X
    MonoidalCategory.IsInvertible K := by
  refine (Scheme.Modules.isInvertible_standard_iff X K).1
    (isInvertible_of_isInvertible_restrictFunctor_standard U hU K fun i => ?_)
  let W := U i
  let Φ := StacksDraft.DerivedModel.schemeModulesComparison W.toScheme
  let Mstd := @Functor.mapDerivedCategory _ _ _ (HasDerivedCategory.standard _) _ _ _
    (HasDerivedCategory.standard _) (Scheme.Modules.restrictFunctor W.ι) _ _ _ |>.obj K
  let c : Φ.functor.obj Mstd ≅ Φ.functor.obj
      ((Scheme.Modules.restrictFunctor W.ι).mapDerivedCategory.obj K) :=
    (Stacks.Injectives.mapDerivedCategoryTargetModelIso W.toScheme.Modules
        (hd₁ := HasDerivedCategory.standard _) (Scheme.Modules.restrictFunctor W.ι)).app K ≪≫
      Stacks.Injectives.mapDerivedCategoryObjIso X.Modules
        (Scheme.Modules.restrictFunctor W.ι) K
  exact @MonoidalCategory.isInvertible_of_iso _ _
    (@Scheme.Modules.derivedMonoidal W.toScheme (HasDerivedCategory.standard _)) _ _
    (Φ.functor.preimageIso c).symm
    ((Scheme.Modules.isInvertible_standard_iff W.toScheme _).2 (hK i))

end Stacks.Duality

end
