module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineBidualitySlice
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineDualizingSlice
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.SliceDerivedBiduality

/-!
# The tensor–hom bijection for derived sheaf hom

For a ringed space, the bijection `derivedSheafHomTensorEquiv` between morphisms
`Z ⟶ RHom(K, M)` and morphisms `Z ⊗ᴸ K ⟶ M` in the derived category is given by tensoring
with `K` and composing with the evaluation map `derivedSheafHomCounit`.

## Main results

* `derivedSheafHomTensorEquiv_apply`: `derivedSheafHomTensorEquiv` sends `a` to the tensor
  product of `a` with `K` followed by the evaluation morphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open TopologicalSpace AlgebraicGeometry Stacks.SheafOfModules

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.AffineTilde.preservesFiniteColimits_tildeFunctor

namespace Stacks.SheafOfModules

section RingedSpace

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Tensor.sheafTensor.{u, u, u} Rc).Additive]
  [∀ M, ((Tensor.sheafTensor.{u, u, u} Rc).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor Rc) (ComplexShape.up ℤ)]

/-- The bijection of [Stacks, Tag 08DI] is tensoring with the identity and evaluating. -/
theorem derivedSheafHomTensorEquiv_apply (Z K M : DerivedCategory (StructureSheafModules Rc))
    (a : Z ⟶ ((derivedSheafHom Rc).obj (op K)).obj M) :
    derivedSheafHomTensorEquiv Rc Z K M a =
      ((derivedTensor Rc).map a).app K ≫ derivedSheafHomCounit Rc K M := by
  have hnat : ∀ (b : Z ⟶ ((derivedSheafHom Rc).obj (op K)).obj M)
      (g : ((derivedSheafHom Rc).obj (op K)).obj M ⟶ ((derivedSheafHom Rc).obj (op K)).obj M),
      RingedSite.derivedCurryHomEquiv (ringedSite Rc) Z K M (b ≫ g) =
        ((derivedTensor Rc).map b).app K ≫ RingedSite.derivedCurryHomEquiv (ringedSite Rc)
          (((derivedSheafHom Rc).obj (op K)).obj M) K M g :=
    fun b g => RingedSite.derivedCurryHomEquiv_naturality_source (ringedSite Rc) b g
  have hcounit : derivedSheafHomCounit Rc K M =
      RingedSite.derivedCurryHomEquiv (ringedSite Rc)
        (((derivedSheafHom Rc).obj (op K)).obj M) K M
        (𝟙 (((derivedSheafHom Rc).obj (op K)).obj M)) := rfl
  rw [hcounit]
  have h0 := hnat a (𝟙 (((derivedSheafHom Rc).obj (op K)).obj M))
  symm
  exact h0.symm.trans
    (congrArg (fun v : Z ⟶ ((derivedSheafHom Rc).obj (op K)).obj M =>
      RingedSite.derivedCurryHomEquiv (ringedSite Rc) Z K M v) (Category.comp_id a))

end RingedSpace

end Stacks.SheafOfModules

namespace Stacks.Duality

open Stacks.Cohomology.SliceDerivedSheafHom (restrictD)

end Stacks.Duality
