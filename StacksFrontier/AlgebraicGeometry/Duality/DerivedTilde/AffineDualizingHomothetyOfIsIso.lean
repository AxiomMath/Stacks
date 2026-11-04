module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineDualizingHomothety
import StacksCore.Tactic.StacksAttribute

/-!
# The derived self internal hom from an invertible homothety

For a pseudo-coherent, bounded below complex `ω` of `R`-modules whose derived homothety
`R ⟶ R𝐻om_R(ω, ω)` is invertible, the derived internal hom `R𝓗om(ω̃, ω̃)` on `Spec R` is
isomorphic to the structure sheaf `𝒪_{Spec R}[0]`.

## Main results

* `derivedTildeDerivedSheafHomSelfUnitIsoOfIsIso`: if the derived homothety of `ω` is invertible,
  then `R𝓗om(ω̃, ω̃) ≅ 𝒪_{Spec R}[0]` as objects of the derived category.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open TopologicalSpace AlgebraicGeometry Stacks.SheafOfModules

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.AffineTilde.preservesFiniteColimits_tildeFunctor

universe u

namespace Stacks.Duality

variable (R : CommRingCat.{u}) [IsNoetherianRing R]
  [HasSheafify (Opens.grothendieckTopology (Spec R)) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology (Spec R)).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Tensor.sheafTensor.{u, u, u, u, u} (Spec R).sheaf).Additive]
  [∀ M, ((Tensor.sheafTensor.{u, u, u, u, u} (Spec R).sheaf).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} (Spec R).sheaf)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂
      (Tensor.sheafTensor (Spec R).sheaf) (ComplexShape.up ℤ)]

/-- **The derived internal hom of a complex on `Spec R` to itself is the structure sheaf, as soon
as its derived homothety over the ring is invertible.** If `ω` is pseudo-coherent and bounded
below and the derived homothety `R ⟶ R𝐻om_R(ω, ω)` is invertible, the comparison of
[Stacks, Tag 0A6H] (3)(a) at the pair `(ω, ω)` carries `R𝐻om_R(ω, ω) ≅ R[0]` to

`R𝓗om_{𝒪_{Spec R}}(ω̃, ω̃) ≅ 𝒪_{Spec R}[0]`.

This is an isomorphism of *objects*; it is not compatible with the evaluation morphisms. -/
def derivedTildeDerivedSheafHomSelfUnitIsoOfIsIso {ω : DerivedCategory (ModuleCat.{u} R)}
    (hpc : StacksDraft.PseudoCoherence.IsPseudoCoherent ω)
    (hplus : (DerivedCategory.TStructure.t).plus ω)
    (hh : IsIso (Dualizing.derivedHomothety
      (StacksDraft.DerivedHom.derivedHomAdjunction (R := (R : Type u))).toDerivedHomAdjunction
      (DerivedCategory.Q.obj (𝟙_ (StacksDraft.DerivedHom.Model.Complex (R : Type u))))
      (StacksDraft.DerivedHom.derivedHomAdjunction (R := (R : Type u))).tensorUnitLeft ω)) :
    letI := derivedMonoidalStructure (Spec R).sheaf
    ((derivedSheafHom (Spec R).sheaf).obj
          (op ((derivedTildeStructureSheafModules R).obj ω))).obj
        ((derivedTildeStructureSheafModules R).obj ω) ≅
      𝟙_ (DerivedCategory (StructureSheafModules (Spec R).sheaf)) := by
  letI := derivedMonoidalStructure (Spec R).sheaf
  exact affinePseudoCoherentDerivedSheafHomIso R ω ω hpc hplus ≪≫
      (derivedTildeStructureSheafModules R).mapIso (@asIso _ _ _ _ _ hh).symm ≪≫
      ((tilde.functor R).mapDerivedCategorySingleFunctor 0).app
        (ModuleCat.of (R : Type u) R) ≪≫
      (DerivedCategory.singleFunctor (StructureSheafModules (Spec R).sheaf) 0).mapIso tildeSelf

end Stacks.Duality

end
