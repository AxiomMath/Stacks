module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.CupProductAugmentation
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.CupProductComparisonBridge

/-!
# The two augmentations of [Stacks, Tag 07M9] are one map

Let `(X, 𝒪_X)` be a space with a sheaf of commutative rings, let `V` be an open subset, put
`A = 𝒪_X(V)` and let `𝒰 : V = ⋃ Ui` be an open covering. There are two augmentations
`Γ(V, 𝒦^•) ⟶ Tot(Č^•(𝒰, 𝒦^•))` of [Stacks, Tag 07M9] as morphisms of complexes of `A`-modules:

* `Stacks.Cech.LinearCupProduct.cechAugmentationTotal`, built for a terminal object of the base
  category;
* `Stacks.Cech.Linear.sectionsToTotalCech`, built from the degree-zero clause of
  [Stacks, Tag 01EP].

Their targets agree, but their sources are two presentations of `Γ(V, 𝒦^•)`: the first restricts
from the terminal object `V` of `Over V`, the second evaluates `SheafOfModules.evaluation` at `V`.
This file shows that the two augmentations agree up to the isomorphism
`Stacks.Cohomology.CechSheaf.sectionsTerminalFunctorIso` between these presentations.

## Main results

* `Stacks.Cech.LinearCupProduct.cechAugmentationTotal_eq_sectionsToTotalCech`: **the generic
  augmentation is the module-valued one, conjugated by the identification of the two
  presentations of `Γ(V, -)`.**

## References

* [Stacks Project, Tag 07M9](https://stacks.math.columbia.edu/tag/07M9)
* [Stacks Project, Tag 01EP](https://stacks.math.columbia.edu/tag/01EP)
* [Stacks Project, Tag 08BN](https://stacks.math.columbia.edu/tag/08BN)
* [Stacks Project, Tag 0FKV](https://stacks.math.columbia.edu/tag/0FKV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open Stacks.Cohomology.CechSheaf (cechAugmentation coverObject sectionsTerminalFunctor
  sectionsTerminalFunctorIso)
open Stacks.Cohomology.CechDerived (cechBicomplex)
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cech.ModuleCupProduct (CoeffRing sectionsComplexFunctor)

universe u

namespace Stacks.Cohomology.CechSheaf

variable {X : Type u} [TopologicalSpace X]
  (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (V : Opens X)

/-- **Sections at the terminal object of the slice over `V` preserve zero morphisms.** -/
instance preservesZeroMorphisms_sectionsTerminalFunctor :
    (sectionsTerminalFunctor.{u, u, u} (R := R) V).PreservesZeroMorphisms := by
  unfold sectionsTerminalFunctor
  infer_instance

end Stacks.Cohomology.CechSheaf

namespace Stacks.Cech.LinearCupProduct

attribute [local instance] ModuleCat.hasLimitsOfSize ModuleCat.hasColimitsOfSize

variable {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
  (V : Opens X) {ι : Type u} (Ui : ι → Opens X) (hU : V = ⨆ i, Ui i)

/-- Conjugation of a composite by an isomorphism of its source. -/
private theorem eq_hom_comp {C : Type*} [Category* C] {a b c d : C}
    (e : a ≅ b) (f : a ⟶ c) (g : c ⟶ d) (u : b ⟶ d) (hu : u = (e.inv ≫ f) ≫ g) :
    f ≫ g = e.hom ≫ u := by
  rw [hu, Category.assoc, Iso.hom_inv_id_assoc]

/-- **The augmentation of [Stacks, Tag 07M9] built generically for the terminal object of
`Over V` is the module-valued augmentation `Stacks.Cech.Linear.sectionsToTotalCech`**, conjugated
by the identification `Stacks.Cohomology.CechSheaf.sectionsTerminalFunctorIso` of the two
presentations of `Γ(V, -)`. -/
theorem cechAugmentationTotal_eq_sectionsToTotalCech
    (K : CochainComplex (SheafOfModules.{u} (ringSheaf O)) ℤ) :
    letI : (sectionsTerminalFunctor.{u, u, u} (R := ringSheaf O) V).PreservesZeroMorphisms :=
      Stacks.Cohomology.CechSheaf.preservesZeroMorphisms_sectionsTerminalFunctor
        (ringSheaf O) V
    letI : (SheafOfModules.evaluation.{u} (ringSheaf O) (op V)).Additive :=
      Stacks.Cohomology.CechDerived.additive_evaluation (ringSheaf O) V
    cechAugmentationTotal (coverObject Ui hU) (CoeffRing O V) Over.mkIdTerminal
        ((sectionsComplexFunctor O V).obj K) =
      ((NatIso.mapHomologicalComplex
          (sectionsTerminalFunctorIso.{u, u, u} (R := ringSheaf O) V) (up ℤ)).app K).hom ≫
        (Stacks.Cech.Linear.sectionsToTotalCech X (ringSheaf O) V Ui hU).app K := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  exact eq_hom_comp ((sectionsTerminalFunctorIso.{u, u, u} (R := ringSheaf O) V).app (K.X n))
    (cechAugmentation V Ui hU (K.X n))
    ((HomologicalComplex.extendXIso _ embeddingUpNat (i := 0) rfl).inv ≫
      (cechBicomplex (ringSheaf O) V Ui hU K).flip.ιTotal (up ℤ) 0 n n (by simp)) _ rfl

end Stacks.Cech.LinearCupProduct

end
