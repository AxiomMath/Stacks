module
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.SmallEtaleAssociatedSheafRestriction
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.Topology.Sheaves.Cohomology.Locality.CohomologyVanishesLocally
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.SmallEtaleGlobalCohomology
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.SmallEtaleGlobalCohomology

public import StacksFrontier.AlgebraicGeometry.Cohomology.UniformVanishing.SheafComparison
public import StacksFrontier.AlgebraicGeometry.Cohomology.UniformVanishing.SheafComparisonUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.SmallEtaleQuasiCoherentCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.SmallEtaleQuasiCoherentCohomologyUnconditional
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.CohomologyAtTheTerminalObject
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.CohomologyAtTheTerminalObjectUnconditional

/-!
# Naturality of the global small étale cohomology comparison

Let `X` be a scheme. For quasi-coherent `𝒪_X`-modules `F` and `G`, the isomorphism
`AlgebraicGeometry.hgroupIsoSmallEtaleGlobalCohomology` between `Hⁿ⁺¹(X, F)` and the global
cohomology `Hⁿ⁺¹(X_étale, Fᵃ)` of the associated sheaf on the small étale site is natural with
respect to a morphism `φ : F ⟶ G` together with a compatible morphism `ψ : Fᵃ ⟶ Gᵃ` of the
associated sheaves.

## Main results

* `AlgebraicGeometry.hgroupIsoSmallEtaleGlobalCohomology_hom_naturality`: the comparison
  isomorphism carries `Hⁿ⁺¹(X, φ)` to `Hⁿ⁺¹(X_étale, ψ)`.

## References

* [Stacks Project, Tag 03P2](https://stacks.math.columbia.edu/tag/03P2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

attribute [local instance 2000] CategoryTheory.IsGrothendieckAbelian.hasExt

variable (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent]
  [HasExt.{u} (Sheaf (Opens.grothendieckTopology (X : Type u)) AddCommGrpCat.{u})]

section Naturality

variable {X F} {G : X.Modules} [G.IsQuasicoherent]

/-- **`hgroupIsoSmallEtaleGlobalCohomology` is natural** for a morphism `φ : F ⟶ G` of
quasi-coherent modules together with a morphism `ψ : Fᵃ ⟶ Gᵃ` of the associated sheaves which
`AlgebraicGeometry.smallEtaleSectionsUnitIso` intertwines with `φ`: it carries `Hⁿ⁺¹(X, φ)` to
`Hⁿ⁺¹(X_étale, ψ)`. -/
theorem hgroupIsoSmallEtaleGlobalCohomology_hom_naturality (φ : F ⟶ G)
    (ψ : smallEtaleAssociatedSheaf X F ⟶ smallEtaleAssociatedSheaf X G)
    (h : (SheafOfModules.toSheaf X.ringCatSheaf).map φ ≫ (smallEtaleSectionsUnitIso X G).hom =
      (smallEtaleSectionsUnitIso X F).hom ≫ (smallEtaleZariskiPushforward X).map ψ) (n : ℕ) :
    (Hfunctor X.ringCatSheaf ⊤ (n + 1)).map φ ≫ (hgroupIsoSmallEtaleGlobalCohomology X G n).hom =
      (hgroupIsoSmallEtaleGlobalCohomology X F n).hom ≫
        AddCommGrpCat.ofHom (Sheaf.H.map ψ (n + 1)) := by
  simp only [hgroupIsoSmallEtaleGlobalCohomology, Iso.trans_hom, Category.assoc]
  rw [reassoc_of% (hgroupIsoSheafCohomology_hom_naturality φ ⊤ n),
    reassoc_of% (smallEtaleQuasiCoherentGlobalCohomologyIso_hom_naturality φ ψ h (n + 1)),
    Stacks.Cohomology.TerminalCohomology.h'IsoH_hom_naturality]

end Naturality

end AlgebraicGeometry

end
