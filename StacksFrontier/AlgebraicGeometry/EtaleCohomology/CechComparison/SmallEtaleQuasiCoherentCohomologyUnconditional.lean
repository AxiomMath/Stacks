module
public import StacksFrontier.Topology.Sheaves.Modules.TensorExactness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Comparison.ZariskiRestriction
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.BigSiteSheafCohomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.FreeYonedaSectionsUnivLE
public import StacksFrontier.Topology.Sheaves.Cohomology.CompactSubset.RestrictionUnivLE
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.SmallEtaleQuasiCoherentCohomology
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.SmallEtaleQuasiCoherentCohomology

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.SmallEtaleAssociatedSheafRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.SmallEtaleHigherDirectImageVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleZariskiCohomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.PushforwardCohomologyCollapse
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.PushforwardCohomologyCollapseUnconditional

/-!
# Naturality of the comparison of Zariski and small étale cohomology

Let `S` be a scheme. For quasi-coherent `𝒪_S`-modules `F` and `F'`, the isomorphism
`AlgebraicGeometry.smallEtaleQuasiCoherentGlobalCohomologyIso` between `H^p(S, F)` and
`H^p(S_étale, Fᵃ)`, which is [Stacks, Tag 03P2] for `𝒞 = S_étale`, is natural with respect to a
morphism `φ : F ⟶ F'` together with a compatible morphism `ψ : Fᵃ ⟶ F'ᵃ` of the associated sheaves.

## Main results

* `AlgebraicGeometry.smallEtaleQuasiCoherentGlobalCohomologyIso_hom_naturality`: the comparison
  isomorphism carries the map induced by `φ` on `H^p(S, -)` to the map induced by `ψ` on
  `H^p(S_étale, -)`.

## References

* [Stacks Project, Tag 03P2](https://stacks.math.columbia.edu/tag/03P2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable (S : Scheme.{u}) (F : S.Modules) [F.IsQuasicoherent]

-- The Zariski side of the collapse asks for an `Ext` universe and enough injectives in the
-- coefficients themselves; both are available at any coefficient universe dominating the space,
-- but only as theorems.  Preservation of injectives by `ε_*` is likewise a theorem.
attribute [local instance] Stacks.Topology.hasExt_sheafOpens
  Stacks.Topology.enoughInjectives_sheafOpens
  Stacks.Cohomology.BiggerSite.preservesInjectiveObjects_sheafPushforwardContinuous

-- `CategoryTheory.Sheaf.H'` carries its `Ext` universe as a parameter, and on the small étale
-- site instance search resolves it to `u + 1` rather than to the morphism universe `u`, because
-- `AlgebraicGeometry.hasExt_sheaf_smallEtaleTopology` is declared after
-- `CategoryTheory.IsGrothendieckAbelian.hasExt` and so wins.  The collapse resolves its own
-- `CategoryTheory.HasExt` binder by instance search *before* unifying with the expected type, so
-- pinning the universe in the statement does not help; the priority has to be flipped.
section Naturality

variable {S F} {F' : S.Modules} [F'.IsQuasicoherent]

attribute [local instance 2000] CategoryTheory.IsGrothendieckAbelian.hasExt in
/-- **`smallEtaleQuasiCoherentGlobalCohomologyIso` is natural** for a morphism `φ : F ⟶ F'` of
quasi-coherent modules together with a morphism `ψ : Fᵃ ⟶ F'ᵃ` of the associated sheaves which
`AlgebraicGeometry.smallEtaleSectionsUnitIso` intertwines with `φ`. -/
public theorem smallEtaleQuasiCoherentGlobalCohomologyIso_hom_naturality (φ : F ⟶ F')
    (ψ : smallEtaleAssociatedSheaf S F ⟶ smallEtaleAssociatedSheaf S F')
    (h : (SheafOfModules.toSheaf S.ringCatSheaf).map φ ≫ (smallEtaleSectionsUnitIso S F').hom =
      (smallEtaleSectionsUnitIso S F).hom ≫ (smallEtaleZariskiPushforward S).map ψ) (p : ℕ) :
    ((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology S) p).map
        ((SheafOfModules.toSheaf S.ringCatSheaf).map φ)).app (op ⊤) ≫
        (smallEtaleQuasiCoherentGlobalCohomologyIso S F' p).hom =
      (smallEtaleQuasiCoherentGlobalCohomologyIso S F p).hom ≫
        ((Sheaf.cohomologyPresheafFunctor (Scheme.smallEtaleTopology S) p).map ψ).app
          (op ((opensToEtale S).obj ⊤)) := by
  simp only [smallEtaleQuasiCoherentGlobalCohomologyIso, smallEtaleQuasiCoherentCohomologyIso,
    Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
  rw [← NatTrans.comp_app_assoc, ← Functor.map_comp, h, Functor.map_comp, NatTrans.comp_app_assoc,
    Stacks.Cohomology.BiggerSite.sheafCohomologyPushforwardIso_hom_naturality
      (hF := fun q hq _ ↦ isZero_rightDerived_pushforward_opensToEtale S F q hq),
    Category.assoc]

end Naturality

end AlgebraicGeometry

end
