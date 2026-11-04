module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.QuasicoherentCartesian
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.QuasicoherentCartesianInl
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.QuasicoherentCartesianInr
public import StacksFrontier.AlgebraicGeometry.Topologies.CartesianOfGlobalPresentation
public import StacksFrontier.AlgebraicGeometry.Topologies.GlobalPresentationIsIso
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentRestrictionOfUniv
public import StacksFrontier.CategoryTheory.Sites.Localization.SlicePostContinuous
public import StacksFrontier.AlgebraicGeometry.Simplicial.QuasicoherentCartesian.Equivalence

/-!
# Quasi-coherent modules on the total site of a simplicial site are the cartesian ones

Let `S` be a simplicial-site situation (Stacks 09WE) and `O` a sheaf of rings on its total
site. Stacks 0D7M says that a sheaf of `O`-modules `F` is quasi-coherent in the sense of
Modules on Sites, Definition 03DL, if and only if `F` is cartesian and every component module
`F_n` is a quasi-coherent `O_n`-module.

## Main results

* `isQuasicoherentOnSite_componentModule_quasicoherentCartesianEquivalence`: the components of a
  quasi-coherent module on the total site are quasi-coherent (in `SimplicialSiteSituation`).
* `isQuasicoherentOnSite_iff_isCartesianModule_quasicoherentCartesianEquivalence`: Stacks 0D7M in
  case (A) (in `SimplicialSite`).
* `isQuasicoherentOnSite_iff_isCartesianModule_and_isQuasicoherentOnSite_componentModule`:
  Stacks 0D7M (in `SimplicialSiteSituation`).

## Implementation notes

The quasi-coherence of the components holds in both cases: the component inclusion is
continuous and cocontinuous (Stacks 09WG), so restriction along it carries quasi-coherence
(Stacks 03DM). The cartesian half of the forward implication and the converse are proved, in
cases (A) and (B), in `QuasicoherentCartesianInl.lean` and `QuasicoherentCartesianInr.lean`
by localizing the transitions at slices.

## References

* [Stacks Project, Tag 0D7M](https://stacks.math.columbia.edu/tag/0D7M)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 07TF](https://stacks.math.columbia.edu/tag/07TF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace CategoryTheory.SimplicialSiteSituation

universe u

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})

section Modules

attribute [local instance] hasWeakSheafifyTotalQuasicoherentCartesian
  wEqualsLocallyBijectiveTotalQuasicoherentCartesian hasWeakSheafifyComponent

/-- **The components of a quasi-coherent module are quasi-coherent**, the first half of the
forward implication of Stacks 0D7M. The component inclusion `C_n ⥤ C_{total}` is continuous and
cocontinuous (Stacks 09WG) and the component structure sheaf is the literal restriction of `O`,
so restriction of modules along it carries quasi-coherence (Stacks 03DM). -/
theorem isQuasicoherentOnSite_componentModule_quasicoherentCartesianEquivalence
    (F : SheafOfModules.{u} (S.totalRingSheaf O))
    (hF : F.IsQuasicoherentOnSite) (n : SimplexCategory) :
    (S.componentModule O F n).IsQuasicoherentOnSite := by
  have : ∀ X : S.component n, (Over.post (X := X) (componentFunctor S n)).IsContinuous
      ((S.componentTopology n).over X) (S.totalTopology.over ((componentFunctor S n).obj X)) :=
    fun X => Functor.isContinuous_overPost _ _ _ X
  exact Stacks.SheafOfModules.SiteTransport.isQuasicoherentOnSite_pushforward_ofUniv.{u, u, u, u,
    u, u} (J := S.totalTopology) (K := S.componentTopology n) (R := S.totalRingSheaf O)
    (S := componentRingSheaf S (S.totalRingSheaf O) n) (componentFunctor S n) (𝟙 _)
    inferInstance F hF

end Modules

end CategoryTheory.SimplicialSiteSituation

namespace CategoryTheory.SimplicialSite

universe u

/-- **Stacks 0D7M in case (A).** For a simplicial site whose transitions are morphisms of sites
represented by continuous functors and a sheaf of commutative rings `O` on its total site, a
sheaf of `O`-modules `F` is quasi-coherent in the sense of Stacks 03DL if and only if `F` is
cartesian in the sense of Stacks 07TF (2) and every component `F_n` is a quasi-coherent
`O_n`-module. -/
theorem isQuasicoherentOnSite_iff_isCartesianModule_quasicoherentCartesianEquivalence
    (C : SimplicialSite.{u})
    (O : Sheaf (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).totalTopology CommRingCat.{u})
    (F : SheafOfModules.{u} ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).totalRingSheaf O)) :
    F.IsQuasicoherentOnSite ↔ (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).IsCartesianModule O F ∧
      ∀ n : SimplexCategory,
        ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentModule O F n).IsQuasicoherentOnSite :=
  ⟨fun hF ↦ ⟨fun _ _ φ ↦
      C.isIso_fiberTransitionModules_of_isQuasicoherentOnSite_quasicoherentCartesianInl O F hF φ,
    SimplicialSiteSituation.isQuasicoherentOnSite_componentModule_quasicoherentCartesianEquivalence
      (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) O F hF⟩,
    fun hF ↦ C.isQuasicoherentOnSite_of_isCartesianModule_quasicoherentCartesianInl O F hF.1 hF.2⟩

end CategoryTheory.SimplicialSite

namespace CategoryTheory.SimplicialSiteSituation

universe u

end CategoryTheory.SimplicialSiteSituation
