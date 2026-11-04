module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.SiteEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAssociatedModuleEtalePullback
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtalePseudoCoherentDescent
public import StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.RingedSiteComparisonConverse

/-!
# Pseudo-coherence on a represented algebraic space and on its scheme

Let `T` be an object of the big fppf site over `S`, with underlying scheme `T`, and let `h_T` be
the algebraic space it represents. The small étale site of `h_T` is the small étale site of the
scheme `T`, and the associated-module functor
`ε^* : Mod(𝒪_T) ⥤ Mod(𝒪_{h_T})` of Stacks 03DU (4) is
`AlgebraicGeometry.Space.representedAssociatedModule`. This file proves that a complex `K` of
`𝒪_T`-modules is `m`-pseudo-coherent in the sense of Stacks 08CB on the scheme `T` exactly when
`ε^*K` is `m`-pseudo-coherent in the sense of Stacks 08FT on the small étale site of `h_T`.

## Main results

* `AlgebraicGeometry.Space.isPseudoCoherentComplexFrom_representedAssociatedModule_iff`: the
  complex-level equivalence.

## The argument

Three identifications are composed:

* on the scheme `T`, pseudo-coherence on the ringed space and on its site of opens agree
  (`AlgebraicGeometry.RingedSpace.PseudoCoherence.isPseudoCoherentComplexFrom_ringedSite_iff`);
* the small Zariski and the small étale site of the scheme `T` see the same pseudo-coherent
  objects, by Stacks 08HE (`AlgebraicGeometry.SmallEtale.pseudoCoherentIffAssociatedModule`),
  read on complexes through Stacks 08FU (2), that every representative of a pseudo-coherent
  object is pseudo-coherent;
* the small étale ringed site of `h_T` is, definitionally, the reindexing of the small étale
  ringed site of the scheme `T` along the comparison equivalence of the two sites, and
  `ε^*` on `h_T` is the reindexing of `ε^*` on `T`; pseudo-coherence is invariant under this
  reindexing (`AlgebraicGeometry.RingedSite.isPseudoCoherentComplexFrom_reindex_iff`).

## References

* [Stacks Project, Tag 08HE](https://stacks.math.columbia.edu/tag/08HE)
* [Stacks Project, Tag 08FT](https://stacks.math.columbia.edu/tag/08FT)
* [Stacks Project, Tag 08CB](https://stacks.math.columbia.edu/tag/08CB)
* [Stacks Project, Tag 08FU](https://stacks.math.columbia.edu/tag/08FU)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 08HE on complexes.** A complex `K` of `𝒪_S`-modules is `m`-pseudo-coherent on the
small Zariski site of `S` exactly when `ε^*K` is `m`-pseudo-coherent on the small étale site of
`S`. -/
theorem isPseudoCoherentComplexFrom_associatedModule_iff
    (K : CochainComplex (SheafOfModules.{u} S.ringCatSheaf) ℤ) (m : ℤ) :
    (smallEtaleRingedSite B S hS).IsPseudoCoherentComplexFrom
        (((associatedModuleOfSheaf B S hS).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) m ↔
      S.zariskiRingedSite.IsPseudoCoherentComplexFrom K m := by
  -- The statement involves no derived category; Stacks 08HE is applied at the standard models.
  let iZ : HasDerivedCategory.{u + 1} (SheafOfModules.{u} S.ringCatSheaf) :=
    HasDerivedCategory.standard _
  let : HasDerivedCategory.{u + 1} (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.O)) := iZ
  let iE : HasDerivedCategory.{u + 1} (SheafOfModules.{u} (structureSheaf B S hS)) :=
    HasDerivedCategory.standard _
  let : HasDerivedCategory.{u + 1} (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O)) := iE
  have h08HE := pseudoCoherentIffAssociatedModule B S hS (DerivedCategory.Q.obj K) m
  refine ⟨fun hK => ?_, fun hK => ?_⟩
  · exact RingedSite.isPseudoCoherentComplexFrom_of_iso_general.{u, u, u, u + 1}
      S.zariskiRingedSite (DerivedCategory.Q.obj K) m
      (h08HE.2 ⟨_, hK, ⟨((associatedModuleOfSheaf B S hS).mapDerivedCategoryFactors.app K).symm⟩⟩)
      K (Iso.refl (DerivedCategory.Q.obj K))
  · have hE : IsPseudoCoherentFromZariski S (DerivedCategory.Q.obj K) m := ⟨K, hK, ⟨Iso.refl _⟩⟩
    exact RingedSite.isPseudoCoherentComplexFrom_of_iso_general.{u + 1, u, u, u + 1}
      (smallEtaleRingedSite B S hS) _ m (h08HE.1 hE) _
      ((associatedModuleOfSheaf B S hS).mapDerivedCategoryFactors.app K).symm

end AlgebraicGeometry.SmallEtale

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Pseudo-coherence on a represented algebraic space is pseudo-coherence on its scheme.** For
an object `T` of the big fppf site over `S` and a complex `K` of `𝒪_T`-modules, `ε^*K` is
`m`-pseudo-coherent on the small étale site of the algebraic space `h_T` exactly when `K` is
`m`-pseudo-coherent on the scheme `T`. -/
theorem isPseudoCoherentComplexFrom_representedAssociatedModule_iff (T : BigFppfOver B S hS)
    (K : CochainComplex ((BigFppfOver.toScheme B S hS).obj T).Modules ℤ) (m : ℤ) :
    RingedSite.IsPseudoCoherentComplexFrom.{u + 1, u, u, u}
        (smallEtaleRingedSite B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
        (((representedAssociatedModule B S hS T
          (isAlgebraicSpace_yoneda B S hS T)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) m ↔
      RingedSpace.PseudoCoherence.IsPseudoCoherentComplexFrom
        (X := ((BigFppfOver.toScheme B S hS).obj T).toRingedSpace) K m :=
  (RingedSite.isPseudoCoherentComplexFrom_reindex_iff
    (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T) T.left.property)
    (SmallEtale.topology B S hS (yoneda.obj T)) (representedSmallEtaleEquivalence B S hS T)
    (((_root_.AlgebraicGeometry.SmallEtale.associatedModuleOfSheaf (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T) T.left.property).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K) m).trans
    ((_root_.AlgebraicGeometry.SmallEtale.isPseudoCoherentComplexFrom_associatedModule_iff
      (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj T) T.left.property K m).trans
      (RingedSpace.PseudoCoherence.isPseudoCoherentComplexFrom_ringedSite_iff
        ((BigFppfOver.toScheme B S hS).obj T).toRingedSpace K m))

end AlgebraicGeometry.Space
