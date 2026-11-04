module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBaseRelativeDirectImage
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.SiteReindex

/-!
# Perfectness over a smaller base scheme

Let `h : W ⟶ S` be a morphism of a big fppf site, `Z` an algebraic space over `W` and `Y` an
algebraic space over `S` with `ε : Λ_h Z ≅ Y` (Stacks 04SG). This file shows that the change of
base `AlgebraicGeometry.Space.smallerBaseDerivedEquivalence : D(𝒪_Y) ≌ D(𝒪_Z)` preserves and
reflects perfect objects (Stacks 08G5), and so proves the proposition
`AlgebraicGeometry.Space.SmallerBasePerfectComparison`.

The change of base of modules is reindexing along the equivalence of small étale sites
`AlgebraicGeometry.Space.smallerBaseSmallEtaleEquivalenceOfIso`, which carries the structure sheaf
to the structure sheaf on the nose, so perfectness of complexes is carried both ways by
`AlgebraicGeometry.RingedSite.isPerfectComplex_reindex_iff`, exactly as pseudo-coherence is in
`AlgebraicGeometry.Space.isPseudoCoherent_smallerBaseDerivedEquivalence_iff`.

## Main results

* `AlgebraicGeometry.Space.isPerfect_smallerBaseDerivedEquivalence_iff`: the change of base
  preserves and reflects perfectness, for arbitrary models of the two derived categories.
* `AlgebraicGeometry.Space.smallerBasePerfectComparison`: the proposition
  `AlgebraicGeometry.Space.SmallerBasePerfectComparison` holds.

## References

* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) {W S : Scheme.{u}} {hW : B.Contains W} {hS : B.Contains S}
  (h : B.obj hW ⟶ B.obj hS)

section Derived

variable {Z : AlgebraicSpaces B W hW} {Y : AlgebraicSpaces B S hS}
  (ε : (OverShriek.relocalizePresheafFunctor h).obj Z.1 ≅ Y.1)
  [HasDerivedCategory (Modules.{u, u} B S hS Y.1 Y.2)]
  [HasDerivedCategory (Modules.{u, u} B W hW Z.1 Z.2)]

/-- **Perfectness over the smaller base** (Stacks 08G5): an object of `D(𝒪_Y)` is perfect exactly
when the corresponding object of `D(𝒪_Z)` is. Reindexing along an equivalence of ringed sites
preserves and reflects perfectness of complexes
(`AlgebraicGeometry.RingedSite.isPerfectComplex_reindex_iff`), and the change of base on derived
categories is induced by the degreewise one. -/
theorem isPerfect_smallerBaseDerivedEquivalence_iff
    (K : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2)) :
    (smallEtaleRingedSite B W hW Z.1 Z.2).IsPerfect
        ((smallerBaseDerivedEquivalence B h ε).functor.obj K) ↔
      (smallEtaleRingedSite B S hS Y.1 Y.2).IsPerfect K := by
  have := Stacks.SheafOfModules.isDenseSubsite_inverse_of_isContinuous
    (J := (smallEtaleRingedSite B S hS Y.1 Y.2).J)
    (J' := (smallEtaleRingedSite B W hW Z.1 Z.2).J) (smallerBaseSmallEtaleEquivalenceOfIso B h ε)
  have hc : ∀ L : CochainComplex (Modules.{u, u} B S hS Y.1 Y.2) ℤ,
      (smallEtaleRingedSite B W hW Z.1 Z.2).IsPerfectComplex
          (((smallerBaseModulesEquivalenceOfIso B h ε).functor.mapHomologicalComplex
            (ComplexShape.up ℤ)).obj L) ↔
        (smallEtaleRingedSite B S hS Y.1 Y.2).IsPerfectComplex L := fun L =>
    RingedSite.isPerfectComplex_reindex_iff (smallEtaleRingedSite B S hS Y.1 Y.2)
      (smallEtaleRingedSite B W hW Z.1 Z.2).J (smallerBaseSmallEtaleEquivalenceOfIso B h ε) L
  constructor
  · rintro ⟨E, hE, ⟨eE⟩⟩
    let Φ := smallerBaseModulesEquivalenceOfIso B h ε
    let L := (Φ.inverse.mapHomologicalComplex (ComplexShape.up ℤ)).obj E
    let eL : (Φ.functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj L ≅ E :=
      (Φ.mapHomologicalComplex (ComplexShape.up ℤ)).counitIso.app E
    refine ⟨L, (hc L).1 (RingedSite.isPerfectComplex_of_iso _ eL.symm hE), ⟨?_⟩⟩
    exact (smallerBaseDerivedEquivalence B h ε).functor.preimageIso
      ((smallerBaseDerivedEquivalenceFactors B h ε).app L ≪≫ DerivedCategory.Q.mapIso eL ≪≫ eE)
  · rintro ⟨E, hE, ⟨eE⟩⟩
    exact ⟨_, (hc E).2 hE, ⟨((smallerBaseDerivedEquivalenceFactors B h ε).app E).symm ≪≫
      (smallerBaseDerivedEquivalence B h ε).functor.mapIso eE⟩⟩

end Derived

section Comparison

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 10000] HasDerivedCategory.standard

/-- **The proposition `AlgebraicGeometry.Space.SmallerBasePerfectComparison` holds**: the change
of base `AlgebraicGeometry.Space.smallerBaseDerivedEquivalence` preserves and reflects perfect
objects (`AlgebraicGeometry.Space.isPerfect_smallerBaseDerivedEquivalence_iff`). -/
theorem smallerBasePerfectComparison : SmallerBasePerfectComparison B h :=
  fun ε K => isPerfect_smallerBaseDerivedEquivalence_iff B h ε K

end Comparison

end AlgebraicGeometry.Space

end
