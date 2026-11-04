module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteEquivalenceTransport
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.LocalNature

/-!
# Strictly perfect local models along an equivalence of sites

Let `e : C' ≌ C` be an equivalence of sites and `R` a sheaf of rings on `C`.  Reindexing along
`e` is an equivalence `Stacks.SheafOfModules.reindexEquivalence` from `R`-modules to modules over
the transported ring.  This file records that a quasi-isomorphism from a strictly perfect complex
to the reindexing of a complex `M` comes from one to `M` itself.

This is what moves a local model of Stacks 08G5 from the slice of the small étale site of `Y` at
a chart `V` to the slice of the small étale site of `X` at the composite chart, for an étale
`f : Y ⟶ X` of algebraic spaces: the two slices are equivalent, and the restriction of `f^*M` to
the first is the reindexing of the restriction of `M` to the second.

## Main results

* `Stacks.SheafOfModules.exists_quasiIso_of_reindex`: a strictly perfect model of the
  reindexing of a complex gives a strictly perfect model of the complex.

## References

* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
* [Stacks Project, Tag 08FL](https://stacks.math.columbia.edu/tag/08FL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v v' u u'

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
  {J : GrothendieckTopology C} {J' : GrothendieckTopology C'}
  (e : C' ≌ C) [e.functor.IsContinuous J' J] [e.inverse.IsContinuous J J']
  (R : Sheaf J RingCat.{w})
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify J' AddCommGrpCat.{w}] [J'.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **A strictly perfect local model transports back along an equivalence of sites.**  Let
`e : C' ≌ C` be an equivalence of sites, `R` a sheaf of rings on `C` and `M` a complex of
`R`-modules.  If a strictly perfect complex over the transported ring maps quasi-isomorphically
to the reindexing of `M`, then a strictly perfect complex of `R`-modules maps
quasi-isomorphically to `M` itself: apply the inverse of the equivalence of module categories,
which is exact and carries the unit module to the unit module, and compose with its unit. -/
theorem exists_quasiIso_of_reindex
    (M : CochainComplex (SheafOfModules.{w} R) ℤ)
    {P : CochainComplex (SheafOfModules.{w} (reindexRing J' e R)) ℤ}
    (hP : IsStrictlyPerfect (reindexRing J' e R) P)
    (q : P ⟶ ((reindexEquivalence.{w, w} (J' := J') e R).functor.mapHomologicalComplex
      (ComplexShape.up ℤ)).obj M) (hq : QuasiIso q) :
    ∃ P' : CochainComplex (SheafOfModules.{w} R) ℤ, IsStrictlyPerfect R P' ∧
      ∃ q' : P' ⟶ M, QuasiIso q' := by
  have : (reindexEquivalence.{w, w} (J' := J') e R).functor.Additive :=
    Functor.additive_of_preserves_binary_products _
  have : (reindexEquivalence.{w, w} (J' := J') e R).inverse.Additive :=
    Functor.additive_of_preserves_binary_products _
  have : (reindexEquivalence.{w, w} (J' := J') e R).inverse.PreservesHomology :=
    Functor.preservesHomologyOfExact _
  have : QuasiIso (((reindexEquivalence.{w, w} (J' := J') e R).inverse.mapHomologicalComplex
      (ComplexShape.up ℤ)).map q) :=
    HomologicalComplex.quasiIso_map_of_preservesHomology q _
  let c : (((reindexEquivalence.{w, w} (J' := J') e R).inverse.mapHomologicalComplex
      (ComplexShape.up ℤ))).obj
      (((reindexEquivalence.{w, w} (J' := J') e R).functor.mapHomologicalComplex
        (ComplexShape.up ℤ)).obj M) ≅ M :=
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl ((reindexEquivalence.{w, w} (J' := J') e R).functor ⋙
        (reindexEquivalence.{w, w} (J' := J') e R).inverse))
      (ComplexShape.up ℤ)).symm.app M ≪≫
      (NatIso.mapHomologicalComplex (reindexEquivalence.{w, w} (J' := J') e R).unitIso.symm
        (ComplexShape.up ℤ)).app M ≪≫
      (Functor.mapHomologicalComplexIdIso _ (ComplexShape.up ℤ)).app M
  refine ⟨(((reindexEquivalence.{w, w} (J' := J') e R).inverse.mapHomologicalComplex
      (ComplexShape.up ℤ))).obj P,
    isStrictlyPerfect_mapHomologicalComplex (reindexEquivalence.{w, w} (J' := J') e R).inverse
      ((reindexEquivalence.{w, w} (J' := J') e R).unitIso.app (SheafOfModules.unit R)) hP,
    (((reindexEquivalence.{w, w} (J' := J') e R).inverse.mapHomologicalComplex
      (ComplexShape.up ℤ))).map q ≫ c.hom, ?_⟩
  have : IsIso c.hom := c.isIso_hom
  infer_instance

end Stacks.SheafOfModules

end
