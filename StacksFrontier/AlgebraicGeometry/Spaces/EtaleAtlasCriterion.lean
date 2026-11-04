module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelPairRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafAlgebraicGlueing
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Sheafification

/-!
# A surjective étale cover makes a sheaf an algebraic space

A sheaf `F` on the big fppf site over `S` is an algebraic space as soon as it admits a
representable, surjective, étale morphism from an object `U` of the site, and likewise as soon
as it admits one from an algebraic space. In particular the condition on the diagonal in the
definition of an algebraic space need not be checked.

Both criteria assume, beyond the hypotheses of Stacks 0BGQ and 0BGR, effective descent along the
covering sieves of the site at the monomorphisms locally of finite type
(`AlgebraicGeometry.Space.IsEffectiveDescentAlongCoveringSieve`).

## Main results

* `AlgebraicGeometry.isAlgebraicSpace_of_surjective_etale_atlas_of_descent`: a sheaf with a
  representable, surjective, étale atlas by an object of the site is an algebraic space.
* `AlgebraicGeometry.isAlgebraicSpace_of_relativelyRepresentable_surjective_etale_of_descent`:
  a sheaf with a representable, surjective, étale cover by an algebraic space is an algebraic
  space.

## References

* [Stacks Project, Tag 0BGQ](https://stacks.math.columbia.edu/tag/0BGQ)
* [Stacks Project, Tag 0BGR](https://stacks.math.columbia.edu/tag/0BGR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **Stacks 0BGQ**, granted effective descent along the covering sieves of the site at the
monomorphisms locally of finite type. A sheaf `F` on the big fppf site over `S` admitting a
representable, surjective, étale morphism `f : h_U ⟶ F` from an object `U` of the site is an
algebraic space over `S`. -/
theorem isAlgebraicSpace_of_surjective_etale_atlas_of_descent
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    (U : BigFppfOver B S hS) (f : yoneda.obj U ⟶ F)
    (hsurj : MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)) f)
    (hetale : MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)) f)
    (hdesc : Space.IsEffectiveDescentAlongCoveringSieve B S hS
      (MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType)) :
    IsAlgebraicSpace B S hS F := by
  have hrep := hsurj.rep
  let R := hrep.pullback f
  let t : R ⟶ U := yoneda.preimage (hrep.fst f)
  let s : R ⟶ U := hrep.snd f
  have hR : IsPullback (yoneda.map t) (yoneda.map s) f f := by
    simpa [s, t] using hrep.isPullback f
  let P : BigFppfOver B S hS ⥤ Over S := Over.post (X := B.obj hS) B.inclusion
  have hsource : (Space.relation B S hS s t).source = P.map s := prod.lift_snd _ _
  have htarget : (Space.relation B S hS s t).target = P.map t := prod.lift_fst _ _
  have : Stacks.Groupoids.IsEtaleEquivalenceRelation (Space.relation B S hS s t) :=
    { isEquivalenceRelation := by
        rw [htarget, hsource]
        exact Space.isEquivalenceRelation_of_isPullback B S hS f t s hR
      etale_source := by
        rw [hsource]
        exact hetale.property f (hrep.fst f) (hrep.snd f) (hrep.isPullback f)
      etale_target := by
        rw [htarget]
        exact hetale.property f (yoneda.map s) t hR.flip }
  have hQ := Space.isAlgebraicSpace_quotientSheaf_relation_of_diagDescent B S hS s t hdesc
  have hqrep := Space.relativelyRepresentable_quotientMap_of_isAlgebraicSpace B S hS s t hQ
  have hqR := Space.quotientMap_isPullback B S hS s t
  exact isAlgebraicSpace_of_surjective_etale_atlas_of_isAlgebraicSpace_quotient B S hS hF f hR
    hsurj hetale hQ (Space.quotientMap B S hS s t) hqR.w
    fun G hG k hk ↦ existsUnique_desc_of_surjective_etale_atlas B S hS hQ.isSheaf
      (Space.quotientMap B S hS s t) hqR (Space.quotientMap_surjective B S hS s t hqrep)
      (Space.quotientMap_etale B S hS s t hqrep) hG k hk

/-- The relative property of a composition stable property pulled back to the site is stable
under composition. -/
private theorem presheaf_inverseImage_isStableUnderComposition
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {P : MorphismProperty Scheme.{u}} (hP : P.IsStableUnderComposition) :
    (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderComposition := by
  have := Space.inverseImage_isStableUnderComposition B S hS hP
  exact MorphismProperty.relative_isStableUnderComposition _

/-- **Stacks 0BGR**, granted effective descent along the covering sieves of the site at the
monomorphisms locally of finite type. A sheaf `F` on the big fppf site over `S` admitting a
representable, surjective, étale morphism `a : G ⟶ F` from an algebraic space `G` over `S` is
an algebraic space over `S`. -/
theorem isAlgebraicSpace_of_relativelyRepresentable_surjective_etale_of_descent
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {G F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hG : IsAlgebraicSpace B S hS G)
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    (a : G ⟶ F)
    (hs : MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)) a)
    (he : MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)) a)
    (hdesc : Space.IsEffectiveDescentAlongCoveringSieve B S hS
      (MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType)) :
    IsAlgebraicSpace B S hS F := by
  obtain ⟨U, f, hfs, hfe⟩ := hG.exists_atlas
  have := presheaf_inverseImage_isStableUnderComposition B S hS
    surjective_isStableUnderComposition.{u}
  have := presheaf_inverseImage_isStableUnderComposition B S hS
    Space.etale_isStableUnderComposition.{u}
  exact isAlgebraicSpace_of_surjective_etale_atlas_of_descent B S hS hF U (f ≫ a)
    (MorphismProperty.comp_mem _ _ _ hfs hs) (MorphismProperty.comp_mem _ _ _ hfe he) hdesc

end AlgebraicGeometry

end
