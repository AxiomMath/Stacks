module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat

/-!
# Morphisms of algebraic spaces to the spectrum of a field are flat

Let `B` be a big fppf site, `S` a scheme contained in it and `K` an object of the big fppf site
of `S` whose underlying scheme is isomorphic to the spectrum of a field. Every morphism of
algebraic spaces over `S` from an algebraic space to the presheaf represented by `K` is flat.

## Main results

* `AlgebraicGeometry.Space.isFlat_to_field`: a morphism of algebraic spaces over `S` whose target
  is represented by an object of the site with the spectrum of a field as underlying scheme is
  flat.

## References

* [Stacks Project, Tag 02X1](https://stacks.math.columbia.edu/tag/02X1)
* [Stacks Project, Tag 03ML](https://stacks.math.columbia.edu/tag/03ML)
* [Stacks Project, Tag 04R3](https://stacks.math.columbia.edu/tag/04R3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **A morphism of algebraic spaces to the spectrum of a field is flat.** Let `K` be an object
of the big fppf site of `S` whose underlying scheme is isomorphic to the spectrum of a field `k`.
Then every morphism from an algebraic space over `S` to the presheaf represented by `K` is flat. -/
theorem isFlat_to_field (hX : IsAlgebraicSpace B S hS X)
    {K : BigFppfOver B S hS} {k : Type u} [Field k]
    (e : (BigFppfOver.toScheme B S hS).obj K ≅ Spec (CommRingCat.of k))
    (p : X ⟶ yoneda.obj K) :
    IsFlat B S hS p := by
  let T := BigFppfOver.toScheme B S hS
  let q : yoneda.obj K ⟶ yoneda.obj K := 𝟙 _
  have : PreservesLimitsOfShape WalkingCospan T := by
    show PreservesLimitsOfShape WalkingCospan ((Over.forget (B.obj hS)) ⋙ B.inclusion)
    exact comp_preservesLimitsOfShape _ _
  have hstab (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange] :
      (P.inverseImage T).IsStableUnderBaseChange :=
    ⟨fun sq hg => MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := P) (sq.map T) hg⟩
  have hpre (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
      (h : P (T.map (𝟙 K))) : (P.inverseImage T).presheaf q := by
    have := hstab P
    simpa [q, T] using
      (MorphismProperty.relative_map_iff (F := yoneda) (P := P.inverseImage T)).2 h
  let Qsurj := MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u}) T
  let Qetale := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) T
  have : Qsurj.IsStableUnderBaseChange := hstab _
  have : Qetale.IsStableUnderBaseChange := hstab _
  have hq_surj : Qsurj.presheaf q := hpre _ inferInstance
  have hq_etale : Qetale.presheaf q := hpre _ inferInstance
  obtain ⟨U, a, α, hcomm, ha_surj, ha_etale⟩ :=
    exists_surjective_etale_presentation_lift B S hS hX
      (isAlgebraicSpace_yoneda B S hS K) p K q hq_surj hq_etale
  apply (holdsOnEveryEtaleChart_iff_surjectiveChart B S hS
    (@Flat : MorphismProperty Scheme.{u}) Flat.isEtaleLocalOnSourceAndTarget
    hX (isAlgebraicSpace_yoneda B S hS K) p).2
  refine ⟨U, K, a, q, α, ha_etale, hq_etale, ha_surj, hcomm.symm, ?_⟩
  show Flat (T.map α)
  have h : Flat ((T.map α ≫ e.hom) ≫ e.inv) := inferInstance
  rwa [Category.assoc, Iso.hom_inv_id, Category.comp_id] at h

end AlgebraicGeometry.Space

end
