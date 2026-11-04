module

public import StacksFrontier.AlgebraicGeometry.Spaces.BeauvilleLaszloGlueingQuasiAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.BeauvilleLaszloGlueingQuasiAffineFlatPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.CoveringMap
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.FlatRelationQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.SeparatedQuasiFiniteDescent
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A quotient by a closed flat equivalence relation is separated

Let `j : R ⟶ U ×_Z U` be an equivalence relation of algebraic spaces over a presheaf `Z` on
the big fppf site of `S`, whose target and source maps `t, s : R ⟶ U` are flat and locally of
finite presentation, and such that `(t, s) : R ⟶ U ⨯ U` is a closed immersion (the product
being taken over `S`). Then the quotient sheaf `U/R` is an algebraic space which is separated
over `S`.

This is the last paragraph of the proof of Stacks 0F9U. The quotient `Y = U/R` is an algebraic
space by Bootstrap, Theorem 04S6. The quotient map `π : U ⟶ Y` is flat, locally of finite
presentation and surjective, and `R = U ×_Y U`. Hence `π ⨯ π : U ⨯ U ⟶ Y ⨯ Y` is flat, locally
of finite presentation and surjective, so a one-member fppf (hence fpqc) covering, along which
the diagonal of `Y` base-changes to the closed immersion `R ⟶ U ⨯ U`. Being a closed immersion
is fpqc local on the target (Stacks 0420), so the diagonal of `Y` is a closed immersion.

## Main results

* `AlgebraicGeometry.Space.isSeparatedOver_quotientSheaf_of_isClosedImmersion`: the quotient
  sheaf of a flat, locally finitely presented equivalence relation which is a closed subspace
  of `U ⨯ U` is an algebraic space separated over `S`.

## References

* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 0420](https://stacks.math.columbia.edu/tag/0420)
* [Stacks Project, Tag 0F9U](https://stacks.math.columbia.edu/tag/0F9U)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- **The quotient by a closed flat equivalence relation is separated.** Let `j` be an
equivalence relation of algebraic spaces `R ⟶ U ×_Z U` whose target and source maps are flat
and locally of finite presentation. If `(t, s) : R ⟶ U ⨯ U` is a closed immersion, then the
quotient sheaf `U/R` is an algebraic space and is separated over `S`.

This is the step of the proof of Stacks 0F9U reading separatedness of `Y = T/W` off the closed
immersion `W ⟶ T ×_X T`: the diagonal of the quotient base-changes along the fppf covering
`U ⨯ U ⟶ Y ⨯ Y` to `(t, s)`, and closed immersions descend (Stacks 0420). -/
@[sga "3 VIB 9.2.1" "(ii), special case"]
theorem isSeparatedOver_quotientSheaf_of_isClosedImmersion
    (site : BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    [HasSheafify (BigFppfOver.topology site S hS) (Type u)]
    {Z : (BigFppfOver site S hS)ᵒᵖ ⥤ Type u} {R U : Over Z} (j : PreRelation R U)
    (hR : IsAlgebraicSpace site S hS R.left) (hU : IsAlgebraicSpace site S hS U.left)
    (hrel : CategoryTheory.IsEquivalenceRelation j.target j.source)
    (htF : IsFlat site S hS j.target.left)
    (htL : IsLocallyOfFinitePresentation site S hS j.target.left)
    (hsF : IsFlat site S hS j.source.left)
    (hsL : IsLocallyOfFinitePresentation site S hS j.source.left)
    (hci : IsClosedImmersion site S hS
      (prod.lift j.target.left j.source.left : R.left ⟶ U.left ⨯ U.left)) :
    IsAlgebraicSpace site S hS (quotientSheaf j).obj ∧
      IsSeparatedOver site S hS (quotientSheaf j).obj := by
  have hY : IsAlgebraicSpace site S hS (quotientSheaf j).obj :=
    bootstrap04S6QuotientSheaf site S hS j hR hU hrel htF htL hsF hsL
  refine ⟨hY, ?_⟩
  let Usp : AlgebraicSpaces site S hS := ⟨U.left, hU⟩
  let Ysp : AlgebraicSpaces site S hS := ⟨(quotientSheaf j).obj, hY⟩
  let π : Usp ⟶ Ysp := ObjectProperty.homMk (toQuotientSheaf j)
  -- the quotient map is flat, locally of finite presentation and surjective
  have hπF : IsFlat site S hS π.hom :=
    holdsOnEveryEtaleChart_toQuotientSheaf j hrel hR hU hY
      (@AlgebraicGeometry.Flat.{u} : MorphismProperty Scheme.{u})
      Flat.isEtaleLocalOnSourceAndTarget
      (holdsOnEveryEtaleChart_isStableUnderBaseChange site S hS
        (@AlgebraicGeometry.Flat.{u} : MorphismProperty Scheme.{u})
        Flat.isEtaleLocalOnSourceAndTarget) htF
  have hπL : IsLocallyOfFinitePresentation site S hS π.hom :=
    holdsOnEveryEtaleChart_toQuotientSheaf j hrel hR hU hY
      (@AlgebraicGeometry.LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u})
      LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget
      (holdsOnEveryEtaleChart_isStableUnderBaseChange site S hS
        (@AlgebraicGeometry.LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u})
        LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget) htL
  have hπS : IsSurjective site S hS π.hom := isSurjective_toQuotientSheaf j
  -- hence so is `π ⨯ π`
  have : (flatProperty site S hS).IsStableUnderComposition :=
    { comp_mem := fun {A₁ A₂ A₃} u v hu hv =>
        isFlat_comp site S hS A₁.property A₂.property A₃.property u.hom v.hom hu hv }
  have : (locallyOfFinitePresentationProperty site S hS).IsStableUnderComposition :=
    { comp_mem := fun {A₁ A₂ A₃} u v hu hv =>
        isLocallyOfFinitePresentation_comp site S hS A₁.property A₂.property A₃.property
          u.hom v.hom hu hv }
  let pp := AlgebraicSpaces.productMapHom site S hS π
  have hpF : IsFlat site S hS pp.hom :=
    AlgebraicSpaces.prop_productMapHom site S hS (flatProperty site S hS) π hπF
  have hpL : IsLocallyOfFinitePresentation site S hS pp.hom :=
    AlgebraicSpaces.prop_productMapHom site S hS
      (locallyOfFinitePresentationProperty site S hS) π hπL
  have hpS : IsSurjective site S hS pp.hom :=
    AlgebraicSpaces.prop_productMapHom site S hS (surjectiveMorphismProperty site S hS) π hπS
  -- so `π ⨯ π` is a one-member fppf, hence fpqc, covering of `Y ⨯ Y`
  have hfppf : IsFppfCovering site S hS
      (fun _ : PUnit.{u + 1} => (AlgebraicSpaces.product site S hS Usp Usp).obj)
      (fun _ => pp.hom) :=
    { target_isAlgebraicSpace := (AlgebraicSpaces.product site S hS Ysp Ysp).property
      source_isAlgebraicSpace := fun _ => (AlgebraicSpaces.product site S hS Usp Usp).property
      flat := fun _ => hpF
      locallyOfFinitePresentation := fun _ => hpL
      jointly_surjective := by
        rw [Set.iUnion_const]
        exact Set.range_eq_univ.mpr hpS }
  have hcov : Topology.IsCovering .fpqc site S hS
      (fun _ : PUnit.{u + 1} => (AlgebraicSpaces.product site S hS Usp Usp).obj)
      (fun _ => pp.hom) :=
    ⟨(AlgebraicSpaces.product site S hS Ysp Ysp).property,
      fun _ => (AlgebraicSpaces.product site S hS Usp Usp).property,
      isFpqcCovering_of_isFppfCovering site S hS _ _ hfppf⟩
  refine isSeparatedOver_of_kernelPair_isClosedImmersion.{u, u} site S hS π hcov ?_
  -- the kernel pair of `π` is `R`, and `kernelPairToProduct π` is `(t, s)` up to that iso
  have hpbP : IsPullback (pullback.fst π π).hom (pullback.snd π π).hom π.hom π.hom :=
    AlgebraicSpaces.isPullback_hom site S hS (IsPullback.of_hasPullback π π)
  have hpbR : IsPullback j.target.left j.source.left (toQuotientSheaf j) (toQuotientSheaf j) :=
    (isPullback_toQuotientSheaf j hrel hR.isSheaf hU.isSheaf).flip
  let e : R.left ≅ (pullback π π).obj := hpbR.isoIsPullback _ _ hpbP
  have he₁ : e.hom ≫ (pullback.fst π π).hom = j.target.left :=
    hpbR.isoIsPullback_hom_fst _ _ hpbP
  have he₂ : e.hom ≫ (pullback.snd π π).hom = j.source.left :=
    hpbR.isoIsPullback_hom_snd _ _ hpbP
  have heq : e.hom ≫ (AlgebraicSpaces.kernelPairToProduct site S hS π).hom =
      prod.lift j.target.left j.source.left := by
    refine prod.hom_ext ?_ ?_
    · change e.hom ≫ prod.lift (pullback.fst π π).hom (pullback.snd π π).hom ≫ prod.fst = _
      rw [prod.lift_fst, prod.lift_fst, he₁]
    · change e.hom ≫ prod.lift (pullback.fst π π).hom (pullback.snd π π).hom ≫ prod.snd = _
      rw [prod.lift_snd, prod.lift_snd, he₂]
  let Q : MorphismProperty ((BigFppfOver site S hS)ᵒᵖ ⥤ Type u) :=
    (MorphismProperty.inverseImage (@AlgebraicGeometry.IsClosedImmersion.{u})
      (BigFppfOver.toScheme site S hS)).presheaf
  have : Q.RespectsIso := MorphismProperty.relative_respectsIso _
  rw [← heq] at hci
  exact (Q.cancel_left_of_respectsIso e.hom _).mp hci

end AlgebraicGeometry.Space

end
