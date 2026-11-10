module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.ChangeOfTopologyDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ProperPushforwardBaseChangeUnconditional
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.FppfToEtaleSquares

/-!
# Extension from the small étale site to the big fppf site commutes with a proper direct image

Let `B` be a chosen big fppf site and `f : X ⟶ Y` a morphism of it. Write `a_X` for the morphism
of topoi from the big fppf topos over `X` to the small étale topos of `X`, the composite
`a_X = π_X ∘ ε_X` of the change of topology `ε_X` to the big étale topos and of the projection
`π_X` to the small étale topos (`AlgebraicGeometry.fppfToSmallEtaleMorphism`). The square of
topoi `a_Y ∘ f_{big,fppf} = f_{small} ∘ a_X` of Stacks 0DDM has a canonical base change map

`a_Y⁻¹ ∘ f_{small,*} ⟶ f_{big,fppf,*} ∘ a_X⁻¹`,

`AlgebraicGeometry.bigFppfSmallEtaleBaseChange`, its mate. This file proves that it is an
isomorphism when `f` is proper, Stacks 0DDN.

## Main definitions

* `AlgebraicGeometry.bigFppfSmallEtaleDirectImageIso` — for `f` proper, the isomorphism
  `a_Y⁻¹ ∘ f_{small,*} ≅ f_{big,fppf,*} ∘ a_X⁻¹` given by the base change map.

## Main results

* `AlgebraicGeometry.isIso_bigFppfSmallEtaleBaseChange` — **Stacks 0DDN**: for `f` proper the
  base change map is an isomorphism.
* `AlgebraicGeometry.mateEquiv_symm_whiskerLeft` — changing a side of a square of right adjoints
  by a natural transformation changes its mate accordingly.

## Implementation notes

The source deduces the result from Stacks 0DDJ (1) and 0DDL.
`AlgebraicGeometry.isIso_bigFppfSmallEtaleBaseChange_of_isIso_smallEtaleSetBaseChange` carries
out this deduction, granted proper base change for sheaves of sets (Stacks 0A3U) for `f`; here
that input is supplied by `Stacks.EtaleCohomology.isIso_smallEtaleSetBaseChange_of_isProper`.

## References

* [Stacks Project, Tag 0DDN](https://stacks.math.columbia.edu/tag/0DDN)
* [Stacks Project, Tag 0DDJ](https://stacks.math.columbia.edu/tag/0DDJ)
* [Stacks Project, Tag 0DDL](https://stacks.math.columbia.edu/tag/0DDL)
* [Stacks Project, Tag 0DDM](https://stacks.math.columbia.edu/tag/0DDM)
* [Stacks Project, Tag 0A3U](https://stacks.math.columbia.edu/tag/0A3U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor CategoryTheory.TwoSquare

universe u

namespace AlgebraicGeometry

section Mates

variable {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
  {G : C ⥤ E} {H H' : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)

/-- Changing the side `H` of a square of right adjoints by a natural transformation `ψ : H ⟶ H'`
changes its mate by `ψ` at the bottom. -/
public theorem mateEquiv_symm_whiskerLeft (w : TwoSquare R₁ H G R₂) (ψ : H ⟶ H') :
    (mateEquiv adj₁ adj₂).symm (w.whiskerLeft ψ) =
      ((mateEquiv adj₁ adj₂).symm w).whiskerBottom ψ := by
  refine NatTrans.ext <| funext fun c => ?_
  simp [mateEquiv_symm_apply, TwoSquare.whiskerLeft, TwoSquare.whiskerBottom]

end Mates

variable (B : BigFppfSite.{u}) {X Y : B.Schemes} (f : X ⟶ Y)

/-- **Stacks 0DDN.** Let `f : X ⟶ Y` be a proper morphism of the big fppf site. Then the base
change map `a_Y⁻¹ ∘ f_{small,*} ⟶ f_{big,fppf,*} ∘ a_X⁻¹` is an isomorphism. -/
@[stacks 0DDN]
public theorem isIso_bigFppfSmallEtaleBaseChange [IsProper (B.inclusion.map f)] :
    IsIso (bigFppfSmallEtaleBaseChange B f) :=
  isIso_bigFppfSmallEtaleBaseChange_of_isIso_smallEtaleSetBaseChange B f
    fun _ _ g g' f' sq =>
      have : IsProper ((associatedBigEtaleSite B).inclusion.map f) :=
        ‹IsProper (B.inclusion.map f)›
      Stacks.EtaleCohomology.isIso_smallEtaleSetBaseChange_of_isProper _ g g' f' sq

/-- **Stacks 0DDN**, as an isomorphism of functors: for `f` proper,
`a_Y⁻¹ ∘ f_{small,*} ≅ f_{big,fppf,*} ∘ a_X⁻¹`, by the base change map. -/
public def bigFppfSmallEtaleDirectImageIso [IsProper (B.inclusion.map f)] :
    (associatedBigEtaleSite B).smallPushforward f (Type (u + 1)) ⋙
        (fppfToSmallEtaleMorphism B Y).inverseImage ≅
      (fppfToSmallEtaleMorphism B X).inverseImage ⋙
        (Over.pullback f).sheafPushforwardContinuous (Type (u + 1))
          (B.topology.over Y) (B.topology.over X) :=
  haveI := isIso_bigFppfSmallEtaleBaseChange B f
  asIso (bigFppfSmallEtaleBaseChange B f)

end AlgebraicGeometry
