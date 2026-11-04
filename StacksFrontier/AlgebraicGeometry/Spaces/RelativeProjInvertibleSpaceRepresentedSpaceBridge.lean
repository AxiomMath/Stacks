module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceChartSource

/-!
# One spelling of the represented algebraic space in the source factor of Stacks 0D2Z

The algebraic space over `S` represented by an object `U` of the big fppf site of `S` is written
three ways in the library:

* `⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩`, the spelling of
  `AlgebraicGeometry.Space.representedSpaceMap` and of every statement of
  `RelativeProjInvertibleSpaceChartSourceSquare`;
* `AlgebraicGeometry.Space.representedAlgebraicSpace B S hS U`, the spelling of
  `…RelativeProjSituation.fibreToSpaceHom`;
* `AlgebraicGeometry.yonedaSpace B S hS U`, the spelling of `AlgebraicGeometry.Space.pointHom`.

The last two are abbreviations whose value is the first, verbatim, so the three are equal by one
unfolding of a reducible constant (`AlgebraicGeometry.Space.representedAlgebraicSpace_eq_mk`,
`AlgebraicGeometry.Space.yonedaSpace_eq_representedAlgebraicSpace`).  The source identification
`…InvertibleTwistingRestriction.chartSourceIso` combines all three: its leading morphism
`pointHom w` starts at `yonedaSpace`, the morphism `representedSpaceMap c_w` ends at the first
spelling of the fibre, and `fibreToSpaceHom` starts at `representedAlgebraicSpace` of the fibre.

## Main results

* `…InvertibleTwistingRestriction.chartSourceIso_eq_value`: **the source identification in one
  spelling**, as the value which `AlgebraicGeometry.Space.chartSourceShaped_square` takes as its
  hypothesis `hJ`, with every represented algebraic space written as
  `⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩`.

## Implementation notes

Supplied as the hypothesis `hJ` of `AlgebraicGeometry.Space.chartSourceShaped_square`,
`…chartSourceIso_eq_value` matches it syntactically up to proofs, where `rfl` makes the
unifier compare `…chartSourceIso` with its value (about 79,000 heartbeats per use).  The function
of the `congrArg` inside the comparison of Stacks 03LU has its domain written out: left to be
inferred, it is unified against the mixed spellings of the morphisms and the elaboration of the
statement exceeds the heartbeat budget at `whnf`.

## References

* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull)

universe u m

attribute [local instance 5000] AlgebraicGeometry.Space.SmallEtale.instHasSheafify
  AlgebraicGeometry.Space.SmallEtale.instWEqualsLocallyBijective

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)

/-- The algebraic space represented by `U` is the anonymous-constructor spelling used by
`AlgebraicGeometry.Space.representedSpaceMap`. -/
theorem representedAlgebraicSpace_eq_mk :
    representedAlgebraicSpace B S hS U = ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ :=
  rfl

/-- The two named spellings of the algebraic space represented by `U` agree. -/
theorem yonedaSpace_eq_representedAlgebraicSpace :
    yonedaSpace B S hS U = representedAlgebraicSpace B S hS U :=
  rfl

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

variable {s : RelativeProjSituation.{u, m}}
  {X : AlgebraicSpaces s.shrink.site s.shrink.base s.shrink.containsBase} {f : X ⟶ s.shrink.space}
  {L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O)}
  [hL : Stacks.SheafOfModules.IsInvertible
    (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property L]
  {ψ : SheafOfModules.GradedAlgebra.UnitalHom
    ((gradedPull (X := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X)
      (Y := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase s.shrink.space)
      (smallEtaleRingedToposHom s.shrink.site s.shrink.base s.shrink.containsBase f)).obj
        s.shrink.algebra)
    (Stacks.SheafOfModules.TensorPower.laurentAlgebra
      (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property L)}
  (Px : Presentation s.site s.base s.containsBase s.space.obj s.space.property)
  {T : BigFppfOver s.shrink.site s.shrink.base s.shrink.containsBase}
  (w : yoneda.obj T ⟶ (locusSpaceOfUnitalHom s f L ψ).obj)

/-- **The source identification `w^*(r^*𝒪(d)) ≅ (c_w^*𝒪(d))^a` in one spelling**: the value of
`…InvertibleTwistingRestriction.chartSourceIso` in the shape of the hypothesis `hJ` of
`AlgebraicGeometry.Space.chartSourceShaped_square`, with the represented algebraic spaces of `T`
and of `T ×_Y Proj_Y(𝒜)` written as `⟨yoneda.obj _, isAlgebraicSpace_yoneda _ _ _ _⟩` throughout
(rather than as `yonedaSpace` at the source of `pointHom w` and as `representedAlgebraicSpace` at
the source of `fibreToSpaceHom`). -/
theorem chartSourceIso_eq_value (d : ℤ) :
    chartSourceIso Px w (locusOpen_locusPoint w) d =
      ((((modulePullbackCompIso s.site s.base s.containsBase
            (pointHom (X := (ofUnitalHom s f L ψ).locusSpace X.property) w :
              (⟨yoneda.obj T, isAlgebraicSpace_yoneda s.site s.base s.containsBase T⟩ :
                AlgebraicSpaces s.site s.base s.containsBase) ⟶ _)
            ((ofUnitalHom s f L ψ).invertibleSpaceMorphism X.property)).app
              (s.twistModule Px d).obj ≪≫
          (eqToIso (congrArg (fun k : (⟨yoneda.obj T,
                isAlgebraicSpace_yoneda s.site s.base s.containsBase T⟩ :
                  AlgebraicSpaces s.site s.base s.containsBase) ⟶
                ⟨s.relativeProjFunctor, s.isAlgebraicSpace_relativeProjFunctor⟩ =>
              (modulePullback s.site s.base s.containsBase k).obj (s.twistModule Px d).obj)
            (pointHom_comp_invertibleSpaceMorphism w :
              @CategoryStruct.comp (AlgebraicSpaces s.site s.base s.containsBase) _ _ _ _
                  (pointHom (X := (ofUnitalHom s f L ψ).locusSpace X.property) w :
                    (⟨yoneda.obj T, isAlgebraicSpace_yoneda s.site s.base s.containsBase T⟩ :
                      AlgebraicSpaces s.site s.base s.containsBase) ⟶ _)
                  ((ofUnitalHom s f L ψ).invertibleSpaceMorphism X.property) =
                @CategoryStruct.comp (AlgebraicSpaces s.site s.base s.containsBase) _ _ _ _
                  (representedSpaceMap s.site s.base s.containsBase
                    ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w)))
                  (s.fibreToSpaceHom T (locusPoint w ≫ f.hom) :
                    (⟨yoneda.obj (s.relativeProjPoints.fibre T (locusPoint w ≫ f.hom)),
                      isAlgebraicSpace_yoneda s.site s.base s.containsBase
                        (s.relativeProjPoints.fibre T (locusPoint w ≫ f.hom))⟩ :
                      AlgebraicSpaces s.site s.base s.containsBase) ⟶ _))) : _) ≪≫
          ((modulePullbackCompIso s.site s.base s.containsBase
            (representedSpaceMap s.site s.base s.containsBase
              ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w)))
            (s.fibreToSpaceHom T (locusPoint w ≫ f.hom) :
              (⟨yoneda.obj (s.relativeProjPoints.fibre T (locusPoint w ≫ f.hom)),
                isAlgebraicSpace_yoneda s.site s.base s.containsBase
                  (s.relativeProjPoints.fibre T (locusPoint w ≫ f.hom))⟩ :
                AlgebraicSpaces s.site s.base s.containsBase) ⟶ _)).app
              (s.twistModule Px d).obj).symm) :
          (modulePullback s.site s.base s.containsBase
              (pointHom (X := (ofUnitalHom s f L ψ).locusSpace X.property) w :
                (⟨yoneda.obj T, isAlgebraicSpace_yoneda s.site s.base s.containsBase T⟩ :
                  AlgebraicSpaces s.site s.base s.containsBase) ⟶ _)).obj
              ((modulePullback s.site s.base s.containsBase
                ((ofUnitalHom s f L ψ).invertibleSpaceMorphism X.property)).obj
                (s.twistModule Px d).obj) ≅
            (modulePullback s.site s.base s.containsBase
              (representedSpaceMap s.site s.base s.containsBase
                ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w)))).obj
              ((modulePullback s.site s.base s.containsBase
                (s.fibreToSpaceHom T (locusPoint w ≫ f.hom) :
                  (⟨yoneda.obj (s.relativeProjPoints.fibre T (locusPoint w ≫ f.hom)),
                    isAlgebraicSpace_yoneda s.site s.base s.containsBase
                      (s.relativeProjPoints.fibre T (locusPoint w ≫ f.hom))⟩ :
                    AlgebraicSpaces s.site s.base s.containsBase) ⟶ _)).obj
                (s.twistModule Px d).obj))) ≪≫
        (modulePullback s.site s.base s.containsBase (representedSpaceMap s.site s.base
            s.containsBase ((ofUnitalHom s f L ψ).chartSection (locusPoint w)
              (locusOpen_locusPoint w)))).mapIso
          (s.fibreToSpaceTwistModuleIso Px T (locusPoint w ≫ f.hom) d) ≪≫
        modulePullbackRepresentedQuasicoherentIso s.site s.base s.containsBase
          ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
          (s.twistPieceQcoh T (locusPoint w ≫ f.hom) d) :=
  rfl

end AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction
