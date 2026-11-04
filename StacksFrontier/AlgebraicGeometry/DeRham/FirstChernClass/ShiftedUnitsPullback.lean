module

public import StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.DeRhamFirstChernClassPullback
public import StacksFrontier.Homology.DerivedIndexing.SingleDegreeEdge

/-!
# Pullback on the hypercohomology of the sheaf of units placed in degree one

Let `f : X' ⟶ X` be a morphism of schemes. The de Rham first Chern class of
[Stacks, Tag 0FLE] is taken in the degree-two hypercohomology `H²(X, 𝒪_X^*[-1])` of the sheaf of
units placed in cohomological degree one, and the pullback map on that group is
`AlgebraicGeometry.Scheme.Hom.shiftedUnitsCohomologyTwoPullback`, obtained from the pullback

`RΓ(X, 𝒪_X^*[-1]) ⟶ RΓ(X', 𝒪_{X'}^*[-1])`

on derived global sections of `AlgebraicGeometry.Scheme.Hom.derivedSectionsPullback`. The
identification `Pic(X) = H¹(X, 𝒪_X^*)` of [Stacks, Tag 09NU], on the other hand, is natural for
the pullback of *first* cohomology classes, which
`AlgebraicGeometry.Scheme.Hom.unitsPushforward_edge_comp_rightDerivedIso` reads as the degreewise
comparison `Stacks.DerivedIndexing.rightDerivedPlusEdge` of the composite
`Γ(X, -) ∘ f_* = Γ(X', -)` of right derived functors.

This file puts the two in the same language: both are instances of
`Stacks.DerivedIndexing.singleDerivedPullback`, the first in degree one and the second — by
`Stacks.DerivedIndexing.rightDerivedPlusEdge_app_eq` — in degree zero. What is left between them
is the degree shift, which is the content of
`DerivedCategory.Plus.singleFunctorCompHomologyFunctorShiftIso`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.derivedSectionsPullback_comp`: pullback on derived global
  sections along a composite `a ≫ b` of morphisms of complexes is derived global sections of `a`
  followed by pullback along `b`.
* `AlgebraicGeometry.Scheme.Hom.derivedSectionsPushforwardIso_eq`: **the comparison of
  [Stacks, Tag 01EZ] for abelian sheaves is the composition isomorphism
  `R(Γ ∘ f_*) ≅ RΓ ∘ Rf_*` of [Stacks, Tag 015M]**, in the spelling
  `Stacks.DerivedIndexing.rightDerivedPlusCompIso` the degreewise comparison is built from. The
  two are `asIso` of the same transformation, so this holds by `Iso.ext rfl`.
* `AlgebraicGeometry.Scheme.Hom.derivedSectionsPullback_eq'`: pullback on derived global sections
  written with the composition isomorphism of [Stacks, Tag 015M].
* `AlgebraicGeometry.Scheme.Hom.derivedSectionsPullback_mapSinglePlus`: **pullback on derived
  global sections along the comparison `(f_*ℱ)[-q] ⟶ f_*(ℱ[-q])` is
  `Stacks.DerivedIndexing.singleDerivedPullback`.**
* `AlgebraicGeometry.Scheme.Hom.unitsComplexPushforwardMapPlus_eq`: **the pullback of units in
  degree one factors** as the single functor applied to `𝒪_X^* ⟶ f_*𝒪_{X'}^*` followed by the
  comparison `(f_*𝒪_{X'}^*)[-1] ⟶ f_*(𝒪_{X'}^*[-1])`.
* `AlgebraicGeometry.Scheme.Hom.shiftedUnitsDerivedSectionsPullback_eq`: **pullback on
  `RΓ(X, 𝒪_X^*[-1])` is `Stacks.DerivedIndexing.singleDerivedPullback` in degree one**, after the
  pullback of units.

## Implementation notes

The degreewise computation behind `unitsComplexPushforwardMapPlus_eq` is carried out on abstract
data, as `Stacks.DerivedIndexing.mkHomFromSingle_eq_single_map_comp`, and instantiated here:
the sheaf of units is stated in the spelling `TopCat.Sheaf` of the category of sheaves of abelian
groups while the complexes live in the spelling `Stacks.Cohomology.Leray.AbelianSheaf`, and the
two carry separate category instances, so a rewrite performed directly on the sheaf-level
morphism builds a motive that is not type-correct.

## References

* [Stacks Project, Tag 0FMD](https://stacks.math.columbia.edu/tag/0FMD)
* [Stacks Project, Tag 0FLE](https://stacks.math.columbia.edu/tag/0FLE)
* [Stacks Project, Tag 09NU](https://stacks.math.columbia.edu/tag/09NU)
* [Stacks Project, Tag 01EZ](https://stacks.math.columbia.edu/tag/01EZ)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits Opposite TopologicalSpace
open Stacks.Cohomology.Leray Stacks.Cohomology.LerayLowDegree
open Stacks.Cohomology.DerivedPushforwardSections
open Stacks.GlueSquishUnits (unitsPushforwardMap)

universe u

namespace AlgebraicGeometry.Scheme.Hom

attribute [local instance] HasDerivedCategory.standard

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {X' X : Scheme.{u}} (f : X' ⟶ X)

/-- **Pullback on derived global sections along a composite.** A morphism of complexes on `X`
followed by a morphism `L ⟶ f_*K'` induces derived global sections of the first followed by
pullback along the second. -/
theorem derivedSectionsPullback_comp
    {K L : CochainComplex.Plus (AbelianSheaf X.toRingedSpace.carrier)}
    {K' : CochainComplex.Plus (AbelianSheaf X'.toRingedSpace.carrier)}
    (a : K ⟶ L)
    (b : L ⟶ (abelianPushforward.{u, u} f.base).mapCochainComplexPlus.obj K') :
    derivedSectionsPullback f (a ≫ b) =
      (sectionsFunctor X.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Q.map a) ≫
        derivedSectionsPullback f b := by
  rw [derivedSectionsPullback, derivedSectionsPullback, DerivedCategory.Plus.Q.map_comp,
    Functor.map_comp, Category.assoc]

/-- **The comparison `RΓ(X', -) ≅ RΓ(X, -) ∘ Rf_*` of [Stacks, Tag 01EZ] for abelian sheaves is
the composition isomorphism `R(Q ∘ P) ≅ RQ ∘ RP` of [Stacks, Tag 015M]**, in the spelling
`Stacks.DerivedIndexing.rightDerivedPlusCompIso` out of which the degreewise comparison
`Stacks.DerivedIndexing.rightDerivedPlusEdge` is built.

Both are `asIso` of the canonical transformation produced by the universal property of right
derivation from the same unit, so the two transformations are the same; only the `IsIso` instance
through which the inverse is taken differs, and that is not data. -/
theorem derivedSectionsPushforwardIso_eq :
    derivedSectionsPushforwardIso f =
      Stacks.DerivedIndexing.rightDerivedPlusCompIso (abelianPushforward.{u, u} f.base)
        (sectionsFunctor X.toRingedSpace.carrier ⊤) :=
  Iso.ext rfl

/-- **Pullback on derived global sections, written with the composition isomorphism of
[Stacks, Tag 015M].** This is `AlgebraicGeometry.Scheme.Hom.derivedSectionsPullback_eq` with the
comparison of [Stacks, Tag 01EZ] replaced by
`Stacks.DerivedIndexing.rightDerivedPlusCompIso`, and the two applications of derived global
sections collected into one. -/
theorem derivedSectionsPullback_eq'
    {K : CochainComplex.Plus (AbelianSheaf X.toRingedSpace.carrier)}
    {K' : CochainComplex.Plus (AbelianSheaf X'.toRingedSpace.carrier)}
    (φ : K ⟶ (abelianPushforward.{u, u} f.base).mapCochainComplexPlus.obj K') :
    derivedSectionsPullback f φ =
      (sectionsFunctor X.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Q.map φ ≫
            (Functor.mapCochainComplexPlusDerivedUnit
              (abelianPushforward.{u, u} f.base)).app K') ≫
        (Stacks.DerivedIndexing.rightDerivedPlusCompIso (abelianPushforward.{u, u} f.base)
          (sectionsFunctor X.toRingedSpace.carrier ⊤)).inv.app
            (DerivedCategory.Plus.Q.obj K') := by
  rw [derivedSectionsPullback_eq, Functor.map_comp, Category.assoc,
    derivedSectionsPushforwardIso_eq]
  rfl

/-- **Pullback on derived global sections along the comparison `(f_*ℱ)[-q] ⟶ f_*(ℱ[-q])` is the
pullback `Stacks.DerivedIndexing.singleDerivedPullback` attached to a complex concentrated in one
degree.** True by definition, once the comparison of [Stacks, Tag 01EZ] has been identified with
the composition isomorphism of [Stacks, Tag 015M]. -/
theorem derivedSectionsPullback_mapSinglePlus (q : ℤ)
    (Z : AbelianSheaf X'.toRingedSpace.carrier) :
    derivedSectionsPullback f
        ((Stacks.DerivedIndexing.mapSinglePlus
          (abelianPushforward.{u, u} f.base) q).app Z) =
      Stacks.DerivedIndexing.singleDerivedPullback (abelianPushforward.{u, u} f.base)
        (sectionsFunctor X.toRingedSpace.carrier ⊤) q Z :=
  derivedSectionsPullback_eq' f _

/-- **The pullback of units placed in degree one factors through the comparison of the direct
image with the formation of a complex concentrated in degree one**: it is the single functor
applied to `𝒪_X^* ⟶ f_*𝒪_{X'}^*`, followed by
`(f_*𝒪_{X'}^*)[-1] ⟶ f_*(𝒪_{X'}^*[-1])`.

Both sides are morphisms out of a complex concentrated in degree one, so there is a single degree
to check; the computation there is
`Stacks.DerivedIndexing.mkHomFromSingle_eq_single_map_comp`. -/
theorem unitsComplexPushforwardMapPlus_eq :
    unitsComplexPushforwardMapPlus f =
      (Stacks.DerivedIndexing.singlePlusFunctor
            (AbelianSheaf X.toRingedSpace.carrier) 1).map (unitsPushforwardMap f) ≫
        (Stacks.DerivedIndexing.mapSinglePlus (abelianPushforward.{u, u} f.base) 1).app
          (SheafOfModules.unitsAbelianSheaf X'.toRingedSpace) :=
  ObjectProperty.hom_ext _
    (Stacks.DerivedIndexing.mkHomFromSingle_eq_single_map_comp
      (abelianPushforward.{u, u} f.base) 1 (unitsPushforwardMap f)
      (fun k hk => comp_d_unitsComplexPushforward_eq_zero f k hk _))

/-- **Pullback on derived global sections of the sheaf of units placed in degree one is
`Stacks.DerivedIndexing.singleDerivedPullback` in degree one**, after derived global sections of
the pullback of units.

This is the shape in which [Stacks, Tag 0FMD]'s remaining square consumes the left-hand side:
the right-hand side is the degree-one instance of the same construction whose degree-zero
instance is, by `Stacks.DerivedIndexing.rightDerivedPlusEdge_app_eq`, the degreewise comparison
[Stacks, Tag 09NU]'s pullback is natural for. -/
theorem shiftedUnitsDerivedSectionsPullback_eq :
    shiftedUnitsDerivedSectionsPullback f =
      (sectionsFunctor X.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Q.map
            ((Stacks.DerivedIndexing.singlePlusFunctor
              (AbelianSheaf X.toRingedSpace.carrier) 1).map (unitsPushforwardMap f))) ≫
        Stacks.DerivedIndexing.singleDerivedPullback (abelianPushforward.{u, u} f.base)
          (sectionsFunctor X.toRingedSpace.carrier ⊤) 1
          (SheafOfModules.unitsAbelianSheaf X'.toRingedSpace) := by
  refine Eq.trans (congrArg (fun φ => derivedSectionsPullback f φ)
    (unitsComplexPushforwardMapPlus_eq f)) ?_
  refine (derivedSectionsPullback_comp f _ _).trans ?_
  exact congrArg (fun z =>
      (sectionsFunctor X.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus.map
        (DerivedCategory.Plus.Q.map ((Stacks.DerivedIndexing.singlePlusFunctor
          (AbelianSheaf X.toRingedSpace.carrier) 1).map (unitsPushforwardMap f))) ≫ z)
    (derivedSectionsPullback_mapSinglePlus f 1
      (SheafOfModules.unitsAbelianSheaf X'.toRingedSpace))

end AlgebraicGeometry.Scheme.Hom

end
