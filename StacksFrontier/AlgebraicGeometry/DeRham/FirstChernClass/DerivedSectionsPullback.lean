module

public import StacksFrontier.Algebra.Homology.DerivedCategory.CochainComplexPlusDerivedUnit
public import StacksFrontier.AlgebraicGeometry.DeRham.Functoriality

/-!
# Pullback on derived global sections along a map of complexes of abelian sheaves

Let `f : X' ⟶ X` be a morphism of schemes. A morphism of bounded-below complexes of abelian
sheaves `φ : K ⟶ f_*K'` on `X` induces a map

`RΓ(X, K) ⟶ RΓ(X', K')`

on derived global sections: apply `RΓ(X, -)` to `φ`, then to the derived-functor unit
`f_*K' ⟶ Rf_*K'`, and finally use the identification `RΓ(X', -) ≅ RΓ(X, -) ∘ Rf_*` of
[Stacks, Tag 01EZ]. This file isolates that construction from the de Rham complex it was built
for in `StacksFrontier.AlgebraicGeometry.DeRham.Functoriality`, and proves it functorial: a
commuting square of such data induces a commuting square on derived global sections.

The point of the isolation is that Tag 0FMD's de Rham square needs the *same* pullback map for
the sheaf of units placed in degree one, `𝒪_X^*[-1]`, as the de Rham pullback
`AlgebraicGeometry.Scheme.Hom.deRhamDerivedSectionsPullback` of Tag 0FL6 is for the de Rham
complex; the comparison of the two is then the functoriality proved here, applied to the square
expressing that `d log` commutes with pullback.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.pushforwardQuotIso`: the direct image of a bounded-below complex
  of abelian sheaves, read in the bounded-below homotopy category, is the homotopy class of the
  termwise direct image.
* `AlgebraicGeometry.Scheme.Hom.pushforwardToDerived`: the derived-functor unit
  `f_*K ⟶ Rf_*K` at a bounded-below complex of abelian sheaves.
* `AlgebraicGeometry.Scheme.Hom.derivedSectionsPullback`: **pullback on derived global sections**
  along a morphism of complexes `K ⟶ f_*K'`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.deRhamDerivedSectionsPullback_eq`: **the de Rham pullback on
  derived global sections of Tag 0FL6 is this construction**, at the canonical map of de Rham
  complexes of Tag 07HX. True by definition.
* `AlgebraicGeometry.Scheme.Hom.pushforwardToDerived_eq`: the unit assembled here is the generic
  one, `CategoryTheory.Functor.mapCochainComplexPlusDerivedUnit`.
* `AlgebraicGeometry.Scheme.Hom.derivedSectionsPullback_naturality`: **pullback on derived global
  sections is functorial.** A square `φ ≫ f_*a' = a ≫ ψ` of morphisms of complexes induces a
  commuting square of maps on derived global sections.

## Implementation notes

`pushforwardQuotIso` and `pushforwardToDerived` are the generalizations to an arbitrary
bounded-below complex of `AlgebraicGeometry.Scheme.Hom.quotDeRhamPushforwardIso` and
`AlgebraicGeometry.Scheme.Hom.deRhamPushforwardToDerived`, and they are *written the same way*,
so that `deRhamDerivedSectionsPullback_eq` holds by `rfl` rather than by a transport: the de
Rham pullback of Tag 0FL6 is the canonical object the tag's square has to be stated about, and a
reformulation of it would have to be proved equal to it anyway.

Functoriality is not proved from that spelling. The unit as written has no naturality, being
assembled pointwise out of `AlgebraicGeometry.Scheme.Hom.plusQIsoOn` and `pushforwardQuotIso`;
what carries naturality is Mathlib-style
`CategoryTheory.Functor.mapCochainComplexPlusDerivedUnit`, a natural transformation
`f_*(-) ⋙ Q ⟶ Q ⋙ Rf_*`. So the two are identified first, and that identification is where
the work is:

* `plusQIsoOn_eq`: `plusQIsoOn` is the component of `DerivedCategory.Plus.quotientCompQhIso`.
  Both are preimages under the fully faithful `DerivedCategory.Plus.ι` of a morphism of the
  unbounded derived category, so it is enough to compare those morphisms; the one for
  `quotientCompQhIso` carries two extra factors, and both are identities, because
  `DerivedCategory.Plus.QhCompιIsoιCompQh` and `HomotopyCategory.Plus.quotientCompιIso` are
  `Iso.refl` and `ObjectProperty.liftCompιIso` respectively.
* `pushforwardQuotIso_eq`: `pushforwardQuotIso` is the identity, because
  `CategoryTheory.Functor.mapHomotopyCategoryFactors` is `CategoryTheory.Quotient.lift.isLift`,
  whose components are identities.

Both of those are proved by `show`-ing the reduced form rather than by rewriting: the two
objects `f_*(K)` read in the bounded-below homotopy category -- as the functor induced by `f_*`
applied to the homotopy class, and as the homotopy class of the termwise image -- agree only
definitionally, so a `rw` that moves a morphism between them produces a motive that is not
type-correct at `implicit` transparency. For the same reason the elimination of the identity
factor inside `pushforwardToDerived_eq` is done by `congrArg` against `Category.id_comp` applied
as a term, which elaborates at default transparency.

## References

* [Stacks Project, Tag 0FMD](https://stacks.math.columbia.edu/tag/0FMD)
* [Stacks Project, Tag 0FL6](https://stacks.math.columbia.edu/tag/0FL6)
* [Stacks Project, Tag 07HX](https://stacks.math.columbia.edu/tag/07HX)
* [Stacks Project, Tag 01EZ](https://stacks.math.columbia.edu/tag/01EZ)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits Opposite TopologicalSpace
open Stacks.Cohomology.Leray Stacks.Cohomology.LerayLowDegree
open Stacks.Cohomology.DerivedPushforwardSections

universe u

namespace AlgebraicGeometry.Scheme.Hom

attribute [local instance] HasDerivedCategory.standard

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {X' X : Scheme.{u}} (f : X' ⟶ X)

/-- The direct image of a bounded-below complex of abelian sheaves, read in the homotopy
category, is the homotopy class of the termwise direct image. -/
def pushforwardQuotIso (K : CochainComplex.Plus (AbelianSheaf X'.toRingedSpace.carrier)) :
    (abelianPushforward.{u, u} f.base).mapHomotopyCategoryPlus.obj
        ((HomotopyCategory.Plus.quotient (AbelianSheaf X'.toRingedSpace.carrier)).obj K) ≅
      (HomotopyCategory.Plus.quotient (AbelianSheaf X.toRingedSpace.carrier)).obj
        ((abelianPushforward.{u, u} f.base).mapCochainComplexPlus.obj K) :=
  (HomotopyCategory.Plus.ι (AbelianSheaf X.toRingedSpace.carrier)).preimageIso
    (((abelianPushforward.{u, u} f.base).mapHomotopyCategoryFactors
      (ComplexShape.up ℤ)).app K.obj)

/-- **The derived-functor unit `f_*K ⟶ Rf_*K`** at a bounded-below complex of abelian sheaves,
written as `AlgebraicGeometry.Scheme.Hom.deRhamPushforwardToDerived` is written, so that the de
Rham pullback of [Stacks, Tag 0FL6] is an instance of
`AlgebraicGeometry.Scheme.Hom.derivedSectionsPullback` by definition. It is the generic unit
`CategoryTheory.Functor.mapCochainComplexPlusDerivedUnit`, by
`AlgebraicGeometry.Scheme.Hom.pushforwardToDerived_eq`. -/
def pushforwardToDerived (K : CochainComplex.Plus (AbelianSheaf X'.toRingedSpace.carrier)) :
    DerivedCategory.Plus.Q.obj
        ((abelianPushforward.{u, u} f.base).mapCochainComplexPlus.obj K) ⟶
      (abelianPushforward.{u, u} f.base).rightDerivedFunctorPlus.obj
        (DerivedCategory.Plus.Q.obj K) :=
  (plusQIsoOn X ((abelianPushforward.{u, u} f.base).mapCochainComplexPlus.obj K)).inv ≫
    DerivedCategory.Plus.Qh.map (pushforwardQuotIso f K).inv ≫
    (abelianPushforward.{u, u} f.base).rightDerivedFunctorPlusUnith.app
      ((HomotopyCategory.Plus.quotient (AbelianSheaf X'.toRingedSpace.carrier)).obj K) ≫
    (abelianPushforward.{u, u} f.base).rightDerivedFunctorPlus.map
      (plusQIsoOn X' K).hom

/-- **Pullback on derived global sections** `RΓ(X, K) ⟶ RΓ(X', K')` along a morphism of
bounded-below complexes of abelian sheaves `φ : K ⟶ f_*K'`: derived global sections of `φ`,
followed by derived global sections of the derived-functor unit `f_*K' ⟶ Rf_*K'`, followed by the
identification of derived global sections on `X'` with derived global sections on `X` of the
derived direct image ([Stacks, Tag 01EZ]). -/
def derivedSectionsPullback
    {K : CochainComplex.Plus (AbelianSheaf X.toRingedSpace.carrier)}
    {K' : CochainComplex.Plus (AbelianSheaf X'.toRingedSpace.carrier)}
    (φ : K ⟶ (abelianPushforward.{u, u} f.base).mapCochainComplexPlus.obj K') :
    (sectionsFunctor X.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus.obj
        (DerivedCategory.Plus.Q.obj K) ⟶
      (sectionsFunctor X'.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus.obj
        (DerivedCategory.Plus.Q.obj K') :=
  (sectionsFunctor X.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus.map
      (DerivedCategory.Plus.Q.map φ) ≫
    (sectionsFunctor X.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus.map
      (pushforwardToDerived f K') ≫
    (derivedSectionsPushforwardIso f).inv.app (DerivedCategory.Plus.Q.obj K')

/-- **The de Rham pullback on derived global sections of [Stacks, Tag 0FL6] is pullback along a
morphism of complexes**, at the canonical map of de Rham complexes
`Ω^•_{X/S} ⟶ f_*Ω^•_{X'/S'}` of [Stacks, Tag 07HX]. True by definition: the two are assembled
from the same four factors. -/
theorem deRhamDerivedSectionsPullback_eq {S' S : Scheme.{u}} (p : X ⟶ S) (p' : X' ⟶ S')
    (g : S' ⟶ S) (hcomm : f ≫ p = p' ≫ g) :
    deRhamDerivedSectionsPullback f p p' g hcomm =
      derivedSectionsPullback f (deRhamAbelianPushforwardMapPlus f p p' g hcomm) := rfl

/-- **The pointwise comparison of the two localizations of bounded-below complexes is the
component of the natural one**: `AlgebraicGeometry.Scheme.Hom.plusQIsoOn` is
`DerivedCategory.Plus.quotientCompQhIso` evaluated at the complex. Both are preimages under the
fully faithful inclusion of the bounded-below derived category of a morphism of the unbounded
one, and the two extra factors the natural comparison carries are identities. -/
theorem plusQIsoOn_eq (Y : Scheme.{u})
    (L : CochainComplex.Plus (AbelianSheaf Y.toRingedSpace.carrier)) :
    plusQIsoOn Y L =
      (DerivedCategory.Plus.quotientCompQhIso
        (AbelianSheaf Y.toRingedSpace.carrier)).app L := by
  refine Iso.ext ?_
  ext
  simp only [plusQIsoOn, Functor.preimageIso_hom,
    DerivedCategory.Plus.quotientCompQhIso_hom_app_hom, Iso.app_hom]
  exact DerivedCategory.Plus.ι.map_preimage _

/-- **The direct image of a complex and the direct image of its homotopy class agree on the
nose**: the comparison `AlgebraicGeometry.Scheme.Hom.pushforwardQuotIso` is the identity,
`CategoryTheory.Functor.mapHomotopyCategoryFactors` having identity components. -/
theorem pushforwardQuotIso_eq
    (K : CochainComplex.Plus (AbelianSheaf X'.toRingedSpace.carrier)) :
    pushforwardQuotIso f K = Iso.refl _ := by
  refine Iso.ext ((HomotopyCategory.Plus.ι
    (AbelianSheaf X.toRingedSpace.carrier)).map_injective ?_)
  refine Eq.trans ((HomotopyCategory.Plus.ι
    (AbelianSheaf X.toRingedSpace.carrier)).map_preimage _) ?_
  exact (CategoryTheory.Functor.map_id _ _).symm

/-- **The unit assembled here is the generic derived-functor unit on bounded-below complexes.**
This is what gives `AlgebraicGeometry.Scheme.Hom.derivedSectionsPullback` its functoriality: the
unit as written is pointwise, while
`CategoryTheory.Functor.mapCochainComplexPlusDerivedUnit` is a natural transformation. -/
theorem pushforwardToDerived_eq
    (K : CochainComplex.Plus (AbelianSheaf X'.toRingedSpace.carrier)) :
    pushforwardToDerived f K =
      (Functor.mapCochainComplexPlusDerivedUnit
        (abelianPushforward.{u, u} f.base)).app K := by
  set w := (abelianPushforward.{u, u} f.base).rightDerivedFunctorPlusUnith.app
      ((HomotopyCategory.Plus.quotient (AbelianSheaf X'.toRingedSpace.carrier)).obj K) ≫
    (abelianPushforward.{u, u} f.base).rightDerivedFunctorPlus.map
      (plusQIsoOn X' K).hom with hw
  have hq : DerivedCategory.Plus.Qh.map (pushforwardQuotIso f K).inv =
      𝟙 (DerivedCategory.Plus.Qh.obj
        ((abelianPushforward.{u, u} f.base).mapHomotopyCategoryPlus.obj
          ((HomotopyCategory.Plus.quotient (AbelianSheaf X'.toRingedSpace.carrier)).obj K))) :=
    Eq.trans (congrArg DerivedCategory.Plus.Qh.map
        (congrArg Iso.inv (pushforwardQuotIso_eq f K)))
      (DerivedCategory.Plus.Qh.map_id _)
  have hstep : DerivedCategory.Plus.Qh.map (pushforwardQuotIso f K).inv ≫ w = w :=
    Eq.trans (congrArg (fun z => z ≫ w) hq) (Category.id_comp w)
  have h1 : pushforwardToDerived f K =
      (plusQIsoOn X ((abelianPushforward.{u, u} f.base).mapCochainComplexPlus.obj K)).inv ≫ w :=
    congrArg (fun z =>
      (plusQIsoOn X ((abelianPushforward.{u, u} f.base).mapCochainComplexPlus.obj K)).inv ≫ z)
      hstep
  rw [h1, hw, plusQIsoOn_eq, plusQIsoOn_eq,
    Functor.mapCochainComplexPlusDerivedUnit_app]
  rfl

/-- `AlgebraicGeometry.Scheme.Hom.derivedSectionsPullback` written with the generic
derived-functor unit. -/
theorem derivedSectionsPullback_eq
    {K : CochainComplex.Plus (AbelianSheaf X.toRingedSpace.carrier)}
    {K' : CochainComplex.Plus (AbelianSheaf X'.toRingedSpace.carrier)}
    (φ : K ⟶ (abelianPushforward.{u, u} f.base).mapCochainComplexPlus.obj K') :
    derivedSectionsPullback f φ =
      (sectionsFunctor X.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Q.map φ) ≫
        (sectionsFunctor X.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus.map
          ((Functor.mapCochainComplexPlusDerivedUnit
            (abelianPushforward.{u, u} f.base)).app K') ≫
        (derivedSectionsPushforwardIso f).inv.app (DerivedCategory.Plus.Q.obj K') := by
  change _ ≫ (sectionsFunctor X.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus.map
      (pushforwardToDerived f K') ≫ _ = _
  rw [pushforwardToDerived_eq]

/-- **Pullback on derived global sections is functorial.** Given morphisms of complexes
`φ : K ⟶ f_*K'` and `ψ : L ⟶ f_*L'` and a commuting square `φ ≫ f_*a' = a ≫ ψ`, the induced
maps on derived global sections commute with those induced by `a` and `a'`.

This is the step that carries a sheaf-level square -- for Tag 0FMD, that `d log` commutes with
pullback -- from the complexes to the hypercohomology they compute. -/
theorem derivedSectionsPullback_naturality
    {K L : CochainComplex.Plus (AbelianSheaf X.toRingedSpace.carrier)}
    {K' L' : CochainComplex.Plus (AbelianSheaf X'.toRingedSpace.carrier)}
    (φ : K ⟶ (abelianPushforward.{u, u} f.base).mapCochainComplexPlus.obj K')
    (ψ : L ⟶ (abelianPushforward.{u, u} f.base).mapCochainComplexPlus.obj L')
    (a : K ⟶ L) (a' : K' ⟶ L')
    (h : φ ≫ (abelianPushforward.{u, u} f.base).mapCochainComplexPlus.map a' = a ≫ ψ) :
    (sectionsFunctor X.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Q.map a) ≫
        derivedSectionsPullback f ψ =
      derivedSectionsPullback f φ ≫
        (sectionsFunctor X'.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Q.map a') := by
  have hu := (Functor.mapCochainComplexPlusDerivedUnit
    (abelianPushforward.{u, u} f.base)).naturality a'
  have hc := (derivedSectionsPushforwardIso f).inv.naturality (DerivedCategory.Plus.Q.map a')
  dsimp only [Functor.comp_map] at hu hc
  simp only [derivedSectionsPullback_eq, Category.assoc]
  rw [← Functor.map_comp_assoc (sectionsFunctor X.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus
      (DerivedCategory.Plus.Q.map a) (DerivedCategory.Plus.Q.map ψ),
    ← DerivedCategory.Plus.Q.map_comp, ← h, DerivedCategory.Plus.Q.map_comp,
    Functor.map_comp_assoc,
    ← Functor.map_comp_assoc (sectionsFunctor X.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus
      (DerivedCategory.Plus.Q.map
        ((abelianPushforward.{u, u} f.base).mapCochainComplexPlus.map a'))
      ((Functor.mapCochainComplexPlusDerivedUnit
        (abelianPushforward.{u, u} f.base)).app L'),
    hu, Functor.map_comp_assoc, hc]

end AlgebraicGeometry.Scheme.Hom

end
