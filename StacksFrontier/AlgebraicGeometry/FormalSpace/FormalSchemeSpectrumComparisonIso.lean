module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalScheme.FunctorOfPointsAffine
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSchemeSpectrumComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.MorphismToAffineScheme
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Cocontinuous
public import StacksFrontier.CategoryTheory.Functor.FullyFaithfulYonedaRestriction
public import StacksFrontier.CategoryTheory.Sites.Stackification.UniversalProperty

/-!
# The formal spectrum is the functor of points of the affine formal scheme (Stacks 0AIE)

Let `A` be an admissible topological ring over a terminal base scheme `S` contained in a big
fppf site `B`. `StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSchemeSpectrumComparison`
builds the comparison morphism
`AlgebraicGeometry.FormalSpace.spfFormalSchemeFppfComparison` from the formal spectrum of `A`
as an affine formal algebraic space over `S` to the functor of points of `Spf A` as an affine
formal scheme à la EGA, and leaves open whether it is an isomorphism. This file proves that it
is, which is the colimit formula `h_{Spf A} = colim h_{Spec (A/I)}` of Stacks 0AIE read in the
category of fppf sheaves over `S`, and deduces unconditionally that the functor of points of
an affine formal scheme is a *classical* affine formal algebraic space over `S`.

## Main definitions

* `AlgebraicGeometry.BigFppfOver.fullyFaithfulToScheme`: over a terminal base the canonical
  functor from the big fppf site of `S` to all schemes is fully faithful.
* `AlgebraicGeometry.FormalSpace.schemePresheafFppfRestriction`: the restriction of a presheaf
  of `Type u` on all schemes to the big fppf site of `S`, with its values lifted — the functor
  of which `AlgebraicGeometry.FormalSpace.formalSchemeFppfPresheafFunctor` is the composite
  with the functor of points.
* `AlgebraicGeometry.FormalSpace.spfFormalSchemeFppfComparisonIso`: the comparison morphism as
  an isomorphism.

## Main results

* `AlgebraicGeometry.FormalSpace.isIso_spfFormalSchemeFppfComparison`: **Stacks 0AIE**, the
  colimit formula. The comparison morphism is an isomorphism of fppf sheaves over `S`.
* `AlgebraicGeometry.FormalSpace.isClassical_formalSchemePointsFppfSheaf`: **Stacks 0AIE**, the
  type of the functor of points. It is a classical affine formal algebraic space over `S`, with
  no hypothesis beyond admissibility of `A` and the source's own size conditions.

## Implementation notes

*The three steps.* The comparison morphism is `CategoryTheory.Limits.colimit.desc` out of the
colimit of represented quotient spectra, taken in fppf sheaves, and the colimit formula of the
source is proved on *affine* schemes. Three things therefore have to happen.

First, the colimit in fppf sheaves has to be recognised as the sheafification of the colimit of
the underlying presheaves. That is immediate once one knows that
`CategoryTheory.Sheaf.sheafifiedYoneda` is `CategoryTheory.uliftYoneda` followed by
sheafification, because `CategoryTheory.presheafToSheaf` is a left adjoint and so preserves
the colimit.

Second, the colimit of the represented quotient spectra, as presheaves on the site, has to be
identified with the restriction to the site of the colimit of the functors of points of the
quotient spectra on all schemes. This is where the base scheme enters, and it is the step that
cannot be taken over a general base: an object `T` of the site contributes
`Mor_{Formal Schemes}(T, Spec (A/I))` on one side and `Mor_S(T, Spec (A/I))` on the other, and
the two agree exactly because a terminal base imposes no condition — which is
`AlgebraicGeometry.BigFppfOver.fullyFaithfulToScheme` composed with full faithfulness of
`AlgebraicGeometry.schemeToFormalScheme`. The identification is then the restriction of
representables along a fully faithful functor, and the two restriction functors involved
preserve colimits.

Third, the comparison map on all schemes is locally bijective for the Zariski topology —
`AlgebraicGeometry.isLocallyInjective_spfQuotientPointsColimitMap` and
`AlgebraicGeometry.isLocallySurjective_spfQuotientPointsColimitMap_of_isAdmissible`, the latter
being the affine case of Stacks 0AHZ — and this has to be moved onto the big fppf site of `S`.
That is `AlgebraicGeometry.BigFppfOver.isCocontinuous_toScheme_zariskiTopology` together with
`CategoryTheory.Presheaf.isLocallyInjective_whisker` and its surjective companion; the lift of
the values is harmless by
`CategoryTheory.Presheaf.isLocallyInjective_whiskerRight_typeUliftFunctor`.

*Why no sheafification of the right-hand side.* The source sheafifies both sides and notes that
the right-hand side is already a sheaf. Here the right-hand side is taken to be the sheaf
`AlgebraicGeometry.FormalSpace.formalSchemePointsFppfSheaf` from the start, the fppf sheaf
condition on the functor of points being
`AlgebraicGeometry.FormalSpace.isFppfSheafFormalSchemePoints_formalScheme`, so no comparison of
a presheaf with its sheafification is needed on that side. What replaces it is the
sheafification adjunction: a morphism out of the sheafified colimit is tested by composing with
`CategoryTheory.toSheafify`, and local bijectivity passes between the two because
`CategoryTheory.toSheafify` is itself locally bijective.

*The base scheme is a hypothesis, not a choice.* Stacks 0AIE opens by assuming the base is
`Spec (Z)`, and the implementation notes of
`StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSchemeSpectrumComparison` explain why that is
load-bearing. `CategoryTheory.Limits.IsTerminal` is the invariant form of the same assumption:
a scheme is terminal exactly when it is isomorphic to the spectrum of the integers.

## References

* [EGA I, Chapter I, Section 10]
* [Stacks Project, Tag 0AHZ](https://stacks.math.columbia.edu/tag/0AHZ)
* [Stacks Project, Tag 0AI1](https://stacks.math.columbia.edu/tag/0AI1)
* [Stacks Project, Tag 0AI2](https://stacks.math.columbia.edu/tag/0AI2)
* [Stacks Project, Tag 0AID](https://stacks.math.columbia.edu/tag/0AID)
* [Stacks Project, Tag 0AIE](https://stacks.math.columbia.edu/tag/0AIE)
* [Stacks Project, Tag 0AIF](https://stacks.math.columbia.edu/tag/0AIF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

namespace BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Over a terminal base the big fppf site of `S` is a full subcategory of schemes.** Its
objects are schemes with a morphism to `S` and its morphisms are morphisms of schemes
commuting with those, and over a terminal base every morphism of schemes does.

The preimage of a morphism of schemes is
`AlgebraicGeometry.Space.overMapOfSchemeHom`; this packages it as full faithfulness. -/
noncomputable def fullyFaithfulToScheme (hterm : IsTerminal S) :
    (BigFppfOver.toScheme B S hS).FullyFaithful where
  preimage {U T} g := Space.overMapOfSchemeHom B S hS hterm U T g
  map_preimage g := B.inclusion.map_preimage g
  preimage_map f := Over.OverMorphism.ext (B.inclusion.preimage_map f.left)

end BigFppfOver

namespace FormalSpace

attribute [local instance] sheaf_hasColimits

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Restriction of a presheaf on schemes to the big fppf site -/

/-- A presheaf of `Type u` on the category of all schemes, restricted along
`AlgebraicGeometry.BigFppfOver.toScheme` to the big fppf site of `S` and with its values
lifted to `Type (u + 1)`.

`AlgebraicGeometry.FormalSpace.formalSchemeFppfPresheafFunctor` is the composite of the functor
of points of a formal scheme with this functor; it is given a name of its own because what is
needed below is that it preserves colimits, which is a statement about it and not about the
functor of points. -/
noncomputable def schemePresheafFppfRestriction (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    ((Scheme.{u})ᵒᵖ ⥤ Type u) ⥤ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)) :=
  (Functor.whiskeringLeft _ _ _).obj (BigFppfOver.toScheme B S hS).op ⋙
    (Functor.whiskeringRight _ _ _).obj uliftFunctor.{u + 1, u}

/-- The functor of points of a formal scheme on the big fppf site of `S` is the restriction of
its functor of points on all schemes. -/
theorem formalSchemeFppfPresheafFunctor_eq (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    formalSchemeFppfPresheafFunctor B S hS =
      formalSchemePointsFunctor ⋙ schemePresheafFppfRestriction B S hS :=
  rfl

/-- The restriction of the functor of points of a formal scheme is its functor of points on the
big fppf site of `S`. -/
theorem schemePresheafFppfRestriction_obj_formalSchemePoints (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (X : FormalScheme.{u}) :
    (schemePresheafFppfRestriction B S hS).obj (formalSchemePoints X) =
      formalSchemeFppfPresheaf B S hS X :=
  rfl

/-- Restriction of presheaves on schemes to the big fppf site of `S` preserves `u`-small
colimits. -/
instance preservesColimitsOfSize_schemePresheafFppfRestriction :
    PreservesColimitsOfSize.{u, u} (schemePresheafFppfRestriction B S hS) :=
  ⟨fun {J} _ ↦ inferInstanceAs (PreservesColimitsOfShape J
    ((Functor.whiskeringLeft _ _ _).obj (BigFppfOver.toScheme B S hS).op ⋙
      (Functor.whiskeringRight _ _ _).obj uliftFunctor.{u + 1, u}))⟩

/-! ### The diagram of quotient spectra on the site -/

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A]

/-- The diagram of quotient spectra of a quotient system, restricted to the ideals of
definition and read as a diagram of objects of the big fppf site of `S` rather than of its
affine part. This is the diagram whose represented sheaves Stacks 0AIE takes the colimit of. -/
noncomputable abbrev QuotientSystem.idealOfDefinitionSiteDiagram (D : QuotientSystem B S hS A) :
    OrderDual (IdealsOfDefinition A) ⥤ BigFppfOver B S hS :=
  (idealOfDefinitionIndex A).monotone.functor ⋙ D.diagram ⋙ BigAffineFppf.inclusion B S hS

omit [IsTopologicalRing A] [IsLinearTopology A A] in
/-- The underlying schemes of the quotient stages are the spectra of the quotients of `A` by
its ideals of definition, which is the diagram of
`AlgebraicGeometry.spfQuotientDiagram`. -/
theorem QuotientSystem.idealOfDefinitionSiteDiagram_comp_toScheme (D : QuotientSystem B S hS A) :
    D.idealOfDefinitionSiteDiagram ⋙ BigFppfOver.toScheme B S hS = spfQuotientDiagram A :=
  rfl

/-- Over a terminal base the big fppf site of `S` is a full subcategory of formal schemes à la
EGA: a morphism of formal schemes between two schemes of the site is a morphism of schemes by
Stacks 0AI0, and over a terminal base it is a morphism of the site. -/
noncomputable def fullyFaithfulToFormalScheme (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (hterm : IsTerminal S) :
    (BigFppfOver.toScheme B S hS ⋙ schemeToFormalScheme).FullyFaithful :=
  (BigFppfOver.fullyFaithfulToScheme B S hS hterm).comp
    (Functor.FullyFaithful.ofFullyFaithful schemeToFormalScheme)

/-- **The two readings of the quotient stages agree over a terminal base.** The sheaf
represented by a quotient stage, as an object of the big fppf site of `S`, has the same
underlying presheaf as the functor of points of that stage read as a formal scheme and
restricted to the site; and the identification is natural in the ideal of definition.

This is the one step of Stacks 0AIE that uses the base scheme. The sections of the left-hand
side over an object `T` are the morphisms `T ⟶ Spec (A/I)` *over `S`*, those of the right-hand
side the morphisms of formal schemes from the underlying scheme of `T`, and the two agree
because `AlgebraicGeometry.BigFppfOver.toScheme` composed with
`AlgebraicGeometry.schemeToFormalScheme` is fully faithful. -/
noncomputable def quotientPointsFppfPresheafDiagramIso (hterm : IsTerminal S)
    (D : QuotientSystem B S hS A) :
    D.idealOfDefinitionSiteDiagram ⋙ uliftYoneda.{u + 1} ≅
      spfQuotientPointsDiagram A ⋙ schemePresheafFppfRestriction B S hS :=
  let K := BigFppfOver.toScheme B S hS ⋙ schemeToFormalScheme
  let e : D.idealOfDefinitionSiteDiagram ⋙ yoneda ≅
      D.idealOfDefinitionSiteDiagram ⋙
        (K ⋙ yoneda ⋙ (Functor.whiskeringLeft (BigFppfOver B S hS)ᵒᵖ (FormalScheme.{u})ᵒᵖ
          (Type u)).obj K.op) :=
    Functor.isoWhiskerLeft D.idealOfDefinitionSiteDiagram
      (fullyFaithfulToFormalScheme B S hS hterm).yonedaRestrictionIso.symm
  Functor.isoWhiskerRight e
    ((Functor.whiskeringRight (BigFppfOver B S hS)ᵒᵖ (Type u) (Type (u + 1))).obj
      uliftFunctor.{u + 1, u})

omit [IsTopologicalRing A] [IsLinearTopology A A] in
/-- The identification sends a morphism `T ⟶ Spec (A/I)` of the site to the morphism of formal
schemes it induces. -/
theorem quotientPointsFppfPresheafDiagramIso_hom_app_app (hterm : IsTerminal S)
    (D : QuotientSystem B S hS A) (I : OrderDual (IdealsOfDefinition A))
    (T : BigFppfOver B S hS)
    (f : ULift.{u + 1} (T ⟶ D.idealOfDefinitionSiteDiagram.obj I)) :
    ((quotientPointsFppfPresheafDiagramIso hterm D).hom.app I).app (op T) f =
      ULift.up (schemeToFormalScheme.map ((BigFppfOver.toScheme B S hS).map f.down)) :=
  rfl

/-! ### The comparison map on the site -/

/-- The comparison map of the colimit formula of Stacks 0AIE, restricted to the big fppf site
of `S` and with its values lifted: the morphism from the colimit of the functors of points of
the quotient spectra to the functor of points of `Spf A`, read on the site. -/
noncomputable def spfQuotientFppfPointsColimitMap (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (hA : TopologicalRing.IsAdmissible A) :
    (schemePresheafFppfRestriction B S hS).obj (colimit (spfQuotientPointsDiagram A)) ⟶
      formalSchemeFppfPresheaf B S hS (spfFormalScheme A hA) :=
  (schemePresheafFppfRestriction B S hS).map (spfQuotientPointsColimitMap A hA)

/-- The comparison map restricted to a quotient stage is the point of `Spf A` determined by the
quotient point `Spec (A/I) ⟶ Spf A` of Stacks 0AHY. -/
theorem restriction_map_colimit_ι_comp_spfQuotientFppfPointsColimitMap
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hA : TopologicalRing.IsAdmissible A) (I : OrderDual (IdealsOfDefinition A)) :
    (schemePresheafFppfRestriction B S hS).map (colimit.ι (spfQuotientPointsDiagram A) I) ≫
        spfQuotientFppfPointsColimitMap B S hS hA =
      (schemePresheafFppfRestriction B S hS).map ((spfQuotientPointsCocone A hA).ι.app I) :=
  Eq.trans ((schemePresheafFppfRestriction B S hS).map_comp _ _).symm
    (congrArg (schemePresheafFppfRestriction B S hS).map
      (colimit.ι_desc (spfQuotientPointsCocone A hA) I))

/-- **The comparison map is locally injective on the big fppf site of `S`.** It is injective at
every scheme, hence locally injective for the Zariski topology on schemes
(`AlgebraicGeometry.isLocallyInjective_spfQuotientPointsColimitMap`), and local injectivity is
carried along a cocontinuous functor. -/
theorem isLocallyInjective_spfQuotientFppfPointsColimitMap
    (hA : TopologicalRing.IsAdmissible A) :
    Presheaf.IsLocallyInjective (BigFppfOver.topology B S hS)
      (spfQuotientFppfPointsColimitMap B S hS hA) := by
  let := isLocallyInjective_spfQuotientPointsColimitMap A hA
  let := Presheaf.isLocallyInjective_whisker (BigFppfOver.topology B S hS)
    Scheme.zariskiTopology.{u} (BigFppfOver.toScheme B S hS) (spfQuotientPointsColimitMap A hA)
  exact Presheaf.isLocallyInjective_whiskerRight_typeUliftFunctor (BigFppfOver.topology B S hS)
    (Functor.whiskerLeft (BigFppfOver.toScheme B S hS).op (spfQuotientPointsColimitMap A hA))

/-- **The comparison map is locally surjective on the big fppf site of `S`.** Every point of
`Spf A` over an affine scheme factors through a quotient stage, which is the surjectivity half
of Stacks 0AHZ, so the map is locally surjective for the Zariski topology on schemes
(`AlgebraicGeometry.isLocallySurjective_spfQuotientPointsColimitMap_of_isAdmissible`), and
local surjectivity is carried along a cocontinuous functor. -/
theorem isLocallySurjective_spfQuotientFppfPointsColimitMap
    (hA : TopologicalRing.IsAdmissible A) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      (spfQuotientFppfPointsColimitMap B S hS hA) := by
  let := isLocallySurjective_spfQuotientPointsColimitMap_of_isAdmissible A hA
  let := Presheaf.isLocallySurjective_whisker (BigFppfOver.topology B S hS)
    Scheme.zariskiTopology.{u} (BigFppfOver.toScheme B S hS) (spfQuotientPointsColimitMap A hA)
  exact Presheaf.isLocallySurjective_whiskerRight_typeUliftFunctor (BigFppfOver.topology B S hS)
    (Functor.whiskerLeft (BigFppfOver.toScheme B S hS).op (spfQuotientPointsColimitMap A hA))

/-! ### The comparison morphism is an isomorphism -/

/-- The comparison map of Stacks 0AIE as a morphism out of the colimit of the *presheaves*
represented by the quotient stages on the big fppf site of `S`: the colimit is identified with
the restricted colimit of the functors of points by
`AlgebraicGeometry.FormalSpace.quotientPointsFppfPresheafDiagramIso`, and the comparison map is
`AlgebraicGeometry.FormalSpace.spfQuotientFppfPointsColimitMap`.

Sheafifying this gives the comparison morphism of Stacks 0AIE; see
`colimitDesc_eq_presheafToSheaf_map_spfQuotientFppfPresheafComparison`. -/
noncomputable def spfQuotientFppfPresheafComparison (hterm : IsTerminal S)
    (hA : TopologicalRing.IsAdmissible A) (D : QuotientSystem B S hS A) :
    colimit (D.idealOfDefinitionSiteDiagram ⋙ uliftYoneda.{u + 1}) ⟶
      formalSchemeFppfPresheaf B S hS (spfFormalScheme A hA) :=
  (HasColimit.isoOfNatIso (quotientPointsFppfPresheafDiagramIso hterm D)).hom ≫
    (preservesColimitIso (schemePresheafFppfRestriction B S hS)
      (spfQuotientPointsDiagram A)).inv ≫
    spfQuotientFppfPointsColimitMap B S hS hA

/-- The comparison map restricted to a quotient stage is the quotient point of Stacks 0AHY,
read through Yoneda's lemma. -/
theorem colimit_ι_comp_spfQuotientFppfPresheafComparison (hterm : IsTerminal S)
    (hA : TopologicalRing.IsAdmissible A) (D : QuotientSystem B S hS A)
    (I : OrderDual (IdealsOfDefinition A)) :
    colimit.ι (D.idealOfDefinitionSiteDiagram ⋙ uliftYoneda.{u + 1}) I ≫
        spfQuotientFppfPresheafComparison hterm hA D =
      (uliftYonedaEquiv.{u + 1}
        (X := D.idealOfDefinitionSiteDiagram.obj I)
        (F := formalSchemeFppfPresheaf B S hS (spfFormalScheme A hA))).symm
          (ULift.up ((spfQuotientCocone A hA).ι.app I)) := by
  rw [spfQuotientFppfPresheafComparison, HasColimit.isoOfNatIso_ι_hom_assoc,
    ι_preservesColimitIso_inv_assoc, restriction_map_colimit_ι_comp_spfQuotientFppfPointsColimitMap]
  ext T x
  rfl

/-- The comparison map on the site is locally injective. -/
theorem isLocallyInjective_spfQuotientFppfPresheafComparison (hterm : IsTerminal S)
    (hA : TopologicalRing.IsAdmissible A) (D : QuotientSystem B S hS A) :
    Presheaf.IsLocallyInjective (BigFppfOver.topology B S hS)
      (spfQuotientFppfPresheafComparison hterm hA D) := by
  let := isLocallyInjective_spfQuotientFppfPointsColimitMap (B := B) (S := S) (hS := hS) hA
  rw [spfQuotientFppfPresheafComparison]
  infer_instance

/-- The comparison map on the site is locally surjective. -/
theorem isLocallySurjective_spfQuotientFppfPresheafComparison (hterm : IsTerminal S)
    (hA : TopologicalRing.IsAdmissible A) (D : QuotientSystem B S hS A) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      (spfQuotientFppfPresheafComparison hterm hA D) := by
  let := isLocallySurjective_spfQuotientFppfPointsColimitMap (B := B) (S := S) (hS := hS) hA
  rw [spfQuotientFppfPresheafComparison]
  infer_instance

/-- The sheafification of the comparison map, restricted to a quotient stage. -/
theorem presheafToSheaf_map_colimit_ι_comp_spfQuotientFppfPresheafComparison
    (hterm : IsTerminal S) (hA : TopologicalRing.IsAdmissible A) (D : QuotientSystem B S hS A)
    (I : OrderDual (IdealsOfDefinition A)) :
    (presheafToSheaf (BigFppfOver.topology B S hS) (Type (u + 1))).map
          (colimit.ι (D.idealOfDefinitionSiteDiagram ⋙ uliftYoneda.{u + 1}) I) ≫
        (presheafToSheaf (BigFppfOver.topology B S hS) (Type (u + 1))).map
          (spfQuotientFppfPresheafComparison hterm hA D) =
      (presheafToSheaf (BigFppfOver.topology B S hS) (Type (u + 1))).map
        ((uliftYonedaEquiv.{u + 1}
          (X := D.idealOfDefinitionSiteDiagram.obj I)
          (F := formalSchemeFppfPresheaf B S hS (spfFormalScheme A hA))).symm
            (ULift.up ((spfQuotientCocone A hA).ι.app I))) := by
  rw [← Functor.map_comp, colimit_ι_comp_spfQuotientFppfPresheafComparison]

/-- **The cocone of quotient points is a colimit cocone**, which is the colimit formula
`h_{Spf A} = colim h_{Spec (A/I)}` of Stacks 0AIE.

The comparison map on the site is locally bijective, so it becomes an isomorphism after
sheafification; the functor of points is already an fppf sheaf, so its sheafification is itself;
and sheafification preserves the colimit. -/
noncomputable def isColimitSpfQuotientFppfCocone (hterm : IsTerminal S)
    (hA : TopologicalRing.IsAdmissible A) (D : QuotientSystem B S hS A) :
    IsColimit (spfQuotientFppfCocone hA D) := by
  letI := isLocallyInjective_spfQuotientFppfPresheafComparison hterm hA D
  letI := isLocallySurjective_spfQuotientFppfPresheafComparison hterm hA D
  haveI hmap : IsIso ((presheafToSheaf (BigFppfOver.topology B S hS) (Type (u + 1))).map
      (spfQuotientFppfPresheafComparison hterm hA D)) :=
    (((BigFppfOver.topology B S hS).W_iff_isIso_map_of_adjunction
      (sheafificationAdjunction (BigFppfOver.topology B S hS) (Type (u + 1)))
      (spfQuotientFppfPresheafComparison hterm hA D)).1
        ((BigFppfOver.topology B S hS).W_of_isLocallyBijective
          (spfQuotientFppfPresheafComparison hterm hA D)))
  haveI hcounit : IsIso ((sheafificationAdjunction (BigFppfOver.topology B S hS)
      (Type (u + 1))).counit.app
      (formalSchemePointsFppfSheaf B S hS (spfFormalScheme A hA))) :=
    NatIso.isIso_app_of_isIso _ _
  exact IsColimit.ofIsoColimit
    (isColimitOfPreserves (presheafToSheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
      (colimit.isColimit (D.idealOfDefinitionSiteDiagram ⋙ uliftYoneda.{u + 1})))
    (Cocone.ext (show (presheafToSheaf (BigFppfOver.topology B S hS) (Type (u + 1))).obj
          (colimit (D.idealOfDefinitionSiteDiagram ⋙ uliftYoneda.{u + 1})) ≅
        formalSchemePointsFppfSheaf B S hS (spfFormalScheme A hA) from
      @asIso _ _ _ _ ((presheafToSheaf (BigFppfOver.topology B S hS) (Type (u + 1))).map
          (spfQuotientFppfPresheafComparison hterm hA D)) hmap ≪≫
        @asIso _ _ _ _ ((sheafificationAdjunction (BigFppfOver.topology B S hS)
          (Type (u + 1))).counit.app
          (formalSchemePointsFppfSheaf B S hS (spfFormalScheme A hA))) hcounit)
      fun I => ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ (sheafificationAdjunction (BigFppfOver.topology B S hS)
            (Type (u + 1))).counit.app
            (formalSchemePointsFppfSheaf B S hS (spfFormalScheme A hA)))
          (presheafToSheaf_map_colimit_ι_comp_spfQuotientFppfPresheafComparison
            hterm hA D I)).trans (Adjunction.homEquiv_counit
            (sheafificationAdjunction (BigFppfOver.topology B S hS) (Type (u + 1)))
            _ _ _).symm)))

/-- **Stacks 0AIE, the colimit formula.** The comparison morphism from the formal spectrum of an
admissible topological ring `A` over a terminal base to the functor of points of the affine
formal scheme `Spf A` is an isomorphism of fppf sheaves over `S`. -/
@[stacks 0AIE "h_{Spf A} = colim h_{Spec (A/I)} as fppf sheaves: the comparison morphism from \
the formal spectrum to the functor of points of the affine formal scheme is an isomorphism"]
theorem isIso_spfFormalSchemeFppfComparison (hterm : IsTerminal S)
    (hA : TopologicalRing.IsAdmissible A) (D : QuotientSystem B S hS A) :
    IsIso (spfFormalSchemeFppfComparison hA D) := by
  have hdesc : colimit.desc D.idealOfDefinitionDiagram (spfQuotientFppfCocone hA D) =
      (IsColimit.coconePointUniqueUpToIso (colimit.isColimit D.idealOfDefinitionDiagram)
        (isColimitSpfQuotientFppfCocone hterm hA D)).hom :=
    colimit.hom_ext fun I => (colimit.ι_desc _ I).trans
      (IsColimit.comp_coconePointUniqueUpToIso_hom _ _ I).symm
  have h : spfFormalSchemeFppfComparison hA D =
      ((D.formalSpectrumIsoIdealOfDefinitionColimit hA.1).symm ≪≫
        IsColimit.coconePointUniqueUpToIso (colimit.isColimit D.idealOfDefinitionDiagram)
          (isColimitSpfQuotientFppfCocone hterm hA D)).hom :=
    congrArg (fun g => (D.formalSpectrumIsoIdealOfDefinitionColimit hA.1).inv ≫ g) hdesc
  rw [h]
  exact Iso.isIso_hom _

/-- **Stacks 0AIE, the colimit formula**, as an isomorphism: the formal spectrum of an admissible
topological ring over a terminal base *is* the functor of points of the affine formal scheme it
defines. -/
noncomputable def spfFormalSchemeFppfComparisonIso (hterm : IsTerminal S)
    (hA : TopologicalRing.IsAdmissible A) (D : QuotientSystem B S hS A) :
    formalSpectrum D ≅ formalSchemePointsFppfSheaf B S hS (spfFormalScheme A hA) :=
  haveI := isIso_spfFormalSchemeFppfComparison hterm hA D
  asIso (spfFormalSchemeFppfComparison hA D)

/-! ### The type of the functor of points -/

/-- **Stacks 0AIE, the type of the functor of points.** The functor of points of the affine
formal scheme `Spf A` of an admissible topological ring `A` over a terminal base is a
*classical* affine formal algebraic space over `S` in the sense of Stacks 0AID (1).

Nothing is assumed beyond admissibility of `A` and the source's own size conditions: that the
quotient spectra lie in the chosen big fppf site, which is part of the datum of a quotient
system, and that their coproduct does, which is
`AlgebraicGeometry.FormalSpace.QuotientSystem.HasLargeSite`. The fppf sheaf condition on the
functor of points is `AlgebraicGeometry.FormalSpace.isFppfSheafFormalSchemePoints_formalScheme`
and the identification with the formal spectrum is
`AlgebraicGeometry.FormalSpace.isIso_spfFormalSchemeFppfComparison`. -/
@[stacks 0AIE "the functor of points of an affine formal scheme over a terminal base is a \
classical affine formal algebraic space"]
theorem isClassical_formalSchemePointsFppfSheaf (hterm : IsTerminal S)
    (hA : TopologicalRing.IsAdmissible A) (D : QuotientSystem B S hS A)
    (hB : D.HasLargeSite) :
    IsClassical B S hS (formalSchemePointsFppfSheaf B S hS (spfFormalScheme A hA)) :=
  isClassical_formalSchemeFppfSheaf_of_iso_formalSpectrum hA D hB
    (spfFormalSchemeFppfComparisonIso hterm hA D)

/-- **Stacks 0AIE.** The functor of points of an affine formal scheme over a terminal base is an
affine formal algebraic space over `S`; it is the affineness half of
`AlgebraicGeometry.FormalSpace.isClassical_formalSchemePointsFppfSheaf`. -/
@[stacks 0AIE "the functor of points of an affine formal scheme over a terminal base is an \
affine formal algebraic space"]
theorem isAffineFormalAlgebraicSpace_formalSchemePointsFppfSheaf (hterm : IsTerminal S)
    (hA : TopologicalRing.IsAdmissible A) (D : QuotientSystem B S hS A)
    (hB : D.HasLargeSite) :
    IsAffineFormalAlgebraicSpace B S hS
      (formalSchemePointsFppfSheaf B S hS (spfFormalScheme A hA)) :=
  (isClassical_formalSchemePointsFppfSheaf hterm hA D hB).1.1

end FormalSpace

end AlgebraicGeometry

end
