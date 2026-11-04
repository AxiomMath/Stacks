module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineCompletionTypes
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSchemeComparison
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSchemeComparisonSheaf
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSpectrumClassical

/-!
# The bridge between the formal spectrum of a formal scheme and of a formal space (Stacks 0AIE)

Two developments in this library carry a formal spectrum `Spf A`, and Stacks 0AIE is the
statement that they describe the same object.

* On the **formal-scheme** side `AlgebraicGeometry.spfFormalScheme` is, for an admissible
  topological ring `A`, an object of `AlgebraicGeometry.FormalScheme` — a locally topologically
  ringed space à la EGA. Its functor of points `AlgebraicGeometry.formalSchemePoints` is a
  presheaf of `Type u` on the category of *all* schemes.
* On the **formal-space** side `AlgebraicGeometry.FormalSpace.formalSpectrum` is, for a
  topological ring with a `AlgebraicGeometry.FormalSpace.QuotientSystem` over `S`, an object of
  `AlgebraicGeometry.FormalSpace.FppfSheaf B S hS` — a sheaf of `Type (u + 1)` on the big fppf
  site of `S`. The five types of Stacks 0AID are predicates on such sheaves.

The crossing has three independent gaps, and this file closes the two that are structural.

*The site and the value universe.* These are crossed by
`AlgebraicGeometry.FormalSpace.formalSchemeFppfPresheaf`, which restricts `h_𝔛` along
`AlgebraicGeometry.BigFppfOver.toScheme` and lifts its values; see
`StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSchemeComparison`. Granted the fppf sheaf
condition it produces an object of the ambient category, and the comparison below lands there.

*The index of the colimit.* Stacks 0AIE takes its colimit over the *ideals of definition* of the
admissible ring `A`, whereas Stacks 0AIF and the McQuillan criterion of Stacks 0AIC take theirs
over the *weak* ideals of definition. The two agree, because in a pre-admissible ring the ideals
of definition are cofinal below the weak ideals of definition. That is
`AlgebraicGeometry.FormalSpace.final_idealOfDefinitionIndex` and the colimit identification it
yields, `AlgebraicGeometry.FormalSpace.QuotientSystem.formalSpectrumIsoIdealOfDefinitionColimit`.

*The base scheme.* The comparison morphism below is built unconditionally from the quotient
points of Stacks 0AHY, and it is an isomorphism as soon as the base scheme is terminal — which
is the source's `Spec (Z)`, and is a hypothesis of the source rather than a gap in this library:
the comparison cannot be an isomorphism over a general base, because the two sides are
presheaves of different things. That is
`AlgebraicGeometry.FormalSpace.isIso_spfFormalSchemeFppfComparison` in
`StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSchemeSpectrumComparisonIso`, which also
carries the unconditional form of the transport of classicality stated below.

## Main definitions

* `AlgebraicGeometry.FormalSpace.idealOfDefinitionIndex`: the ideals of definition of `A` as a
  subfamily of its weak ideals of definition, both ordered by reverse inclusion.
* `AlgebraicGeometry.FormalSpace.QuotientSystem.idealOfDefinitionDiagram`: the diagram of
  quotient spectra of a quotient system, restricted to the ideals of definition — the index
  Stacks 0AIE uses.
* `AlgebraicGeometry.FormalSpace.spfQuotientFppfSection`: the point of `h_{Spf A}` over the
  quotient spectrum `Spec (A ⧸ I)` of an ideal of definition, as a section of the fppf sheaf of
  points.
* `AlgebraicGeometry.FormalSpace.spfFormalSchemeFppfComparison`: the comparison morphism
  `Spf A ⟶ h_{Spf A}` of fppf sheaves over `S`.

## Main results

* `AlgebraicGeometry.FormalSpace.final_idealOfDefinitionIndex` and
  `AlgebraicGeometry.FormalSpace.QuotientSystem.formalSpectrumIsoIdealOfDefinitionColimit`:
  **Stacks 0AIE**, the index reconciliation. The colimit over the ideals of definition of an
  admissible ring is the formal spectrum of Stacks 0AIF, whose index is the weak ideals of
  definition.
* `AlgebraicGeometry.FormalSpace.isClassical_formalSchemeFppfSheaf_of_iso_formalSpectrum`: the
  transport. Granted the identification of `h_{Spf A}` with `Spf A`, the functor of points of
  an affine formal scheme is a *classical* affine formal algebraic space over `S`. Over a
  terminal base the identification is a theorem, and the unconditional conclusion is
  `AlgebraicGeometry.FormalSpace.isClassical_formalSchemePointsFppfSheaf`.

## Implementation notes

*Which direction transports.* `AlgebraicGeometry.FormalSpace.IsClassical` and the other four
types of Stacks 0AID are invariant under isomorphism of fppf sheaves
(`AlgebraicGeometry.FormalSpace.isClassical_of_iso` and its siblings), so a statement about
`Spf A` on the formal-space side transports to `h_{Spf A}` and back along the comparison
isomorphism, in both directions and with no further hypothesis. What is *not* symmetric is the
relation to the ring: admissibility of `A` gives classicality of the sheaf, but not conversely.
The equivalence of the five conditions of Stacks 0AIC is proved in this library, so that is not
the obstacle; what is missing is a choice of presenting ring as a function of the sheaf, 0AIC
giving only that one exists and is unique up to isomorphism of topological rings.

*Size and universe conditions.* The comparison is between a sheaf of `Type (u + 1)` on the big
fppf site of `S` and the lift of a presheaf of `Type u` on all schemes, so `A` must live in
`Type u`, which it does. Two size conditions enter, both of them the source's own and neither
avoidable here: the quotient spectra must lie in the chosen site, which is
`AlgebraicGeometry.FormalSpace.QuotientSystem.inSite`, and for the classicality conclusion their
coproduct must too, which is
`AlgebraicGeometry.FormalSpace.QuotientSystem.HasLargeSite`. The size condition of Stacks 0AI1 —
`AlgebraicGeometry.IsSizeBoundedFormalScheme` — is *not* needed for anything below; it governs
the full faithfulness of the functor of points, which is the last sentence of Stacks 0AIE and is
not proved here.

*Why the base scheme matters, and why the source fixes it.* Stacks 0AIE opens by assuming the
base scheme is `Spec (Z)`, and that assumption is load-bearing for the identification, not a
convenience. `AlgebraicGeometry.FormalSpace.formalSchemeFppfPresheaf` sends an object `T` of the
big fppf site of `S` to `Mor_{Formal Schemes}(T, X)` — the morphisms out of the *underlying
scheme* of `T`, with no compatibility over `S`, because a formal scheme a la EGA carries no
morphism to `S` for them to be compatible with. The formal spectrum, on the other hand, is a
colimit of sheaves represented by objects of the big fppf site of `S`, whose sections over `T`
are morphisms *over* `S`. The two therefore differ as soon as an object of the site admits
morphisms to a quotient spectrum which do not commute with the structure morphisms, and they
agree when `S` is terminal among schemes, which is the source's `Spec (Z)`. Over a general base
the right left-hand side would be the functor of points of a formal scheme *over* `S`, which
this library does not define; the comparison morphism below is nevertheless well defined over
any base, because its legs only have to be morphisms of formal schemes.

*What the isomorphism rests on.* Granted a terminal base, the comparison
`AlgebraicGeometry.FormalSpace.spfFormalSchemeFppfComparison` is an isomorphism as soon as
`AlgebraicGeometry.spfQuotientPointsColimitMap` is locally bijective on the big fppf site. Both
of its ingredients are theorems and neither is assumed anywhere below: on the category of
all schemes the comparison map is locally bijective for the Zariski topology — local injectivity
is `AlgebraicGeometry.isLocallyInjective_spfQuotientPointsColimitMap` and local surjectivity is
`AlgebraicGeometry.isLocallySurjective_spfQuotientPointsColimitMap_of_isAdmissible`, which
discharges the affine case from the surjectivity half of Stacks 0AHZ — and the fppf sheaf
condition on `h_{Spf A}` is
`AlgebraicGeometry.FormalSpace.isFppfSheafFormalSchemePoints_formalScheme`, which is why no
declaration below carries it.

The change of site is `AlgebraicGeometry.BigFppfOver.isCocontinuous_toScheme_zariskiTopology`,
which is what `CategoryTheory.Presheaf.isLocallySurjective_whisker` and its injective companion
need; the repository had only the forward transports of the sheaf condition along
`AlgebraicGeometry.BigFppfOver.toScheme`
(`AlgebraicGeometry.BigFppfOver.coverPreserving_toScheme` and
`AlgebraicGeometry.BigFppfOver.compatiblePreserving_toScheme`). The colimit taken in
`AlgebraicGeometry.FormalSpace.FppfSheaf B S hS` is identified with the sheafification of the
colimit of the restricted presheaves because `CategoryTheory.Sheaf.sheafifiedYoneda` is
`CategoryTheory.uliftYoneda` followed by `CategoryTheory.presheafToSheaf`, a left adjoint. Both
steps are carried out in
`StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSchemeSpectrumComparisonIso`; the transport
below keeps the isomorphism as an argument because in that form it holds over *any* base, and
is therefore left untagged, the unconditional statement over a terminal base being
`AlgebraicGeometry.FormalSpace.isClassical_formalSchemePointsFppfSheaf`.

*What is still missing.* The last sentence of Stacks 0AIE, that Stacks 0AI1 yields an
*equivalence* between the category of affine formal schemes and the category of classical affine
formal algebraic spaces, is not proved anywhere. Beyond the identification above it needs the
two categories, the full faithfulness of the functor of points read on the big fppf site rather
than on all schemes — which is where `AlgebraicGeometry.IsSizeBoundedFormalScheme` enters, since
the site has a size cutoff — and essential surjectivity, which has to produce a quotient system
over `S` from `AlgebraicGeometry.FormalSpace.IsPresentingRing` together with the size conditions
`AlgebraicGeometry.FormalSpace.QuotientSystem.inSite` and
`AlgebraicGeometry.FormalSpace.QuotientSystem.HasLargeSite`.

## References

* [EGA I, Chapter I, Section 10]
* [Stacks Project, Tag 0AHZ](https://stacks.math.columbia.edu/tag/0AHZ)
* [Stacks Project, Tag 0AI1](https://stacks.math.columbia.edu/tag/0AI1)
* [Stacks Project, Tag 0AI2](https://stacks.math.columbia.edu/tag/0AI2)
* [Stacks Project, Tag 0AIC](https://stacks.math.columbia.edu/tag/0AIC)
* [Stacks Project, Tag 0AID](https://stacks.math.columbia.edu/tag/0AID)
* [Stacks Project, Tag 0AIE](https://stacks.math.columbia.edu/tag/0AIE)
* [Stacks Project, Tag 0AIF](https://stacks.math.columbia.edu/tag/0AIF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.FormalSpace

universe u

attribute [local instance] sheaf_hasColimits

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-! ### The index of Stacks 0AIE against the index of Stacks 0AIF -/

/-- The ideals of definition of `A` among its weak ideals of definition, both ordered by reverse
inclusion. An ideal of definition is a weak ideal of definition, and the order is inherited, so
this is an order embedding; what matters below is that it is cofinal. -/
def idealOfDefinitionIndex (A : Type u) [CommRing A] [TopologicalSpace A] :
    OrderDual (IdealsOfDefinition A) →o WeakIdeals A where
  toFun I := OrderDual.toDual
    ⟨(OrderDual.ofDual I).1,
      TopologicalRing.isWeakIdealOfDefinition_of_isIdealOfDefinition (OrderDual.ofDual I).2⟩
  monotone' _ _ h := h

omit [IsTopologicalRing A] in
/-- **Stacks 0AIE**, the index reconciliation. In a pre-admissible topological ring the ideals of
definition are cofinal below the weak ideals of definition — the intersection of a weak ideal of
definition with an ideal of definition is an ideal of definition — so the functor they induce on
index categories is final, and colimits may be computed over either index.

This is what reconciles the colimit of Stacks 0AIE, taken over the ideals of definition of an
admissible ring, with the formal spectrum of Stacks 0AIF, taken over the weak ideals of
definition. -/
@[stacks 0AIE "the ideals of definition are cofinal among the weak ideals of definition, so the \
colimit of the remark and the formal spectrum of Stacks 0AIF have the same index"]
theorem final_idealOfDefinitionIndex (hA : TopologicalRing.IsPreAdmissible A) :
    (idealOfDefinitionIndex A).monotone.functor.Final := by
  let : IsDirectedOrder (IdealsOfDefinition A)ᵒᵈ := ⟨fun I J ↦ by
    refine ⟨OrderDual.toDual ⟨(OrderDual.ofDual I).1 ⊓ (OrderDual.ofDual J).1,
      TopologicalRing.IsIdealOfDefinition.inf (OrderDual.ofDual I).2
        (OrderDual.ofDual J).2⟩, ?_, ?_⟩
    · exact show (OrderDual.ofDual I).1 ⊓ (OrderDual.ofDual J).1 ≤ (OrderDual.ofDual I).1 from
        inf_le_left
    · exact show (OrderDual.ofDual I).1 ⊓ (OrderDual.ofDual J).1 ≤ (OrderDual.ofDual J).1 from
        inf_le_right⟩
  refine (idealOfDefinitionIndex A).monotone.final_functor_iff.mpr fun J ↦ ?_
  obtain ⟨I, hI, hIJ⟩ :=
    TopologicalRing.exists_isIdealOfDefinition_le_of_isWeakIdealOfDefinition hA
      (OrderDual.ofDual J).2
  exact ⟨OrderDual.toDual ⟨I, hI⟩, hIJ⟩

variable [IsLinearTopology A A]

/-- The diagram of represented quotient spectra of a quotient system, restricted to the ideals of
definition of `A`. This is the diagram whose colimit Stacks 0AIE forms. -/
abbrev QuotientSystem.idealOfDefinitionDiagram (D : QuotientSystem B S hS A) :
    OrderDual (IdealsOfDefinition A) ⥤ FppfSheaf B S hS :=
  (idealOfDefinitionIndex A).monotone.functor ⋙ formalSpectrumDiagram D

/-- **Stacks 0AIE**, the colimit of the remark. The colimit of the represented quotient spectra
over the *ideals of definition* of a pre-admissible topological ring is the formal spectrum of
Stacks 0AIF, whose colimit runs over the *weak* ideals of definition. The two indices have the
same colimit by `AlgebraicGeometry.FormalSpace.final_idealOfDefinitionIndex`. -/
@[stacks 0AIE "the colimit over the ideals of definition is the formal spectrum of Stacks 0AIF"]
def QuotientSystem.formalSpectrumIsoIdealOfDefinitionColimit
    (hA : TopologicalRing.IsPreAdmissible A) (D : QuotientSystem B S hS A) :
    colimit D.idealOfDefinitionDiagram ≅ formalSpectrum D :=
  letI : (idealOfDefinitionIndex A).monotone.functor.Final := final_idealOfDefinitionIndex hA
  Functor.Final.colimitIso (idealOfDefinitionIndex A).monotone.functor
    (formalSpectrumDiagram D)

/-! ### The comparison morphism `Spf A ⟶ h_{Spf A}` -/

variable (hA : TopologicalRing.IsAdmissible A)

/-- The point of `h_{Spf A}` over the quotient spectrum `Spec (A ⧸ I)` of an ideal of
definition, as a section of the fppf sheaf of points of `Spf A` over the corresponding object of
the big fppf site of `S`.

It is the morphism `Spec (A ⧸ I) ⟶ Spf A` of Stacks 0AHY, read as a morphism of formal schemes
and lifted to `Type (u + 1)`. -/
def spfQuotientFppfSection (D : QuotientSystem B S hS A)
    (I : OrderDual (IdealsOfDefinition A)) :
    (formalSchemePointsFppfSheaf B S hS (spfFormalScheme A hA)).obj.obj
      (op ((BigAffineFppf.inclusion B S hS).obj
        (D.diagram.obj (idealOfDefinitionIndex A I)))) :=
  ULift.up ((spfQuotientCocone A hA).ι.app I)

/-- The cocone on the diagram of represented quotient spectra, indexed by the ideals of
definition, whose vertex is the fppf sheaf of points of the affine formal scheme `Spf A`. Its
legs are the quotient points of Stacks 0AHY, and its compatibility is theirs. -/
def spfQuotientFppfCocone (D : QuotientSystem B S hS A) :
    Cocone D.idealOfDefinitionDiagram where
  pt := formalSchemePointsFppfSheaf B S hS (spfFormalScheme A hA)
  ι :=
    { app := fun I ↦
        (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).symm
          (spfQuotientFppfSection hA D I)
      naturality := fun I I' f ↦ by
        let J := BigFppfOver.topology B S hS
        let i := (BigAffineFppf.inclusion B S hS).map
          (D.diagram.map ((idealOfDefinitionIndex A).monotone.functor.map f))
        change (Sheaf.sheafifiedYoneda J).map i ≫
            (Sheaf.sectionEquiv J).symm (spfQuotientFppfSection hA D I') =
          (Sheaf.sectionEquiv J).symm (spfQuotientFppfSection hA D I) ≫ 𝟙 _
        rw [Category.comp_id, ← Sheaf.sectionEquiv_symm_map]
        refine congrArg (Sheaf.sectionEquiv J).symm ?_
        change ULift.up ((spfQuotientDiagram A ⋙ schemeToFormalScheme).map f ≫
            (spfQuotientCocone A hA).ι.app I') = ULift.up ((spfQuotientCocone A hA).ι.app I)
        exact congrArg ULift.up ((spfQuotientCocone A hA).w f) }

/-- **The comparison morphism of Stacks 0AIE**, from the formal spectrum of `A` as an affine
formal algebraic space over `S` to the functor of points of `Spf A` as an affine formal scheme,
read on the big fppf site of `S`.

It is the morphism out of the colimit determined by the quotient points `Spec (A ⧸ I) ⟶ Spf A`
of Stacks 0AHY, transported along the index reconciliation
`AlgebraicGeometry.FormalSpace.QuotientSystem.formalSpectrumIsoIdealOfDefinitionColimit`. No
hypothesis beyond admissibility of `A` is used in its construction, the fppf sheaf condition on
`h_{Spf A}` being
`AlgebraicGeometry.FormalSpace.isFppfSheafFormalSchemePoints_formalScheme`; it is an
*isomorphism* over a terminal base, which is
`AlgebraicGeometry.FormalSpace.isIso_spfFormalSchemeFppfComparison`. -/
def spfFormalSchemeFppfComparison (D : QuotientSystem B S hS A) :
    formalSpectrum D ⟶ formalSchemePointsFppfSheaf B S hS (spfFormalScheme A hA) :=
  (D.formalSpectrumIsoIdealOfDefinitionColimit hA.1).inv ≫
    colimit.desc D.idealOfDefinitionDiagram (spfQuotientFppfCocone hA D)

/-- The comparison morphism restricted to a quotient stage is the quotient point of Stacks
0AHY. -/
theorem formalSpectrumIsoIdealOfDefinitionColimit_hom_comp_spfFormalSchemeFppfComparison
    (D : QuotientSystem B S hS A)
    (I : OrderDual (IdealsOfDefinition A)) :
    colimit.ι D.idealOfDefinitionDiagram I ≫
        (D.formalSpectrumIsoIdealOfDefinitionColimit hA.1).hom ≫
          spfFormalSchemeFppfComparison hA D =
      (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).symm
        (spfQuotientFppfSection hA D I) := by
  have h : (D.formalSpectrumIsoIdealOfDefinitionColimit hA.1).hom ≫
      spfFormalSchemeFppfComparison hA D =
        colimit.desc D.idealOfDefinitionDiagram (spfQuotientFppfCocone hA D) := by
    rw [spfFormalSchemeFppfComparison]
    exact Iso.hom_inv_id_assoc _ _
  rw [h]
  exact colimit.ι_desc (spfQuotientFppfCocone hA D) I

/-! ### Transport of classicality across the bridge -/

/-- **Stacks 0AIE, transported.** Let `A` be an admissible topological ring over `S` whose
quotient spectra, and their coproduct, lie in the chosen big fppf site. Granted the fppf sheaf
condition on the functor of points of the affine formal scheme `Spf A` and the identification of
that functor of points with the formal spectrum of `A` as an affine formal algebraic space, the
functor of points is a *classical* affine formal algebraic space over `S` in the sense of
Stacks 0AID (1).

This is the transport the bridge exists for, and it holds in both directions: the five types of
Stacks 0AID are invariant under isomorphism of fppf sheaves, so each of them may be read off
either side of the identification. The identification itself is the content of the first half of
Stacks 0AIE and is taken here as an argument, so that the statement holds over *any* base; over
a terminal base it is a theorem, and the resulting unconditional conclusion is
`AlgebraicGeometry.FormalSpace.isClassical_formalSchemePointsFppfSheaf`. This declaration is
therefore left untagged.
What is unconditional over any base is
`AlgebraicGeometry.FormalSpace.isClassical_formalSpectrum`, the same conclusion for the formal
spectrum itself. -/
theorem isClassical_formalSchemeFppfSheaf_of_iso_formalSpectrum (D : QuotientSystem B S hS A)
    (hB : D.HasLargeSite)
    (e : formalSpectrum D ≅ formalSchemePointsFppfSheaf B S hS (spfFormalScheme A hA)) :
    IsClassical B S hS (formalSchemePointsFppfSheaf B S hS (spfFormalScheme A hA)) :=
  isClassical_of_iso B S hS e (isClassical_formalSpectrum hA D hB)

/-- The converse transport: a formal spectrum identified with the functor of points of an affine
formal scheme inherits every property of that functor of points which is invariant under
isomorphism of fppf sheaves. Stated for classicality, the property Stacks 0AIE is about. -/
theorem isClassical_formalSpectrum_of_iso_formalSchemeFppfSheaf (D : QuotientSystem B S hS A)
    (e : formalSpectrum D ≅ formalSchemePointsFppfSheaf B S hS (spfFormalScheme A hA))
    (h : IsClassical B S hS (formalSchemePointsFppfSheaf B S hS (spfFormalScheme A hA))) :
    IsClassical B S hS (formalSpectrum D) :=
  isClassical_of_iso B S hS e.symm h

end AlgebraicGeometry.FormalSpace

end
