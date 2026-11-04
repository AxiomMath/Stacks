module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.AllTestObjects
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.TypeImplications
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.TypeImplicationsRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineCoproduct
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineCoproductTypes
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffinePullbackPresentation
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineSource
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineSourceTypes
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AtlasChartRefinement
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CoproductRepresentableEtale
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablePresentingRing
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablyIndexedCoproduct
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablyIndexedSurjectiveFlat
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteType
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalProperty
public import StacksFrontier.AlgebraicGeometry.FormalSpace.PrescribedCoverFiniteSubfamily
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableEtaleFiniteType
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Surjective
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautFaithfullyFlatPresentation
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Types
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedEtaleSiteMorphism
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
public import StacksFrontier.RingTheory.Flat.FaithfullyFlat.Descent
public import StacksFrontier.Topology.Algebra.AdicTopology.Descent
public import StacksFrontier.Topology.Algebra.AdicTopology.NoetherianNilradical

/-!
# Transfer of the types of affine formal algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`. The five types of affine formal
algebraic space of Stacks 0AIJ and Stacks 0AID — countably indexed, countably indexed and
classical, weakly adic, adic\* and Noetherian — descend along a morphism of affine formal
algebraic spaces representable by algebraic spaces (**Stacks 0AKQ**) and transfer in both
directions along such a morphism which is moreover surjective and flat (**Stacks 0AKS**,
**Stacks 0GXR**, **Stacks 0GXS**, **Stacks 0AKT** and **Stacks 0AKW**). Consequently, for a
formal algebraic space, one chart of an atlas as in Definition 0AIM having such a type is the
same as every affine formal algebraic space representable étale over it having it
(**Stacks 0AKX**).

## Main definitions

* `AlgebraicGeometry.FormalSpace.IsRepresentableAffine`: a morphism of fppf sheaves which is
  representable by schemes and affine, the conclusion of Stacks 0AKN and the hypothesis of the
  library's two parts of Stacks 0AKP.
* `AlgebraicGeometry.FormalSpace.IsRepresentableFlat`: a morphism of fppf sheaves which is
  representable by algebraic spaces and flat.
* `AlgebraicGeometry.FormalSpace.AffineRepresentableIsAffine`: the statement of
  **Stacks 0AKN**.
* `AlgebraicGeometry.FormalSpace.PropertyDescendsAlongRepresentableAffine` and
  `AlgebraicGeometry.FormalSpace.PropertyDescendsAlongRepresentableAffineOfFiniteType`:
  the shape of the clauses of **Stacks 0AKP** for the types other than countably indexed.
* `AlgebraicGeometry.FormalSpace.HasFaithfullyFlatQuotients`: the hypothesis shared by the
  ring-theoretic descent lemmas of Stacks 0GXL, 0GXM, 0GXP and 0GXQ.
* `AlgebraicGeometry.FormalSpace.HasTautFaithfullyFlatPresentation`: the passage from
  geometry to algebra used by the proofs of Stacks 0AKS, 0GXR, 0GXS, 0AKT and 0AKW.
* `AlgebraicGeometry.FormalSpace.HasCountablePresentingRing`: the dictionary between
  countable indexing and a countable fundamental system of open ideals of a presenting ring,
  proved by `AlgebraicGeometry.FormalSpace.hasCountablePresentingRing`.
* `AlgebraicGeometry.FormalSpace.HasAffineEtaleChartProperty`: condition (1) of
  **Stacks 0AKX**.
* `AlgebraicGeometry.FormalSpace.HasAffineEtaleRefinementWithProperty`: the refinement step in
  the proof of **Stacks 0AKX**, as a condition on a property.

## Main results

* `AlgebraicGeometry.FormalSpace.isCountablyIndexed_of_isRepresentable`,
  `AlgebraicGeometry.FormalSpace.isCountablyIndexedAndClassical_of_isRepresentable`,
  `AlgebraicGeometry.FormalSpace.isWeaklyAdic_of_isRepresentable`,
  `AlgebraicGeometry.FormalSpace.isAdicStar_of_isRepresentable` and
  `AlgebraicGeometry.FormalSpace.isNoetherian_of_isRepresentable`: the five clauses of
  **Stacks 0AKQ**.
* `AlgebraicGeometry.FormalSpace.isCountablyIndexed_iff_of_surjective_flat`: **Stacks 0AKS**.
* `AlgebraicGeometry.FormalSpace.isCountablyIndexedAndClassical_iff_of_surjective_flat`:
  **Stacks 0GXR**.
* `AlgebraicGeometry.FormalSpace.isWeaklyAdic_iff_of_surjective_flat`: **Stacks 0GXS**.
* `AlgebraicGeometry.FormalSpace.isAdicStar_iff_of_surjective_flat`: **Stacks 0AKT**.
* `AlgebraicGeometry.FormalSpace.isNoetherian_iff_of_surjective_flat`: **Stacks 0AKW**.
* `AlgebraicGeometry.FormalSpace.hasAffineEtaleChartProperty_iff_hasAffineEtaleAtlasWithProperty`:
  **Stacks 0AKX**.

## Implementation notes

The library's notions are used verbatim: `IsAffineFormalAlgebraicSpace` of Stacks 0AI7,
`IsCountablyIndexed` of Stacks 0AIJ in the form of
`StacksFrontier/AlgebraicGeometry/FormalSpace/CountablyIndexed.lean`, which is the one the four
other types and the atlas predicate of
`StacksFrontier/AlgebraicGeometry/FormalSpace/Types.lean` use, the four types `IsClassical`,
`IsWeaklyAdic`, `IsAdicStar` and `IsNoetherian` of Stacks 0AID, `IsSurjective` of
Stacks 0GHP, `IsLocallyOfFiniteType` of Stacks 0AM4, and
`Space.IsRepresentableByAlgebraicSpacesULift`.

Flatness of a morphism representable by algebraic spaces is spelled as
`IsRepresentableEtale` spells étaleness: representability together with flatness, in the
every-chart form of Stacks 03MJ which is the definition of `Space.IsFlat`, of every
represented base change. There is no `Space.IsFlatULift` abbreviation to reuse.

### The inputs

Every result here takes the source's hypotheses only.

**Stacks 0AKN** is the library's `relative_isAffineHom_of_isRepresentableByAlgebraicSpaces`.
Parts (1) to (6) of **Stacks 0AKP** are `isAffineFormalAlgebraicSpace_of_relative_isAffineHom`,
`isCountablyIndexed_of_relative_isAffineHom`,
`isCountablyIndexedAndClassical_of_relative_isAffineHom`, `isWeaklyAdic_of_relative_isAffineHom`,
`isAdicStar_of_relative_isAffineHom` and `isNoetherian_of_relative_isAffineHom`; together with
Stacks 0AKN they give the five clauses of Stacks 0AKQ.

The forward implications of Stacks 0AKS, 0GXR, 0GXS, 0AKT and 0AKW are, in the source, the
ring-theoretic descent lemmas of Stacks 0GXL, 0GXN, 0GXP and 0GXQ applied to the continuous
taut homomorphism of presenting rings that the morphism induces. That homomorphism, with its
faithfully flat maps of stages, is `exists_isTaut_faithfullyFlat_presentingRing_of_surjective_flat`,
which asks the source to be countably indexed. Countable indexing of the target is the source's
cofinality argument, `isCountablyIndexed_target_of_surjective_flat`. The descent steps are
`isPreAdmissible_of_isTaut_of_faithfullyFlat_quotient` (Stacks 0GXN),
`isWeaklyPreAdic_of_isTaut_of_faithfullyFlat_quotient` (Stacks 0GXP),
`exists_fg_ideal_of_definition_of_taut` (Stacks 0GXQ), and for Stacks 0AKW `descent_noetherian`
(Stacks 033E) and `noetherian_of_isAdicComplete_fg` (Stacks 05GH).

The predicates `AffineRepresentableIsAffine`, `PropertyDescendsAlongRepresentableAffine`,
`PropertyDescendsAlongRepresentableAffineOfFiniteType`, `HasTautFaithfullyFlatPresentation`,
`PreAdmissibleDescendsAlongTautFaithfullyFlat` and `NoetherianDescendsAlongTautFaithfullyFlat`
name those inputs; none of the results here takes them as a hypothesis.

Stacks 0AKX is stated as the equivalence of its two conditions for each of the five properties
of the source's list. The implication (1) ⟹ (2) is the atlas of Definition 0AIM. For (2) ⟹ (1)
the atlas is refined against a chart,
`exists_surjective_flat_over_chart_of_hasAffineEtaleAtlasWithProperty`: the fibre products of
the chart with the members of the atlas are covered by affine formal algebraic spaces
representable étale over both (Stacks 0AJ3), quasi-compactness of the chart cuts the family down
to a finite one, its members have the property by Stacks 0AKQ, and their disjoint union has it;
the property then passes to the chart along the surjective flat morphism from that disjoint
union by Stacks 0AKS, 0GXR, 0GXS, 0AKT or 0AKW. The same argument for a property given only the
refinement step and the transfer as hypotheses is
`hasAffineEtaleChartProperty_iff_of_refinement_of_transfer`.

## References

* [Stacks Project, Tag 033E](https://stacks.math.columbia.edu/tag/033E)
* [Stacks Project, Tag 0AIC](https://stacks.math.columbia.edu/tag/0AIC)
* [Stacks Project, Tag 0AID](https://stacks.math.columbia.edu/tag/0AID)
* [Stacks Project, Tag 0AIJ](https://stacks.math.columbia.edu/tag/0AIJ)
* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AJ2](https://stacks.math.columbia.edu/tag/0AJ2)
* [Stacks Project, Tag 0AJ3](https://stacks.math.columbia.edu/tag/0AJ3)
* [Stacks Project, Tag 0AKN](https://stacks.math.columbia.edu/tag/0AKN)
* [Stacks Project, Tag 0AKP](https://stacks.math.columbia.edu/tag/0AKP)
* [Stacks Project, Tag 0AKQ](https://stacks.math.columbia.edu/tag/0AKQ)
* [Stacks Project, Tag 0AKS](https://stacks.math.columbia.edu/tag/0AKS)
* [Stacks Project, Tag 0AKT](https://stacks.math.columbia.edu/tag/0AKT)
* [Stacks Project, Tag 0AKW](https://stacks.math.columbia.edu/tag/0AKW)
* [Stacks Project, Tag 0AKX](https://stacks.math.columbia.edu/tag/0AKX)
* [Stacks Project, Tag 0AMZ](https://stacks.math.columbia.edu/tag/0AMZ)
* [Stacks Project, Tag 0AN1](https://stacks.math.columbia.edu/tag/0AN1)
* [Stacks Project, Tag 0AN5](https://stacks.math.columbia.edu/tag/0AN5)
* [Stacks Project, Tag 05GH](https://stacks.math.columbia.edu/tag/05GH)
* [Stacks Project, Tag 0GXL](https://stacks.math.columbia.edu/tag/0GXL)
* [Stacks Project, Tag 0GXM](https://stacks.math.columbia.edu/tag/0GXM)
* [Stacks Project, Tag 0GXN](https://stacks.math.columbia.edu/tag/0GXN)
* [Stacks Project, Tag 0GXP](https://stacks.math.columbia.edu/tag/0GXP)
* [Stacks Project, Tag 0GXQ](https://stacks.math.columbia.edu/tag/0GXQ)
* [Stacks Project, Tag 0GXR](https://stacks.math.columbia.edu/tag/0GXR)
* [Stacks Project, Tag 0GXS](https://stacks.math.columbia.edu/tag/0GXS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe w u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A morphism of presheaves on the big fppf site of `S` which is étale in the sense of
**Stacks 03FR** and whose target is a universe-lifted Yoneda presheaf is flat on every étale
chart in the sense of **Stacks 03MJ**: in a commuting square of étale charts over a morphism `h`
of the site, the chart of the target and the composite of the chart of the source with the
morphism are both étale on schemes, so `h` is étale and a fortiori flat. -/
theorem flat_holdsOnEveryEtaleChartULift_of_isEtaleULift_of_uliftYoneda
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)} {T : BigFppfOver B S hS}
    (g : F ⟶ (uliftYoneda.{w}).obj T) (hg : IsEtaleULift.{w} B S hS g) :
    HoldsOnEveryEtaleChartULift.{w} B S hS
      (@AlgebraicGeometry.Flat.{u} : MorphismProperty Scheme.{u}) g := by
  intro U V a b h ha hb hsq
  obtain ⟨β, rfl⟩ : ∃ β : V ⟶ T, (uliftYoneda.{w}).map β = b :=
    ⟨(uliftYoneda.{w}).preimage b, by simp⟩
  have hβ : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map β) :=
    (relative_etale_uliftYoneda_map_iff B S hS β).mp hb
  have key : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{w})
        ((uliftYoneda.{w}).map (h ≫ β)) := by
    rw [Functor.map_comp, hsq]
    exact hg U a ha
  have hcomp : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map (h ≫ β)) :=
    (relative_etale_uliftYoneda_map_iff B S hS (h ≫ β)).mp key
  rw [Functor.map_comp] at hcomp
  have : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map h) :=
    MorphismProperty.of_postcomp (@AlgebraicGeometry.Etale.{u}) _ _ hβ hcomp
  infer_instance

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Representable affine and representable flat morphisms -/

/-- A morphism of fppf sheaves on the big fppf site of `S` is *representable affine* when it is
representable by schemes and the morphism of schemes underlying every represented base change
of it is affine. This is the conclusion of Stacks 0AKN and the hypothesis of the two parts of
Stacks 0AKP which this library carries. -/
abbrev IsRepresentableAffine {X Y : FppfSheaf B S hS} (f : X ⟶ Y) : Prop :=
  MorphismProperty.relative
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
    (MorphismProperty.inverseImage
      (@IsAffineHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) f

/-- A morphism of fppf sheaves on the big fppf site of `S` is *representable flat* when it is
representable by algebraic spaces and every represented base change of it is a flat morphism of
algebraic spaces, that is satisfies the every-chart condition of Stacks 03MJ for flatness of
morphisms of schemes. -/
abbrev IsRepresentableFlat {X Y : FppfSheaf B S hS} (f : X ⟶ Y) : Prop :=
  ∃ hf : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom,
    Space.HasPropertyULift.{u + 1} B S hS
      (fun _ _ g ↦ Space.HoldsOnEveryEtaleChartULift.{u + 1} B S hS
        (@AlgebraicGeometry.Flat.{u} : MorphismProperty Scheme.{u}) g.hom) f.hom hf

/-- A morphism of fppf sheaves on the big fppf site of `S` which is representable by algebraic
spaces and étale is representable flat: the morphism of algebraic spaces cut out by a
represented base change is étale, hence flat on every étale chart. -/
theorem isRepresentableFlat_of_isRepresentableEtale {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hf : IsRepresentableEtale B S hS f) :
    IsRepresentableFlat B S hS f := by
  obtain ⟨hrep, hetale⟩ := hf
  refine ⟨hrep, fun U ξ => ?_⟩
  change Space.HoldsOnEveryEtaleChartULift.{u + 1} B S hS
    (@AlgebraicGeometry.Flat.{u} : MorphismProperty Scheme.{u}) (pullback.fst ξ f.hom)
  exact Space.flat_holdsOnEveryEtaleChartULift_of_isEtaleULift_of_uliftYoneda B S hS
    (pullback.fst ξ f.hom) (hetale U ξ)

/-! ### The inputs this library does not carry -/

/-- **Stacks 0AKN**, which this library does not carry: a morphism of affine formal algebraic
spaces over `S` which is representable by algebraic spaces is representable by schemes and
affine. -/
def AffineRepresentableIsAffine : Prop :=
  ∀ {X Y : FppfSheaf B S hS} (f : X ⟶ Y),
    IsAffineFormalAlgebraicSpace B S hS X → IsAffineFormalAlgebraicSpace B S hS Y →
    Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom →
    IsRepresentableAffine B S hS f

/-- The shape of the clauses of **Stacks 0AKP** for the types other than countably indexed: a
property of affine formal algebraic spaces passes from the target of a representable affine
morphism of fppf sheaves to its source. -/
def PropertyDescendsAlongRepresentableAffine (P : FppfSheaf B S hS → Prop) : Prop :=
  ∀ {X Y : FppfSheaf B S hS} (f : X ⟶ Y), IsRepresentableAffine B S hS f →
    IsAffineFormalAlgebraicSpace B S hS X → IsAffineFormalAlgebraicSpace B S hS Y →
    P Y → P X

/-- The shape of clause (6) of **Stacks 0AKP**: a property of affine formal algebraic spaces
passes from the target of a representable affine morphism of fppf sheaves which is locally of
finite type to its source. -/
def PropertyDescendsAlongRepresentableAffineOfFiniteType (P : FppfSheaf B S hS → Prop) :
    Prop :=
  ∀ {X Y : FppfSheaf B S hS} (f : X ⟶ Y), IsRepresentableAffine B S hS f →
    IsLocallyOfFiniteType B S hS f →
    IsAffineFormalAlgebraicSpace B S hS X → IsAffineFormalAlgebraicSpace B S hS Y →
    P Y → P X

/-- The hypothesis shared by the ring-theoretic descent lemmas of Stacks 0GXL, 0GXM, 0GXP and
0GXQ: every map `A ⧸ I → C ⧸ closure (I C)` induced by `φ` on the quotient by an open ideal is
faithfully flat. -/
abbrev HasFaithfullyFlatQuotients {A C : Type u} [CommRing A] [TopologicalSpace A]
    [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] (φ : A →+* C) : Prop :=
  ∀ I : Ideal A, IsOpen (I : Set A) →
    (Ideal.quotientMap (Ideal.closure (I.map φ)) φ
      (Ideal.map_le_iff_le_comap.mp (fun _ hx ↦ subset_closure hx))).FaithfullyFlat

/-- The passage from geometry to algebra in the proofs of Stacks 0AKS, 0GXR, 0GXS, 0AKT and
0AKW, which this library does not carry: a surjective flat morphism of affine formal algebraic
spaces over `S` representable by algebraic spaces whose source is McQuillan with presenting
ring `C` has a McQuillan target with a presenting ring `A` admitting a continuous taut
homomorphism `A → C` all of whose maps on quotients by open ideals are faithfully flat. It
packages Stacks 0AKN, the implication (1) ⟹ (3) of Stacks 0AN5, the identification of
Stacks 0AMZ, and the translation of surjectivity and flatness into faithful flatness of the
induced maps of stages. -/
def HasTautFaithfullyFlatPresentation : Prop :=
  ∀ {X Y : FppfSheaf B S hS} (f : X ⟶ Y),
    IsAffineFormalAlgebraicSpace B S hS X → IsAffineFormalAlgebraicSpace B S hS Y →
    Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom →
    IsSurjective B S hS f → IsRepresentableFlat B S hS f →
    ∀ (C : Type u) (_ : CommRing C) (_ : TopologicalSpace C) (_ : IsTopologicalRing C)
      (_ : IsLinearTopology C C), IsPresentingRing B S hS C X →
    ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
      (_ : IsLinearTopology A A) (φ : A →+* C),
      HasSomeSurjectivePresentation B S hS Y ∧ IsPresentingRing B S hS A Y ∧
        Continuous φ ∧ RingHom.IsTaut φ ∧ HasFaithfullyFlatQuotients φ

/-- The dictionary between countable indexing of an affine formal algebraic space and a
countable fundamental system of open ideals of a presenting ring: the implication
(4) ⟹ (1) of Stacks 0AIC together with Stacks 0AN1, in the shape `IsPresentingRing` takes. It
is proved by `AlgebraicGeometry.FormalSpace.hasCountablePresentingRing` below, and so is a
hypothesis of nothing. -/
def HasCountablePresentingRing : Prop :=
  (∀ X : FppfSheaf B S hS, IsAffineFormalAlgebraicSpace B S hS X →
      IsCountablyIndexed B S hS X →
      ∃ (C : Type u) (_ : CommRing C) (_ : TopologicalSpace C) (_ : IsTopologicalRing C)
        (_ : IsLinearTopology C C), IsPresentingRing B S hS C X ∧
          (nhds (0 : C)).IsCountablyGenerated) ∧
    ∀ (X : FppfSheaf B S hS) (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
      (_ : IsTopologicalRing A) (_ : IsLinearTopology A A), IsPresentingRing B S hS A X →
      (nhds (0 : A)).IsCountablyGenerated → IsCountablyIndexed B S hS X

/-- **The dictionary between countable indexing and a countable presenting ring holds.** Both
halves are Stacks 0AN1 read through the weak-ideal colimit presentation of Stacks 0AIC; they
are `StacksFrontier/AlgebraicGeometry/FormalSpace/CountablePresentingRing.lean`. -/
theorem hasCountablePresentingRing : HasCountablePresentingRing B S hS :=
  ⟨exists_countable_isPresentingRing_of_isCountablyIndexed B S hS,
    fun X A instCR instTS instTR instLT hA hc ↦
      @isCountablyIndexed_of_isPresentingRing B S hS X A instCR instTS instTR instLT hA hc⟩

/-! ### Stacks 0AKQ -/

/-- **Stacks 0AKQ, clause (1).** Let `f : X ⟶ Y` be a morphism of affine formal algebraic
spaces over `S` which is representable by algebraic spaces. If `Y` is countably indexed then
so is `X`. -/
@[stacks 0AKQ "clause (1); Stacks 0AKN is the library's \
`relative_isAffineHom_of_isRepresentableByAlgebraicSpaces` and parts (1) and (2) of \
Stacks 0AKP are the library's `isAffineFormalAlgebraicSpace_of_relative_isAffineHom` and \
`isCountablyIndexed_of_relative_isAffineHom`"]
theorem isCountablyIndexed_of_isRepresentable {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsAffineFormalAlgebraicSpace B S hS X)
    (hY : IsAffineFormalAlgebraicSpace B S hS Y)
    (hf : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom)
    (hYc : IsCountablyIndexed B S hS Y) :
    IsCountablyIndexed B S hS X :=
  isCountablyIndexed_of_relative_isAffineHom B S hS f
    (relative_isAffineHom_of_isRepresentableByAlgebraicSpaces B S hS f hX hY hf) hYc

/-- **Stacks 0AKQ, clause (2).** Let `f : X ⟶ Y` be a morphism of affine formal algebraic
spaces over `S` which is representable by algebraic spaces. If `Y` is countably indexed and
classical then so is `X`. -/
@[stacks 0AKQ "clause (2); Stacks 0AKN is the library's \
`relative_isAffineHom_of_isRepresentableByAlgebraicSpaces` and clause (3) of Stacks 0AKP is \
the library's `isCountablyIndexedAndClassical_of_relative_isAffineHom`"]
theorem isCountablyIndexedAndClassical_of_isRepresentable {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsAffineFormalAlgebraicSpace B S hS X)
    (hY : IsAffineFormalAlgebraicSpace B S hS Y)
    (hf : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom)
    (hYc : IsCountablyIndexed B S hS Y ∧ IsClassical B S hS Y) :
    IsCountablyIndexed B S hS X ∧ IsClassical B S hS X :=
  isCountablyIndexedAndClassical_of_relative_isAffineHom B S hS f
    (relative_isAffineHom_of_isRepresentableByAlgebraicSpaces B S hS f hX hY hf) hYc

/-- **Stacks 0AKQ, clause (3).** Let `f : X ⟶ Y` be a morphism of affine formal algebraic
spaces over `S` which is representable by algebraic spaces. If `Y` is weakly adic then so is
`X`. -/
@[stacks 0AKQ "clause (3); Stacks 0AKN is the library's \
`relative_isAffineHom_of_isRepresentableByAlgebraicSpaces` and clause (4) of Stacks 0AKP is \
the library's `isWeaklyAdic_of_relative_isAffineHom`"]
theorem isWeaklyAdic_of_isRepresentable {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsAffineFormalAlgebraicSpace B S hS X)
    (hY : IsAffineFormalAlgebraicSpace B S hS Y)
    (hf : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom)
    (hYc : IsWeaklyAdic B S hS Y) :
    IsWeaklyAdic B S hS X :=
  isWeaklyAdic_of_relative_isAffineHom B S hS f
    (relative_isAffineHom_of_isRepresentableByAlgebraicSpaces B S hS f hX hY hf) hYc

/-- **Stacks 0AKQ, clause (4).** Let `f : X ⟶ Y` be a morphism of affine formal algebraic
spaces over `S` which is representable by algebraic spaces. If `Y` is adic\* then so is
`X`. -/
@[stacks 0AKQ "clause (4); Stacks 0AKN is the library's \
`relative_isAffineHom_of_isRepresentableByAlgebraicSpaces` and clause (5) of Stacks 0AKP is \
the library's `isAdicStar_of_relative_isAffineHom`"]
theorem isAdicStar_of_isRepresentable {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsAffineFormalAlgebraicSpace B S hS X)
    (hY : IsAffineFormalAlgebraicSpace B S hS Y)
    (hf : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom)
    (hYc : IsAdicStar B S hS Y) :
    IsAdicStar B S hS X :=
  isAdicStar_of_relative_isAffineHom B S hS f
    (relative_isAffineHom_of_isRepresentableByAlgebraicSpaces B S hS f hX hY hf) hYc

/-- **Stacks 0AKQ, clause (5).** Let `f : X ⟶ Y` be a morphism of affine formal algebraic
spaces over `S` which is representable by algebraic spaces and locally of finite type. If `Y`
is Noetherian then so is `X`. -/
@[stacks 0AKQ "clause (5); Stacks 0AKN is the library's \
`relative_isAffineHom_of_isRepresentableByAlgebraicSpaces` and clause (6) of Stacks 0AKP is \
the library's `isNoetherian_of_relative_isAffineHom`"]
theorem isNoetherian_of_isRepresentable {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsAffineFormalAlgebraicSpace B S hS X)
    (hY : IsAffineFormalAlgebraicSpace B S hS Y)
    (hf : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom)
    (hft : IsLocallyOfFiniteType B S hS f)
    (hYc : IsNoetherian B S hS Y) :
    IsNoetherian B S hS X :=
  isNoetherian_of_relative_isAffineHom B S hS f
    (relative_isAffineHom_of_isRepresentableByAlgebraicSpaces B S hS f hX hY hf) hft hYc

/-! ### Two more ring-theoretic inputs this library does not carry -/

/-- The pre-admissible case of **Stacks 0GXM**, which this library carries for weak
pre-admissibility only: having an ideal of definition descends along a continuous taut
homomorphism of linearly topologized rings all of whose maps on quotients by open ideals are
faithfully flat. -/
def PreAdmissibleDescendsAlongTautFaithfullyFlat : Prop :=
  ∀ (A C : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
    (_ : IsLinearTopology A A) (_ : CommRing C) (_ : TopologicalSpace C)
    (_ : IsTopologicalRing C) (_ : IsLinearTopology C C) (φ : A →+* C),
    Continuous φ → RingHom.IsTaut φ → HasFaithfullyFlatQuotients φ →
    TopologicalRing.IsPreAdmissible C → TopologicalRing.IsPreAdmissible A

/-- **Stacks 033E** read on a continuous taut homomorphism of adic topological rings, which
this library does not carry: the Noetherian property descends along such a homomorphism when
all its maps on quotients by open ideals are faithfully flat. -/
def NoetherianDescendsAlongTautFaithfullyFlat : Prop :=
  ∀ (A C : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
    (_ : IsLinearTopology A A) (_ : CommRing C) (_ : TopologicalSpace C)
    (_ : IsTopologicalRing C) (_ : IsLinearTopology C C) (φ : A →+* C),
    Continuous φ → RingHom.IsTaut φ → HasFaithfullyFlatQuotients φ →
    TopologicalRing.IsAdic A → IsNoetherianRing C → IsNoetherianRing A

/-! ### Ideals of definition of a pre-adic ring -/

/-- In a pre-adic topological ring every ideal of definition has its powers for a fundamental
system of neighbourhoods of zero: the powers of two ideals of definition are cofinal in each
other.

`StacksFrontier.AlgebraicGeometry.FormalSpace.NoetherianCharacterization` carries the same
conclusion under the additional assumption that the topology is linear; this form takes
pre-adicness alone, which is why it is stated separately here. -/
private theorem isAdic_of_isIdealOfDefinition_of_isPreAdic {R : Type u} [CommRing R]
    [TopologicalSpace R]
    [IsTopologicalRing R] (h : TopologicalRing.IsPreAdic R) {I : Ideal R}
    (hI : TopologicalRing.IsIdealOfDefinition I) : _root_.IsAdic I := by
  obtain ⟨K, _, hKadic⟩ := h
  obtain ⟨m, hm⟩ := (isAdic_iff.mp hKadic).2 (I : Set R) (hI.1.mem_nhds I.zero_mem)
  refine isAdic_iff.mpr ⟨fun n ↦ ?_, hI.2⟩
  refine Ideal.isOpen_of_isOpen_subideal (U := K ^ (m * n)) ?_
    ((isAdic_iff.mp hKadic).1 (m * n))
  rw [pow_mul]
  exact pow_le_pow_left' (show K ^ m ≤ I from fun _ hx ↦ hm hx) n

/-! ### Stacks 0AKS, 0GXR, 0GXS, 0AKT and 0AKW -/

/-- Adicness with a finitely generated ideal of definition descends from a complete ring `C` to a
complete ring `A` along a continuous taut homomorphism with faithfully flat quotient maps. -/
private theorem exists_fg_isAdic_of_taut {A C : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A] [CommRing C] [TopologicalSpace C]
    [IsTopologicalRing C] [IsLinearTopology C C] (φ : A →+* C) (hφcont : Continuous φ)
    (hφtaut : RingHom.IsTaut φ) (hφquot : HasFaithfullyFlatQuotients φ)
    (hA : TopologicalRing.IsComplete A) (hC : TopologicalRing.IsComplete C) {I : Ideal C}
    (hI : _root_.IsAdic I) (hIfg : I.FG) :
    ∃ J : Ideal A, _root_.IsAdic J ∧ J.FG ∧ TopologicalRing.IsAdic A := by
  let : T2Space A := hA.1
  let : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A) := hA.2
  let : T2Space C := hC.1
  let : @CompleteSpace C (IsTopologicalAddGroup.rightUniformSpace C) := hC.2
  obtain ⟨J, hJadic, hJfg⟩ :=
    TopologicalRing.exists_fg_ideal_of_definition_of_taut φ hφcont hφtaut hφquot ⟨I, hI, hIfg⟩
  exact ⟨J, hJadic, hJfg,
    ⟨J, TopologicalRing.isIdealOfDefinition_of_isAdic hJadic, hJadic⟩, hA⟩

/-- **Stacks 0AKS.** Let `f : X ⟶ Y` be a morphism of affine formal algebraic spaces over `S`
which is representable by algebraic spaces, surjective and flat. Then `X` is countably indexed
if and only if `Y` is. -/
@[stacks 0AKS "the equivalence, at the source's own hypotheses. The forward implication is \
the source's cofinality argument, `isCountablyIndexed_target_of_surjective_flat`, which rests \
on Stacks 0AIA, on Stacks 0AKN — the library's \
`relative_isAffineHom_of_isRepresentableByAlgebraicSpaces` — and on faithful flatness of a \
represented base change; the reverse implication is part (2) of Stacks 0AKP, the library's \
`isCountablyIndexed_of_relative_isAffineHom`"]
theorem isCountablyIndexed_iff_of_surjective_flat {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsAffineFormalAlgebraicSpace B S hS X)
    (hY : IsAffineFormalAlgebraicSpace B S hS Y)
    (hf : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom)
    (hsurj : IsSurjective B S hS f) (hflat : IsRepresentableFlat B S hS f) :
    IsCountablyIndexed B S hS X ↔ IsCountablyIndexed B S hS Y := by
  refine ⟨fun hXc ↦ ?_, isCountablyIndexed_of_relative_isAffineHom B S hS f
    (relative_isAffineHom_of_isRepresentableByAlgebraicSpaces B S hS f hX hY hf)⟩
  obtain ⟨hrep, hflat'⟩ := hflat
  exact isCountablyIndexed_target_of_surjective_flat B S hS f hX hY hrep hsurj hflat' hXc

/-- **Stacks 0GXR.** Let `f : X ⟶ Y` be a morphism of affine formal algebraic spaces over `S`
which is representable by algebraic spaces, surjective and flat. Then `X` is countably indexed
and classical if and only if `Y` is. -/
@[stacks 0GXR "the equivalence, at the source's own hypotheses. Stacks 0AKN is the library's \
`relative_isAffineHom_of_isRepresentableByAlgebraicSpaces`; the countably indexed half of the \
forward implication is `isCountablyIndexed_target_of_surjective_flat`, the presenting ring of \
the target with its continuous taut homomorphism to that of the source is \
`exists_isTaut_faithfullyFlat_presentingRing_of_surjective_flat`, and pre-admissibility \
descends along it by Stacks 0GXN; the reverse implication is clause (3) of Stacks 0AKP, the \
library's `isCountablyIndexedAndClassical_of_relative_isAffineHom`"]
theorem isCountablyIndexedAndClassical_iff_of_surjective_flat {X Y : FppfSheaf B S hS}
    (f : X ⟶ Y)
    (hX : IsAffineFormalAlgebraicSpace B S hS X)
    (hY : IsAffineFormalAlgebraicSpace B S hS Y)
    (hf : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom)
    (hsurj : IsSurjective B S hS f) (hflat : IsRepresentableFlat B S hS f) :
    IsCountablyIndexed B S hS X ∧ IsClassical B S hS X ↔
      IsCountablyIndexed B S hS Y ∧ IsClassical B S hS Y := by
  refine ⟨fun hXc ↦ ?_, isCountablyIndexedAndClassical_of_relative_isAffineHom B S hS f
    (relative_isAffineHom_of_isRepresentableByAlgebraicSpaces B S hS f hX hY hf)⟩
  obtain ⟨hrep, hflat'⟩ := hflat
  obtain ⟨hXci, -, C, hCR, hCT, hCTR, hCLT, hCpres, hCadm⟩ := hXc
  obtain ⟨A, hAR, hAT, hATR, hALT, φ, hYmcq, hApres, hφcont, hφtaut, hφquot⟩ :=
    exists_isTaut_faithfullyFlat_presentingRing_of_surjective_flat B S hS f hX hY hrep hsurj
      hflat' hXci C hCR hCT hCTR hCLT hCpres
  exact ⟨isCountablyIndexed_target_of_surjective_flat B S hS f hX hY hrep hsurj hflat' hXci,
    hYmcq, A, hAR, hAT, hATR, hALT, hApres,
    TopologicalRing.isPreAdmissible_of_isTaut_of_faithfullyFlat_quotient φ hφcont hφtaut hφquot
      hCadm.1, hApres.1.2.2, hApres.1.2.1⟩

/-- **Stacks 0GXS.** Let `f : X ⟶ Y` be a morphism of affine formal algebraic spaces over `S`
which is representable by algebraic spaces, surjective and flat. Then `X` is weakly adic if
and only if `Y` is. -/
@[stacks 0GXS "the equivalence, at the source's own hypotheses. Stacks 0AKN is the library's \
`relative_isAffineHom_of_isRepresentableByAlgebraicSpaces`; the presenting ring of the target \
with its continuous taut homomorphism to that of the source is \
`exists_isTaut_faithfullyFlat_presentingRing_of_surjective_flat`, which takes countable \
indexing of the source from item (5) of Stacks 0AIK. The forward implication is the library's \
Stacks 0GXP and the reverse one is clause (4) of Stacks 0AKP, the library's \
`isWeaklyAdic_of_relative_isAffineHom`"]
theorem isWeaklyAdic_iff_of_surjective_flat {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsAffineFormalAlgebraicSpace B S hS X)
    (hY : IsAffineFormalAlgebraicSpace B S hS Y)
    (hf : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom)
    (hsurj : IsSurjective B S hS f) (hflat : IsRepresentableFlat B S hS f) :
    IsWeaklyAdic B S hS X ↔ IsWeaklyAdic B S hS Y := by
  refine ⟨fun hXc ↦ ?_, isWeaklyAdic_of_relative_isAffineHom B S hS f
    (relative_isAffineHom_of_isRepresentableByAlgebraicSpaces B S hS f hX hY hf)⟩
  obtain ⟨hrep, hflat'⟩ := hflat
  have hXci : IsCountablyIndexed B S hS X := isCountablyIndexed_of_isWeaklyAdic B S hS hXc
  obtain ⟨-, C, hCR, hCT, hCTR, hCLT, hCpres, hCadic⟩ := hXc
  obtain ⟨A, hAR, hAT, hATR, hALT, φ, hYmcq, hApres, hφcont, hφtaut, hφquot⟩ :=
    exists_isTaut_faithfullyFlat_presentingRing_of_surjective_flat B S hS f hX hY hrep hsurj
      hflat' hXci C hCR hCT hCTR hCLT hCpres
  let : TopologicalRing.IsWeaklyAdic C := hCadic
  let : TopologicalRing.IsWeaklyPreAdic A :=
    TopologicalRing.isWeaklyPreAdic_of_isTaut_of_faithfullyFlat_quotient φ hφcont hφtaut
      hφquot inferInstance
  let : T2Space A := hApres.1.2.2
  exact ⟨hYmcq, A, hAR, hAT, hATR, hALT, hApres, { completeSpace := hApres.1.2.1 }⟩

/-- **Stacks 0AKT.** Let `f : X ⟶ Y` be a morphism of affine formal algebraic spaces over `S`
which is representable by algebraic spaces, surjective and flat. Then `X` is adic\* if and
only if `Y` is. -/
@[stacks 0AKT "the equivalence, at the source's own hypotheses. The presenting ring of the \
target with its continuous taut homomorphism to that of the source is \
`exists_isTaut_faithfullyFlat_presentingRing_of_surjective_flat`, which takes countable \
indexing of the source from items (2), (3) and (5) of Stacks 0AIK; Stacks 0AKN is the \
library's `relative_isAffineHom_of_isRepresentableByAlgebraicSpaces`. The forward \
implication is the library's Stacks 0GXQ and the reverse one is clause (5) of Stacks 0AKP, \
the library's `isAdicStar_of_relative_isAffineHom`"]
theorem isAdicStar_iff_of_surjective_flat {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsAffineFormalAlgebraicSpace B S hS X)
    (hY : IsAffineFormalAlgebraicSpace B S hS Y)
    (hf : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom)
    (hsurj : IsSurjective B S hS f) (hflat : IsRepresentableFlat B S hS f) :
    IsAdicStar B S hS X ↔ IsAdicStar B S hS Y := by
  refine ⟨fun hXc ↦ ?_, isAdicStar_of_relative_isAffineHom B S hS f
    (relative_isAffineHom_of_isRepresentableByAlgebraicSpaces B S hS f hX hY hf)⟩
  obtain ⟨hrep, hflat'⟩ := hflat
  have hXci : IsCountablyIndexed B S hS X :=
    isCountablyIndexed_of_isWeaklyAdic B S hS (isWeaklyAdic_of_isAdic B S hS
      (isAdic_of_isAdicStar B S hS hXc))
  obtain ⟨-, C, hCR, hCT, hCTR, hCLT, hCpres, hCadic, I, hI, hIfg⟩ := hXc
  obtain ⟨A, hAR, hAT, hATR, hALT, φ, hYmcq, hApres, hφcont, hφtaut, hφquot⟩ :=
    exists_isTaut_faithfullyFlat_presentingRing_of_surjective_flat B S hS f hX hY hrep hsurj
      hflat' hXci C hCR hCT hCTR hCLT hCpres
  obtain ⟨J, hJadic, hJfg, hAadic⟩ := exists_fg_isAdic_of_taut φ hφcont hφtaut hφquot
    ⟨hApres.1.2.2, hApres.1.2.1⟩ hCadic.2
    (isAdic_of_isIdealOfDefinition_of_isPreAdic hCadic.1 hI) hIfg
  exact ⟨hYmcq, A, hAR, hAT, hATR, hALT, hApres, hAadic, J,
    TopologicalRing.isIdealOfDefinition_of_isAdic hJadic, hJfg⟩

/-- **Stacks 0AKW.** Let `f : X ⟶ Y` be a morphism of affine formal algebraic spaces over `S`
which is representable by algebraic spaces, surjective, flat and locally of finite type. Then
`X` is Noetherian if and only if `Y` is. -/
@[stacks 0AKW "the equivalence, at the source's own hypotheses. The presenting ring of the \
target with its continuous taut homomorphism to that of the source is \
`exists_isTaut_faithfullyFlat_presentingRing_of_surjective_flat`; its finitely generated \
ideal of definition is the library's Stacks 0GXQ, the descent of the Noetherian property to \
the quotient by it is Stacks 033E, `descent_noetherian`, and the passage to the complete ring \
is Stacks 05GH, `noetherian_of_isAdicComplete_fg`; Stacks 0AKN is the library's \
`relative_isAffineHom_of_isRepresentableByAlgebraicSpaces`. The reverse implication is \
clause (6) of Stacks 0AKP, the library's `isNoetherian_of_relative_isAffineHom`"]
theorem isNoetherian_iff_of_surjective_flat {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsAffineFormalAlgebraicSpace B S hS X)
    (hY : IsAffineFormalAlgebraicSpace B S hS Y)
    (hf : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom)
    (hsurj : IsSurjective B S hS f) (hflat : IsRepresentableFlat B S hS f)
    (hft : IsLocallyOfFiniteType B S hS f) :
    IsNoetherian B S hS X ↔ IsNoetherian B S hS Y := by
  refine ⟨fun hXc ↦ ?_, isNoetherian_of_relative_isAffineHom B S hS f
    (relative_isAffineHom_of_isRepresentableByAlgebraicSpaces B S hS f hX hY hf) hft⟩
  obtain ⟨hrep, hflat'⟩ := hflat
  have hXci : IsCountablyIndexed B S hS X := isCountablyIndexed_of_isNoetherian B S hS hXc
  obtain ⟨-, C, hCR, hCT, hCTR, hCLT, hCpres, hCnoeth, hCadic⟩ := hXc
  obtain ⟨A, hAR, hAT, hATR, hALT, φ, hYmcq, hApres, hφcont, hφtaut, hφquot⟩ :=
    exists_isTaut_faithfullyFlat_presentingRing_of_surjective_flat B S hS f hX hY hrep hsurj
      hflat' hXci C hCR hCT hCTR hCLT hCpres
  obtain ⟨K, -, hKadic⟩ := hCadic.1
  obtain ⟨J, hJadic, hJfg, hAadic⟩ := exists_fg_isAdic_of_taut φ hφcont hφtaut hφquot
    ⟨hApres.1.2.2, hApres.1.2.1⟩ hCadic.2 hKadic (IsNoetherian.noetherian K)
  let : T2Space A := hApres.1.2.2
  let : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A) := hApres.1.2.1
  have hJopen : IsOpen (J : Set A) := by simpa using (isAdic_iff.mp hJadic).1 1
  have hquot : IsNoetherianRing (A ⧸ J) := descent_noetherian _ (hφquot J hJopen) inferInstance
  let : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  let : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  have : IsAdicComplete J A := hJadic.isAdicComplete_iff.mpr ⟨inferInstance, inferInstance⟩
  exact ⟨hYmcq, A, hAR, hAT, hATR, hALT, hApres,
    noetherian_of_isAdicComplete_fg A J hJfg inferInstance hquot, hAadic⟩

/-! ### Stacks 0AKX -/

/-- **Stacks 0AKX, condition (1).** An fppf sheaf on the big fppf site of `S` *has the chart
property `P`* when every affine formal algebraic space over `S` mapping to it by a morphism
representable by algebraic spaces and étale satisfies `P`. -/
abbrev HasAffineEtaleChartProperty (X : FppfSheaf B S hS) (P : FppfSheaf B S hS → Prop) :
    Prop :=
  ∀ (Y : FppfSheaf B S hS) (g : Y ⟶ X), IsAffineFormalAlgebraicSpace B S hS Y →
    IsRepresentableEtale B S hS g → P Y

/-- The refinement step in the proof of **Stacks 0AKX**, which this library does not carry:
given an atlas of `X` as in Definition 0AIM all of whose members satisfy `P`, every affine
formal algebraic space `Y` representable étale over `X` receives a surjective flat morphism,
locally of finite type and representable by algebraic spaces, from an affine formal algebraic
space satisfying `P`. It packages Stacks 0AJ2 for the fibre products of the members of the
atlas with `Y`, the coverings of Definition 0AIM refining those fibre products,
quasi-compactness of `Y` cutting the resulting family down to a finite one, Stacks 0AKQ along
the étale maps to the members of the atlas, and the fact that a finite disjoint union of
affine formal algebraic spaces satisfying `P` again satisfies `P`. -/
def HasAffineEtaleRefinementWithProperty (P : FppfSheaf B S hS → Prop) : Prop :=
  letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  ∀ {X : FppfSheaf B S hS} (I : Type (u + 1)) (Xi : I → FppfSheaf B S hS)
      (fi : ∀ i, Xi i ⟶ X), (∀ i, IsAffineFormalAlgebraicSpace B S hS (Xi i)) →
      (∀ i, IsRepresentableEtale B S hS (fi i)) →
      Sheaf.IsLocallySurjective (Sigma.desc fi) → (∀ i, P (Xi i)) →
    ∀ (Y : FppfSheaf B S hS) (g : Y ⟶ X), IsAffineFormalAlgebraicSpace B S hS Y →
      IsRepresentableEtale B S hS g →
      ∃ (W : FppfSheaf B S hS) (w : W ⟶ Y), IsAffineFormalAlgebraicSpace B S hS W ∧ P W ∧
        Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS w.hom ∧
        IsSurjective B S hS w ∧ IsRepresentableFlat B S hS w ∧
        IsLocallyOfFiniteType B S hS w

/-- The chart property implies the atlas property: the atlas of Definition 0AIM carried by `hX`
consists of affine formal algebraic spaces representable étale over `X`. -/
private theorem hasAffineEtaleAtlasWithProperty_of_hasAffineEtaleChartProperty
    {X : FppfSheaf B S hS} {P : FppfSheaf B S hS → Prop} (hX : IsFormalAlgebraicSpace B S hS X)
    (h : HasAffineEtaleChartProperty B S hS X P) : HasAffineEtaleAtlasWithProperty B S hS X P := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  obtain ⟨-, I, Xi, fi, hXiaff, hXiet, hXisurj⟩ := hX
  exact ⟨I, Xi, fi, hXiaff, hXiet, hXisurj, fun i ↦ h (Xi i) (fi i) (hXiaff i) (hXiet i)⟩

/-- The equivalence of the two conditions of Stacks 0AKX for a property `P` given the refinement
step `href` of the proof, `HasAffineEtaleRefinementWithProperty`, and the transfer `htransfer` of
`P` along a surjective flat morphism representable by algebraic spaces and locally of finite
type. The implication (1) ⟹ (2) is the atlas of Definition 0AIM carried by `hX`. -/
theorem hasAffineEtaleChartProperty_iff_of_refinement_of_transfer
    (X : FppfSheaf B S hS) (P : FppfSheaf B S hS → Prop)
    (hX : IsFormalAlgebraicSpace B S hS X)
    (href : HasAffineEtaleRefinementWithProperty B S hS P)
    (htransfer : ∀ {W Z : FppfSheaf B S hS} (w : W ⟶ Z),
      IsAffineFormalAlgebraicSpace B S hS W → IsAffineFormalAlgebraicSpace B S hS Z →
      Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS w.hom →
      IsSurjective B S hS w → IsRepresentableFlat B S hS w →
      IsLocallyOfFiniteType B S hS w → (P W ↔ P Z)) :
    HasAffineEtaleChartProperty B S hS X P ↔
      HasAffineEtaleAtlasWithProperty B S hS X P := by
  refine ⟨hasAffineEtaleAtlasWithProperty_of_hasAffineEtaleChartProperty B S hS hX, fun h ↦ ?_⟩
  obtain ⟨J, Zj, gj, hZjaff, hZjet, hZjsurj, hZjP⟩ := h
  intro Y g hY hg
  obtain ⟨W, w, hWaff, hWP, hwrep, hwsurj, hwflat, hwft⟩ :=
    href J Zj gj hZjaff hZjet hZjsurj hZjP Y g hY hg
  exact (htransfer w hWaff hY hwrep hwsurj hwflat hwft).1 hWP

/-- **The refinement step in the proof of Stacks 0AKX.** Let `X` be a formal algebraic space over
`S` with an atlas as in Definition 0AIM all of whose members have a property `P` which descends
along representable étale morphisms of affine formal algebraic spaces and passes to finite
disjoint unions of affine formal algebraic spaces. Then every affine formal algebraic space `Y`
representable étale over `X` receives a morphism `W ⟶ Y` from an affine formal algebraic space
with `P`, which is representable by algebraic spaces, surjective, flat and locally of finite
type.

The atlas refined against `Y` is a jointly surjective family of affine formal algebraic spaces
representable étale over `Y` and over members of the atlas, so having `P`; quasi-compactness of
`Y` cuts it down to a finite subfamily, and `W` is its disjoint union. -/
theorem exists_surjective_flat_over_chart_of_hasAffineEtaleAtlasWithProperty
    (P : FppfSheaf B S hS → Prop)
    (hdesc : ∀ {U V : FppfSheaf B S hS} (v : U ⟶ V), IsAffineFormalAlgebraicSpace B S hS U →
      IsAffineFormalAlgebraicSpace B S hS V → IsRepresentableEtale B S hS v → P V → P U)
    (hsigma : ∀ {I : Type (u + 1)} [Finite I] (Z : I → FppfSheaf B S hS),
      (∀ i, IsAffineFormalAlgebraicSpace B S hS (Z i)) → (∀ i, P (Z i)) →
        letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
          Sheaf.instHasColimitsOfSize
        P (∐ Z))
    {X : FppfSheaf B S hS} (hX : IsFormalAlgebraicSpace B S hS X)
    (hatlas : HasAffineEtaleAtlasWithProperty B S hS X P)
    {Y : FppfSheaf B S hS} (g : Y ⟶ X)
    (hY : IsAffineFormalAlgebraicSpace B S hS Y) (hg : IsRepresentableEtale B S hS g) :
    ∃ (W : FppfSheaf B S hS) (w : W ⟶ Y), IsAffineFormalAlgebraicSpace B S hS W ∧ P W ∧
      Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS w.hom ∧
      IsSurjective B S hS w ∧ IsRepresentableFlat B S hS w ∧
      IsLocallyOfFiniteType B S hS w := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  obtain ⟨I, Xi, fi, hXiaff, hXiet, hXicov, hXiP⟩ := hatlas
  -- the atlas refined against the chart, every member having `P` by descent
  obtain ⟨K, U, w, κ, v, hUaff, hUet, hVet, hcov⟩ :=
    exists_affineEtaleFamily_over_chart_of_atlas B S hS hX Xi fi hXiaff hXiet hXicov g hY hg
  have hUP : ∀ k, P (U k) := fun k ↦ hdesc (v k) (hUaff k) (hXiaff (κ k)) (hVet k) (hXiP (κ k))
  -- quasi-compactness of `Y` cuts it down to a finite subfamily
  obtain ⟨σ, hσ, k, hsub⟩ :=
    exists_finite_subfamily_isAffineEtaleCover_of_isAffineFormalAlgebraicSpace B S hS hY U w
      ⟨hUaff, hUet, hcov⟩
  let : Finite σ := hσ
  obtain ⟨hsubaff, hsubet, hsubcov⟩ := hsub
  -- the disjoint union of the finite subfamily
  have hWet : IsRepresentableEtale B S hS (Sigma.desc fun s ↦ w (k s)) :=
    coproductsRepresentableEtale B S hS σ (fun s ↦ U (k s)) Y (fun s ↦ w (k s)) hσ hsubet
  exact ⟨∐ fun s ↦ U (k s), Sigma.desc fun s ↦ w (k s),
    isAffineFormalAlgebraicSpace_sigma B S hS _ hsubaff,
    hsigma _ hsubaff fun s ↦ hUP (k s),
    hWet.1, isSurjective_of_isLocallySurjective B S hS hsubcov,
    isRepresentableFlat_of_isRepresentableEtale B S hS _ hWet,
    IsLocallyOfFiniteType.of_isRepresentableEtale B S hS _ hWet⟩

/-- The equivalence of the two conditions of Stacks 0AKX for a property `P` which descends along
representable étale morphisms of affine formal algebraic spaces, passes to finite disjoint
unions of affine formal algebraic spaces, and ascends along surjective flat morphisms of affine
formal algebraic spaces which are representable by algebraic spaces and locally of finite type.
Each of the five properties of the source's list satisfies the three conditions; see
`hasAffineEtaleChartProperty_iff_hasAffineEtaleAtlasWithProperty`. -/
theorem hasAffineEtaleChartProperty_iff_of_descends_of_ascends
    (X : FppfSheaf B S hS) (hX : IsFormalAlgebraicSpace B S hS X) (P : FppfSheaf B S hS → Prop)
    (hdesc : ∀ {U V : FppfSheaf B S hS} (v : U ⟶ V), IsAffineFormalAlgebraicSpace B S hS U →
      IsAffineFormalAlgebraicSpace B S hS V → IsRepresentableEtale B S hS v → P V → P U)
    (hsigma : ∀ {I : Type (u + 1)} [Finite I] (Z : I → FppfSheaf B S hS),
      (∀ i, IsAffineFormalAlgebraicSpace B S hS (Z i)) → (∀ i, P (Z i)) →
        letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
          Sheaf.instHasColimitsOfSize
        P (∐ Z))
    (hasc : ∀ {W Z : FppfSheaf B S hS} (w : W ⟶ Z),
      IsAffineFormalAlgebraicSpace B S hS W → IsAffineFormalAlgebraicSpace B S hS Z →
      Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS w.hom →
      IsSurjective B S hS w → IsRepresentableFlat B S hS w →
      IsLocallyOfFiniteType B S hS w → P W → P Z) :
    HasAffineEtaleChartProperty B S hS X P ↔ HasAffineEtaleAtlasWithProperty B S hS X P := by
  refine ⟨hasAffineEtaleAtlasWithProperty_of_hasAffineEtaleChartProperty B S hS hX,
    fun hatlas Y g hY hg ↦ ?_⟩
  obtain ⟨W, w, hWaff, hWP, hwrep, hwsurj, hwflat, hwft⟩ :=
    exists_surjective_flat_over_chart_of_hasAffineEtaleAtlasWithProperty B S hS P hdesc hsigma hX
      hatlas g hY hg
  exact hasc w hWaff hY hwrep hwsurj hwflat hwft hWP

/-- **Stacks 0AKX.** Let `X` be a formal algebraic space over `S` and let `P` be one of the
properties of affine formal algebraic spaces *countably indexed*, *countably indexed and
classical*, *weakly adic*, *adic\** and *Noetherian*. The following are equivalent:

1. if `Y` is an affine formal algebraic space and `Y ⟶ X` is representable by algebraic spaces
   and étale, then `Y` has property `P`;
2. for some covering `{Xᵢ ⟶ X}` as in Definition 0AIM each `Xᵢ` has property `P`.

For (2) ⟹ (1) the atlas is refined against the chart and cut down to a finite subfamily by
quasi-compactness; its members have `P` by Stacks 0AKQ, their disjoint union has `P`, and `P`
passes to the chart along the surjective flat morphism from that disjoint union by Stacks 0AKS,
0GXR, 0GXS, 0AKT or 0AKW. -/
@[stacks 0AKX "the equivalence of conditions (1) and (2), at the source's own hypotheses and \
for each of the five properties of its list. For (2) ⟹ (1) the refinement of the atlas against \
a chart is `exists_surjective_flat_over_chart_of_hasAffineEtaleAtlasWithProperty`: Stacks 0AJ3 \
for the fibre products, the coverings of Definition 0AIM, quasi-compactness of the chart, \
Stacks 0AKQ along the étale maps and the finite disjoint union of the members; the property \
then passes to the chart by Stacks 0AKS, 0GXR, 0GXS, 0AKT or 0AKW"]
theorem hasAffineEtaleChartProperty_iff_hasAffineEtaleAtlasWithProperty
    (X : FppfSheaf B S hS) (hX : IsFormalAlgebraicSpace B S hS X) (P : FppfSheaf B S hS → Prop)
    (hP : P = IsCountablyIndexed B S hS ∨
      P = (fun Z ↦ IsCountablyIndexed B S hS Z ∧ IsClassical B S hS Z) ∨
      P = IsWeaklyAdic B S hS ∨ P = IsAdicStar B S hS ∨ P = IsNoetherian B S hS) :
    HasAffineEtaleChartProperty B S hS X P ↔ HasAffineEtaleAtlasWithProperty B S hS X P := by
  rcases hP with rfl | rfl | rfl | rfl | rfl
  · exact hasAffineEtaleChartProperty_iff_of_descends_of_ascends B S hS X hX _
      (fun v hU hV hv hVP ↦ isCountablyIndexed_of_isRepresentable B S hS v hU hV hv.1 hVP)
      (fun Z _ hZP ↦ isCountablyIndexed_sigma B S hS Z hZP)
      (fun w hW hZ hw hsurj hflat _ hWP ↦
        (isCountablyIndexed_iff_of_surjective_flat B S hS w hW hZ hw hsurj hflat).1 hWP)
  · exact hasAffineEtaleChartProperty_iff_of_descends_of_ascends B S hS X hX _
      (fun v hU hV hv hVP ↦
        isCountablyIndexedAndClassical_of_isRepresentable B S hS v hU hV hv.1 hVP)
      (fun Z hZaff hZP ↦ isCountablyIndexedAndClassical_sigma B S hS Z hZaff hZP)
      (fun w hW hZ hw hsurj hflat _ hWP ↦
        (isCountablyIndexedAndClassical_iff_of_surjective_flat B S hS w hW hZ
          hw hsurj hflat).1 hWP)
  · exact hasAffineEtaleChartProperty_iff_of_descends_of_ascends B S hS X hX _
      (fun v hU hV hv hVP ↦ isWeaklyAdic_of_isRepresentable B S hS v hU hV hv.1 hVP)
      (fun Z hZaff hZP ↦ isWeaklyAdic_sigma B S hS Z hZaff hZP)
      (fun w hW hZ hw hsurj hflat _ hWP ↦
        (isWeaklyAdic_iff_of_surjective_flat B S hS w hW hZ hw hsurj hflat).1 hWP)
  · exact hasAffineEtaleChartProperty_iff_of_descends_of_ascends B S hS X hX _
      (fun v hU hV hv hVP ↦ isAdicStar_of_isRepresentable B S hS v hU hV hv.1 hVP)
      (fun Z hZaff hZP ↦ isAdicStar_sigma B S hS Z hZaff hZP)
      (fun w hW hZ hw hsurj hflat _ hWP ↦
        (isAdicStar_iff_of_surjective_flat B S hS w hW hZ hw hsurj hflat).1 hWP)
  · exact hasAffineEtaleChartProperty_iff_of_descends_of_ascends B S hS X hX _
      (fun v hU hV hv hVP ↦ isNoetherian_of_isRepresentable B S hS v hU hV hv.1
        (IsLocallyOfFiniteType.of_isRepresentableEtale B S hS v hv) hVP)
      (fun Z hZaff hZP ↦ isNoetherian_sigma B S hS Z hZaff hZP)
      (fun w hW hZ hw hsurj hflat hft hWP ↦
        (isNoetherian_iff_of_surjective_flat B S hS w hW hZ hw hsurj hflat
          hft).1 hWP)

end AlgebraicGeometry.FormalSpace

end
