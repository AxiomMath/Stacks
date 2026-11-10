module

public import Mathlib.Data.List.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablePresentingRing
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteTypeCharacterization
public import StacksFrontier.RingTheory.Rig.FiniteType

/-!
# Characterising finite type morphisms of locally adic\* formal algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`.

**Stacks 0GC0** says that for a morphism `f : X ⟶ Y` of locally adic\* formal algebraic spaces
over `S` the following four conditions are equivalent:

1. for every commutative square with `U`, `V` affine formal algebraic spaces and `U ⟶ X`,
   `V ⟶ Y` representable by algebraic spaces and étale, the morphism `U ⟶ V` corresponds to an
   arrow of `WAdm^{adic*}` which is adic and topologically of finite type;
2. there is a covering `{Yⱼ ⟶ Y}` as in Definition 0AIM and for each `j` a covering
   `{Xⱼᵢ ⟶ Yⱼ ×_Y X}` as in Definition 0AIM such that each `Xⱼᵢ ⟶ Yⱼ` corresponds to an arrow
   of `WAdm^{adic*}` which is adic and topologically of finite type;
3. there is a covering `{Xᵢ ⟶ X}` as in Definition 0AIM and for each `i` a factorization
   `Xᵢ ⟶ Yᵢ ⟶ Y` where `Yᵢ` is an affine formal algebraic space, `Yᵢ ⟶ Y` is representable by
   algebraic spaces and étale, and `Xᵢ ⟶ Yᵢ` corresponds to an arrow of `WAdm^{adic*}` which is
   adic and topologically of finite type;
4. `f` is locally of finite type.

The source's proof is the equivalence of conditions (1) and (2) of **Stacks 0GBW** — adic
together with topologically of finite type is the same as taut together with topologically of
finite type on `WAdm^{adic*}` — combined with **Stacks 0ANW**, the same list for locally
countably indexed formal algebraic spaces and the taut condition. The first half, Stacks 0GBW
on charts, is carried out here, for each of the three chart-tested conditions; the four
conditions themselves are identified in
`AlgebraicGeometry.FormalSpace.isLocallyOfFiniteType_tfae_of_isLocallyAdicStar` in
`StacksFrontier.AlgebraicGeometry.FormalSpace.AdicFiniteTypeCharacterizationUnconditional`.

## Main definitions

* `TopologicalRing.IsAdicStar`: membership in `WAdm^{adic*}`, an adic topological ring with a
  finitely generated ideal of definition. This is the class of rings on which the conditions
  of Stacks 0GC0 are tested.
* `TopologicalRing.IsAdicTopologicallyOfFiniteTypeHom`: being adic and topologically of finite
  type, in the shape in which the local-property machinery of Stacks 0ANG takes a property of
  arrows. It is condition (1) of Stacks 0GBW and the property Stacks 0GBW makes local.
* `AlgebraicGeometry.FormalSpace.IsCountablyIndexedOfIsAdicStar`: the affine implication from
  adic\* to countably indexed of the list of Stacks 0AKY, proved by
  `AlgebraicGeometry.FormalSpace.isCountablyIndexedOfIsAdicStar`.
* `AlgebraicGeometry.FormalSpace.ChartPresentationIsAdicStar`: the one input about the type of
  an affine chart which this library does not carry, named with the Stacks tag it is.

## Main results

* `AlgebraicGeometry.FormalSpace.hasPropertyOnAffineChartMap_adicStar_iff`: the equivalence of
  conditions (1) and (2) of **Stacks 0GBW** read on a map of affine formal algebraic spaces
  all of whose presenting rings are adic\*.
* `AlgebraicGeometry.FormalSpace.hasPropertyOnEveryAffineEtaleDiagram_adicStar_iff`,
  `AlgebraicGeometry.FormalSpace.hasPropertyAfterTargetCover_adicStar_iff` and
  `AlgebraicGeometry.FormalSpace.hasPropertyAfterSourceCover_adicStar_iff`: conditions (1),
  (2) and (3) of Stacks 0GC0 agree with conditions (1), (2) and (3) of Stacks 0ANW.

## Implementation notes

Conditions (1), (2) and (3) of Stacks 0GC0 are the three conditions of Stacks 0ANG for the
class `TopologicalRing.IsAdicStar` of adic\* topological rings and the property
`TopologicalRing.IsAdicTopologicallyOfFiniteTypeHom`, exactly as conditions (1), (2) and (3)
of Stacks 0ANW are those three conditions for countably indexed weakly admissible rings and
tautness together with topological finite type, and exactly as conditions (2), (3) and (4) of
Stacks 0GCD are those three conditions for Noetherian adic rings and flatness. So each of the
three is compared with its Stacks 0ANW counterpart one chart at a time, which is what this file
does; the comparison with condition (4) is then Stacks 0ANW itself.

The chart comparison is `hasPropertyOnAffineChartMap_adicStar_iff`, which is where Stacks 0GBW
enters, through `Rig.adicFiniteType_tfae`. Note that neither inclusion of the two chart
conditions is formal. `AlgebraicGeometry.FormalSpace.HasPropertyOnAffineChartMap` quantifies
over *every* presentation of the two charts by rings of the given class, and the two classes
are different: every adic\* ring is countably indexed weakly admissible, by
`Rig.weaklyAdmissible_of_isAdicRing` and `Rig.countablyGenerated_nhds_of_isAdicRing`, which
makes the condition for countably indexed weakly admissible rings quantify over strictly more
presentations. Both directions therefore need to know that *every* weakly admissible
topological ring presenting such a chart is already adic\*, which is the hypothesis
`ChartPresentationIsAdicStar` below.

Two facts about the type of an affine chart are needed, and neither is a conjunct of any of
the four conditions. Only one of them is a hypothesis.

The affine implication from adic\* to countably indexed of the list of **Stacks 0AKY** is what
turns the atlas defining "locally adic\*" into the atlas defining "locally countably indexed",
so that Stacks 0ANW applies to `f` at all. It is not a hypothesis:
`AlgebraicGeometry.FormalSpace.isCountablyIndexedOfIsAdicStar` proves it, from the countable
fundamental system of open ideals `Iⁿ` of an adic topological ring together with Stacks 0AN1.
(`AlgebraicGeometry.FormalSpace.IsCountablyIndexedOfIsNoetherian` is still a hypothesis in the
Noetherian case.)

The one that is a hypothesis, because the library does not carry it:

* `hchart` is **Stacks 0AKX** in the adic\* form of **Stacks 0AKT**, together with the
  uniqueness up to isomorphism of the presenting ring of a McQuillan affine formal algebraic
  space (**Stacks 0AIC**): every weakly admissible topological ring presenting an affine
  formal algebraic space representable étale over a locally adic\* formal algebraic space is
  adic\* with a finitely generated ideal of definition. The library takes the atlas of Stacks
  0AKY as the definition of "locally adic\*", so without this the charts appearing in the four
  conditions are not known to be objects of `WAdm^{adic*}`. It is the same hypothesis as
  `AlgebraicGeometry.FormalSpace.ChartPresentationIsNoetherianAdic` in the Noetherian case.

## References

* [Stacks Project, Tag 0AIC](https://stacks.math.columbia.edu/tag/0AIC)
* [Stacks Project, Tag 0AID](https://stacks.math.columbia.edu/tag/0AID)
* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AKT](https://stacks.math.columbia.edu/tag/0AKT)
* [Stacks Project, Tag 0AKX](https://stacks.math.columbia.edu/tag/0AKX)
* [Stacks Project, Tag 0AKY](https://stacks.math.columbia.edu/tag/0AKY)
* [Stacks Project, Tag 0ANG](https://stacks.math.columbia.edu/tag/0ANG)
* [Stacks Project, Tag 0ANW](https://stacks.math.columbia.edu/tag/0ANW)
* [Stacks Project, Tag 0GBW](https://stacks.math.columbia.edu/tag/0GBW)
* [Stacks Project, Tag 0GC0](https://stacks.math.columbia.edu/tag/0GC0)
* [Stacks Project, Tag 0GCD](https://stacks.math.columbia.edu/tag/0GCD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace TopologicalRing

/-- Membership in `WAdm^{adic*}`: a topological ring whose topology is adic and which has a
finitely generated ideal of definition. This is the class of rings on which the conditions of
Stacks 0GC0 are tested, and the class for which being adic and topologically of finite type is
a local property by Stacks 0GBW. It is the condition on the presenting ring in the definition
of an adic\* affine formal algebraic space, Stacks 0AID part (4). -/
abbrev IsAdicStar (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLinearTopology R R] : Prop :=
  TopologicalRing.IsAdic R ∧ ∃ I : Ideal R, TopologicalRing.IsIdealOfDefinition I ∧ I.FG

/-- Being adic and topologically of finite type, read as a property of arrows of
`WAdm^{adic*}`. This is the shape in which the local-property machinery of Stacks 0ANG takes a
property of arrows, and it is condition (1) of the equivalent conditions of Stacks 0GBW. -/
abbrev IsAdicTopologicallyOfFiniteTypeHom {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁]
    [IsTopologicalRing R₁] [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂]
    (φ : R₁ →+* R₂) : Prop :=
  RingHom.IsAdic φ ∧ IsTopologicallyOfFiniteType φ

/-- An adic\* topological ring is countably indexed weakly admissible: it is weakly admissible
because its topology is adic, and the powers of an ideal of definition are a countable basis of
the neighbourhood filter of zero. -/
theorem isCountablyWeaklyAdmissible_of_isAdicStar {R : Type u} [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R]
    (hR : TopologicalRing.IsAdicStar R) : TopologicalRing.IsCountablyWeaklyAdmissible R :=
  ⟨Rig.weaklyAdmissible_of_isAdicRing hR.1, Rig.countablyGenerated_nhds_of_isAdicRing hR.1⟩

end TopologicalRing

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The inputs about the type of an affine chart -/

/-- The affine implication from adic\* to countably indexed of the list of **Stacks 0AKY**: an
adic\* affine formal algebraic space over `S` is countably indexed. It is proved by
`AlgebraicGeometry.FormalSpace.isCountablyIndexedOfIsAdicStar` below and so is a hypothesis of
nothing. -/
abbrev IsCountablyIndexedOfIsAdicStar : Prop :=
  ∀ U : FppfSheaf B S hS, IsAdicStar B S hS U → IsCountablyIndexed B S hS U

/-- **An adic\* affine formal algebraic space is countably indexed.** The powers of an ideal of
definition of an adic topological ring are a countable fundamental system of neighbourhoods of
zero, so the presenting ring of an adic\* affine formal algebraic space has countably generated
`nhds 0`, and Stacks 0AN1 turns that into countable indexing of the space.

Untagged: Stacks 0AKY is a list of definitions, whose covering set is the five predicates of
`StacksFrontier/AlgebraicGeometry/FormalSpace/Types.lean`; this is the implication between two of
them that the source records in passing. -/
theorem isCountablyIndexedOfIsAdicStar : IsCountablyIndexedOfIsAdicStar B S hS := by
  rintro U ⟨-, A, _, _, _, _, hApres, hAadic, -⟩
  exact isCountablyIndexed_of_isPresentingRing B S hS U A hApres
    (Rig.countablyGenerated_nhds_of_isAdicRing hAadic)

/-- **Stacks 0AKX** in the adic\* form of **Stacks 0AKT**, together with the uniqueness up to
isomorphism of the presenting ring of a McQuillan affine formal algebraic space (**Stacks
0AIC**): every weakly admissible topological ring presenting an affine formal algebraic space
representable étale over a locally adic\* formal algebraic space over `S` is adic and has a
finitely generated ideal of definition. The library takes the atlas of Stacks 0AKY as the
definition of "locally adic\*", so without this the charts appearing in a chart-tested
condition are not known to be objects of `WAdm^{adic*}`. -/
abbrev ChartPresentationIsAdicStar : Prop :=
  ∀ (Z : FppfSheaf B S hS), IsLocallyAdicStar B S hS Z →
    ∀ (U : FppfSheaf B S hS) (a : U ⟶ Z), IsAffineFormalAlgebraicSpace B S hS U →
      IsRepresentableEtale B S hS a →
      ∀ (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
        [IsLinearTopology A A] (E : QuotientSystem B S hS A), (U ≅ formalSpectrum E) →
        TopologicalRing.IsAdicStar A

/-! ### Stacks 0GBW on charts -/

variable {B S hS}

/-- A locally adic\* formal algebraic space over `S` is locally countably indexed: the atlas of
adic\* affine formal algebraic spaces of Stacks 0AKY is an atlas of countably indexed ones. -/
theorem isLocallyCountablyIndexed_of_isLocallyAdicStar {X : FppfSheaf B S hS}
    (hX : IsLocallyAdicStar B S hS X) :
    IsLocallyCountablyIndexed B S hS X := by
  obtain ⟨hform, I, Xi, a, haff, hetale, hsurj, hstar⟩ := hX
  exact ⟨hform, I, Xi, a, haff, hetale, hsurj,
    fun i ↦ isCountablyIndexedOfIsAdicStar B S hS (Xi i) (hstar i)⟩

/-- **The equivalence of conditions (1) and (2) of Stacks 0GBW, read on charts.** Let
`t : U ⟶ V` be a map of affine formal algebraic spaces over `S` all of whose presenting
topological rings are adic\*. Then `t` corresponds to an adic, topologically of finite type
arrow of `WAdm^{adic*}` exactly when it corresponds to a taut, topologically of finite type
arrow of `WAdm^{count}`.

The two conditions quantify over different classes of presentations, so neither inclusion is
formal: the condition for countably indexed weakly admissible rings quantifies over strictly
more presentations, since an adic\* ring is countably indexed weakly admissible, and the
hypotheses `hU` and `hV` are what make the two ranges of quantification agree. On a single
presentation the two properties of the arrow are identified by Stacks 0GBW. -/
@[stacks 0GBW "the equivalence of conditions (1) and (2), read on a map of affine formal \
algebraic spaces whose presenting rings are all adic*"]
theorem hasPropertyOnAffineChartMap_adicStar_iff {U V : FppfSheaf B S hS} (t : U ⟶ V)
    (hU : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLinearTopology R R] (E : QuotientSystem B S hS R), (U ≅ formalSpectrum E) →
      TopologicalRing.IsAdicStar R)
    (hV : ∀ (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
      [IsLinearTopology A A] (D : QuotientSystem B S hS A), (V ≅ formalSpectrum D) →
      TopologicalRing.IsAdicStar A) :
    HasPropertyOnAffineChartMap B S hS TopologicalRing.IsAdicStar
        TopologicalRing.IsAdicTopologicallyOfFiniteTypeHom t ↔
      HasPropertyOnAffineChartMap B S hS TopologicalRing.IsCountablyWeaklyAdmissible
        TopologicalRing.IsTautTopologicallyOfFiniteTypeHom t := by
  constructor
  · intro h A R _ _ _ _ _ _ _ _ _ _ hA D E eU eV g hg
    have hAstar := hV A D eV
    have hRstar := hU R E eU
    exact ((Rig.adicFiniteType_tfae g.toRingHom hAstar.1 hRstar.1
      hAstar.2 hRstar.2).out 1 2).mp (h A R hAstar hRstar hA D E eU eV g hg)
  · intro h A R _ _ _ _ _ _ _ _ hAstar hRstar hA D E eU eV g hg
    exact ((Rig.adicFiniteType_tfae g.toRingHom hAstar.1 hRstar.1
      hAstar.2 hRstar.2).out 1 2).mpr
      (h A R (TopologicalRing.isCountablyWeaklyAdmissible_of_isAdicStar hAstar)
        (TopologicalRing.isCountablyWeaklyAdmissible_of_isAdicStar hRstar) hA D E eU eV g hg)

/-- The chart comparison of `hasPropertyOnAffineChartMap_adicStar_iff` for a map between an
affine representable étale chart of a locally adic\* formal algebraic space `X` and one of a
locally adic\* formal algebraic space `Y`, whose presenting rings are adic\* by `hchart`. -/
theorem hasPropertyOnAffineChartMap_adicStar_iff_of_isRepresentableEtale
    (hchart : ChartPresentationIsAdicStar B S hS) {X Y : FppfSheaf B S hS}
    (hX : IsLocallyAdicStar B S hS X) (hY : IsLocallyAdicStar B S hS Y)
    {U V : FppfSheaf B S hS} (a : U ⟶ X) (b : V ⟶ Y) (t : U ⟶ V)
    (hU : IsAffineFormalAlgebraicSpace B S hS U)
    (hV : IsAffineFormalAlgebraicSpace B S hS V)
    (ha : IsRepresentableEtale B S hS a) (hb : IsRepresentableEtale B S hS b) :
    HasPropertyOnAffineChartMap B S hS TopologicalRing.IsAdicStar
        TopologicalRing.IsAdicTopologicallyOfFiniteTypeHom t ↔
      HasPropertyOnAffineChartMap B S hS TopologicalRing.IsCountablyWeaklyAdmissible
        TopologicalRing.IsTautTopologicallyOfFiniteTypeHom t :=
  hasPropertyOnAffineChartMap_adicStar_iff t
    (fun R _ _ _ _ E e ↦ hchart X hX U a hU ha R E e)
    (fun A _ _ _ _ D e ↦ hchart Y hY V b hV hb A D e)

/-! ### The three chart-tested conditions -/

/-- Condition (1) of **Stacks 0GC0** agrees with condition (1) of **Stacks 0ANW**: on the
charts of a square over `f`, being adic and topologically of finite type on `WAdm^{adic*}` is
being taut and topologically of finite type on `WAdm^{count}`. -/
theorem hasPropertyOnEveryAffineEtaleDiagram_adicStar_iff
    (hchart : ChartPresentationIsAdicStar B S hS) {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsLocallyAdicStar B S hS X) (hY : IsLocallyAdicStar B S hS Y) :
    HasPropertyOnEveryAffineEtaleDiagram B S hS TopologicalRing.IsAdicStar
        TopologicalRing.IsAdicTopologicallyOfFiniteTypeHom f ↔
      HasPropertyOnEveryAffineEtaleDiagram B S hS
        TopologicalRing.IsCountablyWeaklyAdmissible
        TopologicalRing.IsTautTopologicallyOfFiniteTypeHom f :=
  ⟨fun h U V a b t hU hV ha hb hsq ↦
      (hasPropertyOnAffineChartMap_adicStar_iff_of_isRepresentableEtale hchart hX hY
        a b t hU hV ha hb).mp (h U V a b t hU hV ha hb hsq),
    fun h U V a b t hU hV ha hb hsq ↦
      (hasPropertyOnAffineChartMap_adicStar_iff_of_isRepresentableEtale hchart hX hY
        a b t hU hV ha hb).mpr (h U V a b t hU hV ha hb hsq)⟩

/-- Condition (2) of **Stacks 0GC0** agrees with condition (2) of **Stacks 0ANW**.

A chart of the covering of a fibre product `Yⱼ ×_Y X` maps to `X` by its second projection,
which is representable étale because it is a base change of the chart `Yⱼ ⟶ Y`, so the chart
comparison applies to the map from it to `Yⱼ`. -/
theorem hasPropertyAfterTargetCover_adicStar_iff
    (hchart : ChartPresentationIsAdicStar B S hS) {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsLocallyAdicStar B S hS X) (hY : IsLocallyAdicStar B S hS Y) :
    HasPropertyAfterTargetCover B S hS TopologicalRing.IsAdicStar
        TopologicalRing.IsAdicTopologicallyOfFiniteTypeHom f ↔
      HasPropertyAfterTargetCover B S hS
        TopologicalRing.IsCountablyWeaklyAdmissible
        TopologicalRing.IsTautTopologicallyOfFiniteTypeHom f := by
  have key : ∀ {V : FppfSheaf B S hS} (v : V ⟶ Y) {U : FppfSheaf B S hS} (w : U ⟶ pullback v f),
      IsAffineFormalAlgebraicSpace B S hS U → IsAffineFormalAlgebraicSpace B S hS V →
      IsRepresentableEtale B S hS w → IsRepresentableEtale B S hS v →
      (HasPropertyOnAffineChartMap B S hS TopologicalRing.IsAdicStar
          TopologicalRing.IsAdicTopologicallyOfFiniteTypeHom (w ≫ pullback.fst v f) ↔
        HasPropertyOnAffineChartMap B S hS TopologicalRing.IsCountablyWeaklyAdmissible
          TopologicalRing.IsTautTopologicallyOfFiniteTypeHom (w ≫ pullback.fst v f)) :=
    fun {_} v {_} w hU hV hw hv ↦
      hasPropertyOnAffineChartMap_adicStar_iff_of_isRepresentableEtale hchart hX hY
        (w ≫ pullback.snd v f) v (w ≫ pullback.fst v f) hU hV
        (IsRepresentableEtale.comp B S hS hw (isRepresentableEtale_pullback_snd B S hS v f hv)) hv
  constructor <;> rintro ⟨J, V, v, hV, hinner⟩ <;> refine ⟨J, V, v, hV, fun j ↦ ?_⟩ <;>
    obtain ⟨I, U, w, hU, hp⟩ := hinner j <;> refine ⟨I, U, w, hU, fun i ↦ ?_⟩ <;>
    first
      | exact (key (v j) (w i) (hU.1 i) (hV.1 j) (hU.2.1 i) (hV.2.1 j)).mp (hp i)
      | exact (key (v j) (w i) (hU.1 i) (hV.1 j) (hU.2.1 i) (hV.2.1 j)).mpr (hp i)

/-- Condition (3) of **Stacks 0GC0** agrees with condition (3) of **Stacks 0ANW**: the member
of the covering of `X` and the chart of `Y` it factors through are both representable étale, so
the chart comparison applies to the factoring map between them. -/
theorem hasPropertyAfterSourceCover_adicStar_iff
    (hchart : ChartPresentationIsAdicStar B S hS) {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsLocallyAdicStar B S hS X) (hY : IsLocallyAdicStar B S hS Y) :
    HasPropertyAfterSourceCover B S hS TopologicalRing.IsAdicStar
        TopologicalRing.IsAdicTopologicallyOfFiniteTypeHom f ↔
      HasPropertyAfterSourceCover B S hS
        TopologicalRing.IsCountablyWeaklyAdmissible
        TopologicalRing.IsTautTopologicallyOfFiniteTypeHom f := by
  constructor <;> rintro ⟨I, U, u, hU, hfac⟩ <;> refine ⟨I, U, u, hU, fun i ↦ ?_⟩ <;>
    obtain ⟨V, v, t, hV, hv, hsq, hp⟩ := hfac i <;> refine ⟨V, v, t, hV, hv, hsq, ?_⟩ <;>
    first
      | exact (hasPropertyOnAffineChartMap_adicStar_iff_of_isRepresentableEtale hchart hX hY
          (u i) v t (hU.1 i) hV (hU.2.1 i) hv).mp hp
      | exact (hasPropertyOnAffineChartMap_adicStar_iff_of_isRepresentableEtale hchart hX hY
          (u i) v t (hU.1 i) hV (hU.2.1 i) hv).mpr hp

end AlgebraicGeometry.FormalSpace

end
