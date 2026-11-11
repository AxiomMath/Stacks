module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AdicFiniteTypeCharacterization
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteType
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautMorphismRepresentability
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Types
public import StacksFrontier.Topology.Algebra.AdicTopology.AdicRingMap

/-!
# Adic morphisms of formal algebraic spaces

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` be a morphism of
formal algebraic spaces over `S`. Formal Spaces, **Section 0AQ2** matches the notion of an
*adic morphism* with two other conditions: representability of `f` by algebraic spaces, and the
requirement that every commutative square

```
U ⟶ V
↓     ↓
X ⟶ Y
```

with `U` and `V` affine formal algebraic spaces and `U ⟶ X`, `V ⟶ Y` representable by
algebraic spaces and étale, has its upper horizontal map given by an adic map in
`WAdm^{adic*}` — equivalently, by the footnote of that section, by a taut one. Definition 0AQ3
then takes representability as the definition and refers to the discussion for the chart form.

## Main definitions

* `AlgebraicGeometry.FormalSpace.IsAdicMorphism`: **Stacks 0AQ3**, an *adic morphism* of
  formal algebraic spaces over `S` is one that is representable by algebraic spaces.
* `AlgebraicGeometry.FormalSpace.IsCountablyAdicStar`: membership in `WAdm^{adic*}` with
  countably generated topology, the class of rings over which Section 0AQ2 reads its chart
  conditions.
* `AlgebraicGeometry.FormalSpace.AdicChartProperty`: adicness of a continuous homomorphism, in
  the shape in which the local-property machinery of Stacks 0ANG takes a property of ring maps.
* `AlgebraicGeometry.FormalSpace.IsAdicOnEveryAffineEtaleDiagram` and
  `AlgebraicGeometry.FormalSpace.IsTautOnEveryAffineEtaleDiagramAdicStar`: condition (2) of
  Section 0AQ2 in its adic and in its taut reading.

## Main results

* `AlgebraicGeometry.FormalSpace.isAdicMorphism_of_isIso`,
  `AlgebraicGeometry.FormalSpace.IsAdicMorphism.comp` and
  `AlgebraicGeometry.FormalSpace.IsAdicMorphism.of_isPullback`: isomorphisms are adic, and the
  adic morphisms are closed under composition and stable under base change. These are Stacks
  0APY and 0APZ read through Definition 0AQ3.
* `AlgebraicGeometry.FormalSpace.isAdicOnEveryAffineEtaleDiagram_iff_isTautAdicStar`:
  **Section 0AQ2**, the footnote — on `WAdm^{adic*}` the adic and the taut reading of the chart
  condition agree. Proved outright.
* `AlgebraicGeometry.FormalSpace.isAdicOnEveryAffineEtaleDiagram_of_isRepresentable`: the
  implication from condition (1) to condition (2) of Section 0AQ2, deduced from the form of
  Stacks 0ANK that takes five of its inputs as hypotheses. The section itself is
  `AlgebraicGeometry.FormalSpace.isAdicMorphism_tfae` of
  `StacksFrontier.AlgebraicGeometry.FormalSpace.AdicMorphismConverse`, proved outright.

## Implementation notes

Definition 0AQ3 is stated for `X` and `Y` locally adic\*, and under that standing assumption
it declares `f` adic exactly when `f` is representable by algebraic spaces. The predicate
`AlgebraicGeometry.FormalSpace.IsAdicMorphism` is therefore representability by algebraic
spaces and nothing else, and the locally adic\* hypotheses are imposed by the results that use
it rather than built into it; this is how the library treats the standing hypotheses of Stacks
0AQM and 0GCP as well. Representability is read in the value universe `Type (u + 1)` in which
a formal algebraic space lives, so the predicate is
`AlgebraicGeometry.Space.IsRepresentableByAlgebraicSpacesULift` applied to the underlying
morphism of presheaves — the same predicate that Stacks 0AIM, 0AKY and 0ANK are stated with
throughout the library, and the only one that can be applied to a morphism of formal algebraic
spaces at all.

What the standing hypotheses buy is the equivalence of the definition with the chart condition
of the discussion above, which is the sense in which the terminology is justified: this is
`AlgebraicGeometry.FormalSpace.isAdicMorphism_tfae` of
`StacksFrontier.AlgebraicGeometry.FormalSpace.AdicMorphismConverse`, with the implication from the
definition to the chart condition holding with no hypothesis on `X` or `Y`
(`AlgebraicGeometry.FormalSpace.isAdicOnEveryAffineEtaleDiagram_of_isAdicMorphism'` of
`StacksFrontier.AlgebraicGeometry.FormalSpace.AdicMorphismCharts`).

The footnote is Stacks 0GBS read on every chart square, and it is unconditional here because
the class `IsCountablyAdicStar` carries exactly the two inputs 0GBS asks for: the source of the
chart map — the ring presenting the chart of the *target* `Y` — has a finitely generated ideal
of definition, and the target of the chart map is complete and separated, being weakly
admissible. That is why the chart conditions of this file are read at `WAdm^{adic*}` rather
than at the countably indexed weakly admissible class of Stacks 0ANK: at the latter the
implication from taut to adic is not available, the finitely generated ideal of definition
being missing.

Condition (1) of the section is representability by algebraic spaces. The source matches it
with the chart condition through Stacks 0ANK;
`AlgebraicGeometry.FormalSpace.isAdicOnEveryAffineEtaleDiagram_of_isRepresentable` follows that
route through the form `AlgebraicGeometry.FormalSpace.isTaut_tfae_isRepresentableByAlgebraicSpaces`
of 0ANK that takes five of its inputs as hypotheses. The equivalence itself is proved without
them, by a direct route, in `StacksFrontier.AlgebraicGeometry.FormalSpace.AdicMorphismCharts` and
`StacksFrontier.AlgebraicGeometry.FormalSpace.AdicMorphismConverse`.

The predicate `AlgebraicGeometry.FormalSpace.IsAdicOnEveryAffineEtaleDiagramNoetherian` of
`StacksFrontier.AlgebraicGeometry.FormalSpace.RigSmoothBaseChange` is the same chart condition read
at the Noetherian adic class of Stacks 0ANI, which is the class the rig-smooth and rig-flat
developments work over; it is not a second spelling of the notion but the same condition at the
other of the two subcategories in which the local-property machinery is set up, and neither
class is contained in the other — a Noetherian adic ring need not be complete. It is kept
distinct from `AlgebraicGeometry.FormalSpace.IsAdicMorphism`, the equivalence of
`AlgebraicGeometry.FormalSpace.isAdicMorphism_tfae` being proved at `WAdm^{adic*}`.

## References

* [Stacks Project, Tag 0AQ2](https://stacks.math.columbia.edu/tag/0AQ2)
* [Stacks Project, Tag 0AQ3](https://stacks.math.columbia.edu/tag/0AQ3)
* [Stacks Project, Tag 0GBS](https://stacks.math.columbia.edu/tag/0GBS)
* [Stacks Project, Tag 0ANG](https://stacks.math.columbia.edu/tag/0ANG)
* [Stacks Project, Tag 0ANK](https://stacks.math.columbia.edu/tag/0ANK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0AQ3.** Let `f : X ⟶ Y` be a morphism of formal algebraic spaces over `S` with
`X` and `Y` locally adic\*. Then `f` is an *adic morphism* when `f` is representable by
algebraic spaces.

The locally adic\* hypotheses on `X` and `Y` are the standing assumptions under which the
source introduces the terminology; as for Stacks 0AQM they are imposed by the results that use
the predicate rather than built into it, so that the predicate is the defining condition and
nothing more. -/
@[stacks 0AQ3]
abbrev IsAdicMorphism {X Y : FppfSheaf B S hS} (f : X ⟶ Y) : Prop :=
  Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom

/-- An isomorphism of formal algebraic spaces over `S` is an adic morphism. -/
theorem isAdicMorphism_of_isIso {X Y : FppfSheaf B S hS} (f : X ⟶ Y) [IsIso f] :
    IsAdicMorphism B S hS f := by
  have hiso : IsIso f.hom := inferInstance
  have hpb : ∀ (U : BigFppfOver B S hS) (ξ : (uliftYoneda.{u + 1}).obj U ⟶ Y.obj),
      IsPullback (𝟙 ((uliftYoneda.{u + 1}).obj U)) (ξ ≫ inv f.hom) ξ f.hom :=
    fun U ξ ↦ IsPullback.of_horiz_isIso ⟨by simp⟩
  intro U ξ
  exact Space.isAlgebraicSpaceULift_of_iso B S hS (hpb U ξ).isoPullback
    (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS U)

/-- The identity of a formal algebraic space over `S` is an adic morphism. -/
theorem isAdicMorphism_id (X : FppfSheaf B S hS) : IsAdicMorphism B S hS (𝟙 X) :=
  isAdicMorphism_of_isIso B S hS (𝟙 X)

/-- **Stacks 0APY read through Definition 0AQ3.** A composition of adic morphisms of formal
algebraic spaces over `S` is adic. -/
theorem IsAdicMorphism.comp {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsAdicMorphism B S hS f) (hg : IsAdicMorphism B S hS g) :
    IsAdicMorphism B S hS (f ≫ g) :=
  Space.isRepresentableByAlgebraicSpacesULift_comp B S hS f.hom g.hom hf hg

/-- **Stacks 0APZ read through Definition 0AQ3.** A base change of an adic morphism of formal
algebraic spaces over `S` is adic. -/
theorem IsAdicMorphism.of_isPullback {W X Z Y : FppfSheaf B S hS}
    {p : W ⟶ Z} {q : W ⟶ X} {g : Z ⟶ Y} {f : X ⟶ Y} (sq : IsPullback p q g f)
    (hf : IsAdicMorphism B S hS f) :
    IsAdicMorphism B S hS p :=
  Space.isRepresentableByAlgebraicSpacesULift_of_isPullback B S hS q.hom p.hom f.hom g.hom
    (isPullback_hom_of_isPullback B S hS sq) hf

/-- Membership in `WAdm^{adic*}` with countably generated topology: a weakly admissible
topological ring with a countable fundamental system of neighbourhoods of zero which carries a
finitely generated ideal of definition defining its topology. This is the class of rings over
which Formal Spaces, Section 0AQ2 reads the chart condition for an adic morphism. -/
abbrev IsCountablyAdicStar (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLinearTopology R R] : Prop :=
  TopologicalRing.IsCountablyWeaklyAdmissible R ∧ ∃ I : Ideal R, I.FG ∧ _root_.IsAdic I

/-- Adicness of a continuous homomorphism of topological rings, in the shape in which the
local-property machinery of Stacks 0ANG takes a property of ring maps. -/
abbrev AdicChartProperty : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁]
    [IsTopologicalRing R₁] [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂],
    (R₁ →+* R₂) → Prop :=
  fun {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
    [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂] (φ : R₁ →+* R₂) ↦
    RingHom.IsAdic φ

/-- **Section 0AQ2, condition (2).** Every commutative square whose vertical maps are
representable étale maps from affine formal algebraic spaces has its upper horizontal map given
by an adic continuous homomorphism in `WAdm^{adic*}`. -/
abbrev IsAdicOnEveryAffineEtaleDiagram {X Y : FppfSheaf B S hS} (f : X ⟶ Y) : Prop :=
  HasPropertyOnEveryAffineEtaleDiagram B S hS IsCountablyAdicStar AdicChartProperty f

/-- **Section 0AQ2, condition (2) in its taut reading.** The same condition with "adic"
replaced by "taut", which is how the footnote of the section states it. -/
abbrev IsTautOnEveryAffineEtaleDiagramAdicStar {X Y : FppfSheaf B S hS} (f : X ⟶ Y) : Prop :=
  HasPropertyOnEveryAffineEtaleDiagram B S hS IsCountablyAdicStar TautChartProperty f

/-- **Section 0AQ2, the footnote.** On `WAdm^{adic*}` the chart condition of the section may be
read with "adic" or with "taut": the two readings agree, by Stacks 0GBS. -/
@[stacks 0AQ2 "the footnote of the section: on WAdm^{adic*} the adic and the taut reading of \
the chart condition agree"]
theorem isAdicOnEveryAffineEtaleDiagram_iff_isTautAdicStar {X Y : FppfSheaf B S hS}
    (f : X ⟶ Y) :
    IsAdicOnEveryAffineEtaleDiagram B S hS f ↔
      IsTautOnEveryAffineEtaleDiagramAdicStar B S hS f := by
  constructor <;>
    intro h U V a b t hU hV ha hb hsq A R _ _ _ _ _ _ _ _ hCA hCR hA D E eU eV g hg <;>
    have hg' := h U V a b t hU hV ha hb hsq A R hCA hCR hA D E eU eV g hg
  · exact RingHom.isTaut_of_isAdic g.toRingHom hg'
  · exact (@RingHom.isAdic_iff_isTaut A R _ _ _ _ _ _ _ _ g.toRingHom hCA.2
      hCR.1.1.2.1 hCR.1.1.2.2).mpr hg'

/-- **Condition (1) of Section 0AQ2 implies condition (2), through Stacks 0ANK.** A morphism of
locally countably indexed formal algebraic spaces over `S` which is representable by algebraic
spaces has every one of its chart maps in `WAdm^{adic*}` adic.

Stacks 0ANK turns representability into the taut reading of the chart condition at the
countably indexed weakly admissible class, which contains `WAdm^{adic*}`; the footnote then
turns taut into adic. The five hypotheses `h0AJ3`, `h0AKX`, `h0AN5`, `h0AQ0` and `h0AN4` are
those of that form of Stacks 0ANK and are passed straight through. The same implication holds
with no hypothesis at all:
`AlgebraicGeometry.FormalSpace.isAdicOnEveryAffineEtaleDiagram_of_isAdicMorphism'`. -/
theorem isAdicOnEveryAffineEtaleDiagram_of_isRepresentable {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsLocallyCountablyIndexed B S hS X) (hY : IsLocallyCountablyIndexed B S hS Y)
    (h0AJ3 : ∀ (V : FppfSheaf B S hS) (v : V ⟶ Y), IsAffineFormalAlgebraicSpace B S hS V →
      IsRepresentableEtale B S hS v → IsFormalAlgebraicSpace B S hS (pullback v f))
    (h0AKX : ∀ (Z : FppfSheaf B S hS), IsLocallyCountablyIndexed B S hS Z →
      ∀ (U : FppfSheaf B S hS) (a : U ⟶ Z), IsAffineFormalAlgebraicSpace B S hS U →
      IsRepresentableEtale B S hS a → IsCountablyIndexed B S hS U)
    (h0AN5 : ∀ {U V : FppfSheaf B S hS} (t : U ⟶ V),
      IsAffineFormalAlgebraicSpace B S hS U → IsAffineFormalAlgebraicSpace B S hS V →
      IsCountablyIndexed B S hS U → IsCountablyIndexed B S hS V →
      (Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS t.hom ↔
        HasPropertyOnAffineChartMap B S hS TopologicalRing.IsCountablyWeaklyAdmissible
          TautChartProperty t))
    (h0AQ0 : ∀ {A A' A'' : FppfSheaf B S hS} (s : A ⟶ A') (r : A' ⟶ A''),
      IsFormalAlgebraicSpace B S hS A → IsFormalAlgebraicSpace B S hS A' →
      IsFormalAlgebraicSpace B S hS A'' →
      Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (s ≫ r).hom →
      Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS s.hom)
    (h0AN4 : ∀ (I : Type (u + 1)) (U W : I → FppfSheaf B S hS) (a : ∀ i, U i ⟶ X)
      (b : ∀ i, W i ⟶ Y) (t : ∀ i, U i ⟶ W i), IsAffineEtaleCover B S hS U a →
      (∀ i, IsAffineFormalAlgebraicSpace B S hS (W i)) →
      (∀ i, Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (b i).hom) →
      (∀ i, Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (t i).hom) →
      (∀ i, a i ≫ f = t i ≫ b i) →
      Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom)
    (hf : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom) :
    IsAdicOnEveryAffineEtaleDiagram B S hS f := by
  have htaut : IsTautOnEveryAffineEtaleDiagram B S hS f :=
    ((isTaut_tfae_isRepresentableByAlgebraicSpaces B S hS f hX hY h0AJ3 h0AKX h0AN5 h0AQ0
      h0AN4).out 4 1).mp hf
  refine (isAdicOnEveryAffineEtaleDiagram_iff_isTautAdicStar B S hS f).mpr ?_
  intro U V a b t hU hV ha hb hsq A R _ _ _ _ _ _ _ _ hCA hCR hA D E eU eV g hg
  exact htaut U V a b t hU hV ha hb hsq A R hCA.1 hCR.1 hA D E eU eV g hg

/-- **Definition 0AQ3 at the hypotheses it is stated under.** An adic morphism of locally
adic\* formal algebraic spaces over `S` — that is, by Definition 0AQ3, one representable by
algebraic spaces — has every one of its chart maps in `WAdm^{adic*}` adic. This is the content
of the reference that Definition 0AQ3 makes to the discussion above it, read at the locally
adic\* spaces the definition is stated for.

A locally adic\* formal algebraic space is locally countably indexed, so this is
`AlgebraicGeometry.FormalSpace.isAdicOnEveryAffineEtaleDiagram_of_isRepresentable` with the
standing hypotheses of Definition 0AQ3 in place of the weaker ones that proof needs; the five
hypotheses of Stacks 0ANK are passed straight through. -/
theorem isAdicOnEveryAffineEtaleDiagram_of_isAdicMorphism {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsLocallyAdicStar B S hS X) (hY : IsLocallyAdicStar B S hS Y)
    (h0AJ3 : ∀ (V : FppfSheaf B S hS) (v : V ⟶ Y), IsAffineFormalAlgebraicSpace B S hS V →
      IsRepresentableEtale B S hS v → IsFormalAlgebraicSpace B S hS (pullback v f))
    (h0AKX : ∀ (Z : FppfSheaf B S hS), IsLocallyCountablyIndexed B S hS Z →
      ∀ (U : FppfSheaf B S hS) (a : U ⟶ Z), IsAffineFormalAlgebraicSpace B S hS U →
      IsRepresentableEtale B S hS a → IsCountablyIndexed B S hS U)
    (h0AN5 : ∀ {U V : FppfSheaf B S hS} (t : U ⟶ V),
      IsAffineFormalAlgebraicSpace B S hS U → IsAffineFormalAlgebraicSpace B S hS V →
      IsCountablyIndexed B S hS U → IsCountablyIndexed B S hS V →
      (Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS t.hom ↔
        HasPropertyOnAffineChartMap B S hS TopologicalRing.IsCountablyWeaklyAdmissible
          TautChartProperty t))
    (h0AQ0 : ∀ {A A' A'' : FppfSheaf B S hS} (s : A ⟶ A') (r : A' ⟶ A''),
      IsFormalAlgebraicSpace B S hS A → IsFormalAlgebraicSpace B S hS A' →
      IsFormalAlgebraicSpace B S hS A'' →
      Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (s ≫ r).hom →
      Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS s.hom)
    (h0AN4 : ∀ (I : Type (u + 1)) (U W : I → FppfSheaf B S hS) (a : ∀ i, U i ⟶ X)
      (b : ∀ i, W i ⟶ Y) (t : ∀ i, U i ⟶ W i), IsAffineEtaleCover B S hS U a →
      (∀ i, IsAffineFormalAlgebraicSpace B S hS (W i)) →
      (∀ i, Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (b i).hom) →
      (∀ i, Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (t i).hom) →
      (∀ i, a i ≫ f = t i ≫ b i) →
      Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom)
    (hf : IsAdicMorphism B S hS f) :
    IsAdicOnEveryAffineEtaleDiagram B S hS f :=
  isAdicOnEveryAffineEtaleDiagram_of_isRepresentable B S hS f
    (isLocallyCountablyIndexed_of_isLocallyAdicStar hX)
    (isLocallyCountablyIndexed_of_isLocallyAdicStar hY) h0AJ3 h0AKX h0AN5 h0AQ0 h0AN4 hf

end AlgebraicGeometry.FormalSpace

end
