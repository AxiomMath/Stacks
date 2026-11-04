module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.EtaleChartCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.EtaleIffSmoothUnramified
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.EtaleLocalLift
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmoothChartCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmoothSquares

/-!
# Formal smoothness of a morphism of algebraic spaces is an étale-chart condition

[Stacks Project, Tag 061K] states that for a morphism `f : X ⟶ Y` of algebraic spaces over a
scheme `S` the following are equivalent: (1) `f` is formally smooth; (2) in *every* commuting
square of étale scheme charts of `f` the morphism of schemes `ψ` is formally smooth; (3) the
same for *one* such square with surjective vertical arrows. This file proves the two
biconditionals, carrying two named prerequisites that the library does not have.

The forward implications are
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_formallySmoothScheme` and
`AlgebraicGeometry.Space.holdsOnSurjectiveEtaleChart_formallySmoothScheme`, which take the
scheme-level implication (3) ⟹ (1) of [Stacks Project, Tag 0D0F] as a hypothesis. What is new
here is the converse (3) ⟹ (1), and what it needs is isolated by following the Stacks proof,
which splits into two steps: (I) the sheaf of lifts of a given infinitesimal lifting problem
has sections étale-locally, and (II) that sheaf, a pseudo-torsor under
`Hom(a^*Ω_{X/Y}, C_{T/T'})`, is trivial. Step (I) is proved here in full, unconditionally.
Step (II) is the vanishing of the first étale cohomology of that `Hom`-sheaf on an affine
scheme and is carried as the hypothesis `hGlue`.

## Main definitions

* `AlgebraicGeometry.Space.FormallySmoothEtaleLocally` is step (I) as a property of a morphism
  of presheaves: every infinitesimal lifting problem against a square-zero closed immersion of
  affine objects of the site is solvable over an affine étale neighbourhood of every point of
  the thickening, compatibly with the given section of the source. It is exactly the conclusion
  of part (4) of [Stacks Project, Tag 04CY].

## Main results

* `AlgebraicGeometry.Space.formallySmooth_chart_comp_of_formallySmoothScheme`: if the scheme
  morphism `ψ` of a commuting square of étale charts is formally smooth, then the composite of
  the chart of the source with `f` is formally smooth. This is the first half of step (I).
* `AlgebraicGeometry.Space.formallySmoothEtaleLocally_of_surjectiveEtaleChart`: condition (3)
  of [Stacks Project, Tag 061K] implies `FormallySmoothEtaleLocally`, that is, step (I) of the
  Stacks proof of (3) ⟹ (1). This is unconditional.
* `AlgebraicGeometry.Space.formallySmoothEtaleLocally_of_formallySmooth`: condition (1) implies
  `FormallySmoothEtaleLocally` as well, trivially, so the property sits between (1) and (3).
* `AlgebraicGeometry.Space.formallySmooth_of_surjectiveEtaleChart`: the implication (3) ⟹ (1),
  granted `hGlue`.
* `AlgebraicGeometry.Space.formallySmooth_iff_etaleCharts`: **Stacks 061K**, the equivalence of
  (1) and (2).
* `AlgebraicGeometry.Space.formallySmooth_iff_surjectiveEtaleChart`: **Stacks 061K**, the
  equivalence of (1) and (3).
* `AlgebraicGeometry.Space.formallySmooth_iff_holdsOnSurjectiveEtaleChart`: the same
  equivalence with condition (3) read through
  `AlgebraicGeometry.Space.HoldsOnSurjectiveEtaleChart` of [Stacks Project, Tag 03MJ], which
  asks only the chart of the source to be surjective.

## Implementation notes

Condition (2) of the tag reads formal smoothness of `ψ` as
`Stacks.Smooth.FormallySmoothScheme`, the infinitesimal lifting property of a morphism of
schemes against first-order thickenings of all affine schemes. That is
[Stacks Project, Tag 02H0], Definition 37.11.1. The text of Tag 061K cites "More on
Morphisms, Definition 37.6.1" instead, which is [Stacks Project, Tag 02H8], the definition of a
formally *unramified* morphism of schemes; since the word used in the statement is "formally
smooth", the citation is a cross-reference slip and Definition 37.11.1 is the intended reading.

Two hypotheses are carried, neither of which is the conclusion.

`h0D0F` is the scheme-level implication (3) ⟹ (1) of [Stacks Project, Tag 0D0F]: a morphism of
schemes whose maps on sections over affine opens are formally smooth has the infinitesimal
lifting property. It is used only for the forward implications, through
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_formallySmoothScheme`, and it is a statement
about morphisms of schemes which mentions neither algebraic spaces nor charts.

`hGlue` is step (II): a morphism of algebraic spaces whose infinitesimal lifting problems are
solvable étale-locally in the sense of
`AlgebraicGeometry.Space.FormallySmoothEtaleLocally` is formally smooth. In the Stacks proof
this is the triviality of a pseudo-torsor, [Stacks Project, Tag 03AJ], applied to the sheaf of
lifts of [Stacks Project, Tag 061A] under the action of [Stacks Project, Tag 061C], and it
rests on the local projectivity of `Ω_{X/Y}` — [Stacks Project, Tag 061I] together with
[Stacks Project, Tag 060Y] and [Stacks Project, Tag 060S] — and on the resulting vanishing of
the first étale cohomology of `Hom(a^*Ω_{X/Y}, C_{T/T'})`, [Stacks Project, Tag 061J]. Of
those, the sheaf of relative differentials of an algebraic space and its local projectivity are
both available now: `AlgebraicGeometry.Space.sheafOfDifferentials` of
`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentials.lean:148` is [Stacks Project,
Tag 04CT], and [Stacks Project, Tag 061I] is
`AlgebraicGeometry.Space.isLocallyProjective_sheafOfDifferentials` of
`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsLocallyProjective.lean`. What is still
missing is the étale cohomology of a quasi-coherent sheaf on an algebraic space, and hence
[Stacks Project, Tag 061J]; `hGlue` remains carried for that reason.

`hGlue` is strictly weaker than any of the three conditions of Tag 061K. It has a non-trivial
hypothesis, `FormallySmoothEtaleLocally`, which on its own gives no lift over the thickening,
and producing that hypothesis from condition (3) is the entire content of step (I) and is
proved here: `AlgebraicGeometry.Space.formallySmooth_chart_comp_of_formallySmoothScheme`
transports formal smoothness of `ψ` into the site by
`AlgebraicGeometry.Space.formallySmooth_yoneda_map_of_formallySmoothScheme` and composes it
with formal étaleness of the chart of the target — Tags 04AL and 049T — and part (4) of
[Stacks Project, Tag 04CY],
`AlgebraicGeometry.Space.exists_etale_affine_local_lift`, turns the resulting formally smooth
composite into local lifts. Tag 04CY itself descends only formal unramifiedness and formal
étaleness along a surjective étale transformation, which is why the converse here cannot be
assembled the way `AlgebraicGeometry.Space.formallyEtale_of_surjectiveEtaleChart` is: formal
smoothness has no uniqueness statement to make the local lifts agree on overlaps.

The chart of the target is not required to be surjective by the converse; only the chart of
the source is, since it is the surjectivity used to make the local lifts cover the thickening.
The surjectivity of the chart of the target is therefore carried in the statement of condition
(3) for faithfulness to the tag and discarded in the proof.

## References

* [Stacks Project, Tag 02H0](https://stacks.math.columbia.edu/tag/02H0)
* [Stacks Project, Tag 02H8](https://stacks.math.columbia.edu/tag/02H8)
* [Stacks Project, Tag 02X1](https://stacks.math.columbia.edu/tag/02X1)
* [Stacks Project, Tag 03AJ](https://stacks.math.columbia.edu/tag/03AJ)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 049S](https://stacks.math.columbia.edu/tag/049S)
* [Stacks Project, Tag 049T](https://stacks.math.columbia.edu/tag/049T)
* [Stacks Project, Tag 04AL](https://stacks.math.columbia.edu/tag/04AL)
* [Stacks Project, Tag 04CY](https://stacks.math.columbia.edu/tag/04CY)
* [Stacks Project, Tag 04G4](https://stacks.math.columbia.edu/tag/04G4)
* [Stacks Project, Tag 060S](https://stacks.math.columbia.edu/tag/060S)
* [Stacks Project, Tag 060Y](https://stacks.math.columbia.edu/tag/060Y)
* [Stacks Project, Tag 061A](https://stacks.math.columbia.edu/tag/061A)
* [Stacks Project, Tag 061C](https://stacks.math.columbia.edu/tag/061C)
* [Stacks Project, Tag 061H](https://stacks.math.columbia.edu/tag/061H)
* [Stacks Project, Tag 061I](https://stacks.math.columbia.edu/tag/061I)
* [Stacks Project, Tag 061J](https://stacks.math.columbia.edu/tag/061J)
* [Stacks Project, Tag 061K](https://stacks.math.columbia.edu/tag/061K)
* [Stacks Project, Tag 0D0F](https://stacks.math.columbia.edu/tag/0D0F)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Étale-local formal smoothness.** A transformation `f : X ⟶ Y` of presheaves on the big
fppf site over `S` is *étale-locally formally smooth* when every infinitesimal lifting problem
for `f` — a square-zero closed immersion `i : T ⟶ T'` of affine objects of the site together
with sections `x` of `X` over `T` and `y` of `Y` over `T'` agreeing under `f` — admits, over
every point of `T`, a solution on an affine object étale over `T'` whose image contains that
point: a section `z` of `X` lying over `y` and agreeing with `x` on every common refinement.

This is the conclusion of part (4) of [Stacks Project, Tag 04CY], and step (I) of the Stacks
proof of the implication (3) ⟹ (1) of [Stacks Project, Tag 061K]. It is weaker than formal
smoothness, which asks for a single solution over `T'` itself. -/
abbrev FormallySmoothEtaleLocally {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) : Prop :=
  ∀ (T T' : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj T) →
    IsAffine ((BigFppfOver.toScheme B S hS).obj T') → ∀ i : T ⟶ T',
      IsSquareZeroClosedImmersion B S hS i → ∀ (x : X.obj (op T)) (y : Y.obj (op T')),
        f.app (op T) x = Y.map i.op y →
        ∀ t : (BigFppfOver.toScheme B S hS).obj T,
          ∃ (U' : BigFppfOver B S hS) (j : U' ⟶ T') (z : X.obj (op U')),
            IsAffine ((BigFppfOver.toScheme B S hS).obj U') ∧
            Etale ((BigFppfOver.toScheme B S hS).map j) ∧
            (∃ u : (BigFppfOver.toScheme B S hS).obj U',
              ((BigFppfOver.toScheme B S hS).map j).base u =
                ((BigFppfOver.toScheme B S hS).map i).base t) ∧
            f.app (op U') z = Y.map j.op y ∧
            ∀ (W : BigFppfOver B S hS) (p : W ⟶ T) (q : W ⟶ U'),
              p ≫ i = q ≫ j → X.map p.op x = X.map q.op z

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Condition (2) of Stacks 061K makes the chart of the source formally smooth over the
target.** Let `a : yoneda.obj U ⟶ X` and `b : yoneda.obj V ⟶ Y` be étale charts fitting in a
commuting square over `ψ : U ⟶ V`. If the morphism of schemes underlying `ψ` is formally
smooth, then the composite `a ≫ f` is formally smooth.

The morphism `yoneda.map ψ` of representable presheaves is formally smooth by
`AlgebraicGeometry.Space.formallySmooth_yoneda_map_of_formallySmoothScheme`, the chart `b` is
formally étale by Tag 04AL hence formally smooth by Tag 04G4, and Tag 049T composes them; the
square identifies the composite with `a ≫ f`. -/
theorem formallySmooth_chart_comp_of_formallySmoothScheme {f : X ⟶ Y}
    {U V : BigFppfOver B S hS} {a : yoneda.obj U ⟶ X} {b : yoneda.obj V ⟶ Y} {ψ : U ⟶ V}
    (hb : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b)
    (hsq : a ≫ f = yoneda.map ψ ≫ b)
    (hψ : Stacks.Smooth.FormallySmoothScheme ((BigFppfOver.toScheme B S hS).map ψ)) :
    FormallySmooth (a ≫ f) := by
  rw [hsq]
  exact FormallySmooth.comp _ _ (formallySmooth_yoneda_map_of_formallySmoothScheme hψ)
    ((formallyEtale_iff_formallySmooth_and_formallyUnramified b).mp
      (formallyEtale_of_etale B S hS b hb)).1

/-- **Stacks 061K, step (I) of the implication (3) ⟹ (1).** Let `f : X ⟶ Y` be a morphism of
presheaves on the big fppf site over `S`, let `a : yoneda.obj U ⟶ X` be a surjective étale
chart, let `b : yoneda.obj V ⟶ Y` be an étale chart and let `ψ : U ⟶ V` make the square
commute. If the morphism of schemes underlying `ψ` is formally smooth, then `f` is
étale-locally formally smooth.

The composite `a ≫ f` is formally smooth by
`AlgebraicGeometry.Space.formallySmooth_chart_comp_of_formallySmoothScheme`, and part (4) of
[Stacks Project, Tag 04CY] — `AlgebraicGeometry.Space.exists_etale_affine_local_lift` — turns a
formally smooth composite in a representable, surjective, étale situation into lifts over an
affine étale neighbourhood of every point. No hypothesis beyond condition (3) is used. -/
theorem formallySmoothEtaleLocally_of_surjectiveEtaleChart {f : X ⟶ Y}
    {U V : BigFppfOver B S hS} (a : yoneda.obj U ⟶ X) (b : yoneda.obj V ⟶ Y) (ψ : U ⟶ V)
    (ha : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hb : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b)
    (haSurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hsq : a ≫ f = yoneda.map ψ ≫ b)
    (hψ : Stacks.Smooth.FormallySmoothScheme ((BigFppfOver.toScheme B S hS).map ψ)) :
    FormallySmoothEtaleLocally B S hS f := by
  intro T T' _hT hT' i hi x y hxy t
  exact exists_etale_affine_local_lift
    { B := B, S := S, hS := hS, F := yoneda.obj U, G := X, H := Y, a := a, b := f
      representable_a := ha.1, surjective_a := haSurj, etale_a := ha }
    T T' i hT' hi x y hxy
    (formallySmooth_chart_comp_of_formallySmoothScheme B S hS hb hsq hψ) t

/-- A formally smooth transformation is étale-locally formally smooth: the solution over the
thickening itself serves on the identity neighbourhood. -/
theorem formallySmoothEtaleLocally_of_formallySmooth {f : X ⟶ Y} (hf : FormallySmooth f) :
    FormallySmoothEtaleLocally B S hS f := by
  intro T T' hT hT' i hi x y hxy t
  obtain ⟨z, hz₁, hz₂⟩ := hf T T' hT hT' i hi x y hxy
  refine ⟨T', 𝟙 T', z, hT', ?_, ⟨((BigFppfOver.toScheme B S hS).map i).base t, ?_⟩, ?_, ?_⟩
  · have : Etale (𝟙 ((BigFppfOver.toScheme B S hS).obj T')) := inferInstance
    simpa using this
  · simp
  · simpa using hz₂
  · intro W p q hpq
    rw [Category.comp_id] at hpq
    subst hpq
    rw [← ExtendingFunctors.map_map_apply, hz₁]

/-- **Stacks 061K, the implication (3) ⟹ (1).** Let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S` admitting a commuting square of étale scheme charts whose chart of the source
is surjective and whose morphism of schemes `ψ` is formally smooth. If every étale-locally
formally smooth morphism of algebraic spaces over `S` is formally smooth, then `f` is formally
smooth.

Step (I) of the Stacks proof is
`AlgebraicGeometry.Space.formallySmoothEtaleLocally_of_surjectiveEtaleChart` and is
unconditional; the hypothesis `hGlue` is step (II), the triviality of the pseudo-torsor of
lifts, which is [Stacks Project, Tag 03AJ] together with the vanishing of the first étale
cohomology of `Hom(a^*Ω_{X/Y}, C_{T/T'})` on an affine scheme, [Stacks Project, Tag 061J]. -/
theorem formallySmooth_of_surjectiveEtaleChart
    (hGlue : ∀ {X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X' ⟶ Y'),
      IsAlgebraicSpace B S hS X' → IsAlgebraicSpace B S hS Y' →
      FormallySmoothEtaleLocally B S hS g → FormallySmooth g)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    {U V : BigFppfOver B S hS} (a : yoneda.obj U ⟶ X) (b : yoneda.obj V ⟶ Y) (ψ : U ⟶ V)
    (ha : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hb : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b)
    (haSurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hsq : a ≫ f = yoneda.map ψ ≫ b)
    (hψ : Stacks.Smooth.FormallySmoothScheme ((BigFppfOver.toScheme B S hS).map ψ)) :
    FormallySmooth f :=
  hGlue f hX hY
    (formallySmoothEtaleLocally_of_surjectiveEtaleChart B S hS a b ψ ha hb haSurj hsq hψ)

/-- **Stacks 061K, the equivalence of (1) and (2).** A morphism of algebraic spaces over `S` is
formally smooth exactly when the morphism of schemes underlying every commuting square of étale
scheme charts is formally smooth, granted the scheme-level implication (3) ⟹ (1) of
[Stacks Project, Tag 0D0F] and the triviality of the pseudo-torsor of lifts. -/
@[stacks 061K
  "condition (2), granted Stacks 0D0F (3) ⟹ (1) and the pseudo-torsor triviality of 03AJ"]
theorem formallySmooth_iff_etaleCharts
    (h0D0F : ∀ {X' Y' : Scheme.{u}} (g : X' ⟶ Y'),
      Stacks.Smooth.FormallySmoothAffineLocally g → Stacks.Smooth.FormallySmoothScheme g)
    (hGlue : ∀ {X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X' ⟶ Y'),
      IsAlgebraicSpace B S hS X' → IsAlgebraicSpace B S hS Y' →
      FormallySmoothEtaleLocally B S hS g → FormallySmooth g)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    FormallySmooth f ↔
      HoldsOnEveryEtaleChart B S hS (@Stacks.Smooth.FormallySmoothScheme.{u}) f := by
  refine ⟨holdsOnEveryEtaleChart_formallySmoothScheme h0D0F, fun hall ↦ ?_⟩
  obtain ⟨V, b, hbSurj, hbEtale⟩ := hY.exists_atlas
  obtain ⟨U, a, ψ, hdiag, haSurj, haEtale⟩ :=
    exists_surjective_etale_presentation_lift B S hS hX hY f V b hbSurj hbEtale
  exact formallySmooth_of_surjectiveEtaleChart B S hS hGlue hX hY a b ψ haEtale hbEtale haSurj
    hdiag (hall U V a b ψ haEtale hbEtale hdiag.symm)

/-- **Stacks 061K, the equivalence of (1) and (3).** A morphism of algebraic spaces over `S` is
formally smooth exactly when there is one commuting square of étale scheme charts, both chart
maps surjective, whose underlying morphism of schemes is formally smooth, granted the
scheme-level implication (3) ⟹ (1) of [Stacks Project, Tag 0D0F] and the triviality of the
pseudo-torsor of lifts. -/
@[stacks 061K
  "condition (3), granted Stacks 0D0F (3) ⟹ (1) and the pseudo-torsor triviality of 03AJ"]
theorem formallySmooth_iff_surjectiveEtaleChart
    (h0D0F : ∀ {X' Y' : Scheme.{u}} (g : X' ⟶ Y'),
      Stacks.Smooth.FormallySmoothAffineLocally g → Stacks.Smooth.FormallySmoothScheme g)
    (hGlue : ∀ {X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X' ⟶ Y'),
      IsAlgebraicSpace B S hS X' → IsAlgebraicSpace B S hS Y' →
      FormallySmoothEtaleLocally B S hS g → FormallySmooth g)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    FormallySmooth f ↔
      ∃ (U V : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X) (b : yoneda.obj V ⟶ Y) (ψ : U ⟶ V),
        (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty
          Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf a ∧
        (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty
          Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf b ∧
        (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u} : MorphismProperty
          Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf a ∧
        (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u} : MorphismProperty
          Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf b ∧
        yoneda.map ψ ≫ b = a ≫ f ∧
        Stacks.Smooth.FormallySmoothScheme ((BigFppfOver.toScheme B S hS).map ψ) := by
  constructor
  · intro hf
    obtain ⟨V, b, hbSurj, hbEtale⟩ := hY.exists_atlas
    obtain ⟨U, a, ψ, hdiag, haSurj, haEtale⟩ :=
      exists_surjective_etale_presentation_lift B S hS hX hY f V b hbSurj hbEtale
    exact ⟨U, V, a, b, ψ, haEtale, hbEtale, haSurj, hbSurj, hdiag.symm,
      holdsOnEveryEtaleChart_formallySmoothScheme h0D0F hf U V a b ψ haEtale hbEtale hdiag.symm⟩
  · rintro ⟨U, V, a, b, ψ, ha, hb, haSurj, -, hdiag, hψ⟩
    exact formallySmooth_of_surjectiveEtaleChart B S hS hGlue hX hY a b ψ ha hb haSurj
      hdiag.symm hψ

/-- **Stacks 061K, the equivalence of (1) and (3) through Stacks 03MJ.** The same equivalence
with condition (3) read as `AlgebraicGeometry.Space.HoldsOnSurjectiveEtaleChart`, the form in
which the forward implication is stated: only the chart of the source is required to be
surjective, which is all the converse uses. -/
theorem formallySmooth_iff_holdsOnSurjectiveEtaleChart
    (h0D0F : ∀ {X' Y' : Scheme.{u}} (g : X' ⟶ Y'),
      Stacks.Smooth.FormallySmoothAffineLocally g → Stacks.Smooth.FormallySmoothScheme g)
    (hGlue : ∀ {X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X' ⟶ Y'),
      IsAlgebraicSpace B S hS X' → IsAlgebraicSpace B S hS Y' →
      FormallySmoothEtaleLocally B S hS g → FormallySmooth g)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    FormallySmooth f ↔
      HoldsOnSurjectiveEtaleChart B S hS (@Stacks.Smooth.FormallySmoothScheme.{u}) f := by
  refine ⟨holdsOnSurjectiveEtaleChart_formallySmoothScheme h0D0F hX hY, ?_⟩
  rintro ⟨U, V, a, b, ψ, ha, hb, haSurj, hdiag, hψ⟩
  exact formallySmooth_of_surjectiveEtaleChart B S hS hGlue hX hY a b ψ ha hb haSurj
    hdiag.symm hψ

end AlgebraicGeometry.Space

end
