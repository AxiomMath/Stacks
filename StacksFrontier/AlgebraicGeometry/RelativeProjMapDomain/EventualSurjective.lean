module

public import StacksFrontier.AlgebraicGeometry.Morphism.ChartPullback
public import StacksFrontier.AlgebraicGeometry.ProjTwistEpi.Basic
public import StacksFrontier.AlgebraicGeometry.ProjTwistMono.Assembly
public import StacksFrontier.AlgebraicGeometry.RelativeProjBridge.GeneratedInDegreeOne
public import StacksFrontier.AlgebraicGeometry.RelativeProjChain.EventualSurjective
public import StacksFrontier.AlgebraicGeometry.SectionEpiAffine.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Homomorphisms of graded algebras surjective in all large degrees

Let `S` be a scheme, let `A` and `B` be quasi-coherent graded `𝒪_S`-algebras and let
`ψ : A ⟶ B` be a homomorphism between them. Write `X = Proj_S(A)` and `Y = Proj_S(B)`, let
`U(ψ) ⊆ Y` be the open on which `ψ` induces a morphism and let `r_ψ : U(ψ) ⟶ X` be that
morphism.

This file proves Tags 07ZI and 07ZK: if `A_d → B_d` is surjective for every sufficiently large
`d`, then `U(ψ) = Y` and `r_ψ` is a closed immersion, and the comparison maps on the twists are
surjective; if moreover `A` is generated in degree one over `A_0` over every affine open of the
base, then those comparison maps are isomorphisms.

Everything is read in the charts. Over an affine open `V` of the base the two algebras have
graded rings of sections `Γ(V, A)` and `Γ(V, B)`, and `ψ` induces a homomorphism between them
which is again surjective in all large degrees, because `Γ(V, -)` is exact on quasi-coherent
modules over an affine open. The absolute statements of Tags 01N0 and 01N1 then apply to that
homomorphism, and the affine-local description of `U(ψ)` and of `r_ψ` globalizes them.

## Main definitions

Everything below lives in the namespace
`Stacks.AlgebraicGeometry.RelativeProjMapDomain`.

* `EventuallySurjectiveOnAffineSections`: the hypothesis read on sections — over every affine
  open of the base the induced maps on homogeneous sections are surjective in all sufficiently
  large degrees.

## Main results

* `eventuallySurjectiveOnAffineSections_of_eventually_epi`: **the hypothesis bridge.** A
  degreewise epimorphism in all large degrees is surjective on the sections over every affine
  open in all large degrees.
* `relativeMapDomain_eq_top_of_eventually_epi`: Tags 07ZI (1) and 07ZK (1),
  `U(ψ) = Proj_S(B)`.
* `isClosedImmersion_relativeMapHom_of_eventually_epi`: Tags 07ZI (2) and 07ZK (2), the morphism
  `r_ψ` is a closed immersion.
* `epi_chart_twistMap_of_eventually_epi`: Tag 07ZI (3), the comparison maps on the twists are
  surjective over every chart of the base.
* `isIso_chart_twistMap_of_generatedInDegreeOne`: Tag 07ZK (3), those comparison maps are
  isomorphisms once `A` is generated in degree one.

## Implementation notes

The hypothesis is stated as `∀ᶠ d : ℕ in atTop, Epi (ψ.app d)`, an epimorphism of sheaves of
modules in each large degree, which is the faithful reading of "`A_d → B_d` is surjective for
`d ≫ 0`". Its sections-level consequence needs quasi-coherence of the two pieces, which is part
of the data of a graded algebra, and is the content of
`Stacks.SectionEpiAffine.surjective_app_of_isAffineOpen`: on an affine open the global sections
functor is exact on quasi-coherent modules. There is no converse here, and none is needed: an
epimorphism of sheaves is only locally surjective, and it is the affine opens that repair this.

Assertion (3) of Tag 07ZI speaks of the maps `r_ψ^*𝒪_X(n) → 𝒪_{U(ψ)}(n)` between the twists of
the two relative projective spectra. Those maps exist —
`Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwistMap` — and they are glued from exactly the
comparison maps of Tag 01MY appearing below, one for each chart of the base, by
`Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwistMap_chart`. Assertion (3) is stated here over
each chart of the base, which is the same content read chart by chart; the assertions about those
maps themselves are `Stacks.AlgebraicGeometry.Tag07ZGTwist.epi_relativeTwistMap_of_eventually_epi`
and `Stacks.AlgebraicGeometry.Tag07ZGTwist.isIso_relativeTwistMap_of_generatedInDegreeOne`, which
carry the chart-level statements below along the cover of `U(ψ)` by its pieces.

The parenthetical of Tag 07ZI — that the maps on twists are surjective but in general not
isomorphisms — is not formalized, exactly as its affine source Tag 01N0 is not: no
counterexample is recorded in this repository, and the positive content of Tag 07ZK is the
hypothesis under which they do become isomorphisms.

## References

* [Stacks Project, Tag 07ZI](https://stacks.math.columbia.edu/tag/07ZI)
* [Stacks Project, Tag 07ZK](https://stacks.math.columbia.edu/tag/07ZK)
* [Stacks Project, Tag 07ZG](https://stacks.math.columbia.edu/tag/07ZG)
* [Stacks Project, Tag 01N0](https://stacks.math.columbia.edu/tag/01N0)
* [Stacks Project, Tag 01N1](https://stacks.math.columbia.edu/tag/01N1)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Filter
open Stacks.AlgebraicGeometry.ProjShared
open Stacks.AlgebraicGeometry.ProjTwistChain
open Stacks.AlgebraicGeometry.RelativeProjBridge

namespace Stacks.AlgebraicGeometry.RelativeProjMapDomain

universe u

variable {S : Scheme.{u}} {A B : SheafGradedAlgebra S}

/-! ### The hypothesis on sections -/

/-- **The hypothesis of Tag 07ZI, read on sections.** Over every affine open of the base and in
all sufficiently large degrees, every homogeneous section of the target is the image of one of
the source. -/
public def EventuallySurjectiveOnAffineSections (ψ : SheafGradedAlgebraHom A B) : Prop :=
  ∀ U : S.Opens, IsAffineOpen U →
    ∀ᶠ d : ℕ in atTop, Function.Surjective (ψ.sectionPieceHom U d)

variable (ψ : SheafGradedAlgebraHom A B)

/-- An epimorphism of quasi-coherent sheaves of modules is surjective on the sections over an
affine open. Both homogeneous pieces of a graded algebra are quasi-coherent, so this applies to
each degree of `ψ`. -/
public theorem surjective_sectionPieceHom_of_epi {n : ℕ} (hn : Epi (ψ.app (n : ℤ)))
    {U : S.Opens} (hU : IsAffineOpen U) :
    Function.Surjective (ψ.sectionPieceHom U n) := by
  have := hn
  intro b
  obtain ⟨a, ha⟩ :=
    Stacks.SectionEpiAffine.surjective_app_of_isAffineOpen S (ψ.app (n : ℤ)) U hU b
  exact ⟨a, ha⟩

/-- **The hypothesis bridge.** A homomorphism of graded algebras which is an epimorphism in all
sufficiently large degrees is surjective on sections over every affine open of the base in all
sufficiently large degrees. -/
public theorem eventuallySurjectiveOnAffineSections_of_eventually_epi
    (hψ : ∀ᶠ d : ℕ in atTop, Epi (ψ.app (d : ℤ))) :
    EventuallySurjectiveOnAffineSections ψ :=
  fun _ hU => hψ.mono fun _ hd => surjective_sectionPieceHom_of_epi ψ hd hU

/-- Surjectivity on homogeneous sections in a single degree gives surjectivity of that graded
component of the induced homomorphism of section rings. -/
public theorem surjective_gradedAddHom_of_surjective_sectionPieceHom {U : S.Opens} {d : ℕ}
    (h : Function.Surjective (ψ.sectionPieceHom U d)) :
    Function.Surjective (GradedRingHom.gradedAddHom (ψ.sectionHom U) d) := by
  rintro ⟨_, b, rfl⟩
  obtain ⟨a, rfl⟩ := h b
  exact ⟨⟨_, A.of_mem_grading U a⟩, Subtype.ext (ψ.sectionHom_of U a)⟩

/-- Over an affine open of the base the induced homomorphism of graded rings of sections is
surjective on homogeneous components of all sufficiently large degree. This is the hypothesis in
the form the absolute Tags 01N0 and 01N1 want. -/
public theorem eventually_surjective_gradedAddHom
    (hψ : ∀ᶠ d : ℕ in atTop, Epi (ψ.app (d : ℤ))) {V : S.Opens} (hV : IsAffineOpen V) :
    ∀ᶠ d : ℕ in atTop,
      Function.Surjective (GradedRingHom.gradedAddHom (ψ.sectionHom V) d) :=
  (eventuallySurjectiveOnAffineSections_of_eventually_epi ψ hψ V hV).mono fun _ hd =>
    surjective_gradedAddHom_of_surjective_sectionPieceHom ψ hd

/-! ### The domain of definition -/

/-- Over an affine open of the base the induced morphism of projective spectra is defined
everywhere: this is Tag 01N1 (1) applied to the homomorphism of graded rings of sections. -/
public theorem chartDomain_eq_top_of_eventually_epi
    (hψ : ∀ᶠ d : ℕ in atTop, Epi (ψ.app (d : ℤ))) {V : S.Opens} (hV : IsAffineOpen V) :
    ψ.chartDomain V = ⊤ :=
  RelativeProjChain.mapDomain_eq_top_of_eventually_surjective (A.grading V) (B.grading V)
    (ψ.sectionHom V) (eventually_surjective_gradedAddHom ψ hψ hV)

/-- **Stacks 07ZI (1) and 07ZK (1).** If `A_d → B_d` is surjective for all sufficiently large
`d`, then `ψ` induces a morphism on the whole of the relative projective spectrum of `B`:
`U(ψ) = Proj_S(B)`.

An open of the relative projective spectrum is determined by its inverse images under the charts
over the affine opens of the base, and over each such chart the inverse image of `U(ψ)` is the
absolute domain of definition of the induced homomorphism of graded rings of sections, which is
everything by Tag 01N1. -/
@[ega "II 3.5.1" "more general"]
public theorem relativeMapDomain_eq_top_of_eventually_epi
    (hψ : ∀ᶠ d : ℕ in atTop, Epi (ψ.app (d : ℤ))) :
    ψ.relativeMapDomain = ⊤ :=
  (ψ.relativeMapDomain_unique ⊤ fun _ hV =>
    (chartDomain_eq_top_of_eventually_epi ψ hψ hV).symm).symm

/-! ### The closed immersion -/

/-- **Stacks 07ZI (2) and 07ZK (2).** If `A_d → B_d` is surjective for all sufficiently large
`d`, then the morphism `r_ψ : U(ψ) ⟶ Proj_S(A)` of Tag 07ZG is a closed immersion.

Being a closed immersion is Zariski-local at the target, and the charts of `Proj_S(A)` over the
affine opens of the base cover it and pull `r_ψ` back to the absolute morphisms of Tag 01MY,
which are closed immersions by Tag 01N1. -/
public theorem isClosedImmersion_relativeMapHom_of_eventually_epi
    (hψ : ∀ᶠ d : ℕ in atTop, Epi (ψ.app (d : ℤ))) :
    IsClosedImmersion (Tag07ZGMorphism.relativeMapHom ψ) :=
  Tag07ZGMorphism.of_forall_chart ψ (P := @IsClosedImmersion) fun V =>
    RelativeProjChain.isClosedImmersion_mapHom_of_eventually_surjective (A.grading V.1)
      (B.grading V.1) (ψ.sectionHom V.1) (eventually_surjective_gradedAddHom ψ hψ V.2)

/-! ### The maps on twists -/

/-- **Stacks 07ZI (3), chart by chart.** If `A_d → B_d` is surjective for all sufficiently large
`d`, then over every affine open `V` of the base the comparison map of Tag 01MY on the `n`-th
twist, attached to the induced homomorphism of graded rings of sections over `V`, is an
epimorphism.

Assertion (3) of Tag 07ZI is about the maps `r_ψ^*𝒪_X(n) → 𝒪_{U(ψ)}(n)` between the twists of
the two relative projective spectra; those are glued from exactly the comparison maps appearing
here, one for each chart of the base, so this is that assertion read in the charts. -/
public theorem epi_chart_twistMap_of_eventually_epi
    (hψ : ∀ᶠ d : ℕ in atTop, Epi (ψ.app (d : ℤ))) {V : S.Opens} (hV : IsAffineOpen V) (n : ℤ) :
    Epi ((ProjTwistCompare.projMapData (A.grading V) (B.grading V) (ψ.sectionHom V)).twistMap n) :=
  ProjTwistEpi.epi_projMapData_twistMap_of_eventually_surjective (A.grading V) (B.grading V)
    (ψ.sectionHom V) (eventually_surjective_gradedAddHom ψ hψ hV) n

/-- **Stacks 07ZK (3), chart by chart.** If moreover `A` is generated in degree one over `A_0`
over every affine open of the base, the comparison maps of the previous result are
isomorphisms.

Generation in degree one over an affine open `V` makes the graded ring of sections over `V`
generated by its degree-one part over its degree-zero part, which is the hypothesis of Tag 01N1's
third assertion. -/
public theorem isIso_chart_twistMap_of_generatedInDegreeOne
    (hψ : ∀ᶠ d : ℕ in atTop, Epi (ψ.app (d : ℤ)))
    (hgen : ∀ U : S.Opens, IsAffineOpen U → A.IsGeneratedInDegreeOneAt U)
    {V : S.Opens} (hV : IsAffineOpen V) (n : ℤ) :
    IsIso
      ((ProjTwistCompare.projMapData (A.grading V) (B.grading V) (ψ.sectionHom V)).twistMap n) :=
  ProjTwistMono.isIso_projMapData_twistMap (A.grading V) (B.grading V) (ψ.sectionHom V)
    (eventually_surjective_gradedAddHom ψ hψ hV) (A.adjoin_grading_one_eq_top V (hgen V hV)) n

end Stacks.AlgebraicGeometry.RelativeProjMapDomain

end
