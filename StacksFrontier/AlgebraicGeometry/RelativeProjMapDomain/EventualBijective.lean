module

public import StacksFrontier.AlgebraicGeometry.RelativeProjChain.EventualBijective
public import StacksFrontier.AlgebraicGeometry.RelativeProjMapDomain.EventualSurjective

/-!
# Homomorphisms of graded algebras bijective in all large degrees

Let `S` be a scheme, let `A` and `B` be quasi-coherent graded `𝒪_S`-algebras and let
`ψ : A ⟶ B` be a homomorphism between them. Write `X = Proj_S(A)` and `Y = Proj_S(B)`, let
`U(ψ) ⊆ Y` be the open on which `ψ` induces a morphism and let `r_ψ : U(ψ) ⟶ X` be that
morphism.

This file proves Tag 07ZJ: if `A_d → B_d` is an isomorphism for every sufficiently large `d`,
then `U(ψ) = Y`, the morphism `r_ψ` is an isomorphism, and the comparison maps on the twists are
isomorphisms.

As in Tag 07ZI the three assertions are read in the charts. Over an affine open `V` of the base
`ψ` induces a homomorphism `Γ(V, A) → Γ(V, B)` of graded rings which is bijective in all large
degrees, and the absolute Tag 07ZE applies to it.

## Main definitions

Everything below lives in the namespace
`Stacks.AlgebraicGeometry.RelativeProjMapDomain`.

* `EventuallyBijectiveOnSections`: the hypothesis read on sections — over every open of the base
  the induced maps on homogeneous sections are bijective in all sufficiently large degrees.

## Main results

* `eventuallyBijectiveOnSections_of_eventually_isIso`: a degreewise isomorphism in all large
  degrees is bijective on the sections over every open in all large degrees.
* `relativeMapDomain_eq_top_of_eventually_isIso`: Tag 07ZJ (1), `U(ψ) = Proj_S(B)`.
* `isIso_relativeMapHom_of_eventually_isIso`: Tag 07ZJ (2), the morphism `r_ψ` is an
  isomorphism.
* `isIso_chart_twistMap_of_eventually_isIso`: Tag 07ZJ (3), the comparison maps on the twists
  are isomorphisms over every chart of the base.

## Implementation notes

The hypothesis is stated as `∀ᶠ d : ℕ in atTop, IsIso (ψ.app d)`, an isomorphism of sheaves of
modules in each large degree. Unlike the surjective case this passes to sections over an
*arbitrary* open and needs no quasi-coherence: an isomorphism of sheaves of modules is an
isomorphism on sections over every open, and an isomorphism in a concrete category is bijective.

Assertion (3) is stated here over each chart of the base, for the comparison maps of Tag 01MY,
which is the same content read chart by chart: the maps `θ_n` of Tag 07ZG (3) are glued from
exactly these chart-level comparison maps, by
`Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwistMap_chart`. The assertion about `θ_n` itself
is `Stacks.AlgebraicGeometry.Tag07ZGTwist.isIso_relativeTwistMap_of_eventually_isIso`, which
carries the chart-level statement below along the cover of `U(ψ)` by its pieces.

Assertion (2) is obtained from the affine-local transfer principle
`Stacks.AlgebraicGeometry.Tag07ZGMorphism.of_forall_chart` applied to the morphism property
`CategoryTheory.MorphismProperty.isomorphisms`, which is Zariski-local at the target.

## References

* [Stacks Project, Tag 07ZJ](https://stacks.math.columbia.edu/tag/07ZJ)
* [Stacks Project, Tag 07ZG](https://stacks.math.columbia.edu/tag/07ZG)
* [Stacks Project, Tag 07ZE](https://stacks.math.columbia.edu/tag/07ZE)
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

/-- **The hypothesis of Tag 07ZJ, read on sections.** Over every open of the base and in all
sufficiently large degrees, the induced map on homogeneous sections is bijective. -/
public def EventuallyBijectiveOnSections (ψ : SheafGradedAlgebraHom A B) : Prop :=
  ∀ U : S.Opens, ∀ᶠ d : ℕ in atTop, Function.Bijective (ψ.sectionPieceHom U d)

variable (ψ : SheafGradedAlgebraHom A B)

/-- An isomorphism of sheaves of modules is bijective on the sections over every open: it is an
isomorphism there, and an isomorphism of abelian groups is bijective. No quasi-coherence is
needed. -/
public theorem bijective_sectionPieceHom_of_isIso {n : ℕ} (hn : IsIso (ψ.app (n : ℤ)))
    (U : S.Opens) : Function.Bijective (ψ.sectionPieceHom U n) :=
  ConcreteCategory.bijective_of_isIso ((ψ.app (n : ℤ)).app U)

/-- A homomorphism of graded algebras which is an isomorphism in all sufficiently large degrees
is bijective on sections over every open of the base in all sufficiently large degrees. -/
public theorem eventuallyBijectiveOnSections_of_eventually_isIso
    (hψ : ∀ᶠ d : ℕ in atTop, IsIso (ψ.app (d : ℤ))) :
    EventuallyBijectiveOnSections ψ :=
  fun U => hψ.mono fun _ hd => bijective_sectionPieceHom_of_isIso ψ hd U

/-- Bijectivity on homogeneous sections in a single degree gives bijectivity of that graded
component of the induced homomorphism of section rings.

Surjectivity is the same argument as in the surjective case; injectivity is injectivity of the
inclusion of a homogeneous summand into the direct sum. -/
public theorem bijective_gradedAddHom_of_bijective_sectionPieceHom {U : S.Opens} {d : ℕ}
    (h : Function.Bijective (ψ.sectionPieceHom U d)) :
    Function.Bijective (GradedRingHom.gradedAddHom (ψ.sectionHom U) d) := by
  refine ⟨fun x y hxy => ?_, surjective_gradedAddHom_of_surjective_sectionPieceHom ψ h.2⟩
  obtain ⟨-, a, rfl⟩ := x
  obtain ⟨-, b, rfl⟩ := y
  have h0 : ψ.sectionHom U (DirectSum.of (A.sectionPieces U) d a) =
      ψ.sectionHom U (DirectSum.of (A.sectionPieces U) d b) := congrArg Subtype.val hxy
  rw [ψ.sectionHom_of U a, ψ.sectionHom_of U b] at h0
  exact Subtype.ext
    (congrArg (DirectSum.of (A.sectionPieces U) d) (h.1 (DirectSum.of_injective d h0)))

/-- Over an affine open of the base the induced homomorphism of graded rings of sections is
bijective on homogeneous components of all sufficiently large degree. This is the hypothesis of
the absolute Tag 07ZE. -/
public theorem eventually_bijective_gradedAddHom
    (hψ : ∀ᶠ d : ℕ in atTop, IsIso (ψ.app (d : ℤ))) (V : S.Opens) :
    ∀ᶠ d : ℕ in atTop,
      Function.Bijective (GradedRingHom.gradedAddHom (ψ.sectionHom V) d) :=
  (eventuallyBijectiveOnSections_of_eventually_isIso ψ hψ V).mono fun _ hd =>
    bijective_gradedAddHom_of_bijective_sectionPieceHom ψ hd

/-! ### The domain of definition -/

/-- Over an affine open of the base the induced morphism of projective spectra is defined
everywhere: this is Tag 07ZE (1) applied to the homomorphism of graded rings of sections. -/
public theorem chartDomain_eq_top_of_eventually_isIso
    (hψ : ∀ᶠ d : ℕ in atTop, IsIso (ψ.app (d : ℤ))) (V : S.Opens) :
    ψ.chartDomain V = ⊤ :=
  RelativeProjChain.mapDomain_eq_top_of_eventually_bijective (A.grading V) (B.grading V)
    (ψ.sectionHom V) (eventually_bijective_gradedAddHom ψ hψ V)

/-- **Stacks 07ZJ (1).** If `A_d → B_d` is an isomorphism for all sufficiently large `d`, then
`ψ` induces a morphism on the whole of the relative projective spectrum of `B`:
`U(ψ) = Proj_S(B)`.

An open of the relative projective spectrum is determined by its inverse images under the charts
over the affine opens of the base, and over each such chart the inverse image of `U(ψ)` is the
absolute domain of definition of the induced homomorphism of graded rings of sections, which is
everything by Tag 07ZE. -/
public theorem relativeMapDomain_eq_top_of_eventually_isIso
    (hψ : ∀ᶠ d : ℕ in atTop, IsIso (ψ.app (d : ℤ))) :
    ψ.relativeMapDomain = ⊤ :=
  (ψ.relativeMapDomain_unique ⊤ fun V _ =>
    (chartDomain_eq_top_of_eventually_isIso ψ hψ V).symm).symm

/-! ### The isomorphism -/

/-- **Stacks 07ZJ (2).** If `A_d → B_d` is an isomorphism for all sufficiently large `d`, then
the morphism `r_ψ : U(ψ) ⟶ Proj_S(A)` of Tag 07ZG is an isomorphism.

Being an isomorphism is Zariski-local at the target, and the charts of `Proj_S(A)` over the
affine opens of the base cover it and pull `r_ψ` back to the absolute morphisms of Tag 01MY,
which are isomorphisms by Tag 07ZE. -/
public theorem isIso_relativeMapHom_of_eventually_isIso
    (hψ : ∀ᶠ d : ℕ in atTop, IsIso (ψ.app (d : ℤ))) :
    IsIso (Tag07ZGMorphism.relativeMapHom ψ) :=
  Tag07ZGMorphism.of_forall_chart ψ (P := MorphismProperty.isomorphisms Scheme.{u}) fun V =>
    RelativeProjChain.isIso_mapHom_of_eventually_bijective (A.grading V.1) (B.grading V.1)
      (ψ.sectionHom V.1) (eventually_bijective_gradedAddHom ψ hψ V.1)

/-! ### The maps on twists -/

/-- **Stacks 07ZJ (3), chart by chart.** If `A_d → B_d` is an isomorphism for all sufficiently
large `d`, then over every affine open `V` of the base the comparison map of Tag 01MY on the
`n`-th twist, attached to the induced homomorphism of graded rings of sections over `V`, is an
isomorphism.

Assertion (3) of Tag 07ZJ is about the maps `r_ψ^*𝒪_X(n) → 𝒪_{U(ψ)}(n)` between the twists of
the two relative projective spectra; those are glued from exactly the comparison maps appearing
here, one for each chart of the base, so this is that assertion read in the charts. -/
public theorem isIso_chart_twistMap_of_eventually_isIso
    (hψ : ∀ᶠ d : ℕ in atTop, IsIso (ψ.app (d : ℤ))) (V : S.Opens) (n : ℤ) :
    IsIso
      ((ProjTwistCompare.projMapData (A.grading V) (B.grading V) (ψ.sectionHom V)).twistMap n) :=
  RelativeProjChain.isIso_projMapData_twistMap_of_eventually_bijective (A.grading V)
    (B.grading V) (ψ.sectionHom V) (eventually_bijective_gradedAddHom ψ hψ V) n

end Stacks.AlgebraicGeometry.RelativeProjMapDomain

end
