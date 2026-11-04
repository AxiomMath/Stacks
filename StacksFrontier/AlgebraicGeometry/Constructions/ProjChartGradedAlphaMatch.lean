module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartCocycleMatch
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartGradedClauseTwo
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartGradedVeronese
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistAwayPiece

/-!
# The comparison `θ` of Tag 01NK and the isomorphism `α` of Tag 01N8 on the chart of `f`

Let `A = ⨁_{n ≥ 0} 𝒜 n` be a graded ring, `T` a scheme, `L` an invertible `𝒪_T`-module and
`ψ : A → Γ_*(T, L)` a graded map in the degreewise spelling
`Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections`, whose degree-`d` values generate
`L ^⊗ d` for some `d > 0`. Two objects of the same type are then available over `T`:

* the isomorphism `α : φ⁎𝒪_{U_d}(d) ≅ (L ^⊗ d) ^⊗ 1` of [Stacks, Tag 01N8] attached to the
  Veronese restriction `ψ|_{A^{(d)}}` and the morphism `φ` of that tag
  (`Stacks.AlgebraicGeometry.ProjChartCocycleMatch.alphaGlued`), and
* the chart-level comparison
  `θ_f : (A_f)_n ⟶ Γ(L ^⊗ n, V)`,   `x / f ^ j ↦ ψ(x) / ψ(f ^ j)`
  of [Stacks, Tag 01NK] (`Stacks.AlgebraicGeometry.ProjChartGradedDivision.chartSection`), for
  `f ∈ 𝒜 d` and `V` an open on which `ψ(f)` does not vanish.

This file reads `α` in `L ^⊗ d` rather than in `(L ^⊗ d) ^⊗ 1` and proves that the two agree on
the degree-`d` section of `f`.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjChartGradedAlphaMatch.alphaVeronese` — the isomorphism `α` of
  [Stacks, Tag 01N8] for `ψ|_{A^{(d)}}`, with its codomain `(L ^⊗ d) ^⊗ 1` rewritten as
  `L ^⊗ d` through `Stacks.AlgebraicGeometry.ProjVeroneseRestrict.powVeroneseIso` and
  `Stacks.TensorPowerAssoc.powCongrIso`.

## Main results

* `Stacks.AlgebraicGeometry.ProjChartGradedAlphaMatch.alphaVeronese_hom_app_top` — the
  normalisation of `α` in that spelling: it carries the pullback of the degree-`d` section of `f`
  to `ψ(f)`, for every `f ∈ 𝒜 d`.
* `Stacks.AlgebraicGeometry.ProjChartGradedAlphaMatch.chartSection_eq_alphaVeronese` — **`θ` and
  `α` agree on the degree-`d` section of `f`**: for `V` an open on which `ψ(f)` does not vanish,
  the value of `θ_f` on the fraction `f / 1` of `A_f`-degree `d` is the restriction to `V` of the
  value of `α` on the pullback of the degree-`d` section of `f`.

## Why this is the content of the clause `θ|_V = α`, and what of it is here

The fraction `f / 1` is the element of `(A_f)_d` that the degree-`d` section of `f` becomes under
the identification `Γ(D₊(f), 𝒪_X(d)) ≅ (A_f)_d`
(`Stacks.ProjectiveCohomology.sectionsTwistEquivAwayGrading` composed with
`AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeZeroLocalization_twistGrading_eq`), and the
degree-`d` sections of the `f ∈ 𝒜 d` are what both sides are pinned by: `α` is the unique
isomorphism carrying the pullback of each of them to `ψ(f)`
(`Stacks.AlgebraicGeometry.ProjChartAlphaInstance.eq_alpha`), and `θ_f` is determined on `f / 1`
by clause (2) of [Stacks, Tag 01NK]
(`Stacks.AlgebraicGeometry.ProjChartGradedClauseTwo.chartSection_mk_one`). So the identity below
is the clause `θ|_V = α` of the tag's final assertion, read on that one section.

It is *not* the equality of the two as maps. For that one needs `θ` assembled as a morphism of
graded `𝒪_T`-algebras out of `r_{L, ψ}^*(⨁_d 𝒪_X(d))`, which this development does not have (see
the module docstring of `StacksFrontier.AlgebraicGeometry.Constructions.ProjChartFullGradedGluing`),
or — on the chart alone — the `A_{(f)}`-semilinearity of the `α` side to match
`Stacks.AlgebraicGeometry.ProjChartGradedDivision.chartSection_smul` on the `θ` side, together
with the fact that `f / 1` generates `(A_f)_d` over `(A_f)_0`. Neither is proved here.

## Implementation notes

**The two spellings of the codomain of `α`.** [Stacks, Tag 01N8] is formalised for a
`Stacks.AlgebraicGeometry.ProjChartFromRatios.VeroneseSections` datum, whose values live in the
powers of one invertible module `L'`; for the Veronese restriction of `ψ` that `L'` is `L ^⊗ d`,
so `α` lands in `(L ^⊗ d) ^⊗ 1` while `θ_f` at `n = d` lands in `L ^⊗ d`. Composing with
`powVeroneseIso L d 1 : (L ^⊗ d) ^⊗ 1 ≅ L ^⊗ (d * 1)` and then with the transport of exponents
`powCongrIso L (d * 1 = d)` puts the two in one spelling. Both are composed into `α` itself rather
than applied to its value, so the statement of the agreement mentions only one isomorphism.

## References

* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
* [Stacks Project, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8)
* [Stacks Project, Tag 01M6](https://stacks.math.columbia.edu/tag/01M6)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj (integerGrading twistingSheaf)
open Stacks.AlgebraicGeometry.MorphismsIntoProj (pullbackTwist)
open Stacks.AlgebraicGeometry.ProjChartAlphaInstance (pullbackDegreeSection)
open Stacks.AlgebraicGeometry.ProjChartCocycleMatch (alphaGlued alphaGlued_hom_app_top)
open Stacks.AlgebraicGeometry.ProjChartFullGraded (GradedSections)
open Stacks.AlgebraicGeometry.ProjChartGradedClauseTwo (chartSection_mk_one)
open Stacks.AlgebraicGeometry.ProjChartGradedDivision (chartSection)
open Stacks.AlgebraicGeometry.ProjChartGradedVeronese (veroneseAt veroneseAt_pow gluedVeronese
  le_nonvanishingOpen_veroneseAt powCongr_app_toFun)
open Stacks.AlgebraicGeometry.ProjTwistAwayPiece (sectionsTwistEquivGradedPiece
  coe_sectionsTwistEquivGradedPiece_degreeSection)
open AlgebraicGeometry.ProjectiveSpectrum.Proj (degreeSection)
open Stacks.AlgebraicGeometry.ProjVeroneseRestrict (powVeroneseIso hom_app_inv_app)
open Stacks.GradedLocalization (gradedPiece)
open Stacks.NonvanishingOpen (nonvanishingOpen)
open Stacks.GradedSections (powCongrIso powCongrIso_hom)
open Stacks.TensorPowerTrivialize (resTop)
open Stacks.TensorPowers (natTensorPow)
open scoped Stacks.GradedLocalization

universe u w

namespace Stacks.AlgebraicGeometry.ProjChartGradedAlphaMatch

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {T : Scheme.{u}} {L : T.Modules}
  [Stacks.Ample.IsInvertibleModule T L] (ψ : GradedSections 𝒜 L) {d : ℕ} (hd : 0 < d)
  (hgen : ⨆ g : 𝒜 d, nonvanishingOpen T (natTensorPow L d) (ψ.toFun d g) = ⊤)

/-- **The isomorphism `α : φ⁎𝒪_{U_d}(d) ≅ L ^⊗ d` of [Stacks, Tag 01N8]** for the Veronese
restriction `ψ|_{A^{(d)}}` of a datum of graded sections, with its codomain read in `L ^⊗ d`
rather than in `(L ^⊗ d) ^⊗ 1`. -/
def alphaVeronese :
    pullbackTwist 𝒜 (gluedVeronese 𝒜 ψ hd hgen) (d : ℤ) ≅ natTensorPow L d :=
  alphaGlued 𝒜 (veroneseAt 𝒜 ψ d) hd (le_nonvanishingOpen_veroneseAt 𝒜 ψ) hgen ≪≫
    powVeroneseIso L d 1 ≪≫ powCongrIso L (Nat.mul_one d)

/-- **The normalisation of `α` in the spelling `L ^⊗ d`**: it carries the pullback of the
degree-`d` section of `f` to `ψ(f)`, for every `f ∈ 𝒜 d`.

The normalisation of `α` for the Veronese restriction is
`Stacks.AlgebraicGeometry.ProjChartCocycleMatch.alphaGlued_hom_app_top`, whose value is the
trivialising section `ψ|_{A^{(d)}}(f)` of the restriction; that section is `ψ(f)` read backwards
through `powVeroneseIso` by
`Stacks.AlgebraicGeometry.ProjChartGradedVeronese.veroneseAt_pow`, so composing `powVeroneseIso`
back in cancels, and the remaining transport of exponents is `d * 1 = d`. -/
theorem alphaVeronese_hom_app_top (f : A) (hf : f ∈ 𝒜 d) :
    (alphaVeronese 𝒜 ψ hd hgen).hom.app ⊤
        (pullbackDegreeSection 𝒜 (gluedVeronese 𝒜 ψ hd hgen) ⟨f, hf⟩)
      = ψ.toFun d ⟨f, hf⟩ := by
  have hfn : (f : A) ^ 1 ∈ 𝒜 (d * 1) := by
    rw [pow_one, Nat.mul_one]; exact hf
  have hfd : (f : A) ^ 1 ∈ 𝒜 d := by rw [pow_one]; exact hf
  have key : (alphaGlued 𝒜 (veroneseAt 𝒜 ψ d) hd
          (le_nonvanishingOpen_veroneseAt 𝒜 ψ) hgen).hom.app ⊤
        (pullbackDegreeSection 𝒜 (gluedVeronese 𝒜 ψ hd hgen) ⟨f, hf⟩)
      = (powVeroneseIso L d 1).inv.app ⊤ (ψ.toFun (d * 1) ⟨f ^ 1, hfn⟩) :=
    (alphaGlued_hom_app_top 𝒜 (veroneseAt 𝒜 ψ d) hd (le_nonvanishingOpen_veroneseAt 𝒜 ψ) hgen
      ⟨f, hf⟩).trans (veroneseAt_pow 𝒜 ψ hf 1 hfn)
  exact (congrArg (fun z => (powCongrIso L (Nat.mul_one d)).hom.app ⊤
        ((powVeroneseIso L d 1).hom.app ⊤ z)) key).trans
    ((congrArg (fun z => (powCongrIso L (Nat.mul_one d)).hom.app ⊤ z)
        (hom_app_inv_app (powVeroneseIso L d 1) (ψ.toFun (d * 1) ⟨f ^ 1, hfn⟩))).trans
      ((powCongr_app_toFun 𝒜 ψ (Nat.mul_one d) (f ^ 1) hfn hfd).trans
        (congrArg (ψ.toFun d) (Subtype.ext (pow_one f)))))

/-- **The comparison `θ` of [Stacks, Tag 01NK] and the isomorphism `α` of [Stacks, Tag 01N8] agree
on the degree-`d` section of `f`.** For `f ∈ 𝒜 d` and `V` an open of `T` on which `ψ(f)` does not
vanish, the value of the chart-level comparison `θ_f` on the fraction `f / 1` of `A_f`-degree `d`
is the restriction to `V` of the value of `α` on the pullback of the degree-`d` section of `f`.

Both are `ψ(f)|_V`: the left side by clause (2) of [Stacks, Tag 01NK] read on the chart of `f`
(`Stacks.AlgebraicGeometry.ProjChartGradedClauseTwo.chartSection_mk_one` at `n = d`, `x = f`), the
right side by `alphaVeronese_hom_app_top`. -/
-- Beyond what this declaration proves, recorded here rather than in the attribute: the fraction
-- f/1 is the element of (A_f)_d that the degree-d section of f becomes under the identification
-- Γ(D₊(f), 𝒪_X(d)) ≅ (A_f)_d; that identification is not composed in here, so the two descriptions
-- of the section sit on the two sides of the identity as they are. The equality of θ and α as maps
-- on the chart of f is ProjChartGradedAlphaMaps.eq_chartSection_of_smul_of_alpha, and as morphisms
-- of sheaves over any open V on which ψ(A_d) generates it is
-- ProjChartGradedThetaMoreover.moreover. The morphism half of the same final clause is
-- ProjChartGradedVeronese.homOfLE_glued_eq_gluedVeronese.
theorem chartSection_eq_alphaVeronese (f : A) (hf : f ∈ 𝒜 d) {V : T.Opens}
    (hV : V ≤ nonvanishingOpen T (natTensorPow L d) (ψ.toFun d ⟨f, hf⟩))
    (y : gradedPiece 𝒜 (integerGrading (S := A) 𝒜) f (d : ℤ))
    (hrep : (y : LocalizedModule.Away f A)
      = LocalizedModule.mk f (1 : Submonoid.powers f)) :
    chartSection ψ hf hV d y
      = resTop (natTensorPow L d) ((alphaVeronese 𝒜 ψ hd hgen).hom.app ⊤
          (pullbackDegreeSection 𝒜 (gluedVeronese 𝒜 ψ hd hgen) ⟨f, hf⟩)) V :=
  (chartSection_mk_one ψ hf hV d hf y hrep).trans
    (congrArg (fun z => resTop (natTensorPow L d) z V)
      (alphaVeronese_hom_app_top 𝒜 ψ hd hgen f hf).symm)

/-- **The clause `θ|_V = α` of [Stacks, Tag 01NK], on the degree-`d` section of `f`, with the
identification `Γ(D₊(f), 𝒪_X(d)) ≅ (A_f)_d` composed in.**

Let `s` be the global section of `𝒪_X(d)` attached to `f ∈ 𝒜 d` by [Stacks, Tag 01MP], restricted
to the standard open `D₊(f)` and read as an element of `(A_f)_d` through
`Stacks.AlgebraicGeometry.ProjTwistAwayPiece.sectionsTwistEquivGradedPiece`. Then the value on `s`
of the chart-level comparison `θ_f` of [Stacks, Tag 01NK] is the restriction to `V` of the value on
the pullback of `s` of the isomorphism `α` of [Stacks, Tag 01N8] for `ψ|_{A^{(d)}}`.

The fraction of `s` is `f / 1`
(`Stacks.AlgebraicGeometry.ProjTwistAwayPiece.coe_sectionsTwistEquivGradedPiece_degreeSection`), so
this is `chartSection_eq_alphaVeronese` at that element. -/
-- Beyond what this declaration proves, recorded here rather than in the attribute: the equality of
-- θ and α as maps on the chart of f is ProjChartGradedAlphaMaps.eq_chartSection_of_smul_of_alpha,
-- and as morphisms of sheaves over any open V on which ψ(A_d) generates it is
-- ProjChartGradedThetaMoreover.moreover. The agreement at the degree-d section of an ARBITRARY a
-- in 𝒜 d, rather than only at f, is ProjChartGradedAlphaMaps.chartSection_eq_alphaVeronese_of_mem.
-- The morphism half of the same final clause is
-- ProjChartGradedVeronese.homOfLE_glued_eq_gluedVeronese.
theorem chartSection_degreeSection_eq_alphaVeronese (f : A) (hf : f ∈ 𝒜 d) {V : T.Opens}
    (hV : V ≤ nonvanishingOpen T (natTensorPow L d) (ψ.toFun d ⟨f, hf⟩)) :
    chartSection ψ hf hV d
        (sectionsTwistEquivGradedPiece 𝒜 hf hd (d : ℤ)
          ((twistingSheaf 𝒜 (d : ℤ)).val.map
            (homOfLE (le_top : ProjectiveSpectrum.basicOpen 𝒜 f ≤ ⊤)).op
            (degreeSection 𝒜 d ⟨f, hf⟩)))
      = resTop (natTensorPow L d) ((alphaVeronese 𝒜 ψ hd hgen).hom.app ⊤
          (pullbackDegreeSection 𝒜 (gluedVeronese 𝒜 ψ hd hgen) ⟨f, hf⟩)) V :=
  chartSection_eq_alphaVeronese 𝒜 ψ hd hgen f hf hV _
    (coe_sectionsTwistEquivGradedPiece_degreeSection 𝒜 hf hd d ⟨f, hf⟩)

end Stacks.AlgebraicGeometry.ProjChartGradedAlphaMatch

end
