module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.CohomologicalGysinHodgeGeneral
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinConormalRankAny
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinDifferentialCompatibility

/-!
# The Gysin map on cohomology at the Gysin map of Tag 0G86

[Stacks, Tag 0G8A] applies the construction of the cohomological Gysin map to one particular
sheaf-level map: the `γ^p` of [Stacks, Tag 0G86], glued from the Gysin maps of [Stacks, Tag 0G83]
of the local families of equations.  This file supplies that map as a term and feeds it to
`Stacks.DeRham.CohomologicalGysin.gysinHodgeFormsMap`, which is the rest of the construction at
the generality of an arbitrary sheaf-level Gysin map.  The result is the source's

`γ^{p, q} : H^q(Z, Ω^p_{Z/S}) ⟶ H^{q + c}(X, Ω^{p + c}_{X/S})`

under the source's own hypotheses: `i : Z ⟶ X` a closed immersion of finite presentation whose
conormal sheaf is locally free of rank `c = d + 1`, and the vanishing of `ℋ^j_Z(Ω^{p+c}_{X/S})`
in the degrees `j < c`.

## Main definitions

* `Stacks.DeRham.CohomologicalGysin.conormalGysinHom`: **the `γ^p` of [Stacks, Tag 0G86] as a
  term**, chosen from the existence-and-uniqueness statement
  `Stacks.Gysin.existsUnique_gysinHom_of_conormalRank`.
* `Stacks.DeRham.CohomologicalGysin.conormalGysinTargetIso`: the identification of the target
  `i_*ℋ^c_Z(Ω^{p+c}_{X/S})` of that map with the spelling of the same sheaf that the
  cohomological construction consumes.
* `Stacks.DeRham.CohomologicalGysin.gysinHodgeFormsMapOfConormalRank`: **[Stacks, Tag 0G8A]**,
  the map `γ^{p, q}` of the source, at the source's own `γ^p`.

## Main results

* `Stacks.DeRham.CohomologicalGysin.conormalGysinHom_app`: `conormalGysinHom` is, over every open
  contained in an open on which `c` functions generate the ideal of `Z`, the Gysin map of
  [Stacks, Tag 0G83] of those functions — the clause of [Stacks, Tag 0G86] that characterises it.
* `Stacks.DeRham.CohomologicalGysin.eq_conormalGysinHom`: it is the only map with that property,
  so nothing is chosen beyond what [Stacks, Tag 0G86] determines.

## Implementation notes

**Why the choice is harmless.**  `conormalGysinHom` is `Exists.choose` applied to an
`ExistsUnique`, so the term it selects is the unique one satisfying the chart formula; that is
what `conormalGysinHom_app` and `eq_conormalGysinHom` say, and together they pin it down as
tightly as [Stacks, Tag 0G86] pins down `γ^p`.  The charts quantified over are *all* the equation
charts of `Stacks.Gysin.EquationChart`, so the characterisation is about every local family of
equations cutting out `Z` and not about a chosen covering family.

**The two spellings of `i_*ℋ^c_Z(ℱ)`.**  The Gysin map of [Stacks, Tag 0G86] lands in
`Stacks.Gysin.gysinTarget`, which takes the degree-`c` cohomology sheaf of `i_*R𝓗_Z(ℱ[0])` on the
ambient scheme; `gysinHodgeFormsMap` consumes the spelling in which the cohomology sheaf is taken
on the closed subset and pushed forward afterwards.  The direct image along the inclusion of a
closed subset is exact, so the two agree naturally in the coefficient module, by
`Stacks.Perfect.GysinLocalCohomology.supportCohomologySheafFunctorIso`; that natural isomorphism,
evaluated at `Ω^{p+c}_{X/S}`, is `conormalGysinTargetIso`, and it needs no hypothesis on the
coefficient module.  No second construction of the local cohomology sheaf is involved.

**Nothing is assumed.**  The hypotheses of
`gysinHodgeFormsMapOfConormalRank` are exactly the source's: the two hypotheses of
[Stacks, Tag 0G86], which produce `γ^p`, and the vanishing of `ℋ^j_Z(Ω^{p+c}_{X/S})` for `j < c`,
which is the hypothesis [Stacks, Tag 0G8A] states in its own words.  The quasi-coherence of
`Ω^p_{Z/S}` that the comparison `H^q(Z, -) = H^q(X, i_*-)` of [Stacks, Tag 089W] needs is proved
inside `gysinHodgeFormsMap`.  The sufficient condition for the vanishing offered by
[Stacks, Tag 0G7P] is *not* used, and is not available: this library's 0G7P carries only the
complementary vanishing in degrees `j > c`, as
`StacksFrontier.AlgebraicGeometry.DeRham.Gysin.CohomologicalGysinMap` records.

**Where the vanishing hypothesis is taken.**  It is stated for the closed subset
`Set.range i.base`, the image of the closed immersion, which is the source's `Z`; no family of
equations occurs in it.
Stated for every integer `j < c`, as `DerivedCategory.isGE_iff` demands, it has content only in the
degrees `0 ≤ j < c` the source names, because the negative ones are
`Stacks.DeRham.CohomologicalGysin.isZero_localCohomologySheafOfComplex_of_neg`.

## References

* [Stacks Project, Tag 0G8A](https://stacks.math.columbia.edu/tag/0G8A)
* [Stacks Project, Tag 0G86](https://stacks.math.columbia.edu/tag/0G86)
* [Stacks Project, Tag 0G83](https://stacks.math.columbia.edu/tag/0G83)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
* [Stacks Project, Tag 0G7P](https://stacks.math.columbia.edu/tag/0G7P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.SupportedComplexes
open Stacks.AlgebraicGeometry.ConormalEquations
open Stacks.Perfect.GysinLocalCohomology

namespace Stacks.DeRham.CohomologicalGysin

universe u

open DerivedCategory

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.Topology.RingedSpaceSheafifyOpens.opensHasSheafifyAddCommGrpCat
  Stacks.Topology.RingedSpaceSheafifyOpens.opensWEqualsLocallyBijectiveAddCommGrpCat

/-- Sheaves of modules on a ringed space have a derived category. -/
local instance moduleSheavesHasDerivedCategoryConormal (X : RingedSpace.{u, u}) :
    HasDerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X)) :=
  HasDerivedCategory.standard _

section Conormal

open AlgebraicGeometry.Scheme.Hom Stacks.Gysin
open scoped AlgebraicGeometry

variable {Z X S : Scheme.{u}}

/-! ### The Gysin map of Tag 0G86 as a term -/

/-- **The `γ^p` of [Stacks, Tag 0G86] as a term.**  For `π : X ⟶ S` a morphism of schemes and
`i : Z ⟶ X` a closed immersion of finite presentation whose conormal sheaf is locally free of
rank `c`, this is *the* map

`γ^p : i_*Ω^p_{Z/S} ⟶ i_*ℋ^c_Z(Ω^{p+c}_{X/S})`

which restricts, over every open contained in an open on which `c` functions generate the ideal
of `Z`, to the Gysin map of [Stacks, Tag 0G83] of those functions.  It is chosen from
`Stacks.Gysin.existsUnique_gysinHom_of_conormalRank`, whose uniqueness clause makes the choice
immaterial: `conormalGysinHom_app` and `eq_conormalGysinHom` characterise the term completely.

The rank is an arbitrary natural number, as in the tag; `c = 0` is the case in which `Z` is a
clopen piece of `X` and the local families of equations are empty. -/
def conormalGysinHom (i : Z ⟶ X) [IsClosedImmersion i] [LocallyOfFinitePresentation i]
    (π : X ⟶ S) {c : ℕ} (p : ℕ) (hE : ConormalRank i c) :
    pushforwardRelativeForms i π (p : ℤ) ⟶ gysinTarget i π c p :=
  (existsUnique_gysinHom_of_conormalRank i π p hE).choose

/-- **The chart formula of [Stacks, Tag 0G86] for `conormalGysinHom`.**  Over an open contained
in an equation chart, the map is the Gysin map of [Stacks, Tag 0G83] of that chart's equations.
The charts are all the equation charts of `Stacks.Gysin.EquationChart`, so this is a statement
about every local family of `c` equations cutting out `Z`. -/
theorem conormalGysinHom_app (i : Z ⟶ X) [IsClosedImmersion i] [LocallyOfFinitePresentation i]
    (π : X ⟶ S) {c : ℕ} (p : ℕ) (hE : ConormalRank i c)
    (a : EquationChart i c) (V : X.Opens) (hV : V ≤ a.ambient)
    (x : Γ(pushforwardRelativeForms i π (p : ℤ), V)) :
    (conormalGysinHom i π p hE).app V x =
      chartLoc i π p a.ambient a.equations
        (isCutOutByEquationsOn_of_isGeneratedByOn i a.gen a.vanish)
        (equationsClosedSet_restrictEquations i a.ambient
          (isCutOutByEquationsOn_of_isGeneratedByOn i a.gen a.vanish)) V hV x :=
  (existsUnique_gysinHom_of_conormalRank i π p hE).choose_spec.1 a V hV x

/-- **`conormalGysinHom` is the only map that is locally the Gysin map of the equations**, which
is the uniqueness clause of [Stacks, Tag 0G86].  So the `Exists.choose` in its definition selects
a term that is determined by the tag. -/
theorem eq_conormalGysinHom (i : Z ⟶ X) [IsClosedImmersion i] [LocallyOfFinitePresentation i]
    (π : X ⟶ S) {c : ℕ} (p : ℕ) (hE : ConormalRank i c)
    (φ : pushforwardRelativeForms i π (p : ℤ) ⟶ gysinTarget i π c p)
    (hφ : ∀ (a : EquationChart i c) (V : X.Opens) (hV : V ≤ a.ambient)
      (x : Γ(pushforwardRelativeForms i π (p : ℤ), V)),
      φ.app V x =
        chartLoc i π p a.ambient a.equations
          (isCutOutByEquationsOn_of_isGeneratedByOn i a.gen a.vanish)
          (equationsClosedSet_restrictEquations i a.ambient
            (isCutOutByEquationsOn_of_isGeneratedByOn i a.gen a.vanish)) V hV x) :
    φ = conormalGysinHom i π p hE :=
  (existsUnique_gysinHom_of_conormalRank i π p hE).choose_spec.2 φ hφ

/-! ### The two spellings of the target -/

/-- **The target of the Gysin map of [Stacks, Tag 0G86] is the sheaf the cohomological
construction consumes.**  `Stacks.Gysin.gysinTarget` pushes `i_*R𝓗_Z(ℱ[0])` forward first and
takes the degree-`c` cohomology sheaf on the ambient scheme; `gysinHodgeFormsMap` takes the
cohomology sheaf on the closed subset and pushes forward afterwards.  Direct image along the
inclusion of a closed subset is exact, so the two agree, naturally in the coefficient module and
with no hypothesis on it: this is
`Stacks.Perfect.GysinLocalCohomology.supportCohomologySheafFunctorIso` evaluated at
`Ω^{p+c}_{X/S}`. -/
def conormalGysinTargetIso (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) (c p : ℕ) :
    gysinTarget i π c p ≅
      (modulePushforward (closedSubsetInclusion X.toRingedSpace (Set.range i.base))).obj
        (localCohomologySheafOfComplex X.toRingedSpace (Set.range i.base)
          i.isClosedEmbedding.isClosed_range (c : ℤ)
          ((singleFunctor _ (0 : ℤ)).obj
            (relativeDifferentialForms π ((p : ℤ) + (c : ℤ))))) :=
  (supportCohomologySheafFunctorIso (isClosed_range_base i) (c : ℤ)).app
    (relativeDifferentialForms π ((p : ℤ) + (c : ℤ)))

/-! ### Tag 0G8A at the Gysin map of Tag 0G86 -/

/-- **Stacks Project, Tag 0G8A.**  Let `π : X ⟶ S` be a morphism of schemes and `i : Z ⟶ X` a
closed immersion of finite presentation whose conormal sheaf is locally free of rank `c`
— the hypotheses of [Stacks, Tag 0G86].  Let `p ≥ 0` and assume

`ℋ^j_Z(Ω^{p+c}_{X/S}) = 0` for `j = 0, …, c - 1`.

Then there is a map

`γ^{p, q} : H^q(Z, Ω^p_{Z/S}) ⟶ H^{q + c}(X, Ω^{p + c}_{X/S})`

for every `q`, obtained exactly as the source obtains it: the `γ^p` of [Stacks, Tag 0G86]
followed by the passage `ℋ^c_Z(ℱ) = R𝓗_Z(ℱ)[c]`, the identification `H^q(Z, -) = H^q(X, i_*-)`
and the adjunction map `i_*R𝓗_Z(ℱ) ⟶ ℱ`.

The sheaf-level map is `conormalGysinHom`, the `γ^p` of [Stacks, Tag 0G86] itself — glued from the
Gysin maps of [Stacks, Tag 0G83] of the local families of equations, not built from one global
family — and the three remaining steps are `gysinHodgeFormsMap`, which performs them for an
arbitrary sheaf-level Gysin map.  The one identification in between is
`conormalGysinTargetIso`, between two spellings of `i_*ℋ^c_Z(Ω^{p+c}_{X/S})` that agree because
the direct image along the inclusion of a closed subset is exact.

Nothing is assumed: both hypotheses of [Stacks, Tag 0G86] are consumed where the source consumes
them, by `Stacks.Gysin.existsUnique_gysinHom_of_conormalRank`, the quasi-coherence of
`Ω^p_{Z/S}` needed by [Stacks, Tag 089W] is proved inside `gysinHodgeFormsMap`, and `hvan` is the
source's own vanishing hypothesis.  The sufficient condition of [Stacks, Tag 0G7P] is not
available here and is not used.

**The rank is an arbitrary natural number**, as the tag states it: [Stacks, Tag 0G8A] says
`c ≥ 0` explicitly.  Nothing here needs `c ≠ 0`, because
`Stacks.Gysin.existsUnique_gysinHom_of_conormalRank` supplies `γ^p` at every rank — it splits on
`c`, the chart route of `Stacks.Gysin.exists_gysinCharts` handling `c = d + 1` and
`Stacks.Gysin.existsUnique_gysinHom_of_conormalRank_zero` handling `c = 0`, where the local
families of equations are empty and the charts cover the image rather than `X`.

`hvan` is retained because it is the source's own hypothesis, not an artefact of the rank: at
`c = 0` it is vacuous in content — the degrees `j < 0` carry none, by
`Stacks.DeRham.CohomologicalGysin.isZero_localCohomologySheafOfComplex_of_neg` — and the
construction consumes it uniformly.

**What rank `0` forces, and what it does not.**  `ConormalRank i 0` says exactly that the
conormal sheaf of `i` vanishes, so the ideal sheaf vanishes on an affine neighbourhood of every
point of `Set.range i.base` —
`Stacks.AlgebraicGeometry.ConormalEquations.exists_affineOpen_equations_of_conormalRank`, read at
`c = 0`, returns such a neighbourhood and it carries no hypothesis on `c`.  Hence `i` is an
isomorphism onto an open subscheme, which being also closed has *clopen* range.  It does **not**
force that range to be the whole of `X`: the identity satisfies `ConormalRank i 0`, and so does
the inclusion of a proper clopen piece.  The equations of the chapter cannot see the latter, by
`Stacks.Gysin.equationsClosedSet_eq_range`: an empty family cutting out `i` in the sense of
`Stacks.Gysin.IsCutOutByEquations` makes `Set.range i.base` the whole of `X`.  That is why the
`c = 0` branch of [Stacks, Tag 0G86] is glued on the charts together with the complement of the
image instead of on a `Stacks.Gysin.GysinChartData`. -/
@[stacks 0G8A]
def gysinHodgeFormsMapOfConormalRank (i : Z ⟶ X) [IsClosedImmersion i]
    [LocallyOfFinitePresentation i] (π : X ⟶ S) {c : ℕ} (p : ℕ)
    (hE : ConormalRank i c)
    (hvan : ∀ j : ℤ, j < (c : ℤ) →
      IsZero (localCohomologySheafOfComplex X.toRingedSpace (Set.range i.base)
        i.isClosedEmbedding.isClosed_range j ((singleFunctor _ (0 : ℤ)).obj
          (relativeDifferentialForms π ((p : ℤ) + (c : ℤ))))))
    (q : ℕ) :
    Hgroup Z.ringCatSheaf ⊤ q (relativeDifferentialForms (i ≫ π) (p : ℤ)) ⟶
      Hgroup X.ringCatSheaf ⊤ (q + c)
        (relativeDifferentialForms π ((p : ℤ) + (c : ℤ))) :=
  gysinHodgeFormsMap i π c p hvan
    (conormalGysinHom i π p hE ≫ (conormalGysinTargetIso i π c p).hom) q

end Conormal

end Stacks.DeRham.CohomologicalGysin

end
