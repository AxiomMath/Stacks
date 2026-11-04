module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.BigSiteAssociatedSheafRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.SmallEtaleHigherDirectImageVanishing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.PushforwardCohomologyCollapse

/-!
# Zariski and big `τ`-site cohomology of a quasi-coherent module agree

Let `B` be one of the five big sites of a topology `τ`, let `S` be a scheme below its cutoff,
let `F` be a quasi-coherent `𝒪_S`-module and let `Fᵃ` be the associated module of
[Stacks, Tag 03DU] read as an abelian sheaf on the localized big site.  This file proves
[Stacks, Tag 03P2] in the cases `𝒞 = (Sch/S)_τ` for `τ` any of fppf, syntomic, smooth, étale and
Zariski:

  `H^p(V, ℱ) ≅ H^p_τ(V, Fᵃ)`

for every open `V` of `S` and every degree `p`, and in particular, at `V = ⊤`,

  `H^p(S, ℱ) ≅ H^p_τ(S, Fᵃ)`.

The Leray collapse along `ε : (Sch/S)_τ ⟶ S_Zar` is
`Stacks.Cohomology.BiggerSite.sheafCohomologyPushforwardIso`, whose hypothesis — the vanishing
of the higher direct images `R^q ε_* Fᵃ` — is proved here from the affine acyclicity
`AlgebraicGeometry.isZero_sheafCohomology_succ_overAffine`.  What the collapse compares against
is `ε_* Fᵃ`, and the identification of that with `ℱ` is
`AlgebraicGeometry.bigOverSectionsUnitIso`.

## Main definitions

* `AlgebraicGeometry.bigOverQuasiCoherentCohomologyIso`: **[Stacks, Tag 03P2] for
  `𝒞 = (Sch/S)_τ`**, over an arbitrary open of `S`.
* `AlgebraicGeometry.bigOverQuasiCoherentGlobalCohomologyIso`: the same over the whole scheme,
  which is how the source states it.

## Main results

* `AlgebraicGeometry.isZero_rightDerived_pushforward_opensBelowToOver`: the higher direct images
  of `Fᵃ` along `ε` vanish.

## Implementation notes

The vanishing of the higher direct images is the presieve form of the criterion,
`Stacks.Cohomology.HigherDirectImageOnACover.isZero_rightDerived_pushforward_of_presieve`: the
covering family used is the affine opens below a given open, and that is a *presieve* and not a
sieve, since an open subset of an affine open need not be affine.  The two inputs are shared
verbatim with the small étale branch — `AlgebraicGeometry.affineOpensPresieve` and
`AlgebraicGeometry.generate_affineOpensPresieve_mem` are statements about the opens of `S` and
see no site — and an affine open read in the localized big site is an affine object of it
definitionally, by `AlgebraicGeometry.mem_overAffineObjects_opensBelowToOver`.

Cohomology is `CategoryTheory.Sheaf.H'`, `Ext` out of the free abelian sheaf on the Yoneda
presheaf of the object, with its `Ext` universe at the morphism universe `u` of the big site on
both sides.  That is the degree-`p` right-derived functor of sections over the object, by
`Stacks.Cohomology.FreeYonedaUnivLE.sheafCohomologyIsoRightDerivedSections`, so over `⊤` it is
cohomology of the scheme and over `(opensBelowToOver hS).obj ⊤` — a final object of the big
site, by `AlgebraicGeometry.isTerminal_opensBelowToOver_top` — it is `τ`-cohomology of the
scheme.

Three of the instance hypotheses of the collapse have to be supplied by name rather than by
instance search, and that is all the plumbing this file does.

* On the Zariski side the `Ext` universe and enough injectives are the theorems
  `Stacks.Topology.hasExt_sheafOpens` and `Stacks.Topology.enoughInjectives_sheafOpens`,
  supplied as local instances.  Their `UnivLE` hypothesis is `UnivLE.{u, u}` here.
* Preservation of injectives by `ε_*` is
  `Stacks.Cohomology.BiggerSite.preservesInjectiveObjects_sheafPushforwardContinuous`, which
  applies because the opens of `S` have fibre products and equalizers — intersections, and
  trivially — and the inclusion preserves them, by
  `AlgebraicGeometry.opensBelowToOver_preservesLimitsOfShape_walkingCospan` and
  `AlgebraicGeometry.opensBelowToOver_preservesLimitsOfShape_walkingParallelPair`.
* On the big-site side the `Ext` universe and enough injectives are
  `Stacks.Cohomology.FreeYonedaUnivLE.hasExt_essentiallySmallSite` and
  `..._enoughInjectives_essentiallySmallSite`, a localized big site being essentially small at
  the universe of its morphisms (`AlgebraicGeometry.essentiallySmall_overBase`).  No instance
  priority has to be flipped here, unlike on the small étale site: the big sites already measure
  at `Ext` universe `u`, which is why the statements below elaborate as written.

Additivity and left exactness of `ε_*` are found by instance search and are not supplied here.

**A `@[stacks 03DW]` attribute is attached alongside, to the same declaration.**  Descent
Proposition 35.9.3 ([Stacks, Tag 03DW]) and Étale Cohomology Theorem 59.22.4
([Stacks, Tag 03P2]) are the same assertion stated in two chapters.  So the declaration below
is clause (1) of 03DW, *in every degree* and for all five `τ` at once — and in particular in
positive degree, which `AlgebraicGeometry.BigFppfOver.hZeroBaseAssociatedModuleAddEquiv`, the
`q = 0` carrier of 03DW, does not claim.  The affine vanishing `H^p(U, ℱᵃ) = 0` for affine `U`
and `p > 0` that the source's proof passes through is
`AlgebraicGeometry.isZero_sheafCohomology_succ_overAffine`.  Note that the site here is
`AlgebraicGeometry.overTopology` on `Over (AlgebraicGeometry.base B S hS)` and not the
`AlgebraicGeometry.BigFppfOver.baseOverTopology` of the `q = 0` carrier; for `τ ≠ fppf` those
are topologies on different categories, and no bridge between them is claimed.

**The `@[stacks 03P2]` attribute is attached, to the `V = ⊤` form below.**  The source lets `𝒞`
be *either* `(Sch/S)_τ` for `τ ∈ {fppf, syntomic, smooth, étale, Zariski}` *or* `S_étale`, a
disjunction over two cases that the source itself delimits, and the covering set of the tag is
one declaration per case:
`AlgebraicGeometry.bigOverQuasiCoherentGlobalCohomologyIso` below, whose `τ` is a bound variable
so that the one declaration covers all five big sites, together with
`AlgebraicGeometry.smallEtaleQuasiCoherentGlobalCohomologyIso` for `𝒞 = S_étale`.

The tag goes on the global form and not on the `V`-general
`AlgebraicGeometry.bigOverQuasiCoherentCohomologyIso`, because the statement of the tag is
`H^p(S, ℱ) = H^p_τ(S, ℱᵃ)` at `S` itself: `V = ⊤` *is* the tag, and that is what a reader
checking faithfulness compares against.  The `V`-general form stays untagged as the stronger
lemma the global one is derived from — the source records that same generalisation about an
arbitrary object of `𝒞`, but in its comment on the theorem rather than in the theorem.

## References

* [Stacks Project, Tag 01XD](https://stacks.math.columbia.edu/tag/01XD)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03P2](https://stacks.math.columbia.edu/tag/03P2)
* [Stacks Project, Tag 072W](https://stacks.math.columbia.edu/tag/072W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Adequate
open Stacks.Cohomology.HigherDirectImageOnACover
open scoped AlgebraicGeometry

universe u

-- A localized big site is essentially small at the universe of its morphisms, so these two
-- supply its `Ext` universe and enough injectives.  They are not global instances, and
-- `CategoryTheory.Sheaf.H'` is defined through `Ext`, so without them the *statements* below do
-- not even elaborate.
attribute [local instance] Stacks.Cohomology.FreeYonedaUnivLE.enoughInjectives_essentiallySmallSite
  Stacks.Cohomology.FreeYonedaUnivLE.hasExt_essentiallySmallSite

namespace AlgebraicGeometry

variable (S : Scheme.{u}) (F : S.Modules) [F.IsQuasicoherent] (τ : CoveringTopology)
  (B : BigSite.{u} τ) (hS : S.size < cutoff τ B)

/-- **An affine open of `S`, read as an object of a localized big `τ`-site, has affine total
space.**  The total space of the resulting object is the open subscheme itself, so this is
`AlgebraicGeometry.IsAffineOpen` unfolded. -/
public theorem mem_overAffineObjects_opensBelowToOver {V : S.Opens} (hV : IsAffineOpen V) :
    (opensBelowToOver (κ := cutoff τ B) hS).obj V ∈ overAffineObjects τ B S hS := hV

/-- **The higher direct images of `Fᵃ` along the comparison `ε : (Sch/S)_τ ⟶ S_Zar` vanish.**
This is the hypothesis of the Leray collapse of [Stacks, Tag 03P2] in the case
`𝒞 = (Sch/S)_τ`.

The affine opens below an open of `S` generate a covering sieve of it, each of them is an affine
object of the big site, and the higher cohomology of `Fᵃ` there vanishes by
`AlgebraicGeometry.isZero_sheafCohomology_succ_overAffine`. -/
public theorem isZero_rightDerived_pushforward_opensBelowToOver (p : ℕ) (hp : 0 < p) :
    IsZero (((bigOverZariskiPushforward S τ B hS).rightDerived p).obj
      (bigOverAssociatedSheaf S F τ B hS)) := by
  refine isZero_rightDerived_pushforward_of_presieve
    (opensBelowToOver (κ := cutoff τ B) hS) p _ (fun V ↦ ?_)
  refine ⟨affineOpensPresieve S V, generate_affineOpensPresieve_mem S V, fun W g hg ↦ ?_⟩
  exact (isZero_sheafCohomology_succ_overAffine S F τ B hS
      ((opensBelowToOver (κ := cutoff τ B) hS).obj W)
      (mem_overAffineObjects_opensBelowToOver S τ B hS hg) p hp).of_iso
    (Stacks.Cohomology.FreeYonedaUnivLE.sheafCohomologyIsoRightDerivedSections
      (overTopology τ B S hS) _ p ((opensBelowToOver (κ := cutoff τ B) hS).obj W)).symm

-- The Zariski side of the collapse asks for an `Ext` universe and enough injectives in the
-- coefficients themselves; both are available at any coefficient universe dominating the space,
-- but only as theorems.  Preservation of injectives by `ε_*` is likewise a theorem.
attribute [local instance] Stacks.Topology.hasExt_sheafOpens
  Stacks.Topology.enoughInjectives_sheafOpens
  Stacks.Cohomology.BiggerSite.preservesInjectiveObjects_sheafPushforwardContinuous

/-- **The cohomology of `Fᵃ` over an open of `S` collapses onto Zariski cohomology of `ℱ`.**
For a quasi-coherent module `F` on `S`, an open `V` of `S` and a degree `p`,

  `H^p(V, ℱ) ≅ H^p_τ(V, Fᵃ)`,

where the right-hand side is the cohomology on a localized big `τ`-site of `S` of the associated
module `Fᵃ`, taken over the object `V.ι : V ⟶ S`.

This is `Stacks.Cohomology.BiggerSite.sheafCohomologyPushforwardIso` for the continuous functor
`Stacks.Adequate.opensBelowToOver`, whose hypothesis is discharged by
`AlgebraicGeometry.isZero_rightDerived_pushforward_opensBelowToOver`, read on the Zariski side
through `AlgebraicGeometry.bigOverSectionsUnitIso`.

This is the generalisation of [Stacks, Tag 03P2] to an arbitrary open of `S` in the cases
`𝒞 = (Sch/S)_τ`, and carries no attribute: the tag's statement is the one at `S` itself, which
is `AlgebraicGeometry.bigOverQuasiCoherentGlobalCohomologyIso` below. -/
public def bigOverQuasiCoherentCohomologyIso (p : ℕ) (V : S.Opens) :
    Sheaf.H' ((SheafOfModules.toSheaf S.ringCatSheaf).obj F) p V ≅
      Sheaf.H' (bigOverAssociatedSheaf S F τ B hS) p
        ((opensBelowToOver (κ := cutoff τ B) hS).obj V) :=
  ((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology ↥S) p).mapIso
      (bigOverSectionsUnitIso S F τ B hS)).app (op V) ≪≫
    Stacks.Cohomology.BiggerSite.sheafCohomologyPushforwardIso
      (Opens.grothendieckTopology ↥S) (overTopology τ B S hS)
      (opensBelowToOver (κ := cutoff τ B) hS) (bigOverAssociatedSheaf S F τ B hS) V p
      (fun q hq _ ↦ isZero_rightDerived_pushforward_opensBelowToOver S F τ B hS q hq)

/-- **Zariski cohomology of a quasi-coherent module agrees with its big `τ`-site cohomology**:
for a quasi-coherent module `F` on a scheme `S` and a degree `p`,

  `H^p(S, ℱ) ≅ H^p_τ(S, Fᵃ)`.

This is `AlgebraicGeometry.bigOverQuasiCoherentCohomologyIso` at the whole scheme.  The object it
is taken over on the right, `(opensBelowToOver hS).obj ⊤`, is a final object of the big site by
`AlgebraicGeometry.isTerminal_opensBelowToOver_top`, so the right-hand side is `τ`-cohomology of
`S` itself.

**This is [Stacks, Tag 03P2] in the case `𝒞 = (Sch/S)_τ`**, for all five `τ` at once.  Together
with `AlgebraicGeometry.smallEtaleQuasiCoherentGlobalCohomologyIso`, which is the case
`𝒞 = S_étale`, it is the covering set of the tag: the source lets `𝒞` be either of the two, and
these are one declaration per case. -/
@[stacks 03P2 "the case 𝒞 = (Sch/S)_τ: τ is a bound variable, so this one declaration covers \
all five of fppf, syntomic, smooth, étale and Zariski.  The object the right-hand side is taken \
over, (opensBelowToOver hS).obj ⊤, is a final object of the site, so that side is τ-cohomology \
of S itself.  The case 𝒞 = S_étale is smallEtaleQuasiCoherentGlobalCohomologyIso",
  stacks 03DW "clause (1), in EVERY degree q and for all five τ at once (τ is a bound \
variable) — the same statement as Tag 03P2 at 𝒞 = (Sch/S)_τ, Descent Proposition 35.9.3 and \
Étale Cohomology Theorem 59.22.4 being the same assertion in two chapters.  In particular this \
is the POSITIVE-DEGREE case, which the q = 0 carrier \
BigFppfOver.hZeroBaseAssociatedModuleAddEquiv does not claim; the affine vanishing \
H^p(U, Fᵃ) = 0 that the source's proof passes through is \
isZero_sheafCohomology_succ_overAffine.  The site here is overTopology on \
Over (base B S hS), not the BigFppfOver.baseOverTopology that the q = 0 carrier uses; the two \
are topologies on different categories for τ ≠ fppf and no bridge is claimed.  Clause (2) is \
covered by smallEtaleQuasiCoherentGlobalCohomologyIso (the small étale half) together with \
smallZariskiQuasiCoherentGlobalCohomologyIso (the small Zariski half)"]
public def bigOverQuasiCoherentGlobalCohomologyIso (p : ℕ) :
    Sheaf.H' ((SheafOfModules.toSheaf S.ringCatSheaf).obj F) p ⊤ ≅
      Sheaf.H' (bigOverAssociatedSheaf S F τ B hS) p
        ((opensBelowToOver (κ := cutoff τ B) hS).obj ⊤) :=
  bigOverQuasiCoherentCohomologyIso S F τ B hS p ⊤

end AlgebraicGeometry

end
