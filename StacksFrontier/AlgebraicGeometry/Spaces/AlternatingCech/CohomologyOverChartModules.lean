module

public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.CohomologyOverChart
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleStructureSheaf
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.CohomologyOverAnObject
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.DerivedGlobalSectionsCohomology
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparisonUniverses

/-!
# The column `p = 0` of the `E₁`-page at module coefficients

`AlgebraicGeometry.Space.SpacesEtale.zExtKoszulComplexXZeroAddEquiv` identifies the column
`p = 0` of the first page of the alternating Čech spectral sequence of [Stacks, Tag 0728] with
the *abelian* sheaf cohomology of the chart, `Ext^q(K^0, ℱ) ≅ H^q(U, ℱ|_U)`, and the module
documentation of that file records why the vanishing of the rows `q > 0` cannot be had there:
for a general abelian `ℱ` the group `H^q(U, ℱ|_U)` is Galois cohomology and does not vanish,
affineness of the chart notwithstanding. The source kills those rows by Serre vanishing for
**quasi-coherent modules**, so the vanishing hypothesis of [Stacks, Tag 072B] has to be asked
of a sheaf that is the underlying abelian sheaf of a module and asked in module terms.

This file performs that crossing for the column `p = 0`. Its content is the composite of three
things that are all already in the library, which is the point: the crossing needs no new
theory, and in particular it does not need the sections-over-an-object half of
[Stacks, Tag 03FD].

* `AlgebraicGeometry.Space.SpacesEtale.zExtKoszulComplexXZeroAddEquiv` puts the column at the
  abelian sheaf cohomology `CategoryTheory.Sheaf.H` of the **slice** site
  `(C/U, J/U)`, i.e. of the localization of the spaces-étale site at the chart.
* `Stacks.Cohomology.GlobalSections.subsingleton_sheafH_iff_isZero_rightDerivedΓ` turns that
  into the vanishing of the right derived functors of global sections *of the slice site*,
  at a free object universe and a free morphism universe.
* [Stacks, Tag 03FD] compares those with the derived global sections of a sheaf of modules.

## Main definitions

* `AlgebraicGeometry.Space.SpacesEtale.chartRingSheaf`: the structure sheaf of the slice of the
  ringed spaces-étale site at `U`, with commutativity forgotten.
* `AlgebraicGeometry.Space.SpacesEtale.chartGlobalSectionsComparisonIso`: **[Stacks, Tag 03FD]
  on that slice.**

## Main results

* `Space.SpacesEtale.isZero_zExt_koszulComplex_X_zero_of_isZero_rightDerivedModuleΓ`:
  the column `p = 0` of the `E₁`-page vanishes in degree `q` as soon as the restriction of the
  coefficients to the slice at `U` is the underlying abelian sheaf of a module `M` whose own
  derived global sections vanish in degree `q`.
* `AlgebraicGeometry.Space.SpacesEtale.isZero_zExt_koszulComplex_X_zero_of_subsingleton_sheafH'`:
  the same column read against `CategoryTheory.Sheaf.H'`, cohomology *over* the chart on the
  spaces-étale site itself, which is the shape the étale Serre vanishing is stated in.

## Two routes to the same vanishing, and what each still owes

The `Sheaf.H'` form is the shorter route and does not use [Stacks, Tag 03FD] at all. The étale
Serre vanishing exists in this tree, hypothesis-free, as
`AlgebraicGeometry.Space.isZero_sheafH'_of_isQuasicoherentOnSite`
(`StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartSheafCohomologyVanishing`): the
positive-degree `Sheaf.H'` of the underlying abelian sheaf of a quasi-coherent module vanishes
over an affine object of the **small** étale site of an algebraic space. What separates it from
the result below is the site: this file's `Sheaf.H'` is on `SpacesEtale`, that one's is on
`SmallEtale`, and the bridge is [Stacks, Tag 03G1] —
`AlgebraicGeometry.Space.comparisonFunctor_sheafEquivalence`, an `IsEquivalence` instance at
free coefficient universes — transporting `Sheaf.H'` across the equivalence with the two
corepresenting free-abelian-on-yoneda sheaves identified.

That is also the one place where the two sites differ in a way that matters: `SpacesEtale` is a
`CategoryTheory.SmallCategory` and `SmallEtale` is not, its objects lying in `Type (u + 1)` and
its morphisms in `Type u`. `Sheaf.H'` needs its coefficients in the universe of the morphisms,
so the transport is not a formality.

## What this says about the remaining inputs of [Stacks, Tag 072B]

`chartGlobalSectionsComparisonIso` is `ModuleSheafCohomology.Univ.globalSectionsComparisonIso` at
the single universe `u + 1`, applied with no re-seating and no hypotheses discharged by hand.
That is possible because the slice of the spaces-étale site is still a
`CategoryTheory.SmallCategory`: `AlgebraicGeometry.Space.spacesEtaleRingedSite` is a
`AlgebraicGeometry.RingedSite.{u + 1, u + 1, u + 1}`, objects, morphisms and sections of the
structure sheaf all in one universe, and `CategoryTheory.Over U` keeps that. So the
module-versus-abelian crossing needed by the *inner* vanishing of [Stacks, Tag 072B] is not
blocked on a universe seating of any kind. Neither half of [Stacks, Tag 03FD] is: the
sections-over-an-object half `ModuleSheafCohomology.sectionsComparisonIso` also applies on this
site at `u + 1`, and the chain does not use it in any case, the cohomology here being the
*global* sections of the slice rather than sections over an object of the ambient site.

What the hypotheses of the result below stand for is therefore the whole of what is left:

* `e` is [Stacks, Tag 072A] — that `ℱ|_U ⊗_ℤ ℤ(χ)` is the underlying abelian sheaf of a
  quasi-coherent module. It is carried as an isomorphism rather than derived. The
  quasi-coherence half of that tag is itself proved, as
  `AlgebraicGeometry.Space.SignTwistSetup.isQuasicoherentOnSite_twist`; what `e` adds is the
  identification of the abelian sheaf `ℱ|_U` with the underlying sheaf of that module, and its
  twist is stated on the **small** étale site of the quotient, so the same [Stacks, Tag 03G1]
  transport is involved.
* `h` is Serre vanishing on the affine `U`, [Stacks, Tag 01XB], read on the étale site, i.e.
  the positive-degree clause of [Stacks, Tag 03DW]. In this module-valued form it is not
  available; in the `Sheaf.H'` form it is, as recorded above.

Quasi-coherence is not asked of `M` below, because nothing in the argument uses it; it is the
input that `h` would be *deduced* from once the étale Serre vanishing exists, and asking it
here would only weaken the statement.

## References

* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
* [Stacks Project, Tag 072A](https://stacks.math.columbia.edu/tag/072A)
* [Stacks Project, Tag 072B](https://stacks.math.columbia.edu/tag/072B)
* [Stacks Project, Tag 0728](https://stacks.math.columbia.edu/tag/0728)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.SheafOfModules.Tensor (ringSheaf)

universe u

attribute [local instance] HasDerivedCategory.standard
  ModuleSheafCohomology.Univ.gamma_additive
  ModuleSheafCohomology.Univ.toSheaf_preservesFiniteColimits

namespace AlgebraicGeometry.Space.SpacesEtale

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-- The structure sheaf of the slice of the ringed spaces-étale site at `U`, with commutativity
forgotten: sheaves of modules on the slice are sheaves of modules over this sheaf of rings. -/
noncomputable abbrev chartRingSheaf (U : SpacesEtale B S hS X) :
    Sheaf ((topology B S hS X).over U) RingCat.{u + 1} :=
  (ringSheaf (spacesEtaleRingedSite B S hS X).O).over U

/-- **[Stacks, Tag 03FD] on the slice of the spaces-étale site at `U`.** Deriving the global
sections of a sheaf of `𝒪_U`-modules on the slice and then forgetting agrees, in every degree,
with forgetting to an abelian sheaf and deriving global sections of the slice site there.

This is `ModuleSheafCohomology.Univ.globalSectionsComparisonIso` at the single universe `u + 1`,
with nothing re-seated: the slice of the spaces-étale site is a `CategoryTheory.SmallCategory`
and its structure sheaf has sections in the same universe. -/
def chartGlobalSectionsComparisonIso (U : SpacesEtale B S hS X) (n : ℕ) :
    (SheafOfModules.toSheaf.{u + 1} (chartRingSheaf B S hS X U) ⋙
        Sheaf.Γ ((topology B S hS X).over U) AddCommGrpCat.{u + 1}).rightDerived n ≅
      SheafOfModules.toSheaf.{u + 1} (chartRingSheaf B S hS X U) ⋙
        (Sheaf.Γ ((topology B S hS X).over U) AddCommGrpCat.{u + 1}).rightDerived n :=
  ModuleSheafCohomology.Univ.globalSectionsComparisonIso.{u + 1, u + 1, u + 1, u + 1}
    ((topology B S hS X).over U) (chartRingSheaf B S hS X U) n

/-- **The column `p = 0` of the `E₁`-page of [Stacks, Tag 0728] at module coefficients.**
Suppose the restriction of `ℱ` to the slice at the chart `U` is the underlying abelian sheaf of
a sheaf of `𝒪_U`-modules `M`, and that the derived global sections of `M` vanish in degree `q`.
Then `Ext^q(K^0, ℱ) = 0`.

This is the shape in which the row hypothesis of [Stacks, Tag 072B] is *true*: the abelian
reading of the same hypothesis, `AlgebraicGeometry.Space.SpacesEtale.
isZero_zExt_koszulComplex_X_zero_of_subsingleton_sheafH`, asks for the vanishing of
`H^q(U, ℱ|_U)`, which fails for `X = U = Spec 𝔽_q` and `ℱ` constant, whereas the source asks
for Serre vanishing of a quasi-coherent module. The two hypotheses here are exactly
[Stacks, Tag 072A] and [Stacks, Tag 01XB] on the étale site; see the module documentation. -/
theorem isZero_zExt_koszulComplex_X_zero_of_isZero_rightDerivedModuleΓ
    (U : SpacesEtale B S hS X)
    (F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) (q : ℕ)
    (M : SheafOfModules.{u + 1} (chartRingSheaf B S hS X U))
    (e : ((topology B S hS X).overPullback AddCommGrpCat.{u + 1} U).obj F ≅
      (SheafOfModules.toSheaf.{u + 1} (chartRingSheaf B S hS X U)).obj M)
    (h : IsZero (((SheafOfModules.toSheaf.{u + 1} (chartRingSheaf B S hS X U) ⋙
        Sheaf.Γ ((topology B S hS X).over U) AddCommGrpCat.{u + 1}).rightDerived q).obj M)) :
    IsZero (AddCommGrpCat.of
      (Abelian.zExt ((koszulComplex B S hS X U).X 0) F (q : ℤ))) := by
  have h1 := h.of_iso ((chartGlobalSectionsComparisonIso B S hS X U q).app M).symm
  have h2 := h1.of_iso
    (((Sheaf.Γ ((topology B S hS X).over U) AddCommGrpCat.{u + 1}).rightDerived q).mapIso e)
  refine isZero_zExt_koszulComplex_X_zero_of_subsingleton_sheafH B S hS X U F q ?_
  exact (Stacks.Cohomology.GlobalSections.subsingleton_sheafH_iff_isZero_rightDerivedΓ.{u + 1}
    ((topology B S hS X).over U) _ q).2 h2

/-- **The column `p = 0` of the `E₁`-page from the vanishing of cohomology *over* the chart.** -/
theorem isZero_zExt_koszulComplex_X_zero_of_subsingleton_sheafH'
    (U : SpacesEtale B S hS X)
    (F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) (q : ℕ)
    (h : Subsingleton (Sheaf.H'.{u + 1} F q U)) :
    IsZero (AddCommGrpCat.of
      (Abelian.zExt ((koszulComplex B S hS X U).X 0) F (q : ℤ))) := by
  have := Stacks.Cohomology.LocalizedSite.preservesFiniteColimits_overPullback.{u + 1, u + 1,
    u + 1} (topology B S hS X) U
  have := Stacks.Cohomology.LocalizedSite.preservesInjectiveObjects_overPullback.{u + 1, u + 1,
    u + 1} (topology B S hS X) U
  refine isZero_zExt_koszulComplex_X_zero_of_subsingleton_sheafH B S hS X U F q ?_
  exact (Stacks.Cohomology.OverObjectCohomology.subsingleton_H_over_iff_subsingleton_H'.{u + 1}
    (topology B S hS X) U (extensionByZeroAdjunction B S hS X U) F q).2 h

end AlgebraicGeometry.Space.SpacesEtale

end
