module

public import StacksFrontier.AlgebraicGeometry.GluedTwistAlgebra.Assemble
public import StacksFrontier.AlgebraicGeometry.ModuleHomGlue.Restrict
public import StacksFrontier.AlgebraicGeometry.Morphism.ChartPullback
public import StacksFrontier.AlgebraicGeometry.ProjTwistCompTwistMap.Comp
public import StacksFrontier.AlgebraicGeometry.TwistLocality.Basic
import StacksFrontier.AlgebraicGeometry.ModuleHomGlue.Pullback

/-!
# Tag 07ZG, assertion (3): the maps on twists

Let `ψ : A ⟶ B` be a homomorphism of quasi-coherent graded `𝒪_S`-algebras, let `U(ψ)` be the open
of `Proj_S(B)` on which it induces a morphism and let `r_ψ : U(ψ) ⟶ Proj_S(A)` be that morphism.
Tag 07ZG's third assertion attaches to `ψ` a map

`θ_n : r_ψ^* 𝒪_{Proj_S(A)}(n) ⟶ 𝒪_{Proj_S(B)}(n)|_{U(ψ)}`

for every `n : ℤ`, described on the piece of `U(ψ)` over an affine open `U` of the base by the
absolute comparison map of Tag 01MY for `ψ_U`.

This file writes the affine-local description down and proves that it determines `θ_n`.

## Main definitions

* `Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwist`: the `n`-th twist of a relative projective
  spectrum, the `n`-th homogeneous piece of the glued graded algebra of Tag 01NR.
* `Stacks.AlgebraicGeometry.Tag07ZGTwist.chartTwistIso`: the inverse image of the `n`-th relative
  twist along the chart over an affine open `U` of the base is the absolute `n`-th twist on
  `Proj Γ(U, A)`. This is the chart identification of Tag 01NR read on the inverse image.
* `Stacks.AlgebraicGeometry.Tag07ZGTwist.chartSourceIso` and `chartTargetIso`: the resulting
  identifications of the inverse images along the inclusion of a piece of `U(ψ)` of the source and
  target of `θ_n` with the source and target of the absolute comparison map of Tag 01MY for `ψ_U`.
* `Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwistChart`: **the affine-local comparison map.**
  Tag 01MY's `θ` for `ψ_U`, conjugated by those two identifications, as a morphism between the
  inverse images along the inclusion of the piece over `U` of the source and target of `θ_n`.
* `Stacks.AlgebraicGeometry.Tag07ZGTwist.chartTheta`: **the adjoint transpose of Tag 01NR's chart
  identification**, a morphism from the `n`-th relative twist to the direct image along the chart
  of the absolute `n`-th twist. This is the form of the chart identification whose sections are
  computable, and the two-chart compatibility is proved there and transposed back.
* `Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeChartSections`: Stacks 00AL's comparison map for
  the glued twists, read at the `n`-th relative twist.
* `Stacks.AlgebraicGeometry.Tag07ZGTwist.twistMapAt`: **Tag 01MY's comparison map read at given
  legs.** A morphism from a scheme to the domain of definition presents the comparison map between
  the inverse images along the two composites, which are named by two equations, so that neither
  the homomorphism nor its domain of definition occurs in the type. This is the form in which the
  comparison maps of a composite compose and in which they can be transported along an equality of
  homomorphisms.

## Main results

* `Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwistMap_unique`: **the affine-local description
  determines the maps on twists.** Two candidates for `θ_n` whose inverse image along the
  inclusion of every piece of `U(ψ)` is the affine-local comparison map are equal.
* `Stacks.AlgebraicGeometry.Tag07ZGTwist.chartTwistIso_hom_eq`: **the chart identifications of Tag
  01NR at two nested affine opens of the base agree.** For affine opens `T ⊆ U` of the base, the
  identification over `T` is the identification over `U` pulled back along the chart transition,
  followed by Tag 01NO's comparison
  `Stacks.AlgebraicGeometry.ProjInclusionTwist.projInclusionTwistIso`. This is the compatibility
  the previous round recorded as the one thing missing for the existence of `θ_n`, and it is the
  main content of this file.
* `Stacks.AlgebraicGeometry.Tag07ZGTwist.cmpGen_agreeOn_cmpNested`: for a nested pair of affine
  opens of the base, the *glued* comparison of Tag 01NO is the *nested* one. `ChartData`'s
  identifications are glued from the former and Tag 01NO's isomorphism is the latter, so this is
  what connects the two.
* `Stacks.AlgebraicGeometry.Tag07ZGTwist.chartTheta_comp_pushNested`: the same compatibility on
  the direct-image side of the adjunction, where the sections are computable.
* `Stacks.AlgebraicGeometry.Tag07ZGTwist.twistMapAt_comp`: **Tag 01MZ's third assertion in
  composable form.** Tag 01MY's comparison maps read at legs out of one scheme compose, so the
  assertion can be chained; this is what a glueing argument over a cover of the base needs, and
  the congruence isomorphisms that the assertion carries are absorbed into the legs.
* `Stacks.AlgebraicGeometry.Tag07ZGTwist.twistMapAt_nested`: **the comparison maps of Tag 01MY
  over a nested pair of affine opens of the base are compatible with the comparison maps of the
  restrictions.** This is the agreement of the affine-local data of `θ_n` on a nested overlap,
  read at the absolute level, and it is the mathematical content of the existence of `θ_n`.
* `Stacks.AlgebraicGeometry.Tag07ZGTwist.twistMapAt_congr`: Tag 01MY's comparison map transported
  along an **equality of graded ring homomorphisms**, which is what the two factorizations of a
  single homomorphism `Γ(U, A) ⟶ Γ(T, B)` need.
* `Stacks.AlgebraicGeometry.Tag07ZGTwist.localApp_eq_of_refine`: **local data on a cover whose
  overlaps are covered by members below both, compatible for nested pairs, satisfy the
  compatibility hypothesis of
  `Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_restrict_cover` for every pair.**
* `Stacks.AlgebraicGeometry.Tag07ZGTwist.twistMapAt_comp_leg`: **Tag 01MY's comparison map read at
  legs is pseudo-natural in the leg.** Precomposing the presenting morphism with a further
  morphism of schemes gives the inverse image of the comparison map at the original legs,
  conjugated by the pseudofunctoriality identifications of the inverse image.
* `Stacks.AlgebraicGeometry.Tag07ZGTwist.pullback_five_comp_leg` and `pullback_three_comp_leg`: the
  same pseudo-naturality for an arbitrary morphism between two inverse images, and for an
  arbitrary morphism out of one inverse image — the shapes of Tag 01MY's comparison map and of a
  chart identification.
* `Stacks.AlgebraicGeometry.Tag07ZGTwist.three_comp_leg_nested` and
  `three_comp_leg_nested_proj`: **a nested compatibility of a morphism out of an inverse image,
  read at one canonical pair of legs, holds at every pair of legs.** This is the whole transport
  the affine-local comparison map of `θ_n` needs, at the level of variables; the second form has
  the two projective spectra and the two absolute twists substituted, which is what makes its
  concrete instances affordable.

## The route

The source of `θ_n` is an inverse image along `r_ψ` and the target an inverse image along the
inclusion of `U(ψ)`, so over the piece of `U(ψ)` over an affine open `U` of the base both become
inverse images along the two legs of Tag 07ZG's defining square for `r_ψ`:
`Stacks.AlgebraicGeometry.Tag07ZGMorphism.homOfLE_comp_relativeMapHom` factors the inclusion of the
piece followed by `r_ψ` through the absolute morphism of Tag 01MY and the chart of `Proj_S(A)`, and
`AlgebraicGeometry.Scheme.Hom.isoImage_inv_ι` factors the inclusion of the piece followed by the
inclusion of `U(ψ)` through the inclusion of the absolute domain of definition and the chart of
`Proj_S(B)`. Pseudofunctoriality of the inverse image turns each factorization into an
identification, and the chart identifications of Tag 01NR replace the inverse image of a relative
twist along a chart by the absolute twist on that chart. What is left between the two is exactly
the source and target of Tag 01MY's comparison map for `ψ_U`.

Uniqueness is then the separation half
`Stacks.AlgebraicGeometry.Tag07ZGTwistLocality.twistMap_ext`: the pieces cover `U(ψ)`, so a
morphism of sheaves of modules on `U(ψ)` is determined by its restrictions to them, and the
restriction along an open immersion is the inverse image by
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`.

## Implementation notes

The inclusion of the piece over `U` into `U(ψ)` is composed with `r_ψ` and with the inclusion of
`U(ψ)` into factorizations that both begin with the *inverse* of
`AlgebraicGeometry.Scheme.Hom.isoImage`, rather than with the identification of the piece with the
absolute domain of definition in the other direction. That keeps `chartSourceIso` and
`chartTargetIso` composites of components of the pseudofunctoriality isomorphisms and of the chart
identification, with no inverse of a functor image to cancel; the price is that the affine-local
comparison map is the inverse image of Tag 01MY's `θ` along an isomorphism of schemes rather than
`θ` itself.

## How the two chart identifications are compared

`ChartData` carries one identification per chart and no relation between two of them. The relation
is recovered from the glueing datum the identifications come from, and the passage between the
inverse-image side — where the identifications live and where the sections carry no description —
and the direct-image side — where a section over an open of the relative Proj *is* a section over
its inverse image — is the adjunction.

* `Stacks.AlgebraicGeometry.PushforwardCocycle.transpose_cocycle` turns the composition law on the
  inverse-image side into one on the direct-image side, and the transpose is a bijection, so the
  implication can be run backwards: the identity of the two transposes *is* the identity of the
  two morphisms out of the inverse image.
* The transpose of a chart identification is `chartTheta`, the restriction unit followed by the
  direct image of Tag 01NR's identification; over an open inside the inverse image of the affine
  open it acts by Stacks 00AL's comparison map `relativeChartSections`.
* The transpose of Tag 01NO's twist isomorphism, pushed forward, is
  `Stacks.AlgebraicGeometry.ChartTransRelativeProj.pushNested`, whose action on sections is
  `cmpNested`.
* Stacks 00AL's comparison maps at two charts differ by the glueing datum's transition, which for
  the glued twists is `Stacks.AlgebraicGeometry.ChartTransRelativeProj.cmpGen`. Over a *nested*
  pair of affine opens of the base that glued comparison is the *nested* one, by the nested
  cocycle of Tag 01MZ: `cmpGen_agreeOn_cmpNested`.

## Where the existence of `θ_n` is

**The existence of `θ_n` is not proved in this file.** The pieces of `U(ψ)` cover it and the
affine-local comparison maps above are the local data, so what is owed is their agreement on
overlaps, which `Stacks.AlgebraicGeometry.Tag07ZGMorphism.chartImage_inf_eq_iSup` reduces to the
case of a nested pair `T ⊆ U` of affine opens of the base, and that nested agreement at the
absolute level is `twistMapAt_nested`. The glueing machinery is here too:
`localApp_eq_of_refine` turns the nested compatibility into the compatibility hypothesis of
`Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_restrict_cover` for an arbitrary pair,
for exactly the refinement `chartImage_inf_eq_iSup` supplies.

The nested agreement of the affine-local comparison maps themselves is
`Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwistChart_nested` in
`StacksFrontier/AlgebraicGeometry/Morphism/TwistGlue.lean`, and `θ_n` is
`Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwistMap` in
`StacksFrontier/AlgebraicGeometry/Morphism/TwistExists.lean`, where it is glued from the local data.

**The two halves of that agreement must name the comparison map of the restriction
`Γ(U, A) ⟶ Γ(T, A)` the same way, because identifying the two available spellings exceeds the
kernel's budget.**
`chartTwistIso_hom_eq` names it
`Stacks.AlgebraicGeometry.ProjInclusionTwist.projInclusionTwistIso`, whose six factors are written
with the bundle spellings `(projMapData …).hom` and `(projMapData …).twistMap n`, while
`twistMapAt_nested` names it `twistMapAt` of `Stacks.AlgebraicGeometry.ProjTwistCompare.twistMap`,
written with `mapHom` and `twistMap`. The two spellings are equal by
`Stacks.AlgebraicGeometry.ProjTwistCompare.projMapData_hom` and `projMapData_twistMap`, both
`rfl`, and converting the two *composites* into one another is not available: asked for by `rfl`
after `Stacks.AlgebraicGeometry.ProjInclusionTwist.projInclusionTwistMap_eq`, and asked for
through `simp only` with those two equations, the kernel exceeds its deterministic budget both
ways. `StacksFrontier/AlgebraicGeometry/ProjInclusionTwist/Legs.lean` builds the comparison in the
`mapHom`/`twistMap` spelling instead of converting into it, by taking the translation at the level
of variables; `Stacks.AlgebraicGeometry.Tag07ZGTwist.chartTwistIso_hom_eq_twistMapAt` is the
two-chart compatibility with Tag 01NO's comparison map replaced by `twistMapAt` at the legs
`Stacks.AlgebraicGeometry.RelativeProj.projInclusionMap` and the identity, so both halves name
it the same way.

**The pseudo-naturality of the comparison maps in their leg is proved here.** The comparison map
of the restriction appears in `twistMapAt_nested` at a leg out of `U(ψ_T)` and in
`chartTwistIso_hom_eq_twistMapAt` at a leg out of `Proj Γ(T, A)`, and the first leg is the second
precomposed with `mapHom (A.grading T) (B.grading T) (ψ.sectionHom T)`, since the inclusion of a
domain of definition is a monomorphism. Conjugating the two-chart compatibility into the piece
over `T` therefore asks for the inverse image along a morphism of a comparison map at a leg, which
is the comparison map at the composed leg conjugated by the pseudofunctoriality isomorphisms. That
is `twistMapAt_comp_leg`, whose content is
`AlgebraicGeometry.Scheme.Modules.pseudofunctor_associativity` read at a module together with the
naturality of the pseudofunctoriality identification; `pullback_three_comp_leg` is the companion
for a morphism out of an inverse image whose target is not itself an inverse image, which is the
shape of a chart identification, and `three_comp_leg_nested` assembles the two into the whole
nested compatibility — all at the level of variables.

**The transport of the two-chart compatibility to the legs out of a piece of `U(ψ)` is
`Stacks.AlgebraicGeometry.Tag07ZGTwist.chartTwistIso_hom_nested`.** The general transport,
abstracting over the two projective spectra as *schemes*, cannot be instantiated at a concrete
pair of affine opens of the base: each instance asks the kernel to check
`Stacks.AlgebraicGeometry.ProjTwistCompare.twistingSheaf (A.grading T) n` at the type
`(AlgebraicGeometry.Proj (A.grading T)).Modules` once for every sheaf of modules it abstracts
over, the kernel carries no reducibility attributes, and unfolding `AlgebraicGeometry.Proj` that
often exceeds its deterministic budget although elaboration succeeds. The substitution is
therefore taken **once, at the level of variables**, in `three_comp_leg_nested_proj`, which is
`three_comp_leg_nested` with the two spectra, the domain of definition and the two absolute twists
put in; every concrete instance is then a substitution and demands no conversion.

**The agreement of the affine-local comparison maps themselves is proved in the sibling file.**
`relativeTwistChart` is Tag 01MY's `θ` for `ψ_U` conjugated by `chartSourceIso` and
`chartTargetIso`, and each of those is the three-factor transport of a chart identification
followed by the pseudofunctoriality identifications of the two legs of the defining square;
`chartTwistIso_hom_nested` read for `A` and for `B` through that conjugation, with
`twistMapAt_nested` spliced between them, is the nested agreement, and the glueing from there is
`localApp_eq_of_refine` and
`Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_restrict_cover`.

**The affine opens of the base are indexed by `AlgebraicGeometry.Scheme.affineOpens` from
`chartTwistIso` onwards**, the same spelling as the glueing layer of the chart identifications,
because converting a statement of the size of the two-chart compatibility between that spelling
and `Stacks.AlgebraicGeometry.RelativeProjMapDomain.AffineOpen` costs the whole deterministic
budget. The declarations above `chartTwistIso` keep the second spelling, where no projection of
the affine open occurs inside a statement and the two are interchangeable for free.

## Implementation notes

The elaboration budget at this instance is the binding constraint, and the following facts shape
the proofs below.

* **A statement about a `TopCat.Sheaf.LocalModuleEquiv`'s `naturality` cannot be reached at these
  comparisons**, neither by projecting it nor by instantiating a generic naturality lemma at the
  concrete comparison: both exhaust the recursion limit, as
  `StacksFrontier/AlgebraicGeometry/ChartTransNonNested/RelativeProj.lean` already records. Every
  cover argument below therefore goes through the generic `agreeOn_of_cover` and
  `isComposite_of_cover`, whose conclusions are applications of `AgreeOn` and `IsComposite` and
  never mention a component.
* **The identification of the pieces of Tag 01NR's twist datum with Tag 01NO's glued twists is a
  chain of delta steps through every structure literal the datum is assembled from.** It is
  survivable in a *statement* and not in a proof term matched against a goal. It is therefore
  taken once, in `toGluedSection`, and every statement downstream is phrased in the vocabulary of
  `relativeChartSections`, which is built from it.
* **`AlgebraicGeometry.Scheme.affineOpens` and
  `Stacks.AlgebraicGeometry.RelativeProjMapDomain.AffineOpen` are the same subtype spelled two
  ways**, and the second is an `abbrev` while the first goes through a semireducible `def`.
  Reconciling them is cheap inside a statement and expensive when a proof term's type is matched
  against a goal, so each layer below uses **one** spelling throughout: the glueing layer the
  first, and the layer of `chartTwistIso` the second.
* **A rewrite whose pattern leaves the module of a component of `pullbackComp` or `pullbackCongr`
  to be inferred does not fire**, because `Stacks.AlgebraicGeometry.ProjTwistCompare.twistingSheaf`
  is not spelled at the type `(AlgebraicGeometry.Proj 𝒜).Modules` and the metavariable cannot be
  assigned without unfolding `AlgebraicGeometry.Proj`. The congruence cancellations below are
  therefore applied with the module supplied explicitly, and the sections they are used in make
  `AlgebraicGeometry.Proj` locally reducible at implicit transparency.
* **A congruence isomorphism's equation is passed as an argument rather than written
  `a.trans b.symm`.** With the composite equation spelled out in the statement, the rewrite has to
  solve the proof term `Eq.trans ?a (Eq.symm ?b)` by unification, and proof irrelevance discharges
  it without assigning the metavariables; the rewrite then fails on a pattern that is present.

## References

* [Stacks Project, Tag 07ZG](https://stacks.math.columbia.edu/tag/07ZG)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01MZ](https://stacks.math.columbia.edu/tag/01MZ)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 00AL](https://stacks.math.columbia.edu/tag/00AL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjShared
open Stacks.AlgebraicGeometry.ProjTwistChain
open Stacks.AlgebraicGeometry.ProjTwistCompare
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjTwists
open Stacks.AlgebraicGeometry.RelativeProjMapDomain
open Stacks.AlgebraicGeometry.Tag07ZGMorphism

namespace Stacks.AlgebraicGeometry.Tag07ZGTwist

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

universe u

variable {S : Scheme.{u}} {A B : SheafGradedAlgebra S}

/-! ### The relative twists and their chart identifications -/

/-- **The `n`-th twist of a relative projective spectrum**: the `n`-th homogeneous piece of the
glued graded algebra of Tag 01NR. -/
public abbrev relativeTwist (A : SheafGradedAlgebra S) (n : ℤ) :
    (relativeProj A).scheme.Modules :=
  (GluedTwistAlgebra.twistDataOfGradedAlgebra A).algebra.piece n

/-- **The inverse image of the `n`-th relative twist along the chart over an affine open `U` of the
base is the absolute `n`-th twist on `Proj Γ(U, A)`.** This is Tag 01NR's chart identification,
which is stated for the restriction along the chart, traded for the inverse image by
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`. -/
public def chartTwistIso (A : SheafGradedAlgebra S) (n : ℤ) (U : S.affineOpens) :
    (Scheme.Modules.pullback ((relativeProj A).chart U.1 U.2)).obj (relativeTwist A n) ≅
      twistingSheaf (A.grading U.1) n :=
  ((Scheme.Modules.restrictFunctorIsoPullback ((relativeProj A).chart U.1 U.2)).app
      (relativeTwist A n)).symm ≪≫
    (GluedTwistAlgebra.twistDataOfGradedAlgebra A).chartData.chartIso U.1 U.2 n

/-! ### The two factorizations of the inclusion of a piece -/

variable (ψ : SheafGradedAlgebraHom A B)

/-- The inclusion of the piece of `U(ψ)` over an affine open `U` of the base. -/
public abbrev pieceIncl (U : S.affineOpens) :
    (chartImage ψ U).toScheme ⟶ ψ.relativeMapDomain.toScheme :=
  (relativeProj B).scheme.homOfLE (chartImage_le ψ U)

/-- The identification of the absolute domain of definition over an affine open `U` of the base
with the piece of `U(ψ)` over `U`, as the image of an open under the chart. -/
public abbrev chartDomainIso (U : S.affineOpens) :
    (mapDomain (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)).toScheme ≅
      (chartImage ψ U).toScheme :=
  ((relativeProj B).chart U.1 U.2).isoImage
    (mapDomain (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1))

/-- **The inclusion of the piece over `U` followed by `r_ψ`**, factored through the absolute
morphism of Tag 01MY and the chart of `Proj_S(A)` over `U`. This is the defining equation of
`r_ψ`. -/
public theorem pieceIncl_comp_relativeMapHom (U : S.affineOpens) :
    pieceIncl ψ U ≫ relativeMapHom ψ =
      (chartDomainIso ψ U).inv ≫
        mapHom (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1) ≫
          (relativeProj A).chart U.1 U.2 :=
  homOfLE_comp_relativeMapHom ψ U

/-- **The inclusion of the piece over `U` followed by the inclusion of `U(ψ)`**, factored through
the inclusion of the absolute domain of definition and the chart of `Proj_S(B)` over `U`. -/
public theorem pieceIncl_comp_ι (U : S.affineOpens) :
    pieceIncl ψ U ≫ ψ.relativeMapDomain.ι =
      (chartDomainIso ψ U).inv ≫
        (mapDomain (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)).ι ≫
          (relativeProj B).chart U.1 U.2 := by
  rw [Scheme.homOfLE_ι, Scheme.Hom.isoImage_inv_ι]

/-! ### The affine-local comparison map -/

/-- **The source of `θ_n`, read over the piece over an affine open `U` of the base.** The inverse
image along the inclusion of the piece of the inverse image along `r_ψ` of the `n`-th relative
twist is the inverse image along an isomorphism of schemes of the source of Tag 01MY's comparison
map for `ψ_U`. -/
public def chartSourceIso (n : ℤ) (U : S.affineOpens) :
    (Scheme.Modules.pullback (pieceIncl ψ U)).obj
        ((Scheme.Modules.pullback (relativeMapHom ψ)).obj (relativeTwist A n)) ≅
      (Scheme.Modules.pullback (chartDomainIso ψ U).inv).obj
        ((Scheme.Modules.pullback
          (mapHom (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1))).obj
            (twistingSheaf (A.grading U.1) n)) :=
  (Scheme.Modules.pullbackComp (pieceIncl ψ U) (relativeMapHom ψ)).app (relativeTwist A n) ≪≫
    (Scheme.Modules.pullbackCongr (pieceIncl_comp_relativeMapHom ψ U)).app (relativeTwist A n) ≪≫
    ((Scheme.Modules.pullbackComp (chartDomainIso ψ U).inv
      (mapHom (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1) ≫
        (relativeProj A).chart U.1 U.2)).app (relativeTwist A n)).symm ≪≫
    (Scheme.Modules.pullback (chartDomainIso ψ U).inv).mapIso
      (((Scheme.Modules.pullbackComp (mapHom (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1))
          ((relativeProj A).chart U.1 U.2)).app (relativeTwist A n)).symm ≪≫
        (Scheme.Modules.pullback
          (mapHom (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1))).mapIso
            (chartTwistIso A n U))

/-- **The target of `θ_n`, read over the piece over an affine open `U` of the base.** The inverse
image along the inclusion of the piece of the inverse image along the inclusion of `U(ψ)` of the
`n`-th relative twist is the inverse image along an isomorphism of schemes of the target of Tag
01MY's comparison map for `ψ_U`. -/
public def chartTargetIso (n : ℤ) (U : S.affineOpens) :
    (Scheme.Modules.pullback (pieceIncl ψ U)).obj
        ((Scheme.Modules.pullback ψ.relativeMapDomain.ι).obj (relativeTwist B n)) ≅
      (Scheme.Modules.pullback (chartDomainIso ψ U).inv).obj
        ((Scheme.Modules.pullback
          (mapDomain (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)).ι).obj
            (twistingSheaf (B.grading U.1) n)) :=
  (Scheme.Modules.pullbackComp (pieceIncl ψ U) ψ.relativeMapDomain.ι).app (relativeTwist B n) ≪≫
    (Scheme.Modules.pullbackCongr (pieceIncl_comp_ι ψ U)).app (relativeTwist B n) ≪≫
    ((Scheme.Modules.pullbackComp (chartDomainIso ψ U).inv
      ((mapDomain (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)).ι ≫
        (relativeProj B).chart U.1 U.2)).app (relativeTwist B n)).symm ≪≫
    (Scheme.Modules.pullback (chartDomainIso ψ U).inv).mapIso
      (((Scheme.Modules.pullbackComp
          (mapDomain (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)).ι
          ((relativeProj B).chart U.1 U.2)).app (relativeTwist B n)).symm ≪≫
        (Scheme.Modules.pullback
          (mapDomain (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1)).ι).mapIso
            (chartTwistIso B n U))

/-- **The affine-local comparison map on the `n`-th twist.** Over the piece of `U(ψ)` over an
affine open `U` of the base, Tag 01MY's comparison map `θ` for the induced homomorphism
`Γ(U, A) ⟶ Γ(U, B)` of graded rings of sections, conjugated by the identifications of the source
and the target. -/
public def relativeTwistChart (n : ℤ) (U : S.affineOpens) :
    (Scheme.Modules.pullback (pieceIncl ψ U)).obj
        ((Scheme.Modules.pullback (relativeMapHom ψ)).obj (relativeTwist A n)) ⟶
      (Scheme.Modules.pullback (pieceIncl ψ U)).obj
        ((Scheme.Modules.pullback ψ.relativeMapDomain.ι).obj (relativeTwist B n)) :=
  (chartSourceIso ψ n U).hom ≫
    (Scheme.Modules.pullback (chartDomainIso ψ U).inv).map
      (twistMap (A.grading U.1) (B.grading U.1) (ψ.sectionHom U.1) n) ≫
    (chartTargetIso ψ n U).inv

/-! ### Uniqueness -/

/-- The restriction of a morphism of sheaves of modules along an open immersion is its inverse
image, read through `AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`. -/
public theorem restrictFunctor_map_eq_of_pullback_map_eq {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] {M N : Y.Modules} {φ φ' : M ⟶ N}
    (h : (Scheme.Modules.pullback f).map φ = (Scheme.Modules.pullback f).map φ') :
    (Scheme.Modules.restrictFunctor f).map φ = (Scheme.Modules.restrictFunctor f).map φ' := by
  have e := Scheme.Modules.restrictFunctorIsoPullback f
  have hφ : (Scheme.Modules.restrictFunctor f).map φ ≫ e.hom.app N =
      e.hom.app M ≫ (Scheme.Modules.pullback f).map φ := e.hom.naturality φ
  have hφ' : (Scheme.Modules.restrictFunctor f).map φ' ≫ e.hom.app N =
      e.hom.app M ≫ (Scheme.Modules.pullback f).map φ' := e.hom.naturality φ'
  haveI : Mono (e.hom.app N) := (inferInstance : Mono (e.app N).hom)
  refine (cancel_mono (e.hom.app N)).mp (hφ.trans ?_)
  exact (congrArg (fun α => e.hom.app M ≫ α) h).trans hφ'.symm

/-- **Stacks Project, Tag 07ZG.** *The affine-local description determines the maps on twists.*

Two candidates for the `n`-th map on twists whose inverse image along the inclusion of the piece of
`U(ψ)` over every affine open of the base is the affine-local comparison map
`Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwistChart` are equal.

The pieces cover `U(ψ)`, so a morphism of sheaves of modules on `U(ψ)` is determined by its
restrictions to them; this is that separation statement with the restrictions traded for inverse
images. -/
public theorem relativeTwistMap_unique (n : ℤ)
    {θ θ' : (Scheme.Modules.pullback (relativeMapHom ψ)).obj (relativeTwist A n) ⟶
      (Scheme.Modules.pullback ψ.relativeMapDomain.ι).obj (relativeTwist B n)}
    (hθ : ∀ U : S.affineOpens,
      (Scheme.Modules.pullback (pieceIncl ψ U)).map θ = relativeTwistChart ψ n U)
    (hθ' : ∀ U : S.affineOpens,
      (Scheme.Modules.pullback (pieceIncl ψ U)).map θ' = relativeTwistChart ψ n U) :
    θ = θ' :=
  Tag07ZGTwistLocality.twistMap_ext ψ (GluedTwistAlgebra.twistDataOfGradedAlgebra A)
    (GluedTwistAlgebra.twistDataOfGradedAlgebra B) n fun U =>
      restrictFunctor_map_eq_of_pullback_map_eq (pieceIncl ψ U)
        ((hθ U).trans (hθ' U).symm)

/-! ### Generic ingredients of the two-chart compatibility -/

section Generic

/-- **Two local isomorphisms which become the same after one further comparison agree.** The
further comparison is a linear equivalence on the sections over the open in question, hence
injective there. -/
public theorem agreeOn_of_isComposite {X : TopCat.{u}} {𝒪 : (Opens X)ᵒᵖ ⥤ RingCat.{u}}
    {M N P : PresheafOfModules.{u} 𝒪} {W₀ W₁ W₂ : Opens X}
    (e₀ : TopCat.Sheaf.LocalModuleEquiv M N W₁) (e₀' : TopCat.Sheaf.LocalModuleEquiv M N W₂)
    (e₁ : TopCat.Sheaf.LocalModuleEquiv N P W₀) (e₂ : TopCat.Sheaf.LocalModuleEquiv M P W₀)
    (V : Opens X) (hV₀ : V ≤ W₀) (hV₁ : V ≤ W₁) (hV₂ : V ≤ W₂)
    (h : ChartTransRelativeProj.IsComposite e₀ e₁ e₂ V hV₀ hV₁)
    (h' : ChartTransRelativeProj.IsComposite e₀' e₁ e₂ V hV₀ hV₂) :
    ChartTransRelativeProj.AgreeOn e₀ e₀' V hV₁ hV₂ :=
  fun s => (e₁.app V hV₀).injective ((h s).trans (h' s).symm)

/-- The composition law for local isomorphisms, applied to a section: the predicate unfolded, at
the level of variables. -/
public theorem isComposite_apply {X : TopCat.{u}} {𝒪 : (Opens X)ᵒᵖ ⥤ RingCat.{u}}
    {M N P : PresheafOfModules.{u} 𝒪} {W₀ W₁ : Opens X}
    {e₀ : TopCat.Sheaf.LocalModuleEquiv M N W₁} {e₁ : TopCat.Sheaf.LocalModuleEquiv N P W₀}
    {e₂ : TopCat.Sheaf.LocalModuleEquiv M P W₀} {V : Opens X} {hV₀ : V ≤ W₀} {hV₁ : V ≤ W₁}
    (hc : ChartTransRelativeProj.IsComposite e₀ e₁ e₂ V hV₀ hV₁) (s : M.obj (op V)) :
    e₁.app V hV₀ (e₀.app V hV₁ s) = e₂.app V hV₀ s :=
  hc s

variable {X Y : Scheme.{u}}

/-- The adjoint transpose of a morphism out of an inverse image is the hom-equivalence of the
inverse-image--direct-image adjunction. -/
public theorem transpose_eq_homEquiv (f : X ⟶ Y) (M : Y.Modules) {N : X.Modules}
    (ψ : (Scheme.Modules.pullback f).obj M ⟶ N) :
    PushforwardCocycle.transpose f M ψ =
      (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv M N ψ :=
  (Adjunction.homEquiv_unit _ _ _ _).symm

/-- **The adjoint transpose is injective.** It is a bijection, being the hom-equivalence of an
adjunction; this is the direction used to recover an identification of inverse images from the
equality of the transposes. -/
public theorem transpose_injective (f : X ⟶ Y) (M : Y.Modules) {N : X.Modules}
    {ψ ψ' : (Scheme.Modules.pullback f).obj M ⟶ N}
    (h : PushforwardCocycle.transpose f M ψ = PushforwardCocycle.transpose f M ψ') : ψ = ψ' :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv M N).injective
    (((transpose_eq_homEquiv f M ψ).symm.trans h).trans (transpose_eq_homEquiv f M ψ'))

/-- **The transpose of an identification of an inverse image which is itself an identification of
a restriction.** For an open immersion the inverse image and the restriction are identified by
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`, so an identification of the
restriction gives one of the inverse image; its transpose is the unit of the
restriction--direct-image adjunction followed by the direct image of the given identification,
with no trace of the inverse image left. -/
public theorem transpose_restrictIso (a : X ⟶ Y) [IsOpenImmersion a] (M : Y.Modules)
    (K : X.Modules) (E : (Scheme.Modules.restrictFunctor a).obj M ≅ K) :
    PushforwardCocycle.transpose a M
        (((Scheme.Modules.restrictFunctorIsoPullback a).app M).symm ≪≫ E).hom =
      (Scheme.Modules.restrictAdjunction a).unit.app M ≫
        (Scheme.Modules.pushforward a).map E.hom := by
  calc PushforwardCocycle.transpose a M
        (((Scheme.Modules.restrictFunctorIsoPullback a).app M).symm ≪≫ E).hom
      = ((Scheme.Modules.restrictAdjunction a).unit.app M ≫
            (Scheme.Modules.pushforward a).map
              ((Scheme.Modules.restrictFunctorIsoPullback a).hom.app M)) ≫
          (Scheme.Modules.pushforward a).map
            (((Scheme.Modules.restrictFunctorIsoPullback a).app M).inv ≫ E.hom) := by
        rw [ProjTwistTheta.restrictUnit_comp_map_restrictFunctorIsoPullback a M]
        rfl
    _ = (Scheme.Modules.restrictAdjunction a).unit.app M ≫
          (Scheme.Modules.pushforward a).map E.hom := by
        rw [Category.assoc, ← Functor.map_comp, Iso.app_inv, Iso.hom_inv_id_app_assoc]

/-- **A morphism of sheaves of modules is determined by its components over the opens inside a
given open, as soon as the restriction maps of its target to those opens are injective.** -/
public theorem hom_ext_of_resLE_injective {M Q : X.Modules} {W₀ : X.Opens}
    (hinj : ∀ V : X.Opens, Function.Injective
      (Q.val.resLE (inf_le_left : V ⊓ W₀ ≤ V)))
    {φ φ' : M ⟶ Q}
    (h : ∀ V : X.Opens, V ≤ W₀ → ∀ s : M.val.obj (op V),
      φ.val.app (op V) s = φ'.val.app (op V) s) :
    φ = φ' := by
  refine Scheme.Modules.hom_ext _ _ fun V => ConcreteCategory.hom_ext _ _ fun s => ?_
  refine hinj V ?_
  exact ((PresheafOfModules.app_resLE φ.val (inf_le_left : V ⊓ W₀ ≤ V) s).symm.trans
      (h (V ⊓ W₀) inf_le_right _)).trans
    (PresheafOfModules.app_resLE φ'.val (inf_le_left : V ⊓ W₀ ≤ V) s)

/-- **A restriction map of a direct image along a pair of opens with the same inverse image is
injective**: it is a restriction map of the module itself between two opens which are equal. -/
public theorem injective_pushforward_resLE (a : X ⟶ Y) (N : X.Modules) {V W : Y.Opens}
    (hWV : W ≤ V) (hpre : a ⁻¹ᵁ W = a ⁻¹ᵁ V) :
    Function.Injective
      (((Scheme.Modules.pushforward a).obj N).val.resLE hWV) := by
  have : IsIso (N.presheaf.map (homOfLE (a.preimage_mono hWV)).op) :=
    ChartTransRelativeProj.isIso_presheaf_map_of_eq N hpre _
  exact (ConcreteCategory.bijective_of_isIso
    (N.presheaf.map (homOfLE (a.preimage_mono hWV)).op)).1

end Generic

/-! ### The two chart identifications of Tag 01NR over a nested pair -/

section TwoCharts

open Stacks.AlgebraicGeometry.ChartTransRelativeProj

variable (A)

/-- **For a nested pair of affine opens of the base, the glued comparison of Tag 01NO is the
nested one.** `cmpGen` is glued from the comparisons through the charts of the affine opens below
both; over the inverse image of such an affine open `r` the nested cocycle identifies the
comparison through `r` with the nested comparison, and the affine opens below the smaller member
cover its inverse image. -/
public theorem cmpGen_agreeOn_cmpNested (n : ℤ) (hcoc : IsNestedCocycle A n)
    (T U : S.Opens) (h : T ≤ U) (hT : IsAffineOpen T) (hU : IsAffineOpen U)
    (hpre : (relativeProj A).toBase ⁻¹ᵁ T ≤ (relativeProj A).toBase ⁻¹ᵁ U)
    (V : (relativeProj A).scheme.Opens) (hV : V ≤ (relativeProj A).toBase ⁻¹ᵁ T) :
    AgreeOn (cmpGen A T U hT hU n hpre hcoc) (cmpNested A T U h hT hU n) V hV hV := by
  refine agreeOn_of_cover (isSheaf_pushChart A T hT n) (cmpGen A T U hT hU n hpre hcoc)
    (cmpNested A T U h hT hU n)
    (fun r : {r : S.affineOpens // (r.1 : S.Opens) ≤ T} =>
      (relativeProj A).toBase ⁻¹ᵁ (r.1.1 : S.Opens))
    (fun r V₀ hV₀ hV₁ hV₀r s => ?_) V hV hV (hV.trans (le_iSup_preimage_affine_le A T))
  have hrT : (r.1.1 : S.Opens) ≤ T := r.2
  have hrU : (r.1.1 : S.Opens) ≤ U := r.2.trans h
  refine (cmpGen_agreeOn_meetLoc A T U hT hU n hpre hcoc r.1 hrT hrU V₀ hV₀ hV₀r s).trans ?_
  exact agreeOn_of_isComposite (meetLoc A T U hT hU n ⟨r.1, le_inf hrT hrU⟩)
    (cmpNested A T U h hT hU n) (cmpNested A (r.1.1 : S.Opens) T hrT r.1.2 hT n)
    (cmpNested A (r.1.1 : S.Opens) U hrU r.1.2 hU n) V₀ hV₀r hV₀r hV₁
    (isComposite_meetLoc A T U hT hU n ⟨r.1, le_inf hrT hrU⟩ hrT hrU V₀ hV₀r)
    (hcoc (r.1.1 : S.Opens) T U hrT h hrU r.1.2 hT hU V₀ hV₀r hV₁) s

/-- **The nested comparison of Tag 01NO composes with the glued comparison through a smaller
chart.** This is `Stacks.AlgebraicGeometry.ChartTransRelativeProj.cmpGen_comp` with its first
factor traded for the nested comparison by
`Stacks.AlgebraicGeometry.Tag07ZGTwist.cmpGen_agreeOn_cmpNested`. -/
public theorem isComposite_cmpNested_cmpGen (n : ℤ) (hc : IsNestedCocycle A n)
    (T U R : S.Opens) (h : T ≤ U) (hT : IsAffineOpen T) (hU : IsAffineOpen U)
    (hR : IsAffineOpen R)
    (hpre : (relativeProj A).toBase ⁻¹ᵁ T ≤ (relativeProj A).toBase ⁻¹ᵁ U)
    (hRT : (relativeProj A).toBase ⁻¹ᵁ R ≤ (relativeProj A).toBase ⁻¹ᵁ T)
    (hRU : (relativeProj A).toBase ⁻¹ᵁ R ≤ (relativeProj A).toBase ⁻¹ᵁ U)
    (V : (relativeProj A).scheme.Opens) (hVR : V ≤ (relativeProj A).toBase ⁻¹ᵁ R)
    (hVT : V ≤ (relativeProj A).toBase ⁻¹ᵁ T) :
    IsComposite (cmpNested A T U h hT hU n) (cmpGen A R T hR hT n hRT hc)
      (cmpGen A R U hR hU n hRU hc) V hVR hVT :=
  isComposite_of_agreeOn (cmpNested A T U h hT hU n) (cmpGen A T U hT hU n hpre hc)
    (cmpGen A R T hR hT n hRT hc) (cmpGen A R U hR hU n hRU hc) V hVR hVT hVT
    (fun s => (cmpGen_agreeOn_cmpNested A n hc T U h hT hU hpre V hVT s).symm)
    (cmpGen_comp A n hc R T U hR hT hU hRT hpre hRU V hVR hVT)

/-- Cancelling a local isomorphism against its own inverse, at the level of variables. -/
public theorem symm_app_apply_of_isComposite {X : TopCat.{u}} {𝒪 : (Opens X)ᵒᵖ ⥤ RingCat.{u}}
    {M N P : PresheafOfModules.{u} 𝒪} {W₀ W₁ : Opens X}
    (e₀ : TopCat.Sheaf.LocalModuleEquiv M N W₁) (e₁ : TopCat.Sheaf.LocalModuleEquiv N P W₀)
    (e₂ : TopCat.Sheaf.LocalModuleEquiv M P W₀) {V : Opens X} (hV₀ : V ≤ W₀) (hV₁ : V ≤ W₁)
    (hc : ChartTransRelativeProj.IsComposite e₀ e₁ e₂ V hV₀ hV₁) (s : M.obj (op V)) :
    ((e₁.app V hV₀).symm) (e₂.app V hV₀ s) = e₀.app V hV₁ s :=
  (congrArg (fun z => ((e₁.app V hV₀).symm) z) (hc s).symm).trans
    (LinearEquiv.symm_apply_apply (e₁.app V hV₀) (e₀.app V hV₁ s))

/-- **Over an open inside the inverse image of an affine open of the base below the smaller
member, the non-nested chart transition of the glued twists is Tag 01NO's nested comparison.**
The transition cancels the smaller affine open's two glued comparisons
(`Stacks.AlgebraicGeometry.GluedTwistAlgebra.trans_app_cmpGen`), and the nested comparison
composes with them in the same way. -/
public theorem trans_eq_cmpNested_of_le (n : ℤ) (hc : IsNestedCocycle A n)
    (m l r : S.affineOpens) (h : (l.1 : S.Opens) ≤ (m.1 : S.Opens))
    (hrl : (r.1 : S.Opens) ≤ (l.1 : S.Opens))
    {V : (relativeProj A).scheme.Opens} (hVr : V ≤ GluedTwistAlgebra.cover A r)
    (hVm : V ≤ GluedTwistAlgebra.cover A m) (hVl : V ≤ GluedTwistAlgebra.cover A l)
    (s : (GluedTwistAlgebra.chartModule A n m).obj (op V)) :
    (modelData A n hc).trans m l hVm hVl s
      = (cmpNested A (l.1 : S.Opens) (m.1 : S.Opens) h l.2 m.2 n).app V hVl s := by
  have hpre : GluedTwistAlgebra.cover A l ≤ GluedTwistAlgebra.cover A m :=
    GluedTwistAlgebra.cover_mono A h
  have hRT : GluedTwistAlgebra.cover A r ≤ GluedTwistAlgebra.cover A l :=
    GluedTwistAlgebra.cover_mono A hrl
  have hRU : GluedTwistAlgebra.cover A r ≤ GluedTwistAlgebra.cover A m := hRT.trans hpre
  refine Eq.trans (GluedTwistAlgebra.trans_app_cmpGen A n hc m l r
    (le_inf hRU hRT) hVr hVm hVl s) ?_
  exact symm_app_apply_of_isComposite
    (cmpNested A (l.1 : S.Opens) (m.1 : S.Opens) h l.2 m.2 n)
    (cmpGen A (r.1 : S.Opens) (l.1 : S.Opens) r.2 l.2 n hRT hc)
    (cmpGen A (r.1 : S.Opens) (m.1 : S.Opens) r.2 m.2 n hRU hc) hVr hVl
    (isComposite_cmpNested_cmpGen A n hc (l.1 : S.Opens) (m.1 : S.Opens) (r.1 : S.Opens)
      h l.2 m.2 r.2 hpre hRT hRU V hVr hVl) s

/-- **The chart comparison of the glued twists, as a local isomorphism** over the inverse image of
an affine open of the base: over an open inside that inverse image the sections of the glued twist
are the sections of that chart's own absolute twist, compatibly with the restriction maps. -/
public def chartSectionsLoc (n : ℤ) (hc : IsNestedCocycle A n) (m : S.affineOpens) :
    TopCat.Sheaf.LocalModuleEquiv (gluedTwist A n hc).val
      (GluedTwistAlgebra.chartModule A n m) (GluedTwistAlgebra.cover A m) where
  app _V hV := GluedTwistAlgebra.chartSections A n hc m hV
  naturality hV hWV s := GluedTwistAlgebra.chartSections_resLE A n hc m hV hWV s

/-- The local isomorphism acts by the chart comparison, by definition. -/
public theorem chartSectionsLoc_app (n : ℤ) (hc : IsNestedCocycle A n) (m : S.affineOpens)
    (V : (relativeProj A).scheme.Opens) (hV : V ≤ GluedTwistAlgebra.cover A m)
    (x : (gluedTwist A n hc).val.obj (op V)) :
    (chartSectionsLoc A n hc m).app V hV x = GluedTwistAlgebra.chartSections A n hc m hV x :=
  rfl

/-- **Over an open inside the inverse image of an affine open of the base below the smaller
member, Tag 01NO's nested comparison carries the chart comparison of the larger member to that of
the smaller one.** There the non-nested chart transition of the glued twists is the nested
comparison (`trans_eq_cmpNested_of_le`), and the transition carries one chart comparison to the
other by Stacks 00AL
(`Stacks.AlgebraicGeometry.GluedTwistAlgebra.trans_chartSections`). -/
public theorem cmpNested_chartSections_of_le (n : ℤ) (hc : IsNestedCocycle A n)
    (m l r : S.affineOpens) (h : (l.1 : S.Opens) ≤ (m.1 : S.Opens))
    (hrl : (r.1 : S.Opens) ≤ (l.1 : S.Opens)) (V : (relativeProj A).scheme.Opens)
    (hVl : V ≤ GluedTwistAlgebra.cover A l) (hVm : V ≤ GluedTwistAlgebra.cover A m)
    (hVr : V ≤ GluedTwistAlgebra.cover A r) (x : (gluedTwist A n hc).val.obj (op V)) :
    (cmpNested A (l.1 : S.Opens) (m.1 : S.Opens) h l.2 m.2 n).app V hVl
        (GluedTwistAlgebra.chartSections A n hc m hVm x)
      = GluedTwistAlgebra.chartSections A n hc l hVl x :=
  (trans_eq_cmpNested_of_le A n hc m l r h hrl hVr hVm hVl
      (GluedTwistAlgebra.chartSections A n hc m hVm x)).symm.trans
    (GluedTwistAlgebra.trans_chartSections A n hc m l hVm hVl x)

/-- The same statement read as a composition law for the local isomorphisms. -/
public theorem isComposite_chartSections_of_le (n : ℤ) (hc : IsNestedCocycle A n)
    (m l r : S.affineOpens) (h : (l.1 : S.Opens) ≤ (m.1 : S.Opens))
    (hrl : (r.1 : S.Opens) ≤ (l.1 : S.Opens)) (V : (relativeProj A).scheme.Opens)
    (hVl : V ≤ GluedTwistAlgebra.cover A l) (hVm : V ≤ GluedTwistAlgebra.cover A m)
    (hVr : V ≤ GluedTwistAlgebra.cover A r) :
    IsComposite (chartSectionsLoc A n hc m)
      (cmpNested A (l.1 : S.Opens) (m.1 : S.Opens) h l.2 m.2 n)
      (chartSectionsLoc A n hc l) V hVl hVm := by
  intro x
  refine Eq.trans (congrArg (fun z =>
    (cmpNested A (l.1 : S.Opens) (m.1 : S.Opens) h l.2 m.2 n).app V hVl z)
    (chartSectionsLoc_app A n hc m V hVm x)) ?_
  refine Eq.trans (cmpNested_chartSections_of_le A n hc m l r h hrl V hVl hVm hVr x) ?_
  exact (chartSectionsLoc_app A n hc l V hVl x).symm

/-- **Tag 01NO's nested comparison carries the chart comparison of the glued twists over the
larger affine open of the base to the one over the smaller**, over every open inside the inverse
image of the smaller one. The affine opens of the base below the smaller member cover that
inverse image, and a composition law for local isomorphisms is local. -/
public theorem isComposite_chartSections (n : ℤ) (hc : IsNestedCocycle A n)
    (m l : S.affineOpens) (h : (l.1 : S.Opens) ≤ (m.1 : S.Opens))
    (V : (relativeProj A).scheme.Opens) (hVl : V ≤ GluedTwistAlgebra.cover A l)
    (hVm : V ≤ GluedTwistAlgebra.cover A m) :
    IsComposite (chartSectionsLoc A n hc m)
      (cmpNested A (l.1 : S.Opens) (m.1 : S.Opens) h l.2 m.2 n)
      (chartSectionsLoc A n hc l) V hVl hVm :=
  isComposite_of_cover (isSheaf_pushChart A (l.1 : S.Opens) l.2 n)
    (chartSectionsLoc A n hc m) (cmpNested A (l.1 : S.Opens) (m.1 : S.Opens) h l.2 m.2 n)
    (chartSectionsLoc A n hc l)
    (fun r : {r : S.affineOpens // (r.1 : S.Opens) ≤ (l.1 : S.Opens)} =>
      GluedTwistAlgebra.cover A r.1)
    (fun r V₀ hV₀ hV₁ hV₀r =>
      isComposite_chartSections_of_le A n hc m l r.1 h r.2 V₀ hV₀ hV₁ hV₀r)
    V hVl hVm (hVl.trans (le_iSup_preimage_affine_le A (l.1 : S.Opens)))

/-- The raw form of `isComposite_chartSections`: over an open inside the inverse image of the
smaller affine open of the base, Tag 01NO's nested comparison carries the chart comparison of the
larger affine open to that of the smaller. -/
public theorem cmpNested_chartSections (n : ℤ) (hc : IsNestedCocycle A n) (m l : S.affineOpens)
    (h : (l.1 : S.Opens) ≤ (m.1 : S.Opens)) (V : (relativeProj A).scheme.Opens)
    (hVl : V ≤ GluedTwistAlgebra.cover A l) (hVm : V ≤ GluedTwistAlgebra.cover A m)
    (x : (gluedTwist A n hc).val.obj (op V)) :
    (cmpNested A (l.1 : S.Opens) (m.1 : S.Opens) h l.2 m.2 n).app V hVl
        (GluedTwistAlgebra.chartSections A n hc m hVm x)
      = GluedTwistAlgebra.chartSections A n hc l hVl x := by
  refine Eq.trans (congrArg (fun z =>
    (cmpNested A (l.1 : S.Opens) (m.1 : S.Opens) h l.2 m.2 n).app V hVl z)
    (chartSectionsLoc_app A n hc m V hVm x).symm) ?_
  refine Eq.trans (isComposite_apply (isComposite_chartSections A n hc m l h V hVl hVm) x) ?_
  exact chartSectionsLoc_app A n hc l V hVl x

end TwoCharts

/-! ### The chart comparison as a morphism on the relative Proj -/

section Theta

open Stacks.AlgebraicGeometry.ChartTransRelativeProj

variable (A)

/-- **The transpose of an identification of a restriction, on sections.** The unit of the
restriction--direct-image adjunction is a restriction map, and the direct image of a morphism acts
on the sections over an open as the morphism does over the inverse image. -/
public theorem restrictUnit_comp_map_app {X Y : Scheme.{u}} (a : X ⟶ Y) [IsOpenImmersion a]
    (M : Y.Modules) (K : X.Modules) (E : (Scheme.Modules.restrictFunctor a).obj M ≅ K)
    (V : Y.Opens) (s : M.val.obj (op V)) :
    ((Scheme.Modules.restrictAdjunction a).unit.app M ≫
          (Scheme.Modules.pushforward a).map E.hom).val.app (op V) s
      = E.hom.val.app (op (a ⁻¹ᵁ V))
          (M.val.map (homOfLE (a.image_preimage_le V)).op s) :=
  rfl

/-- The components of a composite of morphisms of sheaves of modules, on a section. -/
public theorem comp_val_app_apply {X : Scheme.{u}} {M N P : X.Modules} (φ : M ⟶ N) (ψ : N ⟶ P)
    (V : X.Opens) (s : M.val.obj (op V)) :
    (φ ≫ ψ).val.app (op V) s = ψ.val.app (op V) (φ.val.app (op V) s) :=
  rfl

/-- The identification of the direct image of a direct image with the direct image along the
composite, followed by the congruence isomorphism, written out. -/
public theorem pushforwardCompCongr_eq {X P Q : Scheme.{u}} (a : P ⟶ Q) (c : Q ⟶ X)
    {cP : P ⟶ X} (hac : a ≫ c = cP) (K : P.Modules) :
    PushforwardCocycle.pushforwardCompCongr a c hac K =
      (Scheme.Modules.pushforwardComp a c).hom.app K ≫
        (Scheme.Modules.pushforwardCongr hac).hom.app K :=
  rfl

/-- **The identification collapses to the congruence isomorphism**: the pseudofunctoriality
factor of the direct image is the identity, both of its sides being the same object. -/
public theorem pushforwardCompCongr_eq_pushforwardCongr {X P Q : Scheme.{u}} (a : P ⟶ Q)
    (c : Q ⟶ X) {cP : P ⟶ X} (hac : a ≫ c = cP) (K : P.Modules) :
    PushforwardCocycle.pushforwardCompCongr a c hac K =
      (Scheme.Modules.pushforwardCongr hac).hom.app K := by
  refine Eq.trans (pushforwardCompCongr_eq a c hac K) ?_
  refine Eq.trans (CategoryTheory.eq_whisker
    (PushforwardCocycle.pushforwardComp_hom_app_eq_id a c K) _) ?_
  exact Category.id_comp _

/-- **Stacks 00AL's comparison map for the glued twists, at the `n`-th relative twist of Tag
01NR.** Over an open of the relative projective spectrum inside the inverse image of an affine
open `U` of the base, a section of the `n`-th relative twist is a section of the absolute `n`-th
twist on `Proj Γ(U, A)` over the inverse image of that open along the chart.

This is `Stacks.AlgebraicGeometry.GluedTwistAlgebra.chartSections` at the pieces of Tag 01NR's
twist datum. The identification of those pieces with Tag 01NO's glued twists is a chain of delta
steps through the structure literals the twist datum is assembled from, and is taken **here**, in
a definition with nothing else in it; everything below is stated in this vocabulary, so the chain
is never traversed again. -/
public def toGluedSection (n : ℤ) {V : (relativeProj A).scheme.Opens}
    (x : (relativeTwist A n).val.obj (op V)) :
    (gluedTwist A n (ProjTwistCocycle.isNestedCocycle A n)).val.obj (op V) :=
  x

/-- **Stacks 00AL's comparison map for the glued twists, at the `n`-th relative twist.** -/
public def relativeChartSections (n : ℤ) (m : S.affineOpens)
    {V : (relativeProj A).scheme.Opens} (hV : V ≤ GluedTwistAlgebra.cover A m)
    (x : (relativeTwist A n).val.obj (op V)) :
    (GluedTwistAlgebra.chartModule A n m).obj (op V) :=
  GluedTwistAlgebra.chartSections A n (ProjTwistCocycle.isNestedCocycle A n) m hV
    (toGluedSection A n x)

/-- The comparison map at the relative twist is Stacks 00AL's comparison map of the glued twist,
by definition. -/
public theorem relativeChartSections_eq (n : ℤ) (m : S.affineOpens)
    {V : (relativeProj A).scheme.Opens} (hV : V ≤ GluedTwistAlgebra.cover A m)
    (x : (relativeTwist A n).val.obj (op V)) :
    relativeChartSections A n m hV x
      = GluedTwistAlgebra.chartSections A n (ProjTwistCocycle.isNestedCocycle A n) m hV
          (toGluedSection A n x) :=
  rfl

/-- **The chart comparison of the glued twists, as a morphism of sheaves of modules on the
relative projective spectrum.** This is the adjoint transpose of the chart identification of Tag
01NR: a morphism from the `n`-th relative twist to the direct image along the chart over an affine
open `U` of the base of the absolute `n`-th twist on `Proj Γ(U, A)`. -/
public def chartTheta (n : ℤ) (U : AffineOpen S) :
    relativeTwist A n ⟶
      (Scheme.Modules.pushforward ((relativeProj A).chart U.1 U.2)).obj
        (twistingSheaf (A.grading U.1) n) :=
  PushforwardCocycle.transpose ((relativeProj A).chart U.1 U.2) (relativeTwist A n)
    (chartTwistIso A n U).hom

/-- **The chart comparison is the restriction unit followed by the direct image of the chart
identification**, with no trace of the inverse image left. -/
public theorem chartTheta_eq (n : ℤ) (U : AffineOpen S) :
    chartTheta A n U =
      (Scheme.Modules.restrictAdjunction ((relativeProj A).chart U.1 U.2)).unit.app
          (relativeTwist A n) ≫
        (Scheme.Modules.pushforward ((relativeProj A).chart U.1 U.2)).map
          ((GluedTwistAlgebra.twistDataOfGradedAlgebra A).chartData.chartIso U.1 U.2 n).hom :=
  transpose_restrictIso ((relativeProj A).chart U.1 U.2) (relativeTwist A n)
    (twistingSheaf (A.grading U.1) n)
    ((GluedTwistAlgebra.twistDataOfGradedAlgebra A).chartData.chartIso U.1 U.2 n)

/-- **Tag 01NR's chart identification on the sections over an open of the chart**: the chart
comparison of the glued twists at the image open, carried back along
`chart ⁻¹ᵁ (chart ''ᵁ W) = W`. -/
public theorem chartData_chartIso_hom_app (n : ℤ) (m : S.affineOpens)
    (W : (AlgebraicGeometry.Proj (A.grading (m.1 : S.Opens))).Opens)
    (hW : (relativeProj A).chart (m.1 : S.Opens) m.2 ''ᵁ W ≤ GluedTwistAlgebra.cover A m)
    (x : (Scheme.Modules.restrict (relativeTwist A n)
      ((relativeProj A).chart (m.1 : S.Opens) m.2)).val.obj (op W)) :
    ((GluedTwistAlgebra.twistDataOfGradedAlgebra A).chartData.chartIso
          (m.1 : S.Opens) m.2 n).hom.val.app (op W) x
      = (twistingSheaf (A.grading (m.1 : S.Opens)) n).val.restrictₛₗ
          (eqToHom (((relativeProj A).chart (m.1 : S.Opens) m.2).preimage_image_eq W).symm).op
          (GluedTwistAlgebra.chartSections A n
            (ProjTwistCocycle.isNestedCocycle A n) m hW x) :=
  rfl

/-- **The chart comparison morphism acts on the sections over an open inside the inverse image of
the affine open by Stacks 00AL's comparison map.** The unit factor restricts to the image of the
preimage, which is the open itself there, and the two transports along that equality of opens
cancel. -/
public theorem chartTheta_app (n : ℤ) (m : S.affineOpens)
    {V : (relativeProj A).scheme.Opens} (hV : V ≤ GluedTwistAlgebra.cover A m)
    (s : (relativeTwist A n).val.obj (op V)) :
    (chartTheta A n m).val.app (op V) s = relativeChartSections A n m hV s := by
  have hWV : (relativeProj A).chart (m.1 : S.Opens) m.2 ''ᵁ
      ((relativeProj A).chart (m.1 : S.Opens) m.2 ⁻¹ᵁ V) ≤ V :=
    ((relativeProj A).chart (m.1 : S.Opens) m.2).image_preimage_le V
  refine Eq.trans (congrArg (fun φ : relativeTwist A n ⟶
      (Scheme.Modules.pushforward ((relativeProj A).chart (m.1 : S.Opens) m.2)).obj
        (twistingSheaf (A.grading (m.1 : S.Opens)) n) => φ.val.app (op V) s)
    (chartTheta_eq A n m)) ?_
  refine Eq.trans (restrictUnit_comp_map_app ((relativeProj A).chart (m.1 : S.Opens) m.2)
    (relativeTwist A n) (twistingSheaf (A.grading (m.1 : S.Opens)) n)
    ((GluedTwistAlgebra.twistDataOfGradedAlgebra A).chartData.chartIso
      (m.1 : S.Opens) m.2 n) V s) ?_
  refine Eq.trans (chartData_chartIso_hom_app A n m
    ((relativeProj A).chart (m.1 : S.Opens) m.2 ⁻¹ᵁ V) (hWV.trans hV) _) ?_
  refine Eq.trans (congrArg (fun z =>
    (twistingSheaf (A.grading (m.1 : S.Opens)) n).val.restrictₛₗ
      (eqToHom (((relativeProj A).chart (m.1 : S.Opens) m.2).preimage_image_eq
        ((relativeProj A).chart (m.1 : S.Opens) m.2 ⁻¹ᵁ V)).symm).op z)
    (GluedTwistAlgebra.chartSections_resLE A n (ProjTwistCocycle.isNestedCocycle A n) m hV hWV
      s)) ?_
  exact PresheafOfModules.map_map_eq_self
    (twistingSheaf (A.grading (m.1 : S.Opens)) n).val _ _
    (GluedTwistAlgebra.chartSections A n (ProjTwistCocycle.isNestedCocycle A n) m hV s)


/-! ### Tag 01NO's comparison between the two chart identifications -/

/-- Tag 01NO's twist comparison of Tag 01NO, pushed forward to the relative projective spectrum,
is the generic pushed-forward comparison of
`Stacks.AlgebraicGeometry.PushforwardCocycle.pushComparison` at the chart transition. -/
public theorem pushNested_eq_pushComparison (T U : S.Opens) (h : T ≤ U) (hT : IsAffineOpen T)
    (hU : IsAffineOpen U) (n : ℤ) :
    pushNested A T U h hT hU n =
      PushforwardCocycle.pushComparison (projInclusionMap A T U h hT hU)
        ((relativeProj A).chart U hU) ((relativeProj A).chart_transition T U h hT hU)
        (twistingSheaf (A.grading U) n) (twistingSheaf (A.grading T) n)
        (ProjInclusionTwist.projInclusionTwistIso A T U h hT hU n) :=
  rfl

/-- **Tag 01NO's pushed-forward twist comparison is the direct image of the transpose of Tag
01NO's twist isomorphism**, followed by the congruence isomorphism for the chart transition. The
pseudofunctoriality factor of the direct image is the identity, by
`Stacks.AlgebraicGeometry.PushforwardCocycle.pushforwardComp_hom_app_eq_id`. -/
public theorem pushNested_eq (T U : S.Opens) (h : T ≤ U) (hT : IsAffineOpen T)
    (hU : IsAffineOpen U) (n : ℤ) :
    pushNested A T U h hT hU n =
      (Scheme.Modules.pushforward ((relativeProj A).chart U hU)).map
          (PushforwardCocycle.transpose (projInclusionMap A T U h hT hU)
            (twistingSheaf (A.grading U) n)
            (ProjInclusionTwist.projInclusionTwistIso A T U h hT hU n).hom) ≫
        (Scheme.Modules.pushforwardCongr
            ((relativeProj A).chart_transition T U h hT hU)).hom.app
          (twistingSheaf (A.grading T) n) := by
  refine Eq.trans (pushNested_eq_pushComparison A T U h hT hU n) ?_
  refine Eq.trans (PushforwardCocycle.pushComparison_eq_transpose
    (projInclusionMap A T U h hT hU) ((relativeProj A).chart U hU)
    ((relativeProj A).chart_transition T U h hT hU) (twistingSheaf (A.grading U) n)
    (twistingSheaf (A.grading T) n)
    (ProjInclusionTwist.projInclusionTwistIso A T U h hT hU n)) ?_
  exact CategoryTheory.whisker_eq _
    (pushforwardCompCongr_eq_pushforwardCongr (projInclusionMap A T U h hT hU)
      ((relativeProj A).chart U hU) ((relativeProj A).chart_transition T U h hT hU)
      (twistingSheaf (A.grading T) n))

/-- `cmpNested_chartSections` at the `n`-th relative twist of Tag 01NR, whose glued pieces are
Tag 01NO's glued twists for the nested cocycle of `Stacks.AlgebraicGeometry.ProjTwistCocycle`.
The identification of the two is a chain of delta steps through the structure literals of the
twist datum and is taken here, in a statement with nothing else in it. -/
public theorem cmpNested_relativeChartSections (n : ℤ) (m l : S.affineOpens)
    (h : (l.1 : S.Opens) ≤ (m.1 : S.Opens)) (V : (relativeProj A).scheme.Opens)
    (hVl : V ≤ GluedTwistAlgebra.cover A l) (hVm : V ≤ GluedTwistAlgebra.cover A m)
    (x : (relativeTwist A n).val.obj (op V)) :
    (cmpNested A (l.1 : S.Opens) (m.1 : S.Opens) h l.2 m.2 n).app V hVl
        (relativeChartSections A n m hVm x)
      = relativeChartSections A n l hVl x := by
  refine Eq.trans (congrArg
    (fun z => (cmpNested A (l.1 : S.Opens) (m.1 : S.Opens) h l.2 m.2 n).app V hVl z)
    (relativeChartSections_eq A n m hVm x)) ?_
  refine Eq.trans (cmpNested_chartSections A n (ProjTwistCocycle.isNestedCocycle A n) m l h V
    hVl hVm (toGluedSection A n x)) ?_
  exact (relativeChartSections_eq A n l hVl x).symm

/-- **Tag 01NO's pushed-forward twist comparison carries the chart comparison of the glued twists
over the larger affine open of the base to the one over the smaller**, on the sections over an
open inside the inverse image of the smaller one. This is
`Stacks.AlgebraicGeometry.Tag07ZGTwist.cmpNested_chartSections_relativeTwist` with the local
isomorphism traded for the morphism it is built from, by
`Stacks.AlgebraicGeometry.ChartTransRelativeProj.cmpNested_app`. -/
public theorem pushNested_relativeChartSections (n : ℤ) (T U : S.affineOpens)
    (h : (T.1 : S.Opens) ≤ (U.1 : S.Opens)) (V : (relativeProj A).scheme.Opens)
    (hVT : V ≤ GluedTwistAlgebra.cover A T) (hVU : V ≤ GluedTwistAlgebra.cover A U)
    (x : (relativeTwist A n).val.obj (op V)) :
    (pushNested A (T.1 : S.Opens) (U.1 : S.Opens) h T.2 U.2 n).val.app (op V)
        (relativeChartSections A n U hVU x)
      = relativeChartSections A n T hVT x := by
  refine Eq.trans (cmpNested_app A (T.1 : S.Opens) (U.1 : S.Opens) h T.2 U.2 n V hVT
    (relativeChartSections A n U hVU x)).symm ?_
  exact cmpNested_relativeChartSections A n U T h V hVT hVU x

/-- The inverse image along a chart of the inverse image of that chart's affine open of the base
is everything: the chart's image is that inverse image. -/
public theorem chart_preimage_toBase_preimage (U : S.Opens) (hU : IsAffineOpen U) :
    (relativeProj A).chart U hU ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ U) = ⊤ := by
  rw [← RelativeProjTwistGlue.chart_image_top (relativeProj A) U hU]
  exact ((relativeProj A).chart U hU).preimage_image_eq ⊤

/-- **The chart comparison over the smaller affine open of the base is the chart comparison over
the larger one followed by Tag 01NO's pushed-forward twist comparison.** Checked on the sections
over the opens inside the inverse image of the smaller affine open, which determine a morphism
into the direct image along its chart, since there the inverse image along the chart does not
shrink. -/
public theorem chartTheta_comp_pushNested (n : ℤ) (T U : S.affineOpens)
    (h : (T.1 : S.Opens) ≤ (U.1 : S.Opens)) :
    chartTheta A n U ≫ pushNested A (T.1 : S.Opens) (U.1 : S.Opens) h T.2 U.2 n
      = chartTheta A n T := by
  have hpre : GluedTwistAlgebra.cover A T ≤ GluedTwistAlgebra.cover A U :=
    (relativeProj A).toBase.preimage_mono h
  refine hom_ext_of_resLE_injective
    (W₀ := GluedTwistAlgebra.cover A T)
    (fun V => injective_pushforward_resLE ((relativeProj A).chart (T.1 : S.Opens) T.2)
      (twistingSheaf (A.grading (T.1 : S.Opens)) n) inf_le_left ?_) ?_
  · rw [Scheme.Hom.preimage_inf, chart_preimage_toBase_preimage A (T.1 : S.Opens) T.2,
      inf_top_eq]
  · intro V hVT s
    refine Eq.trans ?_ (chartTheta_app A n T hVT s).symm
    refine Eq.trans (comp_val_app_apply (chartTheta A n U)
      (pushNested A (T.1 : S.Opens) (U.1 : S.Opens) h T.2 U.2 n) V s) ?_
    refine Eq.trans (congrArg (fun z =>
      (pushNested A (T.1 : S.Opens) (U.1 : S.Opens) h T.2 U.2 n).val.app (op V) z)
      (chartTheta_app A n U (hVT.trans hpre) s)) ?_
    exact pushNested_relativeChartSections A n T U h V hVT (hVT.trans hpre) s

/-- **The chart identification of Tag 01NR over the smaller of a nested pair of affine opens of
the base is the one over the larger, pulled back along the chart transition and followed by Tag
01NO's twist comparison.**

This is the two-chart compatibility of Tag 01NR's chart identifications. It is proved by
transposing: the adjoint transpose of the composite on the left is, by
`Stacks.AlgebraicGeometry.PushforwardCocycle.transpose_cocycle`, the chart comparison over the
larger affine open followed by Tag 01NO's pushed-forward comparison, and that composite is the
chart comparison over the smaller one by
`Stacks.AlgebraicGeometry.Tag07ZGTwist.chartTheta_comp_pushNested`. The transpose is a bijection,
so the identity of the transposes is the identity of the two morphisms out of the inverse
image. -/
public theorem chartTwistIso_hom_eq (n : ℤ) (T U : S.affineOpens)
    (h : (T.1 : S.Opens) ≤ (U.1 : S.Opens)) :
    (Scheme.Modules.pullbackCongr
            ((relativeProj A).chart_transition (T.1 : S.Opens) (U.1 : S.Opens) h T.2
              U.2)).inv.app (relativeTwist A n) ≫
        (Scheme.Modules.pullbackComp
            (projInclusionMap A (T.1 : S.Opens) (U.1 : S.Opens) h T.2 U.2)
            ((relativeProj A).chart (U.1 : S.Opens) U.2)).inv.app (relativeTwist A n) ≫
        (Scheme.Modules.pullback
            (projInclusionMap A (T.1 : S.Opens) (U.1 : S.Opens) h T.2 U.2)).map
            (chartTwistIso A n U).hom ≫
        (ProjInclusionTwist.projInclusionTwistIso A (T.1 : S.Opens) (U.1 : S.Opens) h T.2 U.2
            n).hom =
      (chartTwistIso A n T).hom := by
  refine transpose_injective ((relativeProj A).chart (T.1 : S.Opens) T.2)
    (relativeTwist A n) ?_
  refine Eq.trans (PushforwardCocycle.transpose_cocycle
    (projInclusionMap A (T.1 : S.Opens) (U.1 : S.Opens) h T.2 U.2)
    ((relativeProj A).chart (U.1 : S.Opens) U.2)
    ((relativeProj A).chart (T.1 : S.Opens) T.2)
    ((relativeProj A).chart_transition (T.1 : S.Opens) (U.1 : S.Opens) h T.2 U.2)
    (relativeTwist A n) (twistingSheaf (A.grading (U.1 : S.Opens)) n)
    (twistingSheaf (A.grading (T.1 : S.Opens)) n) (chartTwistIso A n U).hom
    (ProjInclusionTwist.projInclusionTwistIso A (T.1 : S.Opens) (U.1 : S.Opens) h T.2 U.2
      n).hom _ rfl).symm ?_
  refine Eq.trans ?_ (chartTheta_comp_pushNested A n T U h)
  exact CategoryTheory.whisker_eq _
    (pushNested_eq A (T.1 : S.Opens) (U.1 : S.Opens) h T.2 U.2 n).symm

end Theta

/-! ### The congruence isomorphisms of the inverse image, composed -/

section CongrCalculus

attribute [local implicit_reducible] AlgebraicGeometry.Proj

variable {X Y : Scheme.{u}}

/-- The congruence isomorphism of the inverse image at a reflexive equality is the identity. By
proof irrelevance the equality has no other proof, so a rewrite with this equation still fires at
an occurrence whose proof term is some other expression of type `f = f`. -/
public alias pullbackCongr_refl_eq := Stacks.AlgebraicGeometry.ModuleHomGlue.pullbackCongr_rfl

/-- Undoing one congruence isomorphism and applying another is the congruence isomorphism between
their sources. The composite equation is an argument rather than the term `a.trans b.symm`, so
that the rewrite has no proof term to unify. -/
@[reassoc]
public theorem pullbackCongr_inv_comp_hom {f g k : X ⟶ Y} (a : f = k) (b : g = k) (c : f = g)
    (M : Y.Modules) :
    (Scheme.Modules.pullbackCongr a).inv.app M ≫ (Scheme.Modules.pullbackCongr c).hom.app M =
      (Scheme.Modules.pullbackCongr b).inv.app M := by
  subst a b
  simp [pullbackCongr_refl_eq]

/-- Applying one congruence isomorphism and undoing another is the congruence isomorphism between
their sources. -/
@[reassoc]
public theorem pullbackCongr_hom_comp_inv {f g k : X ⟶ Y} (a : f = k) (b : g = k) (c : f = g)
    (M : Y.Modules) :
    (Scheme.Modules.pullbackCongr a).hom.app M ≫ (Scheme.Modules.pullbackCongr b).inv.app M =
      (Scheme.Modules.pullbackCongr c).hom.app M := by
  subst a b
  simp [pullbackCongr_refl_eq]

/-- The same cancellation read from the other end. -/
@[reassoc]
public theorem pullbackCongr_inv_comp_hom' {f g k : X ⟶ Y} (a : f = k) (b : g = k) (c : f = g)
    (M : Y.Modules) :
    (Scheme.Modules.pullbackCongr c).inv.app M ≫ (Scheme.Modules.pullbackCongr a).hom.app M =
      (Scheme.Modules.pullbackCongr b).hom.app M := by
  subst a b
  simp [pullbackCongr_refl_eq]

end CongrCalculus

/-! ### Reassociations -/

section CatGeneral

variable {C : Type*} [Category C]

/-- `(a ≫ b ≫ c) ≫ g = a ≫ b ≫ c ≫ g`, at the level of variables. -/
public theorem comp₃_comp {X₀ X₁ X₂ X₃ X₄ : C} (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂) (c : X₂ ⟶ X₃)
    (g : X₃ ⟶ X₄) : (a ≫ b ≫ c) ≫ g = a ≫ b ≫ c ≫ g := by
  simp only [Category.assoc]

/-- A functor applied to a three-fold composite, at the level of variables. This is
`CategoryTheory.Functor.map_comp` twice over, stated separately because at the concrete inverse
images below neither a rewrite nor a simp call can build the motive, the sheaves of modules in the
components not being spelled at the type the functor expects. -/
public theorem map_comp₃ {D : Type*} [Category D] (F : C ⥤ D) {X₀ X₁ X₂ X₃ : C} (f : X₀ ⟶ X₁)
    (g : X₁ ⟶ X₂) (k : X₂ ⟶ X₃) : F.map (f ≫ g ≫ k) = F.map f ≫ F.map g ≫ F.map k := by
  rw [F.map_comp, F.map_comp]

/-- Congruence in the third factor of a three-fold composite. -/
public theorem comp_comp_congr {X₀ X₁ X₂ X₃ : C} (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂) {f g : X₂ ⟶ X₃}
    (hfg : f = g) : a ≫ b ≫ f = a ≫ b ≫ g :=
  congrArg (fun z => a ≫ b ≫ z) hfg

end CatGeneral

/-! ### Pseudofunctoriality of the inverse image, in composable form -/

section Pseudo

variable {W X Y Z : Scheme.{u}}

/-- **The associativity coherence of the inverse image, read at a sheaf of modules.** This is
`AlgebraicGeometry.Scheme.Modules.pseudofunctor_associativity` with the whiskerings and the
associator evaluated at `M`, where the whiskerings become functor images and the associator
becomes an identity. -/
public theorem pseudofunctor_associativity_app (k : W ⟶ X) (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Z.Modules) :
    (Scheme.Modules.pullbackComp k (f ≫ g)).inv.app M ≫
        (Scheme.Modules.pullback k).map ((Scheme.Modules.pullbackComp f g).inv.app M) ≫
        (Scheme.Modules.pullbackComp k f).hom.app ((Scheme.Modules.pullback g).obj M) ≫
        (Scheme.Modules.pullbackComp (k ≫ f) g).hom.app M =
      (Scheme.Modules.pullbackCongr (Category.assoc k f g)).inv.app M :=
  congrArg (fun τ => τ.app M) (Scheme.Modules.pseudofunctor_associativity k f g)

/-- **Undoing the identification of the inverse image along a triple composite, one factor at a
time.** Undoing the identification along `k ≫ (f ≫ g)` and then, inside the inverse image along
`k`, the one along `f ≫ g`, is the same as undoing the identification along `(k ≫ f) ≫ g` and
then the one along `k ≫ f`, up to the congruence isomorphism of the reassociation. -/
@[reassoc]
public theorem pullbackComp_inv_app_comp_map (k : W ⟶ X) (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Z.Modules) :
    (Scheme.Modules.pullbackComp k (f ≫ g)).inv.app M ≫
        (Scheme.Modules.pullback k).map ((Scheme.Modules.pullbackComp f g).inv.app M) =
      (Scheme.Modules.pullbackCongr (Category.assoc k f g)).inv.app M ≫
        (Scheme.Modules.pullbackComp (k ≫ f) g).inv.app M ≫
        (Scheme.Modules.pullbackComp k f).inv.app ((Scheme.Modules.pullback g).obj M) := by
  rw [← pseudofunctor_associativity_app k f g M]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app, Functor.comp_obj,
    Category.comp_id]

/-- The same coherence read in the other direction: applying the identification along `f ≫ g`
inside the inverse image along `k` and then the one along `k ≫ (f ≫ g)` is, after undoing the
identification along `k ≫ f`, the identification along `(k ≫ f) ≫ g` followed by the congruence
isomorphism of the reassociation. -/
@[reassoc]
public theorem pullbackComp_hom_app_comp_map (k : W ⟶ X) (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Z.Modules) :
    (Scheme.Modules.pullbackComp k f).inv.app ((Scheme.Modules.pullback g).obj M) ≫
        (Scheme.Modules.pullback k).map ((Scheme.Modules.pullbackComp f g).hom.app M) ≫
        (Scheme.Modules.pullbackComp k (f ≫ g)).hom.app M =
      (Scheme.Modules.pullbackComp (k ≫ f) g).hom.app M ≫
        (Scheme.Modules.pullbackCongr (Category.assoc k f g)).hom.app M := by
  have h : ((Scheme.Modules.pullback k).mapIso ((Scheme.Modules.pullbackComp f g).app M) ≪≫
        (Scheme.Modules.pullbackComp k (f ≫ g)).app M).hom =
      ((Scheme.Modules.pullbackComp k f).app ((Scheme.Modules.pullback g).obj M) ≪≫
        (Scheme.Modules.pullbackComp (k ≫ f) g).app M ≪≫
        (Scheme.Modules.pullbackCongr (Category.assoc k f g)).app M).hom := by
    refine (Iso.inv_eq_inv _ _).mp ?_
    simpa only [Iso.trans_inv, Iso.app_inv, Functor.mapIso_inv, Category.assoc] using
      pullbackComp_inv_app_comp_map k f g M
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom] at h
  rw [h, Iso.inv_hom_id_app_assoc]

/-- **The left unitality coherence of the inverse image, read at a sheaf of modules.** This is
`AlgebraicGeometry.Scheme.Modules.pseudofunctor_left_unitality` with the whiskering and the left
unitor evaluated at `M`. -/
public theorem pseudofunctor_left_unitality_app (f : X ⟶ Y) (M : Y.Modules) :
    (Scheme.Modules.pullbackComp f (𝟙 Y)).inv.app M ≫
        (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackId Y).hom.app M) =
      (Scheme.Modules.pullbackCongr (Category.comp_id f)).hom.app M :=
  congrArg (fun τ => τ.app M) (Scheme.Modules.pseudofunctor_left_unitality f)

/-- **The identification of the inverse image along the identity, carried inside an inverse
image.** It is the identification of the inverse image along `f ≫ 𝟙` followed by the congruence
isomorphism of the unit law. -/
@[reassoc]
public theorem pullback_map_pullbackId_hom_app (f : X ⟶ Y) (M : Y.Modules) :
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackId Y).hom.app M) =
      (Scheme.Modules.pullbackComp f (𝟙 Y)).hom.app M ≫
        (Scheme.Modules.pullbackCongr (Category.comp_id f)).hom.app M := by
  rw [← pseudofunctor_left_unitality_app f M, Iso.hom_inv_id_app_assoc]

/-- **Naturality of the pseudofunctoriality identification of the inverse image in the sheaf of
modules.** -/
@[reassoc]
public theorem pullbackComp_inv_app_comp_pullback_map (k : W ⟶ X) (f : X ⟶ Y) {M N : Y.Modules}
    (t : M ⟶ N) :
    (Scheme.Modules.pullbackComp k f).inv.app M ≫
        (Scheme.Modules.pullback k).map ((Scheme.Modules.pullback f).map t) =
      (Scheme.Modules.pullback (k ≫ f)).map t ≫
        (Scheme.Modules.pullbackComp k f).inv.app N :=
  ((Scheme.Modules.pullbackComp k f).inv.naturality t).symm

/-- **The five factors transporting a morphism between two inverse images to a pair of legs are
pseudo-natural in the leg.** A morphism `t` between the inverse images of `M` along `a` and of `N`
along `b` is transported to the inverse images along a pair of composites `q ≫ a` and `q ≫ b`,
named by two equations, by five factors; precomposing the presenting morphism `q` with a further
morphism `w` gives the inverse image along `w` of that transport, conjugated by the
pseudofunctoriality identifications for `w`.

The content is the associativity coherence of the inverse image, read at `M` and at `N`, and the
naturality of the pseudofunctoriality identification for `w` and `q`; the congruence isomorphisms
of the two legs contribute nothing, both of their equations becoming the reassociation. -/
public theorem pullback_five_comp_leg {W' V : Scheme.{u}} (w : W' ⟶ W) (q : W ⟶ V)
    (a : V ⟶ X) (b : V ⟶ Y) {M : X.Modules} {N : Y.Modules}
    (t : (Scheme.Modules.pullback a).obj M ⟶ (Scheme.Modules.pullback b).obj N)
    {d : W ⟶ X} (hd : q ≫ a = d) {i : W ⟶ Y} (hi : q ≫ b = i)
    {d' : W' ⟶ X} (hd' : (w ≫ q) ≫ a = d') (hwd : w ≫ d = d')
    {i' : W' ⟶ Y} (hi' : (w ≫ q) ≫ b = i') (hwi : w ≫ i = i') :
    (Scheme.Modules.pullbackCongr hd').inv.app M ≫
        (Scheme.Modules.pullbackComp (w ≫ q) a).inv.app M ≫
        (Scheme.Modules.pullback (w ≫ q)).map t ≫
        (Scheme.Modules.pullbackComp (w ≫ q) b).hom.app N ≫
        (Scheme.Modules.pullbackCongr hi').hom.app N =
      (Scheme.Modules.pullbackCongr hwd).inv.app M ≫
        (Scheme.Modules.pullbackComp w d).inv.app M ≫
        (Scheme.Modules.pullback w).map
          ((Scheme.Modules.pullbackCongr hd).inv.app M ≫
            (Scheme.Modules.pullbackComp q a).inv.app M ≫
            (Scheme.Modules.pullback q).map t ≫
            (Scheme.Modules.pullbackComp q b).hom.app N ≫
            (Scheme.Modules.pullbackCongr hi).hom.app N) ≫
        (Scheme.Modules.pullbackComp w i).hom.app N ≫
        (Scheme.Modules.pullbackCongr hwi).hom.app N := by
  subst hd
  subst hi
  subst hwd
  subst hwi
  obtain rfl : hd' = Category.assoc w q a := Subsingleton.elim _ _
  obtain rfl : hi' = Category.assoc w q b := Subsingleton.elim _ _
  simp only [pullbackCongr_refl_eq, Iso.refl_inv, Iso.refl_hom, NatTrans.id_app,
    Category.id_comp, Category.comp_id, Functor.map_comp, Category.assoc]
  rw [pullbackComp_inv_app_comp_map_assoc, pullbackComp_inv_app_comp_pullback_map_assoc,
    pullbackComp_hom_app_comp_map]

/-- **The three factors transporting a morphism out of an inverse image to a given leg are
pseudo-natural in the leg.** The companion of
`Stacks.AlgebraicGeometry.Tag07ZGTwist.pullback_five_comp_leg` for a morphism whose target is a
sheaf of modules on the scheme the leg maps to, rather than an inverse image along a second
morphism; the second leg is then the presenting morphism itself and only three factors are
needed. -/
@[reassoc]
public theorem pullback_three_comp_leg {W' V : Scheme.{u}} (w : W' ⟶ W) (q : W ⟶ V)
    (a : V ⟶ X) {M : X.Modules} {N : V.Modules}
    (t : (Scheme.Modules.pullback a).obj M ⟶ N)
    {c : W ⟶ X} (hc : q ≫ a = c)
    {c' : W' ⟶ X} (hc' : (w ≫ q) ≫ a = c') (hwc : w ≫ c = c') :
    (Scheme.Modules.pullbackCongr hc').inv.app M ≫
        (Scheme.Modules.pullbackComp (w ≫ q) a).inv.app M ≫
        (Scheme.Modules.pullback (w ≫ q)).map t =
      (Scheme.Modules.pullbackCongr hwc).inv.app M ≫
        (Scheme.Modules.pullbackComp w c).inv.app M ≫
        (Scheme.Modules.pullback w).map
          ((Scheme.Modules.pullbackCongr hc).inv.app M ≫
            (Scheme.Modules.pullbackComp q a).inv.app M ≫
            (Scheme.Modules.pullback q).map t) ≫
        (Scheme.Modules.pullbackComp w q).hom.app N := by
  subst hc
  subst hwc
  obtain rfl : hc' = Category.assoc w q a := Subsingleton.elim _ _
  simp only [pullbackCongr_refl_eq, Iso.refl_inv, NatTrans.id_app, Category.id_comp,
    Functor.map_comp, Category.assoc]
  rw [pullbackComp_inv_app_comp_map_assoc, pullbackComp_inv_app_comp_pullback_map_assoc,
    Iso.inv_hom_id_app, Category.comp_id]

end Pseudo

/-! ### The nested compatibility of a transport at legs -/

section NestedLegs

variable {V₁ V₂ Xs MD : Scheme.{u}}

/-- **Transport of the three-factor transport along an equality of legs.** -/
@[reassoc]
public theorem pullback_three_leg_congr (a : V₂ ⟶ Xs) {M : Xs.Modules} {N : V₂.Modules}
    (χ : (Scheme.Modules.pullback a).obj M ⟶ N) {Z : Scheme.{u}} {d₁ d₂ : Z ⟶ V₂}
    (he : d₁ = d₂) {c : Z ⟶ Xs} (hc₁ : d₁ ≫ a = c) (hc₂ : d₂ ≫ a = c) :
    (Scheme.Modules.pullbackCongr hc₁).inv.app M ≫
        (Scheme.Modules.pullbackComp d₁ a).inv.app M ≫
        (Scheme.Modules.pullback d₁).map χ =
      ((Scheme.Modules.pullbackCongr hc₂).inv.app M ≫
          (Scheme.Modules.pullbackComp d₂ a).inv.app M ≫
          (Scheme.Modules.pullback d₂).map χ) ≫
        (Scheme.Modules.pullbackCongr he).inv.app N := by
  subst he
  obtain rfl : hc₁ = hc₂ := Subsingleton.elim _ _
  rw [pullbackCongr_refl_eq]
  exact (Category.comp_id _).symm

/-- **The nested compatibility of a morphism out of an inverse image, transported to arbitrary
legs.** At the level of variables: `aT` and `aU` are two morphisms into one scheme, `pim` is a
morphism making them agree, `mh` and `ιm` are the two morphisms out of a fourth scheme along which
`tw` compares the inverse images of `N₂` and `N₁`, and `ts` is a section of `ιm` lifting `pim`
through `mh`. The hypothesis `hbase` is the compatibility of `χ₁` with `χ₂` and `tw` at those
canonical legs; the conclusion is the same compatibility read at an arbitrary pair of legs `d'`
and `d` joined by a morphism `k`, with `p` presenting them.

The two transports of `tw` are **arguments** `twAt` and `twAtP` pinned by their defining
equations, rather than written out in the statement: their consumer names them by a definition
whose unfolding at a concrete pair of affine opens of the base is not available to the kernel, and
passing the definition's own defining equation is what keeps the instance affordable.

Every ingredient of the proof is a coherence of the inverse-image pseudofunctor:
`Stacks.AlgebraicGeometry.Tag07ZGTwist.pullback_three_comp_leg` and `pullback_five_comp_leg` for
the pseudo-naturality of the two transports in their legs, and
`pullback_map_pullbackId_hom_app` for the unit law. -/
public theorem three_comp_leg_nested
    (aT : V₁ ⟶ Xs) (aU : V₂ ⟶ Xs) (pim : V₁ ⟶ V₂) (ct : pim ≫ aU = aT)
    (mh : MD ⟶ V₂) (ιm : MD ⟶ V₁) (ts : V₁ ⟶ MD)
    (htsd : ts ≫ mh = pim) (htsi : ts ≫ ιm = 𝟙 V₁)
    {M : Xs.Modules} {N₁ : V₁.Modules} {N₂ : V₂.Modules}
    (χ₁ : (Scheme.Modules.pullback aT).obj M ⟶ N₁)
    (χ₂ : (Scheme.Modules.pullback aU).obj M ⟶ N₂)
    (tw : (Scheme.Modules.pullback mh).obj N₂ ⟶ (Scheme.Modules.pullback ιm).obj N₁)
    {Z' Z : Scheme.{u}} (k : Z' ⟶ Z) {d : Z ⟶ V₂} {c : Z ⟶ Xs} (hc : d ≫ aU = c)
    {d' : Z' ⟶ V₁} {c' : Z' ⟶ Xs} (hc' : d' ≫ aT = c') (hkc : k ≫ c = c')
    (p : Z' ⟶ MD) (hp : p = d' ≫ ts) (hpd : p ≫ mh = k ≫ d) (hpi : p ≫ ιm = d')
    (twAt : (Scheme.Modules.pullback pim).obj N₂ ⟶
      (Scheme.Modules.pullback (𝟙 V₁)).obj N₁)
    (htwAt : twAt =
      (Scheme.Modules.pullbackCongr htsd).inv.app N₂ ≫
        (Scheme.Modules.pullbackComp ts mh).inv.app N₂ ≫
        (Scheme.Modules.pullback ts).map tw ≫
        (Scheme.Modules.pullbackComp ts ιm).hom.app N₁ ≫
        (Scheme.Modules.pullbackCongr htsi).hom.app N₁)
    (twAtP : (Scheme.Modules.pullback (k ≫ d)).obj N₂ ⟶
      (Scheme.Modules.pullback d').obj N₁)
    (htwAtP : twAtP =
      (Scheme.Modules.pullbackCongr hpd).inv.app N₂ ≫
        (Scheme.Modules.pullbackComp p mh).inv.app N₂ ≫
        (Scheme.Modules.pullback p).map tw ≫
        (Scheme.Modules.pullbackComp p ιm).hom.app N₁ ≫
        (Scheme.Modules.pullbackCongr hpi).hom.app N₁)
    (hbase : ((Scheme.Modules.pullbackCongr ct).inv.app M ≫
          (Scheme.Modules.pullbackComp pim aU).inv.app M ≫
          (Scheme.Modules.pullback pim).map χ₂) ≫
        (twAt ≫ (Scheme.Modules.pullbackId V₁).hom.app N₁) = χ₁) :
    (Scheme.Modules.pullbackCongr hc').inv.app M ≫
        (Scheme.Modules.pullbackComp d' aT).inv.app M ≫
        (Scheme.Modules.pullback d').map χ₁ =
      (Scheme.Modules.pullbackCongr hkc).inv.app M ≫
        (Scheme.Modules.pullbackComp k c).inv.app M ≫
        (Scheme.Modules.pullback k).map
          ((Scheme.Modules.pullbackCongr hc).inv.app M ≫
            (Scheme.Modules.pullbackComp d aU).inv.app M ≫
            (Scheme.Modules.pullback d).map χ₂) ≫
        (Scheme.Modules.pullbackComp k d).hom.app N₂ ≫ twAtP := by
  subst hp
  subst htwAt
  subst htwAtP
  have he : d' ≫ pim = k ≫ d := by
    rw [← htsd, ← Category.assoc]
    exact hpd
  have hc₂ : (d' ≫ pim) ≫ aU = c' := by
    rw [Category.assoc, ct]
    exact hc'
  have hc₃ : (k ≫ d) ≫ aU = c' := by
    rw [Category.assoc, hc]
    exact hkc
  have htw := pullback_five_comp_leg d' ts mh ιm tw htsd htsi hpd he hpi (Category.comp_id d')
  rw [← pullback_three_comp_leg_assoc k d aU χ₂ hc hc₃ hkc, htw,
    ← pullback_three_leg_congr_assoc aU χ₂ he hc₂ hc₃,
    ← pullback_map_pullbackId_hom_app d' N₁,
    pullback_three_comp_leg_assoc d' pim aU χ₂ ct hc₂ hc',
    Iso.hom_inv_id_app_assoc (Scheme.Modules.pullbackComp d' pim) N₂, ← hbase]
  exact comp_comp_congr _ _ (map_comp₃ _ _ _ _)

end NestedLegs

/-! ### Tag 01MY's comparison map read at given legs -/

section Legs

attribute [local implicit_reducible] AlgebraicGeometry.Proj

universe w w' w''

variable {R₁ R₂ R₃ : Type u} {σ : Type w} {τ : Type w'} {υ : Type w''}
  [CommRing R₁] [CommRing R₂] [CommRing R₃]
  [SetLike σ R₁] [AddSubgroupClass σ R₁]
  [SetLike τ R₂] [AddSubgroupClass τ R₂]
  [SetLike υ R₃] [AddSubgroupClass υ R₃]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) (𝒞 : ℕ → υ) [GradedRing 𝒜] [GradedRing ℬ] [GradedRing 𝒞]

/-- **Tag 01MY's comparison map on the `n`-th twist, read at given legs.** A morphism `q` from a
scheme `W` to the domain of definition of `φ` presents the inverse images along `q ≫ r_φ` and
along `q ≫ U(φ).ι` of the two twists; this is the comparison map transported to them, with the
two composites named by the equations `hd` and `hi` so that neither `φ` nor its domain of
definition occurs in the type. -/
public def twistMapAt (φ : 𝒜 →+*ᵍ ℬ) (n : ℤ) {W : Scheme.{u}}
    (q : W ⟶ (mapDomain 𝒜 ℬ φ).toScheme)
    {d : W ⟶ AlgebraicGeometry.Proj 𝒜} (hd : q ≫ mapHom 𝒜 ℬ φ = d)
    {i : W ⟶ AlgebraicGeometry.Proj ℬ} (hi : q ≫ (mapDomain 𝒜 ℬ φ).ι = i) :
    (Scheme.Modules.pullback d).obj (twistingSheaf 𝒜 n) ⟶
      (Scheme.Modules.pullback i).obj (twistingSheaf ℬ n) :=
  (Scheme.Modules.pullbackCongr hd).inv.app (twistingSheaf 𝒜 n) ≫
    (Scheme.Modules.pullbackComp q (mapHom 𝒜 ℬ φ)).inv.app (twistingSheaf 𝒜 n) ≫
      (Scheme.Modules.pullback q).map (twistMap 𝒜 ℬ φ n) ≫
        (Scheme.Modules.pullbackComp q (mapDomain 𝒜 ℬ φ).ι).hom.app (twistingSheaf ℬ n) ≫
          (Scheme.Modules.pullbackCongr hi).hom.app (twistingSheaf ℬ n)

/-- **Transport of Tag 01MY's comparison map along an equality of graded ring homomorphisms.**
Two equal homomorphisms have the same comparison map, read at legs that are pinned by the same
two composites: the equality is substituted, after which the two presenting morphisms agree
because the inclusion of a domain of definition is a monomorphism and the four equations are
proofs of the same two propositions.

This is the twist-level analogue of
`Stacks.AlgebraicGeometry.Tag07ZGMorphism.isoOfEq_comp_eq_mapHom_congr`. The legs are what makes
it statable: the type of `twistMap` itself mentions the domain of definition, which the equality
of homomorphisms cannot be rewritten inside. -/
public theorem twistMapAt_congr {f g : 𝒜 →+*ᵍ ℬ} (hfg : f = g) (n : ℤ) {W : Scheme.{u}}
    (q : W ⟶ (mapDomain 𝒜 ℬ f).toScheme) (q' : W ⟶ (mapDomain 𝒜 ℬ g).toScheme)
    {d : W ⟶ AlgebraicGeometry.Proj 𝒜} {i : W ⟶ AlgebraicGeometry.Proj ℬ}
    (hd : q ≫ mapHom 𝒜 ℬ f = d) (hi : q ≫ (mapDomain 𝒜 ℬ f).ι = i)
    (hd' : q' ≫ mapHom 𝒜 ℬ g = d) (hi' : q' ≫ (mapDomain 𝒜 ℬ g).ι = i) :
    twistMapAt 𝒜 ℬ f n q hd hi = twistMapAt 𝒜 ℬ g n q' hd' hi' := by
  subst hfg
  obtain rfl : q = q' := (cancel_mono (mapDomain 𝒜 ℬ f).ι).mp (hi.trans hi'.symm)
  rfl

/-- The comparison map at given legs, with the three factors that do not name the legs bracketed
together. This is the shape Tag 01MZ's assertion is stated in. -/
public theorem twistMapAt_eq_comp (φ : 𝒜 →+*ᵍ ℬ) (n : ℤ) {W : Scheme.{u}}
    (q : W ⟶ (mapDomain 𝒜 ℬ φ).toScheme)
    {d : W ⟶ AlgebraicGeometry.Proj 𝒜} (hd : q ≫ mapHom 𝒜 ℬ φ = d)
    {i : W ⟶ AlgebraicGeometry.Proj ℬ} (hi : q ≫ (mapDomain 𝒜 ℬ φ).ι = i) :
    twistMapAt 𝒜 ℬ φ n q hd hi =
      (Scheme.Modules.pullbackCongr hd).inv.app (twistingSheaf 𝒜 n) ≫
        ((Scheme.Modules.pullbackComp q (mapHom 𝒜 ℬ φ)).inv.app (twistingSheaf 𝒜 n) ≫
            (Scheme.Modules.pullback q).map (twistMap 𝒜 ℬ φ n) ≫
            (Scheme.Modules.pullbackComp q (mapDomain 𝒜 ℬ φ).ι).hom.app
              (twistingSheaf ℬ n)) ≫
          (Scheme.Modules.pullbackCongr hi).hom.app (twistingSheaf ℬ n) := by
  simp only [twistMapAt, Category.assoc]

/-- **Stacks Tag 01MZ's third assertion, read at given legs.** Let `φ` and `χ` be composable
homomorphisms of nonnegatively graded rings and let `q`, `p` and `j` be morphisms from one scheme
`W` to the three domains of definition whose composites with the two morphisms and the two
inclusions are pinned by three morphisms `d`, `m` and `i` out of `W`. Then the comparison map of
the composite, read at the legs `d` and `i`, is the comparison map of `φ` read at `d` and `m`
followed by the comparison map of `χ` read at `m` and `i`.

This is `Stacks.AlgebraicGeometry.ProjTwistCompTwistMap.twistMap_comp_of` with the three
congruence isomorphisms its statement carries absorbed into the legs; the absorption is the
cancellation calculus above. In this form the assertion composes, which is what a glueing
argument over a cover of the base needs. -/
public theorem twistMapAt_comp (φ : 𝒜 →+*ᵍ ℬ) (χ : ℬ →+*ᵍ 𝒞) (n : ℤ) {W : Scheme.{u}}
    (q : W ⟶ (mapDomain 𝒜 𝒞 (χ.comp φ)).toScheme)
    (p : W ⟶ (mapDomain 𝒜 ℬ φ).toScheme) (j : W ⟶ (mapDomain ℬ 𝒞 χ).toScheme)
    {d : W ⟶ AlgebraicGeometry.Proj 𝒜} {m : W ⟶ AlgebraicGeometry.Proj ℬ}
    {i : W ⟶ AlgebraicGeometry.Proj 𝒞}
    (hqd : q ≫ mapHom 𝒜 𝒞 (χ.comp φ) = d) (hpd : p ≫ mapHom 𝒜 ℬ φ = d)
    (hpm : p ≫ (mapDomain 𝒜 ℬ φ).ι = m) (hjm : j ≫ mapHom ℬ 𝒞 χ = m)
    (hqi : q ≫ (mapDomain 𝒜 𝒞 (χ.comp φ)).ι = i) (hji : j ≫ (mapDomain ℬ 𝒞 χ).ι = i) :
    twistMapAt 𝒜 𝒞 (χ.comp φ) n q hqd hqi =
      twistMapAt 𝒜 ℬ φ n p hpd hpm ≫ twistMapAt ℬ 𝒞 χ n j hjm hji := by
  have key := ProjTwistCompTwistMap.twistMap_comp_of 𝒜 ℬ 𝒞 φ χ n q p j
    (hqd.trans hpd.symm) (hpm.trans hjm.symm) (hqi.trans hji.symm)
    (ProjTwistCompTwistMap.image_preimage_mapHom_comp 𝒜 ℬ 𝒞 φ χ)
  rw [twistMapAt_eq_comp, key]
  simp only [twistMapAt, Category.assoc]
  rw [pullbackCongr_inv_comp_hom_assoc hqd hpd (hqd.trans hpd.symm) (twistingSheaf 𝒜 n),
    pullbackCongr_hom_comp_inv_assoc hpm hjm (hpm.trans hjm.symm) (twistingSheaf ℬ n),
    pullbackCongr_inv_comp_hom' hqi hji (hqi.trans hji.symm) (twistingSheaf 𝒞 n)]

/-- **Tag 01MY's comparison map read at legs is pseudo-natural in the leg.** Precomposing the
presenting morphism with a further morphism `w` of schemes gives the inverse image along `w` of
the comparison map at the original legs, conjugated by the pseudofunctoriality identifications of
the inverse image for `w` and the two legs.

This is what lets a comparison map read at a leg out of one scheme be compared with one read at a
leg out of a scheme mapping to it, which is how the two halves of the nested compatibility of the
chart identifications are brought to a common leg. -/
public theorem twistMapAt_comp_leg (φ : 𝒜 →+*ᵍ ℬ) (n : ℤ) {W' W : Scheme.{u}} (w : W' ⟶ W)
    (q : W ⟶ (mapDomain 𝒜 ℬ φ).toScheme)
    {d : W ⟶ AlgebraicGeometry.Proj 𝒜} (hd : q ≫ mapHom 𝒜 ℬ φ = d)
    {i : W ⟶ AlgebraicGeometry.Proj ℬ} (hi : q ≫ (mapDomain 𝒜 ℬ φ).ι = i)
    {d' : W' ⟶ AlgebraicGeometry.Proj 𝒜} (hd' : (w ≫ q) ≫ mapHom 𝒜 ℬ φ = d')
    (hwd : w ≫ d = d')
    {i' : W' ⟶ AlgebraicGeometry.Proj ℬ} (hi' : (w ≫ q) ≫ (mapDomain 𝒜 ℬ φ).ι = i')
    (hwi : w ≫ i = i') :
    twistMapAt 𝒜 ℬ φ n (w ≫ q) hd' hi' =
      (Scheme.Modules.pullbackCongr hwd).inv.app (twistingSheaf 𝒜 n) ≫
        (Scheme.Modules.pullbackComp w d).inv.app (twistingSheaf 𝒜 n) ≫
        (Scheme.Modules.pullback w).map (twistMapAt 𝒜 ℬ φ n q hd hi) ≫
        (Scheme.Modules.pullbackComp w i).hom.app (twistingSheaf ℬ n) ≫
        (Scheme.Modules.pullbackCongr hwi).hom.app (twistingSheaf ℬ n) :=
  pullback_five_comp_leg w q (mapHom 𝒜 ℬ φ) (mapDomain 𝒜 ℬ φ).ι (twistMap 𝒜 ℬ φ n) hd hi hd' hwd
    hi' hwi

/-- **The nested compatibility of a morphism out of an inverse image, transported to arbitrary
legs — indexed by the two graded rings.** This is
`Stacks.AlgebraicGeometry.Tag07ZGTwist.three_comp_leg_nested` with the two projective spectra, the
domain of definition and the two absolute twists substituted, taken **once, at the level of
variables**.

That is what makes it usable. The transport abstracts over the two spectra as schemes and over the
three sheaves of modules, so each of its instances asks the kernel to check
`Stacks.AlgebraicGeometry.ProjTwistCompare.twistingSheaf 𝒜 n` at the type
`(AlgebraicGeometry.Proj 𝒜).Modules`, which unfolds `AlgebraicGeometry.Proj`; the kernel carries no
reducibility attributes, and at a concrete pair of affine opens of the base the instance exceeds
its deterministic budget. Here those checks happen once, against variables, and every further
instance is a substitution. -/
public theorem three_comp_leg_nested_proj (φ : 𝒜 →+*ᵍ ℬ) (n : ℤ) {Xs : Scheme.{u}}
    (aT : AlgebraicGeometry.Proj ℬ ⟶ Xs) (aU : AlgebraicGeometry.Proj 𝒜 ⟶ Xs)
    (pim : AlgebraicGeometry.Proj ℬ ⟶ AlgebraicGeometry.Proj 𝒜) (ct : pim ≫ aU = aT)
    (ts : AlgebraicGeometry.Proj ℬ ⟶ (mapDomain 𝒜 ℬ φ).toScheme)
    (htsd : ts ≫ mapHom 𝒜 ℬ φ = pim)
    (htsi : ts ≫ (mapDomain 𝒜 ℬ φ).ι = 𝟙 (AlgebraicGeometry.Proj ℬ))
    {M : Xs.Modules}
    (χ₁ : (Scheme.Modules.pullback aT).obj M ⟶ twistingSheaf ℬ n)
    (χ₂ : (Scheme.Modules.pullback aU).obj M ⟶ twistingSheaf 𝒜 n)
    (tw : (Scheme.Modules.pullback (mapHom 𝒜 ℬ φ)).obj (twistingSheaf 𝒜 n) ⟶
      (Scheme.Modules.pullback (mapDomain 𝒜 ℬ φ).ι).obj (twistingSheaf ℬ n))
    {Z' Z : Scheme.{u}} (k : Z' ⟶ Z) {d : Z ⟶ AlgebraicGeometry.Proj 𝒜} {c : Z ⟶ Xs}
    (hc : d ≫ aU = c) {d' : Z' ⟶ AlgebraicGeometry.Proj ℬ} {c' : Z' ⟶ Xs} (hc' : d' ≫ aT = c')
    (hkc : k ≫ c = c') (p : Z' ⟶ (mapDomain 𝒜 ℬ φ).toScheme) (hp : p = d' ≫ ts)
    (hpd : p ≫ mapHom 𝒜 ℬ φ = k ≫ d) (hpi : p ≫ (mapDomain 𝒜 ℬ φ).ι = d')
    (twAt : (Scheme.Modules.pullback pim).obj (twistingSheaf 𝒜 n) ⟶
      (Scheme.Modules.pullback (𝟙 (AlgebraicGeometry.Proj ℬ))).obj (twistingSheaf ℬ n))
    (htwAt : twAt =
      (Scheme.Modules.pullbackCongr htsd).inv.app (twistingSheaf 𝒜 n) ≫
        (Scheme.Modules.pullbackComp ts (mapHom 𝒜 ℬ φ)).inv.app (twistingSheaf 𝒜 n) ≫
        (Scheme.Modules.pullback ts).map tw ≫
        (Scheme.Modules.pullbackComp ts (mapDomain 𝒜 ℬ φ).ι).hom.app (twistingSheaf ℬ n) ≫
        (Scheme.Modules.pullbackCongr htsi).hom.app (twistingSheaf ℬ n))
    (twAtP : (Scheme.Modules.pullback (k ≫ d)).obj (twistingSheaf 𝒜 n) ⟶
      (Scheme.Modules.pullback d').obj (twistingSheaf ℬ n))
    (htwAtP : twAtP =
      (Scheme.Modules.pullbackCongr hpd).inv.app (twistingSheaf 𝒜 n) ≫
        (Scheme.Modules.pullbackComp p (mapHom 𝒜 ℬ φ)).inv.app (twistingSheaf 𝒜 n) ≫
        (Scheme.Modules.pullback p).map tw ≫
        (Scheme.Modules.pullbackComp p (mapDomain 𝒜 ℬ φ).ι).hom.app (twistingSheaf ℬ n) ≫
        (Scheme.Modules.pullbackCongr hpi).hom.app (twistingSheaf ℬ n))
    (hbase : ((Scheme.Modules.pullbackCongr ct).inv.app M ≫
          (Scheme.Modules.pullbackComp pim aU).inv.app M ≫
          (Scheme.Modules.pullback pim).map χ₂) ≫
        (twAt ≫ (Scheme.Modules.pullbackId
          (AlgebraicGeometry.Proj ℬ)).hom.app (twistingSheaf ℬ n)) = χ₁) :
    (Scheme.Modules.pullbackCongr hc').inv.app M ≫
        (Scheme.Modules.pullbackComp d' aT).inv.app M ≫
        (Scheme.Modules.pullback d').map χ₁ =
      (Scheme.Modules.pullbackCongr hkc).inv.app M ≫
        (Scheme.Modules.pullbackComp k c).inv.app M ≫
        (Scheme.Modules.pullback k).map
          ((Scheme.Modules.pullbackCongr hc).inv.app M ≫
            (Scheme.Modules.pullbackComp d aU).inv.app M ≫
            (Scheme.Modules.pullback d).map χ₂) ≫
        (Scheme.Modules.pullbackComp k d).hom.app (twistingSheaf 𝒜 n) ≫ twAtP :=
  three_comp_leg_nested aT aU pim ct (mapHom 𝒜 ℬ φ) (mapDomain 𝒜 ℬ φ).ι ts htsd htsi χ₁ χ₂ tw
    k hc hc' hkc p hp hpd hpi twAt htwAt twAtP htwAtP hbase

end Legs

/-! ### The comparison maps over a nested pair of affine opens of the base -/

section Nested

attribute [local implicit_reducible] AlgebraicGeometry.Proj

variable (ψ : SheafGradedAlgebraHom A B) (T U : S.Opens) (h : T ≤ U)
  (hT : IsAffineOpen T) (hU : IsAffineOpen U) (n : ℤ)

/-- **The comparison maps of Tag 01MY over a nested pair of affine opens of the base are
compatible with Tag 01NO's comparisons.** For affine opens `T ⊆ U` of the base, the comparison
map of Tag 01MY for the induced homomorphism `Γ(U, A) ⟶ Γ(U, B)`, pulled back along the
transition `U(ψ_T) ⟶ U(ψ_U)` of the chart domains, followed by the comparison map of the
restriction `Γ(U, B) ⟶ Γ(T, B)`, is the comparison map of the restriction
`Γ(U, A) ⟶ Γ(T, A)` followed by the comparison map of Tag 01MY for `Γ(T, A) ⟶ Γ(T, B)`.

Both sides are the comparison map of the single graded ring homomorphism `Γ(U, A) ⟶ Γ(T, B)`,
read through the two factorizations that
`Stacks.AlgebraicGeometry.RelativeProjMapDomain.SheafGradedAlgebraHom.res_comp_sectionHom`
equates: the composition law is Tag 01MZ's third assertion in the form `twistMapAt_comp`, and the
passage between the two factorizations is `twistMapAt_congr`.

The two morphisms `p` and `j` identifying `Proj Γ(T, A)` and `Proj Γ(T, B)` with the domains of
definition of the two restrictions, which are everything by Tag 01NO, are arguments pinned by
their two defining equations rather than written out: `U(ψ_T)` has nine occurrences inside the
factors and expanding them exceeds the kernel's budget. -/
public theorem twistMapAt_nested
    (p : (mapDomain (A.grading T) (B.grading T) (ψ.sectionHom T)).toScheme ⟶
      (mapDomain (A.grading U) (A.grading T) (A.res h)).toScheme)
    (hpd : p ≫ mapHom (A.grading U) (A.grading T) (A.res h) =
      mapHom (A.grading T) (B.grading T) (ψ.sectionHom T) ≫ projInclusionMap A T U h hT hU)
    (hpm : p ≫ (mapDomain (A.grading U) (A.grading T) (A.res h)).ι =
      mapHom (A.grading T) (B.grading T) (ψ.sectionHom T))
    (j : (mapDomain (A.grading T) (B.grading T) (ψ.sectionHom T)).toScheme ⟶
      (mapDomain (B.grading U) (B.grading T) (B.res h)).toScheme)
    (hjm : j ≫ mapHom (B.grading U) (B.grading T) (B.res h) =
      (mapDomain (A.grading T) (B.grading T) (ψ.sectionHom T)).ι ≫
        projInclusionMap B T U h hT hU)
    (hji : j ≫ (mapDomain (B.grading U) (B.grading T) (B.res h)).ι =
      (mapDomain (A.grading T) (B.grading T) (ψ.sectionHom T)).ι) :
    twistMapAt (A.grading U) (A.grading T) (A.res h) n p hpd hpm ≫
        twistMapAt (A.grading T) (B.grading T) (ψ.sectionHom T) n
          (𝟙 (mapDomain (A.grading T) (B.grading T) (ψ.sectionHom T)).toScheme)
          (Category.id_comp _) (Category.id_comp _) =
      twistMapAt (A.grading U) (B.grading U) (ψ.sectionHom U) n
          (chartDomainTrans ψ T U h hT hU) (chartDomainTrans_comp_mapHom ψ T U h hT hU)
          (chartDomainTrans_ι ψ T U h hT hU) ≫
        twistMapAt (B.grading U) (B.grading T) (B.res h) n j hjm hji := by
  have hd₁ : ((AlgebraicGeometry.Proj (B.grading T)).isoOfEq
          (mapDomain_sectionHom_comp_res ψ T U h hT hU)).inv ≫
        mapHom (A.grading U) (B.grading T) ((ψ.sectionHom T).comp (A.res h)) =
      mapHom (A.grading T) (B.grading T) (ψ.sectionHom T) ≫ projInclusionMap A T U h hT hU := by
    rw [← isoOfEq_comp_mapHom_comp_projInclusionMap ψ T U h hT hU, Iso.inv_hom_id_assoc]
  have hi₁ : ((AlgebraicGeometry.Proj (B.grading T)).isoOfEq
          (mapDomain_sectionHom_comp_res ψ T U h hT hU)).inv ≫
        (mapDomain (A.grading U) (B.grading T) ((ψ.sectionHom T).comp (A.res h))).ι =
      (mapDomain (A.grading T) (B.grading T) (ψ.sectionHom T)).ι :=
    Scheme.isoOfEq_inv_ι _ (mapDomain_sectionHom_comp_res ψ T U h hT hU)
  have hd₂ : ((AlgebraicGeometry.Proj (B.grading T)).isoOfEq
          (mapDomain_res_comp_sectionHom ψ T U h hT hU)).inv ≫
        mapHom (A.grading U) (B.grading T) ((B.res h).comp (ψ.sectionHom U)) =
      mapHom (A.grading T) (B.grading T) (ψ.sectionHom T) ≫ projInclusionMap A T U h hT hU := by
    rw [← isoOfEq_comp_chartDomainTrans_comp_mapHom ψ T U h hT hU, Iso.inv_hom_id_assoc,
      chartDomainTrans_comp_mapHom]
  have hi₂ : ((AlgebraicGeometry.Proj (B.grading T)).isoOfEq
          (mapDomain_res_comp_sectionHom ψ T U h hT hU)).inv ≫
        (mapDomain (A.grading U) (B.grading T) ((B.res h).comp (ψ.sectionHom U))).ι =
      (mapDomain (A.grading T) (B.grading T) (ψ.sectionHom T)).ι :=
    Scheme.isoOfEq_inv_ι _ (mapDomain_res_comp_sectionHom ψ T U h hT hU)
  rw [← twistMapAt_comp (A.grading U) (A.grading T) (B.grading T) (A.res h) (ψ.sectionHom T) n
      _ p _ hd₁ hpd hpm (Category.id_comp _) hi₁ (Category.id_comp _),
    ← twistMapAt_comp (A.grading U) (B.grading U) (B.grading T) (ψ.sectionHom U) (B.res h) n
      _ (chartDomainTrans ψ T U h hT hU) j hd₂ (chartDomainTrans_comp_mapHom ψ T U h hT hU)
      (chartDomainTrans_ι ψ T U h hT hU) hjm hi₂ hji]
  exact twistMapAt_congr (A.grading U) (B.grading T) (ψ.res_comp_sectionHom h).symm n _ _
    hd₁ hi₁ hd₂ hi₂

end Nested

/-! ### Local data compatible on refinements glue -/

section Refine

open Stacks.AlgebraicGeometry.ModuleHomGlue

variable {Y : Scheme.{u}}

/-- **The compatibility hypothesis of
`Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_restrict_cover` follows from its
nested case**, for a cover whose pairwise overlaps are covered by members below both.

The hypothesis of that theorem is an equality of maps on the sections of the source over an open
of the base scheme seen by two members of the cover. Here that open is covered by the opens it
has in common with the members refining both, the target is a sheaf, and on each of those the two
maps are the map of the refining member, by the nested case. The passage from the open to the
smaller ones is `Stacks.AlgebraicGeometry.ModuleHomGlue.localApp_map`, and the separation is the
sheaf axiom for the target in the form
`TopCat.Sheaf.eq_of_locally_eq_of_isSheafPresheaf`.

**The nested case is taken with respect to an arbitrary relation `R` on the index, not with
respect to the containment of the images.** For the covering of `U(ψ)` by its pieces the two are
not the same: the piece over an affine open `T` of the base is `U(ψ) ⊓ p⁻¹(T)`, so one piece is
contained in another whenever `U(ψ)` does not meet the difference of the two affine opens, while
the agreement of the chart-local comparison maps is available only for a genuine inclusion
`T ⊆ U` of affine opens of the base. The containment of the images is nowhere used below, so `R`
is left free and the refinement supplies it. -/
public theorem localApp_eq_of_refine {ι : Type u} {Z : ι → Scheme.{u}}
    (g : ∀ i, Z i ⟶ Y) [∀ i, IsOpenImmersion (g i)] {M N : Y.Modules}
    (Θ : ∀ i, M.restrict (g i) ⟶ N.restrict (g i))
    {κ : ι → ι → Type u} (rf : ∀ i j, κ i j → ι) (R : ι → ι → Prop)
    (hrf₁ : ∀ (i j : ι) (k : κ i j), R i (rf i j k))
    (hrf₂ : ∀ (i j : ι) (k : κ i j), R j (rf i j k))
    (hcov : ∀ i j : ι, g i ''ᵁ (⊤ : (Z i).Opens) ⊓ g j ''ᵁ (⊤ : (Z j).Opens) ≤
      ⨆ k : κ i j, g (rf i j k) ''ᵁ (⊤ : (Z (rf i j k)).Opens))
    (hnest : ∀ (i j : ι), R i j →
      ∀ (V : Y.Opens) (W₁ : (Z i).Opens) (W₂ : (Z j).Opens)
        (h₁ : g i ''ᵁ W₁ = V) (h₂ : g j ''ᵁ W₂ = V),
        localApp (g i) (Θ i) h₁ = localApp (g j) (Θ j) h₂)
    (i j : ι) (W₁ : (Z i).Opens) (W₂ : (Z j).Opens) (V : Y.Opens)
    (h₁ : g i ''ᵁ W₁ = V) (h₂ : g j ''ᵁ W₂ = V) :
    localApp (g i) (Θ i) h₁ = localApp (g j) (Θ j) h₂ := by
  have hVi : V ≤ g i ''ᵁ (⊤ : (Z i).Opens) := h₁ ▸ Scheme.Hom.image_mono (g i) le_top
  have hVj : V ≤ g j ''ᵁ (⊤ : (Z j).Opens) := h₂ ▸ Scheme.Hom.image_mono (g j) le_top
  have hc : V ≤ ⨆ k : κ i j, V ⊓ g (rf i j k) ''ᵁ (⊤ : (Z (rf i j k)).Opens) := by
    rw [← inf_iSup_eq]
    exact le_inf le_rfl ((le_inf hVi hVj).trans (hcov i j))
  refine ConcreteCategory.hom_ext _ _ fun s => ?_
  refine TopCat.Sheaf.eq_of_locally_eq_of_isSheafPresheaf N.isSheaf
    (fun k : κ i j => V ⊓ g (rf i j k) ''ᵁ (⊤ : (Z (rf i j k)).Opens))
    (fun _ => inf_le_left) hc fun k => ?_
  have hk : V ⊓ g (rf i j k) ''ᵁ (⊤ : (Z (rf i j k)).Opens) ≤ V := inf_le_left
  have pi := image_preimage_eq_self (g i) (hk.trans hVi)
  have pj := image_preimage_eq_self (g j) (hk.trans hVj)
  have pr := image_preimage_eq_self (g (rf i j k)) (inf_le_right :
    V ⊓ g (rf i j k) ''ᵁ (⊤ : (Z (rf i j k)).Opens) ≤ _)
  refine Eq.trans (localApp_map (g i) (Θ i) h₁ pi hk s).symm (Eq.trans ?_
    (localApp_map (g j) (Θ j) h₂ pj hk s))
  refine Eq.trans (congrArg (fun φ => φ (M.presheaf.map (homOfLE hk).op s))
    (hnest i (rf i j k) (hrf₁ i j k) _ _ _ pi pr)) ?_
  exact congrArg (fun φ => φ (M.presheaf.map (homOfLE hk).op s))
    (hnest j (rf i j k) (hrf₂ i j k) _ _ _ pj pr).symm

end Refine

end Stacks.AlgebraicGeometry.Tag07ZGTwist

end
