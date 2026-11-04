module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.SmallEtaleQuasiCoherentCohomology
public import StacksFrontier.AlgebraicGeometry.Properties.Constructible
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.Dimension
public import StacksFrontier.AlgebraicGeometry.Spaces.SpectralPoints
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.CohomologyAtTheTerminalObject
public import StacksFrontier.Topology.Sheaves.Cohomology.Vanishing.SpectralSpaces

/-!
# Vanishing above the dimension, for schemes and for point spaces of algebraic spaces

Stacks 0A4R is the statement that on a quasi-compact quasi-separated algebraic space `X` of
dimension at most `d` the cohomology of a quasi-coherent module vanishes above degree `d`
(clause (1)), that the restriction map in degree `d` to a quasi-compact open subspace is onto
(clause (2)), and that the cohomology with support in a closed subspace with quasi-compact
complement vanishes above degree `d` (clause (3)).

This file proves **clause (1) in the case where the algebraic space is a scheme**, which is the
base case of the source's induction, and assembles the purely topological half of clause (1) for
a general quasi-compact quasi-separated algebraic space.

The quasi-coherence hypothesis is load-bearing and is *not* a technical convenience: the
abelian-sheaf reading of clause (1) is false.  Take `X = Spec ℝ` and `ℱ = ℤ/2` on `X_étale`.
Then `dim X = 0`, while `H^q(X_étale, ℤ/2) = H^q(Gal(ℂ/ℝ), ℤ/2) = ℤ/2` is nonzero for every
`q > 0`.  So the statement proved here carries `F.IsQuasicoherent` and speaks about the abelian
sheaf `Fᵃ` of Stacks 03DU associated with a quasi-coherent module, never about an arbitrary
abelian sheaf on the small étale site.

## Main results

* `AlgebraicGeometry.subsingleton_smallEtaleCohomology_quasicoherent_of_topologicalKrullDim_le`
  is **Stacks 0A4R, clause (1), for a quasi-compact quasi-separated scheme**: for a
  quasi-coherent module `F` on such a scheme `X` whose topological Krull dimension — which is
  the dimension of `X` as an algebraic space, Stacks 04N6 — is at most `d`, the small étale
  cohomology of `Fᵃ` vanishes in every degree above `d`.
* `AlgebraicGeometry.subsingleton_zariskiCohomology_of_topologicalKrullDim_le`: the Zariski-side
  input, clause (1) of Stacks 0A3G read on a quasi-compact quasi-separated scheme.
* `AlgebraicGeometry.Space.subsingleton_sheafH_points_of_dimension_le`: on the point space of a
  quasi-compact quasi-separated algebraic space of dimension at most `d`, **every** abelian
  sheaf has vanishing cohomology above degree `d`.  This is the topological content of clause
  (1) for a general algebraic space; it is cohomology of the topological space `|X|`, not étale
  cohomology of `X`, and carries no `@[stacks 0A4R]` attribute for that reason.

## The argument for the scheme case

Three library results compose.

* Stacks 094L, `AlgebraicGeometry.spectralSpace_of_compactSpace_of_quasiSeparatedSpace`: the
  underlying space of a quasi-compact quasi-separated scheme is spectral.
* Clause (1) of Stacks 0A3G,
  `Stacks.CohomologyVanishing.subsingleton_sheafH_of_topologicalKrullDim_le`: on a spectral
  space of Krull dimension at most `d` every abelian sheaf has vanishing cohomology above
  degree `d`.  That statement is unconditional — it carries its sheafification and `Ext` data as
  explicit arguments, not as hypotheses on the vanishing.
* Stacks 03P2 for `𝒞 = S_étale`,
  `AlgebraicGeometry.smallEtaleQuasiCoherentGlobalCohomologyIso`: for a quasi-coherent module
  `F` on a scheme `X` and every degree `q`, `H^q(X, ℱ) ≅ H^q(X_étale, Fᵃ)`.  This is the
  comparison the source invokes as Descent, Lemma 35.9.3 (Stacks 03DW) when it says that for a
  scheme the étale cohomology of a quasi-coherent sheaf is the ordinary one, and it is available
  here in *all* degrees, not only in degree zero.

The first two give the vanishing of the Zariski cohomology of the abelian sheaf underlying `F`,
read over the terminal open `⊤` through
`Stacks.Cohomology.TerminalCohomology.subsingleton_H_iff_subsingleton_H'_top`; the third
transports it to the small étale site.

## What is not proved, and why

**Clause (1) for an algebraic space which is not a scheme.** The source argues by the
stratification of a decent space, inducting downward along a finite chain of open subspaces
`X = U₀ ⊇ U₁ ⊇ …` with a quasi-compact separated scheme étale over each `U_p` and an
isomorphism over the stratum `T_p = U_p ∖ U_{p+1}`; the inductive step is the long exact
sequence of the pair `(U_p, T_p)` together with Stacks 0A4P, which identifies the cohomology
with support along `T_p` on `U_p` with the cohomology with support along its preimage on the
scheme.  One of those inputs is missing.  Stacks 0A4P is available, in every degree, both at
the sheaf level on the ambient small étale site
(`AlgebraicGeometry.Space.closedSectionsWithSupportEtaleRestrictionIso` in degree zero and
`AlgebraicGeometry.Space.closedHigherSectionsWithSupportEtaleRestrictionIso` in every degree, in
`StacksFrontier/AlgebraicGeometry/Spaces/SectionsWithSupportEtaleLocal.lean` and
`…/SectionsWithSupportEtaleLocalHigher.lean`) and in the global-sections form
`H^q_{T_p}(U_p, F) = H^q_{f_p^{-1}(T_p)}(V_p, F)` that the induction uses
(`AlgebraicGeometry.Space.closedCohomologyWithSupportEtaleExcisionIso` in
`…/GlobalSectionsWithSupportEtaleExcision.lean`).  What is still missing is the long exact
sequence of the pair on the small étale site of an algebraic space, unavailable for the reason
recorded in `StacksFrontier/AlgebraicGeometry/Spaces/GlobalSectionsWithSupport.lean`: it needs the
surjectivity of `I(X) ⟶ I(U)` on an injective abelian sheaf for `U` the open complement, and an
open subspace of an algebraic space is not an object of the small étale site, whose objects are
scheme charts.

**Clause (2).** Its spectral-space input is clause (2) of Stacks 0A3G, which is available
unconditionally as
`Stacks.CohomologyVanishing.surjective_cohomologyPresheaf_map_top_of_topologicalKrullDim_le`: on
a spectral space of Krull dimension at most `d` the restriction `H^d(X, F) ⟶ H^d(U, F)` to a
quasi-compact open is onto.  (Its conditional form,
`Stacks.CohomologyVanishing.surjective_cohomologyPresheaf_map_top_of_isCohomologyTransport`,
carrying the transport property of Stacks 0A3D as a hypothesis, is the intermediate step from
which the unconditional one is obtained.)  What is still missing is on the étale side, not the
topological one: the passage to the small étale site needs the comparison of Stacks 03P2 over a
*varying* open, `AlgebraicGeometry.smallEtaleQuasiCoherentCohomologyIso`, to be natural in that
open, and its naturality is not proved; without it the surjectivity cannot be transported, since
the map being transported is a restriction map.

**Clause (3).**  Its spectral-space input is clause (3) of Stacks 0A3G — the vanishing above the
dimension of the cohomology with support in a constructible closed subset — and that is now
available unconditionally as
`Stacks.CohomologyVanishing.subsingleton_rightDerived_supportedSections_of_topologicalKrullDim_le`,
in `StacksFrontier/Topology/Sheaves/Cohomology/Vanishing/SpectralSupportVanishing.lean`.  The whole
proposition — all three clauses at once, for a spectral space whose Krull dimension *equals* `d`,
which is how the source states it — is, again in the namespace `Stacks.CohomologyVanishing`,
`subsingleton_sheafH_and_surjective_and_subsingleton_supported_of_topologicalKrullDim_eq`
in `StacksFrontier/Topology/Sheaves/Cohomology/Vanishing/SpectralSpacesFullStatement.lean`.  The
remaining declarations carrying `@[stacks 0A3G]` state clause (1):
`Stacks.CohomologyVanishing.subsingleton_sheafH_of_topologicalKrullDim_le` and
`Stacks.CohomologyVanishing.subsingleton_sheafH_above_topologicalKrullDim`, both unconditional,
together with
`Stacks.CohomologyVanishing.cohomology_subsingleton_of_topologicalKrullDim_eq_zero` (clause (1)
in dimension zero).

Its proof is the source's, and short: the long exact sequence of the pair `(X, X ∖ Z)` together
with clauses (1) and (2).  For `q > d` the term `H^q(X, F)` vanishes by clause (1), so
`H^q_Z(X, F)` is the image of the connecting map out of `H^{q-1}(X ∖ Z, F)`; constructibility of
the closed set `Z` makes `X ∖ Z` a quasi-compact open — `IsRetrocompact_of_IsConstructible`
applied to `Zᶜ`, whose retrocompactness gives compactness on a spectral space — so clause (2),
applied in degree `q - 1`, which is at least `d`, makes `H^{q-1}(X, F) ⟶ H^{q-1}(X ∖ Z, F)` onto;
the connecting map therefore vanishes, and with it `H^q_Z(X, F)`.  Stacks 0902 is not needed:
clause (2) is stated for every `d` bounding the dimension, so it applies in degree `q - 1`
directly, and nothing has to be said about `X ∖ Z` being itself spectral.

The sequence the argument differentiates is
`Stacks.CohomologyVanishing.supportPairShortComplex_shortExact`, which applies the sections
supported on `Z`, the sections over `X` and the sections over `X ∖ Z` degreewise to an injective
resolution and is short exact because injective abelian sheaves are flasque.  (The pre-existing
`Stacks.Cohomology.SectionsWithSupport.longExact_rightDerived_sectionsWithSupport` is the same
sequence for coefficients in sheaves of modules over a ringed space, which is not what an
arbitrary abelian sheaf needs.)

The bridge between that sequence and clauses (1) and (2) is the content of
`StacksFrontier/Topology/Sheaves/Cohomology/Locality/OpensSiteResolution.lean`.  Clauses (1) and (2)
are stated for Mathlib's `Ext`-theoretic cohomology, `CategoryTheory.Sheaf.H` and
`CategoryTheory.Sheaf.cohomologyPresheaf`, while the sequence lives on an injective resolution;
and clause (2) is a statement about a *restriction map*, so the bridge has to be compatible with
restriction.  Every comparison of `Ext`-theoretic cohomology with right-derived sections in this
library — the `sheafCohomologyIsoRightDerivedSections` of `Stacks.Cohomology.FreeYonedaUnivLE`,
`Stacks.Cohomology.SiteSections.cohomologyIsoRightDerivedSections` and their topological
variants — is a choice made separately at each open, so none of them carries that compatibility.
The two that do are `Stacks.Cohomology.cohomologyPresheafIsoResolution` (Stacks 03AY), an
isomorphism of *presheaves*, whose naturality square at an inclusion of opens is therefore free,
and `Stacks.Cohomology.Locality.mapHomologyIso_evaluation_naturality`, which commutes homology
past evaluation at an open compatibly with restriction.  Both are stated for a small site
`[SmallCategory C]`; that file instantiates them at `Opens.grothendieckTopology X` once, as
`Stacks.Cohomology.OpensSite.cohomologyPresheafIsoResolution` and
`Stacks.Cohomology.OpensSite.mapHomologyIso_evaluation_naturality`, and derives from them the
statement clause (3) consumes,
`Stacks.Cohomology.OpensSite.epi_homologyMap_sections_of_epi_cohomologyPresheaf_map`:
surjectivity of a restriction map on the cohomology presheaf, read on an injective resolution.
Paying that instantiation at a signature rather than inside a proof is what makes it cheap.

Clause (3) of Stacks 0A4R needs, on top of clause (3) of Stacks 0A3G, the identification of
Stacks 0A4P in every degree, which as recorded above is available only in degree zero, so that
the cohomology with support along a closed subspace can be computed on a scheme chart.

## Implementation notes

Cohomology on the small étale site of a scheme is `CategoryTheory.Sheaf.H'` over the object
`(opensToEtale X).obj ⊤`, which is a final object of that site by
`AlgebraicGeometry.isTerminal_opensToEtale_top`; this is the spelling of Stacks 03P2 in this
development, and so the one the comparison is available in.  Vanishing is `Subsingleton`,
matching Stacks 0A3G and the vanishing files of `StacksFrontier/Topology/Sheaves/Cohomology/`; the
`IsZero` form is also given, through `AddCommGrpCat.isZero_of_subsingleton`.

The `Ext` universe is the morphism universe `u` on both sides, which is where Stacks 03P2 is
stated; `Stacks.Topology.hasExt_sheafOpens` and `Stacks.Topology.enoughInjectives_sheafOpens`
are local instances, as in the file proving Stacks 03P2, so that instance search produces
`HasExt.{u}` rather than the `HasExt.{u + 1}` of
`AlgebraicGeometry.hasExt_sheaf_smallEtaleTopology`.

The dimension hypothesis for the scheme case is `topologicalKrullDim`, which is the source's
`dim X` for a scheme (Stacks 0055) and agrees with `AlgebraicGeometry.Space.dimension` of the
algebraic space represented by that scheme, the identity being an étale chart of it; the point
space statement is stated with `AlgebraicGeometry.Space.dimension` itself and converts along
part (2) of Stacks 0A4J.

The point space of an algebraic space over a `Scheme.{u}` is a `Type (u + 1)`, so the abelian
sheaves on it have coefficients in `AddCommGrpCat.{u + 1}`; that is the same coefficient universe
as `AlgebraicGeometry.Space.smallEtaleCohomology` and
`AlgebraicGeometry.Space.cohomologyWithSupport` use on the small étale site.

## References

* [Stacks Project, Tag 0055](https://stacks.math.columbia.edu/tag/0055)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03P2](https://stacks.math.columbia.edu/tag/03P2)
* [Stacks Project, Tag 04N6](https://stacks.math.columbia.edu/tag/04N6)
* [Stacks Project, Tag 094L](https://stacks.math.columbia.edu/tag/094L)
* [Stacks Project, Tag 0A3G](https://stacks.math.columbia.edu/tag/0A3G)
* [Stacks Project, Tag 0A4G](https://stacks.math.columbia.edu/tag/0A4G)
* [Stacks Project, Tag 0A4J](https://stacks.math.columbia.edu/tag/0A4J)
* [Stacks Project, Tag 0A4P](https://stacks.math.columbia.edu/tag/0A4P)
* [Stacks Project, Tag 0A4R](https://stacks.math.columbia.edu/tag/0A4R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-! ### The Zariski side -/

attribute [local instance] Stacks.Topology.hasExt_sheafOpens
  Stacks.Topology.enoughInjectives_sheafOpens

/-- **Clause (1) of Stacks 0A3G on a quasi-compact quasi-separated scheme.** The underlying
space of such a scheme is spectral by Stacks 094L, so an abelian sheaf on it has vanishing
cohomology in every degree above its Krull dimension.

The statement is read over the terminal open `⊤`, which is the shape Stacks 03P2 compares with
étale cohomology. -/
theorem subsingleton_zariskiCohomology_of_topologicalKrullDim_le (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X]
    (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (d q : ℕ)
    (hdim : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) (hq : d < q) :
    Subsingleton (Sheaf.H' G q (⊤ : X.Opens)) := by
  refine (Stacks.Cohomology.TerminalCohomology.subsingleton_H_iff_subsingleton_H'_top
    G q).1 ?_
  exact Stacks.CohomologyVanishing.subsingleton_sheafH_of_topologicalKrullDim_le d X
    inferInstance inferInstance G q hdim hq

/-! ### Clause (1) of Stacks 0A4R for a scheme -/

-- `CategoryTheory.Sheaf.H'` carries its `Ext` universe as a parameter, and on the small étale
-- site instance search resolves it to `u + 1` rather than to the morphism universe `u`, because
-- `AlgebraicGeometry.hasExt_sheaf_smallEtaleTopology` is declared after
-- `CategoryTheory.IsGrothendieckAbelian.hasExt` and so wins.  Stacks 03P2 is stated at `u` on
-- both sides, so the priority has to be flipped here too, exactly as in the file proving it.
attribute [local instance 2000] CategoryTheory.IsGrothendieckAbelian.hasExt in
/-- **Stacks 0A4R, clause (1), for a quasi-compact quasi-separated scheme.** Let `X` be a
quasi-compact quasi-separated scheme whose dimension — the Krull dimension of its underlying
topological space — is at most `d`, and let `F` be a quasi-coherent `𝒪_X`-module. Then the
small étale cohomology of the associated abelian sheaf `Fᵃ` of Stacks 03DU vanishes in every
degree `q > d`.

The proof is the base case of the source's induction. The space of `X` is spectral by
Stacks 094L, so clause (1) of Stacks 0A3G makes the Zariski cohomology of the abelian sheaf
underlying `F` vanish above `d`
(`AlgebraicGeometry.subsingleton_zariskiCohomology_of_topologicalKrullDim_le`); Stacks 03P2 for
`𝒞 = S_étale` — which is the comparison the source cites as Stacks 03DW, available here in all
degrees — transports that vanishing to the small étale site.

Quasi-coherence cannot be dropped: on `X = Spec ℝ`, which is zero-dimensional, the constant
abelian sheaf `ℤ/2` on `X_étale` has `H^q(X_étale, ℤ/2) = ℤ/2` for every `q > 0`. -/
@[stacks 0A4R "clause (1) for a scheme: for a quasi-compact quasi-separated scheme X of \
dimension at most d and a quasi-coherent module F, the small étale cohomology of the associated \
abelian sheaf Fᵃ vanishes above degree d"]
theorem subsingleton_smallEtaleCohomology_quasicoherent_of_topologicalKrullDim_le
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] (F : X.Modules)
    [F.IsQuasicoherent] (d q : ℕ) (hdim : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (hq : d < q) :
    Subsingleton (Sheaf.H' (smallEtaleAssociatedSheaf X F) q ((opensToEtale X).obj ⊤)) := by
  have hzar : Subsingleton
      (Sheaf.H' ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) q (⊤ : X.Opens)) :=
    subsingleton_zariskiCohomology_of_topologicalKrullDim_le X _ d q hdim hq
  exact Equiv.subsingleton
    (((forget AddCommGrpCat.{u}).mapIso
      (smallEtaleQuasiCoherentGlobalCohomologyIso X F q)).toEquiv).symm

attribute [local instance 2000] CategoryTheory.IsGrothendieckAbelian.hasExt in
/-- The vanishing of
`AlgebraicGeometry.subsingleton_smallEtaleCohomology_quasicoherent_of_topologicalKrullDim_le`
read as the cohomology group being a zero object. -/
theorem isZero_smallEtaleCohomology_quasicoherent_of_topologicalKrullDim_le
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] (F : X.Modules)
    [F.IsQuasicoherent] (d q : ℕ) (hdim : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (hq : d < q) :
    IsZero (Sheaf.H' (smallEtaleAssociatedSheaf X F) q ((opensToEtale X).obj ⊤)) :=
  have := subsingleton_smallEtaleCohomology_quasicoherent_of_topologicalKrullDim_le X F d q
    hdim hq
  AddCommGrpCat.isZero_of_subsingleton _

attribute [local instance 2000] CategoryTheory.IsGrothendieckAbelian.hasExt in
/-- **Non-vacuity of
`AlgebraicGeometry.subsingleton_smallEtaleCohomology_quasicoherent_of_topologicalKrullDim_le`,
with every typeclass hypothesis discharged by instance synthesis.**  On the spectrum of a
commutative ring of Krull dimension at most `d` the small étale cohomology of the abelian sheaf
associated with a quasi-coherent module vanishes in every degree above `d`.

An affine scheme is quasi-compact and quasi-separated, and the Krull dimension of its space is
the Krull dimension of the ring, `PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim`.  The class
of rings this speaks about is not confined to the zero-dimensional ones: `ℤ` has dimension one,
`k[x, y]` dimension two, and so on. -/
theorem subsingleton_smallEtaleCohomology_quasicoherent_spec_of_krullDimLE (R : Type u)
    [CommRing R] (d : ℕ) [Ring.KrullDimLE d R] (F : (Spec (.of R)).Modules)
    [F.IsQuasicoherent] (q : ℕ) (hq : d < q) :
    Subsingleton (Sheaf.H' (smallEtaleAssociatedSheaf (Spec (.of R)) F) q
      ((opensToEtale (Spec (.of R))).obj ⊤)) :=
  subsingleton_smallEtaleCohomology_quasicoherent_of_topologicalKrullDim_le (Spec (.of R)) F d q
    (by
      rw [show topologicalKrullDim (Spec (.of R)) = ringKrullDim R from
        PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim R]
      exact_mod_cast Ring.krullDimLE_iff.mp ‹_›)
    hq

/-! ### The topological half of clause (1) for an algebraic space -/

namespace Space

attribute [local instance] pointTopology

/-- **The topological half of clause (1) of Stacks 0A4R.** Let `X` be a quasi-compact
quasi-separated algebraic space over a scheme `S` of dimension at most `d`. Then every abelian
sheaf on the *topological space* `|X|` has vanishing cohomology in every degree above `d`.

The point space is spectral by Stacks 0A4G, its Krull dimension is the dimension of `X` by
part (2) of Stacks 0A4J — quasi-separatedness giving decency through
`AlgebraicGeometry.Space.isDecentSpace_of_isAbsolutelyQuasiSeparated` — and clause (1) of
Stacks 0A3G then applies.

This is **not** clause (1) of Stacks 0A4R and carries no attribute for it: the cohomology here
is that of the topological space `|X|`, whereas Stacks 0A4R is about the small étale site of
`X`.  For a scheme the two are compared, for quasi-coherent coefficients, by Stacks 03P2, and
that comparison is what
`AlgebraicGeometry.subsingleton_smallEtaleCohomology_quasicoherent_of_topologicalKrullDim_le`
uses; no such comparison exists for an algebraic space, which has no Zariski site.  Note also
that no quasi-coherence hypothesis appears, and none is needed, because the conclusion is about
`|X|` rather than `X_étale`: it is on the étale site that the abelian-sheaf reading fails. -/
theorem subsingleton_sheafH_points_of_dimension_le (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B S hS X) (hqc : IsQuasiCompactSpace B S hS X)
    (hqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X)
    (G : Sheaf (Opens.grothendieckTopology (points B S hS X)) AddCommGrpCat.{u + 1})
    (d q : ℕ) (hdim : dimension B S hS X hX ≤ (d : WithBot ℕ∞)) (hq : d < q) :
    Subsingleton (Sheaf.H.{u + 1, u + 1, u + 1, u + 1} G q) := by
  have hdec : IsDecentSpace B S hS X :=
    isDecentSpace_of_isAbsolutelyQuasiSeparated B S hS X hX hqs
  have hspec : SpectralSpace (points B S hS X) :=
    spectralSpace_points_of_isQuasiCompactSpace_isAbsolutelyQuasiSeparated B S hS X hX hqc hqs
  have hkd : topologicalKrullDim (points B S hS X) ≤ (d : WithBot ℕ∞) := by
    rw [topologicalKrullDim_points_eq_dimension_of_isDecentSpace B S hS hX hdec]
    exact hdim
  exact Stacks.CohomologyVanishing.subsingleton_sheafH_of_topologicalKrullDim_le d
    (points B S hS X) inferInstance (hasExt_of_enoughInjectives _) G q hkd hq

end Space

end AlgebraicGeometry

end
