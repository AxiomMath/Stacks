module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectObject
public import StacksFrontier.AlgebraicGeometry.Perfect.LocalTorDimensionCanonicalCertificate
public import StacksFrontier.AlgebraicGeometry.Morphisms.PseudoCoherent
import StacksCore.Tactic.StacksAttribute

/-!
# Affine-locality of the Tor-dimension clause of relative perfectness

Let `f : X ⟶ S` be a morphism of schemes and let `E` be an object of `D(𝒪_X)`. The second clause
of relative perfectness (Stacks 0DI0) is that `E`, read over `f⁻¹𝒪_S`, locally has finite Tor
dimension, which is part (3) of Stacks 08CG on the inverse-image ringed space `(X, f⁻¹𝒪_S)`.
Stacks 0DI2 asserts that relative perfectness may be tested on affine charts, and its proof
splits into the separate affine-locality statements of its two clauses. The pseudo-coherence
clause is `AlgebraicGeometry.pseudoCoherent_derivedSections_tfae`; this file is the Tor-dimension
clause, as far as it goes.

What is proved here are the two implications *into* condition (1): from the condition on every
affine chart, and from the condition on the members of one affine open covering, the object
locally has finite Tor dimension over `f⁻¹𝒪_S`. Both are statements about the covering that
`AlgebraicGeometry.RingedSpace.LocallyHasFiniteTorDimension` quantifies over, and neither needs
a comparison between the derived tensor products of two different open subspaces, which is why
they hold for an arbitrary certificate family. The converse implication (1) ⟹ (2) does need such
a comparison, and is therefore stated at the canonical family, in
`StacksFrontier/AlgebraicGeometry/Perfect/TorDimensionNestedRestriction.lean`; see the
implementation notes.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.ChartHasFiniteTorDimension`: the Tor-dimension condition of
  clauses (2) and (3) of Stacks 0DI2 on one affine chart — the restriction of `E` to `U`, read
  over `f⁻¹𝒪_S`, has finite Tor dimension.

## Main results

* `AlgebraicGeometry.Scheme.Hom.locallyHasFiniteTorDimension_of_forall_chart`: **the implication
  (2) ⟹ (1) of the Tor-dimension clause of Stacks 0DI2.**
* `AlgebraicGeometry.Scheme.Hom.locallyHasFiniteTorDimension_of_exists_affineCovering`: **the
  implication (3) ⟹ (1) of the Tor-dimension clause of Stacks 0DI2.**

## Implementation notes

**Why only these two implications.** `AlgebraicGeometry.RingedSpace.LocallyHasFiniteTorDimension`
is an existential over open coverings, so an implication whose *conclusion* is that predicate
only has to exhibit a covering, and the affine opens of `X` contained in the preimage of an
affine open of `S` are one — that is the whole content of both results below, and it is a
statement about the lattice of opens rather than about Tor amplitude. The converse implication
(1) ⟹ (2) is of a different kind: it must take the condition on the members of *some* covering
and produce it on *one given* affine open, so it has to restrict Tor amplitude from a member of
the covering to its intersection with that affine open, and then reassemble the finitely many
intervals so obtained into a single one on the affine open. Both halves of that exist —
`Stacks.Cohomology.TorAmplitude.hasTorAmplitude_restrictModules` restricts Tor amplitude to an
open subspace, and
`AffineRelativeTorAmplitude.locallyHasFiniteTorDimension_iff_hasFiniteTorDimension` (in the
namespace `AlgebraicGeometry`) collapses the local condition to the global one on a quasi-compact
space, which an affine open is — but they do not compose, because both are stated for an open
subspace of the *ambient* space, whereas the argument needs an open subspace of an open
subspace. The transport across that nesting, and the composite it gives — that locally finite Tor
dimension is inherited by the restriction to an open subspace — are
`Stacks.Cohomology.TorAmplitude.locallyHasFiniteTorDimension_derivedRestrictModules` of
`StacksFrontier/AlgebraicGeometry/Perfect/TorDimensionNestedRestriction.lean`, and with it the
implication is three lines; it is
`AlgebraicGeometry.Scheme.Hom.chartHasFiniteTorDimension_of_locallyHasFiniteTorDimension` in
that same file. It names the canonical certificate family, where the two results below are
universally quantified over it, because its premise is tested against the certificates at the
members of a covering and its conclusion against the certificate at the given open, and a family
has no relation between its members. The three are assembled, with the pseudo-coherence
clause and the comparison with the module side, into Stacks 0DI2 in
`AlgebraicGeometry.Scheme.Hom.isPerfectRelativeTo_tfae`.

**Which derived tensor product, and why the family is a parameter.** As everywhere in
`AlgebraicGeometry.RingedSpace.CertifiedDerivedSheafTensoring`, the derived tensor product on the
inverse-image ringed space is a parameter: a family of certificates, one on each open subspace,
because part (3) of Stacks 08CG restricts to an open covering. The results below are *universally
quantified* over that family and so are strictly stronger than their reading at any one family,
in particular at the genuine derived tensor product of Stacks 06YU — which is the family
`AlgebraicGeometry.RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily`, at which the
predicate is the pinned `Stacks.Cohomology.TorAmplitude.LocallyHasFiniteTorDimension` by
`AlgebraicGeometry.RingedSpace.locallyHasFiniteTorDimension_canonicalCertificate_iff`. No
compatibility between the certificates at different opens is required: each
member of the covering is tested against the certificate at that member, on both sides.

**The flatness and finite presentation of `f` are not used.** Stacks 0DI2 states them, and
they are what makes its clauses (2) and (3) *expressible* on the module side, where `RΓ(U, E)` is
asserted to be `𝒪_S(V)`-perfect: see `AlgebraicGeometry.Scheme.Hom.SectionsRelativelyPerfect`.
Here the condition stays on the sheaf side, where no algebra structure is needed, so dropping
them strengthens the statements. The affine open `V ⊆ S` is still quantified over, exactly as in
the source and as in the pseudo-coherence clause, because it is what clause (2) asks the chart to
map into.

**Opens of the inverse-image ringed space.** `AlgebraicGeometry.RingedSpace.inverseImage` leaves
the space unchanged, so its opens *are* the opens of `X`; the binders below are at the
inverse-image spelling, which is where the `HasDerivedCategory` instances of the open subspaces
are stated, and affineness of such an open is read at `X`.

## References

* [The Stacks Project, Lemma 36.35.3 (0DI2)](https://stacks.math.columbia.edu/tag/0DI2)
* [The Stacks Project, Definition 36.35.1 (0DI0)](https://stacks.math.columbia.edu/tag/0DI0)
* [The Stacks Project, Definition 20.48.1 (08CG)](https://stacks.math.columbia.edu/tag/08CG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Hom

universe d d' u

variable {X S : Scheme.{u}} (f : X ⟶ S)
  [HasDerivedCategory.{d} (OXMod.{u, u} X.toRingedSpace)]
  [HasDerivedCategory.{d'} (OXMod.{u, u} (RingedSpace.inverseImage S.toRingedSpace f.base))]
  [∀ W : TopologicalSpace.Opens (RingedSpace.inverseImage S.toRingedSpace f.base).carrier,
    HasDerivedCategory.{d'}
      (OXMod.{u, u} ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict
        W.isOpenEmbedding))]

/-- **The Tor-dimension condition of clauses (2) and (3) of Stacks 0DI2 on one chart.** For an
open `U` of `X` and an object `E` of `D(𝒪_X)`, this says that the restriction of `E` to `U`, read
over `f⁻¹𝒪_S`, has finite Tor dimension in the sense of part (2) of Stacks 08CG, measured against
the certificate `D U` of the given family.

This is the sheaf-side half of the chart condition; its module-side counterpart, which asserts
that the complex of `Γ(X, U)`-modules `RΓ(U, E)` is `Γ(S, V)`-perfect and therefore needs `U` to
be affine and `f` flat and locally of finite presentation, is
`AlgebraicGeometry.Scheme.Hom.SectionsRelativelyPerfect`. -/
public def ChartHasFiniteTorDimension
    (D : ∀ W : TopologicalSpace.Opens (RingedSpace.inverseImage S.toRingedSpace f.base).carrier,
      RingedSpace.CertifiedDerivedSheafTensoring.{d', u}
        ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict W.isOpenEmbedding))
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (U : TopologicalSpace.Opens (RingedSpace.inverseImage S.toRingedSpace f.base).carrier) : Prop :=
  (D U).HasFiniteTorDimension
    ((RingedSpace.derivedRestrictModules (RingedSpace.inverseImage S.toRingedSpace f.base) U).obj
      ((derivedScalarRestriction f).obj E))

/-- A covering of `(X, f⁻¹𝒪_S)` on whose members `E` has finite Tor dimension over `f⁻¹𝒪_S`
exhibits condition (1): locally finite Tor dimension *is* the existence of such a covering.

Stated with the index type and the covering as variables so that the two implications below
differ only in how they produce the covering. -/
public theorem locallyHasFiniteTorDimension_of_isOpenCover
    (D : ∀ W : TopologicalSpace.Opens (RingedSpace.inverseImage S.toRingedSpace f.base).carrier,
      RingedSpace.CertifiedDerivedSheafTensoring.{d', u}
        ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict W.isOpenEmbedding))
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace)) (I : Type u)
    (U : I → TopologicalSpace.Opens (RingedSpace.inverseImage S.toRingedSpace f.base).carrier)
    (hU : iSup U = ⊤) (h : ∀ i, ChartHasFiniteTorDimension f D E (U i)) :
    RingedSpace.LocallyHasFiniteTorDimension
      (RingedSpace.inverseImage S.toRingedSpace f.base) D
      ((derivedScalarRestriction f).obj E) :=
  ⟨I, U, hU, h⟩

/-- **The implication (2) ⟹ (1) of the Tor-dimension clause of Stacks 0DI2, for an arbitrary
family of Stacks 08CG certificates.** If, for every affine open `U ⊆ X` whose image lies in an
affine open `V ⊆ S`, the restriction `E|_U` has finite Tor dimension over `f⁻¹𝒪_S`, then `E`
locally has finite Tor dimension over `f⁻¹𝒪_S`. The whole of Stacks 0DI2 is
`AlgebraicGeometry.Scheme.Hom.isPerfectRelativeTo_tfae`.

The covering is the canonical one: the affine opens of `X` contained in the preimage of an affine
open of `S`, indexed by the pairs. They cover `X` because the affine opens of `S` cover `S`
(`AlgebraicGeometry.iSup_affineOpens_eq_top`) and the affine opens of `X` inside a given open
cover it (`AlgebraicGeometry.iSup_affineOpens_subtype_eq`), the affine opens forming a basis.

Only the Tor-dimension conjunct of condition (2) is used; its pseudo-coherence conjunct feeds
`AlgebraicGeometry.pseudoCoherent_derivedSections_tfae` instead. -/
public theorem locallyHasFiniteTorDimension_of_forall_chart
    (D : ∀ W : TopologicalSpace.Opens (RingedSpace.inverseImage S.toRingedSpace f.base).carrier,
      RingedSpace.CertifiedDerivedSheafTensoring.{d', u}
        ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict W.isOpenEmbedding))
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (h : ∀ (U : TopologicalSpace.Opens (RingedSpace.inverseImage S.toRingedSpace f.base).carrier),
      IsAffineOpen (X := X) U → ∀ (V : S.Opens), IsAffineOpen V → U ≤ f ⁻¹ᵁ V →
        ChartHasFiniteTorDimension f D E U) :
    RingedSpace.LocallyHasFiniteTorDimension
      (RingedSpace.inverseImage S.toRingedSpace f.base) D
      ((derivedScalarRestriction f).obj E) := by
  refine locallyHasFiniteTorDimension_of_isOpenCover f D E
    (Σ V : S.affineOpens, {U : X.affineOpens // U.1 ≤ f ⁻¹ᵁ (V : S.Opens)})
    (fun p => (p.2.1.1 : X.Opens)) ?_ fun p => h _ p.2.1.2 _ p.1.2 p.2.2
  refine le_antisymm le_top fun x _ => ?_
  have hx : f.base x ∈ (⨆ V : S.affineOpens, (V : S.Opens)) := by
    rw [iSup_affineOpens_eq_top S]; trivial
  obtain ⟨V, hV⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  have hx' : x ∈ (⨆ U : {U : X.affineOpens // U.1 ≤ f ⁻¹ᵁ (V : S.Opens)}, (U.1.1 : X.Opens)) := by
    rw [iSup_affineOpens_subtype_eq]; exact hV
  obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.mp hx'
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V, U⟩, hU⟩

/-- **The implication (3) ⟹ (1) of the Tor-dimension clause of Stacks 0DI2, for an arbitrary
family of Stacks 08CG certificates.** If there are an affine open covering of `S` and, over each
of its members `V`, an affine open covering of `f⁻¹(V)` on whose members `E` has finite Tor
dimension over `f⁻¹𝒪_S`, then `E` locally has finite Tor dimension over `f⁻¹𝒪_S`. The whole of
Stacks 0DI2 is `AlgebraicGeometry.Scheme.Hom.isPerfectRelativeTo_tfae`.

The two-step covering is flattened to a single one indexed by the pairs: the preimages of the
members of the covering of `S` cover `X`, and each is covered by the given affine opens.

This is the implication the reduction to the affine case uses in the direction *towards* relative
perfectness — the one Stacks 0GEH needs for its implication (2) ⟹ (1), where the fibrewise
conditions are checked on charts and relative perfectness is concluded globally. -/
public theorem locallyHasFiniteTorDimension_of_exists_affineCovering
    (D : ∀ W : TopologicalSpace.Opens (RingedSpace.inverseImage S.toRingedSpace f.base).carrier,
      RingedSpace.CertifiedDerivedSheafTensoring.{d', u}
        ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict W.isOpenEmbedding))
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (h : ∃ (ι : Type u) (V : ι → S.affineOpens),
      (⨆ i, (V i : S.Opens)) = ⊤ ∧
        ∀ i, ∃ (κ : Type u) (U : κ → X.affineOpens),
          (⨆ j, (U j : X.Opens)) = f ⁻¹ᵁ (V i).1 ∧
            ∀ j, ChartHasFiniteTorDimension f D E (U j).1) :
    RingedSpace.LocallyHasFiniteTorDimension
      (RingedSpace.inverseImage S.toRingedSpace f.base) D
      ((derivedScalarRestriction f).obj E) := by
  obtain ⟨ι, V, hVtop, hcov⟩ := h
  choose κ U hUtop hU using hcov
  refine locallyHasFiniteTorDimension_of_isOpenCover f D E (Σ i, κ i)
    (fun p => ((U p.1 p.2 : X.affineOpens) : X.Opens)) ?_ fun p => hU p.1 p.2
  refine le_antisymm le_top fun x _ => ?_
  have hx : f.base x ∈ (⨆ i, (V i : S.Opens)) := by rw [hVtop]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  have hx' : x ∈ (⨆ j, ((U i j : X.affineOpens) : X.Opens)) := by rw [hUtop i]; exact hi
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hx'
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i, j⟩, hj⟩

end AlgebraicGeometry.Scheme.Hom

end
