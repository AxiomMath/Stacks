module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentDerivedHom
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectObject

/-!
# Relatively perfect objects along a relative descent situation

In the relative descent situation of Stacks 0DI6 — a directed inverse limit `S = lim Sᵢ` of
quasi-compact, quasi-separated schemes with affine transition maps, and a flat morphism of
finite presentation `X₀ ⟶ S₀` with base changes `Xᵢ ⟶ Sᵢ` and `X ⟶ S` — the `S`-perfect objects
of `D(𝒪_X)` are the colimit of the `Sᵢ`-perfect objects of `D(𝒪_{Xᵢ})`. One half of that
assertion is that every `S`-perfect object of `D(𝒪_X)` is, at some stage `i`, the derived
pullback `Lfᵢ^*Eᵢ` of an `Sᵢ`-perfect object `Eᵢ` of `D(𝒪_{Xᵢ})`. That half is stated here, as a
predicate on the situation.

## Main definitions

* `AlgebraicGeometry.RelativeDescentSituation.structureMapAt` and `structureMapLimit`: the
  structure morphisms `Xᵢ ⟶ Sᵢ` and `X ⟶ S`, the base changes of `X₀ ⟶ S₀`.
* `AlgebraicGeometry.RelativeDescentSituation.StageCertificates` and `LimitCertificates`: the
  derived-tensoring certificates on the inverse-image ringed spaces of those two morphisms,
  against which relative perfectness is stated.
* `AlgebraicGeometry.RelativeDescentSituation.PerfectEssentiallySurjective`: the half of
  Stacks 0DI8 just described.

## Implementation notes

Relative perfectness is `AlgebraicGeometry.Scheme.Hom.IsPerfectRelativeTo` of Stacks 0DI0, whose
second clause — local finiteness of the Tor dimension over the base — is stated against a family
of derived-tensoring certificates, one on each open of the inverse-image ringed space, since no
canonical derived tensor product is constructed there. Those families are therefore parameters:
one for the limit and one for each stage.

Flatness and local finite presentation of the structure morphisms are not hypotheses: they are
base changes of `X₀ ⟶ S₀`, whose flatness and finite presentation are fields of the situation,
and both properties are stable under base change.

The conclusion asks for the existence of *some* isomorphism `Lfᵢ^*Eᵢ ≅ E`, which is what
essential surjectivity of a functor means; it is the shape of
`CategoryTheory.Functor.essImage`, and an isomorphism is data, so the predicate quantifies over
`Nonempty`.

The predicate is proved for every situation, at the canonical certificate families, in
`StacksFrontier/AlgebraicGeometry/Perfect/RelativeDescentPerfectColimit.lean`
(`AlgebraicGeometry.RelativeDescentSituation.perfectEssentiallySurjectiveCanonical`),
by the induction of Stacks 08DR over the quasi-compact opens of `X₀`: the affine case is
Stacks 0DHX read through the affine dictionary, and the union step is the glueing of Stacks 08DG
along an isomorphism on the overlap which descends to a stage by Stacks 0DI7. Stacks 0DI8 is
`AlgebraicGeometry.RelativeDescentSituation.isPerfectRelativeTo_colimit`.

## References

* [Stacks Project, Lemma 36.35.6 (Tag 0DI8)](https://stacks.math.columbia.edu/tag/0DI8)
* [Stacks Project, Tag 0DI6](https://stacks.math.columbia.edu/tag/0DI6)
* [Stacks Project, Definition 36.35.1 (Tag 0DI0)](https://stacks.math.columbia.edu/tag/0DI0)
* [Stacks Project, Tag 0DHX](https://stacks.math.columbia.edu/tag/0DHX)
* [Stacks Project, Lemma 36.35.3 (Tag 0DI2)](https://stacks.math.columbia.edu/tag/0DI2)
* [Stacks Project, Tag 08DR](https://stacks.math.columbia.edu/tag/08DR)
* [Stacks Project, Tag 08DG](https://stacks.math.columbia.edu/tag/08DG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
open StrictlyPerfect
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RelativeDescentSituation

variable {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] (D : RelativeDescentSituation.{u, u} I)

/-- The structure morphism `Xᵢ ⟶ Sᵢ` of a stage, the base change of `X₀ ⟶ S₀`. -/
abbrev structureMapAt (i : D.LaterIndex) :
    D.schemeAt i ⟶ D.descent.system.obj (op i.1) :=
  pullback.snd D.X₀.hom (D.baseMap i)

/-- The structure morphism `X ⟶ S` of the limit, the base change of `X₀ ⟶ S₀`. -/
abbrev structureMapLimit : D.limitScheme ⟶ D.descent.limitCone.pt :=
  pullback.snd D.X₀.hom (D.descent.limitCone.π.app (op D.descent.base))

/-- The derived-tensoring certificates on the inverse-image ringed space of the structure
morphism of a stage. -/
abbrev StageCertificates (i : D.LaterIndex) : Type _ :=
  ∀ U : Opens (RingedSpace.inverseImage (D.descent.system.obj (op i.1)).toRingedSpace
      (D.structureMapAt i).base).carrier,
    RingedSpace.CertifiedDerivedSheafTensoring.{u + 1, u}
      ((RingedSpace.inverseImage (D.descent.system.obj (op i.1)).toRingedSpace
        (D.structureMapAt i).base).restrict U.isOpenEmbedding)

/-- The derived-tensoring certificates on the inverse-image ringed space of the structure
morphism of the limit. -/
abbrev LimitCertificates : Type _ :=
  ∀ U : Opens (RingedSpace.inverseImage D.descent.limitCone.pt.toRingedSpace
      D.structureMapLimit.base).carrier,
    RingedSpace.CertifiedDerivedSheafTensoring.{u + 1, u}
      ((RingedSpace.inverseImage D.descent.limitCone.pt.toRingedSpace
        D.structureMapLimit.base).restrict U.isOpenEmbedding)

/-- **One half of Stacks 0DI8.** Every object of `D(𝒪_X)` perfect relative to the limit base `S`
is the derived pullback, from some stage `i`, of an object of `D(𝒪_{Xᵢ})` perfect relative to
`Sᵢ`. This is essential surjectivity of the comparison out of the colimit of the categories of
relatively perfect objects; nothing in this file proves it. -/
def PerfectEssentiallySurjective (cl : D.LimitCertificates)
    (cs : ∀ i : D.LaterIndex, D.StageCertificates i) : Prop :=
  letI : Flat D.X₀.hom := D.flat
  letI : LocallyOfFinitePresentation D.X₀.hom :=
    D.finitePresentation.locallyOfFinitePresentation
  ∀ E : DerivedCategory (OXMod.{u, u} D.limitScheme.toRingedSpace),
    D.structureMapLimit.IsPerfectRelativeTo cl E →
      ∃ (i : D.LaterIndex) (Ei : DerivedCategory (OXMod.{u, u} (D.schemeAt i).toRingedSpace)),
        (D.structureMapAt i).IsPerfectRelativeTo (cs i) Ei ∧
          Nonempty ((derivedPullback (D.projection i).toLRSHom.toShHom).obj Ei ≅ E)

end AlgebraicGeometry.RelativeDescentSituation

end
