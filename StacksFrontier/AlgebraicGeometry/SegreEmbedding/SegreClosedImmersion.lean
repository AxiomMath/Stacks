module

public import StacksFrontier.AlgebraicGeometry.SegreEmbedding.SegrePresentation
public import StacksFrontier.AlgebraicGeometry.SegreEmbedding.ProjPoly
public import StacksFrontier.AlgebraicGeometry.SegreEmbedding.Reduction
public import StacksFrontier.AlgebraicGeometry.RelativeProjChain.EventualSurjective
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Local

/-!
# The Segre presentation induces a closed immersion, and what is left of Tag 01WD

The Segre presentation of
`StacksFrontier/AlgebraicGeometry/SegreEmbedding/SegrePresentation.lean` is a graded ring
homomorphism surjective in every degree, which is more than Stacks Tag 01N1 (2) asks for.  This
file feeds it to that criterion and reindexes the target, obtaining a closed immersion of
`AlgebraicGeometry.Proj` of the Segre product into the integral model of projective
`(n * m + n + m)`-space, and then records the consequence:

**the remaining content of Tag 01WD is exactly one isomorphism of schemes.**

That is
`Stacks.AlgebraicGeometry.SegreClosedImmersion.absoluteSegre_of_projSegreIso`: an isomorphism
between `Proj` of the Segre product and the fibre product over the terminal scheme of the two
integral models yields `Stacks.AlgebraicGeometry.SegreEmbedding.AbsoluteSegre n m`, and with it,
by `Stacks.AlgebraicGeometry.SegreEmbedding.exists_segreEmbedding_of_absolute`, Tag 01WD over
every base scheme.  Nothing else is owed.

## What is proved, and the route

* `Stacks.AlgebraicGeometry.SegreClosedImmersion.isClosedImmersion_mapHomOfTop`: a graded ring
  homomorphism eventually surjective on components induces a closed immersion
  `Proj ℬ ⟶ Proj 𝒜` on the whole of `Proj ℬ`.  This is
  `Stacks.AlgebraicGeometry.RelativeProjChain.isClosedImmersion_mapHom_of_eventually_surjective`,
  which gives the statement on the domain of definition, composed with the two isomorphisms that
  `Stacks.AlgebraicGeometry.RelativeProj.mapHomOfTop` is built from; the domain of definition is
  everything by
  `Stacks.AlgebraicGeometry.RelativeProjChain.mapDomain_eq_top_of_eventually_surjective`.

* `Stacks.AlgebraicGeometry.SegreClosedImmersion.projSegre R X Y` names `Proj` of the Segre
  product, and `segreProjMap` the morphism it induces to `Proj` of the polynomial ring on `X × Y`;
  `isClosedImmersion_segreProjMap` is the previous item applied to
  `Stacks.RingTheory.SegreProduct.eventually_surjective_gradedAddHom`.

* `Stacks.AlgebraicGeometry.SegreClosedImmersion.absoluteSegreHom n m` composes that with the
  reindexing `Stacks.AlgebraicGeometry.ProjPoly.segreTargetIso`, landing in
  `AlgebraicGeometry.projectiveSpaceAtUniverse (n * m + n + m)`;
  `isClosedImmersion_absoluteSegreHom` is its closedness.

* `Stacks.AlgebraicGeometry.SegreClosedImmersion.absoluteSegre_of_projSegreIso` is the handover.

## Implementation notes

Both gradings involved — `MvPolynomial.gradedAlgebra` for the polynomial ring and
`Stacks.RingTheory.SegreProduct.gradingGradedAlgebra` for the Segre product — are definitions
rather than instances, and a local instance introduced in a *statement* does not survive into the
proof of that statement.  So, as in
`StacksFrontier/AlgebraicGeometry/SegreEmbedding/ProjPoly.lean`, the general results here take
the gradings as ordinary instance **binders**, and only the final specialisations supply the
canonical ones, in the *body* of a definition.  `projSegre` exists to give those specialisations a
name, so that the handover isomorphism is stated between two named objects and carries no local
instance at all.

The two rings must share a universe, since that is how
`Stacks.AlgebraicGeometry.RelativeProj.mapHomOfTop` is stated; the polynomial ring on `X × Y` and
the Segre product inside the polynomial ring on `X ⊕ Y` do, for any index types and any
coefficient ring.

## What is not done

The isomorphism that `absoluteSegre_of_projSegreIso` takes as its hypothesis is **not** proved
here, and is the whole of what Tag 01WD still owes:

`projSegre (ULift.{u} ℤ) (Fin (n + 1)) (Fin (m + 1)) ≅`
`  projectiveSpaceOver m (projectiveSpaceAtUniverse.{u} n)`.

Its proof is a gluing argument: `Proj` of the Segre product is covered by the standard opens
`D₊(x_i y_j)` on which it is the spectrum of the degree-zero homogeneous localisation, the
product of the two projective spaces is covered by the corresponding products of standard opens,
and one has to match the two covers and check the compatibilities on overlaps.  The ring-theoretic
half is done: `StacksFrontier/AlgebraicGeometry/SegreEmbedding/SegreCharts.lean` exhibits those
loci as affine opens and proves they cover, and
`StacksFrontier/AlgebraicGeometry/SegreEmbedding/SegreChartRing.lean` computes the ring each is
the spectrum of, as a tensor product of the two chart rings of the two projective spaces, those
being computed in `StacksFrontier/AlgebraicGeometry/SegreEmbedding/PolyChart.lean`.  What remains
is geometric, and those two files' own "what is not done" sections list it.

Nothing is proved about how `absoluteSegreHom` interacts with the structure morphisms to `Spec`
of the degree-zero parts, and the kernel of the presentation — the two-by-two minors — is not
identified.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace Stacks.AlgebraicGeometry.SegreClosedImmersion

universe v u w w'

/-! ### Eventual surjectivity gives a closed immersion on all of `Proj` -/

section General

variable {A B : Type u} {σ : Type w} {τ : Type w'}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]

/-- A graded ring homomorphism surjective in all sufficiently large degrees induces a closed
immersion on the whole of `Proj ℬ`, not merely on its domain of definition. -/
public theorem isClosedImmersion_mapHomOfTop (ψ : 𝒜 →+*ᵍ ℬ)
    (hdom : ProjShared.mapDomain 𝒜 ℬ ψ = ⊤)
    (hψ : ∀ᶠ d : ℕ in Filter.atTop,
      Function.Surjective (GradedRingHom.gradedAddHom ψ d)) :
    IsClosedImmersion (RelativeProj.mapHomOfTop 𝒜 ℬ ψ hdom) := by
  have : IsClosedImmersion (ProjTwistChain.mapHom 𝒜 ℬ ψ) :=
    RelativeProjChain.isClosedImmersion_mapHom_of_eventually_surjective 𝒜 ℬ ψ hψ
  rw [RelativeProj.mapHomOfTop]
  infer_instance

end General

/-! ### The Segre product, with the gradings as binders -/

section Binders

variable (R : Type u) [CommRing R] (X Y : Type v)
  [GradedAlgebra (MvPolynomial.homogeneousSubmodule (X × Y) R)]
  [GradedAlgebra (Stacks.RingTheory.SegreProduct.grading R X Y)]

/-- The morphism `Proj` of the Segre product `⟶` `Proj` of the polynomial ring on the pairs,
induced by the Segre presentation. -/
public noncomputable def segreProjHom :
    AlgebraicGeometry.Proj (Stacks.RingTheory.SegreProduct.grading R X Y) ⟶
      AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (X × Y) R) :=
  RelativeProj.mapHomOfTop _ _ (Stacks.RingTheory.SegreProduct.presentation R X Y)
    (RelativeProjChain.mapDomain_eq_top_of_eventually_surjective _ _ _
      (Stacks.RingTheory.SegreProduct.eventually_surjective_gradedAddHom R X Y))

/-- The morphism induced by the Segre presentation is a closed immersion. -/
public theorem isClosedImmersion_segreProjHom :
    IsClosedImmersion (segreProjHom R X Y) :=
  isClosedImmersion_mapHomOfTop _ _ _ _
    (Stacks.RingTheory.SegreProduct.eventually_surjective_gradedAddHom R X Y)

end Binders

/-! ### The named objects, with the canonical gradings -/

variable (R : Type u) [CommRing R]

/-- `AlgebraicGeometry.Proj` of the Segre product.  The canonical grading is supplied here, in the
body, so that statements about this object carry no local instance. -/
public noncomputable def projSegre (X Y : Type v) : Scheme.{max v u} :=
  letI := Stacks.RingTheory.SegreProduct.gradingGradedAlgebra R X Y
  AlgebraicGeometry.Proj (Stacks.RingTheory.SegreProduct.grading R X Y)

/-- The morphism induced by the Segre presentation, between the named objects. -/
public noncomputable def segreProjMap (X Y : Type v) :
    projSegre R X Y ⟶ ProjPoly.projPoly R (X × Y) :=
  letI : GradedAlgebra (MvPolynomial.homogeneousSubmodule (X × Y) R) :=
    MvPolynomial.gradedAlgebra
  letI := Stacks.RingTheory.SegreProduct.gradingGradedAlgebra R X Y
  segreProjHom R X Y

/-- The morphism induced by the Segre presentation, between the named objects, is a closed
immersion. -/
public theorem isClosedImmersion_segreProjMap (X Y : Type v) :
    IsClosedImmersion (segreProjMap R X Y) := by
  let : GradedAlgebra (MvPolynomial.homogeneousSubmodule (X × Y) R) :=
    MvPolynomial.gradedAlgebra
  let := Stacks.RingTheory.SegreProduct.gradingGradedAlgebra R X Y
  exact isClosedImmersion_segreProjHom R X Y

/-! ### The closed immersion into the integral model -/

/-- **The Segre closed immersion into the integral model.**  `Proj` of the Segre product of the
two polynomial rings in `n + 1` and `m + 1` variables maps to the integral model of projective
`(n * m + n + m)`-space, by the Segre presentation followed by the reindexing of the variables. -/
public noncomputable def absoluteSegreHom (n m : ℕ) :
    projSegre (ULift.{u} ℤ) (Fin (n + 1)) (Fin (m + 1)) ⟶
      projectiveSpaceAtUniverse.{u} (n * m + n + m) :=
  segreProjMap (ULift.{u} ℤ) (Fin (n + 1)) (Fin (m + 1)) ≫ (ProjPoly.segreTargetIso n m).hom

/-- The Segre morphism into the integral model of projective space is a closed immersion. -/
public theorem isClosedImmersion_absoluteSegreHom (n m : ℕ) :
    IsClosedImmersion (absoluteSegreHom.{u} n m) := by
  have := isClosedImmersion_segreProjMap (ULift.{u} ℤ) (Fin (n + 1)) (Fin (m + 1))
  rw [absoluteSegreHom]
  infer_instance

/-- **The remaining content of Stacks Tag 01WD is exactly one isomorphism.**  Given an
isomorphism of `AlgebraicGeometry.Proj` of the Segre product with the fibre product over the
terminal scheme of the two integral models, the absolute Segre closed immersion exists, and hence
— by `Stacks.AlgebraicGeometry.SegreEmbedding.exists_segreEmbedding_of_absolute` — Tag 01WD holds
over every base scheme.

Nothing beyond that isomorphism is owed: the closed immersion it is composed with is
`absoluteSegreHom`, which is proved here unconditionally. -/
public theorem absoluteSegre_of_projSegreIso (n m : ℕ)
    (e : projSegre (ULift.{u} ℤ) (Fin (n + 1)) (Fin (m + 1)) ≅
      projectiveSpaceOver m (projectiveSpaceAtUniverse.{u} n)) :
    Stacks.AlgebraicGeometry.SegreEmbedding.AbsoluteSegre.{u} n m := by
  have := isClosedImmersion_absoluteSegreHom.{u} n m
  exact ⟨e.inv ≫ absoluteSegreHom n m, inferInstance⟩

end Stacks.AlgebraicGeometry.SegreClosedImmersion

end
