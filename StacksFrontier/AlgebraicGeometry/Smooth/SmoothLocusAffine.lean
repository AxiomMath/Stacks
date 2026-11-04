module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.Smooth.Locus
public import StacksCore.Tactic.StacksAttribute

/-!
# The smooth locus of an affine morphism

For a ring map `R → A` the morphism `Spec A → Spec R` has two smooth loci: the open subscheme
`AlgebraicGeometry.Scheme.Hom.smoothLocus` of points where the stalk map is formally smooth, and
the set `Algebra.smoothLocus R A` of primes `q` of `A` such that `A_q` is formally smooth over
`R`. This file identifies them.

The comparison is the affine case of
`AlgebraicGeometry.formallySmooth_stalkMap_iff`, read through
`AlgebraicGeometry.Scheme.arrowStalkMapSpecIso`: the stalk map of `Spec A → Spec R` at a prime `q`
is the localized ring map `R_p → A_q`, where `p` is the prime of `R` below `q`, and formal
smoothness over `R_p` is formal smoothness over `R`, because `R → R_p` is formally étale.

## Main results

* `AlgebraicGeometry.formallySmooth_stalkMap_specMap_iff`: the point `q` of `Spec A` lies in the
  smooth locus of `Spec A → Spec R` exactly when `q` lies in `Algebra.smoothLocus R A`.
* `AlgebraicGeometry.locallyOfFinitePresentation_specMap` and
  `AlgebraicGeometry.locallyOfFiniteType_specMap`: the morphism of affine schemes attached to an
  algebra of finite presentation, respectively of finite type, is locally of finite presentation,
  respectively locally of finite type.

## Implementation notes

The two instances are what lets a consumer write down the smooth locus of `Spec A → Spec R` at
all, since `AlgebraicGeometry.Scheme.Hom.smoothLocus` is only defined for a morphism locally of
finite presentation; they are the affine-model case of
`AlgebraicGeometry.HasRingHomProperty.Spec_iff`.

The statement is phrased for a prime `q` of `A` rather than for a point of the scheme
`Spec (CommRingCat.of A)`, the two being the same type; and it is phrased as an equivalence of
membership conditions rather than as an equality of an `AlgebraicGeometry.Scheme.Opens` with a
`Set (PrimeSpectrum A)`, which do not share a type on the nose.

## References

* [Stacks Project, Tag 00TB](https://stacks.math.columbia.edu/tag/00TB), smoothness of a ring map
  at a prime.
* [Stacks Project, Tag 00TF](https://stacks.math.columbia.edu/tag/00TF), openness of the smooth
  locus.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- The morphism of affine schemes attached to an algebra of finite presentation is locally of
finite presentation (Stacks 01TQ). -/
instance locallyOfFinitePresentation_specMap [Algebra.FinitePresentation R A] :
    LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap R A))) :=
  HasRingHomProperty.Spec_iff.mpr (RingHom.finitePresentation_algebraMap.mpr ‹_›)

/-- The morphism of affine schemes attached to an algebra of finite type is locally of finite
type (Stacks 01T2). -/
instance locallyOfFiniteType_specMap [Algebra.FiniteType R A] :
    LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap R A))) :=
  HasRingHomProperty.Spec_iff.mpr (RingHom.finiteType_algebraMap.mpr ‹_›)

/-- **The smooth locus of an affine morphism is the algebra's smooth locus.** For an algebra `A` of
finite presentation over `R`, a prime `q` of `A` lies in the smooth locus of
`Spec A → Spec R` — that is, the stalk map at `q` is formally smooth — exactly when `q` lies in
`Algebra.smoothLocus R A`, that is, `A_q` is formally smooth over `R`.

By `AlgebraicGeometry.Scheme.arrowStalkMapSpecIso` the stalk map at `q` is the localized ring map
`R_p → A_q`, with `p` the prime of `R` below `q`; and `Algebra.FormallySmooth.iff_restrictScalars`
replaces formal smoothness of `A_q` over `R_p` by formal smoothness over `R`, the ring map
`R → R_p` being formally étale. Smoothness at a prime is Stacks 00TB. -/
theorem formallySmooth_stalkMap_specMap_iff [Algebra.FinitePresentation R A]
    (q : PrimeSpectrum A) :
    ((Spec.map (CommRingCat.ofHom (algebraMap R A))).stalkMap q).hom.FormallySmooth ↔
      q ∈ Algebra.smoothLocus R A := by
  have hlo : q.asIdeal.LiesOver (Ideal.comap (algebraMap R A) q.asIdeal) := ⟨rfl⟩
  let _ := Localization.AtPrime.algebraOfLiesOver
    (Ideal.comap (algebraMap R A) q.asIdeal) q.asIdeal
  trans Algebra.FormallySmooth (Localization.AtPrime (Ideal.comap (algebraMap R A) q.asIdeal))
    (Localization.AtPrime q.asIdeal)
  · rw [← RingHom.formallySmooth_algebraMap]
    exact RingHom.FormallySmooth.respectsIso.arrow_mk_iso_iff
      (Scheme.arrowStalkMapSpecIso (CommRingCat.ofHom (algebraMap R A)) q)
  · exact Algebra.FormallySmooth.iff_restrictScalars.symm

end AlgebraicGeometry

end
