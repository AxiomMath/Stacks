module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.PolynomialAlgebra
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.UniversallyBoundedFinite

/-!
# Witnesses and a refutation for universally bounded fibres

The degrees of the fibres of a morphism of schemes are bounded by a given integer when every
fibre is finite locally free of rank at most that integer. This file exhibits morphisms for
which that holds, and one for which it fails.

Two witnesses are given over an arbitrary field, both with the bound `2`. In the first the
source is the spectrum of a product of two copies of the field, so the fibre has two points; in
the second it is the spectrum of a square-zero extension, so the fibre has one point. Together
they separate the degree of a fibre from the number of its points, which is the content of the
remark after the definition in the source: the degree bounds the number of points and is not
determined by it.

The refutation is the affine line. Its fibre over the base point is the whole line, which is not
finite over the base field, so no integer bounds the degrees of its fibres. In particular the
bounded-fibre condition is not satisfied by every morphism, and the module-finiteness hypothesis
of `AlgebraicGeometry.hasUniversallyBoundedFibers_specMap_of_finite` is a genuine restriction
rather than one that holds vacuously.

## Main results

* `AlgebraicGeometry.boundsFiberDegrees_specMap_prod_self`: the spectrum of `k × k` over the
  spectrum of `k` has fibre degrees bounded by `2`, with a two-point fibre.
* `AlgebraicGeometry.boundsFiberDegrees_specMap_adjoinRoot_sq`: the spectrum of `k[X]/(X²)` over
  the spectrum of `k` has fibre degrees bounded by `2`, with a one-point fibre.
* `AlgebraicGeometry.not_hasUniversallyBoundedFibers_specMap_polynomial`: the affine line over a
  field does not have universally bounded fibres.

## Implementation notes

`Module.IsFiniteLocallyFreeOfRank.finite` repeats the private
`moduleFinite_of_isFiniteLocallyFreeOfRank` of
`StacksFrontier.AlgebraicGeometry.FittingRank.Basic` and the public
`Module.IsFiniteLocallyFreeOfRank.finite` of
`StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Field`; it is restated privately here
rather than importing either of those for one six-line proof, and the private form is what keeps
this module importable alongside the one that exports the public name. The duplication is a
candidate for consolidation.

The refutation runs the identification of the fibre of a morphism of spectra with the spectrum of
the fibre algebra in the direction opposite to the one the producers use: from a bound on the
fibre degree it extracts finiteness of `κ ⊗_k k[X]` over `κ`, and `Polynomial.polyEquivTensor'`
identifies that base change with `κ[X]`, which `Polynomial.not_finite` rules out.

## References

* [Stacks Project, Tag 03J4](https://stacks.math.columbia.edu/tag/03J4)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Polynomial TensorProduct

universe u v

/-- A finite locally free module of rank `r` is a finite module: the rank condition supplies a
basis over each member of a covering family of localizations. -/
private theorem Module.IsFiniteLocallyFreeOfRank.finite {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] {r : ℕ} (h : Module.IsFiniteLocallyFreeOfRank R M r) :
    Module.Finite R M := by
  obtain ⟨ι, g, hspan, hbasis⟩ := h
  refine Module.Finite.of_localizationSpan (Set.range g) hspan ?_
  rintro ⟨x, i, rfl⟩
  exact Module.Finite.of_basis (hbasis i).some

namespace AlgebraicGeometry

/-- The spectrum of a finite `k`-algebra of dimension `n` over the spectrum of a field `k` has
its fibre degrees bounded by `n`. -/
private theorem boundsFiberDegrees_specMap_of_finrank_eq {k : Type u} (A : Type u) [Field k]
    [CommRing A] [Algebra k A] [Module.Finite k A] (n : ℕ) (hn : Module.finrank k A = n) :
    BoundsFiberDegrees (Spec.map (CommRingCat.ofHom (algebraMap k A))) n := by
  have h := Stacks.Morphisms.isFiniteLocallyFreeOfRank_specMap_of_field (k := k) (A := A)
  rw [hn] at h
  exact @boundsFiberDegrees_of_isFiniteLocallyFreeOfRank _ _ _ n h

/-- The spectrum of `k × k` over the spectrum of a field `k` has its fibre degrees bounded by
`2`. The fibre over the unique point has two points, each of residue degree one. -/
public theorem boundsFiberDegrees_specMap_prod_self (k : Type u) [Field k] :
    BoundsFiberDegrees (Spec.map (CommRingCat.ofHom (algebraMap k (k × k)))) 2 :=
  boundsFiberDegrees_specMap_of_finrank_eq (k × k) 2 (by simp)

/-- The spectrum of the square-zero extension `k[X]/(X²)` over the spectrum of a field `k` has
its fibre degrees bounded by `2`. The fibre over the unique point has a single point, of residue
degree one, so the degree of a fibre is not its number of points. -/
public theorem boundsFiberDegrees_specMap_adjoinRoot_sq (k : Type u) [Field k] :
    BoundsFiberDegrees
      (Spec.map (CommRingCat.ofHom (algebraMap k (AdjoinRoot (X ^ 2 : k[X]))))) 2 := by
  have hne : (X ^ 2 : k[X]) ≠ 0 := by simp
  have : Module.Finite k (AdjoinRoot (X ^ 2 : k[X])) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis hne).basis
  refine boundsFiberDegrees_specMap_of_finrank_eq (AdjoinRoot (X ^ 2 : k[X])) 2 ?_
  rw [PowerBasis.finrank (AdjoinRoot.powerBasis hne), AdjoinRoot.powerBasis_dim]
  simp

/-- The affine line over a field does not have universally bounded fibres: its fibre over the
base point is the whole line, which is not a finite module over the base field. -/
public theorem not_hasUniversallyBoundedFibers_specMap_polynomial (k : Type u) [Field k] :
    ¬ HasUniversallyBoundedFibers (Spec.map (CommRingCat.ofHom (algebraMap k k[X]))) := by
  rintro ⟨n, hn⟩
  let p : PrimeSpectrum k := ⟨⊥, inferInstance⟩
  obtain ⟨r, -, hr⟩ := hn p
  rw [← Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property_iff] at hr
  have hr' := ((Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} r).arrow_mk_iso_iff
    (Spec.fiberToSpecResidueFieldIso k k[X] p)).mp hr
  rw [Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property_iff,
    Stacks.Morphisms.isFiniteLocallyFreeOfRank_specMap_iff] at hr'
  have hfin : Module.Finite p.asIdeal.ResidueField (p.asIdeal.Fiber k[X]) := hr'.finite
  exact Polynomial.not_finite (R := p.asIdeal.ResidueField)
    (Module.Finite.equiv (polyEquivTensor' k p.asIdeal.ResidueField).symm.toLinearEquiv)

end AlgebraicGeometry

end
