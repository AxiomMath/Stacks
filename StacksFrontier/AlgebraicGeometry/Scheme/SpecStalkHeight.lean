module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.Ideal.Height

/-!
# The local invariants of an affine scheme at a point

A point `x` of `Spec R` is a prime `x.asIdeal` of `R`, and two local invariants of the scheme
at that point are read off the prime: the Krull dimension of the stalk is the height of the prime,
and the residue field of the scheme at `x` is the residue field of the prime, as an algebra over
any base ring `k` mapping to `R`.

## Main results

* `AlgebraicGeometry.ringKrullDim_stalk_spec`: the Krull dimension of the stalk of `Spec R` at
  `x` is the height of the prime `x.asIdeal`.
* `AlgebraicGeometry.algebraMap_spec_residueField`: the isomorphism
  `AlgebraicGeometry.Scheme.Spec.residueFieldIso` is linear over a base ring `k` mapping to `R`.
* `AlgebraicGeometry.trdeg_spec_residueField`: the residue field of `Spec R` at `x` and the
  residue field of the prime `x.asIdeal` have the same transcendence degree over a base ring
  `k` mapping to `R`.

## Implementation notes

The `k`-algebra structure on the residue field of a scheme over `Spec k` is not an instance; it is
introduced in the statement itself, as the composite of global sections with evaluation at the
point.

## References

* [Stacks Project, Tag 02IZ](https://stacks.math.columbia.edu/tag/02IZ)
* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The Krull dimension of the stalk of `Spec R` at a point is the height of the corresponding
prime of `R`. -/
public theorem ringKrullDim_stalk_spec (R : CommRingCat.{u}) (x : Spec R) :
    ringKrullDim ((Spec R).presheaf.stalk x) = x.asIdeal.height := by
  have := x.isPrime
  let _ : Algebra ↥R ↥((Spec R).presheaf.stalk x) := StructureSheaf.stalkAlgebra (↥R) x
  have : IsLocalization.AtPrime (↥((Spec R).presheaf.stalk x)) x.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk R x
  exact IsLocalization.AtPrime.ringKrullDim_eq_height x.asIdeal _

/-- The canonical isomorphism between the residue field of the prime of `x` and the residue
field of `Spec R` at `x` is linear over any base ring `k` mapping to `R`. -/
public theorem algebraMap_spec_residueField (k R : Type u) [CommRing k] [CommRing R]
    [Algebra k R] (x : Spec (.of R)) :
    haveI := x.isPrime
    CommRingCat.ofHom (algebraMap k x.asIdeal.ResidueField) ≫
        (Scheme.Spec.residueFieldIso (.of R) x).inv =
      (Scheme.ΓSpecIso (.of k)).inv ≫
        (Spec.map (CommRingCat.ofHom (algebraMap k R))).appTop ≫
        (Spec (.of R)).Γevaluation x := by
  have := x.isPrime
  have h0 : (Scheme.ΓSpecIso (.of R)).inv ≫ (Spec (.of R)).Γevaluation x =
      CommRingCat.ofHom (algebraMap R x.asIdeal.ResidueField) ≫
        (Scheme.Spec.residueFieldIso (.of R) x).inv :=
    (Scheme.Spec.algebraMap_residueFieldIso_inv (.of R) x).symm
  rw [← Scheme.ΓSpecIso_inv_naturality_assoc, h0, ← Category.assoc]
  congr 1

/-- The residue field of `Spec R` at a point `x` has the same transcendence degree over a base
ring `k` mapping to `R` as the residue field of the prime of `x`. -/
public theorem trdeg_spec_residueField (k R : Type u) [CommRing k] [CommRing R] [Algebra k R]
    (x : Spec (.of R)) :
    haveI := x.isPrime
    letI : Algebra k ((Spec (.of R)).residueField x) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫
        (Spec.map (CommRingCat.ofHom (algebraMap k R))).appTop ≫
        (Spec (.of R)).Γevaluation x).hom.toAlgebra
    Algebra.trdeg k ((Spec (.of R)).residueField x) = Algebra.trdeg k x.asIdeal.ResidueField := by
  have := x.isPrime
  let _ : Algebra k ((Spec (.of R)).residueField x) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫
      (Spec.map (CommRingCat.ofHom (algebraMap k R))).appTop ≫
      (Spec (.of R)).Γevaluation x).hom.toAlgebra
  exact (AlgEquiv.trdeg_eq (AlgEquiv.ofRingEquiv
    (f := (Scheme.Spec.residueFieldIso (.of R) x).symm.commRingCatIsoToRingEquiv)
    fun a ↦ congr($(algebraMap_spec_residueField k R x).hom a))).symm

end AlgebraicGeometry

end
