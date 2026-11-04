module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.AffineFiniteType
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.TrdegSupportVanishing
public import StacksCore.Tactic.StacksAttribute

/-!
# Cohomology of sheaves supported in bounded transcendence degree

Let `K` be a field, `X` an affine scheme of finite type over `K`, and `E_a ⊆ X` the set of points
`x` with `trdeg_K κ(x) ≤ a`. Every abelian torsion sheaf `𝓕` on `X_ét` whose support is contained
in `E_a` has `H^b_ét(X, 𝓕) = 0` for `b > a + cd(K)`. This is Stacks 0F0W.

The proof is `AlgebraicGeometry.subsingleton_H_of_smallEtaleSupport_subset_of_cdBound`, which is
the source's argument (Stacks 0F0N, 04CA, 03Q5) with the one use of Stacks 0F0V isolated as its
hypothesis; here that hypothesis is discharged by Stacks 0F0V,
`AlgebraicGeometry.Scheme.etaleCohomologicalDimension_le_add_of_topologicalKrullDim_le`.

## Main results

* `AlgebraicGeometry.subsingleton_H_of_smallEtaleSupport_subset_trdegLESet` — Stacks 0F0W.

## References

* [Stacks Project, Tag 0F0W](https://stacks.math.columbia.edu/tag/0F0W)
* [Stacks Project, Tag 0F0V](https://stacks.math.columbia.edu/tag/0F0V)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

attribute [local instance high]
  Stacks.EtaleCohomology.ConstantTransport.hasExt_sheaf_smallEtaleTopology

/-- **Stacks Project, Tag 0F0W.** Let `K` be a field and `X` an affine scheme of finite type over
`K`. Let `E_a ⊆ X` be the set of points `x` with `trdeg_K κ(x) ≤ a`, and let `𝓕` be an abelian
torsion sheaf on `X_ét` whose support is contained in `E_a`. Then `H^b_ét(X, 𝓕) = 0` for
`b > a + cd(K)`.

The scheme is of finite type over `K` through `f`, the residue fields are `K`-algebras through
`f`, `E_a` is `AlgebraicGeometry.Scheme.trdegLESet K f a`, the support is
`Stacks.EtaleCohomology.smallEtaleSupport` (the points over which some geometric stalk is nonzero),
torsion is `Stacks.Torsion.torsionSheafProperty` (Stacks 0DD7), `cd(K)` is the cohomological
dimension `AlgebraicGeometry.Scheme.etaleCohomologicalDimension` of `Spec K` (Stacks 0F0Q), and the
vanishing of `H^b` is `Subsingleton`. -/
@[stacks 0F0W, sga "2 XIV 3.1" "special case", sga "4½ Arcata 4.6.4" "more general"]
theorem subsingleton_H_of_smallEtaleSupport_subset_trdegLESet (K : Type u) [Field K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [IsAffine X] [LocallyOfFiniteType f] (a : ℕ)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F)
    (hsupp : Stacks.EtaleCohomology.smallEtaleSupport F ⊆ Scheme.trdegLESet K f a)
    (b : ℕ) (hb : (a : ℕ∞) + Scheme.etaleCohomologicalDimension (Spec (.of K)) < b) :
    Subsingleton (Sheaf.H.{u + 1, u + 1} F b) :=
  subsingleton_H_of_smallEtaleSupport_subset_of_cdBound K f a
    (fun Z g _ _ hZ =>
      Scheme.etaleCohomologicalDimension_le_add_of_topologicalKrullDim_le K Z g a hZ)
    F hF hsupp b hb

end AlgebraicGeometry

end
