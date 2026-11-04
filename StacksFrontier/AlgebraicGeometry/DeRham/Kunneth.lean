module

public import StacksFrontier.AlgebraicGeometry.DeRham.KunnethDifferential

/-!
# The de Rham complex of a product

Let `a : X ⟶ S` and `b : Y ⟶ S` be morphisms of schemes. The total complex of the box product of
the two relative de Rham complexes is canonically isomorphic, as a complex, to the relative de
Rham complex of the fibre product:

`Tot(Ω^•_{X/S} ⊠ Ω^•_{Y/S}) ≅ Ω^•_{X ×_S Y / S}`.

In each degree the isomorphism is the one of
`AlgebraicGeometry.Scheme.Hom.deRhamBoxTotalDegreeIso`, which on the `(p, q)` summand is
`ω ⊗ η ↦ pr₁^*ω ∧ pr₂^*η`; its compatibility with the differentials is the graded Leibniz rule,
`AlgebraicGeometry.Scheme.Hom.deRhamBoxTotal_d_comp_deRhamBoxTotalDegreeIso`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.deRhamBoxTotalIso`: **Stacks Project, Tag 0FMA**, the canonical
  isomorphism of complexes `Tot(Ω^•_{X/S} ⊠ Ω^•_{Y/S}) ≅ Ω^•_{X ×_S Y / S}`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.deRhamBoxTotalIso_isoApp`: in each degree the isomorphism of
  complexes is the degreewise isomorphism it was assembled from.

## References

* [Stacks Project, Tag 0FMA](https://stacks.math.columbia.edu/tag/0FMA)
* [Stacks Project, Tag 012Z](https://stacks.math.columbia.edu/tag/012Z)
* [Stacks Project, Tag 0G46](https://stacks.math.columbia.edu/tag/0G46)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

attribute [local instance] hasColimits_sheafOfModules_toRingCat
attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace Scheme.Hom

open FiniteOrderDifferentialOperatorCategory

variable {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)

/-- For two morphisms of schemes `a : X ⟶ S` and `b : Y ⟶ S` there is a canonical isomorphism of
complexes

`Tot(Ω^•_{X/S} ⊠ Ω^•_{Y/S}) ≅ Ω^•_{X ×_S Y / S}`

between the total complex of the box product of the two relative de Rham complexes and the
relative de Rham complex of the fibre product. In degree `n` it is the isomorphism assembled from
the splitting of `Ω_{X ×_S Y/S}` of [Stacks, Tag 01V1], the Künneth decomposition of an exterior
power of a direct sum and the comparison of [Stacks, Tag 01CI], which on the `(p, q)` summand is
`ω ⊗ η ↦ pr₁^*ω ∧ pr₂^*η`; the compatibility with the differentials is the graded Leibniz
rule. -/
@[stacks 0FMA]
noncomputable def deRhamBoxTotalIso :
    deRhamBoxTotal a b ≅ deRhamDiffOpComplex (pullback.fst a b ≫ a) :=
  HomologicalComplex.Hom.isoOfComponents (deRhamBoxTotalDegreeIso a b) fun i j hij => by
    obtain rfl : i + 1 = j := hij
    exact (deRhamBoxTotal_d_comp_deRhamBoxTotalDegreeIso a b i).symm

/-- In each degree the isomorphism of complexes of [Stacks, Tag 0FMA] is the degreewise
isomorphism `Tot(Ω^•_{X/S} ⊠ Ω^•_{Y/S})^n ≅ Ω^n_{X ×_S Y / S}`. -/
theorem deRhamBoxTotalIso_isoApp (n : ℕ) :
    HomologicalComplex.Hom.isoApp (deRhamBoxTotalIso a b) n = deRhamBoxTotalDegreeIso a b n :=
  HomologicalComplex.Hom.isoOfComponents_app (deRhamBoxTotalDegreeIso a b) _ n

end Scheme.Hom

end AlgebraicGeometry

end
