module

public import StacksFrontier.AlgebraicGeometry.Curves.GeometricallyReducedCohenMacaulay
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesCohenMacaulay

/-!
# Geometrically reduced families of curves are Cohen–Macaulay

A family of curves over a field whose total space is a scheme is Cohen–Macaulay as soon as that
scheme is geometrically reduced over the field: the scheme is then reduced, and a reduced locally
Noetherian scheme of dimension at most one is Cohen–Macaulay.

This is the inclusion `Curves^{geomred} ⊂ Curves^{CM}` read on the structure morphism of such a
family: the defining condition of `Curves^{CM}` is Cohen–Macaulayness of that morphism of
algebraic spaces.

## Main results

* `AlgebraicGeometry.Space.isCohenMacaulay_schemeSpaceMap_of_geometricallyReduced`: the structure
  morphism of a geometrically reduced family of curves over a field is Cohen–Macaulay.

## Implementation notes

The base is identified with the spectrum of the field by an equality of schemes, as in
`AlgebraicGeometry.isCohenMacaulay_schemeSpaceMap_iff_of_target_eq_spec`, which converts
Cohen–Macaulayness of the induced morphism of algebraic spaces into Cohen–Macaulayness of the
total scheme. Reducedness of the total scheme is obtained from geometric reducedness together
with flatness over the reduced locally Noetherian base, and the fibres of a morphism locally of
finite type over a locally Noetherian base are locally Noetherian, which is the remaining
hypothesis of that conversion.

## References

* [Stacks Project, Tag 0E1G](https://stacks.math.columbia.edu/tag/0E1G)
* [Stacks Project, Tag 0E0I](https://stacks.math.columbia.edu/tag/0E0I)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u w

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- **A geometrically reduced family of curves over a field is Cohen–Macaulay.** Let
`g : T ⟶ U` be a morphism of the big fppf site of the integers which is flat and locally of
finite type, whose target scheme is the spectrum of a field, and whose source scheme is
geometrically reduced of dimension at most one. Then the induced morphism of algebraic spaces is
Cohen–Macaulay, which is the defining condition of `Curves^{CM}`. -/
@[stacks 0E1G "the inclusion read on the structure morphism of a family of curves over a field, \
  whose Cohen–Macaulayness is the defining condition of the Cohen–Macaulay open substack"]
theorem Space.isCohenMacaulay_schemeSpaceMap_of_geometricallyReduced
    {T U : BigFppfOver B integerBase hZ} (g : T ⟶ U) (k : Type u) [Field k]
    (hU : (BigFppfOver.toScheme B integerBase hZ).obj U = Spec (.of k))
    [Flat ((BigFppfOver.toScheme B integerBase hZ).map g)]
    [LocallyOfFiniteType ((BigFppfOver.toScheme B integerBase hZ).map g)]
    [GeometricallyReduced ((BigFppfOver.toScheme B integerBase hZ).map g)]
    (hdim : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) ≤ 1) :
    Space.IsCohenMacaulay B integerBase hZ (schemeSpaceMap g).hom := by
  have hLNU : IsLocallyNoetherian ((BigFppfOver.toScheme B integerBase hZ).obj U) :=
    hU ▸ (inferInstance : IsLocallyNoetherian (Spec (CommRingCat.of k)))
  have hRedU : IsReduced ((BigFppfOver.toScheme B integerBase hZ).obj U) :=
    hU ▸ (inferInstance : IsReduced (Spec (CommRingCat.of k)))
  have : IsLocallyNoetherian ((BigFppfOver.toScheme B integerBase hZ).obj T) :=
    LocallyOfFiniteType.isLocallyNoetherian ((BigFppfOver.toScheme B integerBase hZ).map g)
  have : IsReduced ((BigFppfOver.toScheme B integerBase hZ).obj T) :=
    GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian
      ((BigFppfOver.toScheme B integerBase hZ).map g)
  refine (isCohenMacaulay_schemeSpaceMap_iff_of_target_eq_spec B hZ g k hU fun v =>
    inferInstanceAs (IsLocallyNoetherian (Limits.pullback
      ((BigFppfOver.toScheme B integerBase hZ).map g)
      (((BigFppfOver.toScheme B integerBase hZ).obj U).fromSpecResidueField v)))).mpr ?_
  exact isCohenMacaulay_of_isReduced_of_topologicalKrullDim_le_one _ hdim

end AlgebraicGeometry

end
