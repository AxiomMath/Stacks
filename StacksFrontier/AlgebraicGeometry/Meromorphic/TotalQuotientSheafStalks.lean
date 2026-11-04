module

public import Mathlib.Topology.Sheaves.Sheafify
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.StalksWeaklyAssociated
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.TotalQuotient

/-!
# Stalks of the sheaf of meromorphic functions

The sheaf of total quotient rings of a scheme is the sheafification of the presheaf which
localizes each ring of sections at the sections that are nonzerodivisors in every stalk.
Sheafification does not change stalks, so every description of a stalk of that presheaf is
also a description of the corresponding stalk of the sheaf. In particular, when every weakly
associated point of the scheme is a generic point of an irreducible component and every
quasi-compact open has finitely many irreducible components, the stalk of the sheaf of
meromorphic functions at a point is the total quotient ring of the local ring there.

## Main definitions

* `AlgebraicGeometry.stalkTotalQuotientSheafIso`: the comparison isomorphism between a stalk
  of the presheaf of total quotient rings and the same stalk of its sheafification.

## Main results

* `AlgebraicGeometry.stalkFunctor_map_toTotalQuotientSheaf_hom`: the map induced on stalks by
  the structure map of the sheaf of total quotient rings factors through the comparison
  isomorphism.
* `AlgebraicGeometry.stalk_totalQuotientSheaf_isFractionRing_of_weaklyAssociated`: under the
  two hypotheses above, the stalk of the sheaf of meromorphic functions is the total quotient
  ring of the local ring.

## Implementation notes

The stalk-level statement for the presheaf is the lemma
`stalk_totalQuotientPresheaf_isFractionRing_of_weaklyAssociatedPoints_subset_genericPoints`.
The transfer to the sheaf uses `TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso`: the
map induced on stalks by the sheafification unit is an isomorphism, and the structure map of
the sheaf is the composite of the objectwise localization map with that unit, so the
comparison isomorphism is an isomorphism of algebras over the local ring.

## References

* [Stacks Project, Tag 0EMF](https://stacks.math.columbia.edu/tag/0EMF)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The isomorphism between the stalk at a point of the presheaf of total quotient rings and the
stalk at that point of the sheaf of total quotient rings, induced by the sheafification unit. -/
noncomputable def stalkTotalQuotientSheafIso (X : Scheme.{u}) (x : X) :
    X.presheaf.totalQuotientPresheaf.stalk x ≅ X.totalQuotientSheaf.presheaf.stalk x :=
  @asIso _ _ _ _ _ (TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x CommRingCat
    X.presheaf.totalQuotientPresheaf)

/-- The forward map of `stalkTotalQuotientSheafIso X x` is the map induced on stalks by the
sheafification unit of the presheaf of total quotient rings. -/
@[simp]
lemma stalkTotalQuotientSheafIso_hom (X : Scheme.{u}) (x : X) :
    (stalkTotalQuotientSheafIso X x).hom =
      (TopCat.Presheaf.stalkFunctor CommRingCat x).map
        (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
          X.presheaf.totalQuotientPresheaf) :=
  rfl

/-- The map induced on stalks by the structure map of the sheaf of total quotient rings is the
map induced by the objectwise localization map followed by the comparison isomorphism. -/
lemma stalkFunctor_map_toTotalQuotientSheaf_hom (X : Scheme.{u}) (x : X) :
    (TopCat.Presheaf.stalkFunctor CommRingCat x).map X.toTotalQuotientSheaf.hom =
      (TopCat.Presheaf.stalkFunctor CommRingCat x).map X.presheaf.toTotalQuotientPresheaf ≫
        (stalkTotalQuotientSheafIso X x).hom :=
  Functor.map_comp _ _ _

/-- If every weakly associated point of a scheme is a generic point of an irreducible component
and every quasi-compact open has finitely many irreducible components, then the stalk `K_{X, x}`
of the sheaf of meromorphic functions at any point is the total quotient ring of the local ring
`𝒪_{X, x}`. -/
@[stacks 0EMF "stalk_total_quotient_ring"]
lemma stalk_totalQuotientSheaf_isFractionRing_of_weaklyAssociated
    (X : Scheme.{u})
    (hass : Stacks.Divisors.schemeWeaklyAssociatedPoints X ⊆ genericPoints X)
    (hfinite : ∀ (U : X.Opens), IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (x : X) :
    letI : Algebra (X.presheaf.stalk x) (X.totalQuotientSheaf.presheaf.stalk x) :=
      ((TopCat.Presheaf.stalkFunctor CommRingCat x).map
        X.toTotalQuotientSheaf.hom).hom.toAlgebra
    IsFractionRing (X.presheaf.stalk x) (X.totalQuotientSheaf.presheaf.stalk x) := by
  let _ : Algebra (X.presheaf.stalk x) (X.presheaf.totalQuotientPresheaf.stalk x) :=
    ((TopCat.Presheaf.stalkFunctor CommRingCat x).map
      X.presheaf.toTotalQuotientPresheaf).hom.toAlgebra
  have hfrac : IsFractionRing (X.presheaf.stalk x)
      (X.presheaf.totalQuotientPresheaf.stalk x) :=
    stalk_totalQuotientPresheaf_isFractionRing_of_weaklyAssociatedPoints_subset_genericPoints
      X hass hfinite x
  rw [stalkFunctor_map_toTotalQuotientSheaf_hom X x]
  let _ : Algebra (X.presheaf.stalk x) (X.totalQuotientSheaf.presheaf.stalk x) :=
    ((TopCat.Presheaf.stalkFunctor CommRingCat x).map X.presheaf.toTotalQuotientPresheaf ≫
      (stalkTotalQuotientSheafIso X x).hom).hom.toAlgebra
  exact IsLocalization.isLocalization_of_algEquiv _
    { (stalkTotalQuotientSheafIso X x).commRingCatIsoToRingEquiv with
      commutes' := fun _ => rfl }

end AlgebraicGeometry
