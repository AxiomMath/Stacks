module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CanonicalFrobeniusAdditivity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ClosedImmersionModuleBaseChange

/-!
# Inverse image of `j_! j^{-1} G`, compatibly with the counit

Let `g : Y' ⟶ Y` be a morphism of schemes, `Y = j(V) ⊔ i(W)` and `Y' = j'(V') ⊔ i'(W')`
decompositions into an open and a complementary closed subscheme with `g(V') ⊆ V` and
`g(W') ⊆ W`.  For a sheaf `G` of `Λ`-modules on `Y_étale`, the inverse image `g^{-1}` of the
short exact sequence `0 → j_! j^{-1} G → G → i_* i^{-1} G → 0` and the sequence
`0 → j'_! j'^{-1} g^{-1} G → g^{-1} G → i'_* i'^{-1} g^{-1} G → 0` have the same middle term,
and each first map is killed by the other second map (the relevant restrictions vanish).  Hence
`g^{-1}(j_! j^{-1} G) ≅ j'_! j'^{-1}(g^{-1} G)`, compatibly with the counits.

## Main definitions

* `Stacks.EtaleCohomology.inverseImageExtensionByZeroCounitIso`: the isomorphism
  `g^{-1}(j_! j^{-1} G) ≅ j'_! j'^{-1}(g^{-1} G)`.

## Main results

* `Stacks.EtaleCohomology.inverseImageExtensionByZeroCounitIso_hom_comp_counit`: this
  isomorphism followed by the counit of `j'` is `g^{-1}` of the counit of `j`.

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG), Step 9.
* [Stacks Project, Tag 095L](https://stacks.math.columbia.edu/tag/095L).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u r

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [Ring Λ] {Y Y' W W' V V' : Scheme.{u}} (g : Y' ⟶ Y)
  (i : W ⟶ Y) [IsClosedImmersion i] (j : V ⟶ Y) [IsOpenImmersion j]
  (hij : Set.range j.base = (Set.range i.base)ᶜ)
  (i' : W' ⟶ Y') [IsClosedImmersion i'] (j' : V' ⟶ Y') [IsOpenImmersion j']
  (hij' : Set.range j'.base = (Set.range i'.base)ᶜ)
  (gW : W' ⟶ W) (hW : i' ≫ g = gW ≫ i) (gV : V' ⟶ V) (hV : j' ≫ g = gV ≫ j)
  (G : EtaleModules.{u, r} Λ Y)

/-- The inverse image under `g` of the short complex `j_! j^{-1} G → G → i_* i^{-1} G`. -/
abbrev inverseImageOpenClosedShortComplex :
    ShortComplex (EtaleModules.{u, r} Λ Y') :=
  ShortComplex.mk
    ((etaleModuleInverseImage.{u, r} Λ g).map
      ((etaleModuleExtensionByZeroAdj.{u, r} Λ j).counit.app G))
    ((etaleModuleInverseImage.{u, r} Λ g).map ((etaleModuleInverseImageAdj.{u, r} Λ i).unit.app G))
    (by rw [← Functor.map_comp,
      etaleModuleExtensionByZero_counit_comp_inverseImage_unit Λ i j hij G, Functor.map_zero])

include hij in
/-- The inverse image under `g` of the sequence `0 → j_! j^{-1} G → G → i_* i^{-1} G → 0` is short
exact. -/
lemma inverseImageOpenClosedShortComplex_shortExact :
    (inverseImageOpenClosedShortComplex Λ g i j hij G).ShortExact := by
  have := etaleModuleInverseImage_preservesFiniteLimits.{u, r} Λ g
  have := etaleModuleInverseImage_preservesFiniteColimits.{u, r} Λ g
  obtain ⟨_, hS⟩ := shortExact_etaleModuleExtensionByZero_directImage.{u, r} Λ i j hij G
  exact hS.map_of_exact (etaleModuleInverseImage.{u, r} Λ g)

omit [IsClosedImmersion i] in
include hij hV in
/-- The counit `j'_! j'^{-1} g^{-1} G → g^{-1} G` composed with `g^{-1}` of the unit
`G → i_* i^{-1} G` is zero. -/
lemma counit_comp_inverseImage_map_unit_eq_zero :
    (etaleModuleExtensionByZeroAdj.{u, r} Λ j').counit.app
        ((etaleModuleInverseImage.{u, r} Λ g).obj G) ≫
      (etaleModuleInverseImage.{u, r} Λ g).map
        ((etaleModuleInverseImageAdj.{u, r} Λ i).unit.app G) =
    0 := by
  apply ((etaleModuleExtensionByZeroAdj.{u, r} Λ j').homEquiv _ _).injective
  refine IsZero.eq_of_tgt ?_ _ _
  refine (IsZero.of_iso ?_ ((etaleModuleInverseImageRestrictionIso.{u, r} Λ j').app _).symm)
  refine (IsZero.of_iso ?_ ((etaleModuleInverseImageCompIso.{u, r} Λ j' g).app _).symm)
  rw [hV]
  refine (IsZero.of_iso ?_ ((etaleModuleInverseImageCompIso.{u, r} Λ gV j).app _))
  exact (etaleModuleInverseImage.{u, r} Λ gV).map_isZero
    (isZero_etaleModuleInverseImage_directImage Λ i j hij _)

omit [IsClosedImmersion i] [IsClosedImmersion i'] in
include hij hW in
/-- `g^{-1}` of the counit `j_! j^{-1} G → G` composed with the unit
`g^{-1} G → i'_* i'^{-1} g^{-1} G` is zero. -/
lemma inverseImage_map_counit_comp_unit_eq_zero :
    (etaleModuleInverseImage.{u, r} Λ g).map
        ((etaleModuleExtensionByZeroAdj.{u, r} Λ j).counit.app G) ≫
      (etaleModuleInverseImageAdj.{u, r} Λ i').unit.app
        ((etaleModuleInverseImage.{u, r} Λ g).obj G) =
    0 := by
  apply ((etaleModuleInverseImageAdj.{u, r} Λ i').homEquiv _ _).symm.injective
  refine IsZero.eq_of_src ?_ _ _
  refine (IsZero.of_iso ?_ ((etaleModuleInverseImageCompIso.{u, r} Λ i' g).app _).symm)
  rw [hW]
  refine (IsZero.of_iso ?_ ((etaleModuleInverseImageCompIso.{u, r} Λ gW i).app _))
  exact (etaleModuleInverseImage.{u, r} Λ gW).map_isZero
    (isZero_etaleModuleInverseImage_extensionByZero Λ i j hij _)

include hij hij' hW hV in
/-- The isomorphism `g^{-1}(j_! j^{-1} G) ≅ j'_! j'^{-1}(g^{-1} G)` compatible with the maps to
`g^{-1} G` given by `g^{-1}` of the counit of `j` and by the counit of `j'`. -/
def inverseImageExtensionByZeroCounitIso :
    (etaleModuleInverseImage.{u, r} Λ g).obj
        ((etaleModuleExtensionByZero.{u, r} Λ j).obj ((etaleModuleRestriction.{u, r} Λ j).obj G)) ≅
      (etaleModuleExtensionByZero.{u, r} Λ j').obj
        ((etaleModuleRestriction.{u, r} Λ j').obj
          ((etaleModuleInverseImage.{u, r} Λ g).obj G)) := by
  have hS₂ := inverseImageOpenClosedShortComplex_shortExact Λ g i j hij G
  have hS₁ : (ShortComplex.mk ((etaleModuleExtensionByZeroAdj.{u, r} Λ j').counit.app
      ((etaleModuleInverseImage.{u, r} Λ g).obj G))
      ((etaleModuleInverseImageAdj.{u, r} Λ i').unit.app
        ((etaleModuleInverseImage.{u, r} Λ g).obj G))
      (etaleModuleExtensionByZero_counit_comp_inverseImage_unit Λ i' j' hij' _)).ShortExact :=
    (shortExact_etaleModuleExtensionByZero_directImage.{u, r} Λ i' j' hij'
      ((etaleModuleInverseImage.{u, r} Λ g).obj G)).choose_spec
  haveI := hS₁.mono_f
  haveI := hS₂.mono_f
  exact {
    hom := hS₁.exact.lift _ (inverseImage_map_counit_comp_unit_eq_zero Λ g i j hij i' gW hW G)
    inv := hS₂.exact.lift _ (counit_comp_inverseImage_map_unit_eq_zero Λ g i j hij j' gV hV G)
    hom_inv_id := by
      rw [← cancel_mono ((inverseImageOpenClosedShortComplex Λ g i j hij G).f), Category.assoc,
        hS₂.exact.lift_f, Category.id_comp]
      exact hS₁.exact.lift_f _ _
    inv_hom_id := by
      rw [← cancel_mono ((etaleModuleExtensionByZeroAdj.{u, r} Λ j').counit.app
        ((etaleModuleInverseImage.{u, r} Λ g).obj G)), Category.assoc, Category.id_comp]
      rw [show (hS₁.exact.lift _
          (inverseImage_map_counit_comp_unit_eq_zero Λ g i j hij i' gW hW G) ≫
          (etaleModuleExtensionByZeroAdj.{u, r} Λ j').counit.app
            ((etaleModuleInverseImage.{u, r} Λ g).obj G)) = _ from hS₁.exact.lift_f _ _]
      exact hS₂.exact.lift_f _ _ }

/-- The isomorphism `inverseImageExtensionByZeroCounitIso` followed by the counit of `j'` is
`g^{-1}` of the counit of `j`. -/
theorem inverseImageExtensionByZeroCounitIso_hom_comp_counit :
    (inverseImageExtensionByZeroCounitIso Λ g i j hij i' j' hij' gW hW gV hV G).hom ≫
        (etaleModuleExtensionByZeroAdj.{u, r} Λ j').counit.app
          ((etaleModuleInverseImage.{u, r} Λ g).obj G) =
      (etaleModuleInverseImage.{u, r} Λ g).map
        ((etaleModuleExtensionByZeroAdj.{u, r} Λ j).counit.app G) := by
  have hS₁ : (ShortComplex.mk ((etaleModuleExtensionByZeroAdj.{u, r} Λ j').counit.app
      ((etaleModuleInverseImage.{u, r} Λ g).obj G))
      ((etaleModuleInverseImageAdj.{u, r} Λ i').unit.app
        ((etaleModuleInverseImage.{u, r} Λ g).obj G))
      (etaleModuleExtensionByZero_counit_comp_inverseImage_unit Λ i' j' hij' _)).ShortExact :=
    (shortExact_etaleModuleExtensionByZero_directImage.{u, r} Λ i' j' hij'
      ((etaleModuleInverseImage.{u, r} Λ g).obj G)).choose_spec
  have := hS₁.mono_f
  exact hS₁.exact.lift_f _ _

end Stacks.EtaleCohomology

end
