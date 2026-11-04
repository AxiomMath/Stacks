module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.Resolution
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.TriangulatedSubcategory
import StacksCore.Tactic.StacksAttribute

/-!
# The derived category is the localization of the K-flat complexes

Let `(C, O)` be a ringed site. The K-flat complexes of `O`-modules form a full
pre-triangulated subcategory of the homotopy category `K(Mod(O))` (Stacks 07A3), every object
of `K(Mod(O))` receives a quasi-isomorphism from one of them (Stacks 06YS), and the
quasi-isomorphisms are a saturated multiplicative system compatible with the triangulated
structure. By Stacks 0GSL the inclusion therefore induces an equivalence from the
localization of the K-flat complexes at their quasi-isomorphisms onto the derived category
`D(Mod(O))`.

Equivalently, and this is the form used downstream: the composite of the inclusion with the
localization functor `DerivedCategory.Qh` is itself a localization functor, for the
quasi-isomorphisms between K-flat complexes. That is what allows a bifunctor defined on K-flat
complexes to be descended to `D(Mod(O))`, which is how the derived tensor product of Stacks
06YU is built.

## Main results

* `Stacks.SheafOfModules.kFlatLocalizer_hasLeftResolutions`: every object of the homotopy
  category admits a resolution by a K-flat one.
* `Stacks.SheafOfModules.kFlatLocalizer_isLocalizedEquivalence`: the inclusion of the K-flat
  complexes is a localized equivalence.
* `Stacks.SheafOfModules.kFlatQ_isLocalization`: the derived category is the localization of
  the K-flat complexes at the quasi-isomorphisms between them.

## Main definitions

* `Stacks.SheafOfModules.kFlatQ`: the functor from K-flat complexes to the derived category.

## Implementation notes

The universes are all equal, inherited from `Stacks.SheafOfModules.exists_kFlat_quasiIso`
(the existence of K-flat resolutions), which is in turn inherited from Stacks 077J
and 03EV. Nothing else in this development needs that restriction.

Stacks 0GSL is proved in `StacksFrontier.CategoryTheory.Triangulated.Localization`, as
`CategoryTheory.ObjectProperty`'s
`isSaturated_and_isCompatibleWithTriangulation_inverseImage_ι_and_isLocalizedEquivalence`,
and the passage from a localized equivalence to a localization functor is Mathlib's
`CategoryTheory.LocalizerMorphism.IsLocalizedEquivalence.isLocalization`.

## References

* [Stacks Project, Tag 0GSL](https://stacks.math.columbia.edu/tag/0GSL)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 07A3](https://stacks.math.columbia.edu/tag/07A3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe c u d

namespace Stacks.SheafOfModules

variable (X : AlgebraicGeometry.RingedSite.{c, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} X.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- Every object of the homotopy category receives a quasi-isomorphism from a K-flat one.
This is Stacks 06YS in the form the localization theory consumes. -/
theorem kFlatLocalizer_hasLeftResolutions :
    (kFlatLocalizer.{c, u, u} X.O).HasLeftResolutions := by
  intro Y
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective Y
  obtain ⟨P, p, hP, hp⟩ := exists_kFlat_quasiIso X K
  exact ⟨{ X₁ := ⟨(HomotopyCategory.quotient _ _).obj P, hP⟩
           w := (HomotopyCategory.quotient _ _).map p
           hw := (HomotopyCategory.quotient_map_mem_quasiIso_iff p).2 hp }⟩

open ObjectProperty in
/-- The inclusion of the K-flat complexes into the homotopy category is a localized
equivalence: it induces an equivalence between the localization of the K-flat complexes at
their quasi-isomorphisms and the derived category. This is Stacks 0GSL applied to the K-flat
subcategory, whose hypotheses are Stacks 07A3 and Stacks 06YS. -/
theorem kFlatLocalizer_isLocalizedEquivalence :
    (kFlatLocalizer.{c, u, u} X.O).IsLocalizedEquivalence := by
  obtain ⟨hsat, hcompat⟩ :=
    quasiIso_isSaturated_and_isCompatibleWithTriangulation.{c, u, u} X.O
  let _ := hcompat
  exact (isSaturated_and_isCompatibleWithTriangulation_inverseImage_ι_and_isLocalizedEquivalence
    (kFlatObjects.{c, u, u} X.O)
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ))
    hsat).2.2 (kFlatLocalizer_hasLeftResolutions X)

variable [HasDerivedCategory.{d}
  (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O))]

/-- The functor from the K-flat complexes, as a subcategory of the homotopy category, to the
derived category. -/
abbrev kFlatQ :
    (kFlatObjects.{c, u, u} X.O).FullSubcategory ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O)) :=
  (kFlatObjects X.O).ι ⋙ DerivedCategory.Qh

/-- The derived category of sheaves of modules on a ringed site is the localization of the
K-flat complexes at the quasi-isomorphisms between K-flat complexes. -/
theorem kFlatQ_isLocalization :
    (kFlatQ.{c, u, d} X).IsLocalization (kFlatQuasiIso.{c, u, u} X.O) := by
  have := kFlatLocalizer_isLocalizedEquivalence X
  exact LocalizerMorphism.IsLocalizedEquivalence.isLocalization
    (kFlatLocalizer X.O) DerivedCategory.Qh

end Stacks.SheafOfModules

end
