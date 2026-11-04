module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.DerivedZariskiGluing
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.DerivedRestriction

/-!
# `Lf^* : D_QCoh(S) ⇄ D_Adeq(𝒪) : Rf_*` and `Rf_* Lf^* ≅ id`

Let `S` be a scheme, `(Sch/S)_τ` a chosen big site over `S` for `τ` one of the Zariski, étale,
smooth, syntomic and fppf topologies, and `f : ((Sch/S)_τ, 𝒪) ⟶ (S_Zar, 𝒪_S)` the morphism of
ringed topoi of [Stacks, Tag 070U]. [Stacks, Tag 070W] asserts that the total derived functors
`Lf^*` and `Rf_*` of [Stacks, Tag 07A6] restrict to adjoint functors

`Rf_* : D_Adeq(𝒪) ⟶ D_QCoh(S)` and `Lf^* : D_QCoh(S) ⟶ D_Adeq(𝒪)`,

and that `Rf_* Lf^* ≅ id_{D_QCoh(S)}`. This file states the remark for the derived functors of
the morphism of [Stacks, Tag 070U] themselves, with no hypothesis.

The three inputs are proved elsewhere in the library:

* `Stacks.Adequate.BigSite.isQuasicoherent_homology_derivedZariskiPushforward`: `Rf_*` carries
  `D_Adeq(𝒪)` into `D_QCoh(S)`;
* `Stacks.Adequate.BigSite.isAdequate_homology_derivedZariskiPullback`: `Lf^*` carries
  `D_QCoh(S)` into `D_Adeq(𝒪)`;
* `Stacks.Adequate.BigSite.isIso_derivedZariskiAdjunction_unit_app`: the unit of the derived
  adjunction is invertible on `D_QCoh(S)`.

## Main definitions

* `Stacks.Adequate.BigSite.derivedQuasicoherentPullback` and
  `Stacks.Adequate.BigSite.derivedAdequateDirectImage`: `Lf^*` and `Rf_*` cut down to the two
  subcategories.
* `Stacks.Adequate.BigSite.derivedQuasicoherentAdequateAdjunction`: their adjunction.
* `Stacks.Adequate.BigSite.derivedAdequateDirectImagePullbackIso`: `Rf_* Lf^* ≅ id`.

## Implementation notes

The source reduces to the Zariski topology by [Stacks, Tag 070V]. That reduction is not made
here: the landing of `Rf_*` is proved for each of the five topologies directly from the vanishing
of the higher cohomology of adequate modules over affine objects ([Stacks, Tag 06VM]), and the
assertions on `Lf^*` are checked over the affine opens of `S`, where `Lf^*` is computed on a
K-flat complex of flat quasi-coherent modules ([Stacks, Tag 06YY]) and the unit factors through
the unit on quasi-coherent modules ([Stacks, Tag 06VN]). The derived categories are the standard
models, in which the derived functors of [Stacks, Tag 07A6] are formed.

## References

* [Stacks Project, Tag 070W](https://stacks.math.columbia.edu/tag/070W)
* [Stacks Project, Tag 070U](https://stacks.math.columbia.edu/tag/070U)
* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Adequate

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.DerivedTensor.ResolutionByExtensionsByZero.instAbelian

variable {τ : CoveringTopology} {S : Scheme.{u}} (B : BigSite τ S)

attribute [local instance 2000] HasDerivedCategory.standard in
/-- `Lf^* : D_QCoh(S) ⥤ D_Adeq(𝒪)`, for the morphism `f` of [Stacks, Tag 070U]. -/
abbrev BigSite.derivedQuasicoherentPullback :
    (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent S.ringCatSheaf :
      ObjectProperty (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          S.zariskiRingedSite.toRingedTopos.O)))).FullSubcategory ⥤
      (DerivedCategoryB.derivedCategoryB (adequate.{u, u} B : ObjectProperty (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf B.ringedSite.toRingedTopos.O)))).FullSubcategory :=
  DerivedCategoryB.liftLeft B.derivedZariskiPullback
    fun K hK i ↦ B.isAdequate_homology_derivedZariskiPullback K hK i

attribute [local instance 2000] HasDerivedCategory.standard in
/-- `Rf_* : D_Adeq(𝒪) ⥤ D_QCoh(S)`, for the morphism `f` of [Stacks, Tag 070U]. -/
abbrev BigSite.derivedAdequateDirectImage :
    (DerivedCategoryB.derivedCategoryB (adequate.{u, u} B : ObjectProperty (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf B.ringedSite.toRingedTopos.O)))).FullSubcategory ⥤
      (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent S.ringCatSheaf :
        ObjectProperty (SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf
            S.zariskiRingedSite.toRingedTopos.O)))).FullSubcategory :=
  DerivedCategoryB.liftRight B.derivedZariskiPushforward
    fun K hK n ↦ B.isQuasicoherent_homology_derivedZariskiPushforward K hK n

attribute [local instance 2000] HasDerivedCategory.standard in
/-- **[Stacks, Tag 070W], the adjunction.** The morphism `f` of [Stacks, Tag 070U] induces
adjoint functors `Lf^* : D_QCoh(S) ⥤ D_Adeq(𝒪)` and `Rf_* : D_Adeq(𝒪) ⥤ D_QCoh(S)`: the total
derived functors of [Stacks, Tag 07A6] preserve the two subcategories, and their adjunction
restricts. -/
@[stacks 070W "the adjunction Lf^* ⊣ Rf_* between D_QCoh(S) and D_Adeq(O), for the derived
functors of the morphism of Tag 070U on a chosen big site, with no hypothesis"]
def BigSite.derivedQuasicoherentAdequateAdjunction :
    B.derivedQuasicoherentPullback ⊣ B.derivedAdequateDirectImage :=
  DerivedCategoryB.restrictAdjunction _ _ _ _ B.derivedZariskiAdjunction

attribute [local instance 2000] HasDerivedCategory.standard in
/-- **[Stacks, Tag 070W], `Rf_* Lf^* ≅ id_{D_QCoh(S)}`.** The unit of the derived adjunction
is invertible at every complex with quasi-coherent cohomology. -/
@[stacks 070W "Rf_* Lf^* ≅ id on D_QCoh(S), for the derived functors of the morphism of
Tag 070U on a chosen big site"]
def BigSite.derivedAdequateDirectImagePullbackIso :
    B.derivedQuasicoherentPullback ⋙ B.derivedAdequateDirectImage ≅ 𝟭 _ :=
  DerivedCategoryB.restrictAdjunctionUnitIso _ _ _ _ B.derivedZariskiAdjunction
    fun K hK ↦ B.isIso_derivedZariskiAdjunction_unit_app K hK

end Stacks.Adequate

end
