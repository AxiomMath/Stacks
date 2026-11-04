module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.BaseChangeOfToposHomExactPullback
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.LocalizationPullbackExact
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.RelocalizedMorphismComparison

/-!
# Derived base change along the localization square of Stacks 04IF

Let `f : (Sh(𝒞), 𝒪_𝒞) ⟶ (Sh(𝒟), 𝒪_𝒟)` be a morphism of ringed topoi and `G` a sheaf of sets on
`𝒟`. Localizing `f` at `G` gives the 2-commutative square of Stacks 04IF,

```
  (Sh(𝒞)/f⁻¹G, 𝒪_{f⁻¹G}) ⟶ (Sh(𝒞), 𝒪_𝒞)
           | f'                   | f
           v                      v
     (Sh(𝒟)/G, 𝒪_G)    ⟶   (Sh(𝒟), 𝒪_𝒟)
```

whose horizontal arrows are localization morphisms. Their pullbacks of sheaves of modules are
restriction to sites of elements, which is exact and keeps K-injective complexes
(`AlgebraicGeometry.RingedTopos.isKInjective_localization_pullbackModules`). So the general
criterion
`AlgebraicGeometry.RingedToposHom.TwoIso.isIso_derivedBaseChange_of_isIso_moduleBaseChange`
reduces the invertibility of the derived base change map `j_G^* Rf_* ⟶ Rf'_* j_{f⁻¹G}^*` of this
square to the invertibility of its module base change map `j_G^* f_* ⟶ f'_* j_{f⁻¹G}^*`.

## Main results

* `isIso_derivedBaseChange_localizedRingedToposSquare_of_isIso_moduleBaseChange`: the reduction.

## References

* [Stacks Project, Tag 04IF](https://stacks.math.columbia.edu/tag/04IF)
* [Stacks Project, Tag 07A7](https://stacks.math.columbia.edu/tag/07A7)
* [Stacks Project, Tag 0944](https://stacks.math.columbia.edu/tag/0944)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPullbackOfToposHom Stacks.Cohomology.DerivedPushforward

namespace AlgebraicGeometry.RingedToposHom

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] hasLeftDerivedFunctor_pullbackOnHomotopy

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})] [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)]
  (f : RingedToposHom X Y)

/-- **Derived base change along the localization square of Stacks 04IF reduces to modules.** If
the module base change map `j_G^* f_* ⟶ f'_* j_{f⁻¹G}^*` of the localization square of `f` at
`G` is invertible, then so is its derived base change map `j_G^* Rf_* E ⟶ Rf'_* j_{f⁻¹G}^* E`,
for every `E`. -/
theorem isIso_derivedBaseChange_localizedRingedToposSquare_of_isIso_moduleBaseChange
    (G : Y.Topos)
    (h : ∀ M, IsIso ((TwoIso.moduleBaseChange (f.localizedRingedToposSquare G)).app M))
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    IsIso (Stacks.CategoryTheory.BaseChange.map (derivedAdjunction f)
      (derivedAdjunction (f.localized G))
      (TwoIso.derivedPullbackSquareIso (f.localizedRingedToposSquare G)) (Iso.refl _) E) :=
  TwoIso.isIso_derivedBaseChange_of_isIso_moduleBaseChange _
    (fun I hI => by
      have hK := RingedTopos.isKInjective_localization_pullbackModules X
        (f.toToposHom.inverseImage.obj G) I hI
      exact hK) h E

end AlgebraicGeometry.RingedToposHom

end
