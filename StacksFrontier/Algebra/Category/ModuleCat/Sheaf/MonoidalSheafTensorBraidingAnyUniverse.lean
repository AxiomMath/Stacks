module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalSheafTensorBraiding

/-!
# The commutativity constraint of `Mod(O)`, for a ring sheaf in any universe

For a site `C : Type u` with `[Category.{v} C]` and a sheaf of commutative rings `R` with values
in an arbitrary universe `w`, the commutativity constraint of
`SheafOfModules.symmetricCategorySheafTensor` is
`Stacks.SheafOfModules.Tensor.sheafTensorBraiding`. This is
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/MonoidalSheafTensorBraiding.lean`, where the ring
sheaf takes values in `max u v`, with the universe of the ring sheaf free; it is stated in the
namespace `SheafOfModules.AnyUniverse`.

## Main results

* `SheafOfModules.AnyUniverse.sheafifyMod_braided`: module sheafification is braided monoidal.
* `SheafOfModules.AnyUniverse.sheafTensorIso_braiding`: `SheafOfModules.sheafTensorIso` is
  compatible with the two braidings.
* `SheafOfModules.AnyUniverse.braiding_eq_sheafTensorBraiding`: the commutativity constraint of
  `SheafOfModules.symmetricCategorySheafTensor` is
  `Stacks.SheafOfModules.Tensor.sheafTensorBraiding`.

## References

* [Stacks Project, Tag 06Y9](https://stacks.math.columbia.edu/tag/06Y9)
* [Stacks Project, Tag 0FPQ](https://stacks.math.columbia.edu/tag/0FPQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Functor.LaxMonoidal Functor.Monoidal

universe v u w

namespace SheafOfModules.AnyUniverse


variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

attribute [local instance] monoidalCategory
  symmetricCategory

/-- **Module sheafification is a braided monoidal functor.**  `Mod(O)` is the localization of
presheaves of modules at the local isomorphisms, with the localized monoidal structure, and the
localization functor of a braided monoidal category is braided
(`CategoryTheory.Localization.Monoidal`).  This re-exhibits that instance at the spelling
`Stacks.SheafOfModules.Tensor.sheafifyMod`, exactly as
`SheafOfModules.sheafification_monoidal` does for the monoidal structure. -/
@[instance_reducible]
def sheafifyMod_braided (R : Sheaf J CommRingCat.{w}) [HasWeakSheafify J AddCommGrpCat.{w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}] : (PresheafOfModules.sheafification
    (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)
    (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)).Braided := by
  letI : (J.W.inverseImage (PresheafOfModules.toPresheaf
      (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)).IsMonoidal :=
    Stacks.SheafOfModules.isMonoidal_localIso (𝒪 := R.obj)
  exact (inferInstance : (Localization.Monoidal.toMonoidalCategory
    (L := PresheafOfModules.sheafification
      (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)
      (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj))
    (W := J.W.inverseImage (PresheafOfModules.toPresheaf
      (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)) (Iso.refl _)).Braided)

attribute [local instance] sheafifyMod_braided

variable (R : Sheaf J CommRingCat.{w})
  [HasWeakSheafify J AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **The re-seating isomorphism `SheafOfModules.sheafTensorIso` is compatible with the two
braidings**: following it by the sheafification of the sectionwise symmetry is the same as
preceding it by the braiding of the localized structure.

Both are `CategoryTheory.MonoidalCategory.braiding_conj_of_laxBraided` for sheafification at
the counit isomorphisms, `sheafTensorIso` being by construction the inverse of the tensor
product of those counits followed by the monoidality isomorphism. -/
theorem sheafTensorIso_braiding
    (M N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) :
    (sheafTensorIso R M N).hom ≫
        ((PresheafOfModules.sheafification (R := Stacks.SheafOfModules.Tensor.ringSheaf (R))
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (R)).obj))).map
          (((Stacks.SheafOfModules.Tensor.presheafTensorBraiding R).hom.app
            ((forget _).obj M)).app ((forget _).obj N)) =
      (β_ M N).hom ≫ (sheafTensorIso R N M).hom := by
  simp only [sheafTensorIso, Iso.trans_hom, Iso.symm_hom, tensorIso_inv, μIso_hom,
    Category.assoc, Stacks.SheafOfModules.Tensor.presheafTensorBraiding,
    BraidedCategory.curriedBraidingNatIso, NatIso.ofComponents_hom_app]
  exact braiding_conj_of_laxBraided
      (PresheafOfModules.sheafification
        (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)
        (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj))
      (counitIso R M) (counitIso R N) (Functor.LaxBraided.braided _ _)

/-- **The commutativity constraint of the re-seated symmetric monoidal structure on `Mod(O)` is
`Stacks.SheafOfModules.Tensor.sheafTensorBraiding`.**

`SheafOfModules.symmetricCategorySheafTensor` is the symmetry of the localized structure
transported along `SheafOfModules.sheafTensorNatIso`, so its braiding is the localized braiding
conjugated by `SheafOfModules.sheafTensorIso`
(`CategoryTheory.MonoidalCategory.reseatSymmetric_braiding`); `sheafTensorIso_braiding` says
that conjugate is the sheafification of the sectionwise symmetry, which is
`sheafTensorBraiding` on the nose. -/
theorem braiding_eq_sheafTensorBraiding
    (M N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) :
    (@BraidedCategory.braiding _ _ (monoidalCategorySheafTensor R)
        (symmetricCategorySheafTensor R).toBraidedCategory M N).hom =
      ((Stacks.SheafOfModules.Tensor.sheafTensorBraiding R).hom.app M).app N :=
  (reseatSymmetric_braiding (sheafTensorNatIso R) (unitIso R) M N).trans
    (Iso.inv_comp_of_hom_comp_eq _ _ _ (sheafTensorIso_braiding R M N))

end SheafOfModules.AnyUniverse

end
