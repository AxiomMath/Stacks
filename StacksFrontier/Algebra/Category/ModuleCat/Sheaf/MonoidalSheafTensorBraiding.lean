module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalSheafTensor
public import StacksFrontier.CategoryTheory.Monoidal.ReseatConstraints
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.TensorSymmetry

/-!
# The commutativity constraint of `Mod(O)` is the braiding of the sheafified tensor product

`SheafOfModules.monoidalCategorySheafTensor` re-seats the symmetric monoidal structure of
`Mod(O)` on `Stacks.SheafOfModules.Tensor.sheafTensor`, the bifunctor
`(ℱ, 𝒢) ↦ (ℱ ⊗_{pre} 𝒢)^#`, so that its tensor product *is* that bifunctor.  Its
commutativity constraint is then the braiding of the localized structure conjugated by the
re-seating isomorphism (`CategoryTheory.MonoidalCategory.reseatSymmetric_braiding`), and
nothing said what that conjugate is.

`Stacks.SheafOfModules.Tensor.sheafTensorBraiding` is the other, independently constructed,
symmetry of the same bifunctor: the sectionwise symmetry of the tensor product of modules,
whiskered through sheafification and the forgetful functor.  **The two agree**, and this file
proves it.

The identification is what lets a statement about the Koszul symmetry of total tensor
complexes — which is built from `sheafTensorBraiding` — be read as a statement about the
commutativity constraint `β_` of `Comp(Mod(O))`, and conversely.

## Main definitions

* `SheafOfModules.sheafifyMod_braided`: module sheafification is a *braided* monoidal functor,
  not merely a monoidal one.  This is Mathlib's braided structure on a localized monoidal
  category, re-exhibited at the spelling `Stacks.SheafOfModules.Tensor.sheafifyMod`.

## Main results

* `CategoryTheory.MonoidalCategory.braiding_conj_of_laxBraided`: a lax braided functor carries
  the braiding of its source to the braiding of its target, read through a pair of
  isomorphisms identifying the images with given objects.
* `SheafOfModules.sheafTensorIso_braiding`: the re-seating isomorphism
  `SheafOfModules.sheafTensorIso` is compatible with the two braidings.
* `SheafOfModules.braiding_eq_sheafTensorBraiding`: **the commutativity constraint of
  `SheafOfModules.symmetricCategorySheafTensor` is
  `Stacks.SheafOfModules.Tensor.sheafTensorBraiding`.**

## Implementation notes

The braided-functor condition of `Mathlib.CategoryTheory.Monoidal.Braided.Basic` is
`CategoryTheory.Functor.LaxBraided.braided`, whose `μ` is the one of the `LaxBraided`
instance's own `LaxMonoidal` field.  `braiding_conj_of_laxBraided` therefore takes that
condition as a *hypothesis* rather than as an instance: in the application below the ambient
`LaxMonoidal` instance is `SheafOfModules.sheafification_monoidal` and the braided one is
`SheafOfModules.sheafifyMod_braided`, which are definitionally equal but not syntactically so,
and a `rewrite` keyed on the instance of the class does not fire across that gap while an
`exact` does.

`Mod(O)` carries two monoidal structures here — the localized one of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/Monoidal.lean` and the re-seated one — so the
final statement names the second by `@`-application, as everything in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/MonoidalSheafTensor.lean` does.

## References

* [Stacks Project, Tag 06Y9](https://stacks.math.columbia.edu/tag/06Y9)
* [Stacks Project, Tag 0FPQ](https://stacks.math.columbia.edu/tag/0FPQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Functor.LaxMonoidal Functor.Monoidal

universe v u

namespace CategoryTheory

/-- If `i.hom ≫ q = p` then `i.inv ≫ p = q`: cancelling an isomorphism off the front of an
equation. -/
theorem Iso.inv_comp_of_hom_comp_eq {E : Type*} [Category E] {a b c : E} (i : a ≅ b)
    (p : a ⟶ c) (q : b ⟶ c) (h : i.hom ≫ q = p) : i.inv ≫ p = q := by
  rw [← h, i.inv_hom_id_assoc]

namespace MonoidalCategory

/-- **A lax braided functor conjugates the braiding of its source to the braiding of its
target**, read through a pair of isomorphisms `cM`, `cN` identifying the images of the two
objects with given objects of the target.

The braided condition itself is the hypothesis `h`; see the implementation notes of this
module for why it is not taken as an instance. -/
theorem braiding_conj_of_laxBraided {A B : Type*} [Category A] [Category B]
    [MonoidalCategory A] [MonoidalCategory B] [BraidedCategory A] [BraidedCategory B]
    (F : A ⥤ B) [F.LaxMonoidal] {M N : B} {P Q : A}
    (cM : F.obj P ≅ M) (cN : F.obj Q ≅ N)
    (h : μ F P Q ≫ F.map (β_ P Q).hom = (β_ (F.obj P) (F.obj Q)).hom ≫ μ F Q P) :
    (cM.inv ⊗ₘ cN.inv) ≫ μ F P Q ≫ F.map (β_ P Q).hom =
      (β_ M N).hom ≫ (cN.inv ⊗ₘ cM.inv) ≫ μ F Q P := by
  rw [h, BraidedCategory.braiding_naturality_assoc]

end MonoidalCategory

end CategoryTheory

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{max u v})
  [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

attribute [local instance] monoidalCategory
  symmetricCategory

/-- **Module sheafification is a braided monoidal functor.**  `Mod(O)` is the localization of
presheaves of modules at the local isomorphisms, with the localized monoidal structure, and the
localization functor of a braided monoidal category is braided
(`CategoryTheory.Localization.Monoidal`).  This re-exhibits that instance at the spelling
`Stacks.SheafOfModules.Tensor.sheafifyMod`, exactly as
`SheafOfModules.sheafification_monoidal` does for the monoidal structure. -/
@[instance_reducible]
def sheafifyMod_braided : (PresheafOfModules.sheafification
    (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)
    (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)).Braided := by
  let : (J.W.inverseImage (PresheafOfModules.toPresheaf
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

/-- **The re-seating isomorphism `SheafOfModules.sheafTensorIso` is compatible with the two
braidings**: following it by the sheafification of the sectionwise symmetry is the same as
preceding it by the braiding of the localized structure.

Both are `CategoryTheory.MonoidalCategory.braiding_conj_of_laxBraided` for sheafification at
the counit isomorphisms, `sheafTensorIso` being by construction the inverse of the tensor
product of those counits followed by the monoidality isomorphism. -/
theorem sheafTensorIso_braiding
    (M N : SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf R)) :
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
    (M N : SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf R)) :
    (@BraidedCategory.braiding _ _ (monoidalCategorySheafTensor R)
        (symmetricCategorySheafTensor R).toBraidedCategory M N).hom =
      ((Stacks.SheafOfModules.Tensor.sheafTensorBraiding R).hom.app M).app N :=
  (reseatSymmetric_braiding (sheafTensorNatIso R) (unitIso R) M N).trans
    (Iso.inv_comp_of_hom_comp_eq _ _ _ (sheafTensorIso_braiding R M N))

end SheafOfModules

end
