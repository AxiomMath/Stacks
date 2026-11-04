module

public import Mathlib.Algebra.Homology.Monoidal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LeftDualSheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalSheafTensor

/-!
# The strict tensor product of sheaves of modules is bilinear and commutes with colimits

`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalStrict` puts on `Mod(𝒪)` the monoidal
structure whose tensor product *is* the tensor product sheaf of [Stacks, Tag 01CA], the one the
duality statements of [Stacks, Tag 0FNY] and [Stacks, Tag 0FNZ] are stated for. That structure
is built by conjugating the localized one, so nothing is known about its interaction with sums
of morphisms or with colimits, and consequently Mathlib's monoidal structure on complexes
cannot be formed over it.

This file supplies exactly what is missing, by comparing it with
`SheafOfModules.monoidalCategorySheafTensor`, the *other* monoidal structure on `Mod(𝒪)` with
the same tensor product, for which bilinearity and the preservation of colimits are known. The
comparison is made at the level of the whiskerings: both are the sheafification of the
presheaf-level whiskering, so the two structures have the same curried tensor product, and
every property not involving the associator or the unitors transfers.

## Main definitions

* `Stacks.SheafOfModules.Strict.tensorLeftIsoSheafTensor` and
  `Stacks.SheafOfModules.Strict.tensorRightIsoSheafTensor`: tensoring on either side is the
  sheaf tensor bifunctor.
* `Stacks.SheafOfModules.Strict.monoidalCategoryCochainComplex`: **the monoidal category of
  complexes of `𝒪`-modules over the tensor product of [Stacks, Tag 01CA]**, the total complex
  of the degreewise tensor product.

## Main results

* `Stacks.SheafOfModules.Strict.whiskerLeft_eq_sheafTensor` and
  `Stacks.SheafOfModules.Strict.whiskerRight_eq_sheafTensor`: the whiskerings of the strict
  structure are the maps of the sheaf tensor bifunctor.
* `Stacks.SheafOfModules.Strict.monoidalPreadditiveRingSheaf`: the strict tensor product is
  bilinear on morphisms.
* `Stacks.SheafOfModules.Strict.preservesColimit_tensorLeft` and
  `Stacks.SheafOfModules.Strict.preservesColimit_tensorRight`: tensoring commutes with
  colimits.
* `Stacks.SheafOfModules.Strict.hasGoodTensor₁₂Tensor`,
  `Stacks.SheafOfModules.Strict.hasGoodTensorTensor₂₃` and
  `Stacks.SheafOfModules.Strict.hasTensor₄ObjExt`: the graded-object hypotheses that the
  monoidal structure on complexes consumes, all three of them instances of the previous two.

## Implementation notes

**The canonical strict structure.** The strict structure is stated for
`Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪` and the sheaf tensor product
for `Stacks.SheafOfModules.Tensor.ringSheaf R`. The two are the same sheaf of rings by `rfl`,
so the statements below use `monoidalCategory R.obj (isSheaf_ringSheaf R)` directly.

**Why the whiskerings suffice.** `CategoryTheory.GradedObject.HasGoodTensor₁₂Tensor`,
`HasGoodTensorTensor₂₃` and `HasTensor₄ObjExt` are, unfolded, assertions that a single functor
`- ⊗ Z` or `Z ⊗ -` preserves certain coproducts, and the diagrams of those coproducts involve
the tensor product only on objects, where the two structures agree definitionally. So each of
them follows from the corresponding natural isomorphism of functors, which is the identity on
objects and is natural exactly because the whiskerings agree.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 0FNZ](https://stacks.math.columbia.edu/tag/0FNZ)
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory GradedObject

noncomputable section

universe v u

namespace Stacks.SheafOfModules.Strict

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  (R : Sheaf J CommRingCat.{max u v})

/-- Sheaves of `𝒪`-modules, for the `Stacks.SheafOfModules.Tensor.ringSheaf` spelling of the
structure sheaf. -/
abbrev Mod := SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf R)

omit [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}] in
/-- The structure presheaf of rings of a sheaf of commutative rings is a sheaf, in the spelling
the strict monoidal structure takes its sheaf condition in. -/
theorem isSheaf_ringSheaf : Presheaf.IsSheaf J
    (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf R.obj) :=
  (Stacks.SheafOfModules.Tensor.ringSheaf R).property

/-- Left whiskering in the strict structure is the map of the sheaf tensor bifunctor: both are
the sheafification of the presheaf-level whiskering. -/
theorem whiskerLeft_eq_sheafTensor (D : Mod R) {A B : Mod R} (g : A ⟶ B) :
    MonoidalCategoryStruct.whiskerLeft
        (self := (monoidalCategory R.obj (isSheaf_ringSheaf R)).toMonoidalCategoryStruct) D g =
      ((Stacks.SheafOfModules.Tensor.sheafTensor R).obj D).map g :=
  (congrArg
      (fun φ => (tensorObjIso R.obj (isSheaf_ringSheaf R) D A).inv ≫ φ ≫
        (tensorObjIso R.obj (isSheaf_ringSheaf R) D B).hom)
      (@MonoidalCategory.id_tensorHom _ _
        (Stacks.SheafOfModules.monoidalCategory R.obj (isSheaf_ringSheaf R)) D _ _ g).symm).trans
    ((tensorHom_eq_sheafifyMap R.obj (isSheaf_ringSheaf R) (𝟙 D) g).trans
      (congrArg
        (Stacks.SheafOfModules.TensorSheafification.sheafify R.obj (isSheaf_ringSheaf R)).map
        (@MonoidalCategory.id_tensorHom _ _ _ ((_root_.SheafOfModules.forget _).obj D) _ _
          ((_root_.SheafOfModules.forget _).map g))))

/-- Right whiskering in the strict structure is the map of the sheaf tensor bifunctor. -/
theorem whiskerRight_eq_sheafTensor {A B : Mod R} (g : A ⟶ B) (D : Mod R) :
    MonoidalCategoryStruct.whiskerRight
        (self := (monoidalCategory R.obj (isSheaf_ringSheaf R)).toMonoidalCategoryStruct) g D =
      ((Stacks.SheafOfModules.Tensor.sheafTensor R).map g).app D :=
  (congrArg
      (fun φ => (tensorObjIso R.obj (isSheaf_ringSheaf R) A D).inv ≫ φ ≫
        (tensorObjIso R.obj (isSheaf_ringSheaf R) B D).hom)
      (@MonoidalCategory.tensorHom_id _ _
        (Stacks.SheafOfModules.monoidalCategory R.obj (isSheaf_ringSheaf R)) _ _ g D).symm).trans
    ((tensorHom_eq_sheafifyMap R.obj (isSheaf_ringSheaf R) g (𝟙 D)).trans
      (congrArg
        (Stacks.SheafOfModules.TensorSheafification.sheafify R.obj (isSheaf_ringSheaf R)).map
        (@MonoidalCategory.tensorHom_id _ _ _ _ _ ((_root_.SheafOfModules.forget _).map g)
          ((_root_.SheafOfModules.forget _).obj D))))

/-- Tensoring on the left in the strict structure is the sheaf tensor bifunctor. -/
def tensorLeftIsoSheafTensor (D : Mod R) :
    ((@curriedTensor _ _ (monoidalCategory R.obj (isSheaf_ringSheaf R))).obj D : Mod R ⥤ Mod R) ≅
      (Stacks.SheafOfModules.Tensor.sheafTensor R).obj D :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun g => by
    exact (Category.comp_id _).trans
      ((whiskerLeft_eq_sheafTensor R D g).trans (Category.id_comp _).symm))

/-- Tensoring on the right in the strict structure is the flipped sheaf tensor bifunctor. -/
def tensorRightIsoSheafTensor (D : Mod R) :
    ((@curriedTensor _ _ (monoidalCategory R.obj (isSheaf_ringSheaf R))).flip.obj D :
        Mod R ⥤ Mod R) ≅
      (Stacks.SheafOfModules.Tensor.sheafTensor R).flip.obj D :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun g => by
    exact (Category.comp_id _).trans
      ((whiskerRight_eq_sheafTensor R g D).trans (Category.id_comp _).symm))

/-- The strict tensor product is bilinear on morphisms. -/
theorem monoidalPreadditiveRingSheaf :
    @MonoidalPreadditive _ _ _ (monoidalCategory R.obj (isSheaf_ringSheaf R)) :=
  @MonoidalPreadditive.mk _ _ _ (monoidalCategory R.obj (isSheaf_ringSheaf R))
    (fun {X Y Z : Mod R} => (whiskerLeft_eq_sheafTensor R X (0 : Y ⟶ Z)).trans
      (((Stacks.SheafOfModules.Tensor.sheafTensor R).obj X).map_zero Y Z))
    (fun {X Y Z : Mod R} => (whiskerRight_eq_sheafTensor R (0 : Y ⟶ Z) X).trans
      (congrArg (fun φ => NatTrans.app φ X)
        ((Stacks.SheafOfModules.Tensor.sheafTensor R).map_zero Y Z)))
    (fun {fixed : Mod R} (source target : Mod R) (first second : source ⟶ target) =>
      ((whiskerLeft_eq_sheafTensor R fixed (first + second)).trans
        (Functor.map_add (F := (Stacks.SheafOfModules.Tensor.sheafTensor R).obj fixed))).trans
        (congrArg₂ (· + ·) (whiskerLeft_eq_sheafTensor R fixed first).symm
          (whiskerLeft_eq_sheafTensor R fixed second).symm))
    (fun {fixed : Mod R} (source target : Mod R) (first second : source ⟶ target) =>
      ((whiskerRight_eq_sheafTensor R (first + second) fixed).trans
      (congrArg (fun φ => NatTrans.app φ fixed)
        (Functor.map_add (F := Stacks.SheafOfModules.Tensor.sheafTensor R)))).trans
        (congrArg₂ (· + ·) (whiskerRight_eq_sheafTensor R first fixed).symm
          (whiskerRight_eq_sheafTensor R second fixed).symm))

/-- Tensoring on the left in the strict structure commutes with colimits. -/
theorem preservesColimit_tensorLeft {K : Type*} [Category K] (F : K ⥤ Mod R) (D : Mod R) :
    PreservesColimit F
      (((@curriedTensor _ _ (monoidalCategory R.obj (isSheaf_ringSheaf R))).obj D :
        Mod R ⥤ Mod R)) :=
  (preservesColimit_iff_of_natIso F (tensorLeftIsoSheafTensor R D)).mpr
    (_root_.SheafOfModules.preservesColimitsOfSize_sheafTensor_obj R D F)

/-- Tensoring on the right in the strict structure commutes with colimits. -/
theorem preservesColimit_tensorRight {K : Type*} [Category K] (F : K ⥤ Mod R) (D : Mod R) :
    PreservesColimit F
      (((@curriedTensor _ _ (monoidalCategory R.obj (isSheaf_ringSheaf R))).flip.obj D :
        Mod R ⥤ Mod R)) :=
  (preservesColimit_iff_of_natIso F (tensorRightIsoSheafTensor R D)).mpr
    (_root_.SheafOfModules.preservesColimitsOfSize_sheafTensor_flip_obj R D F)

/-- Tensoring on the right commutes with the coproducts of the first two graded variables. -/
theorem hasGoodTensor₁₂Tensor (X₁ X₂ X₃ : GradedObject ℤ (Mod R)) :
    letI : MonoidalCategory (Mod R) := monoidalCategory R.obj (isSheaf_ringSheaf R)
    GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ :=
  fun _ i₃ => preservesColimit_tensorRight R _ (X₃ i₃)

/-- Tensoring on the left commutes with the coproducts of the last two graded variables. -/
theorem hasGoodTensorTensor₂₃ (X₁ X₂ X₃ : GradedObject ℤ (Mod R)) :
    letI : MonoidalCategory (Mod R) := monoidalCategory R.obj (isSheaf_ringSheaf R)
    GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ :=
  fun i₁ _ => preservesColimit_tensorLeft R _ (X₁ i₁)

/-- Tensoring on the left commutes with the coproducts of a threefold graded tensor product. -/
theorem hasTensor₄ObjExt (X₁ X₂ X₃ X₄ : GradedObject ℤ (Mod R)) :
    letI : MonoidalCategory (Mod R) := monoidalCategory R.obj (isSheaf_ringSheaf R)
    GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ :=
  fun i₁ _ => preservesColimit_tensorLeft R _ (X₁ i₁)

/-- **The monoidal category of complexes of `𝒪`-modules over the tensor product of
[Stacks, Tag 01CA]**: the tensor product of two complexes is the total complex of their
degreewise tensor product, and the unit is the structure sheaf in degree zero. -/
@[instance_reducible]
def monoidalCategoryCochainComplex : MonoidalCategory (CochainComplex (Mod R) ℤ) :=
  letI : MonoidalCategory (Mod R) := monoidalCategory R.obj (isSheaf_ringSheaf R)
  letI : MonoidalPreadditive (Mod R) := monoidalPreadditiveRingSheaf R
  letI : ∀ X₁ : Mod R, PreservesColimit (Functor.empty.{0} (Mod R))
      ((curriedTensor (Mod R)).obj X₁) := fun X₁ => preservesColimit_tensorLeft R _ X₁
  letI : ∀ X₂ : Mod R, PreservesColimit (Functor.empty.{0} (Mod R))
      ((curriedTensor (Mod R)).flip.obj X₂) := fun X₂ => preservesColimit_tensorRight R _ X₂
  letI : ∀ X₁ X₂ X₃ : GradedObject ℤ (Mod R),
      GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ := hasGoodTensor₁₂Tensor R
  letI : ∀ X₁ X₂ X₃ : GradedObject ℤ (Mod R),
      GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ := hasGoodTensorTensor₂₃ R
  letI : ∀ X₁ X₂ X₃ X₄ : GradedObject ℤ (Mod R),
      GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ := hasTensor₄ObjExt R
  inferInstance

end Stacks.SheafOfModules.Strict

end

end
