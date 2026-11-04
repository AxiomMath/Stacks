module

public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.CategoryTheory.Sites.Monoidal
public import StacksFrontier.CategoryTheory.Sites.CharacterTwistInvertible

/-!
# Tensoring with the character twist is an auto-equivalence of abelian sheaves

Let `W` be a torsor under a group `G` over the final object of a site, in the sense of
`CategoryTheory.IsTorsorObject`, and let `χ : G → ℤˣ` be a character. The twist `ℤ(χ)` is its
own inverse for the tensor product of abelian sheaves, `ℤ ≅ ℤ(χ) ⊗_ℤ ℤ(χ)`, which is
`CategoryTheory.IsTorsorObject.constantSheafIsoTwistTensorSelf`. Consequently `F ↦ F ⊗_ℤ ℤ(χ)` is
an auto-equivalence of the category of abelian sheaves; in particular it is exact and preserves
injective objects.

## Main definitions

* `CategoryTheory.characterTwistTensorFunctor` is `F ↦ F ⊗_ℤ ℤ(χ)` as a functor on abelian
  sheaves; on objects it is `CategoryTheory.characterTwistTensor`.
* `AddCommGrpCat.presheafTensorRight` is the objectwise tensor product over `ℤ` with a fixed
  abelian presheaf on the right, as a functor on abelian presheaves.
* `CategoryTheory.IsTorsorObject.characterTwistTensorEquivalence` is the auto-equivalence.

## Main results

* `CategoryTheory.IsTorsorObject.isEquivalence_characterTwistTensorFunctor`: **tensoring with
  `ℤ(χ)` is an auto-equivalence of abelian sheaves**, its own quasi-inverse.
* `CategoryTheory.IsTorsorObject.preservesFiniteLimits_characterTwistTensorFunctor` and
  `CategoryTheory.IsTorsorObject.preservesFiniteColimits_characterTwistTensorFunctor`:
  **tensoring with `ℤ(χ)` is exact.**
* `CategoryTheory.IsTorsorObject.preservesInjectiveObjects_characterTwistTensorFunctor`:
  **tensoring with `ℤ(χ)` preserves injective objects.**
* `AddCommGrpCat.isMonoidal_W`: the morphisms of abelian presheaves inverted by sheafification
  form a monoidal class of morphisms.

## Implementation notes

The associativity and unit constraints are not built by hand. The objectwise tensor product over
`ℤ` of abelian presheaves is isomorphic, by `AddCommGrpCat.presheafTensorIso`, to the tensor
product of the monoidal structure on presheaves induced by the transported monoidal structure
`AddCommGrpCat.monoidalCategory` on abelian groups; that monoidal structure is closed and
braided, so `CategoryTheory.GrothendieckTopology.W.monoidal` applies and
`CategoryTheory.Sheaf.monoidalCategory` equips abelian sheaves with the localized monoidal
structure, associator, unitors and coherence included. What remains is bookkeeping: tensoring
with `ℤ(χ)` on the right is identified with the localized tensor product by
`CategoryTheory.tensorRightTwistIso`, the isomorphism `ℤ ≅ ℤ(χ) ⊗_ℤ ℤ(χ)` is read as an
isomorphism of the unit object with the tensor square, and `CategoryTheory.Equivalence.mk` turns
the resulting isomorphism `𝟭 ≅ (- ⊗ ℤ(χ)) ⋙ (- ⊗ ℤ(χ))` into an equivalence with no further
coherence check.

`AddCommGrpCat.monoidalCategory` is not an instance — the cartesian monoidal structure on
abelian groups is — so the monoidal structures used here are installed as local instances and
none of the exported statements mentions them. In particular
`CategoryTheory.characterTwistTensorFunctor` is defined from `AddCommGrpCat.presheafTensor`,
not from the monoidal product, and agrees with `CategoryTheory.characterTwistTensor` on objects
by definition.

## References

* [Stacks Project, Tag 0727](https://stacks.math.columbia.edu/tag/0727)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open CategoryTheory.Enriched.FunctorCategory

universe w u₁ u

/-! ### The monoidal structure on abelian groups and on abelian presheaves -/

local instance : MonoidalCategory AddCommGrpCat.{u + 1} := AddCommGrpCat.monoidalCategory.{u + 1}

local instance : (AddCommGrpCat.uliftIntEquivalence.{u + 1}).inverse.Monoidal := by
  change (Monoidal.equivalenceTransported
    (AddCommGrpCat.uliftIntEquivalence.{u + 1})).inverse.Monoidal
  infer_instance

local instance : MonoidalClosed AddCommGrpCat.{u + 1} :=
  MonoidalClosed.ofEquiv (AddCommGrpCat.uliftIntEquivalence.{u + 1}).inverse
    (AddCommGrpCat.uliftIntEquivalence.{u + 1}).symm.toAdjunction

local instance : BraidedCategory AddCommGrpCat.{u + 1} := by
  change BraidedCategory (Monoidal.Transported (AddCommGrpCat.uliftIntEquivalence.{u + 1}))
  infer_instance

namespace AddCommGrpCat

/-! ### Functoriality of the objectwise tensor product of abelian presheaves -/

section Functoriality

variable {C : Type u₁} [Category.{u + 1} C]

/-- The objectwise tensor product of morphisms of abelian presheaves respects composition. -/
lemma presheafTensorMap_comp {F₁ F₂ F₃ G₁ G₂ G₃ : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}}
    (f : F₁ ⟶ F₂) (f' : F₂ ⟶ F₃) (g : G₁ ⟶ G₂) (g' : G₂ ⟶ G₃) :
    presheafTensorMap f g ≫ presheafTensorMap f' g' = presheafTensorMap (f ≫ f') (g ≫ g') := by
  unfold presheafTensorMap
  rw [← MonoidalCategory.tensorHom_comp_tensorHom]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- The objectwise tensor product of two identities is the identity. -/
lemma presheafTensorMap_id (F G : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    presheafTensorMap (𝟙 F) (𝟙 G) = 𝟙 (presheafTensor F G) := by
  unfold presheafTensorMap
  rw [MonoidalCategory.id_tensorHom_id, Category.id_comp, Iso.hom_inv_id]

/-- The comparison of the objectwise tensor product of abelian presheaves with the monoidal
product is natural in the left-hand factor. -/
lemma presheafTensorIso_inv_naturality_left {F₁ F₂ X : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}}
    (f : F₁ ⟶ F₂) :
    f ▷ X ≫ (presheafTensorIso F₂ X).inv =
      (presheafTensorIso F₁ X).inv ≫ presheafTensorMap f (𝟙 X) := by
  unfold presheafTensorMap
  rw [MonoidalCategory.tensorHom_id, Iso.inv_hom_id_assoc]

/-- **Tensoring objectwise over `ℤ` with a fixed abelian presheaf on the right, as a functor.**
On objects it is `AddCommGrpCat.presheafTensor`. -/
def presheafTensorRight (X : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    (Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}) ⥤ Cᵒᵖ ⥤ AddCommGrpCat.{u + 1} where
  obj F := presheafTensor F X
  map f := presheafTensorMap f (𝟙 X)
  map_id F := presheafTensorMap_id F X
  map_comp f g := by rw [presheafTensorMap_comp, Category.comp_id]

/-- The functor `presheafTensorRight X` on objects. -/
@[simp]
lemma presheafTensorRight_obj (X F : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    (presheafTensorRight X).obj F = presheafTensor F X := rfl

/-- The functor `presheafTensorRight X` on morphisms. -/
@[simp]
lemma presheafTensorRight_map (X : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    {F₁ F₂ : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}} (f : F₁ ⟶ F₂) :
    (presheafTensorRight X).map f = presheafTensorMap f (𝟙 X) := rfl

end Functoriality

/-! ### Sheafification is monoidal -/

/-- **The morphisms of abelian presheaves inverted by sheafification form a monoidal class.**
This is `CategoryTheory.GrothendieckTopology.W.monoidal` for the closed braided monoidal
structure on abelian groups. -/
theorem isMonoidal_W {C : Type u₁} [Category.{u + 1} C] [UnivLE.{max u₁ (u + 1), u + 1}]
    (J : GrothendieckTopology C) : (J.W (A := AddCommGrpCat.{u + 1})).IsMonoidal := by
  let _ : HasLimitsOfSize.{max u₁ (u + 1), max u₁ (u + 1)} AddCommGrpCat.{u + 1} :=
    AddCommGrpCat.hasLimitsOfSize
  let _ : EnrichedOrdinaryCategory AddCommGrpCat.{u + 1} AddCommGrpCat.{u + 1} := inferInstance
  let _ : ∀ F₁ F₂ : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      HasFunctorEnrichedHom AddCommGrpCat.{u + 1} F₁ F₂ := by
    intro F₁ F₂ V
    infer_instance
  let _ : ∀ F₁ F₂ : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}, HasEnrichedHom AddCommGrpCat.{u + 1} F₁ F₂ := by
    intro F₁ F₂
    infer_instance
  exact GrothendieckTopology.W.monoidal

end AddCommGrpCat

namespace CategoryTheory

variable {C : Type u₁} [Category.{u + 1} C]
  {W : C} {G : Type w} [Group G] {act : G →* Aut W} {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{u + 1}] (χ : G →* ℤˣ)

/-! ### Tensoring with the twist, as a functor -/

/-- **Tensoring an abelian sheaf with the character twist `ℤ(χ)`, as a functor.** On objects it
is `CategoryTheory.characterTwistTensor`: the sheafification of the objectwise tensor product
over `ℤ` with the twist presheaf. -/
def characterTwistTensorFunctor (act : G →* Aut W) (χ : G →* ℤˣ) (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u + 1}] :
    Sheaf J AddCommGrpCat.{u + 1} ⥤ Sheaf J AddCommGrpCat.{u + 1} :=
  sheafToPresheaf J AddCommGrpCat.{u + 1} ⋙
    AddCommGrpCat.presheafTensorRight (characterTwistPresheaf W act χ) ⋙
      presheafToSheaf J AddCommGrpCat.{u + 1}

/-- Tensoring with the twist, on objects, is `characterTwistTensor`. -/
@[simp]
lemma characterTwistTensorFunctor_obj (F : Sheaf J AddCommGrpCat.{u + 1}) :
    (characterTwistTensorFunctor act χ J).obj F = characterTwistTensor F.obj act χ J := rfl

/-- Tensoring with the twist, on morphisms, is the sheafification of the objectwise tensor
product with the identity of the twist presheaf. -/
lemma characterTwistTensorFunctor_map {F₁ F₂ : Sheaf J AddCommGrpCat.{u + 1}} (f : F₁ ⟶ F₂) :
    (characterTwistTensorFunctor act χ J).map f =
      (presheafToSheaf J AddCommGrpCat.{u + 1}).map
        (AddCommGrpCat.presheafTensorMap
          ((sheafToPresheaf J AddCommGrpCat.{u + 1}).map f)
          (𝟙 (characterTwistPresheaf W act χ))) := rfl

/-- Sheafifying the objectwise tensor product with a morphism of abelian presheaves inserted in
the right-hand factor is natural in the left-hand factor. -/
private lemma map_presheafTensorMap_naturality_left {X Y : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}}
    (s : X ⟶ Y) {F₁ F₂ : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}} (f : F₁ ⟶ F₂) :
    (presheafToSheaf J AddCommGrpCat.{u + 1}).map
          (AddCommGrpCat.presheafTensorMap f (𝟙 X)) ≫
        (presheafToSheaf J AddCommGrpCat.{u + 1}).map
          (AddCommGrpCat.presheafTensorMap (𝟙 F₂) s) =
      (presheafToSheaf J AddCommGrpCat.{u + 1}).map
            (AddCommGrpCat.presheafTensorMap (𝟙 F₁) s) ≫
        (presheafToSheaf J AddCommGrpCat.{u + 1}).map
          (AddCommGrpCat.presheafTensorMap f (𝟙 Y)) := by
  rw [← Functor.map_comp, ← Functor.map_comp, AddCommGrpCat.presheafTensorMap_comp,
    AddCommGrpCat.presheafTensorMap_comp]
  simp only [Category.comp_id, Category.id_comp]

/-! ### The localized monoidal structure on abelian sheaves -/

section Monoidal

variable [UnivLE.{max u₁ (u + 1), u + 1}]

local instance : (J.W (A := AddCommGrpCat.{u + 1})).IsMonoidal := AddCommGrpCat.isMonoidal_W J

local instance : MonoidalCategory (Sheaf J AddCommGrpCat.{u + 1}) :=
  Sheaf.monoidalCategory J AddCommGrpCat.{u + 1}

/-- Sheafification does not change a sheaf. -/
private def sheafifySheafIso :
    sheafToPresheaf J AddCommGrpCat.{u + 1} ⋙ presheafToSheaf J AddCommGrpCat.{u + 1} ≅
      𝟭 (Sheaf J AddCommGrpCat.{u + 1}) :=
  asIso (sheafificationAdjunction J AddCommGrpCat.{u + 1}).counit

/-- The comparison of a tensor product of sheafifications with the sheafification of the
objectwise tensor product is natural in the left-hand factor. -/
private lemma sheafifyTensorRight_naturality (X : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    {F₁ F₂ : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}} (f : F₁ ⟶ F₂) :
    (presheafToSheaf J AddCommGrpCat.{u + 1}).map f ▷
          (presheafToSheaf J AddCommGrpCat.{u + 1}).obj X ≫
        ((Functor.Monoidal.μIso (presheafToSheaf J AddCommGrpCat.{u + 1}) F₂ X).hom ≫
          (presheafToSheaf J AddCommGrpCat.{u + 1}).map
            (AddCommGrpCat.presheafTensorIso F₂ X).inv) =
      ((Functor.Monoidal.μIso (presheafToSheaf J AddCommGrpCat.{u + 1}) F₁ X).hom ≫
            (presheafToSheaf J AddCommGrpCat.{u + 1}).map
              (AddCommGrpCat.presheafTensorIso F₁ X).inv) ≫
        (presheafToSheaf J AddCommGrpCat.{u + 1}).map
          (AddCommGrpCat.presheafTensorMap f (𝟙 X)) := by
  simp only [Functor.Monoidal.μIso_hom, Category.assoc]
  rw [Functor.LaxMonoidal.μ_natural_left_assoc, ← Functor.map_comp, ← Functor.map_comp,
    AddCommGrpCat.presheafTensorIso_inv_naturality_left]

/-- **Tensoring two sheafifications is the sheafification of the objectwise tensor product**,
naturally in the left-hand factor. -/
private def sheafifyTensorRightIso (X : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    presheafToSheaf J AddCommGrpCat.{u + 1} ⋙
        MonoidalCategory.tensorRight ((presheafToSheaf J AddCommGrpCat.{u + 1}).obj X) ≅
      AddCommGrpCat.presheafTensorRight X ⋙ presheafToSheaf J AddCommGrpCat.{u + 1} :=
  NatIso.ofComponents
    (fun F => Functor.Monoidal.μIso (presheafToSheaf J AddCommGrpCat.{u + 1}) F X ≪≫
      (presheafToSheaf J AddCommGrpCat.{u + 1}).mapIso
        (AddCommGrpCat.presheafTensorIso F X).symm)
    (fun f => sheafifyTensorRight_naturality X f)

/-- Tensoring with the twist presheaf and sheafifying inverts the sheafification of the twist. -/
private lemma isIso_map_presheafTensorMap_toSheafify (F : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    IsIso ((presheafToSheaf J AddCommGrpCat.{u + 1}).map
      (AddCommGrpCat.presheafTensorMap (𝟙 F)
        (toSheafify J (characterTwistPresheaf W act χ)))) :=
  (J.W_iff _).1 (AddCommGrpCat.W_presheafTensorMap_id J F (J.W_toSheafify _))

/-- **The tensor product with the twist may be formed before or after sheafifying the twist**,
naturally in the other factor. -/
private def presheafTensorRightSheafifyTwistIso :
    AddCommGrpCat.presheafTensorRight (characterTwistPresheaf W act χ) ⋙
        presheafToSheaf J AddCommGrpCat.{u + 1} ≅
      AddCommGrpCat.presheafTensorRight (characterTwist W act χ J).obj ⋙
        presheafToSheaf J AddCommGrpCat.{u + 1} :=
  NatIso.ofComponents
    (fun F => @asIso _ _ _ _ _ (isIso_map_presheafTensorMap_toSheafify (J := J) χ F))
    (fun f => map_presheafTensorMap_naturality_left
      (toSheafify J (characterTwistPresheaf W act χ)) f)

/-- **Tensoring a sheafification with the twist `ℤ(χ)` is the sheafification of the objectwise
tensor product with the twist presheaf.** -/
private def sheafifyTensorTwistIso :
    presheafToSheaf J AddCommGrpCat.{u + 1} ⋙
        MonoidalCategory.tensorRight (characterTwist W act χ J) ≅
      AddCommGrpCat.presheafTensorRight (characterTwistPresheaf W act χ) ⋙
        presheafToSheaf J AddCommGrpCat.{u + 1} :=
  Functor.isoWhiskerLeft (presheafToSheaf J AddCommGrpCat.{u + 1})
      ((MonoidalCategory.tensoringRight (Sheaf J AddCommGrpCat.{u + 1})).mapIso
        (sheafifySheafIso.app (characterTwist W act χ J)).symm) ≪≫
    sheafifyTensorRightIso (characterTwist W act χ J).obj ≪≫
      (presheafTensorRightSheafifyTwistIso χ).symm

/-- **Tensoring with the twist `ℤ(χ)` is the monoidal product with `ℤ(χ)`.** -/
private def tensorRightTwistIso :
    MonoidalCategory.tensorRight (characterTwist W act χ J) ≅
      characterTwistTensorFunctor act χ J :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight (sheafifySheafIso (J := J)).symm
        (MonoidalCategory.tensorRight (characterTwist W act χ J)) ≪≫
      Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (sheafToPresheaf J AddCommGrpCat.{u + 1})
          (sheafifyTensorTwistIso χ)

variable [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]

namespace IsTorsorObject

variable {T : C} (hT : IsTerminal T) (h : IsTorsorObject act J)

include hT h

/-- **The unit object of abelian sheaves is the tensor square of the twist.** This is
`CategoryTheory.IsTorsorObject.constantSheafIsoTwistTensorSelf`, read in the monoidal structure
on abelian sheaves. -/
private def unitIsoTwistTensorSelf :
    𝟙_ (Sheaf J AddCommGrpCat.{u + 1}) ≅
      characterTwist W act χ J ⊗ characterTwist W act χ J :=
  h.constantSheafIsoTwistTensorSelf χ hT ≪≫
    ((sheafifyTensorTwistIso χ).app (characterTwist W act χ J).obj).symm ≪≫
      MonoidalCategory.whiskerRightIso (sheafifySheafIso.app (characterTwist W act χ J))
        (characterTwist W act χ J)

/-- Tensoring twice with the twist is the identity, because `ℤ(χ)` is its own inverse. -/
private def unitIsoTensorRightSquare :
    𝟭 (Sheaf J AddCommGrpCat.{u + 1}) ≅
      MonoidalCategory.tensorRight (characterTwist W act χ J) ⋙
        MonoidalCategory.tensorRight (characterTwist W act χ J) :=
  (MonoidalCategory.rightUnitorNatIso (Sheaf J AddCommGrpCat.{u + 1})).symm ≪≫
    (MonoidalCategory.tensoringRight (Sheaf J AddCommGrpCat.{u + 1})).mapIso
        (h.unitIsoTwistTensorSelf χ hT) ≪≫
      MonoidalCategory.tensorRightTensor (characterTwist W act χ J) (characterTwist W act χ J)

/-- The monoidal product with the twist is an auto-equivalence of abelian sheaves. -/
private def equivalenceTensorRight :
    Sheaf J AddCommGrpCat.{u + 1} ≌ Sheaf J AddCommGrpCat.{u + 1} :=
  Equivalence.mk (MonoidalCategory.tensorRight (characterTwist W act χ J))
    (MonoidalCategory.tensorRight (characterTwist W act χ J))
    (h.unitIsoTensorRightSquare χ hT) (h.unitIsoTensorRightSquare χ hT).symm

/-- **Tensoring with the character twist is an auto-equivalence of abelian sheaves**, its own
quasi-inverse: `ℤ(χ) ⊗_ℤ ℤ(χ)` is `ℤ`. -/
theorem isEquivalence_characterTwistTensorFunctor :
    (characterTwistTensorFunctor act χ J).IsEquivalence := by
  have : (MonoidalCategory.tensorRight (characterTwist W act χ J)).IsEquivalence :=
    (h.equivalenceTensorRight χ hT).isEquivalence_functor
  exact Functor.isEquivalence_of_iso (tensorRightTwistIso χ)

/-- **Tensoring with the character twist, as an auto-equivalence of abelian sheaves.** -/
def characterTwistTensorEquivalence :
    Sheaf J AddCommGrpCat.{u + 1} ≌ Sheaf J AddCommGrpCat.{u + 1} :=
  haveI := h.isEquivalence_characterTwistTensorFunctor χ hT
  (characterTwistTensorFunctor act χ J).asEquivalence

/-- The functor of the auto-equivalence is tensoring with the twist. -/
@[simp]
lemma characterTwistTensorEquivalence_functor :
    (h.characterTwistTensorEquivalence χ hT).functor = characterTwistTensorFunctor act χ J := rfl

/-- **Tensoring with the character twist is left exact.** -/
theorem preservesFiniteLimits_characterTwistTensorFunctor :
    PreservesFiniteLimits (characterTwistTensorFunctor act χ J) :=
  have := h.isEquivalence_characterTwistTensorFunctor χ hT
  inferInstance

/-- **Tensoring with the character twist is right exact.** -/
theorem preservesFiniteColimits_characterTwistTensorFunctor :
    PreservesFiniteColimits (characterTwistTensorFunctor act χ J) :=
  have := h.isEquivalence_characterTwistTensorFunctor χ hT
  inferInstance

/-- **Tensoring with the character twist preserves injective objects.** -/
theorem preservesInjectiveObjects_characterTwistTensorFunctor :
    (characterTwistTensorFunctor act χ J).PreservesInjectiveObjects :=
  have := h.isEquivalence_characterTwistTensorFunctor χ hT
  inferInstance

end IsTorsorObject

end Monoidal

end CategoryTheory

end
