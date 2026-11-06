module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalStrict
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LeftDualSheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerMultiplication
public import StacksCore.Tactic.StacksAttribute

/-!
# Coherence for the tensor product sheaf of sheaves of modules

Let `O` be a sheaf of commutative rings on a site `(C, J)`. The tensor product sheaf
`((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} (J := J)
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat
          RingCat) hO⟩).obj M).obj N` of Tag 01CA is the sheafification
  of the objectwise tensor
product of the underlying presheaves of modules. Its structural morphisms are built the same way:
the unit constraints are the sheafified presheaf unitors followed by the counit of sheafification,
the symmetry constraint is the sheafified presheaf braiding, and the associativity constraint is
the sheafified presheaf associator, conjugated by the comparison isomorphisms which Tag 05NA
provides.

This file proves that these hand-built morphisms **are** the structural morphisms of the monoidal
structure `Stacks.SheafOfModules.Strict.monoidalCategory`, hence that they satisfy the pentagon,
triangle, unit and hexagon identities. Those identities are what Tag 01CU needs in order to
normalise the multiplication on the tensor powers of an invertible sheaf: the left unit
normalisation needs `tensorSheafLeftUnitor_tensor`, associativity of the multiplication needs
`tensorSheafAssociator_pentagon`, and the commutativity constraint in off-diagonal degrees needs
`tensorSheafBraiding_hexagon_forward`. Those normalisations are *not* proved here: each is an
induction over the comparison
`Stacks.SheafOfModules.TensorPower.powFunctorIsoTensorRight` which consumes one of these
identities at every step. What is proved here is the identities themselves, together with
`TensorPower.tensorPowerMulIso_zero_left_eq`, which performs the `powAdd` half of the left unit
normalisation and so leaves exactly one statement about `powFunctorIsoTensorRight` outstanding.

## Main definitions

* `Stacks.SheafOfModules.tensorSheafLeftUnitor`: the left unit constraint of the tensor product
  sheaf. The right one is `Stacks.SheafOfModules.tensorLeftFunctorObjUnitIso`, which
  `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerConstraints` already supplies, and is
  used here under that name.
* `Stacks.SheafOfModules.tensorSheafAssocLeft` and
  `Stacks.SheafOfModules.tensorSheafAssocRight`: the two comparison isomorphisms of Tag 05NA
  which identify the sheafification of a triple presheaf tensor product with the two nested
  tensor product sheaves.
* `Stacks.SheafOfModules.tensorSheafAssociator`: **the associativity constraint of the tensor
  product sheaf**, the sheafified presheaf associator read between those two comparisons.
* The comparisons use `Stacks.SheafOfModules.tensorObjIso` and the canonical unit
  `Stacks.SheafOfModules.TensorSheafification.toSheafify` directly, without local forwarding
  definitions for either datum.

## Main results

* `Stacks.SheafOfModules.Strict_associator_eq`,
  `Stacks.SheafOfModules.Strict_leftUnitor_eq`, `Stacks.SheafOfModules.Strict_rightUnitor_eq`,
  `Stacks.SheafOfModules.Strict_braiding_eq` and `Stacks.SheafOfModules.Strict_tensorHom_eq`:
  **the structural morphisms of `Strict.monoidalCategory` are exactly the sheafification-built
  ones.** The same statements with the structure active as an instance are
  `Stacks.SheafOfModules.associator_eq_tensorSheafAssociator` and its companions.
* `Stacks.SheafOfModules.tensorSheafAssociator_pentagon`: **the pentagon identity.**
* `Stacks.SheafOfModules.tensorSheafAssociator_triangle`: **the triangle identity.**
* `Stacks.SheafOfModules.tensorSheafLeftUnitor_tensor` and
  `Stacks.SheafOfModules.tensorSheafRightUnitor_tensor`: the unit constraint of a tensor product
  sheaf, read through the associativity constraint.
* `Stacks.SheafOfModules.tensorSheafBraiding_hexagon_forward` and
  `Stacks.SheafOfModules.tensorSheafBraiding_hexagon_reverse`: **the hexagon identities.**
* `Stacks.SheafOfModules.tensorSheafLeftUnitor_unit` and
  `Stacks.SheafOfModules.tensorSheafLeftUnitor_whiskerLeft`: the two unit coherences which are the
  base cases, at the exponents `0` and `1`, of the left unit normalisation of Tag 01CU.
* `Stacks.SheafOfModules.TensorPower.tensorPowerMulIso_zero_left_eq`: multiplication by the
  zeroth tensor power on the left is `powFunctorIsoTensorRight` evaluated at the structure sheaf.
  This reduces the left unit normalisation of Tag 01CU to a single statement about
  `powFunctorIsoTensorRight`; see its docstring.
* `Stacks.SheafOfModules.assoc_key` is the computational heart: the sheafified presheaf
  associator, read between the two Tag 05NA comparisons, is the associator of the localized
  monoidal structure conjugated by `Stacks.SheafOfModules.tensorObjIso`.

## Implementation notes

What is *forced*. Nothing here is a choice: the tensor product sheaf, its unit and its structural
morphisms are all prescribed by Tag 01CA, and the monoidal structure they are compared against is
the one `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Monoidal` obtains by localizing the
objectwise monoidal structure on presheaves of modules along sheafification. The universes are
those of that file: the site `C : Type u` with `Category.{v} C` is arbitrary, while the ring sheaf
and the modules share the single universe `w`, because Mathlib's monoidal structure on presheaves
of modules is stated only in that form. **Nothing is narrowed**; in particular no
`GrothendieckTopology.HasSheafCompose` hypothesis is used. That hypothesis appears in the
`variable` blocks of `Monoidal` and `MonoidalStrict`, but Lean's variable-inclusion heuristic
never attaches it to the declarations this file consumes — `Strict.monoidalCategory`,
`Strict.braidedCategory` and the `Strict.*_eq` lemmas all have exactly the hypotheses used here.

What is *chosen*: the **spelling discipline**. The ring presheaf indexing a presheaf of modules is
written `Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O` by `Monoidal` and
`(Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj` by everything built on the
  tensor product sheaf. The two
are definitionally equal, but `structureSheaf` is a plain definition, so a composite mixing the
two spellings is not type-correct at `implicit` transparency and both `rw` and `simp` silently
refuse to fire on it. Every statement in this file is therefore written in a single spelling, and
each result imported from `CategoryTheory.Localization.Monoidal` is restated in that spelling by
an `exact`, which checks the definitional equality once. So
`Stacks.SheafOfModules.sheafifyValIso`,
`Stacks.SheafOfModules.sheafifyTensorIso` and `Stacks.SheafOfModules.sheafifyUnitIso` are used
here directly, with no restating definitions standing in front of them. The same discipline
dictates `comp_assoc₃` (a reassociation stated in an abstract category so that it can be applied
by `exact`).

## References

* [The Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [The Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
* [The Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public section

open CategoryTheory MonoidalCategory Localization

universe v u w

namespace Stacks.SheafOfModules

attribute [local implicit_reducible]
  TensorSheafification.structureSheaf TensorSheafification.sheafify Tensor.ringSheaf

attribute [local instance] monoidalCategoryPresheafOfModules symmetricCategoryPresheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

/-- Reassociation of a four-fold composite. It is stated in an abstract category so that it can
be applied by `exact` to composites whose intermediate objects agree only up to unfolding the
structure sheaf, which blocks `rw` and `simp`. -/
theorem comp_assoc₃ {D : Type*} [Category D] {W X Y Z Z' : D}
    (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z) (d : Z ⟶ Z') :
    (a ≫ b ≫ c) ≫ d = a ≫ b ≫ c ≫ d := by
  simp

/-- The left unit constraint of the tensor product sheaf. -/
noncomputable def tensorSheafLeftUnitor
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂
      CommRingCat RingCat) (hO)⟩).obj ((SheafOfModules.unit
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)))).obj (M)) ≅ M :=
  (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).mapIso (λ_ M.val) ≪≫
    sheafifyValIso O hO M

/-- The comparison identifying the sheafification of `(M ⊗ N) ⊗ P` with
`(M ⊗_O N) ⊗_O P`. -/
noncomputable def tensorSheafAssocLeft
    (M N P : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj ((M.val ⊗ N.val) ⊗ P.val) ≅
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂
        CommRingCat RingCat) (hO)⟩).obj ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} (J := J)
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat
          RingCat) hO⟩).obj M).obj N))).obj (P)) :=
  @asIso _ _ _ _ ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map
      (Stacks.SheafOfModules.TensorSheafification.toSheafify O hO (M.val ⊗ N.val) ▷ P.val))
    (Stacks.SheafOfModules.TensorSheafification.isIso_sheafify_map_whiskerRight O hO
      (Stacks.SheafOfModules.TensorSheafification.toSheafify O hO (M.val ⊗ N.val)) P.val
      (Stacks.SheafOfModules.TensorSheafification.isIso_sheafify_map_toSheafify O hO (M.val ⊗
        N.val)))

set_option maxHeartbeats 1600000 in
/-- The comparison identifying the sheafification of `M ⊗ (N ⊗ P)` with
`M ⊗_O (N ⊗_O P)`. -/
noncomputable def tensorSheafAssocRight
    (M N P : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj (M.val ⊗ N.val ⊗ P.val) ≅
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂
        CommRingCat RingCat) (hO)⟩).obj (M)).obj ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w,
        w} (J := J)
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).obj N).obj P))) :=
  @asIso _ _ _ _ ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map
      (M.val ◁ Stacks.SheafOfModules.TensorSheafification.toSheafify O hO (N.val ⊗ P.val)))
    (Stacks.SheafOfModules.TensorSheafification.isIso_sheafify_map_whiskerLeft O hO M.val
      (Stacks.SheafOfModules.TensorSheafification.toSheafify O hO (N.val ⊗ P.val))
      (Stacks.SheafOfModules.TensorSheafification.isIso_sheafify_map_toSheafify O hO (N.val ⊗
        P.val)))

/-- The associativity constraint of the tensor product sheaf. -/
noncomputable def tensorSheafAssociator
    (M N P : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂
      CommRingCat RingCat) (hO)⟩).obj ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} (J := J)
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).obj M).obj N))).obj (P)) ≅
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂
        CommRingCat RingCat) (hO)⟩).obj (M)).obj ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w,
        w} (J := J)
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).obj N).obj P))) :=
  (tensorSheafAssocLeft O hO M N P).symm ≪≫
    (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).mapIso (α_ M.val N.val P.val) ≪≫
      tensorSheafAssocRight O hO M N P

section Localized

attribute [local instance] monoidalCategory

theorem tensorObjIso_hom_eq
    (F G : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (tensorObjIso O hO F G).hom =
      ((sheafifyValIso O hO F).inv ⊗ₘ (sheafifyValIso O hO G).inv) ≫
        (sheafifyTensorIso O hO F.val G.val).hom :=
  rfl

theorem tensorObjIso_inv_eq
    (F G : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (tensorObjIso O hO F G).inv =
      (sheafifyTensorIso O hO F.val G.val).inv ≫
        ((sheafifyValIso O hO F).hom ⊗ₘ (sheafifyValIso O hO G).hom) :=
  rfl

/-- Sheafification inverts its own unit, the inverse being the counit. -/
theorem sheafify_map_toSheafify_eq
    (Q : PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj)
      :
    (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map
      (Stacks.SheafOfModules.TensorSheafification.toSheafify O hO Q) =
      (sheafifyValIso O hO ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj
        Q)).inv :=
  (Iso.comp_hom_eq_id (sheafifyValIso O hO ((Stacks.SheafOfModules.TensorSheafification.sheafify
    O hO).obj Q))).mp
    ((Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction O hO).left_triangle_components
      Q)

theorem sheafifyTensorIso_hom_natural_left
    {P₁ P₂ : PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO).obj} (f : P₁ ⟶ P₂)
    (Q : PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj)
      :
    (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map f ▷
      (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj Q ≫
        (sheafifyTensorIso O hO P₂ Q).hom =
      (sheafifyTensorIso O hO P₁ Q).hom ≫ (Stacks.SheafOfModules.TensorSheafification.sheafify O
        hO).map (f ▷ Q) :=
  Localization.Monoidal.μ_natural_left (sheafifyFunctor O hO) (localIso (J := J) O)
    (sheafifyUnitIso O hO) f Q

theorem sheafifyTensorIso_inv_natural_left
    {P₁ P₂ : PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO).obj} (f : P₁ ⟶ P₂)
    (Q : PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj)
      :
    (sheafifyTensorIso O hO P₁ Q).inv ≫
        (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map f ▷
          (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj Q =
      (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map (f ▷ Q) ≫
        (sheafifyTensorIso O hO P₂ Q).inv :=
  Localization.Monoidal.μ_inv_natural_left (sheafifyFunctor O hO) (localIso (J := J) O)
    (sheafifyUnitIso O hO) f Q

theorem sheafifyTensorIso_hom_natural_right
    (P : PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj)
    {Q₁ Q₂ : PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO).obj} (g : Q₁ ⟶ Q₂) :
    (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj P ◁
      (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map g ≫
        (sheafifyTensorIso O hO P Q₂).hom =
      (sheafifyTensorIso O hO P Q₁).hom ≫ (Stacks.SheafOfModules.TensorSheafification.sheafify O
        hO).map (P ◁ g) :=
  Localization.Monoidal.μ_natural_right (sheafifyFunctor O hO) (localIso (J := J) O)
    (sheafifyUnitIso O hO) P g

theorem sheafifyTensorIso_hom_natural
    {P₁ P₂ Q₁ Q₂ : PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf
      O hO).obj}
    (f : P₁ ⟶ P₂) (g : Q₁ ⟶ Q₂) :
    ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map f ⊗ₘ
      (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map g) ≫
        (sheafifyTensorIso O hO P₂ Q₂).hom =
      (sheafifyTensorIso O hO P₁ Q₁).hom ≫ (Stacks.SheafOfModules.TensorSheafification.sheafify O
        hO).map (f ⊗ₘ g) := by
  rw [MonoidalCategory.tensorHom_def, Category.assoc,
    sheafifyTensorIso_hom_natural_right, ← Category.assoc,
    sheafifyTensorIso_hom_natural_left, Category.assoc,
    ← (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map_comp, ←
      MonoidalCategory.tensorHom_def]

/-- The left unitor of the localized monoidal structure, at a sheafified presheaf. -/
theorem localized_leftUnitor_hom
    (A : PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj)
      :
    (λ_ ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj A)).hom =
      (sheafifyUnitIso O hO).inv ▷ ((Stacks.SheafOfModules.TensorSheafification.sheafify O
        hO).obj A) ≫
        (sheafifyTensorIso O hO
            (𝟙_ (PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
              hO).obj)) A).hom ≫
          (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map (λ_ A).hom :=
  Localization.Monoidal.leftUnitor_hom_app (sheafifyFunctor O hO) (localIso (J := J) O)
    (sheafifyUnitIso O hO) A

/-- The right unitor of the localized monoidal structure, at a sheafified presheaf. -/
theorem localized_rightUnitor_hom
    (A : PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj)
      :
    (ρ_ ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj A)).hom =
      ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj A) ◁
          (sheafifyUnitIso O hO).inv ≫
        (sheafifyTensorIso O hO A
            (𝟙_ (PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
              hO).obj))).hom ≫
          (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map (ρ_ A).hom :=
  Localization.Monoidal.rightUnitor_hom_app (sheafifyFunctor O hO) (localIso (J := J) O)
    (sheafifyUnitIso O hO) A

/-- The associator of the localized monoidal structure, at sheafified presheaves. -/
theorem localized_associator_hom
    (A B D : PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO).obj) :
    (α_ ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj A)
      ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj B)
        ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj D)).hom =
      (sheafifyTensorIso O hO A B).hom ▷ ((Stacks.SheafOfModules.TensorSheafification.sheafify O
        hO).obj D) ≫
        (sheafifyTensorIso O hO (A ⊗ B) D).hom ≫
          (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map (α_ A B D).hom ≫
            (sheafifyTensorIso O hO A (B ⊗ D)).inv ≫
              ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj A) ◁
                (sheafifyTensorIso O hO B D).inv := by
  have h : (α_ ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj A)
    ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj B)
        ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj D)).hom =
      ((sheafifyTensorIso O hO A B).hom ⊗ₘ 𝟙
        ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj D)) ≫
        (sheafifyTensorIso O hO (A ⊗ B) D).hom ≫
          (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map (α_ A B D).hom ≫
            (sheafifyTensorIso O hO A (B ⊗ D)).inv ≫
              (𝟙 ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj A) ⊗ₘ
                (sheafifyTensorIso O hO B D).inv) :=
    Localization.Monoidal.associator_hom_app (sheafifyFunctor O hO) (localIso (J := J) O)
      (sheafifyUnitIso O hO) A B D
  rw [h, MonoidalCategory.tensorHom_id, MonoidalCategory.id_tensorHom]

section Braided

attribute [local instance] braidedCategory

/-- The braiding of the localized monoidal structure, at sheafified presheaves. -/
theorem localized_braiding_hom
    (A B : PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO).obj) :
    (β_ ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj A)
      ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj B)).hom =
      (sheafifyTensorIso O hO A B).hom ≫
        (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map (β_ A B).hom ≫
          (sheafifyTensorIso O hO B A).inv :=
  Localization.Monoidal.β_hom_app (sheafifyFunctor O hO) (localIso (J := J) O)
    (sheafifyUnitIso O hO) A B

end Braided


/-- **Step one of the associator comparison.** -/
theorem assoc_step_left
    (M N P : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map (TensorSheafification.toSheafify O hO (M.val ⊗
      N.val) ▷ P.val) ≫
        (tensorObjIso O hO
          ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj (M.val ⊗ N.val)) P).inv =
      (sheafifyTensorIso O hO (M.val ⊗ N.val) P.val).inv ≫
        ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj (M.val ⊗ N.val) ◁
          (sheafifyValIso O hO P).hom) := by
  let presheaf := M.val ⊗ N.val
  let unit : presheaf ⟶ ((TensorSheafification.sheafify O hO).obj presheaf).val :=
    TensorSheafification.toSheafify O hO presheaf
  let comparison : (TensorSheafification.sheafify O hO).obj presheaf ⊗ P ≅
      (TensorSheafification.sheafify O hO).obj
        (((TensorSheafification.sheafify O hO).obj presheaf).val ⊗ P.val) :=
    tensorObjIso O hO ((TensorSheafification.sheafify O hO).obj presheaf) P
  have comparisonInv : comparison.inv =
      (sheafifyTensorIso O hO ((TensorSheafification.sheafify O hO).obj presheaf).val P.val).inv ≫
        ((sheafifyValIso O hO ((TensorSheafification.sheafify O hO).obj presheaf)).hom ⊗ₘ
          (sheafifyValIso O hO P).hom) :=
    tensorObjIso_inv_eq O hO _ P
  have naturality := sheafifyTensorIso_inv_natural_left O hO unit P.val
  have unitImage : (TensorSheafification.sheafify O hO).map unit =
      (sheafifyValIso O hO ((TensorSheafification.sheafify O hO).obj presheaf)).inv :=
    sheafify_map_toSheafify_eq O hO presheaf
  change (TensorSheafification.sheafify O hO).map (unit ▷ P.val) ≫ comparison.inv = _
  rw [comparisonInv, ← Category.assoc, ← naturality, unitImage, MonoidalCategory.tensorHom_def]
  simp only [Category.assoc, MonoidalCategory.inv_hom_whiskerRight_assoc]
  rfl


/-- **Step two of the associator comparison.** -/
theorem assoc_step_mid
    (M N P : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj (M.val ⊗ N.val) ◁
      (sheafifyValIso O hO P).hom) ≫
        ((tensorObjIso O hO M N).inv ▷ P) ≫ (α_ M N P).hom ≫
          (M ◁ (tensorObjIso O hO N P).hom) ≫
            (tensorObjIso O hO M
              ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj (N.val ⊗ P.val))).hom
                =
      ((sheafifyTensorIso O hO M.val N.val).inv ▷
            (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj P.val) ≫
        (α_ ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj M.val)
          ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj N.val)
            ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj P.val)).hom ≫
          ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj M.val ◁
            (sheafifyTensorIso O hO N.val P.val).hom) ≫
            (sheafifyTensorIso O hO M.val (N.val ⊗ P.val)).hom ≫
              (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map
                (M.val ◁ TensorSheafification.toSheafify O hO (N.val ⊗ P.val)) := by
  let leftPresheaf := M.val ⊗ N.val
  let rightPresheaf := N.val ⊗ P.val
  let unit : rightPresheaf ⟶ ((TensorSheafification.sheafify O hO).obj rightPresheaf).val :=
    TensorSheafification.toSheafify O hO rightPresheaf
  let leftComparison : M ⊗ N ≅ (TensorSheafification.sheafify O hO).obj leftPresheaf :=
    tensorObjIso O hO M N
  let rightComparison : N ⊗ P ≅ (TensorSheafification.sheafify O hO).obj rightPresheaf :=
    tensorObjIso O hO N P
  let endComparison : M ⊗ (TensorSheafification.sheafify O hO).obj rightPresheaf ≅
      (TensorSheafification.sheafify O hO).obj
        (M.val ⊗ ((TensorSheafification.sheafify O hO).obj rightPresheaf).val) :=
    tensorObjIso O hO M ((TensorSheafification.sheafify O hO).obj rightPresheaf)
  have leftInv : leftComparison.inv = (sheafifyTensorIso O hO M.val N.val).inv ≫
      ((sheafifyValIso O hO M).hom ⊗ₘ (sheafifyValIso O hO N).hom) :=
    tensorObjIso_inv_eq O hO M N
  have rightHom : rightComparison.hom =
      ((sheafifyValIso O hO N).inv ⊗ₘ (sheafifyValIso O hO P).inv) ≫
        (sheafifyTensorIso O hO N.val P.val).hom := tensorObjIso_hom_eq O hO N P
  have endHom : endComparison.hom =
      ((sheafifyValIso O hO M).inv ⊗ₘ
        (sheafifyValIso O hO ((TensorSheafification.sheafify O hO).obj rightPresheaf)).inv) ≫
      (sheafifyTensorIso O hO M.val
        ((TensorSheafification.sheafify O hO).obj rightPresheaf).val).hom :=
    tensorObjIso_hom_eq O hO M _
  have unitImage : (TensorSheafification.sheafify O hO).map unit =
      (sheafifyValIso O hO ((TensorSheafification.sheafify O hO).obj rightPresheaf)).inv :=
    sheafify_map_toSheafify_eq O hO rightPresheaf
  have naturality := sheafifyTensorIso_hom_natural_right O hO M.val unit
  change ((TensorSheafification.sheafify O hO).obj leftPresheaf ◁ (sheafifyValIso O hO P).hom) ≫
      (leftComparison.inv ▷ P) ≫ (α_ M N P).hom ≫ (M ◁ rightComparison.hom) ≫ endComparison.hom =
    ((sheafifyTensorIso O hO M.val N.val).inv ▷ (TensorSheafification.sheafify O hO).obj P.val) ≫
      (α_ ((TensorSheafification.sheafify O hO).obj M.val)
        ((TensorSheafification.sheafify O hO).obj N.val)
        ((TensorSheafification.sheafify O hO).obj P.val)).hom ≫
      ((TensorSheafification.sheafify O hO).obj M.val ◁ (sheafifyTensorIso O hO N.val P.val).hom) ≫
      (sheafifyTensorIso O hO M.val rightPresheaf).hom ≫
      (TensorSheafification.sheafify O hO).map (M.val ◁ unit)
  rw [leftInv, rightHom, endHom, ← unitImage, ← naturality]
  simp only [MonoidalCategory.tensorHom_def, Category.assoc,
    MonoidalCategory.comp_whiskerRight, MonoidalCategory.whiskerLeft_comp,
    MonoidalCategory.whisker_exchange_assoc,
    MonoidalCategory.associator_naturality_left_assoc,
    MonoidalCategory.associator_naturality_middle_assoc,
    MonoidalCategory.associator_naturality_right_assoc]
  simp only [← MonoidalCategory.whiskerLeft_comp_assoc,
    MonoidalCategory.hom_inv_whiskerRight_assoc, Iso.hom_inv_id,
    MonoidalCategory.whiskerLeft_id, Category.id_comp]


/-- **The associator comparison.** The sheafification-built associativity constraint of the
tensor product sheaf is the associator of the localized monoidal structure, conjugated by
`Stacks.SheafOfModules.tensorObjIso`. -/
theorem assoc_key
    (M N P : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map (TensorSheafification.toSheafify O hO (M.val ⊗
      N.val) ▷ P.val) ≫
        (tensorObjIso O hO
            ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj (M.val ⊗ N.val)) P).inv
              ≫
          ((tensorObjIso O hO M N).inv ▷ P) ≫ (α_ M N P).hom ≫
            (M ◁ (tensorObjIso O hO N P).hom) ≫
              (tensorObjIso O hO M
                ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj (N.val ⊗
                  P.val))).hom =
      (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map (α_ M.val N.val P.val).hom ≫
        (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map
          (M.val ◁ TensorSheafification.toSheafify O hO (N.val ⊗ P.val)) := by
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) (assoc_step_left O hO M N P)).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) (assoc_step_mid O hO M N P)).trans ?_
  rw [localized_associator_hom]
  simp only [Category.assoc, MonoidalCategory.inv_hom_whiskerRight_assoc,
    Iso.inv_hom_id_assoc, MonoidalCategory.whiskerLeft_inv_hom_assoc]
  exact (sheafifyTensorIso O hO (M.val ⊗ N.val) P.val).inv_hom_id_assoc _


section AssociatorData

set_option maxHeartbeats 1600000 in
/-- **The associativity constraint of the tensor product sheaf is the associator of the strict
monoidal structure.** -/
theorem Strict_associator_eq
    (M N P : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    MonoidalCategoryStruct.associator (self := Strict.monoidalCategoryStruct O hO) M N P =
      tensorSheafAssociator O hO M N P := by
  have canonicalKey := assoc_key O hO M N P
  apply Iso.ext
  refine (congrArg Iso.hom (Strict.associator_eq O hO M N P)).trans ?_
  let leftTensor := (TensorSheafification.sheafify O hO).obj (M.val ⊗ N.val)
  let rightTensor := (TensorSheafification.sheafify O hO).obj (N.val ⊗ P.val)
  have leftWhisker := @MonoidalCategory.tensorHom_id _ _ (monoidalCategory O hO)
    _ _ (tensorObjIso O hO M N).inv P
  have rightWhisker := @MonoidalCategory.id_tensorHom _ _ (monoidalCategory O hO)
    M _ _ (tensorObjIso O hO N P).hom
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg₂ (fun first second =>
      (tensorObjIso O hO leftTensor P).inv ≫ first ≫
        (@MonoidalCategoryStruct.associator _ _ (monoidalCategory O hO).toMonoidalCategoryStruct
          M N P).hom ≫ second ≫ (tensorObjIso O hO M rightTensor).hom)
    leftWhisker rightWhisker).trans ?_
  let leftComparison : (TensorSheafification.sheafify O hO).obj ((M.val ⊗ N.val) ⊗ P.val) ≅
      (TensorSheafification.sheafify O hO).obj (leftTensor.val ⊗ P.val) :=
    tensorSheafAssocLeft O hO M N P
  have leftHom : leftComparison.hom =
      (TensorSheafification.sheafify O hO).map
        (TensorSheafification.toSheafify O hO (M.val ⊗ N.val) ▷ P.val) := rfl
  have rightHom : ((TensorSheafification.sheafify O hO).mapIso (α_ M.val N.val P.val) ≪≫
        tensorSheafAssocRight O hO M N P).hom =
      (TensorSheafification.sheafify O hO).map (α_ M.val N.val P.val).hom ≫
        (TensorSheafification.sheafify O hO).map
          (M.val ◁ TensorSheafification.toSheafify O hO (N.val ⊗ P.val)) := rfl
  apply (Iso.eq_inv_comp leftComparison).mpr
  exact (congrArg (· ≫ _) leftHom).trans (canonicalKey.trans rightHom.symm)

end AssociatorData

/-- **The left unit constraint of the tensor product sheaf is the one of the localized monoidal
structure.** -/
theorem leftUnitor_hom_eq
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (λ_ M).hom = (tensorObjIso O hO (SheafOfModules.unit _) M).hom ≫
      (tensorSheafLeftUnitor O hO M).hom := by
  have h2 := localized_leftUnitor_hom O hO M.val
  have h1 : 𝟙_ (SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    ◁
        (sheafifyValIso O hO M).inv ≫
      (λ_ ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj M.val)).hom ≫
        (sheafifyValIso O hO M).hom =
      (λ_ M).hom := by
    rw [← Category.assoc, MonoidalCategory.leftUnitor_naturality, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  have hR : ((sheafifyUnitIso O hO).inv ⊗ₘ (sheafifyValIso O hO M).inv) ≫
        (sheafifyTensorIso O hO
          (𝟙_ (PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
            hO).obj)) M.val).hom =
      𝟙_ (SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) ◁
          (sheafifyValIso O hO M).inv ≫
        (sheafifyUnitIso O hO).inv ▷ ((Stacks.SheafOfModules.TensorSheafification.sheafify O
          hO).obj M.val) ≫
          (sheafifyTensorIso O hO
            (𝟙_ (PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
              hO).obj)) M.val).hom :=
    (congrArg (· ≫ (sheafifyTensorIso O hO
          (𝟙_ (PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
            hO).obj)) M.val).hom)
        (MonoidalCategory.tensorHom_def' (sheafifyUnitIso O hO).inv
          (sheafifyValIso O hO M).inv)).trans (Category.assoc _ _ _)
  have key : (λ_ M).hom =
      (((sheafifyUnitIso O hO).inv ⊗ₘ (sheafifyValIso O hO M).inv) ≫
          (sheafifyTensorIso O hO
            (𝟙_ (PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
              hO).obj)) M.val).hom) ≫
        ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map (λ_ M.val).hom ≫
          (sheafifyValIso O hO M).hom) := by
    rw [← h1, h2, hR]
    simp only [Category.assoc]
  exact key

/-- **The right unit constraint of the tensor product sheaf is the one of the localized monoidal
structure.** -/
theorem rightUnitor_hom_eq
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (ρ_ M).hom = (tensorObjIso O hO M (SheafOfModules.unit _)).hom ≫
      (tensorLeftFunctorObjUnitIso O hO M).hom := by
  have h2 := localized_rightUnitor_hom O hO M.val
  have h1 : (sheafifyValIso O hO M).inv ▷
        𝟙_ (SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) ≫
      (ρ_ ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj M.val)).hom ≫
        (sheafifyValIso O hO M).hom =
      (ρ_ M).hom := by
    rw [← Category.assoc, MonoidalCategory.rightUnitor_naturality, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  have hR : ((sheafifyValIso O hO M).inv ⊗ₘ (sheafifyUnitIso O hO).inv) ≫
        (sheafifyTensorIso O hO M.val
          (𝟙_ (PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
            hO).obj))).hom =
      (sheafifyValIso O hO M).inv ▷
          𝟙_ (SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) ≫
        ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj M.val) ◁
          (sheafifyUnitIso O hO).inv ≫
          (sheafifyTensorIso O hO M.val
            (𝟙_ (PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
              hO).obj))).hom :=
    (congrArg (· ≫ (sheafifyTensorIso O hO M.val
          (𝟙_ (PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
            hO).obj))).hom)
        (MonoidalCategory.tensorHom_def (sheafifyValIso O hO M).inv
          (sheafifyUnitIso O hO).inv)).trans (Category.assoc _ _ _)
  have key : (ρ_ M).hom =
      (((sheafifyValIso O hO M).inv ⊗ₘ (sheafifyUnitIso O hO).inv) ≫
          (sheafifyTensorIso O hO M.val
            (𝟙_ (PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
              hO).obj))).hom) ≫
        ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map (ρ_ M.val).hom ≫
          (sheafifyValIso O hO M).hom) := by
    rw [← h1, h2, hR]
    simp only [Category.assoc]
  exact key

section Braided2

attribute [local instance] braidedCategory

/-- **The symmetry constraint of the tensor product sheaf is the braiding of the localized
monoidal structure.** -/
theorem braiding_hom_eq
    (M N : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (β_ M N).hom ≫ (tensorObjIso O hO N M).hom =
      (tensorObjIso O hO M N).hom ≫ (tensorSheafBraiding O hO M N).hom := by
  have h1 := BraidedCategory.braiding_naturality
    (sheafifyValIso O hO M).inv (sheafifyValIso O hO N).inv
  have h2 := localized_braiding_hom O hO M.val N.val
  change (β_ M N).hom ≫ ((sheafifyValIso O hO N).inv ⊗ₘ (sheafifyValIso O hO M).inv) ≫
      (sheafifyTensorIso O hO N.val M.val).hom =
    ((sheafifyValIso O hO M).inv ⊗ₘ (sheafifyValIso O hO N).inv) ≫
      (sheafifyTensorIso O hO M.val N.val).hom ≫
        (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map (β_ M.val N.val).hom
  rw [← Category.assoc, ← h1, h2]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end Braided2


/-- **The left unit constraint of the tensor product sheaf is the left unitor of the strict
monoidal structure.** -/
theorem Strict_leftUnitor_eq
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    MonoidalCategoryStruct.leftUnitor (self := Strict.monoidalCategoryStruct O hO) M =
      tensorSheafLeftUnitor O hO M := by
  apply Iso.ext
  rw [Strict.leftUnitor_eq]
  simp only [Iso.trans_hom, Iso.symm_hom]
  rw [leftUnitor_hom_eq]
  exact (tensorObjIso O hO (SheafOfModules.unit
    (TensorSheafification.structureSheaf O hO)) M).inv_hom_id_assoc _

/-- **The right unit constraint of the tensor product sheaf is the right unitor of the strict
monoidal structure.** -/
theorem Strict_rightUnitor_eq
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    MonoidalCategoryStruct.rightUnitor (self := Strict.monoidalCategoryStruct O hO) M =
      tensorLeftFunctorObjUnitIso O hO M := by
  apply Iso.ext
  rw [Strict.rightUnitor_eq]
  simp only [Iso.trans_hom, Iso.symm_hom]
  rw [rightUnitor_hom_eq]
  exact Iso.inv_hom_id_assoc _ _

section Braided3

attribute [local instance] braidedCategory

/-- **The symmetry constraint of the tensor product sheaf is the braiding of the strict monoidal
structure.** -/
theorem Strict_braiding_eq
    (M N : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    Strict.braiding O hO M N = tensorSheafBraiding O hO M N := by
  apply Iso.ext
  change (tensorObjIso O hO M N).inv ≫ (β_ M N).hom ≫ (tensorObjIso O hO N M).hom = _
  rw [braiding_hom_eq]
  exact (tensorObjIso O hO M N).inv_hom_id_assoc _

end Braided3

/-- Sheafification of a morphism of sheaves of modules, compared with the counit. -/
theorem sheafifyValIso_hom_naturality
    {X Y : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)} (f :
      X ⟶ Y) :
    (sheafifyValIso O hO X).hom ≫ f =
      (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map f.val ≫ (sheafifyValIso O hO
        Y).hom :=
  ((Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction O hO).counit.naturality f).symm

/-- **The tensor product of morphisms in the strict monoidal structure is the sheafification of
the tensor product of the underlying morphisms of presheaves.** -/
theorem Strict_tensorHom_eq
    {X₁ Y₁ X₂ Y₂ : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO)}
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    MonoidalCategoryStruct.tensorHom (self := Strict.monoidalCategoryStruct O hO) f g =
      (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map (f.val ⊗ₘ g.val) := by
  have conj : ∀ {X Y : SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)} (f : X ⟶ Y),
      (sheafifyValIso O hO X).hom ≫ f ≫ (sheafifyValIso O hO Y).inv =
        (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map f.val := fun f => by
    rw [← Category.assoc, sheafifyValIso_hom_naturality, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  refine (Strict.tensorHom_eq O hO f g).trans ?_
  refine (congrArg₂ (fun left right => left ≫ (f ⊗ₘ g) ≫ right)
    (tensorObjIso_inv_eq O hO X₁ X₂) (tensorObjIso_hom_eq O hO Y₁ Y₂)).trans ?_
  have conjugate :
      ((sheafifyValIso O hO X₁).hom ⊗ₘ (sheafifyValIso O hO X₂).hom) ≫
        (f ⊗ₘ g) ≫
          ((sheafifyValIso O hO Y₁).inv ⊗ₘ (sheafifyValIso O hO Y₂).inv) =
      (TensorSheafification.sheafify O hO).map f.val ⊗ₘ
        (TensorSheafification.sheafify O hO).map g.val :=
    (congrArg (((sheafifyValIso O hO X₁).hom ⊗ₘ
        (sheafifyValIso O hO X₂).hom) ≫ ·)
      (MonoidalCategory.tensorHom_comp_tensorHom f g
        (sheafifyValIso O hO Y₁).inv (sheafifyValIso O hO Y₂).inv)).trans
      ((MonoidalCategory.tensorHom_comp_tensorHom
        (sheafifyValIso O hO X₁).hom (sheafifyValIso O hO X₂).hom
        (f ≫ (sheafifyValIso O hO Y₁).inv)
        (g ≫ (sheafifyValIso O hO Y₂).inv)).trans
          (congrArg₂ (fun first second => first ⊗ₘ second) (conj f) (conj g)))
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg ((sheafifyTensorIso O hO X₁.val X₂.val).inv ≫ ·)
    ((comp_assoc₃ _ _ _ _).symm.trans
      (congrArg (· ≫ (sheafifyTensorIso O hO Y₁.val Y₂.val).hom) conjugate))).trans ?_
  exact (congrArg ((sheafifyTensorIso O hO X₁.val X₂.val).inv ≫ ·)
    (sheafifyTensorIso_hom_natural O hO f.val g.val)).trans
      ((sheafifyTensorIso O hO X₁.val X₂.val).inv_hom_id_assoc _)


section Payoff

attribute [local instance] Strict.monoidalCategory Strict.braidedCategory

/-- The associator of the strict monoidal structure is the associativity constraint of the
tensor product sheaf. -/
theorem associator_eq_tensorSheafAssociator
    (M N P : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    α_ M N P = tensorSheafAssociator O hO M N P :=
  Strict_associator_eq O hO M N P

/-- The left unitor of the strict monoidal structure is the left unit constraint of the tensor
product sheaf. -/
theorem leftUnitor_eq_tensorSheafLeftUnitor
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    λ_ M = tensorSheafLeftUnitor O hO M :=
  Strict_leftUnitor_eq O hO M

/-- The right unitor of the strict monoidal structure is the right unit constraint of the tensor
product sheaf. -/
theorem rightUnitor_eq_tensorSheafRightUnitor
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    ρ_ M = tensorLeftFunctorObjUnitIso O hO M :=
  Strict_rightUnitor_eq O hO M

/-- The braiding of the strict monoidal structure is the symmetry constraint of the tensor
product sheaf. -/
theorem braiding_eq_tensorSheafBraiding
    (M N : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    β_ M N = tensorSheafBraiding O hO M N :=
  Strict_braiding_eq O hO M N

/-- The tensor product of morphisms in the strict monoidal structure is the sheafification of
the tensor product of the underlying morphisms of presheaves. -/
theorem tensorHom_eq_sheafify_map
    {X₁ Y₁ X₂ Y₂ : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO)}
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    f ⊗ₘ g = (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map (f.val ⊗ₘ g.val) :=
  Strict_tensorHom_eq O hO f g

/-- Left whiskering in the strict monoidal structure is the sheafification of left whiskering of
presheaves. -/
theorem whiskerLeft_eq_sheafify_map
    (X : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    {Y₁ Y₂ : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)} (f
      : Y₁ ⟶ Y₂) :
    X ◁ f = (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map (X.val ◁ f.val) := by
  rw [← MonoidalCategory.id_tensorHom, tensorHom_eq_sheafify_map]
  exact congrArg (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map
    (MonoidalCategory.id_tensorHom X.val f.val)

/-- Right whiskering in the strict monoidal structure is the sheafification of right whiskering
of presheaves. -/
theorem whiskerRight_eq_sheafify_map
    {X₁ X₂ : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)} (f
      : X₁ ⟶ X₂)
    (Y : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    f ▷ Y = (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map (f.val ▷ Y.val) := by
  rw [← MonoidalCategory.tensorHom_id, tensorHom_eq_sheafify_map]
  exact congrArg (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map
    (MonoidalCategory.tensorHom_id f.val Y.val)

/-- The tensor product sheaf of two isomorphisms is their tensor product in the strict monoidal
structure. -/
theorem tensorSheafMapIso_hom_eq
    {M M' N N' : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO)}
    (i : M ≅ M') (j : N ≅ N') :
    (TensorPower.tensorSheafMapIso O hO i j).hom = i.hom ⊗ₘ j.hom :=
  (tensorHom_eq_sheafify_map O hO i.hom j.hom).symm

/-- The tensor sheaf of an isomorphism with an identity, on the right, is a right whiskering. -/
private theorem tensorSheafMapIso_refl_right_hom
    {M M' : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)}
    (i : M ≅ M') (N : SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    {f : M ⟶ M'} (h : i.hom = f) :
    (TensorPower.tensorSheafMapIso O hO i (Iso.refl N)).hom = f ▷ N := by
  subst h
  exact (tensorSheafMapIso_hom_eq O hO i (Iso.refl N)).trans (MonoidalCategory.tensorHom_id _ _)

/-- The tensor sheaf of an identity with an isomorphism, on the left, is a left whiskering. -/
private theorem tensorSheafMapIso_refl_left_hom
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    {N N' : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)}
    (j : N ≅ N') {g : N ⟶ N'} (h : j.hom = g) :
    (TensorPower.tensorSheafMapIso O hO (Iso.refl M) j).hom = M ◁ g := by
  subst h
  exact (tensorSheafMapIso_hom_eq O hO (Iso.refl M) j).trans (MonoidalCategory.id_tensorHom _ _)

/-- **The pentagon identity for the associativity constraint of the tensor product sheaf.** -/
theorem tensorSheafAssociator_pentagon
    (M N P Q : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
      :
    (TensorPower.tensorSheafMapIso O hO
            (tensorSheafAssociator O hO M N P) (Iso.refl Q)).hom ≫
        (tensorSheafAssociator O hO M ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O,
          Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat
          RingCat) (hO)⟩).obj (N)).obj (P))) Q).hom ≫
          (TensorPower.tensorSheafMapIso O hO (Iso.refl M)
            (tensorSheafAssociator O hO N P Q)).hom =
      (tensorSheafAssociator O hO ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O,
        Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj (M)).obj (N)))
        P Q).hom ≫
        (tensorSheafAssociator O hO M N ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O,
          Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat
          RingCat) (hO)⟩).obj (P)).obj (Q)))).hom := by

  have firstAssoc := (congrArg Iso.hom (associator_eq_tensorSheafAssociator O hO M N P)).symm
  have lastAssoc := (congrArg Iso.hom (associator_eq_tensorSheafAssociator O hO N P Q)).symm
  have firstMap := tensorSheafMapIso_refl_right_hom O hO _ Q firstAssoc
  have middleMap := (congrArg Iso.hom (associator_eq_tensorSheafAssociator O hO M (@MonoidalCategoryStruct.tensorObj _ _ (Strict.monoidalCategoryStruct O hO) N P) Q)).symm
  have lastMap := tensorSheafMapIso_refl_left_hom O hO M _ lastAssoc
  have rightFirst := (congrArg Iso.hom (associator_eq_tensorSheafAssociator O hO (@MonoidalCategoryStruct.tensorObj _ _ (Strict.monoidalCategoryStruct O hO) M N) P Q)).symm
  have rightLast := (congrArg Iso.hom (associator_eq_tensorSheafAssociator O hO M N (@MonoidalCategoryStruct.tensorObj _ _ (Strict.monoidalCategoryStruct O hO) P Q))).symm
  exact (congrArg₂ (fun first second => first ≫ second) firstMap (congrArg₂ (fun first second => first ≫ second) middleMap lastMap)).trans
    ((@MonoidalCategory.pentagon _ _ (Strict.monoidalCategory O hO) M N P Q).trans (congrArg₂ (fun first second => first ≫ second) rightFirst rightLast).symm)

/-- **The triangle identity for the constraints of the tensor product sheaf.** -/
theorem tensorSheafAssociator_triangle
    (M N : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (tensorSheafAssociator O hO M
            (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
              N).hom ≫
        (TensorPower.tensorSheafMapIso O hO (Iso.refl M)
          (tensorSheafLeftUnitor O hO N)).hom =
      (TensorPower.tensorSheafMapIso O hO
        (tensorLeftFunctorObjUnitIso O hO M) (Iso.refl N)).hom := by

  have associatorMap := (congrArg Iso.hom (associator_eq_tensorSheafAssociator O hO M (SheafOfModules.unit (TensorSheafification.structureSheaf O hO)) N)).symm
  have leftUnit := (congrArg Iso.hom (leftUnitor_eq_tensorSheafLeftUnitor O hO N)).symm
  have rightUnit := (congrArg Iso.hom (rightUnitor_eq_tensorSheafRightUnitor O hO M)).symm
  have leftMap := tensorSheafMapIso_refl_left_hom O hO M _ leftUnit
  have rightMap := tensorSheafMapIso_refl_right_hom O hO _ N rightUnit
  exact (congrArg₂ (fun first second => first ≫ second) associatorMap leftMap).trans
    ((@MonoidalCategory.triangle _ _ (Strict.monoidalCategory O hO) M N).trans rightMap.symm)

/-- **The unit coherence which normalises multiplication by the zeroth tensor power on the
left.** It is `CategoryTheory.MonoidalCategory.leftUnitor_tensor_hom` for the tensor product
sheaf. -/
theorem tensorSheafLeftUnitor_tensor
    (M N : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (tensorSheafLeftUnitor O hO ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O,
      Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj (M)).obj (N)))).hom =
      (tensorSheafAssociator O hO
            (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) M
              N).inv ≫
        (TensorPower.tensorSheafMapIso O hO (tensorSheafLeftUnitor O hO M) (Iso.refl N)).hom := by

  have sourceUnit := (congrArg Iso.hom (leftUnitor_eq_tensorSheafLeftUnitor O hO (@MonoidalCategoryStruct.tensorObj _ _ (Strict.monoidalCategoryStruct O hO) M N))).symm
  have targetUnit := (congrArg Iso.hom (leftUnitor_eq_tensorSheafLeftUnitor O hO M)).symm
  have associatorMap := (congrArg Iso.inv (associator_eq_tensorSheafAssociator O hO (SheafOfModules.unit (TensorSheafification.structureSheaf O hO)) M N)).symm
  have tensorMap := tensorSheafMapIso_refl_right_hom O hO _ N targetUnit
  exact sourceUnit.trans ((@MonoidalCategory.leftUnitor_tensor_hom _ _ (Strict.monoidalCategory O hO) M N).trans
    (congrArg₂ (fun first second => first ≫ second) associatorMap tensorMap).symm)

/-- **The right-handed counterpart of `tensorSheafLeftUnitor_tensor`.** -/
theorem tensorSheafRightUnitor_tensor
    (M N : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (tensorLeftFunctorObjUnitIso O hO ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O,
      Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj (M)).obj (N)))).hom =
      (tensorSheafAssociator O hO M N
            (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
              hO))).hom ≫
        (TensorPower.tensorSheafMapIso O hO (Iso.refl M)
          (tensorLeftFunctorObjUnitIso O hO N)).hom := by

  have sourceUnit := (congrArg Iso.hom (rightUnitor_eq_tensorSheafRightUnitor O hO (@MonoidalCategoryStruct.tensorObj _ _ (Strict.monoidalCategoryStruct O hO) M N))).symm
  have targetUnit := (congrArg Iso.hom (rightUnitor_eq_tensorSheafRightUnitor O hO N)).symm
  have associatorMap := (congrArg Iso.hom (associator_eq_tensorSheafAssociator O hO M N (SheafOfModules.unit (TensorSheafification.structureSheaf O hO)))).symm
  have tensorMap := tensorSheafMapIso_refl_left_hom O hO M _ targetUnit
  exact sourceUnit.trans ((@MonoidalCategory.rightUnitor_tensor_hom _ _ (Strict.monoidalCategory O hO) M N).trans
    (congrArg₂ (fun first second => first ≫ second) associatorMap tensorMap).symm)

/-- **The forward hexagon identity for the constraints of the tensor product sheaf.** -/
theorem tensorSheafBraiding_hexagon_forward
    (M N P : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (tensorSheafAssociator O hO M N P).hom ≫
        (tensorSheafBraiding O hO M ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O,
          Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat
          RingCat) (hO)⟩).obj (N)).obj (P)))).hom ≫
          (tensorSheafAssociator O hO N P M).hom =
      (TensorPower.tensorSheafMapIso O hO (tensorSheafBraiding O hO M N) (Iso.refl P)).hom ≫
        (tensorSheafAssociator O hO N M P).hom ≫
          (TensorPower.tensorSheafMapIso O hO (Iso.refl N)
            (tensorSheafBraiding O hO M P)).hom := by

  have leftFirst := (congrArg Iso.hom (associator_eq_tensorSheafAssociator O hO M N P)).symm
  have leftMiddle := (congrArg Iso.hom (braiding_eq_tensorSheafBraiding O hO M (@MonoidalCategoryStruct.tensorObj _ _ (Strict.monoidalCategoryStruct O hO) N P))).symm
  have leftLast := (congrArg Iso.hom (associator_eq_tensorSheafAssociator O hO N P M)).symm
  have firstBraid := (congrArg Iso.hom (braiding_eq_tensorSheafBraiding O hO M N)).symm
  have lastBraid := (congrArg Iso.hom (braiding_eq_tensorSheafBraiding O hO M P)).symm
  have rightFirst := tensorSheafMapIso_refl_right_hom O hO _ P firstBraid
  have rightMiddle := (congrArg Iso.hom (associator_eq_tensorSheafAssociator O hO N M P)).symm
  have rightLast := tensorSheafMapIso_refl_left_hom O hO N _ lastBraid
  exact (congrArg₂ (fun first second => first ≫ second) leftFirst (congrArg₂ (fun first second => first ≫ second) leftMiddle leftLast)).trans
    ((@BraidedCategory.hexagon_forward _ _ (Strict.monoidalCategory O hO) (Strict.braidedCategory O hO) M N P).trans
      (congrArg₂ (fun first second => first ≫ second) rightFirst (congrArg₂ (fun first second => first ≫ second) rightMiddle rightLast)).symm)

/-- **The reverse hexagon identity for the constraints of the tensor product sheaf.** -/
theorem tensorSheafBraiding_hexagon_reverse
    (M N P : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (tensorSheafAssociator O hO M N P).inv ≫
        (tensorSheafBraiding O hO ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O,
          Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj (M)).obj (N)))
          P).hom ≫
          (tensorSheafAssociator O hO P M N).inv =
      (TensorPower.tensorSheafMapIso O hO (Iso.refl M) (tensorSheafBraiding O hO N P)).hom ≫
        (tensorSheafAssociator O hO M P N).inv ≫
          (TensorPower.tensorSheafMapIso O hO
            (tensorSheafBraiding O hO M P) (Iso.refl N)).hom := by

  have leftFirst := (congrArg Iso.inv (associator_eq_tensorSheafAssociator O hO M N P)).symm
  have leftMiddle := (congrArg Iso.hom (braiding_eq_tensorSheafBraiding O hO (@MonoidalCategoryStruct.tensorObj _ _ (Strict.monoidalCategoryStruct O hO) M N) P)).symm
  have leftLast := (congrArg Iso.inv (associator_eq_tensorSheafAssociator O hO P M N)).symm
  have firstBraid := (congrArg Iso.hom (braiding_eq_tensorSheafBraiding O hO N P)).symm
  have lastBraid := (congrArg Iso.hom (braiding_eq_tensorSheafBraiding O hO M P)).symm
  have rightFirst := tensorSheafMapIso_refl_left_hom O hO M _ firstBraid
  have rightMiddle := (congrArg Iso.inv (associator_eq_tensorSheafAssociator O hO M P N)).symm
  have rightLast := tensorSheafMapIso_refl_right_hom O hO _ N lastBraid
  exact (congrArg₂ (fun first second => first ≫ second) leftFirst (congrArg₂ (fun first second => first ≫ second) leftMiddle leftLast)).trans
    ((@BraidedCategory.hexagon_reverse _ _ (Strict.monoidalCategory O hO) (Strict.braidedCategory O hO) M N P).trans
      (congrArg₂ (fun first second => first ≫ second) rightFirst (congrArg₂ (fun first second => first ≫ second) rightMiddle rightLast)).symm)

/-- The two unit constraints of the tensor product sheaf agree at the structure sheaf itself.
This is the base case, at exponent `0`, of the left unit normalisation of Tag 01CU. -/
theorem tensorSheafLeftUnitor_unit :
    tensorSheafLeftUnitor O hO (SheafOfModules.unit
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) =
      tensorLeftFunctorObjUnitIso O hO (SheafOfModules.unit
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) := by
  apply Iso.ext
  rw [← leftUnitor_eq_tensorSheafLeftUnitor, ← rightUnitor_eq_tensorSheafRightUnitor]
  exact MonoidalCategory.unitors_equal

/-- Tensoring the left unit constraint with the structure sheaf on the left gives the left unit
constraint of the tensor product. This is the base case, at exponent `1`, of the left unit
normalisation of Tag 01CU. -/
theorem tensorSheafLeftUnitor_whiskerLeft
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    TensorPower.tensorSheafMapIso O hO
          (Iso.refl (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf
            O hO)))
          (tensorSheafLeftUnitor O hO M) =
      tensorSheafLeftUnitor O hO
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂
          CommRingCat RingCat) (hO)⟩).obj ((SheafOfModules.unit
          (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)))).obj (M)))
            := by

  apply Iso.ext
  have unitMap := (congrArg Iso.hom (leftUnitor_eq_tensorSheafLeftUnitor O hO M)).symm
  have tensorMap := tensorSheafMapIso_refl_left_hom O hO
    (SheafOfModules.unit (TensorSheafification.structureSheaf O hO)) _ unitMap
  have naturality := (cancel_mono (@MonoidalCategoryStruct.leftUnitor _ _ (Strict.monoidalCategoryStruct O hO) M).hom).mp
    (@MonoidalCategory.leftUnitor_naturality _ _ (Strict.monoidalCategory O hO) _ _ (@MonoidalCategoryStruct.leftUnitor _ _ (Strict.monoidalCategoryStruct O hO) M).hom)
  have targetUnit := (congrArg Iso.hom (leftUnitor_eq_tensorSheafLeftUnitor O hO (@MonoidalCategoryStruct.tensorObj _ _ (Strict.monoidalCategoryStruct O hO) (SheafOfModules.unit (TensorSheafification.structureSheaf O hO)) M))).symm
  exact tensorMap.trans (naturality.trans targetUnit.symm)

end Payoff

end Localized


namespace TensorPower

open Stacks.Equivalence

/-- **The left unit normalisation of Tag 01CU, reduced.** Multiplication by the zeroth tensor
power on the left is the comparison `powFunctorIsoTensorRight` evaluated at the structure sheaf;
the `powAdd` side of the normalisation is discharged here by `powAdd_zero_left`. What remains of
the left unit normalisation `mulIso 0 n ≪≫ reindex = leftUnitor` is therefore exactly the
statement that `(powFunctorIsoTensorRight O hO L n).app` at the structure sheaf is the inverse of
`Stacks.SheafOfModules.tensorSheafLeftUnitor`, whose base cases at the exponents `0` and `1` are
`tensorSheafLeftUnitor_unit` and `tensorSheafLeftUnitor_whiskerLeft`. -/
theorem tensorPowerMulIso_zero_left_eq
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    [((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).flip.obj L).IsEquivalence] (n : ℤ) :
    tensorPowerMulIso O hO L 0 n ≪≫ tensorPowerReindex O hO L (Int.zero_add n) =
      ((powFunctorIsoTensorRight O hO L n).app
        (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))).symm
          := by
  have hz : (CategoryTheory.Equivalence.powAdd ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).flip.obj L).asEquivalence 0 n
        (0 + n) rfl).app (SheafOfModules.unit
          (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) ≪≫
      tensorPowerReindex O hO L (Int.zero_add n) = Iso.refl _ := by
    rw [tensorPowerReindex_eq_eqToIso]
    have h := Stacks.Equivalence.powAdd_app_cast
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).flip.obj L).asEquivalence 0 n n (Int.zero_add n)
      (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    rw [CategoryTheory.Equivalence.powAdd_zero_left] at h
    exact h.symm
  refine (Iso.trans_assoc _ _ _).trans ?_
  exact (congrArg (fun z =>
    ((powFunctorIsoTensorRight O hO L n).app (tensorPower O hO L 0)).symm ≪≫ z) hz).trans
      (Iso.trans_refl _)

end TensorPower

end Stacks.SheafOfModules

end
