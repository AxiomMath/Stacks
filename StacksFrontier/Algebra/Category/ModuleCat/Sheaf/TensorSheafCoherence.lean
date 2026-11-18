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
* `Stacks.SheafOfModules.toSheafTensor`: the canonical morphism `M ⊗ N ⟶ M ⊗_O N` from the
  presheaf tensor product to the tensor product sheaf, the unit of the sealed sheafification
  `Stacks.SheafOfModules.Tensor.sheafification`.
* `Stacks.SheafOfModules.sheafifyIsoSheafification` and
  `Stacks.SheafOfModules.sheafifyIsoSheafTensor`: the comparison
  `Stacks.SheafOfModules.Tensor.sheafificationIso` of Mathlib's sheafification with the sealed
  one, spelled over `Stacks.SheafOfModules.TensorSheafification.structureSheaf`, as a natural
  isomorphism and at a presheaf tensor product of two sheaves.

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

The tensor product sheaf is built with the sealed sheafification
`Stacks.SheafOfModules.Tensor.sheafification`, the localized monoidal structure with Mathlib's.
The two meet only through `Stacks.SheafOfModules.sheafifyIsoSheafification`, which is spelled over
the structure sheaf so that composites through it stay in one category, and through
`Stacks.SheafOfModules.sheafifyIsoSheafTensor`, whose target is spelled as the tensor product
sheaf, so that `Stacks.SheafOfModules.tensorObjIso_hom_eq` and the two Tag 05NA comparisons
cancel against each other by `rw`.

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

/-! ### Mathlib's sheafification and the sealed one

The tensor product sheaf is built with the sealed sheafification
`Stacks.SheafOfModules.Tensor.sheafification`, while the localized monoidal structure of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Monoidal` is built with Mathlib's,
`Stacks.SheafOfModules.TensorSheafification.sheafify`. The two are compared by
`Stacks.SheafOfModules.Tensor.sheafificationIso`, the last factor of the body
`Stacks.SheafOfModules.tensorObjIso_def` of `Stacks.SheafOfModules.tensorObjIso`; the lemmas
below are the two further facts about that comparison used in this file: it carries Mathlib's
counit to the sealed one, and it is Mathlib's sheafification of the sealed unit followed by
Mathlib's counit. -/

/-- The comparison `Stacks.SheafOfModules.Tensor.sheafificationIso` of Mathlib's sheafification
with the sealed one, spelled over `Stacks.SheafOfModules.TensorSheafification.structureSheaf`,
the spelling of the localized monoidal structure. -/
noncomputable def sheafifyIsoSheafification :
    TensorSheafification.sheafify O hO ≅
      (Tensor.sheafification
          ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩ :
        PresheafOfModules.{w} (TensorSheafification.structureSheaf O hO).obj ⥤
          SheafOfModules.{w} (TensorSheafification.structureSheaf O hO)) :=
  Tensor.sheafificationIso
    ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩

/-- Mathlib's sheafification of the presheaf tensor product of two sheaves of modules is their
tensor product sheaf: the component of `Stacks.SheafOfModules.sheafifyIsoSheafification`, with
its target spelled as the tensor product sheaf. -/
noncomputable def sheafifyIsoSheafTensor
    (F G : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO)) :
    (TensorSheafification.sheafify O hO).obj (F.val ⊗ G.val) ≅
      ((Tensor.sheafTensor.{u, v, w, w, w}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).obj F).obj G :=
  (sheafifyIsoSheafification O hO).app (F.val ⊗ G.val)

/-- On a presheaf of modules, the unit of the sealed sheafification into the underlying presheaf
is the unit of `Stacks.SheafOfModules.Tensor.sheafificationAdjunction`. -/
private theorem sheafificationForgetAdjunction_unit_app_eq (R : Sheaf J CommRingCat.{w})
    (Q : PresheafOfModules.{w} (Tensor.ringSheaf R).obj) :
    (Tensor.sheafificationForgetAdjunction R).unit.app Q =
      (Tensor.sheafificationAdjunction R).unit.app Q :=
  PresheafOfModules.hom_ext fun X ↦ ModuleCat.hom_ext (LinearMap.ext fun x ↦
    Tensor.sheafificationForgetAdjunction_unit_app_app_apply R Q X x)

/-- Mathlib's sheafification of the sealed sheafification unit, followed by Mathlib's counit, is
the comparison `Stacks.SheafOfModules.Tensor.sheafificationIso`. -/
private theorem sheafification_map_unit_comp_counit (R : Sheaf J CommRingCat.{w})
    (Q : PresheafOfModules.{w} (Tensor.ringSheaf R).obj) :
    (PresheafOfModules.sheafification (𝟙 (Tensor.ringSheaf R).obj)).map
        ((Tensor.sheafificationForgetAdjunction R).unit.app Q) ≫
        (PresheafOfModules.sheafificationAdjunction (𝟙 (Tensor.ringSheaf R).obj)).counit.app
          ((Tensor.sheafification R).obj Q) =
      (Tensor.sheafificationIso R).hom.app Q := by
  rw [sheafificationForgetAdjunction_unit_app_eq]
  refine ((PresheafOfModules.sheafificationAdjunction
    (𝟙 (Tensor.ringSheaf R).obj)).homEquiv_counit _ _ _).symm.trans ?_
  rw [Equiv.symm_apply_eq, Adjunction.homEquiv_unit]
  exact (Tensor.unit_comp_sheafificationIso_hom_app R Q).symm

/-- The canonical morphism `M ⊗ N ⟶ M ⊗_O N` from the presheaf tensor product to the tensor
product sheaf: the unit of the sealed sheafification `Stacks.SheafOfModules.Tensor.sheafification`
into the underlying presheaf. -/
noncomputable def toSheafTensor
    (M N : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO)) :
    M.val ⊗ N.val ⟶ (((Tensor.sheafTensor.{u, v, w, w, w}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).obj M).obj
          N).val :=
  (Tensor.sheafificationForgetAdjunction
    ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).unit.app
      (M.val ⊗ N.val)

/-- Mathlib's sheafification of `Stacks.SheafOfModules.toSheafTensor`, followed by Mathlib's
counit, is the comparison `Stacks.SheafOfModules.Tensor.sheafificationIso`. -/
private theorem sheafify_map_toSheafTensor_comp_sheafifyValIso_hom
    (M N : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO)) :
    (TensorSheafification.sheafify O hO).map (toSheafTensor O hO M N) ≫
        (sheafifyValIso O hO (((Tensor.sheafTensor.{u, v, w, w, w}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).obj M).obj
          N)).hom =
      (sheafifyIsoSheafTensor O hO M N).hom :=
  sheafification_map_unit_comp_counit
    ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩ (M.val ⊗ N.val)

/-- Mathlib's sheafification of `Stacks.SheafOfModules.toSheafTensor` is the comparison
`Stacks.SheafOfModules.Tensor.sheafificationIso` followed by the inverse of Mathlib's counit. -/
private theorem sheafify_map_toSheafTensor_eq
    (M N : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO)) :
    (TensorSheafification.sheafify O hO).map (toSheafTensor O hO M N) =
      (sheafifyIsoSheafTensor O hO M N).hom ≫
        (sheafifyValIso O hO (((Tensor.sheafTensor.{u, v, w, w, w}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).obj M).obj
          N)).inv :=
  (Iso.eq_comp_inv _).mpr (sheafify_map_toSheafTensor_comp_sheafifyValIso_hom O hO M N)

/-- Mathlib's sheafification inverts `Stacks.SheafOfModules.toSheafTensor`. -/
theorem isIso_sheafify_map_toSheafTensor
    (M N : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO)) :
    IsIso ((TensorSheafification.sheafify O hO).map (toSheafTensor O hO M N)) := by
  rw [sheafify_map_toSheafTensor_eq]
  exact (sheafifyIsoSheafTensor O hO M N ≪≫ (sheafifyValIso O hO _).symm).isIso_hom

/-- The comparison `Stacks.SheafOfModules.Tensor.sheafificationIso` carries Mathlib's counit of
sheafification to the sealed one. -/
private theorem sheafificationIso_hom_app_comp_counit
    (F : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO)) :
    (sheafifyIsoSheafification O hO).hom.app F.val ≫
        (Tensor.sheafificationAdjunction
          ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).counit.app F =
      (sheafifyValIso O hO F).hom := by
  rw [sheafifyIsoSheafification, Tensor.sheafificationIso_def]
  exact Adjunction.leftAdjointUniq_hom_app_counit _ _ F

/-- A morphism `P ⟶ F` into a sheaf, sheafified by the sealed sheafification and followed by the
sealed counit, is the same morphism sheafified by Mathlib's sheafification and followed by
Mathlib's counit, up to the comparison `Stacks.SheafOfModules.Tensor.sheafificationIso`. -/
private theorem sheafificationIso_hom_app_comp_map_comp_counit
    {P : PresheafOfModules.{w} (TensorSheafification.structureSheaf O hO).obj}
    {F : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO)} (f : P ⟶ F.val) :
    (sheafifyIsoSheafification O hO).hom.app P ≫
        (Tensor.sheafification
          ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).map f ≫
          (Tensor.sheafificationAdjunction
            ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).counit.app
              F =
      (TensorSheafification.sheafify O hO).map f ≫ (sheafifyValIso O hO F).hom := by
  rw [← sheafificationIso_hom_app_comp_counit]
  exact ((sheafifyIsoSheafification O hO).hom.naturality_assoc
      f _).symm

/-- The left unit constraint of the tensor product sheaf: the sheafified presheaf left unitor,
followed by the counit of the sealed sheafification. -/
noncomputable def tensorSheafLeftUnitor
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂
      CommRingCat RingCat) (hO)⟩).obj ((SheafOfModules.unit
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)))).obj (M)) ≅ M :=
  (Tensor.sheafification
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).mapIso
      (λ_ M.val) ≪≫
    (asIso (Tensor.sheafificationAdjunction
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).counit).app M

/-- The comparison identifying the sheafification of `(M ⊗ N) ⊗ P` with
`(M ⊗_O N) ⊗_O P`: the sheafification of `Stacks.SheafOfModules.toSheafTensor` for `M ⊗ N`
tensored with `P`, followed by `Stacks.SheafOfModules.sheafifyIsoSheafTensor`. -/
noncomputable def tensorSheafAssocLeft
    (M N P : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj ((M.val ⊗ N.val) ⊗ P.val) ≅
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O)
        (forget₂
        CommRingCat RingCat) (hO)⟩).obj ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
          (J := J)
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat
          RingCat) hO⟩).obj M).obj N))).obj (P)) :=
  @asIso _ _ _ _ ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map
      (toSheafTensor O hO M N ▷ P.val))
    (Stacks.SheafOfModules.TensorSheafification.isIso_sheafify_map_whiskerRight O hO _ P.val
      (isIso_sheafify_map_toSheafTensor O hO M N)) ≪≫
    sheafifyIsoSheafTensor O hO
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
          ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).obj M).obj
            N) P

/-- The comparison identifying the sheafification of `M ⊗ (N ⊗ P)` with
`M ⊗_O (N ⊗_O P)`: the sheafification of `M` tensored with
`Stacks.SheafOfModules.toSheafTensor` for `N ⊗ P`, followed by
`Stacks.SheafOfModules.sheafifyIsoSheafTensor`. -/
noncomputable def tensorSheafAssocRight
    (M N P : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj (M.val ⊗ N.val ⊗ P.val) ≅
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O)
        (forget₂
        CommRingCat RingCat) (hO)⟩).obj (M)).obj
          ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w,
        w} (J := J)
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).obj N).obj
          P))) :=
  @asIso _ _ _ _ ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map
      (M.val ◁ toSheafTensor O hO N P))
    (Stacks.SheafOfModules.TensorSheafification.isIso_sheafify_map_whiskerLeft O hO M.val _
      (isIso_sheafify_map_toSheafTensor O hO N P)) ≪≫
    sheafifyIsoSheafTensor O hO M
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
          ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).obj N).obj P)

/-- The comparison `Stacks.SheafOfModules.tensorSheafAssocLeft`, as a morphism. -/
theorem tensorSheafAssocLeft_hom
    (M N P : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (tensorSheafAssocLeft O hO M N P).hom =
      (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map
          (toSheafTensor O hO M N ▷ P.val) ≫
        (sheafifyIsoSheafTensor O hO
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
          ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).obj M).obj
            N) P).hom :=
  rfl

/-- The comparison `Stacks.SheafOfModules.tensorSheafAssocRight`, as a morphism. -/
theorem tensorSheafAssocRight_hom
    (M N P : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (tensorSheafAssocRight O hO M N P).hom =
      (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map
          (M.val ◁ toSheafTensor O hO N P) ≫
        (sheafifyIsoSheafTensor O hO M
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
          ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).obj N).obj
            P)).hom :=
  rfl

/-- The associativity constraint of the tensor product sheaf. -/
noncomputable def tensorSheafAssociator
    (M N P : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂
      CommRingCat RingCat) (hO)⟩).obj ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
        (J := J)
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).obj M).obj
          N))).obj (P)) ≅
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O)
        (forget₂
        CommRingCat RingCat) (hO)⟩).obj (M)).obj
          ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w,
        w} (J := J)
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).obj N).obj
          P))) :=
  (tensorSheafAssocLeft O hO M N P).symm ≪≫
    (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).mapIso (α_ M.val N.val P.val) ≪≫
      tensorSheafAssocRight O hO M N P

section Localized

attribute [local instance] monoidalCategory

theorem tensorObjIso_hom_eq
    (F G : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (tensorObjIso O hO F G).hom =
      ((sheafifyValIso O hO F).inv ⊗ₘ (sheafifyValIso O hO G).inv) ≫
        (sheafifyTensorIso O hO F.val G.val).hom ≫
          (sheafifyIsoSheafTensor O hO F G).hom := by
  rw [tensorObjIso_def]
  rfl

theorem tensorObjIso_inv_eq
    (F G : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (tensorObjIso O hO F G).inv =
      (sheafifyIsoSheafTensor O hO F G).inv ≫
        (sheafifyTensorIso O hO F.val G.val).inv ≫
          ((sheafifyValIso O hO F).hom ⊗ₘ (sheafifyValIso O hO G).hom) := by
  rw [tensorObjIso_def]
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
    (tensorSheafAssocLeft O hO M N P).hom ≫
        (tensorObjIso O hO ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
          ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).obj M).obj
            N)) P).inv =
      (sheafifyTensorIso O hO (M.val ⊗ N.val) P.val).inv ≫
        ((sheafifyIsoSheafTensor O hO M N).hom ⊗ₘ (sheafifyValIso O hO P).hom) := by
  rw [tensorSheafAssocLeft_hom, tensorObjIso_inv_eq, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← reassoc_of% (sheafifyTensorIso_inv_natural_left O hO (toSheafTensor O hO M N) P.val),
    ← MonoidalCategory.tensorHom_id,
    MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp,
    sheafify_map_toSheafTensor_comp_sheafifyValIso_hom]

/-- **Step two of the associator comparison.** -/
theorem assoc_step_mid
    (M N P : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    ((sheafifyIsoSheafTensor O hO M N).hom ⊗ₘ (sheafifyValIso O hO P).hom) ≫
        ((tensorObjIso O hO M N).inv ▷ P) ≫ (α_ M N P).hom ≫
          (M ◁ (tensorObjIso O hO N P).hom) ≫
            (tensorObjIso O hO M ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
              ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).obj
                N).obj P))).hom =
      ((sheafifyTensorIso O hO M.val N.val).inv ▷
            (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj P.val) ≫
        (α_ ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj M.val)
          ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj N.val)
            ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj P.val)).hom ≫
          ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj M.val ◁
            (sheafifyTensorIso O hO N.val P.val).hom) ≫
            (sheafifyTensorIso O hO M.val (N.val ⊗ P.val)).hom ≫
              (tensorSheafAssocRight O hO M N P).hom := by
  rw [tensorObjIso_inv_eq, tensorObjIso_hom_eq, tensorObjIso_hom_eq, tensorSheafAssocRight_hom]
  rw [← reassoc_of% (sheafifyTensorIso_hom_natural_right O hO M.val (toSheafTensor O hO N P)),
    sheafify_map_toSheafTensor_eq]
  simp only [MonoidalCategory.tensorHom_def, Category.assoc,
    MonoidalCategory.comp_whiskerRight, MonoidalCategory.whiskerLeft_comp,
    MonoidalCategory.whisker_exchange_assoc,
    MonoidalCategory.associator_naturality_left_assoc,
    MonoidalCategory.associator_naturality_middle_assoc,
    MonoidalCategory.associator_naturality_right_assoc]
  simp only [← MonoidalCategory.whiskerLeft_comp_assoc, ← MonoidalCategory.comp_whiskerRight_assoc,
    Iso.hom_inv_id, Iso.hom_inv_id_assoc,
    MonoidalCategory.whiskerLeft_id, MonoidalCategory.id_whiskerRight, Category.id_comp]

/-- **The associator comparison.** The sheafification-built associativity constraint of the
tensor product sheaf is the associator of the localized monoidal structure, conjugated by
`Stacks.SheafOfModules.tensorObjIso`. -/
theorem assoc_key
    (M N P : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (tensorSheafAssocLeft O hO M N P).hom ≫
        (tensorObjIso O hO ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
          ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).obj M).obj
            N)) P).inv ≫
          ((tensorObjIso O hO M N).inv ▷ P) ≫ (α_ M N P).hom ≫
            (M ◁ (tensorObjIso O hO N P).hom) ≫
              (tensorObjIso O hO M ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
                ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).obj
                  N).obj P))).hom =
      (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map (α_ M.val N.val P.val).hom ≫
        (tensorSheafAssocRight O hO M N P).hom := by
  rw [reassoc_of% (assoc_step_left O hO M N P), assoc_step_mid, localized_associator_hom]
  simp only [Category.assoc, MonoidalCategory.inv_hom_whiskerRight_assoc,
    Iso.inv_hom_id_assoc, MonoidalCategory.whiskerLeft_inv_hom_assoc]

section AssociatorData

/-- **The associativity constraint of the tensor product sheaf is the associator of the strict
monoidal structure.** -/
theorem Strict_associator_eq
    (M N P : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    MonoidalCategoryStruct.associator (self := Strict.monoidalCategoryStruct O hO) M N P =
      tensorSheafAssociator O hO M N P := by
  apply Iso.ext
  rw [Strict.associator_eq]
  simp only [tensorSheafAssociator, Iso.trans_hom, Iso.symm_hom, tensorIso_hom, Iso.refl_hom,
    MonoidalCategory.tensorHom_id, MonoidalCategory.id_tensorHom, Functor.mapIso_hom,
    Category.assoc]
  rw [Iso.eq_inv_comp]
  exact assoc_key O hO M N P

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
  refine key.trans ?_
  rw [tensorObjIso_hom_eq]
  simp only [Category.assoc]
  exact congrArg (_ ≫ _ ≫ ·)
    (sheafificationIso_hom_app_comp_map_comp_counit O hO (λ_ M.val).hom).symm

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
  refine key.trans ?_
  rw [tensorObjIso_hom_eq]
  simp only [Category.assoc]
  exact congrArg (_ ≫ _ ≫ ·)
    (sheafificationIso_hom_app_comp_map_comp_counit O hO (ρ_ M.val).hom).symm

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
  simp only [tensorObjIso_hom_eq, Category.assoc]
  rw [← Category.assoc, ← h1, h2]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact congrArg (_ ≫ _ ≫ ·) ((sheafifyIsoSheafification O hO).hom.naturality
      (β_ M.val N.val).hom)

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

/-- **The tensor product of morphisms in the strict monoidal structure is the sealed
sheafification `Stacks.SheafOfModules.Tensor.sheafification` of the tensor product of the
underlying morphisms of presheaves.** -/
theorem Strict_tensorHom_eq
    {X₁ Y₁ X₂ Y₂ : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO)}
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    MonoidalCategoryStruct.tensorHom (self := Strict.monoidalCategoryStruct O hO) f g =
      (Tensor.sheafification
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).map
          (f.val ⊗ₘ g.val) := by
  have conj : ∀ {X Y : SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)} (f : X ⟶ Y),
      (sheafifyValIso O hO X).hom ≫ f ≫ (sheafifyValIso O hO Y).inv =
        (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map f.val := fun f => by
    rw [← Category.assoc, sheafifyValIso_hom_naturality, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  rw [Strict.tensorHom_eq, tensorObjIso_inv_eq, tensorObjIso_hom_eq]
  simp only [Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom_assoc, conj]
  rw [reassoc_of% (sheafifyTensorIso_hom_natural O hO f.val g.val), Iso.inv_hom_id_assoc]
  exact NatIso.naturality_1 (sheafifyIsoSheafification O hO) (f.val ⊗ₘ g.val)


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

/-- The tensor product of morphisms in the strict monoidal structure is the sealed
sheafification `Stacks.SheafOfModules.Tensor.sheafification` of the tensor product of the
underlying morphisms of presheaves. -/
theorem tensorHom_eq_sheafify_map
    {X₁ Y₁ X₂ Y₂ : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO)}
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    f ⊗ₘ g = (Tensor.sheafification
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).map
      (f.val ⊗ₘ g.val) :=
  Strict_tensorHom_eq O hO f g

/-- Left whiskering in the strict monoidal structure is the sealed sheafification
`Stacks.SheafOfModules.Tensor.sheafification` of left whiskering of presheaves. -/
theorem whiskerLeft_eq_sheafify_map
    (X : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    {Y₁ Y₂ : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)} (f
      : Y₁ ⟶ Y₂) :
    X ◁ f = (Tensor.sheafification
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).map
      (X.val ◁ f.val) := by
  rw [← MonoidalCategory.id_tensorHom, tensorHom_eq_sheafify_map]
  exact congrArg (Tensor.sheafification
    ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).map
    (MonoidalCategory.id_tensorHom X.val f.val)

/-- Right whiskering in the strict monoidal structure is the sealed sheafification
`Stacks.SheafOfModules.Tensor.sheafification` of right whiskering of presheaves. -/
theorem whiskerRight_eq_sheafify_map
    {X₁ X₂ : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)} (f
      : X₁ ⟶ X₂)
    (Y : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    f ▷ Y = (Tensor.sheafification
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).map
      (f.val ▷ Y.val) := by
  rw [← MonoidalCategory.tensorHom_id, tensorHom_eq_sheafify_map]
  exact congrArg (Tensor.sheafification
    ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).map
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
        Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj (M)).obj
          (N)))
        P Q).hom ≫
        (tensorSheafAssociator O hO M N ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O,
          Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat
          RingCat) (hO)⟩).obj (P)).obj (Q)))).hom := by
  have firstAssoc := (congrArg Iso.hom (associator_eq_tensorSheafAssociator O hO M N P)).symm
  have lastAssoc := (congrArg Iso.hom (associator_eq_tensorSheafAssociator O hO N P Q)).symm
  have firstMap := tensorSheafMapIso_refl_right_hom O hO _ Q firstAssoc
  have middleMap := (congrArg Iso.hom (associator_eq_tensorSheafAssociator O hO M
      (@MonoidalCategoryStruct.tensorObj _ _ (Strict.monoidalCategoryStruct O hO) N P) Q)).symm
  have lastMap := tensorSheafMapIso_refl_left_hom O hO M _ lastAssoc
  have rightFirst := (congrArg Iso.hom (associator_eq_tensorSheafAssociator O hO
      (@MonoidalCategoryStruct.tensorObj _ _ (Strict.monoidalCategoryStruct O hO) M N) P Q)).symm
  have rightLast := (congrArg Iso.hom (associator_eq_tensorSheafAssociator O hO M N
      (@MonoidalCategoryStruct.tensorObj _ _ (Strict.monoidalCategoryStruct O hO) P Q))).symm
  exact (congrArg₂ (fun first second => first ≫ second) firstMap (congrArg₂ (fun first second =>
      first ≫ second) middleMap lastMap)).trans
    ((@MonoidalCategory.pentagon _ _ (Strict.monoidalCategory O hO) M N P Q).trans (congrArg₂
      (fun first second => first ≫ second) rightFirst rightLast).symm)

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
  have associatorMap := (congrArg Iso.hom (associator_eq_tensorSheafAssociator O hO M
      (SheafOfModules.unit (TensorSheafification.structureSheaf O hO)) N)).symm
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
      Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj (M)).obj
        (N)))).hom =
      (tensorSheafAssociator O hO
            (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) M
              N).inv ≫
        (TensorPower.tensorSheafMapIso O hO (tensorSheafLeftUnitor O hO M) (Iso.refl N)).hom := by
  have sourceUnit := (congrArg Iso.hom (leftUnitor_eq_tensorSheafLeftUnitor O hO
      (@MonoidalCategoryStruct.tensorObj _ _ (Strict.monoidalCategoryStruct O hO) M N))).symm
  have targetUnit := (congrArg Iso.hom (leftUnitor_eq_tensorSheafLeftUnitor O hO M)).symm
  have associatorMap := (congrArg Iso.inv (associator_eq_tensorSheafAssociator O hO
      (SheafOfModules.unit (TensorSheafification.structureSheaf O hO)) M N)).symm
  have tensorMap := tensorSheafMapIso_refl_right_hom O hO _ N targetUnit
  exact sourceUnit.trans ((@MonoidalCategory.leftUnitor_tensor_hom _ _
      (Strict.monoidalCategory O hO) M N).trans
    (congrArg₂ (fun first second => first ≫ second) associatorMap tensorMap).symm)

/-- **The right-handed counterpart of `tensorSheafLeftUnitor_tensor`.** -/
theorem tensorSheafRightUnitor_tensor
    (M N : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (tensorLeftFunctorObjUnitIso O hO ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O,
      Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj (M)).obj
        (N)))).hom =
      (tensorSheafAssociator O hO M N
            (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
              hO))).hom ≫
        (TensorPower.tensorSheafMapIso O hO (Iso.refl M)
          (tensorLeftFunctorObjUnitIso O hO N)).hom := by
  have sourceUnit := (congrArg Iso.hom (rightUnitor_eq_tensorSheafRightUnitor O hO
      (@MonoidalCategoryStruct.tensorObj _ _ (Strict.monoidalCategoryStruct O hO) M N))).symm
  have targetUnit := (congrArg Iso.hom (rightUnitor_eq_tensorSheafRightUnitor O hO N)).symm
  have associatorMap := (congrArg Iso.hom (associator_eq_tensorSheafAssociator O hO M N
      (SheafOfModules.unit (TensorSheafification.structureSheaf O hO)))).symm
  have tensorMap := tensorSheafMapIso_refl_left_hom O hO M _ targetUnit
  exact sourceUnit.trans ((@MonoidalCategory.rightUnitor_tensor_hom _ _
      (Strict.monoidalCategory O hO) M N).trans
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
  have leftMiddle := (congrArg Iso.hom (braiding_eq_tensorSheafBraiding O hO M
      (@MonoidalCategoryStruct.tensorObj _ _ (Strict.monoidalCategoryStruct O hO) N P))).symm
  have leftLast := (congrArg Iso.hom (associator_eq_tensorSheafAssociator O hO N P M)).symm
  have firstBraid := (congrArg Iso.hom (braiding_eq_tensorSheafBraiding O hO M N)).symm
  have lastBraid := (congrArg Iso.hom (braiding_eq_tensorSheafBraiding O hO M P)).symm
  have rightFirst := tensorSheafMapIso_refl_right_hom O hO _ P firstBraid
  have rightMiddle := (congrArg Iso.hom (associator_eq_tensorSheafAssociator O hO N M P)).symm
  have rightLast := tensorSheafMapIso_refl_left_hom O hO N _ lastBraid
  exact (congrArg₂ (fun first second => first ≫ second) leftFirst (congrArg₂ (fun first second =>
      first ≫ second) leftMiddle leftLast)).trans
    ((@BraidedCategory.hexagon_forward _ _ (Strict.monoidalCategory O hO)
      (Strict.braidedCategory O hO) M N P).trans
      (congrArg₂ (fun first second => first ≫ second) rightFirst (congrArg₂ (fun first second =>
        first ≫ second) rightMiddle rightLast)).symm)

/-- **The reverse hexagon identity for the constraints of the tensor product sheaf.** -/
theorem tensorSheafBraiding_hexagon_reverse
    (M N P : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (tensorSheafAssociator O hO M N P).inv ≫
        (tensorSheafBraiding O hO ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O,
          Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj (M)).obj
            (N)))
          P).hom ≫
          (tensorSheafAssociator O hO P M N).inv =
      (TensorPower.tensorSheafMapIso O hO (Iso.refl M) (tensorSheafBraiding O hO N P)).hom ≫
        (tensorSheafAssociator O hO M P N).inv ≫
          (TensorPower.tensorSheafMapIso O hO
            (tensorSheafBraiding O hO M P) (Iso.refl N)).hom := by
  have leftFirst := (congrArg Iso.inv (associator_eq_tensorSheafAssociator O hO M N P)).symm
  have leftMiddle := (congrArg Iso.hom (braiding_eq_tensorSheafBraiding O hO
      (@MonoidalCategoryStruct.tensorObj _ _ (Strict.monoidalCategoryStruct O hO) M N) P)).symm
  have leftLast := (congrArg Iso.inv (associator_eq_tensorSheafAssociator O hO P M N)).symm
  have firstBraid := (congrArg Iso.hom (braiding_eq_tensorSheafBraiding O hO N P)).symm
  have lastBraid := (congrArg Iso.hom (braiding_eq_tensorSheafBraiding O hO M P)).symm
  have rightFirst := tensorSheafMapIso_refl_left_hom O hO M _ firstBraid
  have rightMiddle := (congrArg Iso.inv (associator_eq_tensorSheafAssociator O hO M P N)).symm
  have rightLast := tensorSheafMapIso_refl_right_hom O hO _ N lastBraid
  exact (congrArg₂ (fun first second => first ≫ second) leftFirst (congrArg₂ (fun first second =>
      first ≫ second) leftMiddle leftLast)).trans
    ((@BraidedCategory.hexagon_reverse _ _ (Strict.monoidalCategory O hO)
      (Strict.braidedCategory O hO) M N P).trans
      (congrArg₂ (fun first second => first ≫ second) rightFirst (congrArg₂ (fun first second =>
        first ≫ second) rightMiddle rightLast)).symm)

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
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O)
          (forget₂
          CommRingCat RingCat) (hO)⟩).obj ((SheafOfModules.unit
          (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)))).obj (M)))
            := by
  apply Iso.ext
  have unitMap := (congrArg Iso.hom (leftUnitor_eq_tensorSheafLeftUnitor O hO M)).symm
  have tensorMap := tensorSheafMapIso_refl_left_hom O hO
    (SheafOfModules.unit (TensorSheafification.structureSheaf O hO)) _ unitMap
  have naturality := (cancel_mono (@MonoidalCategoryStruct.leftUnitor _ _
      (Strict.monoidalCategoryStruct O hO) M).hom).mp
    (@MonoidalCategory.leftUnitor_naturality _ _ (Strict.monoidalCategory O hO) _ _
      (@MonoidalCategoryStruct.leftUnitor _ _ (Strict.monoidalCategoryStruct O hO) M).hom)
  have targetUnit := (congrArg Iso.hom (leftUnitor_eq_tensorSheafLeftUnitor O hO
      (@MonoidalCategoryStruct.tensorObj _ _ (Strict.monoidalCategoryStruct O hO)
      (SheafOfModules.unit (TensorSheafification.structureSheaf O hO)) M))).symm
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
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
        L).IsEquivalence] (n : ℤ) :
    tensorPowerMulIso O hO L 0 n ≪≫ tensorPowerReindex O hO L (Int.zero_add n) =
      ((powFunctorIsoTensorRight O hO L n).app
        (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))).symm
          := by
  have hz : (CategoryTheory.Equivalence.powAdd
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
        L).asEquivalence 0 n
        (0 + n) rfl).app (SheafOfModules.unit
          (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) ≪≫
      tensorPowerReindex O hO L (Int.zero_add n) = Iso.refl _ := by
    rw [tensorPowerReindex_eq_eqToIso]
    have h := Stacks.Equivalence.powAdd_app_cast
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
        L).asEquivalence 0 n n (Int.zero_add n)
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
