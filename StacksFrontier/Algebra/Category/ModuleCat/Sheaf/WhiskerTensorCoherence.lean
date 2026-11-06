module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.WhiskerTensorNaturality

/-!
# Symmetry and unitality of the restriction tensorator

`Stacks.SheafOfModules.TensorPower.map_coherentMulIso_tensorPowerComparison` takes six
normalisations of a tensorator `β M N : R(M ⊗ N) ≅ R M ⊗ R N` as inputs. This file proves three of
them, `Stacks.SheafOfModules.TensorPower.IsSymmetric`,
`Stacks.SheafOfModules.TensorPower.IsLeftUnital` and
`Stacks.SheafOfModules.TensorPower.IsRightUnital`, for the tensorator
`Stacks.SheafOfModules.TensorPower.whiskerTensorator` of restriction
`Stacks.SheafOfModules.TensorPower.whiskerRestriction` along a continuous and cocontinuous functor
of sites `H`.

Restriction of *presheaves* of modules along `H` is Mathlib's monoidal functor
`PresheafOfModules.pushforward₀OfCommRingCat`, whose unit and multiplication constraints are
objectwise identities, so each coherence holds at the presheaf level on local pure tensors by
`rfl`. The sheaf-level normalisations follow by **transporting such an identity through
sheafification**.

## Main definitions

In namespace `Stacks.SheafOfModules.TensorPower`:

* `whiskerSheafifyUnit`: the restricted sheafification unit of an *arbitrary* presheaf of modules,
  with its two local-bijectivity facts. `whiskerTensorUnit` is its value on a tensor product
  presheaf, so the characterizing equation `whiskerTensorSheafIso_hom` applies to it unchanged.

## Main results

In namespace `Stacks.SheafOfModules.TensorPower`:

* `sheafificationUnit_comp_sheafifyDescent`: **the descent step.** A morphism of presheaves of
  modules into a sheaf descends to the sheafification, and the descent agrees with it on the
  sheafification unit. Together with `whiskerSheafifyUnit_comp_map` and
  `whiskerSheafifyUnit_naturality` this is the whole transport calculus.
* `braiding_hom_eq_sheafify_map`, `leftUnitor_hom_eq_sheafify_map` and
  `rightUnitor_hom_eq_sheafify_map`: the three structural constraints of the tensor product sheaf,
  written as the sheafification of the corresponding presheaf constraint (followed, for the two
  unitors, by the counit). These are what make the transport applicable.
* `whiskerPresheafTensorIso_braiding`, `whiskerPresheafTensorIso_leftUnitor` and
  `whiskerPresheafTensorIso_rightUnitor`: **the three coherences at the presheaf level**, each by
  `rfl` on a local pure tensor.
* `isSymmetric_whiskerTensorator`, `isLeftUnital_whiskerTensorator` and
  `isRightUnital_whiskerTensorator`: **the three normalisations.**

## Implementation notes

Each elaboration below stays inside the default heartbeat budget by the following choices.

In namespace `Stacks.SheafOfModules.TensorPower`:

* The reassociations are **term-mode** `CategoryTheory.Category.assoc` chains, not `rw` rewrites by
  it. The source of `whiskerTensorUnit` is a tensor product presheaf read at the
  `Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf` spelling of the indexing
  presheaf of rings while the morphisms out of it are read at the
  `Stacks.SheafOfModules.TensorSheafification.structureSheaf … .obj` spelling; the two are
  definitionally equal, so a term checked by `exact` is accepted, but a `rw` that names the
  intermediate object produces a term which is not type-correct at `implicit` transparency and the
  rewrite is refused.
* `whiskerTensorUnit_hom_ext` passes the two local-bijectivity facts of `whiskerTensorUnit`
  **explicitly**, by `@`-application of
  `Stacks.SheafOfModules.TensorLocalProperties.hom_ext_of_locallyBijective`. They are instances,
  but at a spelling instance search does not bridge, and a `haveI` does not help: the facts have to
  reach the lemma as arguments.
* `whiskerUnitIso` is `CategoryTheory.Iso.refl`, so its `hom` is an identity whose source and
  target are the two definitionally equal spellings
  `(whiskerRestriction O hO H).obj (_root_.SheafOfModules.unit _)` and
  `_root_.SheafOfModules.unit _` over `H.op ⋙ O`. A `rw` by
  `CategoryTheory.MonoidalCategory.id_whiskerRight` therefore does not fire; the degenerate factor
  is cancelled by a term-mode `have` instead, where the defeq is checked once.

## Associativity

The fourth normalisation, `Stacks.SheafOfModules.TensorPower.IsAssociative`, is
`Stacks.SheafOfModules.TensorPower.isAssociative_whiskerTensorator`, in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/WhiskerTensorAssociativity.lean`, together with
`Stacks.SheafOfModules.TensorPower.map_coherentMulIso_whiskerTensorPowerIso`: the comparison of
tensor powers along a restriction is multiplicative.

Its proof needs one comparison layer more than the three here. The associativity constraint of the
tensor product sheaf is `Stacks.SheafOfModules.tensorSheafAssociator`, the sheafified presheaf
associator conjugated by `Stacks.SheafOfModules.tensorSheafAssocLeft` and
`Stacks.SheafOfModules.tensorSheafAssocRight`; the first of those enters **inverted**, so the
transport above does not apply to it directly. The identity is instead precomposed with
`Stacks.SheafOfModules.tensorSheafAssocLeft`, after which the locally bijective presheaf mapping
into the source is `Stacks.SheafOfModules.TensorPower.whiskerSheafifyUnit` at the triple objectwise
tensor product rather than `Stacks.SheafOfModules.TensorPower.whiskerTensorUnit`.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
* [Stacks Project, Tag 02NC](https://stacks.math.columbia.edu/tag/02NC)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory
open Stacks.SheafOfModules.TensorLocalProperties

universe v u v' u' w

namespace Stacks.SheafOfModules.TensorPower

attribute [local instance] Stacks.SheafOfModules.Strict.monoidalCategory
  Stacks.SheafOfModules.Strict.braidedCategory
  Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

/-- **The counit of sheafification undoes the sheafification unit on a sheaf.** This is the
right triangle identity of the sheafification adjunction. -/
public theorem sheafificationUnit_comp_sheafifyValIso
    (M : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    sheafificationUnit (R := Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)
          M.val ≫
        (Stacks.SheafOfModules.sheafifyValIso O hO M).hom.val = 𝟙 M.val :=
  (Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction O hO).right_triangle_components M

/-- **Descent along the sheafification unit.** A morphism of presheaves of modules into a sheaf
descends to the sheafification, and the descent agrees with it on the sheafification unit. -/
public theorem sheafificationUnit_comp_sheafifyDescent
    {P : PresheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj}
    {M : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)} (f : P ⟶ M.val) :
    sheafificationUnit (R := Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) P ≫
        ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map f ≫
          (Stacks.SheafOfModules.sheafifyValIso O hO M).hom).val = f :=
  ((Category.assoc (sheafificationUnit
        (R := Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) P)
      ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map f).val
      (Stacks.SheafOfModules.sheafifyValIso O hO M).hom.val).symm.trans
    ((congrArg (· ≫ (Stacks.SheafOfModules.sheafifyValIso O hO M).hom.val)
        (Stacks.SheafOfModules.TensorSheafification.sheafificationUnit_naturality_structureSheaf
          O hO f)).trans
      ((Category.assoc f _ _).trans
        ((congrArg (f ≫ ·) (sheafificationUnit_comp_sheafifyValIso O hO M)).trans
          (Category.comp_id f)))))

/-- The symmetry constraint of the tensor product sheaf is the sheafification of the braiding of
the underlying presheaves of modules. -/
public theorem braiding_hom_eq_sheafify_map
    (M N : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (β_ M N).hom =
      (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map (β_ M.val N.val).hom := by
  rw [Stacks.SheafOfModules.braiding_eq_tensorSheafBraiding]
  rfl

/-- The left unit constraint of the tensor product sheaf is the sheafification of the left
unitor of the underlying presheaves of modules, followed by the counit. -/
public theorem leftUnitor_hom_eq_sheafify_map
    (M : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (λ_ M).hom =
      (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map (λ_ M.val).hom ≫
        (Stacks.SheafOfModules.sheafifyValIso O hO M).hom := by
  rw [Stacks.SheafOfModules.leftUnitor_eq_tensorSheafLeftUnitor]
  rfl

/-- The right unit constraint of the tensor product sheaf is the sheafification of the right
unitor of the underlying presheaves of modules, followed by the counit. -/
public theorem rightUnitor_hom_eq_sheafify_map
    (M : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (Stacks.SheafOfModules.tensorLeftFunctorObjUnitIso O hO M).hom =
      (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map (ρ_ M.val).hom ≫
        (Stacks.SheafOfModules.sheafifyValIso O hO M).hom :=
  rfl

section Whisker

variable {C' : Type u'} [Category.{v'} C'] {J' : GrothendieckTopology C'}
  (H : C' ⥤ C) [H.IsContinuous J' J] [H.IsCocontinuous J' J]
  [J'.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J' AddCommGrpCat.{w}]

/-- The restricted sheafification unit of an arbitrary presheaf of modules. -/
public noncomputable def whiskerSheafifyUnit
    (P : PresheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj) :
    ((whiskerPresheafRestriction O H).obj P :
        PresheafOfModules.{w}
          (Stacks.SheafOfModules.TensorSheafification.structureSheaf (H.op ⋙ O)
            (whiskerStructureIsSheaf (J' := J') O hO H)).obj) ⟶
      ((whiskerRestriction (J' := J') O hO H).obj
        ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj P)).val :=
  (whiskerPresheafRestriction O H).map
    (sheafificationUnit (R := Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) P)

/-- The restricted sheafification unit is locally injective for the smaller topology. -/
public instance isLocallyInjective_whiskerSheafifyUnit
    (P : PresheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj) :
    PresheafOfModules.IsLocallyInjective J' (whiskerSheafifyUnit (J' := J') O hO H P) := by
  have h : PresheafOfModules.IsLocallyInjective J
      (sheafificationUnit
        (R := Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) P) :=
    inferInstanceAs (Presheaf.IsLocallyInjective J (CategoryTheory.toSheafify J P.presheaf))
  exact Presheaf.isLocallyInjective_whisker J' J H
    ((PresheafOfModules.toPresheaf
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj).map
        (sheafificationUnit
          (R := Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) P))

/-- The restricted sheafification unit is locally surjective for the smaller topology. -/
public instance isLocallySurjective_whiskerSheafifyUnit
    (P : PresheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj) :
    PresheafOfModules.IsLocallySurjective J' (whiskerSheafifyUnit (J' := J') O hO H P) := by
  have h : PresheafOfModules.IsLocallySurjective J
      (sheafificationUnit
        (R := Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) P) :=
    inferInstanceAs (Presheaf.IsLocallySurjective J (CategoryTheory.toSheafify J P.presheaf))
  exact Presheaf.isLocallySurjective_whisker J' J H
    ((PresheafOfModules.toPresheaf
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj).map
        (sheafificationUnit
          (R := Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) P))

omit [H.IsCocontinuous J' J] [J'.WEqualsLocallyBijective AddCommGrpCat]
  [HasWeakSheafify J' AddCommGrpCat] in
/-- On a tensor product presheaf the restricted sheafification unit is the comparison
`whiskerTensorUnit` the characterizing equation of the restriction tensorator is stated with. -/
public theorem whiskerSheafifyUnit_tensorPresheaf
    (M N : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    whiskerSheafifyUnit (J' := J') O hO H
        ((PresheafOfModules.tensorObj (O := O) (M.val) (N.val))) =
      whiskerTensorUnit (J' := J') O hO H M N := rfl

omit [H.IsCocontinuous J' J] [J'.WEqualsLocallyBijective AddCommGrpCat]
  [HasWeakSheafify J' AddCommGrpCat] in
/-- **The descent step, restricted along `H`.** A morphism of presheaves of modules into a sheaf
descends to the sheafification, and the restriction of that descent, read on the restricted
sheafification unit, is the restriction of the morphism. -/
public theorem whiskerSheafifyUnit_comp_map
    {P : PresheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj}
    {M : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)} (f : P ⟶ M.val) :
    whiskerSheafifyUnit (J' := J') O hO H P ≫
        ((whiskerRestriction (J' := J') O hO H).map
          ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map f ≫
            (Stacks.SheafOfModules.sheafifyValIso O hO M).hom)).val =
      (whiskerPresheafRestriction O H).map f :=
  ((whiskerPresheafRestriction O H).map_comp
      (sheafificationUnit
        (R := Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) P)
      (((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map f ≫
        (Stacks.SheafOfModules.sheafifyValIso O hO M).hom)).val).symm.trans
    (congrArg (whiskerPresheafRestriction O H).map (sheafificationUnit_comp_sheafifyDescent O hO f))

omit [H.IsCocontinuous J' J] [J'.WEqualsLocallyBijective AddCommGrpCat]
  [HasWeakSheafify J' AddCommGrpCat] in
/-- The restricted sheafification unit is natural. -/
public theorem whiskerSheafifyUnit_naturality
    {P Q : PresheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj} (g : P ⟶ Q) :
    whiskerSheafifyUnit (J' := J') O hO H P ≫
        ((whiskerRestriction (J' := J') O hO H).map
          ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map g)).val =
      (whiskerPresheafRestriction O H).map g ≫ whiskerSheafifyUnit (J' := J') O hO H Q :=
  ((whiskerPresheafRestriction O H).map_comp _ _).symm.trans
    ((congrArg (whiskerPresheafRestriction O H).map
        (Stacks.SheafOfModules.TensorSheafification.sheafificationUnit_naturality_structureSheaf
          O hO g)).trans
      ((whiskerPresheafRestriction O H).map_comp _ _))

omit [J.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify J AddCommGrpCat] in
/-- **The restriction tensorator is compatible with the symmetry constraint at the level of
presheaves.** Restriction of presheaves of modules along `H` is objectwise, and so is the
braiding, so the identity holds on local pure tensors by `rfl`. -/
@[reassoc]
public theorem whiskerPresheafTensorIso_braiding
    (M N : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (whiskerPresheafRestriction O H).map (β_ M.val N.val).hom ≫
        (whiskerPresheafTensorIso O hO H N M).hom =
      (whiskerPresheafTensorIso O hO H M N).hom ≫
        (β_ ((whiskerPresheafRestriction O H).obj M.val)
          ((whiskerPresheafRestriction O H).obj N.val)).hom := by
  ext1 X
  let : CommRing ((H.op ⋙ O ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj X) :=
    inferInstanceAs (CommRing ((O ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj (H.op.obj X)))
  exact ModuleCat.MonoidalCategory.tensor_ext fun _ _ => rfl

omit [J'.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify J' AddCommGrpCat] in
/-- Two morphisms out of the restriction of a tensor product sheaf agreeing on the restricted
sheafification unit are equal. The two local-bijectivity facts are supplied by hand: they are
instances, but stated at the `whiskerPresheafRestriction` spelling of the indexing presheaf of
rings, which instance search does not bridge. -/
public theorem whiskerTensorUnit_hom_ext
    (M N : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    {X : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf (H.op ⋙ O)
        (whiskerStructureIsSheaf (J' := J') O hO H))}
    {a b : (whiskerRestriction (J' := J') O hO H).obj
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
            (M)).obj (N))) ⟶ X}
    (h : whiskerTensorUnit (J' := J') O hO H M N ≫ a.val =
      whiskerTensorUnit (J' := J') O hO H M N ≫ b.val) : a = b :=
  @hom_ext_of_locallyBijective _ _ J' _ _ _ _ _
    (isLocallyInjective_whiskerTensorUnit (J' := J') O hO H M N)
    (isLocallySurjective_whiskerTensorUnit (J' := J') O hO H M N) _ _ h

/-- The restriction tensorator in the spelling its characterizing equation is stated in. -/
public theorem whiskerTensorator_eq_whiskerTensorSheafIso
    (M N : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    whiskerTensorator (J' := J') O hO H M N = whiskerTensorSheafIso (J' := J') O hO H M N := rfl

omit [H.IsCocontinuous J' J] [J'.WEqualsLocallyBijective AddCommGrpCat]
  [HasWeakSheafify J' AddCommGrpCat] in
/-- **The symmetry constraint of the tensor product sheaf, read on the restricted sheafification
unit.** The transport of `whiskerSheafifyUnit_naturality` to the braiding; a separate declaration
because the comparison of the two spellings of the objectwise tensor product it forces is checked
once here rather than inside `isSymmetric_whiskerTensorator`. -/
public theorem whiskerTensorUnit_comp_braiding
    (M N : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    whiskerTensorUnit (J' := J') O hO H M N ≫
        ((whiskerRestriction (J' := J') O hO H).map (β_ M N).hom).val =
      (whiskerPresheafRestriction O H).map (β_ M.val N.val).hom ≫
        whiskerTensorUnit (J' := J') O hO H N M := by
  rw [braiding_hom_eq_sheafify_map O hO M N]
  exact whiskerSheafifyUnit_naturality O hO H (β_ M.val N.val).hom

set_option maxHeartbeats 1600000 in
omit [J.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify J AddCommGrpCat]
  [H.IsCocontinuous J' J] in
/-- **The symmetry constraint formed on the smaller site, read on its sheafification unit**, the
mirror of `whiskerTensorUnit_comp_braiding` for the second of the two locally bijective
morphisms entering the restriction tensorator. -/
public theorem whiskerTensorUnit'_comp_braiding
    (M N : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    whiskerTensorUnit' (J' := J') O hO H M N ≫
        ((β_ ((whiskerRestriction (J' := J') O hO H).obj M)
          ((whiskerRestriction (J' := J') O hO H).obj N)).hom).val =
      (β_ ((whiskerPresheafRestriction O H).obj M.val)
          ((whiskerPresheafRestriction O H).obj N.val)).hom ≫
        whiskerTensorUnit' (J' := J') O hO H N M := by
  rw [braiding_hom_eq_sheafify_map (H.op ⋙ O)
    (whiskerStructureIsSheaf (J' := J') O hO H)
    ((whiskerRestriction (J' := J') O hO H).obj M)
    ((whiskerRestriction (J' := J') O hO H).obj N)]
  exact
    Stacks.SheafOfModules.TensorSheafification.sheafificationUnit_naturality_structureSheaf
      (H.op ⋙ O) (whiskerStructureIsSheaf (J' := J') O hO H)
      (β_ ((whiskerRestriction (J' := J') O hO H).obj M).val
        ((whiskerRestriction (J' := J') O hO H).obj N).val).hom

set_option maxHeartbeats 1600000 in
omit [J.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify J AddCommGrpCat]
  [H.IsCocontinuous J' J] in
/-- **The sheafification unit of the objectwise tensor product with the unit on the left**, in the
spelling the descent step is stated in. The two spellings of the restricted unit are definitionally
equal, and this is where that is checked: a separate declaration because the check and the
statement of `whiskerTensorUnit'_comp_leftUnitor` do not fit in one heartbeat budget together. -/
public theorem whiskerTensorUnit'_unit_left
    (M : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    whiskerTensorUnit' (J' := J') O hO H
        (_root_.SheafOfModules.unit
          (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) M =
      sheafificationUnit
        (R := Stacks.SheafOfModules.TensorSheafification.structureSheaf (H.op ⋙ O)
          (whiskerStructureIsSheaf (J' := J') O hO H))
        (PresheafOfModulesOfCommRing.Monoidal.tensorObj
          (PresheafOfModules.unit
            (Stacks.SheafOfModules.TensorSheafification.structureSheaf (H.op ⋙ O)
              (whiskerStructureIsSheaf (J' := J') O hO H)).obj)
          ((whiskerRestriction (J' := J') O hO H).obj M).val) := rfl

set_option maxHeartbeats 1600000 in
omit [J.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify J AddCommGrpCat]
  [H.IsCocontinuous J' J] in
/-- **The sheafification unit of the objectwise tensor product with the unit on the right**, the
mirror of `whiskerTensorUnit'_unit_left`. -/
public theorem whiskerTensorUnit'_unit_right
    (M : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    whiskerTensorUnit' (J' := J') O hO H M
        (_root_.SheafOfModules.unit
          (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) =
      sheafificationUnit
        (R := Stacks.SheafOfModules.TensorSheafification.structureSheaf (H.op ⋙ O)
          (whiskerStructureIsSheaf (J' := J') O hO H))
        (PresheafOfModulesOfCommRing.Monoidal.tensorObj
          ((whiskerRestriction (J' := J') O hO H).obj M).val
          (PresheafOfModules.unit
            (Stacks.SheafOfModules.TensorSheafification.structureSheaf (H.op ⋙ O)
              (whiskerStructureIsSheaf (J' := J') O hO H)).obj)) := rfl

/-- The restriction tensorator followed by a morphism `g`, read on the restricted sheafification
unit: the characterizing equation `whiskerTensorSheafIso_hom` with `g` appended. -/
private theorem whiskerTensorUnit_comp_tensorator_hom_comp
    (M N : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    {Y : PresheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf (H.op ⋙ O)
        (whiskerStructureIsSheaf (J' := J') O hO H)).obj}
    (g : ((whiskerRestriction (J' := J') O hO H).obj M ⊗
      (whiskerRestriction (J' := J') O hO H).obj N).val ⟶ Y) :
    whiskerTensorUnit (J' := J') O hO H M N ≫
        (whiskerTensorator (J' := J') O hO H M N).hom.val ≫ g =
      (whiskerPresheafTensorIso O hO H M N).hom ≫ whiskerTensorUnit' (J' := J') O hO H M N ≫
        g :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ g) (whiskerTensorSheafIso_hom O hO H M N)).trans (Category.assoc _ _ _))

/-- **The restriction tensorator is compatible with the symmetry constraint of Tag 01CA**: one of
the four normalisations of `map_coherentMulIso_tensorPowerComparison` that were missing for
restriction along a continuous and cocontinuous functor of sites. -/
public theorem isSymmetric_whiskerTensorator :
    IsSymmetric (K := J') O hO (H.op ⋙ O) (whiskerStructureIsSheaf (J' := J') O hO H)
      (whiskerRestriction O hO H) (whiskerTensorator (J' := J') O hO H) := by
  intro M N
  refine whiskerTensorUnit_hom_ext O hO H M N ?_
  refine ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _)
    (whiskerTensorUnit_comp_braiding (J' := J') O hO H M N)).trans ((Category.assoc _ _ _).trans
      (congrArg (_ ≫ ·) (whiskerTensorSheafIso_hom O hO H N M))))).trans
    (Eq.trans ?_ (whiskerTensorUnit_comp_tensorator_hom_comp O hO H M N
      (β_ ((whiskerRestriction (J' := J') O hO H).obj M)
        ((whiskerRestriction (J' := J') O hO H).obj N)).hom.val).symm)
  exact (whiskerPresheafTensorIso_braiding_assoc O hO H M N _).trans
    (congrArg (_ ≫ ·) (whiskerTensorUnit'_comp_braiding (J' := J') O hO H M N).symm)

omit [J.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify J AddCommGrpCat] in
/-- **The restriction tensorator is compatible with the left unit constraint at the level of
presheaves.** Both constraints are objectwise scalar multiplication, and the comparison of the
objectwise tensor products is the identity, so this holds on local pure tensors by `rfl`. -/
@[reassoc]
public theorem whiskerPresheafTensorIso_leftUnitor
    (M : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (whiskerPresheafRestriction O H).map (λ_ M.val).hom =
      (whiskerPresheafTensorIso O hO H
          (_root_.SheafOfModules.unit
            (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) M).hom ≫
        (λ_ ((whiskerPresheafRestriction O H).obj M.val)).hom := by
  ext1 X
  let : CommRing ((H.op ⋙ O ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj X) :=
    inferInstanceAs (CommRing ((O ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj (H.op.obj X)))
  exact ModuleCat.MonoidalCategory.tensor_ext fun _ _ => rfl

omit [J.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify J AddCommGrpCat] in
/-- **The restriction tensorator is compatible with the right unit constraint at the level of
presheaves**, the mirror of `whiskerPresheafTensorIso_leftUnitor`. -/
@[reassoc]
public theorem whiskerPresheafTensorIso_rightUnitor
    (M : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (whiskerPresheafRestriction O H).map (ρ_ M.val).hom =
      (whiskerPresheafTensorIso O hO H M
          (_root_.SheafOfModules.unit
            (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))).hom ≫
        (ρ_ ((whiskerPresheafRestriction O H).obj M.val)).hom := by
  ext1 X
  let : CommRing ((H.op ⋙ O ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj X) :=
    inferInstanceAs (CommRing ((O ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj (H.op.obj X)))
  exact ModuleCat.MonoidalCategory.tensor_ext fun _ _ => rfl

omit [H.IsCocontinuous J' J] [J'.WEqualsLocallyBijective AddCommGrpCat]
  [HasWeakSheafify J' AddCommGrpCat] in
/-- **The left unit constraint of the tensor product sheaf, read on the restricted sheafification
unit**, by the descent step. A separate declaration for the reason given for
`whiskerTensorUnit_comp_braiding`. -/
public theorem whiskerTensorUnit_comp_leftUnitor
    (M : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    whiskerTensorUnit (J' := J') O hO H
          (_root_.SheafOfModules.unit
            (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) M ≫
        ((whiskerRestriction (J' := J') O hO H).map (λ_ M).hom).val =
      (whiskerPresheafRestriction O H).map (λ_ M.val).hom := by
  rw [leftUnitor_hom_eq_sheafify_map O hO M]
  exact whiskerSheafifyUnit_comp_map O hO H (λ_ M.val).hom

omit [J.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify J AddCommGrpCat]
  [H.IsCocontinuous J' J] in
/-- **The left unit constraint formed on the smaller site, read on its sheafification unit**, the
mirror of `whiskerTensorUnit_comp_leftUnitor`. -/
public theorem whiskerTensorUnit'_comp_leftUnitor
    (M : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    whiskerTensorUnit' (J' := J') O hO H
          (_root_.SheafOfModules.unit
            (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) M ≫
        ((λ_ ((whiskerRestriction (J' := J') O hO H).obj M)).hom).val =
      (λ_ ((whiskerPresheafRestriction O H).obj M.val)).hom := by
  rw [leftUnitor_hom_eq_sheafify_map (H.op ⋙ O) (whiskerStructureIsSheaf (J' := J') O hO H)
    ((whiskerRestriction (J' := J') O hO H).obj M),
    whiskerTensorUnit'_unit_left (J' := J') O hO H M]
  exact sheafificationUnit_comp_sheafifyDescent (H.op ⋙ O)
    (whiskerStructureIsSheaf (J' := J') O hO H)
    (M := (whiskerRestriction (J' := J') O hO H).obj M)
    (λ_ ((whiskerRestriction (J' := J') O hO H).obj M).val).hom

/-- **The restriction tensorator is compatible with the left unit constraint of Tag 01CA**: a
second of the four normalisations of `map_coherentMulIso_tensorPowerComparison` that were missing
for restriction along a continuous and cocontinuous functor of sites. -/
public theorem isLeftUnital_whiskerTensorator :
    IsLeftUnital (K := J') O hO (H.op ⋙ O) (whiskerStructureIsSheaf (J' := J') O hO H)
      (whiskerRestriction O hO H) (whiskerTensorator (J' := J') O hO H)
      (whiskerUnitIso (J' := J') O hO H) := by
  intro M
  have hid : (whiskerUnitIso (J' := J') O hO H).hom ▷
        (whiskerRestriction (J' := J') O hO H).obj M ≫
      (λ_ ((whiskerRestriction (J' := J') O hO H).obj M)).hom =
    (λ_ ((whiskerRestriction (J' := J') O hO H).obj M)).hom :=
    (congrArg (fun z => z ≫ (λ_ ((whiskerRestriction (J' := J') O hO H).obj M)).hom)
        (MonoidalCategory.id_whiskerRight
          ((whiskerRestriction (J' := J') O hO H).obj
            (_root_.SheafOfModules.unit
              (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)))
          ((whiskerRestriction (J' := J') O hO H).obj M))).trans
      (Category.id_comp (λ_ ((whiskerRestriction (J' := J') O hO H).obj M)).hom)
  have hL := whiskerTensorUnit_comp_leftUnitor (J' := J') O hO H M
  have hR := whiskerTensorUnit'_comp_leftUnitor (J' := J') O hO H M
  refine Eq.trans ?_ (congrArg
    (fun z => (whiskerTensorator (J' := J') O hO H
      (_root_.SheafOfModules.unit
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) M).hom ≫ z) hid).symm
  refine whiskerTensorUnit_hom_ext O hO H
    (_root_.SheafOfModules.unit
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) M ?_
  refine hL.trans (Eq.trans ?_ ((whiskerTensorUnit_comp_tensorator_hom_comp O hO H
    (_root_.SheafOfModules.unit
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) M
    (λ_ ((whiskerRestriction (J' := J') O hO H).obj M)).hom.val).trans
      (congrArg (_ ≫ ·) hR)).symm)
  exact whiskerPresheafTensorIso_leftUnitor O hO H M

omit [H.IsCocontinuous J' J] [J'.WEqualsLocallyBijective AddCommGrpCat]
  [HasWeakSheafify J' AddCommGrpCat] in
/-- **The right unit constraint of the tensor product sheaf, read on the restricted sheafification
unit**, by the descent step. A separate declaration for the reason given for
`whiskerTensorUnit_comp_braiding`. -/
public theorem whiskerTensorUnit_comp_rightUnitor
    (M : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    whiskerTensorUnit (J' := J') O hO H M
          (_root_.SheafOfModules.unit
            (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) ≫
        ((whiskerRestriction (J' := J') O hO H).map
          (Stacks.SheafOfModules.tensorLeftFunctorObjUnitIso O hO M).hom).val =
      (whiskerPresheafRestriction O H).map (ρ_ M.val).hom := by
  rw [rightUnitor_hom_eq_sheafify_map O hO M]
  exact whiskerSheafifyUnit_comp_map O hO H (ρ_ M.val).hom

omit [J.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify J AddCommGrpCat]
  [H.IsCocontinuous J' J] in
/-- **The right unit constraint formed on the smaller site, read on its sheafification unit**, the
mirror of `whiskerTensorUnit_comp_rightUnitor`. -/
public theorem whiskerTensorUnit'_comp_rightUnitor
    (M : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    whiskerTensorUnit' (J' := J') O hO H M
          (_root_.SheafOfModules.unit
            (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) ≫
        ((Stacks.SheafOfModules.tensorLeftFunctorObjUnitIso (H.op ⋙ O)
          (whiskerStructureIsSheaf (J' := J') O hO H)
          ((whiskerRestriction (J' := J') O hO H).obj M)).hom).val =
      (ρ_ ((whiskerPresheafRestriction O H).obj M.val)).hom := by
  rw [rightUnitor_hom_eq_sheafify_map (H.op ⋙ O) (whiskerStructureIsSheaf (J' := J') O hO H)
    ((whiskerRestriction (J' := J') O hO H).obj M),
    whiskerTensorUnit'_unit_right (J' := J') O hO H M]
  exact sheafificationUnit_comp_sheafifyDescent (H.op ⋙ O)
    (whiskerStructureIsSheaf (J' := J') O hO H)
    (M := (whiskerRestriction (J' := J') O hO H).obj M)
    (ρ_ ((whiskerRestriction (J' := J') O hO H).obj M).val).hom

/-- **The restriction tensorator is compatible with the right unit constraint of Tag 01CA**: a
third of the four normalisations of `map_coherentMulIso_tensorPowerComparison` that were missing
for restriction along a continuous and cocontinuous functor of sites. -/
public theorem isRightUnital_whiskerTensorator :
    IsRightUnital (K := J') O hO (H.op ⋙ O) (whiskerStructureIsSheaf (J' := J') O hO H)
      (whiskerRestriction O hO H) (whiskerTensorator (J' := J') O hO H)
      (whiskerUnitIso (J' := J') O hO H) := by
  intro M
  have hid : (Stacks.SheafOfModules.TensorPower.tensorSheafMapIso (H.op ⋙ O)
    (whiskerStructureIsSheaf (J' := J') O hO H)
        (Iso.refl ((whiskerRestriction (J' := J') O hO H).obj M))
        (whiskerUnitIso (J' := J') O hO H)).hom ≫
      (Stacks.SheafOfModules.tensorLeftFunctorObjUnitIso (H.op ⋙ O)
        (whiskerStructureIsSheaf (J' := J') O hO H)
        ((whiskerRestriction (J' := J') O hO H).obj M)).hom =
    (Stacks.SheafOfModules.tensorLeftFunctorObjUnitIso (H.op ⋙ O)
      (whiskerStructureIsSheaf (J' := J') O hO H)
      ((whiskerRestriction (J' := J') O hO H).obj M)).hom :=
    (congrArg (fun z => z ≫ (Stacks.SheafOfModules.tensorLeftFunctorObjUnitIso (H.op ⋙ O)
      (whiskerStructureIsSheaf (J' := J') O hO H)
          ((whiskerRestriction (J' := J') O hO H).obj M)).hom)
        ((Stacks.SheafOfModules.tensorSheafMapIso_hom_eq (H.op ⋙ O)
          (whiskerStructureIsSheaf (J' := J') O hO H)
            (Iso.refl ((whiskerRestriction (J' := J') O hO H).obj M))
            (whiskerUnitIso (J' := J') O hO H)).trans
          (MonoidalCategory.id_tensorHom_id ((whiskerRestriction (J' := J') O hO H).obj M)
            ((whiskerRestriction (J' := J') O hO H).obj
              (_root_.SheafOfModules.unit
              (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)))))).trans
      (Category.id_comp _)
  have hL := whiskerTensorUnit_comp_rightUnitor (J' := J') O hO H M
  have hR := whiskerTensorUnit'_comp_rightUnitor (J' := J') O hO H M
  refine Eq.trans ?_ (congrArg
    (fun z => (whiskerTensorator (J' := J') O hO H M
      (_root_.SheafOfModules.unit
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))).hom ≫ z) hid).symm
  refine whiskerTensorUnit_hom_ext O hO H M
    (_root_.SheafOfModules.unit
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) ?_
  refine hL.trans (Eq.trans ?_ ((whiskerTensorUnit_comp_tensorator_hom_comp O hO H M
    (_root_.SheafOfModules.unit
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    (Stacks.SheafOfModules.tensorLeftFunctorObjUnitIso (H.op ⋙ O)
      (whiskerStructureIsSheaf (J' := J') O hO H)
        ((whiskerRestriction (J' := J') O hO H).obj M)).hom.val).trans
      (congrArg (_ ≫ ·) hR)).symm)
  exact whiskerPresheafTensorIso_rightUnitor O hO H M

end Whisker

end Stacks.SheafOfModules.TensorPower

end
