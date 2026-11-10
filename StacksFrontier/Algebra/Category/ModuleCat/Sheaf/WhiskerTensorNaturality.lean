module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerMapMultiplication
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafOverSlice

/-!
# Naturality of the restriction tensorator, in the form the multiplicativity statement uses

`Stacks.SheafOfModules.TensorPower.map_coherentMulIso_tensorPowerComparison` is the statement
that the comparison `R(L^{⊗ n}) ≅ (R L)^{⊗ n}` of tensor powers along a functor `R` carries the
coherent multiplication of Tag 01CU for `L` to the one for `R L`. It takes six normalisations of
the tensorator `β M N : R(M ⊗ N) ≅ R M ⊗ R N` as explicit inputs — `IsNaturalLeft`,
`IsNaturalRight`, `IsLeftUnital`, `IsRightUnital`, `IsAssociative` and `IsSymmetric` — and they are
instantiated for the pullback along a morphism of ringed spaces in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorPowerPullbackMultiplication.lean`.

This file supplies **two of the six for restriction along a continuous and cocontinuous functor
of sites**, `Stacks.SheafOfModules.TensorPower.whiskerRestriction`, whose slice case is the
comparison `Stacks.SheafOfModules.TensorPower.overTensorPowerIso` used by
`Stacks.SheafOfModules.TensorPower.overTensorPowerUnitIso`.

## Main definitions

* `Stacks.SheafOfModules.TensorPower.whiskerTensorator`: the tensorator of restriction along a
  functor of sites, in **both** slots. `whiskerTensorComparison` is its restriction to the first
  slot with the second fixed, which is the one-slot form `mapTensorPowerIso` consumes; the six
  normalisations are stated for the two-slot form, so it has to be named.

## Main results

* `Stacks.SheafOfModules.TensorPower.tensorSheafMap_id_right_eq_whiskerRight` and
  `tensorSheafMap_id_left_eq_whiskerLeft`: **the vocabulary bridge.** Tensoring a morphism with
  an identity is whiskering, in the strict monoidal structure of Tag 01CA. The naturality of the
  restriction tensorator is proved in the `tensorSheafMap` vocabulary and the normalisations are
  stated in the `▷`/`◁` vocabulary, and nothing connected the two.
* `Stacks.SheafOfModules.TensorPower.isNaturalLeft_whiskerTensorator` and
  `isNaturalRight_whiskerTensorator`: **two of the six normalisations**, for restriction along an
  arbitrary continuous and cocontinuous functor of sites, hence in particular for a slice.
* `Stacks.SheafOfModules.TensorPower.tensorPowerComparison_whiskerTensorator`: the comparison
  that the six normalisations are about **is** `whiskerTensorPowerIso`, hence
  `overTensorPowerIso` in the slice case. So no further identification is needed: supplying the
  remaining four normalisations is the whole of what is left.

## Implementation notes

Both naturality statements come from `whiskerTensorSheafIso_naturality_left` and
`_naturality_right` with the bridge applied three times — once on the left-hand side, and once
on each factor of the right-hand side after `CategoryTheory.Functor.map_id` turns the restricted
identity into an identity.

The bridge itself is `Stacks.SheafOfModules.whiskerRight_eq_sheafify_map` together with
`MonoidalCategory.tensorHom_id` at the level of presheaves of modules: both sides are the
sheafification of a morphism of presheaves, and there the two spellings agree by a monoidal
identity. The presheaf-level monoidal structure therefore has to be a local instance, as it is
wherever this calculus is used.

## Where the other four are

`IsLeftUnital`, `IsRightUnital` and `IsSymmetric` are proved in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/WhiskerTensorCoherence.lean`, and `IsAssociative`
in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/WhiskerTensorAssociativity.lean`, which also draws
the conclusion all six were collected for:
`Stacks.SheafOfModules.TensorPower.map_coherentMulIso_whiskerTensorPowerIso`, multiplicativity of
the comparison of tensor powers along a restriction, hence of `overTensorPowerIso` in the slice
case.

The route is not new coherence theory. Restriction of *presheaves* of modules along `H` is already
a monoidal functor
— `Stacks.SheafOfModules.TensorPower.whiskerPresheafRestriction` is
`PresheafOfModules.pushforward₀OfCommRingCat`, and `whiskerPresheafTensorIso` is its
multiplication constraint — so all four coherences are available at the presheaf level, and what
has to be supplied is their transport through sheafification to `whiskerTensorSheafIso`, which
is pinned by the characterising equation `whiskerTensorSheafIso_hom`. No
`CategoryTheory.Functor.Braided` instance for any restriction of sheaves of modules exists, and
none is needed: the braided identity for `whiskerPresheafRestriction` holds objectwise on local
pure tensors, so `IsSymmetric` is reached without one.

A separate route for the slice case alone would be
`Stacks.SheafOfModules.SliceRestriction.overFunctorStrictMonoidal`, a genuine monoidal-functor
instance, which would give five of the six for *its own* tensorator; it needs two identifications
that do not exist, of `whiskerRestriction O hO (Over.forget U)` with
`SheafOfModules.overFunctor` and of `whiskerTensorSheafIso` with
`Stacks.SheafOfModules.SliceRestriction.tensorSheafOver`, the second being the comparison whose
value on a local section is recorded as inaccessible in
`StacksFrontier/AlgebraicGeometry/TensorPowerTrivialize/GeneralModule.lean`.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 02NC](https://stacks.math.columbia.edu/tag/02NC)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

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

/-! ### The vocabulary bridge: tensoring with an identity is whiskering -/

/-- **Tensoring a morphism with the identity of a fixed second factor is right whiskering**, in
the strict monoidal structure of Tag 01CA. Both sides are the sheafification of a morphism of
presheaves of modules, where the two spellings agree by `MonoidalCategory.tensorHom_id`. -/
public theorem tensorSheafMap_id_right_eq_whiskerRight
    {M M' : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)}
    (u : M ⟶ M')
    (N : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩)).map
      ((u, (𝟙 N)) : (_, _) ⟶ (_, _))) = u ▷ N :=
  (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map.{u, v, w, w, w}
      (R := ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩)
      u (𝟙 N)).trans
    ((congrArg (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map
        (MonoidalCategory.tensorHom_id u.val N.val)).trans
      (Stacks.SheafOfModules.whiskerRight_eq_sheafify_map O hO u N).symm)

/-- **Tensoring the identity of a fixed first factor with a morphism is left whiskering**, the
mirror of `tensorSheafMap_id_right_eq_whiskerRight`. -/
public theorem tensorSheafMap_id_left_eq_whiskerLeft
    (M : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    {N N' : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)}
    (v : N ⟶ N') :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩)).map
      (((𝟙 M), v) : (_, _) ⟶ (_, _))) = M ◁ v :=
  (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map.{u, v, w, w, w}
      (R := ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩)
      (𝟙 M) v).trans
    ((congrArg (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map
        (MonoidalCategory.id_tensorHom M.val v.val)).trans
      (Stacks.SheafOfModules.whiskerLeft_eq_sheafify_map O hO M v).symm)

/-! ### Two of the six normalisations, for restriction along a functor of sites -/

section Whisker

variable {C' : Type u'} [Category.{v'} C'] {J' : GrothendieckTopology C'}
  (H : C' ⥤ C) [H.IsContinuous J' J] [H.IsCocontinuous J' J]
  [J'.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J' AddCommGrpCat.{w}]

/-- **The tensorator of restriction along a functor of sites, in both slots.**
`Stacks.SheafOfModules.TensorPower.whiskerTensorComparison` is this with the second slot fixed,
which is the form `mapTensorPowerIso` consumes; the six normalisations of
`map_coherentMulIso_tensorPowerComparison` are stated for the two-slot form. -/
public def whiskerTensorator (M N : _root_.SheafOfModules.{w}
    (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (whiskerRestriction (J' := J') O hO H).obj
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
            (M)).obj (N))) ≅
      (((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨(H.op ⋙ O), Presheaf.isSheaf_of_isSheaf_comp _ ((H.op ⋙ O))
            (forget₂ CommRingCat RingCat) ((whiskerStructureIsSheaf (J' := J') O hO H))⟩).obj
          (((whiskerRestriction (J' := J') O hO H).obj M))).obj
        (((whiskerRestriction (J' := J') O hO H).obj N))) :=
  whiskerTensorSheafIso (J' := J') O hO H M N

/-- **Naturality of the restriction tensorator in its first slot**, in the whiskering vocabulary
the normalisations of `map_coherentMulIso_tensorPowerComparison` are stated in. -/
public theorem isNaturalLeft_whiskerTensorator :
    IsNaturalLeft (K := J') O hO (H.op ⋙ O) (whiskerStructureIsSheaf (J' := J') O hO H)
      (whiskerRestriction O hO H) (whiskerTensorator (J' := J') O hO H) := by
  intro M M' N u
  have h := whiskerTensorSheafIso_naturality_left (J' := J') O hO H u N
  rw [CategoryTheory.Functor.map_id (whiskerRestriction (J' := J') O hO H) N] at h
  rw [← tensorSheafMap_id_right_eq_whiskerRight O hO u N,
    ← tensorSheafMap_id_right_eq_whiskerRight (H.op ⋙ O)
      (whiskerStructureIsSheaf (J' := J') O hO H)
      ((whiskerRestriction O hO H).map u) ((whiskerRestriction O hO H).obj N)]
  exact h

/-- **Naturality of the restriction tensorator in its second slot**, the mirror of
`isNaturalLeft_whiskerTensorator`. -/
public theorem isNaturalRight_whiskerTensorator :
    IsNaturalRight (K := J') O hO (H.op ⋙ O) (whiskerStructureIsSheaf (J' := J') O hO H)
      (whiskerRestriction O hO H) (whiskerTensorator (J' := J') O hO H) := by
  intro M N N' v
  have h := whiskerTensorSheafIso_naturality_right (J' := J') O hO H M v
  rw [CategoryTheory.Functor.map_id (whiskerRestriction (J' := J') O hO H) M] at h
  rw [← tensorSheafMap_id_left_eq_whiskerLeft O hO M v,
    ← tensorSheafMap_id_left_eq_whiskerLeft (H.op ⋙ O)
      (whiskerStructureIsSheaf (J' := J') O hO H)
      ((whiskerRestriction O hO H).obj M) ((whiskerRestriction O hO H).map v)]
  exact h

/-- **The comparison the six normalisations are about is `whiskerTensorPowerIso`**, hence
`Stacks.SheafOfModules.TensorPower.overTensorPowerIso` in the slice case. So supplying the four
remaining normalisations is all that separates `map_coherentMulIso_tensorPowerComparison` from
multiplicativity of the comparison that `overTensorPowerUnitIso` is built from: no further
identification of comparisons is needed. -/
public theorem tensorPowerComparison_whiskerTensorator
    (L : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L]
    [IsInvertible (H.op ⋙ O) (whiskerStructureIsSheaf (J' := J') O hO H)
      ((whiskerRestriction O hO H).obj L)] (n : ℤ) :
    tensorPowerComparison O hO (H.op ⋙ O) (whiskerStructureIsSheaf (J' := J') O hO H)
        (whiskerRestriction O hO H) L (whiskerTensorator (J' := J') O hO H)
        (whiskerUnitIso (J' := J') O hO H) n =
      whiskerTensorPowerIso (J' := J') O hO H L n := rfl

end Whisker

end Stacks.SheafOfModules.TensorPower

end
