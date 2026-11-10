module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyBijectiveUniqueness
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorLocallyFree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerRestriction

/-!
# Restriction along a functor of sites commutes with the tensor product of sheaves of modules

Let `(C, J, 𝒪)` be a ringed site and let `H : C' ⥤ C` be a functor of sites which is continuous
and cocontinuous. Restriction along `H` carries the tensor product of sheaves of modules to the
tensor product of the restrictions,

`(F ⊗ G)|_{C'} ≅ F|_{C'} ⊗ G|_{C'}`,

and hence, with `Stacks.SheafOfModules.TensorPower.mapTensorPowerIso`,

`(L^{⊗ n})|_{C'} ≅ (L|_{C'})^{⊗ n}` for every `n : ℤ`.

Two instances of `H` are the ones wanted. `Over.forget U` gives restriction to a slice, i.e.
Mathlib's `SheafOfModules.overFunctor`, and is spelled out below. The open-image functor
`Opens U ⥤ Opens X` of an open subset of a ringed space gives
`Stacks.Cohomology.HigherDirectImage.moduleRestriction`, and is in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorPowerRestrictOpen.lean`.

## Main definitions

* `Stacks.SheafOfModules.TensorPower.whiskerStructureIsSheaf`: the pulled-back structure sheaf
  is a sheaf, in the form the tensor-power development indexes by.
* `Stacks.SheafOfModules.TensorPower.whiskerRestriction`: restriction of sheaves of modules
  along `H`.

## Main results

* `Stacks.SheafOfModules.TensorPower.whiskerTensorSheafIso`:
  **`(F ⊗ G)|_{C'} ≅ F|_{C'} ⊗ G|_{C'}`.**
* `Stacks.SheafOfModules.TensorPower.whiskerTensorSheafIso_hom`: its characterizing equation,
  on the sheafification unit of the objectwise tensor product.
* `Stacks.SheafOfModules.TensorPower.whiskerTensorSheafIso_naturality`,
  `whiskerTensorSheafIso_naturality_left` and `whiskerTensorSheafIso_naturality_right`:
  **the identification is natural in both variables.** This is what a consumer that tensors a
  morphism with an identity needs — the isomorphism alone only compares two fixed factors — and
  it is the input by which the trivialization of one factor over an open is tensored with the
  identity of the other.
* `Stacks.SheafOfModules.TensorPower.whiskerTensorComparison`: the same, packaged as the
  `TensorComparison` that `mapTensorPowerIso` consumes.
* `Stacks.SheafOfModules.TensorPower.whiskerTensorPowerIso`:
  **`(L^{⊗ n})|_{C'} ≅ (L|_{C'})^{⊗ n}`.**
* `Stacks.SheafOfModules.TensorPower.overTensorSheafIso` and `overTensorPowerIso`: the two
  statements for restriction to a slice.

## Implementation notes

The tensor product of sheaves of modules is the *sheafification* of the objectwise tensor product
of the underlying presheaves, so the content of `whiskerTensorSheafIso` is entirely that
restriction commutes with that sheafification. Both halves are already available and neither is
reproved:

* **The presheaf half.** `PresheafOfModules.pushforward₀OfCommRingCat H 𝒪` is monoidal
  (`Mathlib/Algebra/Category/ModuleCat/Presheaf/PushforwardZeroMonoidal.lean`), so its
  multiplication constraint `Functor.Monoidal.μIso` identifies `(F ⊗ G)|_{C'}` with
  `F|_{C'} ⊗ G|_{C'}` *as presheaves*. Using the monoidal multiplication constraint avoids
  expensive unfolding of nested functors.
* **The sheafification half.** Cocontinuity of `H` enters through
  `Presheaf.isLocallyInjective_whisker` and `Presheaf.isLocallySurjective_whisker`: the
  restriction of the sheafification unit of the presheaf tensor product is still locally
  bijective. Then
  `Stacks.SheafOfModules.TensorLocalProperties.iso_of_locallyBijective` says two sheaves
  receiving locally bijective maps from isomorphic presheaves are isomorphic. That is the whole
  proof.

**This corrects a measurement.** The reduction of `tensorPower` to this comparison was dispatched
on the premise that nothing in the repository relates the tensor product of sheaves of modules to
restriction, in either direction. That is false in the direction that matters:
`Stacks.SheafOfModules.TensorLocalProperties.tensor_over_congr`
(`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorLocallyFree.lean`) already proves that
`(F ⊗ G)|_U` depends only on `F|_U` and `G|_U`, and its proof assembles exactly the four
ingredients above. A grep for `moduleRestriction` misses it, because the restriction there is
Mathlib's
`SheafOfModules.overFunctor`, spelled `.over U`.

**Why the downstream-site instances are hypotheses.** `HasWeakSheafify J'` and
`J'.WEqualsLocallyBijective` do *not* follow from their counterparts on `J` — the file above
records that, and it is why its own extension principles are proved from the type-valued
statement rather than from Mathlib's `homEquivOfIsLocallyBijective`. They are needed here to
*write* the right-hand side at all, since the tensor product downstairs is a sheafification
there, so they are taken as instance arguments. For `J' = J.over U` they are genuinely open; for
the site of an open subspace of a ringed space they are automatic, which is why
`TensorPowerRestrictOpen.lean` has no such hypothesis.

**`J'` is passed explicitly to `whiskerStructureIsSheaf`.** Its only other occurrence in that
declaration is inside the instance argument `[H.IsContinuous J' J]`, so leaving it implicit makes
instance search responsible for inventing the topology it is supposed to be checking, and
elaboration reports `typeclass instance problem is stuck`.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 0GMW](https://stacks.math.columbia.edu/tag/0GMW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open Stacks.SheafOfModules.TensorLocalProperties

universe v u v' u' w

attribute [local implicit_reducible]
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
  Stacks.SheafOfModules.Tensor.sheafTensor PresheafOfModules.tensorBifunctor

namespace Stacks.SheafOfModules.TensorSheafification

section Functoriality

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w}) (hO : Presheaf.IsSheaf J (structureRingPresheaf O))

variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

/-- **The sheafification unit is natural.** Stated for
`Stacks.SheafOfModules.TensorLocalProperties.sheafificationUnit`, the unit read as a morphism of
presheaves of modules over the structure sheaf `structureSheaf O hO`.

`Stacks.SheafOfModules.TensorSheafification.sheafificationUnit_naturality` (in `PullbackTensor`)
is the same statement for the sheaf of rings `commRingSheaf J 𝒪 h𝒪`; the two should be unified. -/
theorem sheafificationUnit_naturality_structureSheaf
    {P P' : PresheafOfModules.{w} (structureSheaf O hO).obj} (p : P ⟶ P') :
    (PresheafOfModules.sheafificationAdjunction
      (R := structureSheaf O hO)
      (𝟙 (structureSheaf O hO).obj)).unit.app
      P ≫
        ((PresheafOfModules.sheafification (𝟙 (structureSheaf O hO).obj)).map p).val =
      p ≫ (PresheafOfModules.sheafificationAdjunction
        (R := structureSheaf O hO)
        (𝟙 (structureSheaf O hO).obj)).unit.app
        P' :=
  ((PresheafOfModules.sheafificationAdjunction
    (𝟙 (structureSheaf O hO).obj)).unit.naturality p).symm

end Functoriality

end Stacks.SheafOfModules.TensorSheafification

namespace Stacks.SheafOfModules.TensorPower

section Whisker

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {C' : Type u'} [Category.{v'} C'] {J' : GrothendieckTopology C'}

/-- The structure sheaf pulled back along a continuous functor of sites is a sheaf, stated for
the presheaf of not-necessarily-commutative rings that
  `Stacks.SheafOfModules.TensorSheafification.structureSheaf` indexes by.
This is the second argument every tensor-product and tensor-power declaration takes. -/
theorem whiskerStructureIsSheaf (O : Cᵒᵖ ⥤ CommRingCat.{w})
    (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
    (H : C' ⥤ C) [H.IsContinuous J' J] :
    Presheaf.IsSheaf J' (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf (H.op ⋙
      O)) :=
  ((H.sheafPushforwardContinuous RingCat.{w} J' J).obj
    (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)).property

variable (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]
  (H : C' ⥤ C) [H.IsContinuous J' J] [H.IsCocontinuous J' J]
  [J'.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J' AddCommGrpCat.{w}]

/-- **Restriction of sheaves of modules along a continuous functor of sites.** For `H` the
inclusion of a slice this is `SheafOfModules.overFunctor`, and for `H` the open-image functor of
an open subset of a ringed space it is `moduleRestriction`. -/
noncomputable abbrev whiskerRestriction :
    _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) ⥤
      _root_.SheafOfModules.{w}
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf (H.op ⋙ O)
          (whiskerStructureIsSheaf (J' := J') O hO H)) :=
  _root_.SheafOfModules.pushforward (F := H)
    (show Stacks.SheafOfModules.TensorSheafification.structureSheaf (H.op ⋙ O)
      (whiskerStructureIsSheaf (J' := J') O hO H) ⟶
        (H.sheafPushforwardContinuous RingCat.{w} J' J).obj
          (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)
      from 𝟙 _)

/-- **Restriction of presheaves of modules along `H`, as a monoidal functor.** This is Mathlib's
`PresheafOfModules.pushforward₀OfCommRingCat`; it agrees with the underlying-presheaf action of
`whiskerRestriction`, and its multiplication constraint is the presheaf half of
`whiskerTensorSheafIso`. -/
noncomputable abbrev whiskerPresheafRestriction :=
  PresheafOfModules.pushforward₀OfCommRingCat.{w} H O

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  [H.IsCocontinuous J' J] [J'.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J' AddCommGrpCat.{w}] in
/-- **Restriction of sheaves of modules acts on the underlying presheaves as
`whiskerPresheafRestriction`.** Both are the pushforward along `H`, the comparison of structure
presheaves being the identity. -/
theorem whiskerRestriction_map_val
    {M N : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)} (ψ : M ⟶ N) :
    ((whiskerRestriction (J' := J') O hO H).map ψ).val =
      (whiskerPresheafRestriction O H).map ψ.val :=
  rfl

/-- **Restriction commutes with the objectwise tensor product of presheaves of modules**: the
multiplication constraint of `whiskerPresheafRestriction`, read in the direction carrying the
restriction of a tensor product to the tensor product of the restrictions. -/
noncomputable abbrev whiskerPresheafTensorIso
    (F G : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO)) :=
  (Functor.Monoidal.μIso (whiskerPresheafRestriction O H) F.val G.val).symm

/-- **The restriction along `H` of the sheafification unit of the objectwise tensor product.**
It is locally bijective for the topology of the smaller site because `H` is cocontinuous, which
is what exhibits the restriction of a tensor product of sheaves of modules as a sheafification
of the restricted objectwise tensor product. -/
noncomputable abbrev whiskerTensorUnit
    (F G : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO)) :
    ((whiskerPresheafRestriction O H).obj
        (PresheafOfModules.tensorObj (O := O) F.val G.val) :
      PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf (H.op ⋙ O)
        (whiskerStructureIsSheaf (J' := J') O hO H)).obj) ⟶
      ((whiskerRestriction (J' := J') O hO H).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} (J := J)
          ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O
            (forget₂ CommRingCat RingCat) hO⟩).obj F).obj G)).val :=
  (whiskerPresheafRestriction O H).map
    ((PresheafOfModules.sheafificationAdjunction
      (R := Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)
      (𝟙 (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj)).unit.app
      (PresheafOfModules.tensorObj (O := O) F.val G.val))

/-- **The sheafification unit of the objectwise tensor product formed on the smaller site**, the
second locally bijective morphism entering `whiskerTensorSheafIso`. -/
noncomputable abbrev whiskerTensorUnit'
    (F G : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO)) :=
  (PresheafOfModules.sheafificationAdjunction
    (R := Stacks.SheafOfModules.TensorSheafification.structureSheaf (H.op ⋙ O)
      (whiskerStructureIsSheaf (J' := J') O hO H))
    (𝟙 (Stacks.SheafOfModules.TensorSheafification.structureSheaf (H.op ⋙ O)
      (whiskerStructureIsSheaf (J' := J') O hO H)).obj)).unit.app
    (PresheafOfModules.tensorObj (O := H.op ⋙ O)
      ((whiskerRestriction (J' := J') O hO H).obj F).val
      ((whiskerRestriction (J' := J') O hO H).obj G).val)

/-- The restricted sheafification unit of the objectwise tensor product is locally injective
for the topology of the smaller site: cocontinuity of `H` carries local injectivity downwards.
Not an instance: the indexing presheaf of rings is read here at the spelling
`H.op ⋙ O` coming out of `whiskerPresheafRestriction` and at `structureSheaf (H.op ⋙ O) _` by
the tensor-product development, and the two are definitionally but not syntactically equal, so
instance search indexed on the second spelling does not find a global instance stated at the
first. It is supplied where needed. -/
instance isLocallyInjective_whiskerTensorUnit
    (F G : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO)) :
    PresheafOfModules.IsLocallyInjective J' (whiskerTensorUnit (J' := J') O hO H F G) := by
  let P : PresheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj :=
    PresheafOfModules.tensorObj (O := O) F.val G.val
  let η := (PresheafOfModules.sheafificationAdjunction
    (R := Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)
    (𝟙 (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj)).unit.app
    P
  have hPi : PresheafOfModules.IsLocallyInjective J η :=
    inferInstanceAs (Presheaf.IsLocallyInjective J (CategoryTheory.toSheafify J P.presheaf))
  exact Presheaf.isLocallyInjective_whisker J' J H
    ((PresheafOfModules.toPresheaf
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj).map η)

/-- The restricted sheafification unit of the objectwise tensor product is locally surjective
for the topology of the smaller site. See
`Stacks.SheafOfModules.TensorPower.isLocallyInjective_whiskerTensorUnit` for why this is not an
instance. -/
instance isLocallySurjective_whiskerTensorUnit
    (F G : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO)) :
    PresheafOfModules.IsLocallySurjective J' (whiskerTensorUnit (J' := J') O hO H F G) := by
  let P : PresheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj :=
    PresheafOfModules.tensorObj (O := O) F.val G.val
  let η := (PresheafOfModules.sheafificationAdjunction
    (R := Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)
    (𝟙 (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj)).unit.app
    P
  have hPs : PresheafOfModules.IsLocallySurjective J η :=
    inferInstanceAs (Presheaf.IsLocallySurjective J (CategoryTheory.toSheafify J P.presheaf))
  exact Presheaf.isLocallySurjective_whisker J' J H
    ((PresheafOfModules.toPresheaf
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj).map η)

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  [H.IsCocontinuous J' J] in
/-- The sheafification unit of the objectwise tensor product formed on the smaller site is
locally injective. -/
instance isLocallyInjective_whiskerTensorUnit'
    (F G : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO)) :
    PresheafOfModules.IsLocallyInjective J' (whiskerTensorUnit' (J' := J') O hO H F G) := by
  let Q : PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf
      (H.op ⋙ O) (whiskerStructureIsSheaf (J' := J') O hO H)).obj :=
    PresheafOfModules.tensorObj (O := H.op ⋙ O)
      ((whiskerRestriction (J' := J') O hO H).obj F).val
      ((whiskerRestriction (J' := J') O hO H).obj G).val
  exact inferInstanceAs (Presheaf.IsLocallyInjective J' (CategoryTheory.toSheafify J' Q.presheaf))

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  [H.IsCocontinuous J' J] in
/-- The sheafification unit of the objectwise tensor product formed on the smaller site is
locally surjective. -/
instance isLocallySurjective_whiskerTensorUnit'
    (F G : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO)) :
    PresheafOfModules.IsLocallySurjective J' (whiskerTensorUnit' (J' := J') O hO H F G) := by
  let Q : PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf
      (H.op ⋙ O) (whiskerStructureIsSheaf (J' := J') O hO H)).obj :=
    PresheafOfModules.tensorObj (O := H.op ⋙ O)
      ((whiskerRestriction (J' := J') O hO H).obj F).val
      ((whiskerRestriction (J' := J') O hO H).obj G).val
  exact inferInstanceAs (Presheaf.IsLocallySurjective J' (CategoryTheory.toSheafify J' Q.presheaf))

/-- **Restriction along a continuous, cocontinuous functor of sites commutes with the tensor
product of sheaves of modules**: `(F ⊗ G)|_{C'} ≅ F|_{C'} ⊗ G|_{C'}`. -/
noncomputable def whiskerTensorSheafIso
    (F G : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO)) :
    (whiskerRestriction O hO H).obj (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      (J := J) ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O
        (forget₂ CommRingCat RingCat) hO⟩).obj F).obj G) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w, w, w} (J := J')
        ⟨(H.op ⋙ O), Presheaf.isSheaf_of_isSheaf_comp J' (H.op ⋙ O)
          (forget₂ CommRingCat RingCat) (whiskerStructureIsSheaf (J' := J') O hO H)⟩).obj
        ((whiskerRestriction O hO H).obj F)).obj ((whiskerRestriction O hO H).obj G) :=
  isoOfLocallyBijective (whiskerTensorUnit (J' := J') O hO H F G)
    (whiskerTensorUnit' (J' := J') O hO H F G)
    (isLocallyInjective_whiskerTensorUnit (J' := J') O hO H F G)
    (isLocallySurjective_whiskerTensorUnit (J' := J') O hO H F G)
    (isLocallyInjective_whiskerTensorUnit' (J' := J') O hO H F G)
    (isLocallySurjective_whiskerTensorUnit' (J' := J') O hO H F G)
    (whiskerPresheafTensorIso O hO H F G)

/-- `whiskerTensorSheafIso` is the isomorphism that
`Stacks.SheafOfModules.TensorLocalProperties.iso_of_locallyBijective` builds from the two
sheafification units and the comparison of the objectwise tensor products. Quoting this before
anything else keeps the statements below from having to unfold a *projection* of the
isomorphism, which is where the heartbeat budget goes: the construction is a tactic block, so
`Iso.hom` of it reduces by iota into the sheafification rather than stopping at the two
congruent applications. -/
theorem whiskerTensorSheafIso_eq
    (F G : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO)) :
    whiskerTensorSheafIso (J' := J') O hO H F G =
      isoOfLocallyBijective (whiskerTensorUnit (J' := J') O hO H F G)
        (whiskerTensorUnit' (J' := J') O hO H F G)
        (isLocallyInjective_whiskerTensorUnit (J' := J') O hO H F G)
        (isLocallySurjective_whiskerTensorUnit (J' := J') O hO H F G)
        (isLocallyInjective_whiskerTensorUnit' (J' := J') O hO H F G)
        (isLocallySurjective_whiskerTensorUnit' (J' := J') O hO H F G)
        (whiskerPresheafTensorIso O hO H F G) :=
  rfl

/-- **The characterizing equation of `whiskerTensorSheafIso`**: restricted along the
sheafification unit of the objectwise tensor product, it is the comparison of the objectwise
tensor products followed by the sheafification unit of the smaller site. By
`Stacks.SheafOfModules.TensorLocalProperties.iso_of_locallyBijective_eq` it determines the
isomorphism, and it is the input every statement about the isomorphism is derived from. -/
theorem whiskerTensorSheafIso_hom
    (F G : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO)) :
    whiskerTensorUnit (J' := J') O hO H F G ≫
        (whiskerTensorSheafIso (J' := J') O hO H F G).hom.val =
      (whiskerPresheafTensorIso O hO H F G).hom ≫ whiskerTensorUnit' (J' := J') O hO H F G := by
  rw [whiskerTensorSheafIso_eq]
  exact isoOfLocallyBijective_hom (R := Stacks.SheafOfModules.TensorSheafification.structureSheaf
    (H.op ⋙ O) (whiskerStructureIsSheaf (J' := J') O hO H)) _ _ _ _ _ _ _

section Naturality

variable {F F' G G' : _root_.SheafOfModules.{w}
  (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)}

omit [H.IsCocontinuous J' J] [J'.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J' AddCommGrpCat.{w}] in
/-- The restricted sheafification unit of the objectwise tensor product is natural: it is the
restriction of a natural transformation. -/
theorem whiskerTensorUnit_naturality (f : F ⟶ F') (g : G ⟶ G') :
    whiskerTensorUnit (J' := J') O hO H F G ≫
        ((whiskerRestriction (J' := J') O hO H).map
          ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} (J := J)
            ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O
              (forget₂ CommRingCat RingCat) hO⟩).map
            (X := F)
            (Y := F') f).app G ≫
            ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} (J := J)
            ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O
              (forget₂ CommRingCat RingCat) hO⟩).obj F').map
            (X := G)
            (Y := G') g))).val =
      (whiskerPresheafRestriction O H).map
          (PresheafOfModules.tensorHom (O := O) f.val g.val) ≫
        whiskerTensorUnit (J' := J') O hO H F' G' := by
  have pairedMap := Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map
    (R := ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩) f g
  have restriction := whiskerRestriction_map_val (J' := J') O hO H
    ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} (J := J)
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).map
      (X := F)
      (Y := F') f).app G ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} (J := J)
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).obj F').map
      (X := G)
      (Y := G') g))
  have naturality := ((whiskerPresheafRestriction O H).map_comp _ _).symm.trans
    ((congrArg (fun morphism => (whiskerPresheafRestriction O H).map morphism)
        (Stacks.SheafOfModules.TensorSheafification.sheafificationUnit_naturality_structureSheaf
          O hO (PresheafOfModules.tensorHom (O := O) f.val g.val))).trans
      ((whiskerPresheafRestriction O H).map_comp _ _))
  exact (congrArg (fun morphism => whiskerTensorUnit (J' := J') O hO H F G ≫ morphism)
    restriction).trans
      ((congrArg (fun morphism => whiskerTensorUnit (J' := J') O hO H F G ≫
          (whiskerPresheafRestriction O H).map morphism)
        (congrArg _root_.SheafOfModules.Hom.val pairedMap)).trans naturality)

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  [H.IsCocontinuous J' J] in
/-- **The induced map of tensor product sheaves on the smaller site, on underlying presheaves**,
is the sheafification of the induced map of the restricted objectwise tensor products.  Both
sides are the same morphism, by `whiskerRestriction_map_val` under the sheafification; the
identification is named because `whiskerTensorUnit'_naturality` below would otherwise have to
make it, unfold `tensorSheafMap` and match the sheafification unit all in one unification, which
exhausts the elaborator's budget although each step on its own is cheap.

**The two factors of the source and target are named.** A morphism of the product category is
written as a pair, so `Functor.uncurry.obj _ |>.map (_, _)` leaves the objects of `Functor.map`
as metavariables whose only occurrences are under `Prod.fst` and `Prod.snd`; they are then
determined not by the pair but by the right-hand side, which asks the unifier to read a pair of
module sheaves back out of a sheafification of their objectwise tensor product. That inversion
is what exhausts the budget — the two sides *at fixed objects* are definitionally equal in a
fraction of it. Passing `X` and `Y` removes the metavariables, and the comparison is then the
cheap one. -/
theorem tensorSheafMap_whiskerRestriction_val (f : F ⟶ F') (g : G ⟶ G') :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨H.op ⋙ O, Presheaf.isSheaf_of_isSheaf_comp J' (H.op ⋙ O)
        (forget₂ CommRingCat RingCat) (whiskerStructureIsSheaf (J' := J') O hO H)⟩)).map
        (X := (((whiskerRestriction (J' := J') O hO H).obj F),
          ((whiskerRestriction (J' := J') O hO H).obj G)))
        (Y := (((whiskerRestriction (J' := J') O hO H).obj F'),
          ((whiskerRestriction (J' := J') O hO H).obj G')))
        (((whiskerRestriction (J' := J') O hO H).map f),
          ((whiskerRestriction (J' := J') O hO H).map g))).val =
      ((PresheafOfModules.sheafification
          (R := Stacks.SheafOfModules.Tensor.ringSheaf
            ⟨H.op ⋙ O, Presheaf.isSheaf_of_isSheaf_comp J' (H.op ⋙ O)
              (forget₂ CommRingCat RingCat) (whiskerStructureIsSheaf (J' := J') O hO H)⟩)
          (𝟙 _)).map
        (PresheafOfModules.tensorHom
          ((whiskerPresheafRestriction O H).map f.val)
          ((whiskerPresheafRestriction O H).map g.val))).val := by
  refine Eq.trans (congrArg _root_.SheafOfModules.Hom.val
    (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map
      ⟨H.op ⋙ O, Presheaf.isSheaf_of_isSheaf_comp J' (H.op ⋙ O)
        (forget₂ CommRingCat RingCat) (whiskerStructureIsSheaf (J' := J') O hO H)⟩
      ((whiskerRestriction (J' := J') O hO H).map f)
      ((whiskerRestriction (J' := J') O hO H).map g))) ?_
  congr 1

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  [H.IsCocontinuous J' J] in
/-- The sheafification unit of the objectwise tensor product formed on the smaller site is
natural. -/
theorem whiskerTensorUnit'_naturality (f : F ⟶ F') (g : G ⟶ G') :
    whiskerTensorUnit' (J' := J') O hO H F G ≫
        ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w, w, w} (J := J')
          ⟨(H.op ⋙ O), Presheaf.isSheaf_of_isSheaf_comp J' (H.op ⋙ O)
            (forget₂ CommRingCat RingCat) (whiskerStructureIsSheaf (J' := J') O hO H)⟩).map
          (X := ((whiskerRestriction (J' := J') O hO H).obj F))
          (Y := ((whiskerRestriction (J' := J') O hO H).obj F'))
          ((whiskerRestriction (J' := J') O hO H).map
            f)).app ((whiskerRestriction (J' := J') O hO H).obj G) ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w, w, w} (J := J')
          ⟨(H.op ⋙ O), Presheaf.isSheaf_of_isSheaf_comp J' (H.op ⋙ O)
            (forget₂ CommRingCat RingCat) (whiskerStructureIsSheaf (J' := J') O hO
              H)⟩).obj ((whiskerRestriction (J' := J') O hO H).obj F')).map
          (X := ((whiskerRestriction (J' := J') O hO H).obj G))
          (Y := ((whiskerRestriction (J' := J') O hO H).obj G'))
          ((whiskerRestriction (J' := J') O hO H).map
            g))).val =
      PresheafOfModules.tensorHom (O := (H.op ⋙ O)) ((whiskerPresheafRestriction O H).map
        f.val) ((whiskerPresheafRestriction O H).map g.val) ≫
        whiskerTensorUnit' (J' := J') O hO H F' G' := by
  have pairedMap := Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map
    (R := ⟨H.op ⋙ O, Presheaf.isSheaf_of_isSheaf_comp J' (H.op ⋙ O)
      (forget₂ CommRingCat RingCat) (whiskerStructureIsSheaf (J' := J') O hO H)⟩)
    ((whiskerRestriction (J' := J') O hO H).map f)
    ((whiskerRestriction (J' := J') O hO H).map g)
  have naturality :=
    Stacks.SheafOfModules.TensorSheafification.sheafificationUnit_naturality_structureSheaf
      (H.op ⋙ O) (whiskerStructureIsSheaf (J' := J') O hO H)
      (PresheafOfModules.tensorHom (O := H.op ⋙ O)
        ((whiskerRestriction (J' := J') O hO H).map f).val
        ((whiskerRestriction (J' := J') O hO H).map g).val)
  have tensorMapEquality := congrArg₂ (PresheafOfModules.tensorHom (O := H.op ⋙ O))
    (whiskerRestriction_map_val (J' := J') O hO H f)
    (whiskerRestriction_map_val (J' := J') O hO H g)
  exact (congrArg (fun morphism => whiskerTensorUnit' (J' := J') O hO H F G ≫ morphism)
    (congrArg _root_.SheafOfModules.Hom.val pairedMap)).trans
      (naturality.trans (congrArg
        (fun morphism => morphism ≫ whiskerTensorUnit' (J' := J') O hO H F' G') tensorMapEquality))

/-- **`whiskerTensorSheafIso` is natural in both variables at once.** The identification of
`(F ⊗ G)|_{C'}` with `F|_{C'} ⊗ G|_{C'}` carries the restriction of the morphism induced by
`f : F ⟶ F'` and `g : G ⟶ G'` to the morphism induced by the restrictions of `f` and `g`. This
is what a consumer tensoring a morphism with an identity needs, and what the bare isomorphism
does not supply. -/
theorem whiskerTensorSheafIso_naturality (f : F ⟶ F') (g : G ⟶ G') :
    (whiskerRestriction (J' := J') O hO H).map
          ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} (J := J)
            ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O
              (forget₂ CommRingCat RingCat) hO⟩).map
            (X := F)
            (Y := F') f).app G ≫
            ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} (J := J)
            ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O
              (forget₂ CommRingCat RingCat) hO⟩).obj F').map
            (X := G)
            (Y := G') g)) ≫
        (whiskerTensorSheafIso (J' := J') O hO H F' G').hom =
      (whiskerTensorSheafIso (J' := J') O hO H F G).hom ≫
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w, w, w} (J := J')
          ⟨(H.op ⋙ O), Presheaf.isSheaf_of_isSheaf_comp J' (H.op ⋙ O)
            (forget₂ CommRingCat RingCat) (whiskerStructureIsSheaf (J' := J') O hO H)⟩).map
          (X := ((whiskerRestriction (J' := J') O hO H).obj F))
          (Y := ((whiskerRestriction (J' := J') O hO H).obj F'))
          ((whiskerRestriction (J' := J') O hO H).map
            f)).app ((whiskerRestriction (J' := J') O hO H).obj G) ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w, w, w} (J := J')
          ⟨(H.op ⋙ O), Presheaf.isSheaf_of_isSheaf_comp J' (H.op ⋙ O)
            (forget₂ CommRingCat RingCat) (whiskerStructureIsSheaf (J' := J') O hO
              H)⟩).obj ((whiskerRestriction (J' := J') O hO H).obj F')).map
          (X := ((whiskerRestriction (J' := J') O hO H).obj G))
          (Y := ((whiskerRestriction (J' := J') O hO H).obj G'))
          ((whiskerRestriction (J' := J') O hO H).map
            g)) := by
  rw [whiskerTensorSheafIso_eq, whiskerTensorSheafIso_eq]
  exact isoOfLocallyBijective_naturality
    (R := Stacks.SheafOfModules.TensorSheafification.structureSheaf (H.op ⋙ O)
      (whiskerStructureIsSheaf (J' := J') O hO H)) _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (whiskerTensorUnit_naturality O hO H f g) (whiskerTensorUnit'_naturality O hO H f g)
    (by
      ext : 1
      exact ModuleCat.hom_ext (TensorProduct.ext' fun _ _ => rfl))

/-- **`whiskerTensorSheafIso` is natural in the first variable**: tensoring with the identity of
a fixed second factor commutes with the identification. -/
theorem whiskerTensorSheafIso_naturality_left (f : F ⟶ F')
    (G : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (whiskerRestriction (J' := J') O hO H).map
          ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} (J := J)
            ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O
              (forget₂ CommRingCat RingCat) hO⟩).map
            (X := F)
            (Y := F') f).app G ≫
            ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} (J := J)
            ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O
              (forget₂ CommRingCat RingCat) hO⟩).obj F').map
            (X := G)
            (Y := G) (𝟙 G))) ≫
        (whiskerTensorSheafIso (J' := J') O hO H F' G).hom =
      (whiskerTensorSheafIso (J' := J') O hO H F G).hom ≫
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w, w, w} (J := J')
          ⟨(H.op ⋙ O), Presheaf.isSheaf_of_isSheaf_comp J' (H.op ⋙ O)
            (forget₂ CommRingCat RingCat) (whiskerStructureIsSheaf (J' := J') O hO H)⟩).map
          (X := ((whiskerRestriction (J' := J') O hO H).obj F))
          (Y := ((whiskerRestriction (J' := J') O hO H).obj F'))
          ((whiskerRestriction (J' := J') O hO H).map
            f)).app ((whiskerRestriction (J' := J') O hO H).obj G) ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w, w, w} (J := J')
          ⟨(H.op ⋙ O), Presheaf.isSheaf_of_isSheaf_comp J' (H.op ⋙ O)
            (forget₂ CommRingCat RingCat) (whiskerStructureIsSheaf (J' := J') O hO
              H)⟩).obj ((whiskerRestriction (J' := J') O hO H).obj F')).map
          (X := ((whiskerRestriction (J' := J') O hO H).obj G))
          (Y := ((whiskerRestriction (J' := J') O hO H).obj G))
          ((whiskerRestriction (J' := J') O hO H).map (𝟙
            G))) :=
  whiskerTensorSheafIso_naturality O hO H f (𝟙 G)

/-- **`whiskerTensorSheafIso` is natural in the second variable**: tensoring the identity of a
fixed first factor with a morphism commutes with the identification. -/
theorem whiskerTensorSheafIso_naturality_right
    (F : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) (g : G ⟶ G') :
    (whiskerRestriction (J' := J') O hO H).map
          ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} (J := J)
            ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O
              (forget₂ CommRingCat RingCat) hO⟩).map
            (X := F)
            (Y := F) (𝟙 F)).app G ≫
            ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} (J := J)
            ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O
              (forget₂ CommRingCat RingCat) hO⟩).obj F).map
            (X := G)
            (Y := G') g)) ≫
        (whiskerTensorSheafIso (J' := J') O hO H F G').hom =
      (whiskerTensorSheafIso (J' := J') O hO H F G).hom ≫
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w, w, w} (J := J')
          ⟨(H.op ⋙ O), Presheaf.isSheaf_of_isSheaf_comp J' (H.op ⋙ O)
            (forget₂ CommRingCat RingCat) (whiskerStructureIsSheaf (J' := J') O hO H)⟩).map
          (X := ((whiskerRestriction (J' := J') O hO H).obj F))
          (Y := ((whiskerRestriction (J' := J') O hO H).obj F))
          ((whiskerRestriction (J' := J') O hO H).map
            (𝟙 F))).app ((whiskerRestriction (J' := J') O hO H).obj G) ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w, w, w} (J := J')
          ⟨(H.op ⋙ O), Presheaf.isSheaf_of_isSheaf_comp J' (H.op ⋙ O)
            (forget₂ CommRingCat RingCat) (whiskerStructureIsSheaf (J' := J') O hO
              H)⟩).obj ((whiskerRestriction (J' := J') O hO H).obj F)).map
          (X := ((whiskerRestriction (J' := J') O hO H).obj G))
          (Y := ((whiskerRestriction (J' := J') O hO H).obj G'))
          ((whiskerRestriction (J' := J') O hO H).map
            g)) :=
  whiskerTensorSheafIso_naturality O hO H (𝟙 F) g

end Naturality

/-- `whiskerTensorSheafIso`, packaged as the input `mapTensorPowerIso` consumes. -/
noncomputable def whiskerTensorComparison
    (L : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
      :
    TensorComparison O hO (H.op ⋙ O) (whiskerStructureIsSheaf (J' := J') O hO H)
      (whiskerRestriction O hO H) L :=
  fun M => whiskerTensorSheafIso O hO H M L

/-- The restriction of the structure sheaf along a continuous functor of sites is the structure
sheaf of the smaller site. -/
noncomputable def whiskerUnitIso :
    (whiskerRestriction O hO H).obj
        (_root_.SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
          hO)) ≅
      _root_.SheafOfModules.unit
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf (H.op ⋙ O)
          (whiskerStructureIsSheaf (J' := J') O hO H)) :=
  Iso.refl _

/-- **`(L^{⊗ n})|_{C'} ≅ (L|_{C'})^{⊗ n}` for every integer `n`.** No hypothesis beyond
invertibility of `L` on each of the two sites. -/
noncomputable def whiskerTensorPowerIso
    (L : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    [((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} (J := J)
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
        L).IsEquivalence]
    [((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w, w, w} (J := J')
      ⟨(H.op ⋙ O), Presheaf.isSheaf_of_isSheaf_comp J' (H.op ⋙ O)
        (forget₂ CommRingCat RingCat) (whiskerStructureIsSheaf (J' := J') O hO H)⟩).flip.obj
          ((whiskerRestriction O hO H).obj L)).IsEquivalence] (n : ℤ) :
    (whiskerRestriction O hO H).obj (tensorPower O hO L n) ≅
      tensorPower (H.op ⋙ O) (whiskerStructureIsSheaf (J' := J') O hO H)
        ((whiskerRestriction O hO H).obj L) n :=
  mapTensorPowerIso O hO (H.op ⋙ O) (whiskerStructureIsSheaf (J' := J') O hO H)
    (whiskerRestriction O hO H) L (whiskerTensorComparison O hO H L) (whiskerUnitIso O hO H) n

end Whisker

/-- The structure sheaf of the slice site. -/
theorem sliceStructureIsSheaf {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (O : Cᵒᵖ ⥤ CommRingCat.{w})
    (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
      (U : C) :
    Presheaf.IsSheaf (J.over U)
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf ((Over.forget U).op ⋙ O)) :=
  whiskerStructureIsSheaf O hO (Over.forget U)

section Slice

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]
  (U : C)
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify (J.over U) AddCommGrpCat.{w}]

/-- **`(F ⊗ G)|_U ≅ F|_U ⊗ G|_U`** for restriction to a slice. -/
noncomputable def overTensorSheafIso
    (F G : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO)) :
    (whiskerRestriction O hO (Over.forget U)).obj
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} (J := J)
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O
          (forget₂ CommRingCat RingCat) hO⟩).obj F).obj G) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, w, w, w}
        ⟨((Over.forget U).op ⋙ O), Presheaf.isSheaf_of_isSheaf_comp _ ((Over.forget U).op ⋙ O)
          (forget₂ CommRingCat RingCat) (sliceStructureIsSheaf O hO U)⟩).obj
        ((whiskerRestriction O hO (Over.forget U)).obj F)).obj
        ((whiskerRestriction O hO (Over.forget U)).obj G) :=
  whiskerTensorSheafIso O hO (Over.forget U) F G

/-- **`(L^{⊗ n})|_U ≅ (L|_U)^{⊗ n}`** for restriction to a slice. -/
noncomputable def overTensorPowerIso
    (L : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    [((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} (J := J)
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
        L).IsEquivalence]
    [((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, w, w, w} (J := J.over U)
      ⟨((Over.forget U).op ⋙ O), Presheaf.isSheaf_of_isSheaf_comp _ ((Over.forget U).op ⋙ O)
        (forget₂ CommRingCat RingCat) (sliceStructureIsSheaf O hO U)⟩).flip.obj
          ((whiskerRestriction O hO (Over.forget U)).obj L)).IsEquivalence] (n : ℤ) :
    (whiskerRestriction O hO (Over.forget U)).obj (tensorPower O hO L n) ≅
      tensorPower ((Over.forget U).op ⋙ O) (sliceStructureIsSheaf O hO U)
        ((whiskerRestriction O hO (Over.forget U)).obj L) n :=
  whiskerTensorPowerIso O hO (Over.forget U) L n

end Slice

end Stacks.SheafOfModules.TensorPower
