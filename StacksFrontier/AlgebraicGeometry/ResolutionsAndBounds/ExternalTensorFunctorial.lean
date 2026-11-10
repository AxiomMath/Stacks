module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.OnSpaceMonoidal
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.ExternalTensor.Basic
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.Basic
public import StacksFrontier.AlgebraicGeometry.RegularSequence.ExtVanishing

/-!
# Identities, zero maps, sums, scalars and composites of external tensor products

The tensor product of modules on a ringed space, and with it the external tensor product of a
module on `X` and a module on `Y` over a base `S`, is functorial and additive in both variables.
This file records that the induced map is the identity on a pair of identities, is zero as soon
as *one* of the two maps is zero, is additive in each variable separately, and is compatible
with composition in each variable.

Over an affine base `Spec R` the two sides carry more than addition: the morphisms of modules on
an `R`-scheme are an `R`-module, by `AlgebraicGeometry.modulesLinear`, and the external tensor
product of maps is `R`-bilinear and not merely bi-additive. That is proved here as well, and the
agreement of the two one-variable laws — `(c • a) ⊠ b = a ⊠ (c • b)` — is what says that the
pairing `(a, b) ↦ a ⊠ b` kills the `R`-bilinearity relations.

The computation on a pair of zero maps is the one that is not formal: the tensor product of
sheaves of modules is the sheafification of the objectwise tensor product of presheaves, so the
statement is the corresponding presheaf computation — `m ⊗ n ↦ 0 ⊗ 0 = 0` on local pure
tensors — together with the fact that sheafification preserves zero morphisms.

## Main results

* `AlgebraicGeometry.tensorSheafMap_zero_zero`: the map of tensor products induced by a pair of
  zero maps is zero, and `AlgebraicGeometry.tensorSheafMap_id` the same for a pair of
  identities.
* `AlgebraicGeometry.externalTensorProductMap_zero_zero`,
  `AlgebraicGeometry.externalTensorProductMap_id` and
  `AlgebraicGeometry.externalTensorProductMap_comp`: the three statements for the external
  tensor product of modules on two schemes over a base.
* `AlgebraicGeometry.externalTensorProductMap_add_left`,
  `AlgebraicGeometry.externalTensorProductMap_add_right`,
  `AlgebraicGeometry.externalTensorProductMap_zero_left` and
  `AlgebraicGeometry.externalTensorProductMap_zero_right`: **the external tensor product of
  maps is bi-additive**, and vanishes as soon as one of its two arguments does.
* `AlgebraicGeometry.tensorSheafMap_globalSmulCenter_left` and `_right`: multiplication by a
  global function on one tensor factor is multiplication by that function on the tensor product.
* `AlgebraicGeometry.tensorSheafMap_smul_left` and `_right`: the tensor product of modules on an
  `R`-scheme is `R`-bilinear on morphisms.
* `AlgebraicGeometry.externalTensorProductMap_smul_left`,
  `AlgebraicGeometry.externalTensorProductMap_smul_right` and
  `AlgebraicGeometry.externalTensorProductMap_smul_left_eq_smul_right`: **the external tensor
  product of maps of modules on two `R`-schemes is `R`-bilinear**, and a scalar may be moved
  from either factor to the other.

## Implementation notes

Sheafification of presheaves of modules is a left adjoint, hence preserves zero morphisms; the
instance `AlgebraicGeometry.sheafifyFunctor_isLeftAdjoint` records the adjunction in the form
instance search for `CategoryTheory.Functor.PreservesZeroMorphisms` consumes.

`AlgebraicGeometry.Scheme.Modules X` is a `def` for `SheafOfModules X.ringCatSheaf`, and
the uncurried `Stacks.SheafOfModules.Tensor.sheafTensor` is stated over
`Stacks.SheafOfModules.Tensor.ringSheaf` of the structure sheaf, so a goal mixing the two
spellings is not type-correct under the transparency at which `rw` operates — the error names
the two ring sheaves, and no reducibility attribute is added to make it go away. Every statement
about the external tensor product is therefore assembled as a term: identity and composition
are functor laws, and the additive and scalar statements are congruence in the one pullback
factor that moves, followed by the corresponding law for the tensor product on the fibre
product. The additivity of the tensor product itself is
`Stacks.SheafOfModules.Tensor.sheafTensor_additive` in the left variable and
`Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive` in the right; the latter is named
rather than searched for, its module argument being read here at the `Scheme.Modules` spelling.
The two vanishing statements are read off the corresponding additivity at `0`, which needs no
further computation.

*How the scalar statements are organised, and why not through
`CategoryTheory.MonoidalLinear`.* The `R`-linear structure of
`AlgebraicGeometry.modulesLinear` is `CategoryTheory.Linear.ofRingMorphism` at the ring
morphism `R ⟶ CatCenter` that sends a scalar to multiplication by its image among the global
functions, so `c • φ` is by definition `(c • 𝟙) ≫ φ` and the whole content of bilinearity is the
single statement that `⊗` carries `c • 𝟙` in either variable to `c • 𝟙`. That statement needs no
base ring at all: it is `AlgebraicGeometry.tensorSheafMap_globalSmulCenter_left` and `_right`,
for an arbitrary global function on an arbitrary scheme, proved on local pure sections by
`Stacks.SheafOfModules.OnSpace.tensor_hom_ext`, with `TensorProduct.smul_tmul` and
`TensorProduct.tmul_smul` moving the scalar out. The base-ring statements then follow by
composing, with no further computation: `AlgebraicGeometry.baseScalar` is multiplication by the
image of the scalar among the global functions on the nose, so
`Stacks.RegularSequence.globalSmulCenter` applies to it by `rfl`.

`CategoryTheory.MonoidalLinear` is the abstract packaging of the same two laws, but it is not the
route taken: `AlgebraicGeometry.externalTensorProductMap` is defined through the uncurried
`Stacks.SheafOfModules.Tensor.sheafTensor` and not through a monoidal product, so going through
`MonoidalLinear` would mean installing a monoidal structure as a local instance and crossing
back and forth to reach the same two statements. The two whiskering laws it asks for *are* the
two statements proved here, so a `MonoidalLinear` instance can be read off them if one is ever
wanted.

The `R`-linearity of the two pullback functors is not proved here either: it is
`AlgebraicGeometry.over_pullback_linear`, which needs the two projections as morphisms of
`R`-schemes — `AlgebraicGeometry.externalTensorOverFst` and `externalTensorOverSnd`, the second
of which is where the pullback square's commutativity is consumed.

Because `AlgebraicGeometry.modulesLinear` is not an instance — the base ring is not recoverable
from a sheaf of modules — the scalar statements carry their linear structures in `letI`, as
`AlgebraicGeometry.over_pullback_linear` does. Each is given at both spellings of the category
of modules that the statement mentions: instance search is keyed on the syntactic form of the
category, and the morphisms being scaled live in
`SheafOfModules (Stacks.RingedSpace.structureSheafRing _)` while their tensor product lives in
`SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf _)`.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 0G46](https://stacks.math.columbia.edu/tag/0G46)
* [Stacks Project, Tag 0G0A](https://stacks.math.columbia.edu/tag/0G0A)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

noncomputable section

namespace AlgebraicGeometry

attribute [local implicit_reducible] Scheme.Modules

/-- Sheafification of presheaves of modules on a ringed space is a left adjoint. -/
instance sheafifyFunctor_isLeftAdjoint (Z : RingedSpace.{u, u}) :
    (sheafifyFunctor Z).IsLeftAdjoint :=
  ⟨_, ⟨PresheafOfModules.sheafificationAdjunction (𝟙 (structureSheafRing Z).obj)⟩⟩

/-- The map of presheaf tensor products induced by a pair of zero maps is zero: on a local pure
tensor it is `m ⊗ n ↦ 0 ⊗ 0 = 0`. -/
theorem presheafTensorMap_zero_zero (Z : RingedSpace.{u, u})
    {A B C D : PresheafOfModules.{u} (O Z)} :
    (PresheafOfModules.tensorHom (O := (Z).presheaf) ((0 : A ⟶ C)) ((0 : B ⟶ D))) = 0 :=
  PresheafOfModules.tensorHom_zero_left (0 : B ⟶ D)

/-- The map of presheaf tensor products induced by a pair of identities is the identity. -/
theorem presheafTensorMap_id (Z : RingedSpace.{u, u}) (A B : PresheafOfModules.{u} (O Z)) :
    (PresheafOfModules.tensorHom (O := (Z).presheaf) ((𝟙 A)) ((𝟙 B))) =
        𝟙 ((PresheafOfModules.tensorObj (O := (Z).presheaf) (A) (B))) :=
  PresheafOfModules.tensorHom_id A B

/-- **The map of tensor products of modules on a ringed space induced by a pair of zero maps is
zero.** -/
theorem tensorSheafMap_zero_zero (Z : RingedSpace.{u, u})
    {A B C D : SheafOfModules.{u} (structureSheafRing Z)} :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((Z)).presheaf, ((Z)).IsSheaf⟩)).map (((0 : A ⟶ C), (0 : B ⟶ D)) : (_, _) ⟶ (_, _))) = 0 :=
  (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map
    ⟨Z.presheaf, Z.IsSheaf⟩ (0 : A ⟶ C) (0 : B ⟶ D)).trans <|
    (congrArg (sheafifyFunctor Z).map
      (presheafTensorMap_zero_zero Z (A := A.val) (B := B.val)
        (C := C.val) (D := D.val))).trans (Functor.map_zero _ _ _)

/-- **The map of tensor products of modules on a ringed space induced by a pair of identities is
the identity.** -/
theorem tensorSheafMap_id (Z : RingedSpace.{u, u})
    (A B : SheafOfModules.{u} (structureSheafRing Z)) :
    ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((Z)).presheaf, ((Z)).IsSheaf⟩)).map
        (((𝟙 A), (𝟙 B)) : (_, _) ⟶ (_, _))) = 𝟙 ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((Z)).presheaf, ((Z)).IsSheaf⟩).obj (A)).obj (B))) :=
  (Functor.uncurry.obj
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨Z.presheaf, Z.IsSheaf⟩)).map_id (A, B)

/-! ### Multiplication by a global function on one tensor factor -/

section GlobalScalar

open Stacks.RegularSequence (globalSmulCenter)

/-- **Multiplication by a global function on the second tensor factor is multiplication by that
function on the tensor product.** On a local pure tensor it is `m ⊗ n ↦ m ⊗ (r n) = r (m ⊗ n)`,
the scalar passing through the canonical map from the presheaf tensor product because that map
is linear. -/
theorem tensorSheafMap_globalSmulCenter_right (Z : Scheme.{u}) (r : Γ(Z, ⊤))
    (A B : SheafOfModules.{u} (structureSheafRing Z.toRingedSpace)) :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨Z.toRingedSpace.presheaf, Z.toRingedSpace.IsSheaf⟩)).map
        ((𝟙 A, (globalSmulCenter Z r).app B) : (_, _) ⟶ (_, _)))
      = (globalSmulCenter Z r).app
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨Z.toRingedSpace.presheaf, Z.toRingedSpace.IsSheaf⟩).obj A).obj B) := by
  refine Stacks.SheafOfModules.OnSpace.tensor_hom_ext Z.toRingedSpace fun U a b => ?_
  obtain ⟨U⟩ := U
  let : Module (Z.toRingedSpace.presheaf.obj (Opposite.op U))
      ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    ⟨Z.toRingedSpace.presheaf, Z.toRingedSpace.IsSheaf⟩).obj A).obj B).val.obj (Opposite.op U)) :=
    Stacks.SheafOfModules.Tensor.ringSheafSectionModule
      ⟨Z.toRingedSpace.presheaf, Z.toRingedSpace.IsSheaf⟩ (Opposite.op U) _
  refine (tensorSheafMap_app_toTensorSheafSection Z.toRingedSpace A B A B (𝟙 A)
    ((globalSmulCenter Z r).app B) U a b).trans ?_
  change toTensorSheafSection Z.toRingedSpace A B (Opposite.op U)
      (a ⊗ₜ[Z.presheaf.obj (Opposite.op U)] (Z.presheaf.map U.leTop.op r • b))
    = Z.presheaf.map U.leTop.op r •
        toTensorSheafSection Z.toRingedSpace A B (Opposite.op U)
          (a ⊗ₜ[Z.presheaf.obj (Opposite.op U)] b)
  rw [TensorProduct.tmul_smul]
  exact map_smul ((sheafifyUnit Z.toRingedSpace
    (PresheafOfModules.tensorObj (O := Z.presheaf) A.val B.val)).app (Opposite.op U)).hom _ _

/-- **Multiplication by a global function on the first tensor factor is multiplication by that
function on the tensor product.** On a local pure tensor the scalar is moved to the second factor
by `TensorProduct.smul_tmul`, the two factors being modules over the same commutative ring of
local functions, and then out by `AlgebraicGeometry.tensorSheafMap_globalSmulCenter_right`'s
computation. -/
theorem tensorSheafMap_globalSmulCenter_left (Z : Scheme.{u}) (r : Γ(Z, ⊤))
    (A B : SheafOfModules.{u} (structureSheafRing Z.toRingedSpace)) :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨Z.toRingedSpace.presheaf, Z.toRingedSpace.IsSheaf⟩)).map
        (((globalSmulCenter Z r).app A, 𝟙 B) : (_, _) ⟶ (_, _)))
      = (globalSmulCenter Z r).app
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨Z.toRingedSpace.presheaf, Z.toRingedSpace.IsSheaf⟩).obj A).obj B) := by
  refine Stacks.SheafOfModules.OnSpace.tensor_hom_ext Z.toRingedSpace fun U a b => ?_
  obtain ⟨U⟩ := U
  let : Module (Z.toRingedSpace.presheaf.obj (Opposite.op U))
      ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    ⟨Z.toRingedSpace.presheaf, Z.toRingedSpace.IsSheaf⟩).obj A).obj B).val.obj (Opposite.op U)) :=
    Stacks.SheafOfModules.Tensor.ringSheafSectionModule
      ⟨Z.toRingedSpace.presheaf, Z.toRingedSpace.IsSheaf⟩ (Opposite.op U) _
  refine (tensorSheafMap_app_toTensorSheafSection Z.toRingedSpace A B A B
    ((globalSmulCenter Z r).app A) (𝟙 B) U a b).trans ?_
  change toTensorSheafSection Z.toRingedSpace A B (Opposite.op U)
      ((Z.presheaf.map U.leTop.op r • a) ⊗ₜ[Z.presheaf.obj (Opposite.op U)] b)
    = Z.presheaf.map U.leTop.op r •
        toTensorSheafSection Z.toRingedSpace A B (Opposite.op U)
          (a ⊗ₜ[Z.presheaf.obj (Opposite.op U)] b)
  rw [TensorProduct.smul_tmul, TensorProduct.tmul_smul]
  exact map_smul ((sheafifyUnit Z.toRingedSpace
    (PresheafOfModules.tensorObj (O := Z.presheaf) A.val B.val)).app (Opposite.op U)).hom _ _

end GlobalScalar

/-! ### The tensor product of modules on an `R`-scheme is `R`-bilinear on morphisms -/

section Bilinear

open Stacks.RegularSequence (globalSmulCenter)

variable (R : Type u) [CommRing R] (W : Over (Spec (.of R)))

/-- The image of the base ring among the global functions of an `R`-scheme. This is the ring
morphism whose multiplication operators are the scalar action of
`AlgebraicGeometry.modulesLinear`: `AlgebraicGeometry.baseRingToSections` is its composite with
restriction to an open. -/
abbrev baseRingToGlobalSections : R →+* Γ(W.left, ⊤) :=
  ((forget₂ CommRingCat RingCat).map
    ((Scheme.ΓSpecIso (.of R)).inv ≫ W.hom.appTop)).hom

/-- **The base scalar acts by multiplication by a global function.** The centre element of
`AlgebraicGeometry.modulesLinear` attached to `c : R` is multiplication by the image of `c` among
the global functions, on the nose. -/
theorem baseScalar_eq_globalSmulCenter (c : R) :
    baseScalar R W c = globalSmulCenter W.left (baseRingToGlobalSections R W c) := rfl

/-- **The tensor product of modules on an `R`-scheme is `R`-linear in its first variable.**
A scalar is by definition multiplication by a global function precomposed, the tensor product of
maps composes factorwise, and multiplication by a global function on one factor is
multiplication by it on the tensor product. -/
theorem tensorSheafMap_smul_left (c : R)
    {A B C D : SheafOfModules.{u} (structureSheafRing W.left.toRingedSpace)}
    (α : A ⟶ C) (β : B ⟶ D) :
    letI : Linear R (SheafOfModules.{u} (structureSheafRing W.left.toRingedSpace)) :=
      modulesLinear R W
    letI : Linear R (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        ⟨W.left.toRingedSpace.presheaf, W.left.toRingedSpace.IsSheaf⟩)) :=
      modulesLinear R W
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨W.left.toRingedSpace.presheaf, W.left.toRingedSpace.IsSheaf⟩)).map
              ((c • α, β) : (_, _) ⟶ (_, _)))
      = c • ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨W.left.toRingedSpace.presheaf, W.left.toRingedSpace.IsSheaf⟩)).map
              ((α, β) : (_, _) ⟶ (_, _))) := by
  let : Linear R (SheafOfModules.{u} (structureSheafRing W.left.toRingedSpace)) :=
    modulesLinear R W
  let : Linear R (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      ⟨W.left.toRingedSpace.presheaf, W.left.toRingedSpace.IsSheaf⟩)) :=
    modulesLinear R W
  have h := tensorSheafMap_comp_tensorSheafMap W.left.toRingedSpace
    ((globalSmulCenter W.left (baseRingToGlobalSections R W c)).app A) α (𝟙 B) β
  erw [tensorSheafMap_globalSmulCenter_left, Category.id_comp] at h
  exact h.symm

/-- **The tensor product of modules on an `R`-scheme is `R`-linear in its second variable**, the
mirror of `AlgebraicGeometry.tensorSheafMap_smul_left`. -/
theorem tensorSheafMap_smul_right (c : R)
    {A B C D : SheafOfModules.{u} (structureSheafRing W.left.toRingedSpace)}
    (α : A ⟶ C) (β : B ⟶ D) :
    letI : Linear R (SheafOfModules.{u} (structureSheafRing W.left.toRingedSpace)) :=
      modulesLinear R W
    letI : Linear R (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        ⟨W.left.toRingedSpace.presheaf, W.left.toRingedSpace.IsSheaf⟩)) :=
      modulesLinear R W
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨W.left.toRingedSpace.presheaf, W.left.toRingedSpace.IsSheaf⟩)).map
              ((α, c • β) : (_, _) ⟶ (_, _)))
      = c • ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨W.left.toRingedSpace.presheaf, W.left.toRingedSpace.IsSheaf⟩)).map
              ((α, β) : (_, _) ⟶ (_, _))) := by
  let : Linear R (SheafOfModules.{u} (structureSheafRing W.left.toRingedSpace)) :=
    modulesLinear R W
  let : Linear R (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      ⟨W.left.toRingedSpace.presheaf, W.left.toRingedSpace.IsSheaf⟩)) :=
    modulesLinear R W
  have h := tensorSheafMap_comp_tensorSheafMap W.left.toRingedSpace (𝟙 A) α
    ((globalSmulCenter W.left (baseRingToGlobalSections R W c)).app B) β
  erw [tensorSheafMap_globalSmulCenter_right, Category.id_comp] at h
  exact h.symm

end Bilinear

/-- The external tensor product of maps is the tensor map of the left pullback, followed by the
tensor map of the right pullback. -/
private theorem externalTensorProductMap_eq_app_comp_map {X Y S : Scheme.{u}} (f : X ⟶ S)
    (g : Y ⟶ S) {E E' : X.Modules} {G G' : Y.Modules} (φ : E ⟶ E') (ψ : G ⟶ G') :
    externalTensorProductMap f g φ ψ =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨(pullback f g).toRingedSpace.presheaf, (pullback f g).toRingedSpace.IsSheaf⟩).map
          ((Scheme.Modules.pullback (pullback.fst f g)).map φ)).app
          ((Scheme.Modules.pullback (pullback.snd f g)).obj G) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨(pullback f g).toRingedSpace.presheaf, (pullback f g).toRingedSpace.IsSheaf⟩).obj
            ((Scheme.Modules.pullback (pullback.fst f g)).obj E')).map
          ((Scheme.Modules.pullback (pullback.snd f g)).map ψ) :=
  rfl

/-! ### The external tensor product of maps over an affine base is bilinear -/

section ExternalBilinear

variable (R : Type u) [CommRing R] (X Y : Over (Spec (.of R)))

/-- The fibre product `X ×_{Spec R} Y` as an `R`-scheme, through the first projection followed by
the structure morphism of `X`. This is the `R`-scheme whose modules the external tensor product
lives on, and it is what supplies the `R`-linear structure on the target of
`AlgebraicGeometry.externalTensorProductMap`. -/
abbrev externalTensorOver : Over (Spec (.of R)) :=
  Over.mk (pullback.fst X.hom Y.hom ≫ X.hom)

/-- The first projection of `X ×_{Spec R} Y`, as a morphism of `R`-schemes. -/
def externalTensorOverFst : externalTensorOver R X Y ⟶ X :=
  Over.homMk (pullback.fst X.hom Y.hom)

/-- The second projection of `X ×_{Spec R} Y`, as a morphism of `R`-schemes. That it *is* one is
the commutativity of the pullback square. -/
def externalTensorOverSnd : externalTensorOver R X Y ⟶ Y :=
  Over.homMk (pullback.snd X.hom Y.hom) pullback.condition.symm

/-- **The external tensor product of maps is `R`-linear in its first variable**: `(c • a) ⊠ b`
is `c • (a ⊠ b)`. Pullback along the first projection is `R`-linear by
`AlgebraicGeometry.over_pullback_linear`, and the tensor product on the fibre product is
`R`-linear in its first variable by `AlgebraicGeometry.tensorSheafMap_smul_left`. -/
theorem externalTensorProductMap_smul_left (c : R) {E E' : X.left.Modules}
    {G G' : Y.left.Modules} (φ : E ⟶ E') (ψ : G ⟶ G') :
    letI : Linear R X.left.Modules := modulesLinear R X
    letI : Linear R (pullback X.hom Y.hom).Modules :=
      modulesLinear R (externalTensorOver R X Y)
    externalTensorProductMap X.hom Y.hom (c • φ) ψ
      = c • externalTensorProductMap X.hom Y.hom φ ψ := by
  let : Linear R X.left.Modules := modulesLinear R X
  let : Linear R (pullback X.hom Y.hom).Modules :=
    modulesLinear R (externalTensorOver R X Y)
  have : (Scheme.Modules.pullback (pullback.fst X.hom Y.hom)).Linear R :=
    over_pullback_linear R (externalTensorOverFst R X Y)
  have key := tensorSheafMap_smul_left R (externalTensorOver R X Y) c
    ((Scheme.Modules.pullback (pullback.fst X.hom Y.hom)).map φ)
    ((Scheme.Modules.pullback (pullback.snd X.hom Y.hom)).map ψ)
  refine Eq.trans ?_ key
  dsimp only [externalTensorProductMap]
  erw [Functor.map_smul]
  rfl

/-- **The external tensor product of maps is `R`-linear in its second variable**: `a ⊠ (c • b)`
is `c • (a ⊠ b)`, the mirror of `AlgebraicGeometry.externalTensorProductMap_smul_left`. -/
theorem externalTensorProductMap_smul_right (c : R) {E E' : X.left.Modules}
    {G G' : Y.left.Modules} (φ : E ⟶ E') (ψ : G ⟶ G') :
    letI : Linear R Y.left.Modules := modulesLinear R Y
    letI : Linear R (pullback X.hom Y.hom).Modules :=
      modulesLinear R (externalTensorOver R X Y)
    externalTensorProductMap X.hom Y.hom φ (c • ψ)
      = c • externalTensorProductMap X.hom Y.hom φ ψ := by
  let : Linear R Y.left.Modules := modulesLinear R Y
  let : Linear R (pullback X.hom Y.hom).Modules :=
    modulesLinear R (externalTensorOver R X Y)
  have : (Scheme.Modules.pullback (pullback.snd X.hom Y.hom)).Linear R :=
    over_pullback_linear R (externalTensorOverSnd R X Y)
  have key := tensorSheafMap_smul_right R (externalTensorOver R X Y) c
    ((Scheme.Modules.pullback (pullback.fst X.hom Y.hom)).map φ)
    ((Scheme.Modules.pullback (pullback.snd X.hom Y.hom)).map ψ)
  refine Eq.trans ?_ key
  dsimp only [externalTensorProductMap]
  erw [Functor.map_smul]
  rfl

/-- **A scalar passes from either factor of an external tensor product of maps to the other**:
`(c • a) ⊠ b = a ⊠ (c • b)`. This is the relation that bi-additivity does not give, and it is
what says that the pairing `(a, b) ↦ a ⊠ b` annihilates the `R`-bilinearity relations between
`Hom(ℰ, ℰ')` and `Hom(𝒢, 𝒢')`; it mentions no linear structure on the modules of the fibre
product, both sides being `c • (a ⊠ b)` there. -/
theorem externalTensorProductMap_smul_left_eq_smul_right (c : R) {E E' : X.left.Modules}
    {G G' : Y.left.Modules} (φ : E ⟶ E') (ψ : G ⟶ G') :
    letI : Linear R X.left.Modules := modulesLinear R X
    letI : Linear R Y.left.Modules := modulesLinear R Y
    externalTensorProductMap X.hom Y.hom (c • φ) ψ
      = externalTensorProductMap X.hom Y.hom φ (c • ψ) :=
  (externalTensorProductMap_smul_left R X Y c φ ψ).trans
    (externalTensorProductMap_smul_right R X Y c φ ψ).symm

end ExternalBilinear

variable {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

/-- **The external tensor product of a pair of zero maps is zero.** -/
theorem externalTensorProductMap_zero_zero {E E' : X.Modules} {G G' : Y.Modules} :
    externalTensorProductMap f g (0 : E ⟶ E') (0 : G ⟶ G') = 0 := by
  have h₁ : (Scheme.Modules.pullback (pullback.fst f g)).map (0 : E ⟶ E') = 0 :=
    Functor.map_zero _ _ _
  have h₂ : (Scheme.Modules.pullback (pullback.snd f g)).map (0 : G ⟶ G') = 0 :=
    Functor.map_zero _ _ _
  exact (congrArg ((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨(pullback f g).toRingedSpace.presheaf,
          (pullback f g).toRingedSpace.IsSheaf⟩)).map
      (X := ((Scheme.Modules.pullback (pullback.fst f g)).obj E,
        (Scheme.Modules.pullback (pullback.snd f g)).obj G))
      (Y := ((Scheme.Modules.pullback (pullback.fst f g)).obj E',
        (Scheme.Modules.pullback (pullback.snd f g)).obj G')))
      (Prod.ext h₁ h₂)).trans
    (tensorSheafMap_zero_zero _)

/-- **The external tensor product of a pair of identities is the identity.** -/
theorem externalTensorProductMap_id (E : X.Modules) (G : Y.Modules) :
    externalTensorProductMap f g (𝟙 E) (𝟙 G) = 𝟙 (externalTensorProduct f g E G) :=
  (Functor.prod (Scheme.Modules.pullback (pullback.fst f g))
    (Scheme.Modules.pullback (pullback.snd f g)) ⋙
      Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨(pullback f g).toRingedSpace.presheaf,
          (pullback f g).toRingedSpace.IsSheaf⟩)).map_id (E, G)

/-- **External tensor products of maps compose factorwise.** -/
theorem externalTensorProductMap_comp {E₁ E₂ E₃ : X.Modules} {G₁ G₂ G₃ : Y.Modules}
    (a : E₁ ⟶ E₂) (b : E₂ ⟶ E₃) (c : G₁ ⟶ G₂) (d : G₂ ⟶ G₃) :
    externalTensorProductMap f g a c ≫ externalTensorProductMap f g b d
      = externalTensorProductMap f g (a ≫ b) (c ≫ d) :=
  ((Functor.prod (Scheme.Modules.pullback (pullback.fst f g))
    (Scheme.Modules.pullback (pullback.snd f g)) ⋙
      Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨(pullback f g).toRingedSpace.presheaf,
          (pullback f g).toRingedSpace.IsSheaf⟩)).map_comp
        ((a, c) : (E₁, G₁) ⟶ (E₂, G₂))
        ((b, d) : (E₂, G₂) ⟶ (E₃, G₃))).symm

/-! ### Additivity, and vanishing as soon as one factor vanishes -/

/-- **The external tensor product of maps is additive in its first variable.** The external
tensor product of `φ` and `ψ` is the action of `Stacks.SheafOfModules.Tensor.sheafTensor` on the
pullback of `φ` in its left variable, followed by its action on the pullback of `ψ` in its right
one, so this is the additivity of the pullback functor and of `sheafTensor` in its left variable
followed by the distributivity of composition. -/
theorem externalTensorProductMap_add_left {E E' : X.Modules} {G G' : Y.Modules}
    (φ φ' : E ⟶ E') (ψ : G ⟶ G') :
    externalTensorProductMap f g (φ + φ') ψ
      = externalTensorProductMap f g φ ψ + externalTensorProductMap f g φ' ψ :=
  by
  rw [externalTensorProductMap_eq_app_comp_map, externalTensorProductMap_eq_app_comp_map,
    externalTensorProductMap_eq_app_comp_map,
    Functor.map_add (Scheme.Modules.pullback (pullback.fst f g))]
  erw [Functor.map_add, NatTrans.app_add, Preadditive.add_comp]
  rfl

/-- **The external tensor product of maps is additive in its second variable**, the mirror of
`AlgebraicGeometry.externalTensorProductMap_add_left`. The additivity of
`Stacks.SheafOfModules.Tensor.sheafTensor` in its right variable is carried by
`Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive`, which is named rather than searched for
because its module argument is read here at the `AlgebraicGeometry.Scheme.Modules` spelling of
the category and instance search is keyed on the other one. -/
theorem externalTensorProductMap_add_right {E E' : X.Modules} {G G' : Y.Modules}
    (φ : E ⟶ E') (ψ ψ' : G ⟶ G') :
    externalTensorProductMap f g φ (ψ + ψ')
      = externalTensorProductMap f g φ ψ + externalTensorProductMap f g φ ψ' :=
  have : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨(pullback f g).toRingedSpace.presheaf, (pullback f g).toRingedSpace.IsSheaf⟩).obj
          ((Scheme.Modules.pullback (pullback.fst f g)).obj E')).Additive :=
    Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive _ _
  by
  rw [externalTensorProductMap_eq_app_comp_map, externalTensorProductMap_eq_app_comp_map,
    externalTensorProductMap_eq_app_comp_map,
    Functor.map_add (Scheme.Modules.pullback (pullback.snd f g))]
  erw [Functor.map_add, Preadditive.comp_add]
  rfl

/-- **The external tensor product of a zero map with any map is zero**, read off additivity in
the first variable at `φ = φ' = 0`. -/
theorem externalTensorProductMap_zero_left {E E' : X.Modules} {G G' : Y.Modules}
    (ψ : G ⟶ G') : externalTensorProductMap f g (0 : E ⟶ E') ψ = 0 :=
  (left_eq_add (a := externalTensorProductMap f g (0 : E ⟶ E') ψ)).mp
    (by rw [← externalTensorProductMap_add_left, add_zero])

/-- **The external tensor product of any map with a zero map is zero**, read off additivity in
the second variable at `ψ = ψ' = 0`. -/
theorem externalTensorProductMap_zero_right {E E' : X.Modules} {G G' : Y.Modules}
    (φ : E ⟶ E') : externalTensorProductMap f g φ (0 : G ⟶ G') = 0 :=
  (left_eq_add (a := externalTensorProductMap f g φ (0 : G ⟶ G'))).mp
    (by rw [← externalTensorProductMap_add_right, add_zero])

end AlgebraicGeometry

end

end
