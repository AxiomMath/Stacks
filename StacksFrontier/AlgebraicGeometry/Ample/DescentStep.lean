module

public import StacksFrontier.Topology.Sheaves.Modules.Invertible

/-!
# Invertible sheaves of modules have tensor inverses

Let `𝒪` be a sheaf of commutative rings on a site `(C, J)` with sheafification. Tag 01CS
defines a sheaf of `𝒪`-modules `L` to be *invertible* when tensoring by `L` is an
autoequivalence of the category of `𝒪`-modules. This file proves the concrete
characterisation of Tag 0B8K: `L` is invertible exactly when there is some `N` with
`L ⊗_𝒪 N ≅ 𝒪`.

The content is the functor-level comparison
`(- ⊗ (L ⊗ N)) ≅ (- ⊗ N) ⋙ (- ⊗ L)`, which is what turns a single tensor inverse into a
quasi-inverse of the whole tensor functor. It is assembled from the presheaf associator and
from Tag 05NA, which says that sheafifying a tensor product does not change if one of the
factors is replaced by its sheafification.

## Main results

* `Stacks.SheafOfModules.Invertible.isInvertible_iff_exists_tensor_iso_unit` is Tag 0B8K: an
  `𝒪`-module sheaf is invertible if and only if it has a tensor inverse.
* `Stacks.SheafOfModules.tensorLeftFunctorObjIso` is the functor-level
  associativity comparison described above.
* `Stacks.SheafOfModules.Invertible.tensorLeftFunctorUnitIso` identifies tensoring by the
  structure sheaf with the identity functor.
* `Stacks.SheafOfModules.Invertible.isInvertible_of_iso` transports invertibility along an
  isomorphism of module sheaves.

## Implementation notes

`(Stacks.SheafOfModules.Tensor.sheafTensor _).obj L` is `F ↦ (L ⊗ F)^#`, built out of
Mathlib's `tensorLeft` on `PresheafOfModules` followed by
  `Stacks.SheafOfModules.TensorSheafification.sheafify`. The two
auxiliary isomorphisms `tensorSheafifyLeftIso` and `tensorSheafifyRightIso` say that the
sheafification unit may be inserted in either tensor slot without changing the sheafification,
which is exactly `Stacks.SheafOfModules.TensorSheafification.isIso_sheafify_map_whiskerLeft` and
`Stacks.SheafOfModules.TensorSheafification.isIso_sheafify_map_whiskerRight` applied to a
  sheafification unit. These are the
only inputs besides the monoidal and symmetric structures on presheaves of modules, both of
which are transported from `PresheafOfModules
  (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪)` — the same
category as
  `PresheafOfModules (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj` — by
  `local instance`s.

Tag 0B8K also contains the statements that an invertible sheaf is locally a direct summand of
a finite free sheaf, and that any tensor inverse is canonically the dual sheaf. Those are not
in this file; only the tensor-inverse characterisation is.

## References

* [Stacks Project, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
-/

@[expose] public section

open CategoryTheory MonoidalCategory
open AlgebraicGeometry.SheafOfModules (IsInvertible
  isInvertible_iff_tensorLeftFunctor_isEquivalence)

universe v u w

namespace Stacks.SheafOfModules.Invertible

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules

/-- The sheafification unit, with the restriction-of-scalars along the identity — which is the
identity functor — left implicit, so that it can be whiskered against `tensorLeft`. -/
noncomputable abbrev unitToForget :
    𝟭 (PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj) ⟶
      Stacks.SheafOfModules.TensorSheafification.sheafify O hO ⋙
        _root_.SheafOfModules.forget (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
          hO) :=
  (Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction O hO).unit

/-- Sheafifying the underlying presheaf of a sheaf of modules returns it unchanged: the counit
of the sheafification adjunction is an isomorphism. -/
noncomputable def sheafifyForgetIso :
    _root_.SheafOfModules.forget (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) ⋙
        Stacks.SheafOfModules.TensorSheafification.sheafify O hO ≅
      Functor.id (_root_.SheafOfModules.{w}
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) := by
  letI : IsIso (Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction O hO).counit := by
    change IsIso
      (PresheafOfModules.sheafificationAdjunction
        (𝟙 (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj)).counit
    infer_instance
  exact
    (eqToIso (rfl :
      (_root_.SheafOfModules.forget (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)
        ⋙
          PresheafOfModules.restrictScalars
            (𝟙 (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj)) ⋙
          Stacks.SheafOfModules.TensorSheafification.sheafify O hO =
        _root_.SheafOfModules.forget (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
          hO) ⋙
          Stacks.SheafOfModules.TensorSheafification.sheafify O hO).symm) ≪≫
      asIso (Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction O hO).counit

/-- Inserting a sheafification unit in the right-hand tensor slot does not change the
sheafification of the tensor product: `(A ⊗ -)^# ≅ (A ⊗ (-)^#)^#`. -/
noncomputable def tensorSheafifyLeftIso
    (A : PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
      :
    tensorLeft A ⋙ Stacks.SheafOfModules.TensorSheafification.sheafify O hO ≅
      Stacks.SheafOfModules.TensorSheafification.sheafify O hO ⋙
        _root_.SheafOfModules.forget (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
          hO) ⋙
          tensorLeft A ⋙ Stacks.SheafOfModules.TensorSheafification.sheafify O hO := by
  let η := Functor.whiskerRight (unitToForget O hO) (tensorLeft A ⋙
    Stacks.SheafOfModules.TensorSheafification.sheafify O hO)
  haveI : ∀ X, IsIso (η.app X) := fun X ↦
    Stacks.SheafOfModules.TensorSheafification.isIso_sheafify_map_whiskerLeft O hO A
      (Stacks.SheafOfModules.TensorSheafification.toSheafify O hO X)
      (Stacks.SheafOfModules.TensorSheafification.isIso_sheafify_map_toSheafify O hO X)
  haveI := NatIso.isIso_of_isIso_app η
  let e := asIso η
  exact e

/-- Inserting a sheafification unit in the left-hand tensor slot does not change the
sheafification of the tensor product: `(A ⊗ -)^# ≅ ((A)^# ⊗ -)^#`. -/
noncomputable def tensorSheafifyRightIso
    (A : PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
      :
    tensorLeft A ⋙ Stacks.SheafOfModules.TensorSheafification.sheafify O hO ≅
      tensorLeft ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj A).val ⋙
        Stacks.SheafOfModules.TensorSheafification.sheafify O hO := by
  let η := Functor.whiskerRight ((curriedTensor _).map ((unitToForget O hO).app A))
    (Stacks.SheafOfModules.TensorSheafification.sheafify O hO)
  haveI : ∀ X, IsIso (η.app X) := fun X ↦
    Stacks.SheafOfModules.TensorSheafification.isIso_sheafify_map_whiskerRight O hO
      (Stacks.SheafOfModules.TensorSheafification.toSheafify O hO A) X
      (Stacks.SheafOfModules.TensorSheafification.isIso_sheafify_map_toSheafify O hO A)
  haveI := NatIso.isIso_of_isIso_app η
  let e := asIso η
  exact e

/-- Tensoring by the structure sheaf is the identity functor. -/
noncomputable def tensorLeftFunctorUnitIso :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj
        (_root_.SheafOfModules.unit
          (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) ≅
      Functor.id (_root_.SheafOfModules.{w}
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :=
  Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft
        (_root_.SheafOfModules.forget (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
          hO))
        (leftUnitorNatIso _))
      (Stacks.SheafOfModules.TensorSheafification.sheafify O hO) ≪≫
    sheafifyForgetIso O hO

/-- Isomorphic module sheaves have isomorphic tensor functors. -/
noncomputable def tensorLeftFunctorCongr
    {A B : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO)} (e : A ≅ B) :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj A ≅
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj B :=
  Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft (_root_.SheafOfModules.forget
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
      ((curriedTensor _).mapIso
        ((_root_.SheafOfModules.forget (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
          hO)).mapIso e)))
    (Stacks.SheafOfModules.TensorSheafification.sheafify O hO)

/-- A tensor inverse `e : L ⊗ N ≅ 𝒪` makes tensoring by `N` followed by tensoring by `L`
isomorphic to the identity functor. -/
private noncomputable def tensorLeftFunctorCompIsoId
    {L N : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO)}
    (e : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj L).obj N ≅
      _root_.SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj N ⋙
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj L ≅
      Functor.id _ :=
  (Stacks.SheafOfModules.tensorLeftFunctorObjIso O hO L N).symm ≪≫
    tensorLeftFunctorCongr O hO e ≪≫ tensorLeftFunctorUnitIso O hO

/-- **Stacks Project, Tag 0B8K.** A sheaf of modules is invertible if and only if it has a
tensor inverse, that is, if and only if some `N` satisfies `L ⊗ N ≅ 𝒪`. -/
@[stacks 0B8K "tensor_inverse_characterization"]
theorem isInvertible_iff_exists_tensor_iso_unit
    (L : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
      :
    IsInvertible O hO L ↔
      ∃ N : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
        hO),
        Nonempty (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
          ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj L).obj N ≅
          _root_.SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
            hO)) := by
  constructor
  · intro h
    exact ⟨((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj
          L).objPreimage
      (_root_.SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)),
      ⟨((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj
          L).objObjPreimageIso _⟩⟩
  · rintro ⟨N, ⟨e⟩⟩
    refine (isInvertible_iff_tensorLeftFunctor_isEquivalence O hO L).mpr
      (Functor.IsEquivalence.mk' _
        (tensorLeftFunctorCompIsoId O hO
          ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).mapIso (β_ N.val L.val) ≪≫
            e)).symm
        (tensorLeftFunctorCompIsoId O hO e))

/-- A module sheaf with a tensor inverse is invertible. This is the direction of Tag 0B8K
that is used to recognise invertible sheaves. -/
theorem isInvertible_of_tensor_iso_unit
    {L N : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO)}
    (e : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj L).obj N ≅
      _root_.SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    IsInvertible O hO L :=
  (isInvertible_iff_exists_tensor_iso_unit O hO L).mpr ⟨N, ⟨e⟩⟩

/-- Invertibility only depends on the isomorphism class of a module sheaf. -/
theorem isInvertible_of_iso
    {L M : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO)} (e : L ≅ M)
    [IsInvertible O hO L] : IsInvertible O hO M :=
  (isInvertible_iff_tensorLeftFunctor_isEquivalence O hO M).mpr
    (Functor.isEquivalence_of_iso (tensorLeftFunctorCongr O hO e))

end Stacks.SheafOfModules.Invertible

end
