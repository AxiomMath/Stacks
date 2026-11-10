module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
public import Mathlib.Algebra.Colimit.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Linear.Yoneda
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.Order.CompletePartialOrder
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPreservesColimits
public import StacksFrontier.CategoryTheory.Sites.Modules.Flat
import StacksCore.Tactic.StacksAttribute

/-!
# Tensoring sheaves of modules commutes with colimits

Tensoring on the left by a fixed sheaf of modules preserves arbitrary small colimits.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.PresheafOfModules.tensorLeft`: tensoring presheaves of
  modules on the left by a fixed presheaf of modules, objectwise.
* `AlgebraicGeometry.SheafOfModules.presheafTensorLeft`: the same endofunctor, named for the
  ring presheaf underlying a sheaf of commutative rings.
* `AlgebraicGeometry.SheafOfModules.sheafTensorLeft`: tensoring sheaves of modules on the left
  by a fixed sheaf of modules, that is, sheafifying the objectwise tensor product.

## Main results

* `AlgebraicGeometry.SheafOfModules.PresheafOfModules.tensorLeft_preservesColimits`: the
  objectwise tensor functor on presheaves of modules preserves all colimits indexed in the
  module universe.
* `AlgebraicGeometry.SheafOfModules.sheafTensorLeft_preservesColimits`: so does its sheaf-level
  counterpart.

## Implementation notes

The results are stated for a sheaf of commutative rings on an arbitrary site; the ringed-space
formulation is obtained by taking the site of open subsets. The ring and module universes are
independent, and colimit diagrams have objects in the module universe and morphisms in an
arbitrary universe.

The objectwise statement holds because each evaluation of the tensor functor is a left adjoint,
the right adjoint being the hom functor out of the fixed module; the adjunction is built by hand
here rather than taken from the monoidal closed structure on modules, which would tie the module
universe to the ring universe.

The sheaf-level tensor product is the sheafification of the objectwise one, so the sheaf-level
statement follows from the objectwise one once sheafification is known to send a morphism
inverted by sheafification to an isomorphism after tensoring. That reduces to the fact that
tensoring preserves local bijections, which is
`Stacks.SheafOfModules.TensorColimits.TensorLocalization.W_whiskerRight` for tensoring on the
right and is transported to the left by the symmetry of the tensor product of modules.

Two presheaves of rings are definitionally equal here, the one underlying `R` composed with the
forgetful functor to rings and the underlying presheaf of the sheaf of rings associated with
`R`. Only the first has a reducible underlying ring at each object, so only the first lets the
module instances synthesize; every statement about modules below is phrased in that one
spelling, and the second occurs only as the sheaf of rings indexing a category of sheaves of
modules.

## References

* [Stacks Project, Tag 05NB](https://stacks.math.columbia.edu/tag/05NB)
* [Stacks Project, Tag 03EP](https://stacks.math.columbia.edu/tag/03EP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open TensorProduct
open Opposite

universe u v w z a

namespace AlgebraicGeometry.SheafOfModules

attribute [local implicit_reducible] PresheafOfModules.tensorObj PresheafOfModules.tensorMap

/- `moduleTensorLeft` and `moduleTensorAdjunction` are defined once, in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPreservesColimits`, and reused from here and
from `StacksFrontier.Algebra.Category.ModuleCat.Presheaf.FlatColimits`, which both need the same
module-universe-independent left tensor functor and its adjunction. -/
open Stacks.SheafOfModules.TensorColimits (moduleTensorLeft moduleTensorAdjunction)

section SheafTensor

variable {C : Type u} [Category.{v} C]

namespace PresheafOfModules

/-- Tensoring presheaves of modules on the left by `F`, objectwise. The module universe is
independent of the ring universe. -/
@[implicit_reducible]
noncomputable def tensorLeft {O : Cᵒᵖ ⥤ CommRingCat.{w}}
    (F : _root_.PresheafOfModules.{z} (ringPresheaf O)) :
    _root_.PresheafOfModules.{z} (ringPresheaf O) ⥤
      _root_.PresheafOfModules.{z} (ringPresheaf O) where
  obj G := tensorObj F G
  map {G H} φ :=
    { app := fun X => ModuleCat.ofHom (TensorProduct.map LinearMap.id (φ.app X).hom)
      naturality := by
        intro X Y g
        apply ModuleCat.hom_ext
        apply TensorProduct.ext
        ext x y
        change (F.map g).hom x ⊗ₜ[(ringPresheaf O).obj Y] (φ.app Y).hom ((G.map g).hom y) =
          (F.map g).hom x ⊗ₜ[(ringPresheaf O).obj Y] (H.map g).hom ((φ.app X).hom y)
        exact congrArg₂ (fun p q ↦ p ⊗ₜ[(ringPresheaf O).obj Y] q) rfl
          (_root_.PresheafOfModules.naturality_apply φ g y) }
  map_id G := by
    apply _root_.PresheafOfModules.hom_ext
    intro X
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext x y
    rfl
  map_comp φ ψ := by
    apply _root_.PresheafOfModules.hom_ext
    intro X
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext x y
    rfl

/-- Tensoring on the left by `F` and tensoring on the right by `F` agree, by the symmetry of
the tensor product of modules. -/
noncomputable def tensorLeftIsoTensorRight {O : Cᵒᵖ ⥤ CommRingCat.{w}}
    (F : _root_.PresheafOfModules.{z} (ringPresheaf O)) :
    tensorLeft F ≅ tensorRight F :=
  NatIso.ofComponents (fun G => _root_.PresheafOfModules.isoMk
    (fun X => (TensorProduct.comm ((ringPresheaf O).obj X) (F.obj X) (G.obj X)).toModuleIso)
    (by
      intro X Y g
      apply ModuleCat.hom_ext
      apply TensorProduct.ext
      ext x y
      rfl)) (by
        intro G H φ
        apply _root_.PresheafOfModules.hom_ext
        intro X
        apply ModuleCat.hom_ext
        apply TensorProduct.ext
        ext x y
        rfl)

/-- Tensoring presheaves of modules on the left by a fixed presheaf of modules preserves all
colimits indexed in the module universe: at each object it is a left adjoint. -/
@[stacks 03EP "part (1)"]
theorem tensorLeft_preservesColimits {O : Cᵒᵖ ⥤ CommRingCat.{w}}
    (F : _root_.PresheafOfModules.{z} (ringPresheaf O)) :
    PreservesColimitsOfSize.{a, z} (tensorLeft F) where
  preservesColimitsOfShape :=
    { preservesColimit :=
        { preserves := fun {c} hc => by
            refine ⟨_root_.PresheafOfModules.evaluationJointlyReflectsColimits _ _ (fun X => ?_)⟩
            let : PreservesColimitsOfSize.{a, z} (moduleTensorLeft (F.obj X)) :=
              (moduleTensorAdjunction (F.obj X)).leftAdjoint_preservesColimits
            exact isColimitOfPreserves (moduleTensorLeft (F.obj X))
              (isColimitOfPreserves (_root_.PresheafOfModules.evaluation _ X) hc) } }

end PresheafOfModules

variable (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- Tensoring on the left by `F` in the category of presheaves of modules over the ring
presheaf underlying a sheaf of commutative rings. -/
noncomputable def presheafTensorLeft (R : Sheaf J CommRingCat.{w})
    (F : _root_.PresheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf R).obj) :
    _root_.PresheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf R).obj ⥤
      _root_.PresheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf R).obj :=
  PresheafOfModules.tensorLeft (O := R.obj) F

variable [J.WEqualsLocallyBijective AddCommGrpCat.{z}]
  [HasWeakSheafify J AddCommGrpCat.{z}]

/-- Tensoring on the left by `F` in the category of sheaves of modules. The objectwise
presheaf tensor product is sheafified to obtain a sheaf. -/
noncomputable def sheafTensorLeft (R : Sheaf J CommRingCat.{w})
    (F : _root_.SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf R)) :
    _root_.SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf R) ⥤
      _root_.SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf R) :=
  _root_.SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf R) ⋙
    presheafTensorLeft J R F.val ⋙
    _root_.PresheafOfModules.sheafification (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- Sheafification sends a morphism it inverts to an isomorphism after tensoring on the
left. -/
private lemma isIso_sheafification_map_presheafTensorLeft_map (R : Sheaf J CommRingCat.{w})
    (F : _root_.PresheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)
    {P Q : _root_.PresheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf R).obj} (f : P ⟶ Q)
    (hf : IsIso ((_root_.PresheafOfModules.sheafification
      (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)).map f)) :
    IsIso ((_root_.PresheafOfModules.sheafification
      (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)).map
        ((presheafTensorLeft J R F).map f)) := by
  let L : _root_.PresheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf R).obj ⥤
      _root_.SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf R) :=
    _root_.PresheafOfModules.sheafification (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)
  have key : ∀ {P Q : _root_.PresheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf R).obj}
      (g : P ⟶ Q), IsIso (L.map g) ↔
        J.W ((_root_.PresheafOfModules.toPresheaf _).map g) := by
    intro P Q g
    change MorphismProperty.isomorphisms _ (L.map g) ↔ _
    change ((MorphismProperty.isomorphisms _).inverseImage L) g ↔ _
    rw [← _root_.PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms]
    rfl
  let T : _root_.PresheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf R).obj ⥤
      _root_.PresheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf R).obj :=
    PresheafOfModules.tensorRight (O := R.obj) F
  have hright : IsIso (L.map (T.map f)) :=
    (key (T.map f)).mpr
      (Stacks.SheafOfModules.TensorColimits.TensorLocalization.W_whiskerRight
        R.obj f F ((key f).mp hf))
  let e : presheafTensorLeft J R F ≅ T := PresheafOfModules.tensorLeftIsoTensorRight F
  have he : (presheafTensorLeft J R F).map f = e.hom.app P ≫ T.map f ≫ e.inv.app Q := by
    rw [← e.hom.naturality_assoc, e.hom_inv_id_app, Category.comp_id]
  change IsIso (L.map _)
  rw [he, L.map_comp, L.map_comp]
  infer_instance

/-- Sheafifying the objectwise left tensor functor gives the sheaf-level one. -/
private noncomputable def sheafTensorLeftIso (R : Sheaf J CommRingCat.{w})
    (F : _root_.SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf R)) :
    presheafTensorLeft J R F.val ⋙
        _root_.PresheafOfModules.sheafification (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj) ≅
      _root_.PresheafOfModules.sheafification (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj) ⋙ sheafTensorLeft J R F := by
  let L : _root_.PresheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf R).obj ⥤
      _root_.SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf R) :=
    _root_.PresheafOfModules.sheafification (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)
  let adj := _root_.PresheafOfModules.sheafificationAdjunction
    (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)
  let T := presheafTensorLeft J R F.val
  let τ : T ⋙ L ⟶ L ⋙ sheafTensorLeft J R F :=
    { app := fun P => L.map (T.map (adj.unit.app P))
      naturality := fun P Q f => by
        change L.map (T.map f) ≫ L.map (T.map (adj.unit.app Q)) =
          L.map (T.map (adj.unit.app P)) ≫
            L.map (T.map ((_root_.SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf R) ⋙
              _root_.PresheafOfModules.restrictScalars
                (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)).map (L.map f)))
        rw [← L.map_comp, ← L.map_comp, ← T.map_comp, ← T.map_comp]
        exact congrArg (fun g => L.map (T.map g)) (adj.unit.naturality f) }
  have hτ (P) : IsIso (τ.app P) := by
    apply isIso_sheafification_map_presheafTensorLeft_map
    change IsIso (L.map (adj.unit.app P))
    infer_instance
  letI : IsIso τ := NatIso.isIso_of_isIso_app τ
  exact asIso τ

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **Stacks Project, Tag 05NB.** Tensoring with a fixed sheaf of modules commutes with
all small colimits, independently of the ring universe. -/
@[stacks 05NB, stacks 03EP "part (2)", sga "5 V 1.2.1" "inductive limits"]
theorem sheafTensorLeft_preservesColimits (R : Sheaf J CommRingCat.{w})
    (F : _root_.SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf R)) :
    PreservesColimitsOfSize.{a, z} (sheafTensorLeft J R F) := by
  have : HasColimitsOfSize.{a, z} AddCommGrpCat.{z} := ⟨fun {_ _} => inferInstance⟩
  have h : PreservesColimitsOfSize.{a, z} (presheafTensorLeft J R F.val) :=
    PresheafOfModules.tensorLeft_preservesColimits (O := R.obj) F.val
  let adj := _root_.PresheafOfModules.sheafificationAdjunction
    (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)
  have := adj.fullyFaithfulROfIsIsoCounit.full
  have := adj.fullyFaithfulROfIsIsoCounit.faithful
  apply (adj.preservesColimitsOfSize_iff (sheafTensorLeft J R F)).mpr
  exact preservesColimits_of_natIso (sheafTensorLeftIso J R F)

end SheafTensor

end AlgebraicGeometry.SheafOfModules
