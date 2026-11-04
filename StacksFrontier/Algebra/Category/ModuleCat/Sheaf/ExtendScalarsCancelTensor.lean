module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatChangeOfRings
import StacksCore.Tactic.StacksAttribute

/-! # Cancelling an extension of scalars inside a tensor product of sheaves of modules

Let `f : O₁ ⟶ O₂` be a morphism of sheaves of commutative rings on a site `(C, J)`, let `G` be
a sheaf of `O₁`-modules and let `H` be a sheaf of `O₂`-modules. This file constructs the
identity

`H ⊗_{O₂} (O₂ ⊗_{O₁} G) = H|_{O₁} ⊗_{O₁} G`

as an isomorphism of the underlying sheaves of abelian groups, and computes it on the images of
pure tensors. Sectionwise it is `TensorProduct.AlgebraTensorModule.cancelBaseChange`.

## Main definitions

* `Stacks.FlatChangeOfRings.cancelExtendScalarsTensorSheafIso`:
  `H|_{O₁} ⊗_{O₁} G ≅ H ⊗_{O₂} (O₂ ⊗_{O₁} G)` as sheaves of abelian groups.
* `Stacks.FlatChangeOfRings.presheafCancelComparison`: the morphism of presheaves of
  `O₁`-modules of which that isomorphism is the sheafification.
* `Stacks.FlatChangeOfRings.sheafTensorSymmIso`: the symmetry `A ⊗_{O} B ≅ B ⊗_{O} A` of the
  tensor product sheaf, and `tensorObjCommOf` its objectwise counterpart.
* `Stacks.FlatChangeOfRings.cancelExtendScalarsTensorSheafIso'` and
  `presheafCancelComparison'`: the same identity and the same comparison with the extended
  factor on the left of both tensor products.

## Main results

* `Stacks.FlatChangeOfRings.presheafCancelComparison_apply`: the comparison on a pure tensor,
  `a ⊗ x ↦ a ⊗ (1 ⊗ x)`.
* `Stacks.FlatChangeOfRings.cancelExtendScalarsTensorSheafIso_hom`: the isomorphism is the
  sheafification of that comparison.
* `Stacks.FlatChangeOfRings.presheafCancelComparison'_apply`: the braided comparison on a pure
  tensor, `x ⊗ a ↦ (1 ⊗ x) ⊗ a`.
* `Stacks.FlatChangeOfRings.cancelExtendScalarsTensorSheafIso'_hom`: the braided isomorphism is
  the sheafification of the braided comparison.
* `Stacks.FlatChangeOfRings.toSheaf_map_sheafTensorSymmIso_hom`: the symmetry of the tensor
  product sheaf is, on underlying sheaves of abelian groups, the sheafification of the
  objectwise symmetry.

## Implementation notes

The two sides of the identity are sheaves of modules over different rings, `O₂` and `O₁`, so
the isomorphism is stated for the underlying sheaves of abelian groups.

## References

* [Stacks Project, Tag 05V4](https://stacks.math.columbia.edu/tag/05V4)
* [Stacks Project, Tag 03CU](https://stacks.math.columbia.edu/tag/03CU)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 08MQ](https://stacks.math.columbia.edu/tag/08MQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TensorProduct

universe v u w

namespace Stacks.FlatChangeOfRings

open Stacks
open Stacks.SheafOfModules.Tensor (ringSheaf sheafTensor)

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

variable {O₁ O₂ : Sheaf J CommRingCat.{w}} (f : O₁ ⟶ O₂)

/-- The identity `H|_{O₁} ⊗_{O₁} G = H ⊗_{O₂} (O₂ ⊗_{O₁} G)`, as an isomorphism of sheaves of
abelian groups. -/
def cancelExtendScalarsTensorSheafIso
    (G : SheafOfModules.{w} (ringSheaf O₁))
    (H : SheafOfModules.{w} (ringSheaf O₂)) :
    (SheafOfModules.toSheaf (ringSheaf O₁)).obj
        (((sheafTensor O₁).flip.obj G).obj
          ((SheafOfModules.restrictScalars.{w} (ringSheafMap f)).obj H)) ≅
      (SheafOfModules.toSheaf (ringSheaf O₂)).obj
        (((sheafTensor O₂).flip.obj ((extendScalars f).obj G)).obj H) :=
  (tensorBaseChangeSheafIso f G).app H ≪≫
    (SheafOfModules.toSheaf (ringSheaf O₂)).mapIso
      ((tensorRightExtendScalarsIso f G).app H.val)

/-! ## The symmetry of the tensor product sheaf -/

/-- The symmetry `M ⊗_{p,O} N ≅ N ⊗_{p,O} M` of the objectwise tensor product, over the presheaf
of rings `(Stacks.SheafOfModules.Tensor.ringSheaf O).obj`. -/
def tensorObjCommOf (O : Sheaf J CommRingCat.{w})
    (M N : PresheafOfModules.{w} (ringSheaf O).obj) :
    (tensorRightOf O N).obj M ≅ (tensorRightOf O M).obj N :=
  Stacks.tensorObjComm (O := O.obj) M N

/-- The symmetry `A ⊗_{O} B ≅ B ⊗_{O} A` of the tensor product sheaf: the sheafification of the
symmetry of the objectwise tensor product. -/
def sheafTensorSymmIso (O : Sheaf J CommRingCat.{w})
    (A B : SheafOfModules.{w} (ringSheaf O)) :
    ((sheafTensor O).flip.obj A).obj B ≅ ((sheafTensor O).flip.obj B).obj A :=
  (PresheafOfModules.sheafification (R := ringSheaf O)
    (𝟙 (ringSheaf O).obj)).mapIso (tensorObjCommOf O B.val A.val)

/-- On underlying sheaves of abelian groups, the symmetry of the tensor product sheaf is the
sheafification of the symmetry of the objectwise tensor product. -/
lemma toSheaf_map_sheafTensorSymmIso_hom (O : Sheaf J CommRingCat.{w})
    (A B : SheafOfModules.{w} (ringSheaf O)) :
    (SheafOfModules.toSheaf (ringSheaf O)).map
        (sheafTensorSymmIso O A B).hom =
      (presheafToSheaf J AddCommGrpCat.{w}).map
        ((PresheafOfModules.toPresheaf (ringSheaf O).obj).map
          (tensorObjCommOf O B.val A.val).hom) := rfl

/-! ## The comparison before sheafification, and its formula on pure tensors -/

/-- The comparison `H|_{O₁} ⊗_{p,O₁} G ⟶ (H ⊗_{p,O₂} (O₂ ⊗_{O₁} G))|_{O₁}` of presheaves of
`O₁`-modules, both tensor products being objectwise: the inverse of the presheaf-level base
change followed by the unit of sheafification in the second tensor factor. -/
def presheafCancelComparison
    (G : SheafOfModules.{w} (ringSheaf O₁))
    (H : SheafOfModules.{w} (ringSheaf O₂)) :
    (PresheafOfModules.restrictScalars (ringSheafMap f).hom ⋙
        tensorRightOf O₁ G.val).obj H.val ⟶
      (PresheafOfModules.restrictScalars (ringSheafMap f).hom).obj
        ((tensorRightOf O₂ ((extendScalars f).obj G).val).obj H.val) :=
  (baseChangeNatIsoOf f G).inv.app H.val ≫
    (PresheafOfModules.restrictScalars (ringSheafMap f).hom).map
      ((tensorRightNatTrans (O := O₂.obj) (toExtendScalarsVal f G)).app H.val)

/-- `presheafCancelComparison` sends a section `a ⊗ x` of `H|_{O₁} ⊗_{p,O₁} G` over `X` to
`a ⊗ (1 ⊗ x)`, the second factor being the image of the pure tensor `1 ⊗ x` of the sectionwise
extension of scalars under the unit of sheafification. -/
lemma presheafCancelComparison_apply
    (G : SheafOfModules.{w} (ringSheaf O₁))
    (H : SheafOfModules.{w} (ringSheaf O₂)) (X : Cᵒᵖ) :
    letI : Algebra (O₁.obj.obj X) (O₂.obj.obj X) := (f.hom.app X).hom.toAlgebra
    letI : Module (O₂.obj.obj X) (H.val.obj X) := (H.val.obj X).isModule
    letI : Module (O₁.obj.obj X) (G.val.obj X) := (G.val.obj X).isModule
    letI : Module (O₁.obj.obj X) (H.val.obj X) := Module.compHom _ (f.hom.app X).hom
    letI : Module (O₂.obj.obj X) (((extendScalars f).obj G).val.obj X) :=
      (((extendScalars f).obj G).val.obj X).isModule
    letI : Module (O₁.obj.obj X) (((sheafToPresheaf J CommRingCat).obj O₂).obj X) :=
      (f.hom.app X).hom.toModule
    ∀ (a : H.val.obj X) (x : G.val.obj X),
      PresheafOfModules.Hom.app (presheafCancelComparison f G H) X
          (a ⊗ₜ[O₁.obj.obj X] x) =
        a ⊗ₜ[O₂.obj.obj X]
          (PresheafOfModules.Hom.app (toExtendScalarsVal f G) X
            ((1 : O₂.obj.obj X) ⊗ₜ[O₁.obj.obj X] x)) :=
  fun _ _ => rfl

/-- `cancelExtendScalarsTensorSheafIso` is the sheafification of `presheafCancelComparison`. -/
lemma cancelExtendScalarsTensorSheafIso_hom
    (G : SheafOfModules.{w} (ringSheaf O₁))
    (H : SheafOfModules.{w} (ringSheaf O₂)) :
    (cancelExtendScalarsTensorSheafIso f G H).hom =
      (presheafToSheaf J AddCommGrpCat.{w}).map
        ((PresheafOfModules.toPresheaf (ringSheaf O₁).obj).map
          (presheafCancelComparison f G H)) := by
  rw [presheafCancelComparison, Functor.map_comp, Functor.map_comp]
  rfl

/-! ## The identity with the extended factor on the left -/

/-- The identity `G ⊗_{O₁} H|_{O₁} = (O₂ ⊗_{O₁} G) ⊗_{O₂} H`, as an isomorphism of sheaves of
abelian groups: `cancelExtendScalarsTensorSheafIso` with the extended factor moved to the left of
both tensor products. -/
def cancelExtendScalarsTensorSheafIso'
    (G : SheafOfModules.{w} (ringSheaf O₁))
    (H : SheafOfModules.{w} (ringSheaf O₂)) :
    (SheafOfModules.toSheaf (ringSheaf O₁)).obj
        (((sheafTensor O₁).flip.obj
          ((SheafOfModules.restrictScalars.{w} (ringSheafMap f)).obj H)).obj G) ≅
      (SheafOfModules.toSheaf (ringSheaf O₂)).obj
        (((sheafTensor O₂).flip.obj H).obj ((extendScalars f).obj G)) :=
  (SheafOfModules.toSheaf (ringSheaf O₁)).mapIso
      (sheafTensorSymmIso O₁ ((SheafOfModules.restrictScalars.{w} (ringSheafMap f)).obj H) G) ≪≫
    cancelExtendScalarsTensorSheafIso f G H ≪≫
    (SheafOfModules.toSheaf (ringSheaf O₂)).mapIso
      (sheafTensorSymmIso O₂ ((extendScalars f).obj G) H)

/-- The comparison `G ⊗_{p,O₁} H|_{O₁} ⟶ (H ⊗_{p,O₂} (O₂ ⊗_{O₁} G))|_{O₁}`:
`presheafCancelComparison` conjugated by the symmetry of the objectwise tensor product. -/
def presheafCancelComparison'
    (G : SheafOfModules.{w} (ringSheaf O₁))
    (H : SheafOfModules.{w} (ringSheaf O₂)) :
    (tensorRightOf O₁
        ((PresheafOfModules.restrictScalars (ringSheafMap f).hom).obj H.val)).obj G.val ⟶
      (PresheafOfModules.restrictScalars (ringSheafMap f).hom).obj
        ((tensorRightOf O₂ H.val).obj ((extendScalars f).obj G).val) :=
  (tensorObjCommOf O₁ G.val
      ((PresheafOfModules.restrictScalars (ringSheafMap f).hom).obj H.val)).hom ≫
    presheafCancelComparison f G H ≫
    (PresheafOfModules.restrictScalars (ringSheafMap f).hom).map
      (tensorObjCommOf O₂ H.val ((extendScalars f).obj G).val).hom

/-- `presheafCancelComparison'` sends a section `x ⊗ a` of `G ⊗_{p,O₁} H|_{O₁}` over `X` to
`(1 ⊗ x) ⊗ a`, the first factor being the image of the pure tensor `1 ⊗ x` of the sectionwise
extension of scalars under the unit of sheafification. -/
lemma presheafCancelComparison'_apply
    (G : SheafOfModules.{w} (ringSheaf O₁))
    (H : SheafOfModules.{w} (ringSheaf O₂)) (X : Cᵒᵖ) :
    letI : Algebra (O₁.obj.obj X) (O₂.obj.obj X) := (f.hom.app X).hom.toAlgebra
    letI : Module (O₂.obj.obj X) (H.val.obj X) := (H.val.obj X).isModule
    letI : Module (O₁.obj.obj X) (G.val.obj X) := (G.val.obj X).isModule
    letI : Module (O₁.obj.obj X) (H.val.obj X) := Module.compHom _ (f.hom.app X).hom
    letI : Module (O₂.obj.obj X) (((extendScalars f).obj G).val.obj X) :=
      (((extendScalars f).obj G).val.obj X).isModule
    letI : Module (O₁.obj.obj X) (((sheafToPresheaf J CommRingCat).obj O₂).obj X) :=
      (f.hom.app X).hom.toModule
    ∀ (x : G.val.obj X) (a : H.val.obj X),
      PresheafOfModules.Hom.app (presheafCancelComparison' f G H) X
          (x ⊗ₜ[O₁.obj.obj X] a) =
        (PresheafOfModules.Hom.app (toExtendScalarsVal f G) X
            ((1 : O₂.obj.obj X) ⊗ₜ[O₁.obj.obj X] x)) ⊗ₜ[O₂.obj.obj X] a :=
  fun _ _ => rfl

/-- `cancelExtendScalarsTensorSheafIso'` is the sheafification of `presheafCancelComparison'`. -/
lemma cancelExtendScalarsTensorSheafIso'_hom
    (G : SheafOfModules.{w} (ringSheaf O₁))
    (H : SheafOfModules.{w} (ringSheaf O₂)) :
    (cancelExtendScalarsTensorSheafIso' f G H).hom =
      (presheafToSheaf J AddCommGrpCat.{w}).map
        ((PresheafOfModules.toPresheaf (ringSheaf O₁).obj).map
          (presheafCancelComparison' f G H)) := by
  rw [presheafCancelComparison', Functor.map_comp, Functor.map_comp, Functor.map_comp,
    Functor.map_comp, ← cancelExtendScalarsTensorSheafIso_hom]
  rfl

end Stacks.FlatChangeOfRings

end
