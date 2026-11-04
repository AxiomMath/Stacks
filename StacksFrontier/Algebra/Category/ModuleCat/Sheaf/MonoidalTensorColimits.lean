module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorProductRightExact

/-!
# The monoidal product of sheaves of modules commutes with colimits in each variable

`Stacks.SheafOfModules.monoidalCategory 𝒪 h𝒪` is the monoidal structure on sheaves of modules
obtained by localizing the objectwise monoidal structure on presheaves of modules along
sheafification. This file shows that tensoring with a fixed sheaf of modules, on either side,
commutes with all colimits indexed in the module universe (Stacks 05NB, both variables), for that
monoidal structure itself rather than for the tensor product sheaf
`Stacks.SheafOfModules.Tensor.sheafTensor` it is isomorphic to.

## Main results

* `Stacks.SheafOfModules.preservesColimitsOfSize_tensorLeft` and
  `Stacks.SheafOfModules.preservesColimitsOfSize_tensorRight`.

## Implementation notes

Sheafification `L` is a monoidal functor of the localized structure, with tensorator the
isomorphism `Localization.Monoidal.μ`, so `L ⋙ tensorLeft (L P)` is isomorphic to
`tensorLeft P ⋙ L`, which commutes with colimits because both factors do. Since the right adjoint
of `L` is fully faithful, a functor out of sheaves commutes with colimits as soon as its
precomposite with `L` does (`CategoryTheory.Adjunction.preservesColimitsOfSize_iff`). A sheaf `F`
is the sheafification of its underlying presheaf, which reduces the statement for `tensorLeft F`
to the one for `tensorLeft (L F.val)`.

## References

* [Stacks Project, Tag 05NB](https://stacks.math.columbia.edu/tag/05NB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u v w

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w})
  (h𝒪 : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪))
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

attribute [local instance] monoidalCategory

/-- Sheafification intertwines tensoring on the left with a presheaf of modules and tensoring
on the left with its sheafification. -/
noncomputable def sheafifyCompTensorLeftIso
    (P : _root_.PresheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪)) :
    sheafifyFunctor 𝒪 h𝒪 ⋙ tensorLeft ((sheafifyFunctor 𝒪 h𝒪).obj P) ≅
      tensorLeft P ⋙ sheafifyFunctor 𝒪 h𝒪 :=
  NatIso.ofComponents
    (fun Q ↦ Localization.Monoidal.μ (sheafifyFunctor 𝒪 h𝒪) (localIso (J := J) 𝒪)
      (sheafifyUnitIso 𝒪 h𝒪) P Q)
    (fun g ↦ Localization.Monoidal.μ_natural_right (sheafifyFunctor 𝒪 h𝒪)
      (localIso (J := J) 𝒪) (sheafifyUnitIso 𝒪 h𝒪) P g)

/-- Sheafification intertwines tensoring on the right with a presheaf of modules and tensoring
on the right with its sheafification. -/
noncomputable def sheafifyCompTensorRightIso
    (P : _root_.PresheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪)) :
    sheafifyFunctor 𝒪 h𝒪 ⋙ tensorRight ((sheafifyFunctor 𝒪 h𝒪).obj P) ≅
      tensorRight P ⋙ sheafifyFunctor 𝒪 h𝒪 :=
  NatIso.ofComponents
    (fun Q ↦ Localization.Monoidal.μ (sheafifyFunctor 𝒪 h𝒪) (localIso (J := J) 𝒪)
      (sheafifyUnitIso 𝒪 h𝒪) Q P)
    (fun g ↦ Localization.Monoidal.μ_natural_left (sheafifyFunctor 𝒪 h𝒪)
      (localIso (J := J) 𝒪) (sheafifyUnitIso 𝒪 h𝒪) g P)

/-- Tensoring on the left with isomorphic objects gives isomorphic functors. -/
noncomputable def tensorLeftMapIso {D : Type*} [Category D] [MonoidalCategory D] {X Y : D}
    (e : X ≅ Y) : tensorLeft X ≅ tensorLeft Y :=
  NatIso.ofComponents (fun Z ↦ whiskerRightIso e Z) (fun g ↦ by simp [whisker_exchange])

/-- Tensoring on the right with isomorphic objects gives isomorphic functors. -/
noncomputable def tensorRightMapIso {D : Type*} [Category D] [MonoidalCategory D] {X Y : D}
    (e : X ≅ Y) : tensorRight X ≅ tensorRight Y :=
  NatIso.ofComponents (fun Z ↦ whiskerLeftIso Z e) (fun g ↦ by simp [← whisker_exchange])

section

variable (G : _root_.SheafOfModules.{w}
  (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪) ⥤
    _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- A functor out of sheaves of modules commutes with colimits as soon as its precomposite with
sheafification does: the right adjoint of sheafification is fully faithful. -/
theorem preservesColimitsOfSize_of_sheafify_comp
    (hG : PreservesColimitsOfSize.{w, w} (sheafifyFunctor 𝒪 h𝒪 ⋙ G)) :
    PreservesColimitsOfSize.{w, w} G := by
  let adj := Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction 𝒪 h𝒪
  have : IsIso adj.counit := inferInstance
  let := adj.fullyFaithfulROfIsIsoCounit.full
  let := adj.fullyFaithfulROfIsIsoCounit.faithful
  exact (adj.preservesColimitsOfSize_iff G).mpr hG

end

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **Tensoring on the left with a sheaf of modules commutes with colimits** (Stacks 05NB). -/
theorem preservesColimitsOfSize_tensorLeft
    (F : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)) :
    PreservesColimitsOfSize.{w, w} (tensorLeft F) := by
  let adj := Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction 𝒪 h𝒪
  have hL : PreservesColimitsOfSize.{w, w} (sheafifyFunctor 𝒪 h𝒪) :=
    adj.leftAdjoint_preservesColimits
  let P : _root_.PresheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪) := F.val
  have hP : PreservesColimitsOfSize.{w, w} (tensorLeft P) := inferInstance
  have h : PreservesColimitsOfSize.{w, w} (tensorLeft ((sheafifyFunctor 𝒪 h𝒪).obj P)) :=
    preservesColimitsOfSize_of_sheafify_comp 𝒪 h𝒪 _
      (preservesColimits_of_natIso (sheafifyCompTensorLeftIso 𝒪 h𝒪 P).symm)
  exact preservesColimits_of_natIso (tensorLeftMapIso (sheafifyValIso 𝒪 h𝒪 F))

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **Tensoring on the right with a sheaf of modules commutes with colimits** (Stacks 05NB). -/
theorem preservesColimitsOfSize_tensorRight
    (F : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)) :
    PreservesColimitsOfSize.{w, w} (tensorRight F) := by
  let adj := Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction 𝒪 h𝒪
  have hL : PreservesColimitsOfSize.{w, w} (sheafifyFunctor 𝒪 h𝒪) :=
    adj.leftAdjoint_preservesColimits
  let P : _root_.PresheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪) := F.val
  have hP : PreservesColimitsOfSize.{w, w} (tensorRight P) := inferInstance
  have h : PreservesColimitsOfSize.{w, w} (tensorRight ((sheafifyFunctor 𝒪 h𝒪).obj P)) :=
    preservesColimitsOfSize_of_sheafify_comp 𝒪 h𝒪 _
      (preservesColimits_of_natIso (sheafifyCompTensorRightIso 𝒪 h𝒪 P).symm)
  exact preservesColimits_of_natIso (tensorRightMapIso (sheafifyValIso 𝒪 h𝒪 F))

end Stacks.SheafOfModules

end
