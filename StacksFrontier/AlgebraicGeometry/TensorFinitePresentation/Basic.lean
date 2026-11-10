module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExactnessSheafify
public import StacksFrontier.AlgebraicGeometry.TensorCoherence.Basic
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorProduct.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Tensor products of finitely presented sheaves of modules

The tensor product of two sheaves of modules of finite presentation on a ringed space is of
finite presentation. If `F` has a finite presentation over each `U` of an open cover and `G` over
each `V` of another, then over `U ⊓ V` the tensor product of the restricted presentations is a
finite presentation of `(F ⊗ G)|_{U ⊓ V}`, and the opens `U ⊓ V` cover.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.tensorPresentationOver`: a presentation of
  `(F ⊗_{𝒪_X} G)|_U` obtained from presentations of `F|_U` and of `G|_U`.
* `AlgebraicGeometry.SheafOfModules.tensorPresentationOverInf`: the same over `U ⊓ V`, from a
  presentation of `F|_U` and one of `G|_V`.

## Main results

* `Stacks.SheafOfModules.TensorProduct.tensorPresentation_isFinite`: the tensor product of two
  finite presentations is finite.
* `AlgebraicGeometry.SheafOfModules.tensorPresentationOver_isFinite` and
  `AlgebraicGeometry.SheafOfModules.tensorPresentationOverInf_isFinite`: the same for the two
  restricted versions.
* `AlgebraicGeometry.SheafOfModules.tensorSheaf_isFinitePresentation`: the tensor product of two
  sheaves of modules of finite presentation on a ringed space is of finite presentation.

## References

* [Stacks Project, Tag 01CE](https://stacks.math.columbia.edu/tag/01CE)
-/

@[expose] public section

open CategoryTheory MonoidalCategory Limits TopologicalSpace

universe v u w

namespace Stacks.SheafOfModules.TensorProduct

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [UnivLE.{max v u, w}]
  [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]
  [HasSheafify J AddCommGrpCat.{w}]
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w})
  (h𝒪 : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪))

omit [UnivLE.{max v u, w}] [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The tensor product of two finite presentations is finite. -/
theorem tensorPresentation_isFinite
    {F G : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)}
    (P : F.Presentation) (Q : G.Presentation)
    [hP : P.IsFinite] [hQ : Q.IsFinite] :
    (tensorPresentation 𝒪 h𝒪 P Q).IsFinite := by
  let _ : Finite P.generators.I := hP.isFiniteType_generators.finite
  let _ : Finite P.relations.I := hP.isFiniteType_relations.finite
  let _ : Finite Q.generators.I := hQ.isFiniteType_generators.finite
  let _ : Finite Q.relations.I := hQ.isFiniteType_relations.finite
  refine ⟨⟨?_⟩, ⟨?_⟩⟩
  · change Finite (P.generators.I × Q.generators.I)
    infer_instance
  · change Finite ((P.relations.I × Q.generators.I) ⊕ (P.generators.I × Q.relations.I))
    infer_instance

end Stacks.SheafOfModules.TensorProduct

namespace AlgebraicGeometry.SheafOfModules

open AlgebraicGeometry TopologicalSpace Stacks.SheafOfModules.TensorStalkRingedSpace
open Stacks.SheafOfModules.TensorProduct

variable (X : AlgebraicGeometry.RingedSpace.{u, u})
  (F G : _root_.SheafOfModules.{u} (structureSheafRing
    X))
  (U : Opens X.carrier)

/-- The inverse of `AlgebraicGeometry.tensorRestrictionIso` is an isomorphism. -/
instance isIso_tensorRestrictionIso_inv :
    IsIso (AlgebraicGeometry.tensorRestrictionIso X F G U).inv :=
  (AlgebraicGeometry.tensorRestrictionIso X F G U).isIso_inv

/-- A presentation of `(F ⊗_{𝒪_X} G)|_U` built from presentations of `F|_U` and of `G|_U`, by
transporting their tensor presentation along `AlgebraicGeometry.tensorRestrictionIso`. -/
noncomputable def tensorPresentationOver
    (P : (F.over U).Presentation) (Q : (G.over U).Presentation) :
    (((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (F)).obj
      (G))).over U).Presentation :=
  (tensorPresentation (Stacks.SheafOfModules.TensorOver.OU (X := X) U)
    (Stacks.SheafOfModules.TensorOver.hOU U) P Q).ofIsIso
      (AlgebraicGeometry.tensorRestrictionIso X F G U).inv

/-- The presentation `tensorPresentationOver X F G U P Q` is finite when `P` and `Q` are. -/
theorem tensorPresentationOver_isFinite
    (P : (F.over U).Presentation) (Q : (G.over U).Presentation)
    [hP : P.IsFinite] [hQ : Q.IsFinite] :
    (tensorPresentationOver X F G U P Q).IsFinite :=
  @_root_.SheafOfModules.instIsFiniteOfIsIso _ _ _ _ _ _ _ _
    (AlgebraicGeometry.tensorRestrictionIso X F G U).inv
    ((AlgebraicGeometry.tensorRestrictionIso X F G U).isIso_inv)
    (tensorPresentation (Stacks.SheafOfModules.TensorOver.OU (X := X) U)
      (Stacks.SheafOfModules.TensorOver.hOU U) P Q)
    (tensorPresentation_isFinite (Stacks.SheafOfModules.TensorOver.OU (X := X) U)
      (Stacks.SheafOfModules.TensorOver.hOU U) P Q (hP := hP) (hQ := hQ))

/-- A presentation of `(F ⊗_{𝒪_X} G)|_{U ⊓ V}` built from a presentation of `F|_U` and one of
`G|_V`: restrict each to the intersection, then tensor. -/
noncomputable def tensorPresentationOverInf (V : Opens X.carrier)
    (P : (F.over U).Presentation) (Q : (G.over V).Presentation) :
    (((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (F)).obj
      (G))).over (U ⊓ V)).Presentation :=
  tensorPresentationOver X F G (U ⊓ V)
    (Stacks.SheafOfModules.LocalKernel.presentationOver (M := F) (homOfLE inf_le_left) P)
    (Stacks.SheafOfModules.LocalKernel.presentationOver (M := G) (homOfLE inf_le_right) Q)

/-- The presentation `tensorPresentationOverInf X F G U V P Q` is finite when `P` and `Q` are. -/
theorem tensorPresentationOverInf_isFinite (V : Opens X.carrier)
    (P : (F.over U).Presentation) (Q : (G.over V).Presentation)
    [P.IsFinite] [Q.IsFinite] :
    (tensorPresentationOverInf X F G U V P Q).IsFinite :=
  tensorPresentationOver_isFinite X F G (U ⊓ V) _ _

/-- The tensor product of two finitely presented modules on a ringed space is of finite
presentation. -/
@[stacks 01CE "tensor_finite_presentation", instance]
theorem tensorSheaf_isFinitePresentation (X : AlgebraicGeometry.RingedSpace.{u, u})
    (F G : _root_.SheafOfModules.{u}
      (structureSheafRing X))
    [_root_.SheafOfModules.IsFinitePresentation.{u, u, u} F]
    [_root_.SheafOfModules.IsFinitePresentation.{u, u, u} G] :
    _root_.SheafOfModules.IsFinitePresentation.{u, u, u}
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (F)).obj
        (G))) := by
  obtain ⟨qF, hqF⟩ :
      ∃ q : _root_.SheafOfModules.QuasicoherentData.{u, u, u, u} F,
        q.IsFinitePresentation :=
    _root_.SheafOfModules.IsFinitePresentation.exists_quasicoherentData F
  obtain ⟨qG, hqG⟩ :
      ∃ q : _root_.SheafOfModules.QuasicoherentData.{u, u, u, u} G,
        q.IsFinitePresentation :=
    _root_.SheafOfModules.IsFinitePresentation.exists_quasicoherentData G
  let J := Opens.grothendieckTopology X.carrier
  have hF : TopologicalSpace.IsOpenCover qF.X :=
    (Opens.coversTop_iff X.carrier qF.X).mp qF.coversTop
  have hG : TopologicalSpace.IsOpenCover qG.X :=
    (Opens.coversTop_iff X.carrier qG.X).mp qG.coversTop
  have hPair : J.CoversTop (fun ij : qF.I × qG.I => qF.X ij.1 ⊓ qG.X ij.2) := by
    rw [Opens.coversTop_iff X.carrier]
    apply top_unique
    rintro x -
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp
      (by simp [hF.iSup_set_eq_univ] : x ∈ ⋃ i, (qF.X i : Set X.carrier))
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp
      (by simp [hG.iSup_set_eq_univ] : x ∈ ⋃ j, (qG.X j : Set X.carrier))
    exact Opens.mem_iSup.2 ⟨(i, j), hi, hj⟩
  let qT : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj
      (F)).obj (G))).QuasicoherentData :=
    { I := qF.I × qG.I
      X ij := qF.X ij.1 ⊓ qG.X ij.2
      coversTop := hPair
      presentation := fun ij =>
        tensorPresentationOverInf X F G (qF.X ij.1) (qG.X ij.2)
          (qF.presentation ij.1) (qG.presentation ij.2) }
  have hqT : qT.IsFinitePresentation := by
    constructor
    intro ij
    have := hqF.isFinite_presentation ij.1
    have := hqG.isFinite_presentation ij.2
    exact tensorPresentationOverInf_isFinite X F G (qF.X ij.1) (qG.X ij.2)
      (qF.presentation ij.1) (qG.presentation ij.2)
  exact ⟨qT, hqT⟩

end AlgebraicGeometry.SheafOfModules

end
