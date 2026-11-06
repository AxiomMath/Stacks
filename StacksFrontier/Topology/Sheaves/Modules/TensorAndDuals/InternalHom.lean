module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFiniteFreeSummand.LeftDual
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.TensorHomAdjunction
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.InternalHomTensorCurrying

/-!
# Internal Hom out of a tensor product of sheaves of modules on a ringed space

Let `(X, 𝒪_X)` be a ringed space and let `F`, `G`, `H` be sheaves of `𝒪_X`-modules. The
sheaf-hom out of the tensor product `F ⊗ G` is canonically isomorphic to the iterated
sheaf-hom `ℋom(F, ℋom(G, H))`, naturally and contravariantly in the two tensor factors and
covariantly in the target. On global morphisms the isomorphism is the usual currying
bijection.

The tensor product of sheaves of modules is the sheafification of the objectwise tensor
product, and the sheaf-hom is already a sheaf, so the comparison is the composite of two
steps: precomposition with the sheafification unit, which is bijective on sections because
that unit is locally bijective and the target of the internal Hom is a sheaf, and the
currying isomorphism for *presheaves* of modules.

## Main definitions

* `Stacks.SheafOfModules.sheafHomSpace`: the sheaf-hom of two sheaves of modules on a ringed
  space.
* `Stacks.SheafOfModules.evalNestedInternalHomSection`,
  `Stacks.SheafOfModules.evalTensorHomSection`: evaluation of a local section of an iterated
  sheaf-hom, respectively of a sheaf-hom out of a tensor product, on two local sections.
* `Stacks.SheafOfModules.IsTensorCurry`: the relation "`c` is the curry of `t`", read on
  local pure tensors.
* `Stacks.SheafOfModules.sheafHomMapLeft`, `Stacks.SheafOfModules.sheafHomMapRight`:
  precomposition in the source and postcomposition in the target of the sheaf-hom.
* `Stacks.SheafOfModules.internalHomTensorIso`: the canonical isomorphism.
* `Stacks.SheafOfModules.tensorHomEquiv`: the induced bijection on morphisms.

## Main results

* `Stacks.SheafOfModules.internalHomTensorIso_hom_app_tmul`: the canonical isomorphism is
  currying, evaluated on local pure tensors.
* `Stacks.SheafOfModules.tensorHomEquiv_isTensorCurry`: the bijection on morphisms is the
  canonical currying map.
* `Stacks.SheafOfModules.internalHomTensorIso_natural_left`,
  `Stacks.SheafOfModules.internalHomTensorIso_natural_middle`,
  `Stacks.SheafOfModules.internalHomTensorIso_natural_right`: naturality in all three entries.

## Implementation notes

The evaluation formulae are stated rather than merely asserting that source and target are
abstractly isomorphic: they are what identifies this isomorphism with the currying map of the
source.

## References

* [Stacks Project, Tag 01CN](https://stacks.math.columbia.edu/tag/01CN)
-/

@[expose] public section

open CategoryTheory TensorProduct Opposite TopologicalSpace
open Stacks.SheafOfModules.TensorStalkRingedSpace Stacks.PresheafOfModules.InternalHom

universe u

namespace Stacks.SheafOfModules

variable (X : AlgebraicGeometry.RingedSpace.{u, u})
variable {F G H : _root_.SheafOfModules.{u} (structureSheafRing X)}

/-- The sheaf-hom `ℋom_{𝒪_X}(F, G)` of two sheaves of modules on a ringed space: the
sheaf-hom over the structure sheaf of the space. -/
noncomputable abbrev sheafHomSpace (X : AlgebraicGeometry.RingedSpace.{u, u})
    (F G : _root_.SheafOfModules.{u} (structureSheafRing X)) :
    _root_.SheafOfModules.{u} (structureSheafRing X) :=
  _root_.Stacks.SheafOfModules.sheafHom X.presheaf (structureSheafRing X).property F G

/-- Evaluation of a local section of an iterated sheaf-hom on two local sections. -/
noncomputable def evalNestedInternalHomSection
    (U : Opens X.carrier)
    (q : (sheafHomSpace X F (sheafHomSpace X G H)).val.obj (op U))
    (f : F.val.obj (op U)) (g : G.val.obj (op U)) : H.val.obj (op U) :=
  ((((q.app (op (Over.mk (𝟙 U)))).hom f).app (op (Over.mk (𝟙 U)))).hom g)

/-- Evaluation of a local morphism out of a tensor product on a local pure tensor. -/
noncomputable def evalTensorHomSection
    (U : Opens X.carrier)
    (s : (sheafHomSpace X
      (((Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj F).obj G) H).val.obj (op U))
    (f : F.val.obj (op U)) (g : G.val.obj (op U)) : H.val.obj (op U) :=
  (s.app (op (Over.mk (𝟙 U)))).hom
    (toTensorSheafSection X F G (op U) (f ⊗ₜ[X.presheaf.obj (op U)] g))

/-- A morphism `F ⟶ ℋom(G, H)` is the curry of a morphism `F ⊗ G ⟶ H` when their
evaluations agree on every local pure tensor. -/
def IsTensorCurry (t : ((Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj F).obj G ⟶ H)
    (c : F ⟶ sheafHomSpace X G H) : Prop :=
  ∀ (U : Opens X.carrier) (f : F.val.obj (op U)) (g : G.val.obj (op U)),
    (((c.val.app (op U) f).app (op (Over.mk (𝟙 U)))).hom g) =
      t.val.app (op U)
        (toTensorSheafSection X F G (op U) (f ⊗ₜ[X.presheaf.obj (op U)] g))

/-- Precomposition in the first variable of the sheaf-hom. -/
noncomputable def sheafHomMapLeft
    {A A' B : _root_.SheafOfModules.{u} (structureSheafRing X)} (f : A' ⟶ A) :
    sheafHomSpace X A B ⟶ sheafHomSpace X A' B :=
  ⟨internalHomMapLeft X.presheaf f.val⟩

/-- Postcomposition in the second variable of the sheaf-hom. -/
noncomputable def sheafHomMapRight
    {A B B' : _root_.SheafOfModules.{u} (structureSheafRing X)} (f : B ⟶ B') :
    sheafHomSpace X A B ⟶ sheafHomSpace X A B' :=
  ⟨internalHomMapRight X.presheaf A.val f.val⟩

/-- Precomposition with the sheafification unit of the objectwise tensor product, read on
internal Hom presheaves. -/
noncomputable def sheafificationInternalHomComparison
    (F G H : _root_.SheafOfModules.{u} (structureSheafRing X)) :
    internalHom X.presheaf (((Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj F).obj G).val H.val ⟶
      internalHom X.presheaf (MonoidalCategory.tensorObj F.val G.val) H.val :=
  internalHomMapLeft X.presheaf
    (sheafifyUnit X (PresheafOfModules.tensorObj (O := X.presheaf) F.val G.val))

/-- The restriction to the opens contained in `U` of the sheafification unit of the objectwise
tensor product `F ⊗ G` is locally surjective. -/
lemma restrictedSheafifyUnit_locallySurjective
    (F G : _root_.SheafOfModules.{u} (structureSheafRing X)) (U : Opens X.carrier) :
    PresheafOfModules.IsLocallySurjective
      ((Opens.grothendieckTopology X.carrier).over U)
      ((restrFun X.presheaf U).map
        (sheafifyUnit X (PresheafOfModules.tensorObj (O := X.presheaf) F.val G.val))) := by
  show Presheaf.IsLocallySurjective _ ((Over.forget U).op.whiskerLeft
    ((PresheafOfModules.toPresheaf _).map
      (sheafifyUnit X (PresheafOfModules.tensorObj (O := X.presheaf) F.val G.val))))
  have : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier)
      ((PresheafOfModules.toPresheaf _).map
        (sheafifyUnit X (PresheafOfModules.tensorObj (O := X.presheaf) F.val G.val))) := by
    show Presheaf.IsLocallySurjective _
      (CategoryTheory.toSheafify _
        (PresheafOfModules.tensorObj (O := X.presheaf) F.val G.val).presheaf)
    infer_instance
  exact Presheaf.isLocallySurjective_whisker
    ((Opens.grothendieckTopology X.carrier).over U)
    (Opens.grothendieckTopology X.carrier) (Over.forget U) _

/-- The restriction to the opens contained in `U` of the sheafification unit of the objectwise
tensor product `F ⊗ G` is locally injective. -/
lemma restrictedSheafifyUnit_locallyInjective
    (F G : _root_.SheafOfModules.{u} (structureSheafRing X)) (U : Opens X.carrier) :
    PresheafOfModules.IsLocallyInjective
      ((Opens.grothendieckTopology X.carrier).over U)
      ((restrFun X.presheaf U).map
        (sheafifyUnit X (PresheafOfModules.tensorObj (O := X.presheaf) F.val G.val))) := by
  show Presheaf.IsLocallyInjective _ ((Over.forget U).op.whiskerLeft
    ((PresheafOfModules.toPresheaf _).map
      (sheafifyUnit X (PresheafOfModules.tensorObj (O := X.presheaf) F.val G.val))))
  have : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X.carrier)
      ((PresheafOfModules.toPresheaf _).map
        (sheafifyUnit X (PresheafOfModules.tensorObj (O := X.presheaf) F.val G.val))) := by
    show Presheaf.IsLocallyInjective _
      (CategoryTheory.toSheafify _
        (PresheafOfModules.tensorObj (O := X.presheaf) F.val G.val).presheaf)
    infer_instance
  exact Presheaf.isLocallyInjective_whisker
    ((Opens.grothendieckTopology X.carrier).over U)
    (Opens.grothendieckTopology X.carrier) (Over.forget U) _

/-- The restriction of a sheaf of modules `H` to the opens contained in `U` is a sheaf for the
induced topology. -/
lemma restricted_isSheaf (H : _root_.SheafOfModules.{u} (structureSheafRing X))
    (U : Opens X.carrier) :
    Presheaf.IsSheaf ((Opens.grothendieckTopology X.carrier).over U)
      ((restrFun X.presheaf U).obj H.val).presheaf :=
  (Over.forget U).op_comp_isSheaf_of_isSheaf
    ((Opens.grothendieckTopology X.carrier).over U)
    (Opens.grothendieckTopology X.carrier) H.val.presheaf H.isSheaf

/-- On every open `U`, precomposition with the sheafification unit of `F ⊗ G` is a bijection on
sections of the internal Hom presheaves into `H`. -/
lemma sheafificationInternalHomComparison_app_bijective
    (F G H : _root_.SheafOfModules.{u} (structureSheafRing X)) (U : Opens X.carrier) :
    Function.Bijective
      ((sheafificationInternalHomComparison X F G H).app (op U)) := by
  have := restrictedSheafifyUnit_locallySurjective X F G U
  have := restrictedSheafifyUnit_locallyInjective X F G U
  exact (PresheafOfModules.homEquivOfIsLocallyBijective
    (f := (restrFun X.presheaf U).map
      (sheafifyUnit X (PresheafOfModules.tensorObj (O := X.presheaf) F.val G.val)))
    (restricted_isSheaf X H U)).bijective

/-- Precomposition with the sheafification unit of `F ⊗ G` is an isomorphism of internal Hom
presheaves into `H`. -/
lemma sheafificationInternalHomComparison_isIso
    (F G H : _root_.SheafOfModules.{u} (structureSheafRing X)) :
    IsIso (sheafificationInternalHomComparison X F G H) := by
  have (U : (Opens X.carrier)ᵒᵖ) :
      IsIso ((sheafificationInternalHomComparison X F G H).app U) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact sheafificationInternalHomComparison_app_bijective X F G H U.unop
  refine ⟨⟨{ app := fun U ↦ inv ((sheafificationInternalHomComparison X F G H).app U)
             naturality := fun {U V} i ↦ ?_ }, ?_, ?_⟩⟩
  · rw [Functor.map_inv, IsIso.comp_inv_eq, Category.assoc,
      (sheafificationInternalHomComparison X F G H).naturality, IsIso.inv_hom_id_assoc]
  · ext U
    simp
  · ext U
    simp

/-- The sheaf-hom out of a tensor product is canonically the corresponding iterated sheaf-hom:
`ℋom(F ⊗ G, H) ≅ ℋom(F, ℋom(G, H))`. -/
@[stacks 01CN "canonical isomorphism"]
noncomputable def internalHomTensorIso
    (F G H : _root_.SheafOfModules.{u} (structureSheafRing X)) :
    sheafHomSpace X (((Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj F).obj G) H ≅
      sheafHomSpace X F (sheafHomSpace X G H) :=
  let c := internalHomMapLeft X.presheaf (G := H.val)
    (sheafifyUnit X (PresheafOfModules.tensorObj (O := X.presheaf) F.val G.val))
  have : IsIso c := sheafificationInternalHomComparison_isIso X F G H
  let e := asIso c ≪≫ presheafInternalHomTensorIso X.presheaf F.val G.val H.val
  { hom := ⟨e.hom⟩
    inv := ⟨e.inv⟩
    hom_inv_id := _root_.SheafOfModules.hom_ext e.hom_inv_id
    inv_hom_id := _root_.SheafOfModules.hom_ext e.inv_hom_id }

/-- The canonical sheaf-hom isomorphism is currying: on every open, its evaluation on two
local sections agrees with evaluation on their pure tensor. -/
@[stacks 01CN "canonical characterization"]
theorem internalHomTensorIso_hom_app_tmul
    (U : Opens X.carrier)
    (s : (sheafHomSpace X
      (((Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj F).obj G) H).val.obj (op U))
    (f : F.val.obj (op U)) (g : G.val.obj (op U)) :
    evalNestedInternalHomSection X U
        ((internalHomTensorIso X F G H).hom.val.app (op U) s) f g =
      evalTensorHomSection X U s f g := by
  have h := presheafInternalHomTensorIso_hom_app X.presheaf F.val G.val H.val U
    ((sheafificationInternalHomComparison X F G H).app (op U) s)
    (𝟙 U) f (𝟙 U) g
  change evalNestedInternalHomSection X U
      ((internalHomTensorIso X F G H).hom.val.app (op U) s) f g =
    (s.app (op (Over.mk (𝟙 U)))).hom
      (toTensorSheafSection X F G (op U)
        ((F.val.map (𝟙 (op U))) f ⊗ₜ[X.presheaf.obj (op U)] g)) at h
  simpa only [evalTensorHomSection, PresheafOfModules.map_id,
    ModuleCat.restrictScalarsId'_inv_app,
    ModuleCat.restrictScalarsId'App_inv_apply] using h

/-- Giving a morphism `F ⊗ G ⟶ H` is canonically equivalent to giving a morphism
`F ⟶ ℋom(G, H)`. -/
@[stacks 01CN "morphism equivalence"]
noncomputable def tensorHomEquiv
    (F G H : _root_.SheafOfModules.{u} (structureSheafRing X)) :
    (((Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj F).obj G ⟶ H) ≃ (F ⟶ sheafHomSpace X G H) :=
  (PresheafOfModules.sheafificationHomEquiv
      (R := structureSheafRing X) (𝟙 (structureSheafRing X).obj)).trans
    ((presheafTensorHomEquiv X.presheaf F.val G.val H.val).trans
      { toFun := fun f ↦ ⟨f⟩
        invFun := fun f ↦ f.val
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl })

/-- The forward direction of `tensorHomEquiv` is the canonical currying map. -/
@[stacks 01CN "morphism equivalence characterization"]
theorem tensorHomEquiv_isTensorCurry
    (t : ((Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj F).obj G ⟶ H) :
    IsTensorCurry X t (tensorHomEquiv X F G H t) := by
  intro U f g
  have h := presheafTensorHomEquiv_apply X.presheaf F.val G.val H.val
    (PresheafOfModules.sheafificationHomEquiv
      (R := structureSheafRing X) (𝟙 (structureSheafRing X).obj) t)
    U f (𝟙 U) g
  change (((tensorHomEquiv X F G H t).val.app (op U) f).app
      (op (Over.mk (𝟙 U)))).hom g =
    (PresheafOfModules.sheafificationHomEquiv
      (R := structureSheafRing X) (𝟙 (structureSheafRing X).obj) t).app (op U)
      ((F.val.map (𝟙 (op U))) f ⊗ₜ[X.presheaf.obj (op U)] g) at h
  rw [PresheafOfModules.map_id] at h
  have hb := (PresheafOfModules.sheafificationAdjunction
    (R := structureSheafRing X) (𝟙 (structureSheafRing X).obj)).homEquiv_unit
      (PresheafOfModules.tensorObj (O := X.presheaf) F.val G.val) H t
  change PresheafOfModules.sheafificationHomEquiv
      (R := structureSheafRing X) (𝟙 (structureSheafRing X).obj) t =
    sheafifyUnit X (PresheafOfModules.tensorObj (O := X.presheaf) F.val G.val) ≫ t.val at hb
  rwa [hb] at h

/-- `sheafificationInternalHomComparison` is natural in the two tensor factors: it commutes with
precomposition by `f ⊗ g` and by its sheafification. -/
lemma sheafificationInternalHomComparison_natural
    {F' G' : _root_.SheafOfModules.{u} (structureSheafRing X)}
    (f : F' ⟶ F) (g : G' ⟶ G) :
    sheafificationInternalHomComparison X F G H ≫
        internalHomMapLeft X.presheaf (MonoidalCategory.tensorHom f.val g.val) =
      internalHomMapLeft X.presheaf
        ((Functor.uncurry.obj (Tensor.sheafTensor.{u, u, u, u, u}
          ⟨X.presheaf, X.IsSheaf⟩)).map (X := (F', G')) (Y := (F, G)) (f, g)).val ≫
        sheafificationInternalHomComparison X F' G' H := by
  have unitNaturality := (PresheafOfModules.sheafificationAdjunction
    (R := structureSheafRing X) (𝟙 (structureSheafRing X).obj)).unit.naturality
      (PresheafOfModules.tensorHom (O := X.presheaf) f.val g.val)
  have tensorMap := Tensor.sheafTensor_uncurry_map.{u, u, u, u, u}
    ⟨X.presheaf, X.IsSheaf⟩
    (left := F') (left' := F) (right := G') (right' := G) f g
  have nativeNaturality :
      PresheafOfModules.tensorHom (O := X.presheaf) f.val g.val ≫
          sheafifyUnit X (PresheafOfModules.tensorObj (O := X.presheaf) F.val G.val) =
        sheafifyUnit X (PresheafOfModules.tensorObj (O := X.presheaf) F'.val G'.val) ≫
          ((Functor.uncurry.obj (Tensor.sheafTensor.{u, u, u, u, u}
            ⟨X.presheaf, X.IsSheaf⟩)).map (X := (F', G')) (Y := (F, G)) (f, g)).val :=
    unitNaturality.trans
      (congrArg (fun morphism =>
        sheafifyUnit X (PresheafOfModules.tensorObj (O := X.presheaf) F'.val G'.val) ≫
          morphism.val) tensorMap.symm)
  exact (internalHomMapLeft_comp X.presheaf (G := H.val)
    (PresheafOfModules.tensorHom (O := X.presheaf) f.val g.val)
    (sheafifyUnit X (PresheafOfModules.tensorObj (O := X.presheaf) F.val G.val))).trans
      ((congrArg (internalHomMapLeft X.presheaf (G := H.val))
        nativeNaturality).trans
        (internalHomMapLeft_comp X.presheaf (G := H.val)
          (sheafifyUnit X (PresheafOfModules.tensorObj (O := X.presheaf) F'.val G'.val))
          ((Functor.uncurry.obj (Tensor.sheafTensor.{u, u, u, u, u}
            ⟨X.presheaf, X.IsSheaf⟩)).map (X := (F', G')) (Y := (F, G)) (f, g)).val).symm)

/-- `sheafificationInternalHomComparison` commutes with postcomposition by a morphism
`h : H ⟶ H'` in the target. -/
lemma sheafificationInternalHomComparison_natural_right
    {H' : _root_.SheafOfModules.{u} (structureSheafRing X)} (h : H ⟶ H') :
    internalHomMapRight X.presheaf (((Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj F).obj G).val
        h.val ≫ sheafificationInternalHomComparison X F G H' =
      sheafificationInternalHomComparison X F G H ≫
        internalHomMapRight X.presheaf (MonoidalCategory.tensorObj F.val G.val) h.val := by
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  rfl

/-- Naturality of the canonical isomorphism in the tensor factors follows from naturality of its
presheaf counterpart, composed with `sheafificationInternalHomComparison_natural`. -/
private lemma comparison_comp_currying_natural
    {F' G' : _root_.SheafOfModules.{u} (structureSheafRing X)} (f : F' ⟶ F) (g : G' ⟶ G)
    {Y : PresheafOfModules (Oforget X.presheaf)}
    {k : internalHom X.presheaf F.val (internalHom X.presheaf G.val H.val) ⟶ Y}
    {k' : internalHom X.presheaf (MonoidalCategory.tensorObj F'.val G'.val) H.val ⟶ Y}
    (hk : (presheafInternalHomTensorIso X.presheaf F.val G.val H.val).hom ≫ k =
      internalHomMapLeft X.presheaf (MonoidalCategory.tensorHom f.val g.val) ≫ k') :
    (sheafificationInternalHomComparison X F G H ≫
        (presheafInternalHomTensorIso X.presheaf F.val G.val H.val).hom) ≫ k =
      internalHomMapLeft X.presheaf
        ((Functor.uncurry.obj (Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩)).map
          ((f, g) : (F', G') ⟶ (F, G))).val ≫
        (sheafificationInternalHomComparison X F' G' H ≫ k') := by
  rw [Category.assoc, hk, ← Category.assoc, sheafificationInternalHomComparison_natural,
    Category.assoc]
  rfl

/-- The canonical isomorphism commutes with precomposition in its first argument. -/
@[stacks 01CN "functoriality in the first entry"]
theorem internalHomTensorIso_natural_left
    {F' : _root_.SheafOfModules.{u} (structureSheafRing X)} (f : F' ⟶ F) :
    (internalHomTensorIso X F G H).hom ≫ sheafHomMapLeft X f =
      sheafHomMapLeft X ((Functor.uncurry.obj (Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩)).map
        ((f, 𝟙 G) : (_, _) ⟶ (_, _))) ≫
        (internalHomTensorIso X F' G H).hom :=
  _root_.SheafOfModules.hom_ext <| comparison_comp_currying_natural X f (𝟙 G)
    (k' := (presheafInternalHomTensorIso X.presheaf F'.val G.val H.val).hom)
    (presheafInternalHomTensorIso_natural_left ..)

/-- The canonical isomorphism commutes with precomposition in its second argument. -/
@[stacks 01CN "functoriality in the second entry"]
theorem internalHomTensorIso_natural_middle
    {G' : _root_.SheafOfModules.{u} (structureSheafRing X)} (g : G' ⟶ G) :
    (internalHomTensorIso X F G H).hom ≫ sheafHomMapRight X (sheafHomMapLeft X g) =
      sheafHomMapLeft X ((Functor.uncurry.obj (Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩)).map
        ((𝟙 F, g) : (_, _) ⟶ (_, _))) ≫
        (internalHomTensorIso X F G' H).hom :=
  _root_.SheafOfModules.hom_ext <| comparison_comp_currying_natural X (𝟙 F) g
    (k' := (presheafInternalHomTensorIso X.presheaf F.val G'.val H.val).hom)
    (presheafInternalHomTensorIso_natural_middle ..)

/-- The canonical isomorphism commutes with postcomposition in its target. -/
@[stacks 01CN "functoriality in the third entry"]
theorem internalHomTensorIso_natural_right
    {H' : _root_.SheafOfModules.{u} (structureSheafRing X)} (h : H ⟶ H') :
    sheafHomMapRight X h ≫ (internalHomTensorIso X F G H').hom =
      (internalHomTensorIso X F G H).hom ≫ sheafHomMapRight X (sheafHomMapRight X h) := by
  apply _root_.SheafOfModules.hom_ext
  show internalHomMapRight X.presheaf
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj F).obj G).val h.val ≫
      (sheafificationInternalHomComparison X F G H' ≫
      (presheafInternalHomTensorIso X.presheaf F.val G.val H'.val).hom) =
    (sheafificationInternalHomComparison X F G H ≫
      (presheafInternalHomTensorIso X.presheaf F.val G.val H.val).hom) ≫
      internalHomMapRight X.presheaf F.val
        (internalHomMapRight X.presheaf G.val h.val)
  rw [← Category.assoc, sheafificationInternalHomComparison_natural_right X h,
    Category.assoc, presheafInternalHomTensorIso_natural_right, Category.assoc]

add_to_stacks 01CN "canonical_iso" Stacks.SheafOfModules.internalHomTensorIso
add_to_stacks 01CN "in_particular" Stacks.SheafOfModules.tensorHomEquiv

end Stacks.SheafOfModules
