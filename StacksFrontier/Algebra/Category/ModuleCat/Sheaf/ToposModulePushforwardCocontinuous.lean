module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RanUnderlying
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModules
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The direct image of sheaves of modules along a cocontinuous functor is the transported one

Let `w : X ⥤ Y` be a cocontinuous functor of sites, so that the direct image of sheaves of sets
of the morphism of topoi it induces (Stacks 00XO) is right Kan extension along `w.op`,
`CategoryTheory.Functor.sheafPushforwardCocontinuous`. Restricting scalars along `δ : R ⟶ O_X`,
transporting sheaves of modules along that functor
(`Stacks.Sheaves.ToposPullback.pullbackModuleFunctor`, Stacks 03D1 and 03D2) and restricting
scalars along `ν : O_Y ⟶ f^{-1}R` is isomorphic to `Stacks.SheafOfModules.pushforwardCocontinuous`,
the direct image of sheaves of modules carrying its module structure on the right Kan extension
at `AddCommGrpCat`, whenever the two scalar maps agree on every leg of the limit cone computing
the Kan extension.

## Main definitions

* `Stacks.SheafOfModules.sectionsLeg`: the leg at `(U, ψ : V ⟶ w(U))` of the limit cone computing
  the right Kan extension, as a natural transformation from the sections over `V` of the direct
  image of a sheaf of sets to its sections over `U`.
* `Stacks.SheafOfModules.pushforwardCocontinuousModuleAddHom`: the comparison of the two
  underlying presheaves of abelian groups.
* `Stacks.SheafOfModules.pushforwardCocontinuousModuleHom` and
  `Stacks.SheafOfModules.pushforwardCocontinuousModuleObjIso`: the comparison at one sheaf of
  modules.

## Main results

* `Stacks.SheafOfModules.preservesFiniteProducts_sheafPushforwardCocontinuous`: the direct image
  of sheaves of sets along a cocontinuous functor preserves finite products.
* `Stacks.SheafOfModules.pushforwardCocontinuousModulesIso`: the comparison, as an isomorphism
  of functors.

## References

* [Stacks Project, Tag 00XO](https://stacks.math.columbia.edu/tag/00XO)
* [Stacks Project, Tag 03D1](https://stacks.math.columbia.edu/tag/03D1)
* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 0FN3](https://stacks.math.columbia.edu/tag/0FN3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Functor Opposite CategoryTheory.Sheaf
open Stacks.Sheaves.ToposPullback
open Stacks.Sheaves.RingedToposModules

universe ww vv uu vv' uu'

namespace Stacks.SheafOfModules

section Elementwise

variable {X : Type uu} [Category.{vv} X] {Y : Type uu'} [Category.{vv'} Y] (w : X ⥤ Y)
  [∀ F : Xᵒᵖ ⥤ Type ww, w.op.HasPointwiseRightKanExtension F]
  [∀ F : Xᵒᵖ ⥤ AddCommGrpCat.{ww}, w.op.HasPointwiseRightKanExtension F]

/-- **The comparison carries legs to legs, elementwise**: the leg at `j` of the image of a
section `x` under the comparison of the right Kan extensions of `N` and of its underlying presheaf
of sets is the leg at `j` of `x`. -/
lemma ranπ_ranCompIso_hom_app (N : Xᵒᵖ ⥤ AddCommGrpCat.{ww}) (V : Yᵒᵖ)
    (j : StructuredArrow V w.op) (x : (w.op.ran.obj N).obj V) :
    ranπ w.op (N ⋙ forget AddCommGrpCat.{ww}) V j
        (((forget AddCommGrpCat.{ww}).rightKanExtensionCompIsoOfPreserves N w.op).hom.app V x) =
      (ranπ w.op N V j).hom x := by
  exact ConcreteCategory.congr_hom
    (ranCompIso_hom_app_comp_ranπ w.op (forget AddCommGrpCat.{ww}) N V j) x

omit [∀ F : Xᵒᵖ ⥤ AddCommGrpCat.{ww}, w.op.HasPointwiseRightKanExtension F] in
/-- **Naturality of the leg in the extended functor, elementwise**: the leg at `j` of the image
of a section `x` under `w.op.ran.map φ` is the image under `φ` of the leg at `j` of `x`. -/
lemma ranπ_map_functor_apply {N₁ N₂ : Xᵒᵖ ⥤ Type ww} (φ : N₁ ⟶ N₂) (V : Yᵒᵖ)
    (j : StructuredArrow V w.op) (x : (w.op.ran.obj N₁).obj V) :
    ranπ w.op N₂ V j ((w.op.ran.map φ).app V x) = φ.app j.right (ranπ w.op N₁ V j x) := by
  exact ConcreteCategory.congr_hom (ranπ_map_functor w.op φ V j) x

end Elementwise

section SMulElementwise

variable {X : Type uu} [Category.{vv} X] {Y : Type uu'} [Category.{vv'} Y] (w : X ⥤ Y)
  {S : Xᵒᵖ ⥤ RingCat.{ww}} {T : Yᵒᵖ ⥤ RingCat.{ww}}
  [∀ F : Xᵒᵖ ⥤ RingCat.{ww}, w.op.HasPointwiseRightKanExtension F]
  [∀ F : Xᵒᵖ ⥤ AddCommGrpCat.{ww}, w.op.HasPointwiseRightKanExtension F]
  (ψ : T ⟶ w.op.ran.obj S) (M : PresheafOfModules.{ww} S)

/-- **The defining property of `ranSMul`, elementwise.** On the leg at `(U, ψ)` scalar
multiplication on the direct image acts through the ring map `scalarπ`. -/
lemma ranSMul_π_apply (V : Yᵒᵖ) (r : T.obj V) (j : StructuredArrow V w.op)
    (m : (w.op.ran.obj M.presheaf).obj V) :
    (ranπ w.op M.presheaf V j).hom ((ranSMul w ψ M V r).hom m) =
      (smulPresheaf M j.right ((scalarπ w ψ V j).hom r)).hom
        ((ranπ w.op M.presheaf V j).hom m) := by
  exact ConcreteCategory.congr_hom (ranSMul_π w ψ M V r j) m

end SMulElementwise

section Cocontinuous

variable {X : Type uu} [Category.{vv} X] {Y : Type uu'} [Category.{vv'} Y] (w : X ⥤ Y)
  (JX : GrothendieckTopology X) (JY : GrothendieckTopology Y) [w.IsCocontinuous JX JY]
  [∀ F : Xᵒᵖ ⥤ Type ww, w.op.HasPointwiseRightKanExtension F]

/-- **The direct image of sheaves of sets along a cocontinuous functor preserves finite
products.** -/
@[sga "4 III 2.4" "partial"]
instance preservesFiniteProducts_sheafPushforwardCocontinuous :
    PreservesFiniteProducts (w.sheafPushforwardCocontinuous (Type ww) JX JY) := by
  let : PreservesLimitsOfSize.{0, 0} (w.op.ran : (Xᵒᵖ ⥤ Type ww) ⥤ (Yᵒᵖ ⥤ Type ww)) :=
    (w.op.ranAdjunction (Type ww)).rightAdjoint_preservesLimits
  have : PreservesFiniteProducts (w.op.ran : (Xᵒᵖ ⥤ Type ww) ⥤ (Yᵒᵖ ⥤ Type ww)) :=
    ⟨fun _ => inferInstance⟩
  have : PreservesFiniteProducts
      (w.sheafPushforwardCocontinuous (Type ww) JX JY ⋙ sheafToPresheaf JY (Type ww)) :=
    inferInstanceAs (PreservesFiniteProducts (sheafToPresheaf JX (Type ww) ⋙ w.op.ran))
  exact preservesFiniteProducts_of_reflects_of_preserves _ (sheafToPresheaf JY (Type ww))

/-- **The leg of the limit cone, as a natural transformation of sections functors.** At a sheaf
of sets `F` on `X` its component is the leg at `(U, ψ : V ⟶ w(U))` of the limit cone computing
the direct image at `V`. -/
def sectionsLeg (V : Yᵒᵖ) (j : StructuredArrow V w.op) :
    w.sheafPushforwardCocontinuous (Type ww) JX JY ⋙ Sheaf.sectionsFunctor JY V ⟶
      Sheaf.sectionsFunctor JX j.right where
  app F := ranπ w.op F.obj V j
  naturality _ _ m := ranπ_map_functor w.op m.hom V j

end Cocontinuous

section Comparison

variable {X : Type uu} [Category.{vv} X] {Y : Type uu'} [Category.{vv'} Y] (w : X ⥤ Y)
  (JX : GrothendieckTopology X) (JY : GrothendieckTopology Y) [w.IsCocontinuous JX JY]
  [JX.HasSheafCompose (forget RingCat.{ww})] [JY.HasSheafCompose (forget RingCat.{ww})]
  [JX.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [JY.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [∀ F : Xᵒᵖ ⥤ Type ww, w.op.HasPointwiseRightKanExtension F]
  [∀ F : Xᵒᵖ ⥤ RingCat.{ww}, w.op.HasPointwiseRightKanExtension F]
  [∀ F : Xᵒᵖ ⥤ AddCommGrpCat.{ww}, w.op.HasPointwiseRightKanExtension F]
  (R OX : Sheaf JX RingCat.{ww}) (δ : R ⟶ OX) (OY : Sheaf JY RingCat.{ww})
  (ν : OY ⟶ pullbackRingSheaf JY (w.sheafPushforwardCocontinuous (Type ww) JX JY) R)
  (fSharp' : OY ⟶ (w.sheafPushforwardCocontinuous RingCat.{ww} JX JY).obj OX)

/-- **The comparison of the two underlying presheaves of abelian groups**: the comparison
between the right Kan extension along `w.op` of the underlying presheaf of abelian groups of `M`
and the right Kan extension of its underlying presheaf of sets, with the transported addition on
the latter, as a morphism of presheaves of abelian groups. -/
def pushforwardCocontinuousModuleAddHom (M : _root_.SheafOfModules.{ww} OX) :
    w.op.ran.obj M.val.presheaf ⟶
      pullbackModuleAb JY (w.sheafPushforwardCocontinuous (Type ww) JX JY) R
        ((_root_.SheafOfModules.restrictScalars δ).obj M) where
  app V :=
    letI : AddCommGroup
        ((w.sheafPushforwardCocontinuous (Type ww) JX JY ⋙ Sheaf.sectionsFunctor JY V).obj
          (Sheaf.moduleSheaf R ((_root_.SheafOfModules.restrictScalars δ).obj M))) :=
      Sheaf.moduleObjAddCommGroup R ((_root_.SheafOfModules.restrictScalars δ).obj M)
        (w.sheafPushforwardCocontinuous (Type ww) JX JY ⋙ Sheaf.sectionsFunctor JY V)
    AddCommGrpCat.ofHom (AddMonoidHom.mk'
      (((forget AddCommGrpCat.{ww}).rightKanExtensionCompIsoOfPreserves
        M.val.presheaf w.op).hom.app V)
      (fun x y => by
        refine ranπ_ext w.op (M.val.presheaf ⋙ forget AddCommGrpCat.{ww}) fun j => ?_
        refine (ranπ_ranCompIso_hom_app w M.val.presheaf V j (x + y)).trans ?_
        refine ((ranπ w.op M.val.presheaf V j).hom.map_add x y).trans (Eq.symm ?_)
        refine (Sheaf.moduleAddObj_naturality R
          ((_root_.SheafOfModules.restrictScalars δ).obj M)
          (sectionsLeg w JX JY V j) _ _).trans ?_
        refine (Sheaf.sectionsFunctor_map_moduleAddHom R
          ((_root_.SheafOfModules.restrictScalars δ).obj M) j.right _ _).trans ?_
        exact congrArg₂ (· + ·) (ranπ_ranCompIso_hom_app w M.val.presheaf V j x)
          (ranπ_ranCompIso_hom_app w M.val.presheaf V j y)))
  naturality _ _ g := by
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x => ?_)
    exact ConcreteCategory.congr_hom
      (((forget AddCommGrpCat.{ww}).rightKanExtensionCompIsoOfPreserves
        M.val.presheaf w.op).hom.naturality g) x

variable (hcompat : ∀ (V : Yᵒᵖ) (j : StructuredArrow V w.op) (r : OY.obj.obj V),
  (δ.hom.app j.right).hom (ranπ w.op (Sheaf.ringSheaf R).obj V j ((ν.hom.app V).hom r)) =
    (ranπ w.op OX.obj V j).hom ((fSharp'.hom.app V).hom r))

include hcompat

/-- **The comparison at one sheaf of modules, as a morphism of sheaves of modules**, when the
scalar maps `fSharp'` and `ν` followed by `δ` agree on every leg of the limit cone (`hcompat`). -/
def pushforwardCocontinuousModuleHom (M : _root_.SheafOfModules.{ww} OX) :
    (pushforwardCocontinuous.{ww} w fSharp').obj M ⟶
      (_root_.SheafOfModules.restrictScalars ν).obj
        ((pullbackModuleFunctor JY (w.sheafPushforwardCocontinuous (Type ww) JX JY) R).obj
          ((_root_.SheafOfModules.restrictScalars δ).obj M)) :=
  ⟨PresheafOfModules.homMk (pushforwardCocontinuousModuleAddHom w JX JY R OX δ M)
    (fun V r m => by
      refine ranπ_ext w.op (M.val.presheaf ⋙ forget AddCommGrpCat.{ww}) fun j => ?_
      refine (ranπ_ranCompIso_hom_app w M.val.presheaf V j _).trans
        ((ranSMul_π_apply w (structureMapPresheaf w fSharp') M.val V r j m).trans (Eq.symm ?_))
      refine (Sheaf.moduleSMulObj_naturality R
        ((_root_.SheafOfModules.restrictScalars δ).obj M)
        (sectionsLeg w JX JY V j) _ _).trans ?_
      refine (moduleSMulObj_restrictScalars δ M (Sheaf.sectionsFunctor JX j.right) _ _).trans ?_
      refine (Sheaf.sectionsFunctor_map_moduleSMulHom OX M j.right _ _).trans ?_
      exact congrArg₂ (· • ·) (hcompat V j r)
        (ranπ_ranCompIso_hom_app w M.val.presheaf V j m))⟩

/-- **The comparison at one sheaf of modules, as an isomorphism.** -/
def pushforwardCocontinuousModuleObjIso (M : _root_.SheafOfModules.{ww} OX) :
    (pushforwardCocontinuous.{ww} w fSharp').obj M ≅
      (_root_.SheafOfModules.restrictScalars ν).obj
        ((pullbackModuleFunctor JY (w.sheafPushforwardCocontinuous (Type ww) JX JY) R).obj
          ((_root_.SheafOfModules.restrictScalars δ).obj M)) := by
  haveI : IsIso ((sheafToPresheaf JY (Type ww)).map ((Sheaf.moduleSheafFunctor OY).map
      (pushforwardCocontinuousModuleHom w JX JY R OX δ OY ν fSharp' hcompat M))) :=
    inferInstanceAs (IsIso ((forget AddCommGrpCat.{ww}).rightKanExtensionCompIsoOfPreserves
      M.val.presheaf w.op).hom)
  haveI := isIso_of_reflects_iso ((Sheaf.moduleSheafFunctor OY).map
    (pushforwardCocontinuousModuleHom w JX JY R OX δ OY ν fSharp' hcompat M))
    (sheafToPresheaf JY (Type ww))
  haveI := isIso_of_reflects_iso
    (pushforwardCocontinuousModuleHom w JX JY R OX δ OY ν fSharp' hcompat M)
    (Sheaf.moduleSheafFunctor OY)
  exact asIso (pushforwardCocontinuousModuleHom w JX JY R OX δ OY ν fSharp' hcompat M)

/-- **The direct image of sheaves of modules along a cocontinuous functor of sites, with a
restriction of scalars on each side, is the transported one.** Restricting scalars along
`δ : R ⟶ O_X`, transporting modules along the direct image of sheaves of sets of the morphism of
topoi attached to `w` (Stacks 03D1, 03D2), and restricting scalars along
`ν : O_Y ⟶ f^{-1}R` is the direct image `Stacks.SheafOfModules.pushforwardCocontinuous` over the
structure map `fSharp'`, as soon as the two scalar maps agree on every leg of the limit cone that
computes the Kan extension. -/
def pushforwardCocontinuousModulesIso :
    _root_.SheafOfModules.restrictScalars δ ⋙
        pullbackModuleFunctor JY (w.sheafPushforwardCocontinuous (Type ww) JX JY) R ⋙
          _root_.SheafOfModules.restrictScalars ν ≅
      pushforwardCocontinuous.{ww} w fSharp' :=
  (NatIso.ofComponents
    (fun M => pushforwardCocontinuousModuleObjIso w JX JY R OX δ OY ν fSharp' hcompat M)
    (fun {_ _} φ => hom_ext_moduleSheafFunctor (by
      rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
      refine Sheaf.hom_ext ?_
      exact ranCompIso_naturality w.op (forget AddCommGrpCat.{ww}) (presheafMap φ.val)))).symm

end Comparison

end Stacks.SheafOfModules

end
