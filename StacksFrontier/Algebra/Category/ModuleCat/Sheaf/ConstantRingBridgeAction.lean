module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantRingBridge
public import StacksFrontier.CategoryTheory.Sites.Modules.Tensor
import StacksCore.Tactic.StacksAttribute

/-!
# The action of a constant ideal on a sheaf of modules over a constant sheaf of rings

Let `(C, J)` be a site, let `R` be a commutative ring and let `Osharp` be a sheaf of commutative
rings presented by the constant presheaf of rings with value `R` through `a`. A sheaf of
`R`-modules `F` becomes a sheaf of `Osharp`-modules by
`Stacks.ConstantSheaf.sheafOfModulesOfConstantRing`, and an `R`-linear map `φ : M ⟶ R` makes the
constant sheaf on `M`, read the same way, a sheaf of ideals of `Osharp` by
`Stacks.ConstantSheaf.constantModuleToUnit`. This file builds the resulting multiplication

`M̲ ⊗_{Osharp} F ⟶ F`

whose image is the product of that sheaf of ideals with `F`. For `M` an ideal `I` of `R` and `φ`
its inclusion this is the map whose image is the `I̲ · F` of Tag 093M.

The multiplication is assembled from two pieces. The first is the action of the structure sheaf
on any sheaf of modules, read over the constant presheaf of rings: `restrictScalarsAction` is the
map `Osharp ⊗ N ⟶ N` of presheaves of modules over the constant presheaf of rings, given on
sections by `r ⊗ y ↦ r • y`. The second is `PresheafOfModules.tensorSheafifyDesc`, the inverse
direction of Tag 0GMW, which carries the tensor product sheaf of two sheafifications to the
sheafification of the objectwise tensor product; since the bridge of a sheaf of `R`-modules *is*
such a sheafification, composing it with the universal property of that sheafification
(`PresheafOfModules.sheafificationHomEquiv`) is exactly what carries the presheaf-level
multiplication to the sheaf `M̲ ⊗_{Osharp} F`.

Tag 0GMW is stated over `CategoryTheory.Sheaf.toRingCat`, while the bridge is stated over
`Stacks.SheafOfModules.Tensor.ringSheaf`. The two sheaves of rings are definitionally equal, so
terms cross freely, but `Stacks.SheafOfModules.Tensor.ringSheaf` is a plain `def` and instance
search does not unfold it, so the local bijectivity hypotheses of this file do not reach Tag
0GMW by search. They are therefore handed over as explicit arguments at the two declarations
that invoke it.

## Main definitions

* `Stacks.ConstantSheaf.restrictScalarsAction`: the action `Osharp ⊗ N ⟶ N` of the structure
  sheaf on a presheaf of `Osharp`-modules, read over the constant presheaf of rings.
* `Stacks.ConstantSheaf.constantScalarMap`: the presheaf-level map `M̲ ⟶ Osharp` underlying
  `constantModuleToUnit`.
* `Stacks.ConstantSheaf.constantTensorAction`: the multiplication `M̲ ⊗_{Osharp} F ⟶ F`.

## Main results

* `Stacks.ConstantSheaf.constantTensorAction_unit_tmul`: the multiplication sends the pure tensor
  of the sheafification-unit images of a section `i` of `M̲` and a section `s` of `F` to
  `a(φ i) · s`.

## Implementation notes

The sections of `Osharp` are commutative, but `Stacks.SheafOfModules.Tensor.ringSheaf` lands in
`RingCat`, so the `CommRing` instance on them is not found by instance search;
`commRing_ringSheafSections` supplies it, and it is what makes the multiplication balanced in its
second variable.

Both variables of the multiplication are restrictions of scalars along `a`, whose carriers agree
with those of the unrestricted objects but whose module structures do not. The bilinearity of
`r ⊗ y ↦ r • y` is therefore stated through `restrictScalarsActionFun`, whose `show`s name the
unrestricted spellings, and each of the four conditions is discharged by an ordinary module
lemma applied to explicit arguments, so that the definitional unfolding happens in the
elaborator rather than in a rewrite.

## References

* [Stacks Project, Tag 093M](https://stacks.math.columbia.edu/tag/093M)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open AlgebraicGeometry.SheafOfModules
  (associatedRingMap moduleSheafification moduleSheafificationUnit)

universe v u w

namespace Stacks.ConstantSheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {O : Cᵒᵖ ⥤ CommRingCat.{w}} {Osharp : Sheaf J CommRingCat.{w}} (a : O ⟶ Osharp.obj)

/-- The sections of a sheaf of commutative rings are a commutative ring. Instance search does
not find this through `Stacks.SheafOfModules.Tensor.ringSheaf`, which lands in `RingCat`. -/
noncomputable instance commRing_ringSheafSections (U : Cᵒᵖ) :
    CommRing ((Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj.obj U : RingCat.{w}) :=
  inferInstanceAs (CommRing (Osharp.obj.obj U : CommRingCat.{w}))

variable (N : PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj)

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- Two sections of a sheaf of commutative rings act on a module of sections in either order. -/
theorem smul_comm_ringSheafSections (U : Cᵒᵖ)
    (r c : ((Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj.obj U : RingCat.{w}))
    (y : N.obj U) :
    r • c • y = c • r • y := by
  rw [smul_smul, smul_smul, mul_comm]

/-- The action of a section of the structure sheaf on a section of an `Osharp`-module, read as a
map of modules over the constant presheaf of rings: `r ⊗ y ↦ r • y`. -/
noncomputable def restrictScalarsActionFun (U : Cᵒᵖ)
    (r : ((PresheafOfModules.restrictScalars (associatedRingMap J a)).obj
      ((PresheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj))).obj U)
    (y : ((PresheafOfModules.restrictScalars (associatedRingMap J a)).obj N).obj U) :
    ((PresheafOfModules.restrictScalars (associatedRingMap J a)).obj N).obj U :=
  (show ((Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj.obj U : RingCat.{w}) from r) •
    (show (N.obj U) from y)

/-- The action `Osharp ⊗ N ⟶ N` of the structure sheaf on a presheaf of `Osharp`-modules, as a
map of presheaves of modules over the constant presheaf of rings. -/
noncomputable def restrictScalarsAction :
    (PresheafOfModules.restrictScalars (associatedRingMap J a)).obj
        (PresheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj) ⊗
      (PresheafOfModules.restrictScalars (associatedRingMap J a)).obj N ⟶
      (PresheafOfModules.restrictScalars (associatedRingMap J a)).obj N where
  app U := ModuleCat.MonoidalCategory.tensorLift (restrictScalarsActionFun J a N U)
    (fun r r' y => add_smul
      (show ((Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj.obj U : RingCat.{w}) from r)
      (show ((Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj.obj U : RingCat.{w}) from r')
      (show (N.obj U) from y))
    (fun c r y => mul_smul ((associatedRingMap J a).app U c)
      (show ((Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj.obj U : RingCat.{w}) from r)
      (show (N.obj U) from y))
    (fun r y y' => smul_add
      (show ((Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj.obj U : RingCat.{w}) from r)
      (show (N.obj U) from y) (show (N.obj U) from y'))
    (fun c r y => smul_comm_ringSheafSections J N U
      (show ((Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj.obj U : RingCat.{w}) from r)
      ((associatedRingMap J a).app U c) (show (N.obj U) from y))
  naturality {U _} g := ModuleCat.MonoidalCategory.tensor_ext fun r y =>
    (PresheafOfModules.map_smul N g
      (show ((Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj.obj U : RingCat.{w}) from r)
      (show (N.obj U) from y)).symm

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- On sections over `U`, `restrictScalarsAction` sends `r ⊗ y` to `r • y`. -/
@[simp]
theorem restrictScalarsAction_app_tmul (U : Cᵒᵖ)
    (r : ((PresheafOfModules.restrictScalars (associatedRingMap J a)).obj
      ((PresheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj))).obj U)
    (y : ((PresheafOfModules.restrictScalars (associatedRingMap J a)).obj N).obj U) :
    (restrictScalarsAction J a N).app U (r ⊗ₜ[(O.obj U : CommRingCat.{w})] y) =
      restrictScalarsActionFun J a N U r y :=
  rfl

end Stacks.ConstantSheaf

namespace Stacks.ConstantSheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {R : Type w} [CommRing R] [HasWeakSheafify J (ModuleCat.{w} R)]
  {Osharp : Sheaf J CommRingCat.{w}} (a : constantRingPresheaf C R ⟶ Osharp.obj)
  [locallyInjective : Presheaf.IsLocallyInjective J (associatedRingMap J a)]
  [locallySurjective : Presheaf.IsLocallySurjective J (associatedRingMap J a)]
  {M : ModuleCat.{w} R} (φ : M ⟶ ModuleCat.of R R) (F : Sheaf J (ModuleCat.{w} R))

/-- The map of presheaves of modules over the constant presheaf of rings from the constant sheaf
on `M` to the structure sheaf induced by an `R`-linear `φ : M ⟶ R`; it is the presheaf-level
datum underlying `constantModuleToUnit`. -/
noncomputable def constantScalarMap :
    ofConstantRingPresheaf ((constantSheaf J (ModuleCat.{w} R)).obj M).obj ⟶
      unitOverConstantRing J (associatedRingMap J a) :=
  (constantRingPresheafOfModules C R).map
    ((sheafToPresheaf J (ModuleCat.{w} R)).map
      (constantToRingAsModule J (associatedRingMap J a) φ))

/-- The multiplication `M̲ ⊗ F ⟶ F` of presheaves of modules over the constant presheaf of
rings: multiply a section of `F` by the section `a (φ i)` of the structure sheaf. -/
noncomputable def constantTensorPairing :
    PresheafOfModules.tensorObj
        (ofConstantRingPresheaf ((constantSheaf J (ModuleCat.{w} R)).obj M).obj)
        (ofConstantRingPresheaf F.obj) ⟶
      (PresheafOfModules.restrictScalars (associatedRingMap J a)).obj
        (sheafOfModulesOfConstantRing J (associatedRingMap J a) F).val :=
  MonoidalCategory.tensorHom (constantScalarMap J a φ)
      (moduleSheafificationUnit J a (ofConstantRingPresheaf F.obj)) ≫
    restrictScalarsAction J a (sheafOfModulesOfConstantRing J (associatedRingMap J a) F).val

/-- The multiplication `M̲ ⊗_{Osharp} F ⟶ F` of sheaves of modules over the structure sheaf.
For `M` an ideal `I` of `R` and `φ` its inclusion, its image is the product `I̲ · F` of the
sheaf of ideals `I̲` with `F`. -/
noncomputable def constantTensorAction :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Osharp))).obj
        (sheafOfModulesOfConstantRing J (associatedRingMap J a)
            ((constantSheaf J (ModuleCat.{w} R)).obj M),
          sheafOfModulesOfConstantRing J (associatedRingMap J a) F) ⟶
      sheafOfModulesOfConstantRing J (associatedRingMap J a) F :=
  letI : Presheaf.IsLocallyInjective J (Sheaf.toRingCatMap J a) := locallyInjective
  letI : Presheaf.IsLocallySurjective J (Sheaf.toRingCatMap J a) := locallySurjective
  PresheafOfModules.tensorSheafifyDesc J a
      (ofConstantRingPresheaf ((constantSheaf J (ModuleCat.{w} R)).obj M).obj)
      (ofConstantRingPresheaf F.obj) ≫
    (PresheafOfModules.sheafificationHomEquiv (associatedRingMap J a)
        (P := PresheafOfModules.tensorObj
          (ofConstantRingPresheaf ((constantSheaf J (ModuleCat.{w} R)).obj M).obj)
          (ofConstantRingPresheaf F.obj))
        (F := sheafOfModulesOfConstantRing J (associatedRingMap J a) F)).symm
      (constantTensorPairing J a φ F)

/-- The multiplication `M̲ ⊗_{Osharp} F ⟶ F` sends the pure tensor of the sheafification-unit
images of a section `i` of the constant presheaf on `M` and a section `s` of `F` to the product
of `a (φ i)` with `s`. -/
theorem constantTensorAction_unit_tmul (U : Cᵒᵖ)
    (i : (ofConstantRingPresheaf ((constantSheaf J (ModuleCat.{w} R)).obj M).obj).obj U)
    (s : (ofConstantRingPresheaf F.obj).obj U) :
    (constantTensorAction J a φ F).val.app U
        (((PresheafOfModules.sheafificationAdjunction
              (R := Stacks.SheafOfModules.Tensor.ringSheaf Osharp)
              (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj)).unit.app
            (PresheafOfModules.tensorObj
              (sheafOfModulesOfConstantRing J (associatedRingMap J a)
                ((constantSheaf J (ModuleCat.{w} R)).obj M)).val
              (sheafOfModulesOfConstantRing J (associatedRingMap J a) F).val)).app U
          ((moduleSheafificationUnit J a
              (ofConstantRingPresheaf ((constantSheaf J (ModuleCat.{w} R)).obj M).obj)).app U i ⊗ₜ
            (moduleSheafificationUnit J a (ofConstantRingPresheaf F.obj)).app U s)) =
      restrictScalarsActionFun J a
        (sheafOfModulesOfConstantRing J (associatedRingMap J a) F).val U
        ((constantScalarMap J a φ).app U i)
        ((moduleSheafificationUnit J a (ofConstantRingPresheaf F.obj)).app U s) := by
  let : Presheaf.IsLocallyInjective J (Sheaf.toRingCatMap J a) := locallyInjective
  let : Presheaf.IsLocallySurjective J (Sheaf.toRingCatMap J a) := locallySurjective
  have h1 := PresheafOfModules.tensorSheafifyDesc_unit_tmul J a
      (ofConstantRingPresheaf ((constantSheaf J (ModuleCat.{w} R)).obj M).obj)
      (ofConstantRingPresheaf F.obj) U
      ((moduleSheafificationUnit J a
        (ofConstantRingPresheaf ((constantSheaf J (ModuleCat.{w} R)).obj M).obj)).app U i)
      ((moduleSheafificationUnit J a (ofConstantRingPresheaf F.obj)).app U s)
  have h2 := PresheafOfModules.tensorSheafifyBilinear_unit J a
      (ofConstantRingPresheaf ((constantSheaf J (ModuleCat.{w} R)).obj M).obj)
      (ofConstantRingPresheaf F.obj) U i s
  have h3 := AlgebraicGeometry.SheafOfModules.lift_unit_apply J (associatedRingMap J a)
      (PresheafOfModules.tensorObj
        (ofConstantRingPresheaf ((constantSheaf J (ModuleCat.{w} R)).obj M).obj)
        (ofConstantRingPresheaf F.obj))
      (sheafOfModulesOfConstantRing J (associatedRingMap J a) F)
      (constantTensorPairing J a φ F) U (i ⊗ₜ s)
  exact (congrArg
    (fun z => ((PresheafOfModules.sheafificationHomEquiv (associatedRingMap J a)
        (P := PresheafOfModules.tensorObj
          (ofConstantRingPresheaf ((constantSheaf J (ModuleCat.{w} R)).obj M).obj)
          (ofConstantRingPresheaf F.obj))
        (F := sheafOfModulesOfConstantRing J (associatedRingMap J a) F)).symm
      (constantTensorPairing J a φ F)).val.app U z) (h1.trans h2)).trans h3

section Locality

variable [J.WEqualsLocallyBijective (ModuleCat.{w} R)]

/-- A map out of `F` over the structure sheaf which kills every constant multiple `a (φ m) · y`
kills the whole product `M̲ ⊗_{Osharp} F`. A section of `M̲` is only locally constant, so the
hypothesis is applied after restricting to a covering sieve on which it is constant; the
restriction is computed by the naturality of `g` and of the ideal map, and the value of the
ideal map on a constant section is `constantToRingAsModule_app_toSheafify`. -/
theorem constantTensorAction_comp_eq_zero
    {Z : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)}
    (g : sheafOfModulesOfConstantRing J (associatedRingMap J a) F ⟶ Z)
    (hg : ∀ (m : M) (U : Cᵒᵖ)
        (y : (sheafOfModulesOfConstantRing J (associatedRingMap J a) F).val.obj U),
      (g.val.app U) (((associatedRingMap J a).app U) (φ.hom m) • y) = 0) :
    constantTensorAction J a φ F ≫ g = 0 := by
  have key : (PresheafOfModules.sheafificationHomEquiv (associatedRingMap J a)).symm
        (constantTensorPairing J a φ F) ≫ g = 0 := by
    apply PresheafOfModules.sheafification_hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro i s
    refine Eq.trans (congrArg (fun x => (g.val.app U) x)
      (AlgebraicGeometry.SheafOfModules.lift_unit_apply J (associatedRingMap J a) _ _
        (constantTensorPairing J a φ F) U (i ⊗ₜ s))) ?_
    apply Z.isSheaf.isSeparated _ _
      (Presheaf.imageSieve_mem J (CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj M)) i)
    rintro V h ⟨m, hm⟩
    have hscalar : ((Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj.map h.op)
          ((constantScalarMap J a φ).app U i) =
        ((associatedRingMap J a).app (op V)) (φ.hom m) := by
      refine Eq.trans ?_
        (constantToRingAsModule_app_toSheafify J (associatedRingMap J a) φ (op V) m)
      refine Eq.trans (PresheafOfModules.naturality_apply (constantScalarMap J a φ) h.op i).symm ?_
      exact congrArg (fun x => ((constantScalarMap J a φ).app (op V)) x) hm.symm
    show Z.val.map h.op ((g.val.app U) _) = Z.val.map h.op 0
    rw [map_zero]
    refine Eq.trans (PresheafOfModules.naturality_apply g.val h.op _).symm ?_
    refine Eq.trans (congrArg (fun z => (g.val.app (op V)) z)
      (PresheafOfModules.map_smul (sheafOfModulesOfConstantRing J (associatedRingMap J a) F).val
        h.op ((constantScalarMap J a φ).app U i)
        ((moduleSheafificationUnit J a (ofConstantRingPresheaf F.obj)).app U s))) ?_
    refine Eq.trans (congrArg (fun r => (g.val.app (op V))
      (r • ((sheafOfModulesOfConstantRing J (associatedRingMap J a) F).val.map h.op
        ((moduleSheafificationUnit J a (ofConstantRingPresheaf F.obj)).app U s)))) hscalar) ?_
    exact hg m (op V) _
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => _ ≫ k) key).trans comp_zero)

end Locality

end Stacks.ConstantSheaf

end
