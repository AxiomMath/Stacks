module

public import Mathlib.LinearAlgebra.Dual.BaseChange
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparisonIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomStalk
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundle
public import StacksFrontier.AlgebraicGeometry.ComponentDegrees.Rank
public import StacksFrontier.AlgebraicGeometry.Conormal.SquareEpi
public import StacksFrontier.AlgebraicGeometry.Modules.DualSheafStalk.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFreeTFAE
public import StacksFrontier.AlgebraicGeometry.ReflexiveHull.DualStalk
public import StacksFrontier.AlgebraicGeometry.StalkFreeBridge.StalkFree
public import StacksFrontier.Topology.Sheaves.Modules.TensorAndDuals.InternalHom
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackStalkAdjunction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Base change of a virtual normal bundle

Let
```
Z' --i'--→ X'
|          |
g          f
↓          ↓
Z  --i---→ X
```
be a cartesian square of schemes whose horizontal arrows are immersions, and let `𝒩` be a
virtual normal bundle for `Z` in `X`, that is a finite locally free `𝒪_Z`-module together with
a surjection `𝒩^∨ ⟶ 𝒞_{Z/X}` onto the conormal sheaf.  Then `g^* 𝒩` is a virtual normal bundle
for `Z'` in `X'`.  This is Stacks 0FBJ.

Two inputs go into the construction.  Finite local freeness of `g^* 𝒩` transports the local free
presentations of `𝒩`, and makes the dual base-change map `g^*(𝒩^∨) ⟶ (g^* 𝒩)^∨` invertible, so
that a surjection out of `(g^* 𝒩)^∨` may be built from the pullback of the given one.  The
target is then reached by the surjection `g^* 𝒞_{Z/X} ⟶ 𝒞_{Z'/X'}` of Stacks 0473, which is the
only step of the Stacks Project's own proof.

## Main definitions

* `Stacks.Chow.pullbackDualMap` — the dual base-change map `g^*(M^∨) ⟶ (g^* M)^∨`.
* `Stacks.Chow.VirtualNormalBundle.baseChange` — Stacks 0FBJ: the virtual normal bundle
  `g^* 𝒩` for `Z'` in `X'`.

## Main results

* `Stacks.Chow.pullbackDualMap_isIso` — the dual base-change map of a finite locally free
  module is an isomorphism.
* `Stacks.Chow.isFiniteLocallyFree_pullback` — the pullback of a finite locally free module is
  finite locally free.

## Implementation notes

The pullback functor is `RingedSpaceModuleAdjunction.modulePullback` on the underlying ringed
spaces, which is the spelling in which the conormal comparison map of Stacks 0473 is stated and
is the same functor as `AlgebraicGeometry.Scheme.Modules.pullback`.

Invertibility of the dual base-change map is checked on stalks.  The three inputs are the stalk
formula for a pullback (Stacks 0098,
`RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv`), the stalk formula for a
dual (Stacks 01CP, `Stacks.AlgebraicGeometry.ReflexiveModules.dualStalkEquiv`), and freeness and
finiteness of the stalk of a finite locally free module
(`Stacks.StalkFreeBridge.freeAndFinite_stalk_of_isFiniteLocallyFree`); the algebra is then that
base change commutes with dualisation for a finite free module.

The statement is for immersions rather than closed immersions, and mentions no base scheme `S`:
the predicate `Stacks.Chow.VirtualNormalBundle` is itself stated for an immersion with no base,
and neither the dimension function nor finite type over a base enters the construction.

## References

* [Stacks Project, Tag 0FBJ](https://stacks.math.columbia.edu/tag/0FBJ)
* [Stacks Project, Tag 0FBQ](https://stacks.math.columbia.edu/tag/0FBQ)
* [Stacks Project, Tag 0473](https://stacks.math.columbia.edu/tag/0473)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CN](https://stacks.math.columbia.edu/tag/01CN)
* [Stacks Project, Tag 01CP](https://stacks.math.columbia.edu/tag/01CP)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.ReflexiveModules
open Stacks.SheafOfModules.SheafHomStalk
open scoped TensorProduct

universe u

namespace Stacks.Chow

noncomputable section

variable {X Y : Scheme.{u}}

/-- The image in `A ⊗_{𝒪_X} B` of a pure tensor of local sections over an open `U`: the
sheafification unit of the sectionwise tensor product, evaluated at `U`. -/
abbrev tensorSheafPure (X : Scheme.{u}) (A B : X.Modules) (U : X.Opens) :=
  Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection X.toRingedSpace A B (op U)

/-- The evaluation pairing `M^∨ ⊗_{𝒪_X} M ⟶ 𝒪_X` of a module on a scheme with its dual. -/
abbrev dualEvaluationMap (X : Scheme.{u}) (M : X.Modules) :=
  Stacks.SheafOfModules.evaluation X.sheaf.obj (structureSheafRing X.toRingedSpace).property M

/-- The evaluation pairing sends the pure tensor `s ⊗ m` of a local functional and a local
section to the value `s(m)`. -/
theorem evaluation_tmul (X : Scheme.{u}) (M : X.Modules) (U : X.Opens)
    (s : (dualSheaf M).val.obj (op U)) (m : M.val.obj (op U)) :
    (dualEvaluationMap X M).val.app (op U)
        (tensorSheafPure X (dualSheaf M) M U (s ⊗ₜ[X.presheaf.obj (op U)] m)) =
      (s.app (op (Over.mk (𝟙 U)))).hom m := by
  have h := (Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction X.sheaf.obj
      (structureSheafRing X.toRingedSpace).property).homEquiv
    ((PresheafOfModules.tensorObj (O := X.sheaf.obj) ((dualSheaf M).val) (M.val)))
    (SheafOfModules.unit X.ringCatSheaf) |>.apply_symm_apply
      (Stacks.SheafOfModules.evaluationPresheaf X.sheaf.obj
        (structureSheafRing X.toRingedSpace).property M)
  exact congrArg (fun q => q.app (op U)
    (s ⊗ₜ[(Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf
      X.sheaf.obj).obj (op U)] m)) h

/-- **[Stacks Project, Tag 01CD]** for a morphism of schemes: pulling back a tensor product
of modules is the tensor product of the pullbacks, `g^*(A ⊗ B) ≅ g^*A ⊗ g^*B`. -/
def pullbackTensorIso (g : X ⟶ Y) (A B : Y.Modules) :
    (modulePullback g.toLRSHom.toShHom).obj
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((Y.toRingedSpace)).presheaf, ((Y.toRingedSpace)).IsSheaf⟩).obj (A)).obj (B))) ≅
      (((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj
            (((modulePullback g.toLRSHom.toShHom).obj A))).obj
        (((modulePullback g.toLRSHom.toShHom).obj B))) :=
  @asIso _ _ _ _ (Stacks.RingedSpace.comparison g.toLRSHom.toShHom A B)
    (Stacks.RingedSpace.comparison_isIso g.toLRSHom.toShHom A B)

/-- The forward map of `Stacks.Chow.pullbackTensorIso` is the canonical comparison morphism. -/
theorem pullbackTensorIso_hom (g : X ⟶ Y) (A B : Y.Modules) :
    (pullbackTensorIso g A B).hom = Stacks.RingedSpace.comparison g.toLRSHom.toShHom A B := rfl

/-- The pairing `g^*(M^∨) ⊗ g^*M ⟶ 𝒪_X` obtained by pulling back the evaluation pairing of
`M` through the tensor comparison of Tag 01CD and the identification `g^* 𝒪_Y ≅ 𝒪_X`. -/
abbrev pullbackEvaluation (g : X ⟶ Y) (M : Y.Modules) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj
          (((modulePullback g.toLRSHom.toShHom).obj (dualSheaf M)))).obj
      (((modulePullback g.toLRSHom.toShHom).obj M))) ⟶
      SheafOfModules.unit X.ringCatSheaf :=
  (pullbackTensorIso g (dualSheaf M) M).inv ≫
    (modulePullback g.toLRSHom.toShHom).map (dualEvaluationMap Y M) ≫
      SheafOfModules.pullbackObjUnitToUnit (structureSheafHom g.toLRSHom.toShHom)

/-- Precomposing `Stacks.Chow.pullbackEvaluation` with the tensor comparison of Tag 01CD
returns the pulled-back evaluation pairing followed by `g^* 𝒪_Y ⟶ 𝒪_X`. -/
theorem comparison_comp_pullbackEvaluation (g : X ⟶ Y) (M : Y.Modules) :
    Stacks.RingedSpace.comparison g.toLRSHom.toShHom (dualSheaf M) M ≫
      pullbackEvaluation g M =
      (modulePullback g.toLRSHom.toShHom).map (dualEvaluationMap Y M) ≫
        SheafOfModules.pullbackObjUnitToUnit (structureSheafHom g.toLRSHom.toShHom) :=
  Iso.hom_inv_id_assoc (pullbackTensorIso g (dualSheaf M) M) _

/-- **The dual base-change map** `g^*(M^∨) ⟶ (g^*M)^∨`: the morphism adjoint, under the
internal-Hom/tensor adjunction of [Stacks Project, Tag 01CN], to the pulled-back evaluation
pairing `g^*(M^∨) ⊗ g^*M ⟶ 𝒪_X`. -/
def pullbackDualMap (g : X ⟶ Y) (M : Y.Modules) :
    (modulePullback g.toLRSHom.toShHom).obj (dualSheaf M) ⟶
      dualSheaf ((modulePullback g.toLRSHom.toShHom).obj M) :=
  Stacks.SheafOfModules.tensorHomEquiv X.toRingedSpace _ _ _ (pullbackEvaluation g M)

/-- The dual base-change map is characterised by currying: the functional it attaches to a
local section of `g^*(M^∨)` evaluates on a local section of `g^*M` through the pulled-back
evaluation pairing. -/
theorem pullbackDualMap_eval (g : X ⟶ Y) (M : Y.Modules) (W : X.Opens)
    (a : ((modulePullback g.toLRSHom.toShHom).obj (dualSheaf M)).val.obj (op W))
    (b : ((modulePullback g.toLRSHom.toShHom).obj M).val.obj (op W)) :
    (((pullbackDualMap g M).val.app (op W) a).app (op (Over.mk (𝟙 W)))).hom b =
      (pullbackEvaluation g M).val.app (op W) (tensorSheafPure X _ _ W
        (a ⊗ₜ[X.presheaf.obj (op W)] b)) :=
  Stacks.SheafOfModules.tensorHomEquiv_isTensorCurry X.toRingedSpace
    (pullbackEvaluation g M) W a b

/-- The tensor comparison of Tag 01CD carries the pullback of a pure tensor of local sections
to the pure tensor of their pullbacks. -/
theorem comparison_tensorSheafPure (g : X ⟶ Y) (A B : Y.Modules) (U : Y.Opens)
    (a : A.val.obj (op U)) (b : B.val.obj (op U)) :
    (Stacks.RingedSpace.comparison g.toLRSHom.toShHom A B).val.app (op (g ⁻¹ᵁ U))
        (((modulePullbackPushforwardAdjunction g.toLRSHom.toShHom).unit.app
          ((((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨((Y.toRingedSpace)).presheaf, ((Y.toRingedSpace)).IsSheaf⟩).obj (A)).obj
              (B)))).val.app (op U)
          (tensorSheafPure Y A B U (a ⊗ₜ[Y.presheaf.obj (op U)] b))) =
      tensorSheafPure X ((modulePullback g.toLRSHom.toShHom).obj A)
          ((modulePullback g.toLRSHom.toShHom).obj B) (g ⁻¹ᵁ U)
        (((modulePullbackPushforwardAdjunction g.toLRSHom.toShHom).unit.app A).val.app (op U) a
          ⊗ₜ[X.presheaf.obj (op (g ⁻¹ᵁ U))]
          ((modulePullbackPushforwardAdjunction g.toLRSHom.toShHom).unit.app B).val.app
            (op U) b) :=
  Stacks.RingedSpace.comparison_pullbackUnit_unit_tmul g.toLRSHom.toShHom A B (op U) a b

/-- A composite of morphisms of modules acts on local sections by composing the actions. -/
theorem comp_val_app {S : Scheme.{u}} {A B C : S.Modules} (a : A ⟶ B) (b : B ⟶ C)
    (U : S.Opens) (x : A.val.obj (op U)) :
    (a ≫ b).val.app (op U) x = b.val.app (op U) (a.val.app (op U) x) := rfl

/-- An equation `a ≫ b = c ≫ d` of morphisms of modules holds sectionwise. -/
private theorem comp_val_app_congr {S : Scheme.{u}} {A B C D : S.Modules} {a : A ⟶ B}
    {b : B ⟶ D} {c : A ⟶ C} {d : C ⟶ D} (h : a ≫ b = c ≫ d) (U : S.Opens)
    (x : A.val.obj (op U)) :
    b.val.app (op U) (a.val.app (op U) x) = d.val.app (op U) (c.val.app (op U) x) :=
  congrArg (fun t => t.val.app (op U) x) h

/-- The pushforward of a morphism of modules acts on sections over `U` as the morphism itself
acts on sections over `g^{-1}U`. -/
theorem pushforward_map_val_app (g : X ⟶ Y) {A B : X.Modules} (c : A ⟶ B)
    (U : Y.Opens) (y : ((modulePushforward g.toLRSHom.toShHom).obj A).val.obj (op U)) :
    ((modulePushforward g.toLRSHom.toShHom).map c).val.app (op U) y =
      c.val.app (op (g ⁻¹ᵁ U)) y := rfl

/-- Sectionwise form of `Stacks.Chow.comparison_comp_pullbackEvaluation`. -/
theorem pullbackEvaluation_comparison_app (g : X ⟶ Y) (M : Y.Modules) (W : X.Opens)
    (w : ((modulePullback g.toLRSHom.toShHom).obj
      ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((Y.toRingedSpace)).presheaf, ((Y.toRingedSpace)).IsSheaf⟩).obj ((dualSheaf M))).obj
          (M)))).val.obj (op W)) :
    (pullbackEvaluation g M).val.app (op W)
        ((Stacks.RingedSpace.comparison g.toLRSHom.toShHom (dualSheaf M) M).val.app (op W) w) =
      (SheafOfModules.pullbackObjUnitToUnit
          (structureSheafHom g.toLRSHom.toShHom)).val.app (op W)
        (((modulePullback g.toLRSHom.toShHom).map (dualEvaluationMap Y M)).val.app (op W) w) :=
  comp_val_app_congr (comparison_comp_pullbackEvaluation g M) W w

/-- Naturality of the unit of `g^* ⊣ g_*` on local sections: the pullback of a morphism
commutes with the canonical map from sections of a module to sections of its pullback. -/
theorem pullback_map_unit_app (g : X ⟶ Y) {A B : Y.Modules} (c : A ⟶ B)
    (U : Y.Opens) (z : A.val.obj (op U)) :
    ((modulePullback g.toLRSHom.toShHom).map c).val.app (op (g ⁻¹ᵁ U))
        (((modulePullbackPushforwardAdjunction g.toLRSHom.toShHom).unit.app
          A).val.app (op U) z) =
      ((modulePullbackPushforwardAdjunction g.toLRSHom.toShHom).unit.app
        B).val.app (op U) (c.val.app (op U) z) :=
  (pushforward_map_val_app g ((modulePullback g.toLRSHom.toShHom).map c) U _).symm.trans
    (comp_val_app_congr
      ((modulePullbackPushforwardAdjunction g.toLRSHom.toShHom).unit.naturality c) U z).symm

/-- The identification `g^* 𝒪_Y ⟶ 𝒪_X` takes the canonical image of a local function on `Y`
to its pullback along `g`. -/
theorem pullbackObjUnitToUnit_unit_app (g : X ⟶ Y) (U : Y.Opens)
    (r : (SheafOfModules.unit Y.ringCatSheaf).val.obj (op U)) :
    (SheafOfModules.pullbackObjUnitToUnit
          (structureSheafHom g.toLRSHom.toShHom)).val.app (op (g ⁻¹ᵁ U))
        (((modulePullbackPushforwardAdjunction g.toLRSHom.toShHom).unit.app
          (SheafOfModules.unit Y.ringCatSheaf)).val.app (op U) r) =
      (g.app U).hom r :=
  (comp_val_app _ _ U r).symm.trans
    (congrArg (fun t => t.val.app (op U) r)
      (SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
        (structureSheafHom g.toLRSHom.toShHom)))

/-- The pulled-back evaluation pairing, on the pure tensor of the canonical images of a local
functional `s` on `M` and a local section `m`, is the pullback of the function `s(m)`. -/
theorem pullbackEvaluation_unit_tmul (g : X ⟶ Y) (M : Y.Modules) (U : Y.Opens)
    (s : (dualSheaf M).val.obj (op U)) (m : M.val.obj (op U)) :
    (pullbackEvaluation g M).val.app (op (g ⁻¹ᵁ U))
      (tensorSheafPure X ((modulePullback g.toLRSHom.toShHom).obj (dualSheaf M))
          ((modulePullback g.toLRSHom.toShHom).obj M) (g ⁻¹ᵁ U)
        (((modulePullbackPushforwardAdjunction g.toLRSHom.toShHom).unit.app
            (dualSheaf M)).val.app (op U) s ⊗ₜ[X.presheaf.obj (op (g ⁻¹ᵁ U))]
          ((modulePullbackPushforwardAdjunction g.toLRSHom.toShHom).unit.app M).val.app
            (op U) m)) =
      (g.app U).hom ((s.app (op (Over.mk (𝟙 U)))).hom m) :=
  (congrArg (fun t => (pullbackEvaluation g M).val.app (op (g ⁻¹ᵁ U)) t)
      (comparison_tensorSheafPure g (dualSheaf M) M U s m)).symm.trans
    ((pullbackEvaluation_comparison_app g M (g ⁻¹ᵁ U) _).trans
      ((congrArg (fun t => (SheafOfModules.pullbackObjUnitToUnit
            (structureSheafHom g.toLRSHom.toShHom)).val.app (op (g ⁻¹ᵁ U)) t)
          (pullback_map_unit_app g (dualEvaluationMap Y M) U _)).trans
        ((pullbackObjUnitToUnit_unit_app g U _).trans
          (congrArg (fun t => (g.app U).hom t) (evaluation_tmul Y M U s m)))))

/-! ### Finite local freeness, finite presentation, and pullback -/

/-- A finite locally free module on a scheme is of finite presentation: it is locally free of
finite rank, so the local generating sections have no relations. -/
theorem isFinitePresentation_of_isFiniteLocallyFree {S : Scheme.{u}} (M : S.Modules)
    (h : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M) :
    M.IsFinitePresentation := by
  obtain ⟨q, hq, hfin⟩ := h.exists_isFiniteLocallyFreeData
  have hqc : M.IsQuasicoherent := q.quasiCoherentData.isQuasicoherent
  have h01 := ((Stacks.FiniteLocallyFree.ModuleTFAE.finiteLocallyFree_tfae M).out 4 1).mp h
  exact h01.2

/-- The pullback of a finite locally free sheaf of modules along a morphism of sites coming
from a continuous map of spaces is finite locally free: the local free presentations transport
with the same finite index types. -/
@[ega "III 7.7.9" "partial"]
theorem isFiniteLocallyFree_pullbackData {T T' : TopCat.{u}} (f : T ⟶ T')
    {S : Sheaf (Opens.grothendieckTopology T') RingCat.{u}}
    {R : Sheaf (Opens.grothendieckTopology T) RingCat.{u}}
    (φ : S ⟶ ((Opens.map f).sheafPushforwardContinuous RingCat _ _).obj R)
    [(SheafOfModules.pushforward φ).IsRightAdjoint]
    (M : SheafOfModules.{u} S)
    (h : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((SheafOfModules.pullback φ).obj M) := by
  obtain ⟨q, hq, hfin⟩ := h.exists_isFiniteLocallyFreeData
  choose G hG eUnit eM using fun i ↦
    Stacks.AlgebraicGeometry.ComponentDegrees.exists_pullbackOver f φ M (q.X i)
  refine { exists_isFiniteLocallyFreeData := ⟨{
      I := q.I
      X := fun i ↦ (Opens.map f).obj (q.X i)
      coversTop := (Opens.coversTop_iff _ _).2
        (((Opens.coversTop_iff _ _).1 q.coversTop).comap f.hom)
      generators := fun i ↦
        ((q.generators i).map (G i) (eUnit i).some).ofEpi (eM i).some.hom }, ?_, ?_⟩ }
  · constructor
    intro i
    have h0 : IsIso (q.generators i).π := hq.isIso i
    have h2 : IsIso (((q.generators i).map (G i) (eUnit i).some).π ≫ (eM i).some.hom) :=
      inferInstance
    exact Eq.mpr (congrArg IsIso (SheafOfModules.GeneratingSections.ofEpi_π
      ((q.generators i).map (G i) (eUnit i).some) (eM i).some.hom)) h2
  · constructor
    intro i
    have : (q.generators i).IsFiniteType := hfin.isFiniteType i
    infer_instance

/-- **The pullback of a finite locally free module along a morphism of schemes is finite
locally free.** -/
theorem isFiniteLocallyFree_pullback (g : X ⟶ Y) (M : Y.Modules)
    (h : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((modulePullback g.toLRSHom.toShHom).obj M) :=
  isFiniteLocallyFree_pullbackData _ (structureSheafHom g.toLRSHom.toShHom) M h

/-! ### Invertibility of the dual base-change map -/

/-- Linear algebra behind the dual base-change isomorphism: for `V` finite free over `R` and
`S` an `R`-algebra, a map from a model of `S ⊗_R V^*` to the `S`-dual of a model of `S ⊗_R V`
which is evaluation on pure tensors is bijective, because base change of the dual of a finite
free module is the dual of the base change. -/
theorem bijective_of_dual_baseChange
    {R S V W D : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    [AddCommGroup W] [Module S W] [AddCommGroup D] [Module S D]
    (eV : W ≃ₗ[S] S ⊗[R] V) (eD : D ≃ₗ[S] S ⊗[R] Module.Dual R V)
    (k : D →ₗ[S] Module.Dual S W)
    (h : ∀ (l : Module.Dual R V) (v : V),
      k (eD.symm (1 ⊗ₜ[R] l)) (eV.symm (1 ⊗ₜ[R] v)) = algebraMap R S (l v)) :
    Function.Bijective k := by
  let e : D ≃ₗ[S] Module.Dual S W := eD ≪≫ₗ
    (TensorProduct.isBaseChange R V S).toDualBaseChange ≪≫ₗ Module.Dual.congr eV.symm
  have hh : k.comp eD.symm.toLinearMap = e.toLinearMap.comp eD.symm.toLinearMap := by
    apply (TensorProduct.isBaseChange R (Module.Dual R V) S).algHom_ext
    intro l
    have hh' : (k (eD.symm (1 ⊗ₜ[R] l))).comp eV.symm.toLinearMap =
        (e (eD.symm (1 ⊗ₜ[R] l))).comp eV.symm.toLinearMap := by
      apply (TensorProduct.isBaseChange R V S).algHom_ext
      intro v
      simpa [e, Module.Dual.congr, LinearEquiv.congrLeft] using (h l v).trans
        ((TensorProduct.isBaseChange R V S).toDualBaseChange_tmul (1 : S) l v |>.trans
          (one_mul _)).symm
    exact LinearMap.ext fun w => by
      obtain ⟨v, rfl⟩ := eV.symm.surjective w
      exact LinearMap.congr_fun hh' v
  have hk : k = e.toLinearMap := LinearMap.ext fun d => by
    obtain ⟨t, rfl⟩ := eD.symm.surjective d
    exact LinearMap.congr_fun hh t
  exact hk ▸ e.bijective

/-- The dual base-change map, read through the stalk description of a dual of
[Stacks Project, Tag 01CP]: on the germs of the canonical images of a local functional and a
local section it is the map of local rings applied to the germ of the value. -/
theorem pullbackDualMap_dualStalkEquiv_germ (g : X ⟶ Y) (M : Y.Modules)
    [M.IsFinitePresentation]
    (hPfp : _root_.SheafOfModules.IsFinitePresentation.{u, u, u}
      ((modulePullback g.toLRSHom.toShHom).obj M))
    (x : X) (V : Y.Opens) (hxV : (g.toLRSHom.toShHom).hom.base x ∈ V)
    (sV : (dualSheaf M).val.obj (op V)) (t : M.val.obj (op V)) :
    @dualStalkEquiv X ((modulePullback g.toLRSHom.toShHom).obj M) hPfp x
        (stalkHom (pullbackDualMap g M) x
          (germAt (Rc := X.sheaf)
            ((modulePullback g.toLRSHom.toShHom).obj (dualSheaf M)) (g ⁻¹ᵁ V) x hxV
            (((modulePullbackPushforwardAdjunction g.toLRSHom.toShHom).unit.app
              (dualSheaf M)).val.app (op V) sV)))
        (germAt (Rc := X.sheaf)
          ((modulePullback g.toLRSHom.toShHom).obj M) (g ⁻¹ᵁ V) x hxV
          (((modulePullbackPushforwardAdjunction g.toLRSHom.toShHom).unit.app M).val.app
            (op V) t))
      = g.stalkMap x (dualStalkEquiv M ((g.toLRSHom.toShHom).hom.base x)
          (germAt (Rc := Y.sheaf) (dualSheaf M) V ((g.toLRSHom.toShHom).hom.base x) hxV sV)
          (germAt (Rc := Y.sheaf) M V ((g.toLRSHom.toShHom).hom.base x) hxV t)) := by
  have h1 := stalkHom_germAt (pullbackDualMap g M) x (g ⁻¹ᵁ V) hxV
    (((modulePullbackPushforwardAdjunction g.toLRSHom.toShHom).unit.app
      (dualSheaf M)).val.app (op V) sV)
  have h2 := @dualStalkEquiv_germAt X ((modulePullback g.toLRSHom.toShHom).obj M) hPfp x
    (g ⁻¹ᵁ V) hxV
    (Scheme.Modules.Hom.app (pullbackDualMap g M) (g ⁻¹ᵁ V)
      (((modulePullbackPushforwardAdjunction g.toLRSHom.toShHom).unit.app
        (dualSheaf M)).val.app (op V) sV))
    (((modulePullbackPushforwardAdjunction g.toLRSHom.toShHom).unit.app M).val.app (op V) t)
  have h3 := dualStalkEquiv_germAt M ((g.toLRSHom.toShHom).hom.base x) V hxV sV t
  have h4 := Scheme.Hom.germ_stalkMap_apply g V x hxV
    (Stacks.AlgebraicGeometry.ReflexiveModules.evalAt M sV t)
  have h5 := (pullbackDualMap_eval g M (g ⁻¹ᵁ V)
      (((modulePullbackPushforwardAdjunction g.toLRSHom.toShHom).unit.app
        (dualSheaf M)).val.app (op V) sV)
      (((modulePullbackPushforwardAdjunction g.toLRSHom.toShHom).unit.app M).val.app
        (op V) t)).trans (pullbackEvaluation_unit_tmul g M V sV t)
  refine (congrArg (fun z => @dualStalkEquiv X _ hPfp x z
    (germAt (Rc := X.sheaf) ((modulePullback g.toLRSHom.toShHom).obj M) (g ⁻¹ᵁ V) x hxV
      (((modulePullbackPushforwardAdjunction g.toLRSHom.toShHom).unit.app M).val.app
        (op V) t))) h1).trans ?_
  refine h2.trans ?_
  refine (congrArg (fun z =>
    Stacks.AlgebraicGeometry.ReflexiveModules.ringGermAt X (g ⁻¹ᵁ V) x hxV z) h5).trans ?_
  exact h4.symm.trans (congrArg (fun z => g.stalkMap x z) h3.symm)

/-- **The dual base-change map of a finite locally free module is an isomorphism**,
`g^*(M^∨) ≅ (g^*M)^∨`.  It is an isomorphism on every stalk: the stalk of a pullback is the
base change of the stalk ([Stacks Project, Tag 0098]), the stalk of a dual is the dual of the
stalk ([Stacks Project, Tag 01CP]), and the stalk of `M` is a finite free module over the local
ring, for which base change commutes with dualisation. -/
@[ega "0 5.4.5" "special case"]
theorem pullbackDualMap_isIso (g : X ⟶ Y) (M : Y.Modules)
    (hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M) :
    IsIso (pullbackDualMap g M) := by
  have hMfp : M.IsFinitePresentation := isFinitePresentation_of_isFiniteLocallyFree M hM
  have hPfp : _root_.SheafOfModules.IsFinitePresentation.{u, u, u}
      ((modulePullback g.toLRSHom.toShHom).obj M) :=
    isFinitePresentation_of_isFiniteLocallyFree _ (isFiniteLocallyFree_pullback g M hM)
  refine isIso_of_bijective_stalkHom (pullbackDualMap g M) fun x => ?_
  let _ := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := Y.presheaf) M.val ((g.toLRSHom.toShHom).hom.base x)
  let _ := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := Y.presheaf) (dualSheaf M).val ((g.toLRSHom.toShHom).hom.base x)
  let _ := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) (dualSheaf ((modulePullback g.toLRSHom.toShHom).obj M)).val x
  obtain ⟨hfree, hfinite⟩ :=
    Stacks.StalkFreeBridge.freeAndFinite_stalk_of_isFiniteLocallyFree M
      ((g.toLRSHom.toShHom).hom.base x)
  have hfree' : Module.Free (ToType (Y.presheaf.stalk
      ((g.toLRSHom.toShHom).hom.base x)))
      (↑(TopCat.Presheaf.stalk M.val.presheaf
        ((g.toLRSHom.toShHom).hom.base x))) := hfree
  have hfinite' : Module.Finite (ToType (Y.presheaf.stalk
      ((g.toLRSHom.toShHom).hom.base x)))
      (↑(TopCat.Presheaf.stalk M.val.presheaf
        ((g.toLRSHom.toShHom).hom.base x))) := hfinite
  let algInst : Algebra (Y.presheaf.stalk ((g.toLRSHom.toShHom).hom.base x))
      (X.presheaf.stalk x) :=
    ((g.toLRSHom.toShHom).hom.stalkMap x).hom.toAlgebra
  let _ := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) ((modulePullback g.toLRSHom.toShHom).obj (dualSheaf M)).val x
  let _ := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) ((modulePullback g.toLRSHom.toShHom).obj M).val x
  obtain ⟨eM, heM⟩ := RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv
    g.toLRSHom.toShHom M x
  obtain ⟨eD, heD⟩ := RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv
    g.toLRSHom.toShHom (dualSheaf M) x
  set a := dualStalkEquiv M ((g.toLRSHom.toShHom).hom.base x)
  set b := @dualStalkEquiv X ((modulePullback g.toLRSHom.toShHom).obj M) hPfp x
  set e := eD ≪≫ₗ a.baseChange (Y.presheaf.stalk ((g.toLRSHom.toShHom).hom.base x))
    (X.presheaf.stalk x) _ _
  have hk : Function.Bijective (fun d => b (stalkHom (pullbackDualMap g M) x d)) := by
    refine @bijective_of_dual_baseChange _ _ _ _ _ _ _ _ _ _ hfree' hfinite' _ _ _ _ eM e
      { toFun := fun d => b (stalkHom (pullbackDualMap g M) x d)
        map_add' := fun d d' =>
          (congrArg b (map_add (stalkHom (pullbackDualMap g M) x) d d')).trans
            (map_add b _ _)
        map_smul' := fun r d =>
          (congrArg b (LinearMap.map_smul (stalkHom (pullbackDualMap g M) x) r d)).trans
            (LinearEquiv.map_smul b r _) } ?_
    intro l v
    obtain ⟨U, hxU, s, hs⟩ := exists_germ_eq (dualSheaf M) (a.symm l)
    obtain ⟨V, hVU, hxV, t, ht⟩ := TopCat.Presheaf.exists_le_germ_eq
      (Stacks.SheafOfModules.SheafHomStalk.commVal M).presheaf v hxU
    have hsV : a (germAt (dualSheaf M) V ((g.toLRSHom.toShHom).hom.base x) hxV
        (resLE (dualSheaf M) hVU s)) = l :=
      ((congrArg a ((germAt_resLE (dualSheaf M) hVU hxV s).trans hs)).trans
        (a.apply_symm_apply l))
    have hd : e.symm (1 ⊗ₜ[ToType (Y.presheaf.stalk ((g.toLRSHom.toShHom).hom.base x))] l) =
        germAt (Rc := X.sheaf)
          ((modulePullback g.toLRSHom.toShHom).obj (dualSheaf M)) (g ⁻¹ᵁ V) x hxV
          (((modulePullbackPushforwardAdjunction g.toLRSHom.toShHom).unit.app
            (dualSheaf M)).val.app (op V) (resLE (dualSheaf M) hVU s)) :=
      e.injective ((e.apply_symm_apply _).trans (Eq.symm (((congrArg (a.baseChange
        (Y.presheaf.stalk ((g.toLRSHom.toShHom).hom.base x))
        (X.presheaf.stalk x) _ _) (heD V hxV (resLE (dualSheaf M) hVU s))).trans
        (LinearEquiv.baseChange_tmul _ _ _ _ _ _)).trans (congrArg _ hsV))))
    have hm : eM.symm (1 ⊗ₜ[ToType (Y.presheaf.stalk ((g.toLRSHom.toShHom).hom.base x))] v) =
        germAt (Rc := X.sheaf) ((modulePullback g.toLRSHom.toShHom).obj M) (g ⁻¹ᵁ V) x hxV
          (((modulePullbackPushforwardAdjunction g.toLRSHom.toShHom).unit.app M).val.app
            (op V) t) :=
      eM.injective ((eM.apply_symm_apply _).trans
        ((heM V hxV t).trans (congrArg _ ht)).symm)
    have hlv : a (germAt (dualSheaf M) V ((g.toLRSHom.toShHom).hom.base x) hxV
          (resLE (dualSheaf M) hVU s))
        (germAt (Rc := Y.sheaf) M V ((g.toLRSHom.toShHom).hom.base x) hxV t) = l v :=
      (congrArg (fun z => z (germAt (Rc := Y.sheaf) M V
          ((g.toLRSHom.toShHom).hom.base x) hxV t)) hsV).trans (congrArg (fun w => l w) ht)
    exact ((congrArg (fun d => b (stalkHom (pullbackDualMap g M) x d)
          (eM.symm (1 ⊗ₜ[ToType (Y.presheaf.stalk
            ((g.toLRSHom.toShHom).hom.base x))] v))) hd).trans
      ((congrArg (fun w => b (stalkHom (pullbackDualMap g M) x
            (germAt (Rc := X.sheaf)
              ((modulePullback g.toLRSHom.toShHom).obj (dualSheaf M)) (g ⁻¹ᵁ V) x hxV
              (((modulePullbackPushforwardAdjunction g.toLRSHom.toShHom).unit.app
                (dualSheaf M)).val.app (op V) (resLE (dualSheaf M) hVU s)))) w) hm).trans
        ((pullbackDualMap_dualStalkEquiv_germ g M hPfp x V hxV
            (resLE (dualSheaf M) hVU s) t).trans
          (congrArg (fun z => g.stalkMap x z) hlv))))
  exact (b.bijective.of_comp_iff' (stalkHom (pullbackDualMap g M) x)).mp hk

/-! ### Stacks 0FBJ -/

/-- **Stacks 0FBJ.** For a cartesian square of schemes whose horizontal arrows `i : Z ⟶ X`
and `i' : Z' ⟶ X'` are immersions, the pullback `g^* 𝒩` of a virtual normal bundle `𝒩` for
`Z` in `X` is a virtual normal bundle for `Z'` in `X'`: it is finite locally free, and the
surjection `(g^* 𝒩)^∨ ⟶ 𝒞_{Z'/X'}` is the composite of the base-change isomorphism
`(g^* 𝒩)^∨ ≅ g^* (𝒩^∨)`, the pullback of the given surjection, and the surjection
`g^* 𝒞_{Z/X} ⟶ 𝒞_{Z'/X'}` of [Stacks Project, Tag 0473]. -/
@[stacks 0FBJ]
def VirtualNormalBundle.baseChange {Z X Z' X' : Scheme.{u}} (i : Z ⟶ X) (i' : Z' ⟶ X')
    [IsImmersion i] [IsImmersion i'] (g : Z' ⟶ Z) (f : X' ⟶ X)
    (sq : IsPullback i' g f i) (N : VirtualNormalBundle i) : VirtualNormalBundle i' :=
  { bundle := (modulePullback g.toLRSHom.toShHom).obj N.bundle
    isFiniteLocallyFree := isFiniteLocallyFree_pullback g N.bundle N.isFiniteLocallyFree
    surjection := (@asIso _ _ _ _ (pullbackDualMap g N.bundle)
          (pullbackDualMap_isIso g N.bundle N.isFiniteLocallyFree)).inv ≫
        (modulePullback g.toLRSHom.toShHom).map N.surjection ≫
          Stacks.Immersion.immersionConormalSheafMap i' i g f
            (Stacks.Immersion.toShHom_square sq.w)
    epi := @epi_comp _ _ _ _ _ _
      (@IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_inv _)) _
      (@epi_comp _ _ _ _ _ _
        (@Functor.map_epi _ _ _ _ (modulePullback g.toLRSHom.toShHom)
          (Functor.preservesEpimorphisms_of_adjunction
            (modulePullbackPushforwardAdjunction g.toLRSHom.toShHom)) _ _ N.surjection N.epi) _
        (Stacks.Immersion.epi_immersionConormalSheafMap i' i g f sq)) }

end
end Stacks.Chow

end
