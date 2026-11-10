module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Subobject.Limits
public import StacksFrontier.Homology.Injectives.Sheaf.DualizingModule
public import StacksFrontier.Homology.Injectives.Sheaf.InternalHomExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtensionByZeroUnit
import StacksCore.Tactic.StacksAttribute

/-!
# The evaluation map into the double dual is a monomorphism

Let `(C, O)` be a ringed site and `J` an injective abelian sheaf admitting a monomorphism from
`⨁ j_{U!}O_U/I`. Write `F^∨ = ℋom(F, J)` for the abelian internal hom with its induced
`O`-module structure, and `ev : F ⟶ (F^∨)^∨` for the evaluation map `ev(x)(φ) = φ(x)`.

This file fixes that `J` for the family `U ↦ j_{U!}O_U`, constructs `ev`, and proves that it is
a monomorphism: the chosen `J` detects sections, so a section killed by `ev` is zero.

## Main definitions

* `Stacks.Injectives.DualEvaluation.extensionByZeroUnitFamily`: the family `U ↦ j_{U!}O_U`.
* `Stacks.Injectives.DualEvaluation.dualizingSheafOfRingedSite`: the dualizing sheaf of the site.
* `Stacks.Injectives.DualEvaluation.ev`: the evaluation map `F ⟶ (F^∨)^∨`.

## Main results

* `Stacks.Injectives.DualEvaluation.evaluation_mono`: the evaluation map is a monomorphism.
* `Stacks.Injectives.DualEvaluation.ev_apply`: the defining formula `ev(x)(φ) = φ(x)`.
* `Stacks.Injectives.DualEvaluation.exists_local_hom_ne_zero`: every nonzero local section is
  detected by a local homomorphism into the dualizing sheaf.
* `Stacks.Injectives.DualEvaluation.sections_injective_of_mono`: a monomorphism of abelian
  sheaves is injective on sections over every object.

## Implementation notes

A section of the dual `ℋom(F, J)` over `U` is, definitionally, a homomorphism of the restricted
abelian presheaves over the localized site, so the pairing of such a section against a section of
`F` over `U` is its component at the terminal object `𝟙 U`; no comparison map is needed, and
`ev_apply` is the formula read off at that component.

`sections_injective_of_mono` is derived from the right-adjointness of the forgetful functor to
presheaves.

`mono_cokernelDesc` is stated for an arbitrary abelian category and proved with a single abelian
instance. That matters at the point of use: `SheafOfModules R` carries two propositionally equal
but not definitionally equal `HasZeroMorphisms` instances, one from
`SheafOfModules.instPreadditive` and one derived from `Abelian`, and a proof mixing them does not
typecheck.

The coefficients are a sheaf of *commutative* rings: the `O`-module structure on `ℋom(F, J)` is
`(r · φ)(x) = φ(r · x)`, and this action is associative only when `O` is commutative.

## References

* [Stacks Project, Tag 01DS](https://stacks.math.columbia.edu/tag/01DS)
* [Stacks Project, Tag 01DQ](https://stacks.math.columbia.edu/tag/01DQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Injectives.AbelianDual
open Stacks.SheafOfModules

namespace Stacks.Injectives.DualEvaluation

universe w v u

section General

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat}

/-- The evaluation functors `SheafOfModules.evaluation R U` are jointly faithful: a morphism of
sheaves of modules is zero as soon as all of its sections are. -/
theorem hom_zero_of_evaluation {X Y : SheafOfModules.{w} R} (f : X ⟶ Y)
    (h : ∀ U, (SheafOfModules.evaluation R U).map f = 0) : f = 0 := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.Hom.ext
  funext U
  exact h U

/-- In any abelian category, the canonical coimage-to-image morphism
`cokernel.desc (kernelSubobject t).arrow t _` of a morphism `t : X ⟶ Y` is a monomorphism. It is
the image inclusion of `t`, identified with `Abelian.factorThruCoimage t` along the canonical
isomorphism `cokernel (kernelSubobject t).arrow ≅ Abelian.coimage t`. -/
theorem mono_cokernelDesc {A : Type*} [Category A] [Abelian A] {X Y : A} (t : X ⟶ Y) :
    Mono (cokernel.desc (kernelSubobject t).arrow t (kernelSubobject_arrow_comp t)) := by
  set q := cokernel.desc (kernelSubobject t).arrow t (kernelSubobject_arrow_comp t) with hq
  let e : cokernel (kernelSubobject t).arrow ≅ Abelian.coimage t :=
    (cokernelEpiComp (kernelSubobjectIso t).inv (kernelSubobject t).arrow).symm.trans
      (cokernelIsoOfEq (kernelSubobject_arrow' t))
  have hfac : e.inv ≫ q = Abelian.factorThruCoimage t := by
    apply coequalizer.hom_ext
    change cokernel.π (kernel.ι t) ≫ e.inv ≫ q
        = cokernel.π (kernel.ι t) ≫ Abelian.factorThruCoimage t
    rw [Abelian.coimage.fac t, ← Category.assoc]
    show (cokernel.π (kernel.ι t) ≫ e.inv) ≫ q = t
    simp only [e, Iso.trans_inv, Iso.symm_inv, cokernelEpiComp_hom,
      cokernelIsoOfEq_inv_comp_desc, cokernel.π_desc, hq]
  have hm : Mono (e.inv ≫ q) := by rw [hfac]; infer_instance
  have hq' : q = e.hom ≫ (e.inv ≫ q) := by
    rw [← Category.assoc, e.hom_inv_id, Category.id_comp]
  rw [hq']; exact mono_comp _ _

end General

section RingedSite

variable {C : Type u} [SmallCategory C] {K : GrothendieckTopology C}

/-- A monomorphism of abelian sheaves is injective on sections over every object. -/
theorem sections_injective_of_mono {A B : Sheaf K AddCommGrpCat.{u}} (f : A ⟶ B) (hf : Mono f)
    (X : Cᵒᵖ) : Function.Injective (f.hom.app X) := by
  have := hf
  have h1 : Mono ((sheafToPresheaf K AddCommGrpCat.{u}).map f) :=
    Functor.PreservesMonomorphisms.preserves (F := sheafToPresheaf K AddCommGrpCat.{u}) f
  exact (AddCommGrpCat.mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app _).1 h1 X)

section Evaluation

variable (O : Sheaf K CommRingCat.{u}) (Jab : Sheaf K AddCommGrpCat.{u})

/-- Evaluating a dual section at a restricted section is natural in the slice object. -/
theorem evSection_aux (F : SheafOfModules.{u} (underlyingRingSheaf O))
    {X V V' : C} (k : V' ⟶ V) (h : V ⟶ X) (x : F.val.presheaf.obj (op X))
    (φ : (Over.forget V).op ⋙ F.val.presheaf ⟶ (Over.forget V).op ⋙ Jab.obj) :
    φ.app (op (Over.mk k)) (F.val.presheaf.map (k ≫ h).op x) =
      Jab.obj.map k.op (φ.app (op (Over.mk (𝟙 V))) (F.val.presheaf.map h.op x)) := by
  rw [op_comp, Functor.map_comp, CategoryTheory.comp_apply]
  have hn := NatTrans.naturality_apply φ (Over.homMk k : Over.mk k ⟶ Over.mk (𝟙 V)).op
    (F.val.presheaf.map h.op x)
  simp only [Functor.comp_map, Functor.op_map, Over.forget_map] at hn
  exact hn

/-- Restricting a dual section to a smaller slice object and evaluating there is the same as
evaluating and then restricting the value. -/
theorem evSection_aux' (F : SheafOfModules.{u} (underlyingRingSheaf O))
    {X V V' : C} (k : V' ⟶ V) (h : V ⟶ X) (h' : V' ⟶ X) (hw : k ≫ h = h')
    (x : F.val.presheaf.obj (op X))
    (φ : (presheafHom F.val.presheaf Jab.obj).obj (op V)) :
    ((presheafHom F.val.presheaf Jab.obj).map k.op φ).app (op (Over.mk (𝟙 V')))
        (F.val.presheaf.map h'.op x) =
      Jab.obj.map k.op (φ.app (op (Over.mk (𝟙 V))) (F.val.presheaf.map h.op x)) := by
  subst hw
  rw [presheafHom_map_app (𝟙 V') k k (Category.id_comp k)]
  exact evSection_aux O Jab F k h x φ

/-- The double-dual section attached to a section `x` of `F` over `X`: it sends a dual section
`φ` over a slice object to `φ` evaluated at the restriction of `x` to that object. -/
def evSection (F : SheafOfModules.{u} (underlyingRingSheaf O)) (X : Cᵒᵖ)
    (x : F.val.presheaf.obj X) :
    (Over.forget X.unop).op ⋙ ((dualFunctor O Jab).obj (op F)).val.presheaf ⟶
      (Over.forget X.unop).op ⋙ Jab.obj where
  app Z := AddCommGrpCat.ofHom
    { toFun := fun φ => φ.app (op (Over.mk (𝟙 Z.unop.left)))
        (F.val.presheaf.map Z.unop.hom.op x)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  naturality {Z Z'} f := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro φ
    change ((presheafHom F.val.presheaf Jab.obj).map (unop f).left.op φ).app
          (op (Over.mk (𝟙 (unop Z').left))) (F.val.presheaf.map (unop Z').hom.op x)
        = Jab.obj.map (unop f).left.op
            (φ.app (op (Over.mk (𝟙 (unop Z).left))) (F.val.presheaf.map (unop Z).hom.op x))
    exact evSection_aux' O Jab F (unop f).left (unop Z).hom (unop Z').hom
      (Over.w (unop f)) x φ

/-- The evaluation morphism, on underlying presheaves of abelian groups. -/
def evPresheafHom (F : SheafOfModules.{u} (underlyingRingSheaf O)) :
    F.val.presheaf ⟶
      ((dualFunctor O Jab).obj (op ((dualFunctor O Jab).obj (op F)))).val.presheaf where
  app X := AddCommGrpCat.ofHom
    { toFun := evSection O Jab F X
      map_zero' := by
        apply NatTrans.ext
        funext Z
        apply AddCommGrpCat.hom_ext
        apply AddMonoidHom.ext
        intro φ
        exact (congrArg (fun y => (φ.app (op (Over.mk (𝟙 (unop Z).left)))).hom y)
          (map_zero (AddCommGrpCat.Hom.hom (F.val.presheaf.map (unop Z).hom.op)))).trans
            (map_zero _)
      map_add' := fun a b => by
        apply NatTrans.ext
        funext Z
        apply AddCommGrpCat.hom_ext
        apply AddMonoidHom.ext
        intro φ
        exact (congrArg (fun y => (φ.app (op (Over.mk (𝟙 (unop Z).left)))).hom y)
          (map_add (AddCommGrpCat.Hom.hom (F.val.presheaf.map (unop Z).hom.op)) a b)).trans
            (map_add _ _ _) }
  naturality {X Y} f := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    apply NatTrans.ext
    funext Z
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro φ
    have h : (F.val.presheaf.map (unop Z).hom.op).hom ((F.val.presheaf.map f).hom x)
        = (F.val.presheaf.map ((unop Z).hom ≫ unop f).op).hom x := by
      rw [op_comp, Functor.map_comp]
      rfl
    exact congrArg (fun y => (φ.app (op (Over.mk (𝟙 (unop Z).left)))).hom y) h

/-- The evaluation morphism is `O`-linear, the action on the dual being precomposition with the
action on its argument. -/
theorem evPresheafHom_smul (F : SheafOfModules.{u} (underlyingRingSheaf O)) (X : Cᵒᵖ)
    (r : (underlyingRingSheaf O).obj.obj X) (m : F.val.obj X) :
    (evPresheafHom O Jab F).app X (r • m) = r • (evPresheafHom O Jab F).app X m := by
  apply NatTrans.ext
  funext Z
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro φ
  have h2 : ((underlyingRingSheaf O).obj.map (𝟙 (unop Z).left).op).hom
      (((underlyingRingSheaf O).obj.map (unop Z).hom.op).hom r)
      = ((underlyingRingSheaf O).obj.map (unop Z).hom.op).hom r := by
    rw [op_id, CategoryTheory.Functor.map_id]
    rfl
  have h : (F.val.presheaf.map (unop Z).hom.op).hom (r • m)
      = (((underlyingRingSheaf O).obj.map (𝟙 (unop Z).left).op).hom
          (((underlyingRingSheaf O).obj.map (unop Z).hom.op).hom r))
        • (F.val.presheaf.map (unop Z).hom.op).hom m := by
    rw [h2]
    exact F.val.map_smul (unop Z).hom.op r m
  exact congrArg (fun y => (φ.app (op (Over.mk (𝟙 (unop Z).left)))).hom y) h

/-- The evaluation morphism `ev : F ⟶ (F^∨)^∨`, sending a section `x` of `F` to evaluation at
`x`. -/
def ev (F : SheafOfModules.{u} (underlyingRingSheaf O)) :
    F ⟶ (dualFunctor O Jab).obj (op ((dualFunctor O Jab).obj (op F))) :=
  ⟨PresheafOfModules.homMk (evPresheafHom O Jab F) (evPresheafHom_smul O Jab F)⟩

/-- **The defining formula of the evaluation morphism:** `(ev x)(φ) = φ(x)`. -/
theorem ev_apply (F : SheafOfModules.{u} (underlyingRingSheaf O)) (U : C)
    (x : F.val.obj (op U)) (φ : ((dualFunctor O Jab).obj (op F)).val.obj (op U)) :
    (((ev O Jab F).val.app (op U)) x).app (op (Over.mk (𝟙 U))) φ
      = φ.app (op (Over.mk (𝟙 U))) x := by
  have h : (F.val.presheaf.map (𝟙 U).op).hom x = x := by
    rw [op_id, CategoryTheory.Functor.map_id]
    rfl
  exact congrArg (fun y => (φ.app (op (Over.mk (𝟙 U)))).hom y) h

end Evaluation

variable [HasSheafify K AddCommGrpCat.{u}] (O : Sheaf K CommRingCat.{u})

/-- The family `U ↦ j_{U!}O_U` of extensions by zero of the structure sheaves of the localized
sites. -/
abbrev extensionByZeroUnitFamily : C → SheafOfModules.{u} (underlyingRingSheaf O) :=
  fun U => extensionByZeroUnit.{u, u, u, u} (underlyingRingSheaf O) U

/-- The dualizing sheaf of the ringed site: an injective abelian sheaf admitting a monomorphism
from the direct sum of all the quotients `j_{U!}O_U/I`. -/
abbrev dualizingSheafOfRingedSite : Sheaf K AddCommGrpCat.{u} :=
  dualizingSheaf (underlyingRingSheaf O) (extensionByZeroUnitFamily O)

/-- **The separation property of the dualizing sheaf.** A nonzero section `x` of an `O`-module
`F` over `U` is not killed by every local homomorphism `F|_U ⟶ J|_U`, where `J` is the dualizing
sheaf of the site. -/
theorem exists_local_hom_ne_zero (F : SheafOfModules.{u} (underlyingRingSheaf O)) (U : C)
    (x : F.val.obj (op U)) (hx : x ≠ 0) :
    ∃ φ : ((Over.forget U).op ⋙ F.val.presheaf ⟶
        (Over.forget U).op ⋙ (dualizingSheafOfRingedSite O).obj),
      φ.app (op (Over.mk (𝟙 U))) x ≠ 0 := by
  let s : extensionByZeroUnitFamily O U ⟶ F :=
    (extensionByZeroUnitHomEquiv.{u, u, u, u} (underlyingRingSheaf O) U F).symm x
  have hsx : extensionByZeroUnitHomEquiv.{u, u, u, u} (underlyingRingSheaf O) U F s = x :=
    Equiv.apply_symm_apply _ _
  let π : extensionByZeroUnitFamily O U ⟶ cokernel (kernelSubobject s).arrow :=
    cokernel.π (kernelSubobject s).arrow
  let q : cokernel (kernelSubobject s).arrow ⟶ F :=
    cokernel.desc (kernelSubobject s).arrow s (kernelSubobject_arrow_comp s)
  have hπq : π ≫ q = s := cokernel.π_desc _ _ _
  have hqmono : Mono q := mono_cokernelDesc s
  let g : (SheafOfModules.toSheaf (underlyingRingSheaf O)).obj
      (cokernel (kernelSubobject s).arrow) ⟶ dualizingSheafOfRingedSite O :=
    cyclicQuotientEmbedding (underlyingRingSheaf O) (extensionByZeroUnitFamily O)
      ⟨U, kernelSubobject s⟩
  have hgmono : Mono g :=
    mono_cyclicQuotientEmbedding (underlyingRingSheaf O) (extensionByZeroUnitFamily O)
      ⟨U, kernelSubobject s⟩
  have hmono : Mono ((SheafOfModules.toSheaf (underlyingRingSheaf O)).map q) := inferInstance
  let φ₀ : (SheafOfModules.toSheaf (underlyingRingSheaf O)).obj F ⟶
      dualizingSheafOfRingedSite O :=
    Injective.factorThru g ((SheafOfModules.toSheaf (underlyingRingSheaf O)).map q)
  have hfac : (SheafOfModules.toSheaf (underlyingRingSheaf O)).map q ≫ φ₀ = g :=
    Injective.comp_factorThru _ _
  refine ⟨Functor.whiskerLeft (Over.forget U).op φ₀.hom, ?_⟩
  change φ₀.hom.app (op U) x ≠ 0
  intro hzero
  let genQ := extensionByZeroUnitHomEquiv.{u, u, u, u} (underlyingRingSheaf O) U
    (cokernel (kernelSubobject s).arrow) π
  have hxq : (SheafOfModules.evaluation (underlyingRingSheaf O) (op U)).map q genQ = x := by
    rw [show genQ = extensionByZeroUnitHomEquiv.{u, u, u, u} (underlyingRingSheaf O) U
          (cokernel (kernelSubobject s).arrow) π from rfl,
      ← extensionByZeroUnitHomEquiv_naturality, hπq, hsx]
  have key : g.hom.app (op U) genQ = φ₀.hom.app (op U) x := by
    rw [← hfac, ← hxq]
    rfl
  have hgen : genQ = 0 := by
    refine sections_injective_of_mono g hgmono (op U) ?_
    rw [key, hzero]
    exact (map_zero _).symm
  refine hx ?_
  rw [← hxq, hgen]
  exact map_zero _

/-- **Sectionwise injectivity of the evaluation morphism.** A section killed by the
section-level evaluation map is zero. -/
theorem evaluation_injective (F : SheafOfModules.{u} (underlyingRingSheaf O)) (U : C)
    (x : F.val.obj (op U))
    (h : ((ev O (dualizingSheafOfRingedSite O) F).val.app (op U)) x = 0) :
    x = 0 := by
  by_contra hx
  obtain ⟨φ, hφ⟩ := exists_local_hom_ne_zero O F U x hx
  apply hφ
  rw [← ev_apply O (dualizingSheafOfRingedSite O) F U x φ, h]
  rfl

/-- For every sheaf of `O`-modules `F` on a ringed site the evaluation map `ev : F ⟶ (F^∨)^∨`
into the double dual is a monomorphism, the dual being taken against the dualizing sheaf of the
site. -/
@[stacks 01DS]
theorem evaluation_mono (F : SheafOfModules.{u} (underlyingRingSheaf O)) :
    Mono (ev O (dualizingSheafOfRingedSite O) F) := by
  rw [Preadditive.mono_iff_cancel_zero]
  intro Z g hg
  apply hom_zero_of_evaluation
  intro U
  ext z
  induction U with
  | op U =>
    refine evaluation_injective O F U _ ?_
    have hcomp : ((ev O (dualizingSheafOfRingedSite O) F).val.app (op U))
        (((SheafOfModules.evaluation (underlyingRingSheaf O) (op U)).map g) z)
        = ((SheafOfModules.evaluation (underlyingRingSheaf O) (op U)).map
            (g ≫ ev O (dualizingSheafOfRingedSite O) F)) z := by
      rw [Functor.map_comp]
      rfl
    rw [hcomp, hg]
    rfl

end RingedSite

end Stacks.Injectives.DualEvaluation

end
