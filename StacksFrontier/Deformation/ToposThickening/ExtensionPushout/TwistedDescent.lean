module

public import StacksFrontier.Deformation.ToposThickening.ExtensionPushout.SqZeroExt
public import StacksFrontier.Deformation.ToposThickening.ExtensionPushout.PushoutModule

/-!
# Pushout along a morphism of thickenings: the twisted module and its descent

The pushout `F'₂ ⊔_{K₂} K₁` is made a module over `T = O'₂ ⋉ I₁` by twisting the action of the
second thickened structure sheaf by `(a, m) ⊛ p := a · p - c₁(m ⊗ p̄)`. The kernel of
`q : T ⟶ O'₁` annihilates the twisted module, so it descends along `q` to an `O'₁`-module, which
gives the extension of `F` by `K₁` over the first thickening, with action map `c₁`.

See `StacksFrontier.Deformation.ToposThickening.ExtensionPushout` for the overview.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TensorProduct
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor)

universe v u w v₂ u₂ t

attribute [local implicit_reducible] SheafOfModules.unit PresheafOfModules.unit
  CategoryTheory.ConcreteCategory.hom CategoryTheory.sheafCompose SheafOfModules.forget
  SheafOfModules.restrictScalars PresheafOfModules.restrictScalars ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj' PresheafOfModules.restrictScalarsObj

attribute [local instance] PresheafOfModules.moduleMulOpposite
  PresheafOfModules.isCentralScalar_of_commRing

namespace Deformation.ToposThickening

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v₂, u₂, max v₂ u₂}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{max v₂ u₂})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{max v₂ u₂} RingCat.{max v₂ u₂})]

section PushoutExtension

variable [Y.J.WEqualsLocallyBijective AddCommGrpCat.{max v₂ u₂}]
  [HasSheafify Y.J AddCommGrpCat.{max v₂ u₂}]
  [HasWeakSheafify Y.J AddCommGrpCat.{max v₂ u₂}]

attribute [local instance] sectionsModuleOfCommRing

namespace MorphismOfFirstOrderThickenings

attribute [local instance] sectionsModuleOverTwo

variable {i : RingedToposHom X Y}

attribute [local instance] sectionsModuleOverSqZero sectionsModuleOfSqZeroExt

namespace PushoutExtensionData

variable {D : MorphismOfFirstOrderThickenings i} (dat : D.PushoutExtensionData)
  (E₂ : Abelian.YonedaExtension ((SheafOfModules.restrictScalars D.ringMap₂).obj dat.F)
    ((SheafOfModules.restrictScalars D.ringMap₂).obj dat.K₂) 0)

/-- The twisting term `c₁(m ⊗ p̄)`, read in the pushout: the correction by which the action of
the structure sheaf of the second thickening is modified to an action of `T = O'₂ ⋉ I₁`. -/
noncomputable def twist (U : Y.Cᵒᵖ) (m : D.first.I.val.obj U)
    (p : (dat.pushoutModule E₂).val.obj U) : (dat.pushoutModule E₂).val.obj U :=
  dat.inclSection E₂ U
    (dat.c₁.val.app U (dat.tensorMk U m (dat.quotSection E₂ U p)))

/-- The twisting term, as a function of the section of `F` the pushout section maps to. -/
lemma twist_eq (U : Y.Cᵒᵖ) (m : D.first.I.val.obj U)
    (p : (dat.pushoutModule E₂).val.obj U) :
    dat.twist E₂ U m p = dat.inclSection E₂ U
      (dat.c₁.val.app U (dat.tensorMk U m (dat.quotSection E₂ U p))) := rfl

/-- The twisting term is additive in the ideal section. -/
lemma twist_add_left (U : Y.Cᵒᵖ) (m m' : D.first.I.val.obj U)
    (p : (dat.pushoutModule E₂).val.obj U) :
    dat.twist E₂ U (m + m') p = dat.twist E₂ U m p + dat.twist E₂ U m' p := by
  simp only [dat.twist_eq]
  rw [dat.tensorMk_add_left, dat.c₁_add, dat.inclSection_add]

/-- The twisting term vanishes on the zero ideal section. -/
lemma twist_zero_left (U : Y.Cᵒᵖ) (p : (dat.pushoutModule E₂).val.obj U) :
    dat.twist E₂ U 0 p = 0 := by
  simp only [dat.twist_eq]
  rw [dat.tensorMk_zero_left, dat.c₁_zero, dat.inclSection_zero]

/-- The twisting term is additive in the pushout section. -/
lemma twist_add_right (U : Y.Cᵒᵖ) (m : D.first.I.val.obj U)
    (p p' : (dat.pushoutModule E₂).val.obj U) :
    dat.twist E₂ U m (p + p') = dat.twist E₂ U m p + dat.twist E₂ U m p' := by
  simp only [dat.twist_eq]
  rw [dat.quotSection_add, dat.tensorMk_add_right, dat.c₁_add, dat.inclSection_add]

/-- The twisting term respects differences of pushout sections. -/
lemma twist_sub_right (U : Y.Cᵒᵖ) (m : D.first.I.val.obj U)
    (p p' : (dat.pushoutModule E₂).val.obj U) :
    dat.twist E₂ U m (p - p') = dat.twist E₂ U m p - dat.twist E₂ U m p' := by
  simp only [dat.twist_eq]
  rw [dat.quotSection_sub, dat.tensorMk_sub_right, dat.c₁_sub, dat.inclSection_sub]

/-- The twisting term is linear in the ideal section over the structure sheaf of the second
thickening. -/
lemma twist_smul_left (U : Y.Cᵒᵖ) (a : D.O₂.obj.obj U) (m : D.first.I.val.obj U)
    (p : (dat.pushoutModule E₂).val.obj U) :
    dat.twist E₂ U (a • m) p = a • dat.twist E₂ U m p := by
  simp only [dat.twist_eq]
  rw [D.smul_overTwo_eq D.first.I, dat.tensorMk_smul_left, dat.c₁_smul, dat.inclSection_smul]

/-- Moving a scalar from the pushout section to the ideal section leaves the twisting term
unchanged. -/
lemma twist_smul_right (U : Y.Cᵒᵖ) (a : D.O₂.obj.obj U) (m : D.first.I.val.obj U)
    (p : (dat.pushoutModule E₂).val.obj U) :
    dat.twist E₂ U m (a • p) = a • dat.twist E₂ U m p := by
  simp only [dat.twist_eq]
  rw [dat.quotSection_smul, dat.tensorMk_smul_right, dat.c₁_smul, dat.inclSection_smul]

/-- The twisting term vanishes on sections coming from the new kernel module. -/
private lemma twist_inclSection_aux (U : Y.Cᵒᵖ) (m : D.first.I.val.obj U)
    (k : dat.K₁.val.obj U) : dat.twist E₂ U m (dat.inclSection E₂ U k) = 0 := by
  simp only [dat.twist_eq]
  rw [dat.quotSection_inclSection, dat.tensorMk_zero_right, dat.c₁_zero, dat.inclSection_zero]

/-- The twisting term is itself killed by twisting, because the new kernel module is carried to
zero in `F`. This is the square-zero condition making the twisted action associative. -/
lemma twist_twist (U : Y.Cᵒᵖ) (m m' : D.first.I.val.obj U)
    (p : (dat.pushoutModule E₂).val.obj U) :
    dat.twist E₂ U m (dat.twist E₂ U m' p) = 0 :=
  dat.twist_inclSection_aux E₂ U m _

/-- The twisting term commutes with restriction. -/
lemma twist_restrict {U V : Y.Cᵒᵖ} (g : U ⟶ V) (m : D.first.I.val.obj U)
    (p : (dat.pushoutModule E₂).val.obj U) :
    (dat.pushoutModule E₂).val.map g (dat.twist E₂ U m p) =
      dat.twist E₂ V (D.idealRestrict g m) ((dat.pushoutModule E₂).val.map g p) := by
  simp only [dat.twist_eq]
  rw [dat.quotSection_restrict, D.idealRestrict_eq, ← dat.tensorMk_restrict, dat.c₁_restrict,
    dat.inclSection_restrict]

/-- The twisted action of a local section of `T = O'₂ ⋉ I₁` on a local section of the pushout:
the action of the ring component, corrected by the twisting term of the ideal component. -/
noncomputable def twistedSmul (U : Y.Cᵒᵖ) (s : D.sqZeroSections U)
    (p : (dat.pushoutModule E₂).val.obj U) : (dat.pushoutModule E₂).val.obj U :=
  D.sqZeroFst s • p - dat.twist E₂ U (D.sqZeroSnd s) p

/-- The twisted action, unfolded. -/
lemma twistedSmul_eq (U : Y.Cᵒᵖ) (s : D.sqZeroSections U)
    (p : (dat.pushoutModule E₂).val.obj U) :
    dat.twistedSmul E₂ U s p = D.sqZeroFst s • p - dat.twist E₂ U (D.sqZeroSnd s) p := rfl

/-- The twisted action is additive in the pushout section. -/
lemma twistedSmul_add_right (U : Y.Cᵒᵖ) (s : D.sqZeroSections U)
    (p p' : (dat.pushoutModule E₂).val.obj U) :
    dat.twistedSmul E₂ U s (p + p') =
      dat.twistedSmul E₂ U s p + dat.twistedSmul E₂ U s p' := by
  simp only [dat.twistedSmul_eq]
  rw [smul_add, dat.twist_add_right]
  abel

/-- The twisted action is additive in the section of `T`. -/
lemma twistedSmul_add_left (U : Y.Cᵒᵖ) (s s' : D.sqZeroSections U)
    (p : (dat.pushoutModule E₂).val.obj U) :
    dat.twistedSmul E₂ U (s + s') p =
      dat.twistedSmul E₂ U s p + dat.twistedSmul E₂ U s' p := by
  simp only [dat.twistedSmul_eq, D.sqZeroFst_add, D.sqZeroSnd_add]
  rw [add_smul, dat.twist_add_left]
  abel

/-- The twisted action is associative. This is the Leibniz rule for the ideal component of a
product in `T` together with the vanishing of the twisting term on the new kernel module. -/
lemma twistedSmul_mul (U : Y.Cᵒᵖ) (s s' : D.sqZeroSections U)
    (p : (dat.pushoutModule E₂).val.obj U) :
    dat.twistedSmul E₂ U (s * s') p =
      dat.twistedSmul E₂ U s (dat.twistedSmul E₂ U s' p) := by
  simp only [dat.twistedSmul_eq, D.sqZeroFst_mul, D.sqZeroSnd_mul]
  rw [mul_smul, dat.twist_add_left, dat.twist_smul_left, dat.twist_smul_left, smul_sub,
    dat.twist_sub_right, dat.twist_twist, sub_zero, dat.twist_smul_right]
  abel

/-- The unit of `T` acts as the identity. -/
lemma twistedSmul_one (U : Y.Cᵒᵖ) (p : (dat.pushoutModule E₂).val.obj U) :
    dat.twistedSmul E₂ U 1 p = p := by
  simp only [dat.twistedSmul_eq, D.sqZeroFst_one, D.sqZeroSnd_one]
  rw [one_smul, dat.twist_zero_left, sub_zero]

/-- The twisted action makes the local sections of the pushout a module over the local sections
of `T = O'₂ ⋉ I₁`. -/
@[instance_reducible]
noncomputable def twistedModule (U : Y.Cᵒᵖ) :
    Module (D.sqZeroSections U) ((dat.pushoutModule E₂).val.obj U) :=
  moduleOfAxioms (dat.twistedSmul E₂ U) (dat.twistedSmul_add_right E₂ U)
    (dat.twistedSmul_add_left E₂ U) (dat.twistedSmul_mul E₂ U) (dat.twistedSmul_one E₂ U)

/-- The twisted action is semilinear for restriction. -/
lemma twistedSmul_restrict {U V : Y.Cᵒᵖ} (g : U ⟶ V) (s : D.sqZeroSections U)
    (p : (dat.pushoutModule E₂).val.obj U) :
    (dat.pushoutModule E₂).val.map g (dat.twistedSmul E₂ U s p) =
      dat.twistedSmul E₂ V ((D.sqZeroRestrict g).hom s)
        ((dat.pushoutModule E₂).val.map g p) :=
  have h₁ : (dat.pushoutModule E₂).val.map g
        (D.sqZeroFst s • p - dat.twist E₂ U (D.sqZeroSnd s) p) =
      (dat.pushoutModule E₂).val.map g (D.sqZeroFst s • p) -
        (dat.pushoutModule E₂).val.map g (dat.twist E₂ U (D.sqZeroSnd s) p) :=
    map_sub ((dat.pushoutModule E₂).val.map g).hom _ _
  have h₂ := (dat.pushoutModule E₂).val.map_smul g (D.sqZeroFst s) p
  have h₃ := dat.twist_restrict E₂ g (D.sqZeroSnd s) p
  h₁.trans
    ((congrArg (fun t => (dat.pushoutModule E₂).val.map g (D.sqZeroFst s • p) - t) h₃).trans
      (congrArg (fun t => t - dat.twist E₂ V (D.idealRestrict g (D.sqZeroSnd s))
        ((dat.pushoutModule E₂).val.map g p)) h₂))

/-- The pushout with its twisted action, as a presheaf of modules over `T = O'₂ ⋉ I₁`. -/
noncomputable def twistedPresheaf : PresheafOfModules.{max v₂ u₂} D.sqZeroPresheaf :=
  letI _inst : ∀ U : Y.Cᵒᵖ, Module (D.sqZeroPresheaf.obj U)
      ((dat.pushoutModule E₂).val.presheaf.obj U) := dat.twistedModule E₂
  PresheafOfModules.ofPresheaf (dat.pushoutModule E₂).val.presheaf
    (fun {_ _} g s p => dat.twistedSmul_restrict E₂ g s p)

/-- The pushout with its twisted action, as a sheaf of modules over `T = O'₂ ⋉ I₁`. -/
noncomputable def twistedSheaf : SheafOfModules.{max v₂ u₂} D.sqZeroExt where
  val := dat.twistedPresheaf E₂
  isSheaf := (dat.pushoutModule E₂).isSheaf

/-- Multiplication of a local section of the pushout by a section of the defining ideal of the
second thickening is the twisting term at the image of that section under the induced map of
defining ideals. This is what makes the kernel of `q` annihilate the twisted action. -/
lemma inclTwo_smul_eq (hE₂ : (extensionActionMap D.second E₂).1 = dat.c₂)
    (U : Y.Cᵒᵖ) (b : D.second.I.val.obj U) (p : (dat.pushoutModule E₂).val.obj U) :
    D.inclTwo U b • p = dat.twist E₂ U (D.idealMap.val.app U b) p := by
  have hspec := (extensionActionMap D.second (dat.pushoutExtension E₂)).2 U b p
  rw [dat.pushoutExtension_actionMap E₂ hE₂] at hspec
  exact hspec.symm.trans
    (congrArg (dat.inclSection E₂ U) (dat.comm U b (dat.quotSection E₂ U p)))

/-- The twisting term is odd in the ideal section. -/
lemma twist_neg_left (U : Y.Cᵒᵖ) (m : D.first.I.val.obj U)
    (p : (dat.pushoutModule E₂).val.obj U) :
    dat.twist E₂ U (-m) p = -dat.twist E₂ U m p := by
  have h := dat.twist_add_left E₂ U m (-m) p
  rw [add_neg_cancel, dat.twist_zero_left] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

/-- The twisting term vanishes on sections coming from the new kernel module. -/
lemma twist_inclSection (U : Y.Cᵒᵖ) (m : D.first.I.val.obj U) (k : dat.K₁.val.obj U) :
    dat.twist E₂ U m (dat.inclSection E₂ U k) = 0 :=
  dat.twist_inclSection_aux E₂ U m k

/-- The twisting term is killed by the quotient map onto `F`. -/
lemma quotSection_twist (U : Y.Cᵒᵖ) (m : D.first.I.val.obj U)
    (p : (dat.pushoutModule E₂).val.obj U) :
    dat.quotSection E₂ U (dat.twist E₂ U m p) = 0 := by
  simp only [dat.twist_eq]
  exact dat.quotSection_inclSection E₂ U _

/-- The inclusion of the new kernel module into the pushout is linear for the twisted action. -/
lemma inclSection_smul_sqZero (U : Y.Cᵒᵖ) (r : D.sqZeroSections U) (k : dat.K₁.val.obj U) :
    dat.inclSection E₂ U
        ((structureRingMap i).hom.app U (D.sqZeroProj.hom.app U r) • k) =
      dat.twistedSmul E₂ U r (dat.inclSection E₂ U k) := by
  rw [D.structureRingMap_sqZeroProj]
  refine (dat.inclSection_smul E₂ U _ k).trans ?_
  rw [dat.twistedSmul_eq, dat.twist_inclSection, sub_zero]

/-- The quotient map from the pushout onto `F` is linear for the twisted action. -/
lemma quotSection_smul_sqZero (U : Y.Cᵒᵖ) (r : D.sqZeroSections U)
    (p : (dat.pushoutModule E₂).val.obj U) :
    dat.quotSection E₂ U (dat.twistedSmul E₂ U r p) =
      (structureRingMap i).hom.app U (D.sqZeroProj.hom.app U r) • dat.quotSection E₂ U p := by
  rw [D.structureRingMap_sqZeroProj, dat.twistedSmul_eq, dat.quotSection_sub,
    dat.quotSection_smul, dat.quotSection_twist, sub_zero]
  rfl

/-- The inclusion of the new kernel module into the pushout, as a map of `T`-modules. -/
noncomputable def twistedIncl :
    (SheafOfModules.restrictScalars D.sqZeroProj).obj
        ((SheafOfModules.restrictScalars (structureRingMap i)).obj dat.K₁) ⟶
      dat.twistedSheaf E₂ :=
  ⟨PresheafOfModules.homMk
    ((PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf D.O₂).obj).map
      (dat.pushoutIncl E₂).val)
    (fun U r k => dat.inclSection_smul_sqZero E₂ U r k)⟩

/-- The quotient map from the pushout onto `F`, as a map of `T`-modules. -/
noncomputable def twistedQuot :
    dat.twistedSheaf E₂ ⟶
      (SheafOfModules.restrictScalars D.sqZeroProj).obj
        ((SheafOfModules.restrictScalars (structureRingMap i)).obj dat.F) :=
  ⟨PresheafOfModules.homMk
    ((PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf D.O₂).obj).map
      (dat.pushoutQuot E₂).val)
    (fun U r p => dat.quotSection_smul_sqZero E₂ U r p)⟩

/-- The two maps of `T`-modules compose to zero. -/
lemma twistedIncl_twistedQuot : dat.twistedIncl E₂ ≫ dat.twistedQuot E₂ = 0 := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro k
  exact dat.quotSection_inclSection E₂ U k

/-- The pushout sequence, read as a sequence of `T`-modules, is short exact: short exactness is
a property of the underlying sequence of abelian sheaves, which the twisting does not change. -/
lemma twisted_shortExact :
    (ShortComplex.mk (dat.twistedIncl E₂) (dat.twistedQuot E₂)
      (dat.twistedIncl_twistedQuot E₂)).ShortExact := by
  apply ShortExact.reflects_shortExact_of_faithful (SheafOfModules.toSheaf D.sqZeroExt)
  change ((ShortComplex.mk (dat.pushoutIncl E₂) (dat.pushoutQuot E₂)
    (dat.pushoutIncl_quot E₂)).map
      (SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf D.O₂))).ShortExact
  exact (dat.pushout_shortExact E₂).map_of_exact
    (SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf D.O₂))

/-- The kernel of `q` annihilates the twisted action: a section of `T` killed by `q` has ring
component a section of the defining ideal of the second thickening and ideal component its
image under the induced map of defining ideals, and multiplication by such a ring component is
exactly the twisting term by such an ideal component. -/
lemma twistedSmul_eq_zero (hE₂ : (extensionActionMap D.second E₂).1 = dat.c₂)
    (U : Y.Cᵒᵖ) (s : D.sqZeroSections U) (hs : D.sqZeroProj.hom.app U s = 0)
    (p : (dat.pushoutModule E₂).val.obj U) : dat.twistedSmul E₂ U s p = 0 := by
  obtain ⟨b, hb, hm⟩ := D.exists_ideal_of_sqZeroProj_eq_zero U s hs
  have hfst : D.sqZeroFst s • p = dat.twist E₂ U (D.sqZeroSnd s) p :=
    (congrArg (fun a : (Stacks.SheafOfModules.Tensor.ringSheaf D.O₂).obj.obj U => a • p)
        hb.symm).trans
      ((dat.inclTwo_smul_eq E₂ hE₂ U b p).trans (congrArg (fun m => dat.twist E₂ U m p) hm))
  change D.sqZeroFst s • p - dat.twist E₂ U (D.sqZeroSnd s) p = 0
  exact sub_eq_zero.2 hfst

/-- The `O'₁`-module structure on the pushout `F'₂ ⊔_{K₂} K₁`: the twisted `T`-module descends
along the locally surjective `q : T ⟶ O'₁`, whose kernel annihilates it. This is the step the
source omits. -/
noncomputable def descendedModule (hE₂ : (extensionActionMap D.second E₂).1 = dat.c₂) :
    Σ N : SheafOfModules.{max v₂ u₂} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O),
      (SheafOfModules.restrictScalars D.sqZeroProj).obj N ≅ dat.twistedSheaf E₂ :=
  letI : Presheaf.IsLocallySurjective Y.J D.sqZeroProj.hom := D.sqZeroProj_locallySurjective
  descendModule D.sqZeroProj (dat.twistedSheaf E₂)
    (fun U s hs p => dat.twistedSmul_eq_zero E₂ hE₂ U s hs p)

/-- The twisted action of the section of `T` with zero ring component and ideal component `-m`
is the twisting term by `m`. -/
lemma twistedSmul_mk_zero_neg (U : Y.Cᵒᵖ) (m : D.first.I.val.obj U)
    (p : (dat.pushoutModule E₂).val.obj U) :
    dat.twistedSmul E₂ U (D.sqZeroMk 0 (-m)) p = dat.twist E₂ U m p := by
  rw [dat.twistedSmul_eq, D.sqZeroFst_mk, D.sqZeroSnd_mk, zero_smul, dat.twist_neg_left,
    sub_neg_eq_add, zero_add]

variable (hE₂ : (extensionActionMap D.second E₂).1 = dat.c₂)

/-- The middle term of the extension over the first thickening: the pushout `F'₂ ⊔_{K₂} K₁`
with the `O'₁`-module structure descended along `q`. -/
noncomputable def middle :
    SheafOfModules.{max v₂ u₂} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) :=
  (dat.descendedModule E₂ hE₂).1

/-- Restricting the middle term along `q` gives back the pushout with its twisted action. -/
noncomputable def middleIso :
    (SheafOfModules.restrictScalars D.sqZeroProj).obj (dat.middle E₂ hE₂) ≅
      dat.twistedSheaf E₂ :=
  (dat.descendedModule E₂ hE₂).2

/-- The inclusion of the new kernel module into the middle term, over the first thickening. -/
noncomputable def extInclOne :
    (SheafOfModules.restrictScalars (structureRingMap i)).obj dat.K₁ ⟶ dat.middle E₂ hE₂ :=
  D.sqZeroRestrictFullyFaithful.preimage
    (dat.twistedIncl E₂ ≫ (dat.middleIso E₂ hE₂).inv)

/-- The quotient map from the middle term onto `F`, over the first thickening. -/
noncomputable def extQuotOne :
    dat.middle E₂ hE₂ ⟶ (SheafOfModules.restrictScalars (structureRingMap i)).obj dat.F :=
  D.sqZeroRestrictFullyFaithful.preimage
    ((dat.middleIso E₂ hE₂).hom ≫ dat.twistedQuot E₂)

/-- The inclusion of the new kernel module is the pushout inclusion, after restricting scalars
along `q` and comparing with the pushout. -/
lemma restrictScalars_extInclOne :
    (SheafOfModules.restrictScalars D.sqZeroProj).map (dat.extInclOne E₂ hE₂) =
      dat.twistedIncl E₂ ≫ (dat.middleIso E₂ hE₂).inv :=
  D.sqZeroRestrictFullyFaithful.map_preimage _

/-- The quotient map onto `F` is the pushout quotient map, after restricting scalars along `q`
and comparing with the pushout. -/
lemma restrictScalars_extQuotOne :
    (SheafOfModules.restrictScalars D.sqZeroProj).map (dat.extQuotOne E₂ hE₂) =
      (dat.middleIso E₂ hE₂).hom ≫ dat.twistedQuot E₂ :=
  D.sqZeroRestrictFullyFaithful.map_preimage _

/-- The two maps over the first thickening compose to zero. -/
lemma extInclOne_extQuotOne : dat.extInclOne E₂ hE₂ ≫ dat.extQuotOne E₂ hE₂ = 0 := by
  apply D.sqZeroRestrictFullyFaithful.map_injective
  rw [Functor.map_comp, dat.restrictScalars_extInclOne E₂ hE₂,
    dat.restrictScalars_extQuotOne E₂ hE₂, Functor.map_zero, Category.assoc,
    Iso.inv_hom_id_assoc, dat.twistedIncl_twistedQuot]

/-- The sequence `0 → K₁ → F'₂ ⊔_{K₂} K₁ → F → 0` is short exact over the first thickening:
restriction of scalars along the locally surjective `q` is fully faithful, hence reflects short
exactness. -/
lemma extOne_shortExact :
    (ShortComplex.mk (dat.extInclOne E₂ hE₂) (dat.extQuotOne E₂ hE₂)
      (dat.extInclOne_extQuotOne E₂ hE₂)).ShortExact := by
  apply shortExact_of_fullyFaithful_map (SheafOfModules.restrictScalars D.sqZeroProj)
    D.sqZeroRestrictFullyFaithful
  have ha := dat.restrictScalars_extInclOne E₂ hE₂
  have hb := dat.restrictScalars_extQuotOne E₂ hE₂
  let eS : (ShortComplex.mk (dat.extInclOne E₂ hE₂) (dat.extQuotOne E₂ hE₂)
        (dat.extInclOne_extQuotOne E₂ hE₂)).map
        (SheafOfModules.restrictScalars D.sqZeroProj) ≅
      ShortComplex.mk (dat.twistedIncl E₂) (dat.twistedQuot E₂)
        (dat.twistedIncl_twistedQuot E₂) :=
    ShortComplex.isoMk (Iso.refl _) (dat.middleIso E₂ hE₂) (Iso.refl _)
      (by simp only [ShortComplex.map_f, Iso.refl_hom, Category.id_comp, ha,
            Category.assoc, Iso.inv_hom_id, Category.comp_id])
      (by simp only [ShortComplex.map_g, Iso.refl_hom, Category.comp_id, hb])
  exact ShortComplex.shortExact_of_iso eS.symm (dat.twisted_shortExact E₂)

/-- **Stacks Project, Tag 08MJ.** The extension over the first thickening produced from an
extension over the second: the pushout `F'₂ ⊔_{K₂} K₁` carries an `O'₁`-module structure, built
by descending the action of `T = O'₂ ⋉ I₁` twisted by `c₁` along the locally surjective
`q : T ⟶ O'₁`, and sits in a short exact sequence `0 → K₁ → F'₂ ⊔_{K₂} K₁ → F → 0` of
`O'₁`-modules. Its middle term restricted along `q` is identified with the pushout by
`middleIso`, compatibly with the two maps by `restrictScalars_extInclOne` and
`restrictScalars_extQuotOne`. -/
@[stacks 08MJ "the canonical map on extensions, by pushout along the map of kernel modules"]
noncomputable def extensionOne :
    Abelian.YonedaExtension
      ((SheafOfModules.restrictScalars (structureRingMap i)).obj dat.F)
      ((SheafOfModules.restrictScalars (structureRingMap i)).obj dat.K₁) 0 where
  Z := ComposableArrows.mk₀ (dat.middle E₂ hE₂)
  f := dat.extInclOne E₂ hE₂
  g := dat.extQuotOne E₂ hE₂
  mono_f := (dat.extOne_shortExact E₂ hE₂).mono_f
  exact := ComposableArrows.exact₁ _
  exact_g := (dat.extOne_shortExact E₂ hE₂).exact.exact_toComposableArrows
  epi_g := (dat.extOne_shortExact E₂ hE₂).epi_g

/-- The inclusion of the new kernel module, on local sections. -/
lemma extInclOne_app (U : Y.Cᵒᵖ) (k : dat.K₁.val.obj U) :
    (dat.extInclOne E₂ hE₂).val.app U k =
      (dat.middleIso E₂ hE₂).inv.val.app U (dat.inclSection E₂ U k) :=
  congrArg (fun z : (SheafOfModules.restrictScalars D.sqZeroProj).obj
      ((SheafOfModules.restrictScalars (structureRingMap i)).obj dat.K₁) ⟶
        (SheafOfModules.restrictScalars D.sqZeroProj).obj (dat.middle E₂ hE₂) =>
    z.val.app U k) (dat.restrictScalars_extInclOne E₂ hE₂)

/-- The quotient map onto `F`, on local sections. -/
lemma extQuotOne_app (U : Y.Cᵒᵖ) (x : (dat.middle E₂ hE₂).val.obj U) :
    (dat.extQuotOne E₂ hE₂).val.app U x =
      dat.quotSection E₂ U ((dat.middleIso E₂ hE₂).hom.val.app U x) :=
  congrArg (fun z : (SheafOfModules.restrictScalars D.sqZeroProj).obj (dat.middle E₂ hE₂) ⟶
      (SheafOfModules.restrictScalars D.sqZeroProj).obj
        ((SheafOfModules.restrictScalars (structureRingMap i)).obj dat.F) =>
    z.val.app U x) (dat.restrictScalars_extQuotOne E₂ hE₂)

/-- The comparison with the pushout is bijective on local sections. -/
lemma middleIso_inv_hom (U : Y.Cᵒᵖ) (x : (dat.middle E₂ hE₂).val.obj U) :
    (dat.middleIso E₂ hE₂).inv.val.app U ((dat.middleIso E₂ hE₂).hom.val.app U x) = x :=
  congrArg (fun z : (SheafOfModules.restrictScalars D.sqZeroProj).obj (dat.middle E₂ hE₂) ⟶
      (SheafOfModules.restrictScalars D.sqZeroProj).obj (dat.middle E₂ hE₂) =>
    z.val.app U x) (dat.middleIso E₂ hE₂).hom_inv_id

/-- Multiplication on the middle term by a section of the defining ideal of the first
thickening corresponds, under the comparison with the pushout, to the twisting term. -/
lemma middleIso_hom_inclOne_smul (U : Y.Cᵒᵖ) (m : D.first.I.val.obj U)
    (x : (dat.middle E₂ hE₂).val.obj U) :
    (dat.middleIso E₂ hE₂).hom.val.app U (D.inclOne U m • x) =
      dat.twist E₂ U m ((dat.middleIso E₂ hE₂).hom.val.app U x) := by
  refine Eq.trans ?_ (Eq.trans (map_smul ((dat.middleIso E₂ hE₂).hom.val.app U).hom
    (D.sqZeroMk 0 (-m)) x) ?_)
  · exact congrArg (fun z : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U =>
      (dat.middleIso E₂ hE₂).hom.val.app U (z • x)) (D.sqZeroProj_mk_zero_neg U m).symm
  · exact dat.twistedSmul_mk_zero_neg E₂ U m _

/-- The extension over the first thickening satisfies the characterizing local formula of the
canonical action map for `c₁`: multiplication by a section of `I₁` on the middle term is the
twisting term, which is exactly `c₁` composed with the inclusion of `K₁`. -/
lemma extensionOne_actionMap_spec (U : Y.Cᵒᵖ) (m : D.first.I.val.obj U)
    (x : (dat.extensionOne E₂ hE₂).Z.left.val.obj U) :
    (dat.extensionOne E₂ hE₂).f.val.app U
        (dat.c₁.val.app U
          (((PresheafOfModules.sheafificationAdjunction
            (R := Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i))
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i)).obj)).unit.app
            (PresheafOfModules.tensorObj D.first.I.val dat.F.val)).app U
            (m ⊗ₜ[(baseRing i).obj.obj U]
              (dat.extensionOne E₂ hE₂).g.val.app U x))) =
      D.inclOne U m • x := by
  have h₁ : (dat.extQuotOne E₂ hE₂).val.app U x =
      dat.quotSection E₂ U ((dat.middleIso E₂ hE₂).hom.val.app U x) :=
    dat.extQuotOne_app E₂ hE₂ U x
  have h₂ : (dat.extInclOne E₂ hE₂).val.app U
        (dat.c₁.val.app U (dat.tensorMk U m
          (dat.quotSection E₂ U ((dat.middleIso E₂ hE₂).hom.val.app U x)))) =
      (dat.middleIso E₂ hE₂).inv.val.app U
        (dat.twist E₂ U m ((dat.middleIso E₂ hE₂).hom.val.app U x)) :=
    dat.extInclOne_app E₂ hE₂ U _
  exact (congrArg (fun y : dat.F.val.obj U => (dat.extInclOne E₂ hE₂).val.app U
        (dat.c₁.val.app U (dat.tensorMk U m y))) h₁).trans
    (h₂.trans ((congrArg (fun z => (dat.middleIso E₂ hE₂).inv.val.app U z)
        (dat.middleIso_hom_inclOne_smul E₂ hE₂ U m x).symm).trans
      (dat.middleIso_inv_hom E₂ hE₂ U (D.inclOne U m • x))))

/-- **Stacks Project, Tag 08MJ.** The canonical action map of the extension produced over the
first thickening is the prescribed `c₁`. -/
@[stacks 08MJ "the action map of the pushed-out extension is c₁"]
theorem extensionOne_actionMap :
    (extensionActionMap D.first (dat.extensionOne E₂ hE₂)).1 = dat.c₁ :=
  extensionActionMap_unique D.first (dat.extensionOne E₂ hE₂) dat.c₁
    (dat.extensionOne_actionMap_spec E₂ hE₂)

end PushoutExtensionData

end MorphismOfFirstOrderThickenings

end PushoutExtension

end Deformation.ToposThickening

end
