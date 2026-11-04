module

public import StacksFrontier.AlgebraicGeometry.Reflexive.DoubleDual
public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.LocalHom
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Reflexivity of a coherent module on a scheme is reflexivity of its stalks

Let `F` be a sheaf of modules on a scheme `X`.  Its dual `F^∨ = SheafHom(F, 𝒪_X)` is the
internal hom into the structure sheaf, and `F` is reflexive when the canonical map
`F ⟶ F^∨∨` of `StacksFrontier.AlgebraicGeometry.Reflexive.DoubleDual` is an isomorphism.
This file compares that global condition with the algebraic reflexivity of the stalks.

The comparison rests on [Stacks, Tag 01CP]: for `F` of finite presentation the canonical map
from the stalk of an internal hom to the module of maps of stalks is an isomorphism.  Applying
it to `F^∨` identifies `(F^∨)_x` with the `𝒪_{X,x}`-linear dual of `F_x`
(`dualStalkEquiv`), and applying it again to `F^∨∨` identifies `(F^∨∨)_x` with the dual of
`(F^∨)_x`.  Under these identifications the stalk of the canonical map `F ⟶ F^∨∨` becomes the
algebraic evaluation map `F_x ⟶ (F_x)^∨∨`, which is the content of
`dualStalkEquiv_eq_dualStalkEquiv_toDoubleDual`: both sides send a pair of germs to the germ of
the value of the functional.  Reflexivity of `F` therefore makes the algebraic evaluation map
bijective.

This is the implication (1) ⇒ (2) of [Stacks, Tag 0AY3], and it is the step through which
[Stacks, Tag 0EBI] and [Stacks, Tag 0AY4] reduce to the algebraic theory of reflexive modules
in `StacksFrontier.Algebra.Module.Reflexive`.

## Main definitions

* `dualSheafHom F` — the dual `F^∨`, packaged as a `Stacks.SheafOfModules.SheafHom` so that the
  stalk comparison of Tag 01CP applies to it.  Its underlying module is `dualSheaf F` on the
  nose.
* `dualStalkEquiv F x` — the stalk of `F^∨` at `x` is the `𝒪_{X,x}`-linear dual of `F_x`.
* `stalkMapOfHom f x` — the map induced on stalks by a morphism of modules on a scheme.

## Main results

* `dualStalkEquiv_germ` — the germ formula pinning down `dualStalkEquiv`.
* `isReflexive_stalk_of_isReflexive` — a reflexive module of finite presentation whose dual is
  also of finite presentation has reflexive stalks.

## Implementation notes

`isReflexive_stalk_of_isReflexive` carries the hypothesis `[(dualSheaf F).IsFinitePresentation]`
in addition to `[F.IsFinitePresentation]`.  Over a locally Noetherian scheme and for `F`
coherent this is automatic — it is coherence of the internal hom, [Stacks, Tag 01Y2], which
rests on [Stacks, Tag 01CQ].

**01CQ is proved.**  Both of its clauses are formalized and tagged in
`StacksFrontier/AlgebraicGeometry/InternalHomCoherent/LocalKernel.lean`, and the discharge is
packaged as
`Stacks.AlgebraicGeometry.ReflexiveModules.isFinitePresentation_dualSheaf`
(`ExtensionChain/Depth.lean`), which is 01Y2 for the dual.  That is what makes 0EBI's two parts
unconditional.

The hypothesis is nonetheless kept here, deliberately, and dropping it would be a loss.
`isReflexive_stalk_of_isReflexive` is stated for an **arbitrary** scheme with only the two
finite-presentation hypotheses — no integrality, no Noetherian hypothesis, no coherence —
whereas the discharge needs a coherent structure sheaf, i.e. `[IsLocallyNoetherian X]`.  So
narrowing this statement to 0AY3's own hypotheses in order to remove the binder would trade a
theorem that holds on any scheme for one that holds only on locally Noetherian schemes, and it
would still earn no tag (see below).  Anyone wanting the unconditional form at 0AY3's
generality should add a corollary alongside, not narrow this.

**No `@[stacks 0AY3]` attribute is placed.** Tag 0AY3 is a three-way equivalence; only
(1) ⇒ (2) is proved here, and only under the extra finite-presentation hypothesis on the dual.

The identification of the stalk of the structure sheaf — read as the unit module, so that it is
the target of the internal hom — with the stalk of `𝒪_X` as a ring is
`structStalkLinearEquiv`; it is built from the comparison of a filtered colimit in
`CommRingCat` with the same colimit in `AddCommGrpCat`, and `structStalkLinearEquiv_germ` says
it is the identity on germs.

## References

* [Stacks Project, Tag 0AVU](https://stacks.math.columbia.edu/tag/0AVU)
* [Stacks Project, Tag 0AY3](https://stacks.math.columbia.edu/tag/0AY3)
* [Stacks Project, Tag 01CP](https://stacks.math.columbia.edu/tag/01CP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open Stacks.AlgebraicGeometry.ReflexiveModules
open Stacks.SheafOfModules.SheafHomStalk

universe u

namespace Stacks.AlgebraicGeometry.ReflexiveModules

/-! ### The stalk of the structure sheaf as a module over itself -/

/-- The unit module of a presheaf of commutative rings, as a presheaf of modules. -/
public abbrev unitModulePresheaf {Y : TopCat.{u}} (R : Y.Presheaf CommRingCat.{u}) :
    PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat) :=
  PresheafOfModules.unit (R ⋙ forget₂ CommRingCat RingCat)

/-- The stalk of the unit module of `R` is the stalk of `R`, as abelian groups. -/
public def unitModuleStalkAddEquiv {Y : TopCat.{u}} (R : Y.Presheaf CommRingCat.{u}) (y : Y) :
    TopCat.Presheaf.stalk (C := Ab.{u}) (unitModulePresheaf R).presheaf y ≃+ R.stalk y :=
  (preservesColimitIso
    (forget₂ CommRingCat.{u} RingCat.{u} ⋙ forget₂ RingCat.{u} AddCommGrpCat.{u})
    ((TopologicalSpace.OpenNhds.inclusion y).op ⋙ R)).symm.addCommGroupIsoToAddEquiv

/-- The comparison of stalks of the unit module sends a germ to the corresponding germ. -/
public lemma unitModuleStalkAddEquiv_germ {Y : TopCat.{u}} (R : Y.Presheaf CommRingCat.{u}) (y : Y)
    (U : Opens Y) (hy : y ∈ U) (r : R.obj (.op U)) :
    unitModuleStalkAddEquiv R y (TopCat.Presheaf.germ (unitModulePresheaf R).presheaf U y hy r)
      = R.germ U y hy r :=
  congrArg (fun f : AddCommGrpCat.of (R.obj (.op U)) ⟶ AddCommGrpCat.of (R.stalk y) ↦ f r)
    (ι_preservesColimitIso_inv
      (forget₂ CommRingCat.{u} RingCat.{u} ⋙ forget₂ RingCat.{u} AddCommGrpCat.{u})
      ((TopologicalSpace.OpenNhds.inclusion y).op ⋙ R) (.op ⟨U, hy⟩))

/-- The comparison of stalks of the unit module is linear on germs. -/
public lemma unitModuleStalkAddEquiv_germ_smul {Y : TopCat.{u}} (R : Y.Presheaf CommRingCat.{u})
    (y : Y) (U : Opens Y) (hy : y ∈ U) (r s : R.obj (.op U)) :
    unitModuleStalkAddEquiv R y
        (TopCat.Presheaf.germ (unitModulePresheaf R).presheaf U y hy
          (r • (s : ((unitModulePresheaf R).obj (.op U)))))
      = R.germ U y hy r • unitModuleStalkAddEquiv R y
          (TopCat.Presheaf.germ (unitModulePresheaf R).presheaf U y hy s) := by
  rw [unitModuleStalkAddEquiv_germ,
    show (r • (s : ((unitModulePresheaf R).obj (.op U))) : ((unitModulePresheaf R).obj (.op U)))
      = ((r * s : R.obj (.op U)) : ((unitModulePresheaf R).obj (.op U))) from rfl,
    unitModuleStalkAddEquiv_germ]
  exact map_mul (R.germ U y hy).hom r s

/-- The stalk of the unit module of `R` at `y` is `R_y`, as an `R_y`-module. -/
public def unitModuleStalkLinearEquiv {Y : TopCat.{u}} (R : Y.Presheaf CommRingCat.{u}) (y : Y) :
    TopCat.Presheaf.stalk (C := Ab.{u}) (unitModulePresheaf R).presheaf y ≃ₗ[R.stalk y]
      R.stalk y := by
  refine { unitModuleStalkAddEquiv R y with map_smul' := ?_ }
  intro r m
  change unitModuleStalkAddEquiv R y (r • m) = r • unitModuleStalkAddEquiv R y m
  obtain ⟨U, hyU, a, rfl⟩ := R.exists_germ_eq r
  obtain ⟨V, hyV, b, rfl⟩ := TopCat.Presheaf.exists_germ_eq (unitModulePresheaf R).presheaf m
  have hyUV : y ∈ U ⊓ V := ⟨hyU, hyV⟩
  have h1 : U ⊓ V ≤ U := inf_le_left
  have h2 : U ⊓ V ≤ V := inf_le_right
  rw [← R.germ_res_apply (homOfLE h1) y hyUV a,
    ← TopCat.Presheaf.germ_res_apply (unitModulePresheaf R).presheaf (homOfLE h2) y hyUV b,
    ← PresheafOfModules.germ_smul (unitModulePresheaf R) y (U ⊓ V) hyUV
      (R.map (homOfLE h1).op a) ((unitModulePresheaf R).presheaf.map (homOfLE h2).op b)]
  exact unitModuleStalkAddEquiv_germ_smul R y (U ⊓ V) hyUV (R.map (homOfLE h1).op a)
    ((unitModulePresheaf R).presheaf.map (homOfLE h2).op b)

/-- On germs, the identification of the stalk of the unit module with the stalk of `R` is the
identity on germs of sections. -/
public lemma unitModuleStalkLinearEquiv_germ {Y : TopCat.{u}}
    (R : Y.Presheaf CommRingCat.{u}) (y : Y)
    (U : Opens Y) (hy : y ∈ U) (r : R.obj (.op U)) :
    unitModuleStalkLinearEquiv R y (TopCat.Presheaf.germ (unitModulePresheaf R).presheaf U y hy r)
      = R.germ U y hy r :=
  unitModuleStalkAddEquiv_germ R y U hy r

/-! ### The dual sheaf as an internal hom, and its stalks -/

variable {X : Scheme.{u}}

/-- The dual `F^∨ = SheafHom(F, 𝒪_X)`, packaged as a `SheafHom` so that the stalk comparison of
[Stacks, Tag 01CP] applies to it. Its underlying module is `dualSheaf F` on the nose. -/
@[sga "3 III 0.6"]
public def dualSheafHom (F : X.Modules) :
    SheafHom X.sheaf F (SheafOfModules.unit (structureSheaf X.sheaf)) where
  obj := dualSheaf F
  sectionsEquiv U := by
    change ((restrFun X.sheaf.obj U).obj F.val ⟶
      (restrFun X.sheaf.obj U).obj (SheafOfModules.unit (structureSheaf X.sheaf)).val) ≃+
        (F.over U ⟶ (SheafOfModules.unit (structureSheaf X.sheaf)).over U)
    let e : (F.over U ⟶ (SheafOfModules.unit (structureSheaf X.sheaf)).over U) ≃
        ((restrFun X.sheaf.obj U).obj F.val ⟶
          (restrFun X.sheaf.obj U).obj (SheafOfModules.unit (structureSheaf X.sheaf)).val) :=
      (SheafOfModules.fullyFaithfulForget ((structureSheaf X.sheaf).over U)).homEquiv
        (X := F.over U) (Y := (SheafOfModules.unit (structureSheaf X.sheaf)).over U)
    exact
      { toFun := e.symm
        invFun := e
        left_inv := e.apply_symm_apply
        right_inv := e.symm_apply_apply
        map_add' := by
          intro f g
          apply e.injective
          simp only [Equiv.apply_symm_apply]
          rfl }
  restrict_natural := by
    intro U V hVU s W hWV m
    change ((homRestr X.sheaf.obj F.val
      (SheafOfModules.unit (structureSheaf X.sheaf)).val (homOfLE hVU) s).app
        (op (Over.mk (homOfLE hWV)))) m = _
    rfl
  smul_natural := by
    intro U r s W hWU m
    change ((smulHom X.sheaf.obj F.val
      (SheafOfModules.unit (structureSheaf X.sheaf)).val U r s).app
        (op (Over.mk (homOfLE hWU)))) m = _
    rfl

/-- **`SheafHom(F, G)` packaged as a `SheafHom` of [Stacks, Tag 01CO]**, so that the stalk
comparison of [Stacks, Tag 01CP] applies to it. Its underlying module is the internal hom of
`StacksFrontier.Algebra.Category.ModuleCat.Presheaf.InternalHom` on the nose, which is also the
`Stacks.SheafOfModules.OnSpace.sheafHom` of the underlying ringed space.

A section over `U` of the internal hom *is* a linear natural family on the slice over `U`, so
the identification of sections is the full faithfulness of the forgetful functor on the slice
and both naturality axioms hold by `rfl` once the sections are named. -/
@[ega "0 4.1.5" "partial, schemes"]
public def sheafHomOfModules (F G : X.Modules) : SheafHom X.sheaf F G where
  obj := ⟨internalHom X.sheaf.obj F.val G.val,
    internalHom_isSheaf X.sheaf.obj F.val G.val G.isSheaf⟩
  sectionsEquiv U := by
    change ((restrFun X.sheaf.obj U).obj F.val ⟶ (restrFun X.sheaf.obj U).obj G.val) ≃+
      (F.over U ⟶ G.over U)
    let e : (F.over U ⟶ G.over U) ≃
        ((restrFun X.sheaf.obj U).obj F.val ⟶ (restrFun X.sheaf.obj U).obj G.val) :=
      (SheafOfModules.fullyFaithfulForget ((structureSheaf X.sheaf).over U)).homEquiv
        (X := F.over U) (Y := G.over U)
    exact
      { toFun := e.symm
        invFun := e
        left_inv := e.apply_symm_apply
        right_inv := e.symm_apply_apply
        map_add' := by
          intro f g
          apply e.injective
          simp only [Equiv.apply_symm_apply]
          rfl }
  restrict_natural := by
    intro U V hVU s W hWV m
    change ((homRestr X.sheaf.obj F.val G.val (homOfLE hVU) s).app
      (op (Over.mk (homOfLE hWV)))) m = _
    rfl
  smul_natural := by
    intro U r s W hWU m
    change ((smulHom X.sheaf.obj F.val G.val U r s).app
      (op (Over.mk (homOfLE hWU)))) m = _
    rfl

/-- The section identification of `dualSheafHom` evaluates a local section of the dual at a
local section of the module, which is `dualPairing`. -/
public lemma dualSheafHom_sectionsEquiv_apply (F : X.Modules) (U : X.Opens)
    (t : Γ(dualSheaf F, U)) (m : Γ(F, U)) :
    ((dualSheafHom F).sectionsEquiv U t).val.app (op (Over.mk (𝟙 U))) m
      = dualPairing F t (Over.mk (𝟙 U)) m :=
  rfl

/-- Postcomposition with a linear equivalence, as a linear equivalence of modules of linear
maps. -/
public def postcompLinearEquiv {R M N P : Type*} [CommSemiring R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] (e : N ≃ₗ[R] P) :
    (M →ₗ[R] N) ≃ₗ[R] (M →ₗ[R] P) where
  toFun f := e.toLinearMap.comp f
  invFun f := e.symm.toLinearMap.comp f
  left_inv f := by ext m; simp
  right_inv f := by ext m; simp
  map_add' f g := by ext m; simp
  map_smul' r f := by ext m; simp


/-- The stalk of the structure sheaf of a scheme, read as the stalk of the unit module. -/
public abbrev structStalk (X : Scheme.{u}) (x : X) : Ab.{u} :=
  TopCat.Presheaf.stalk (C := Ab.{u}) (unitModulePresheaf X.presheaf).presheaf x

/-- The stalk of the structure sheaf, as a module over itself. -/
public def structStalkLinearEquiv (X : Scheme.{u}) (x : X) :
    structStalk X x ≃ₗ[X.presheaf.stalk x] X.presheaf.stalk x :=
  unitModuleStalkLinearEquiv X.presheaf x

/-- The identification of the stalk of the structure sheaf with itself is the identity on
germs. -/
public lemma structStalkLinearEquiv_germ (X : Scheme.{u}) (x : X) (U : X.Opens) (hx : x ∈ U)
    (r : Γ(X, U)) :
    structStalkLinearEquiv X x
        (TopCat.Presheaf.germ (unitModulePresheaf X.presheaf).presheaf U x hx r)
      = X.presheaf.germ U x hx r :=
  unitModuleStalkLinearEquiv_germ X.presheaf x U hx r

/-- **[Stacks, Tag 01CP] for the dual.** For `F` of finite presentation the stalk of `F^∨` at
`x` is the `𝒪_{X,x}`-linear dual of the stalk of `F`. -/
public def dualStalkEquiv (F : X.Modules) [F.IsFinitePresentation] (x : X) :
    (dualSheaf F).presheaf.stalk x ≃ₗ[X.presheaf.stalk x]
      Module.Dual (X.presheaf.stalk x) (F.presheaf.stalk x) :=
  letI e₀ : (dualSheaf F).presheaf.stalk x ≃ₗ[X.presheaf.stalk x]
      (F.presheaf.stalk x →ₗ[X.presheaf.stalk x] structStalk X x) :=
    (sheafHomStalkLinearEquivOfFinitePresentation (dualSheafHom F) x).equiv
  e₀.trans (postcompLinearEquiv (structStalkLinearEquiv X x))

/-- The value of the dual stalk comparison, in terms of the comparison of Tag 01CP. -/
public lemma dualStalkEquiv_apply (F : X.Modules) [F.IsFinitePresentation] (x : X)
    (sigma : (dualSheaf F).presheaf.stalk x) (m : F.presheaf.stalk x) :
    dualStalkEquiv F x sigma m =
      structStalkLinearEquiv X x
        ((sheafHomStalkLinearEquivOfFinitePresentation (dualSheafHom F) x).equiv sigma m) :=
  rfl

/-- The dual stalk comparison on germs: the germ of a local functional, evaluated at the germ
of a local section, is the germ of the value. -/
public lemma dualStalkEquiv_germ (F : X.Modules) [F.IsFinitePresentation] (x : X)
    (U : X.Opens) (hx : x ∈ U) (t : Γ(dualSheaf F, U)) (m : Γ(F, U)) :
    dualStalkEquiv F x
        (TopCat.Presheaf.germ (C := Ab.{u}) (dualSheaf F).val.presheaf U x hx t)
        (TopCat.Presheaf.germ (C := Ab.{u}) F.val.presheaf U x hx m)
      = X.presheaf.germ U x hx (dualPairing F t (Over.mk (𝟙 U)) m) :=
  (dualStalkEquiv_apply F x _ _).trans
    ((congrArg (structStalkLinearEquiv X x)
        ((sheafHomStalkLinearEquivOfFinitePresentation (dualSheafHom F) x).germ_apply
          U hx t m)).trans
      (structStalkLinearEquiv_germ X x U hx (dualPairing F t (Over.mk (𝟙 U)) m)))

/-! ### Reflexivity is reflexivity of the stalks -/

/-- The map induced on stalks by a morphism of modules on a scheme. -/
public def stalkMapOfHom {F G : X.Modules} (f : F ⟶ G) (x : X) :
    F.presheaf.stalk x ⟶ G.presheaf.stalk x :=
  (Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} x).map f

/-- The map induced on stalks sends the germ of a local section to the germ of its image. -/
public lemma stalkMapOfHom_germ {F G : X.Modules} (f : F ⟶ G) (x : X) (U : X.Opens)
    (hx : x ∈ U) (s : Γ(F, U)) :
    stalkMapOfHom f x (TopCat.Presheaf.germ (C := Ab.{u}) F.val.presheaf U x hx s)
      = TopCat.Presheaf.germ (C := Ab.{u}) G.val.presheaf U x hx
          (Scheme.Modules.Hom.app f U s) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply _ _ _ _ _

/-- The map induced on stalks by an isomorphism is bijective. -/
public lemma bijective_stalkMapOfHom {F G : X.Modules} (f : F ⟶ G) (hf : IsIso f) (x : X) :
    Function.Bijective (stalkMapOfHom f x) :=
  (ConcreteCategory.isIso_iff_bijective _).mp (Functor.map_isIso _ _)

/-- The germ of a local functional of `F^∨`, evaluated through the double-dual comparison at
the germ of a local section of `F`, is the germ of the value of the functional. -/
public lemma dualStalkEquiv_toDoubleDual_germ (F : X.Modules) [F.IsFinitePresentation]
    [(dualSheaf F).IsFinitePresentation] (x : X) (U : X.Opens) (hx : x ∈ U)
    (t : Γ(dualSheaf F, U)) (f : Γ(F, U)) :
    dualStalkEquiv (dualSheaf F) x
        (stalkMapOfHom (toDoubleDual F) x
          (TopCat.Presheaf.germ (C := Ab.{u}) F.val.presheaf U x hx f))
        (TopCat.Presheaf.germ (C := Ab.{u}) (dualSheaf F).val.presheaf U x hx t)
      = X.presheaf.germ U x hx (dualPairing F t (Over.mk (𝟙 U)) f) := by
  rw [stalkMapOfHom_germ, dualStalkEquiv_germ]
  exact congrArg (X.presheaf.germ U x hx) (toDoubleDual_val_app_apply F U f t)

/-- The two stalk comparisons agree: a germ of the dual, read as a functional on the stalk,
evaluates on a germ of `F` exactly as the double-dual comparison of that germ evaluates on
the germ of the dual. -/
public lemma dualStalkEquiv_eq_dualStalkEquiv_toDoubleDual (F : X.Modules)
    [F.IsFinitePresentation] [(dualSheaf F).IsFinitePresentation] (x : X)
    (m : F.presheaf.stalk x) (tau : (dualSheaf F).presheaf.stalk x) :
    dualStalkEquiv F x tau m
      = dualStalkEquiv (dualSheaf F) x (stalkMapOfHom (toDoubleDual F) x m) tau := by
  obtain ⟨V, hxV, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq (C := Ab.{u})
    (dualSheaf F).val.presheaf tau
  obtain ⟨W, hxW, f, rfl⟩ := TopCat.Presheaf.exists_germ_eq (C := Ab.{u}) F.val.presheaf m
  have hxU : x ∈ V ⊓ W := ⟨hxV, hxW⟩
  have hVU : V ⊓ W ≤ V := inf_le_left
  have hWU : V ⊓ W ≤ W := inf_le_right
  rw [← TopCat.Presheaf.germ_res_apply (C := Ab.{u}) (dualSheaf F).val.presheaf
      (homOfLE hVU) x hxU t,
    ← TopCat.Presheaf.germ_res_apply (C := Ab.{u}) F.val.presheaf (homOfLE hWU) x hxU f]
  exact (dualStalkEquiv_germ F x (V ⊓ W) hxU _ _).trans
    (dualStalkEquiv_toDoubleDual_germ F x (V ⊓ W) hxU _ _).symm

/-- **[Stacks, Tag 0AY3], (1) implies (2).** If a module of finite presentation whose dual is
also of finite presentation is reflexive, then each of its stalks is a reflexive module over the
local ring at that point. -/
public theorem isReflexive_stalk_of_isReflexive (F : X.Modules) [F.IsFinitePresentation]
    [(dualSheaf F).IsFinitePresentation] (hF : IsReflexive F) (x : X) :
    Module.IsReflexive (X.presheaf.stalk x) (F.presheaf.stalk x) := by
  refine ⟨?_⟩
  have hfun : ⇑(Module.Dual.eval (X.presheaf.stalk x) (F.presheaf.stalk x)) =
      fun m : F.presheaf.stalk x => (dualStalkEquiv F x).symm.dualMap
        (dualStalkEquiv (dualSheaf F) x (stalkMapOfHom (toDoubleDual F) x m)) := by
    funext m
    refine LinearMap.ext fun lam => ?_
    rw [LinearEquiv.dualMap_apply]
    have h := dualStalkEquiv_eq_dualStalkEquiv_toDoubleDual F x m
      ((dualStalkEquiv F x).symm lam)
    rw [(dualStalkEquiv F x).apply_symm_apply] at h
    exact h
  rw [hfun]
  exact (((dualStalkEquiv F x).symm.dualMap.bijective.comp
    (dualStalkEquiv (dualSheaf F) x).bijective).comp
      (bijective_stalkMapOfHom (toDoubleDual F) hF x))

end Stacks.AlgebraicGeometry.ReflexiveModules
