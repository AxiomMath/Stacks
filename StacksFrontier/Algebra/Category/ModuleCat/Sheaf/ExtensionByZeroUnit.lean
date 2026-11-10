module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LeftExact
public import StacksFrontier.CategoryTheory.Sites.AbelianSheafificationExistence
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import StacksCore.Tactic.StacksAttribute

/-!
# The extension by zero of the structure sheaf, and the maps out of it

Let `R` be a sheaf of rings on a site `C` and let `U : C` be an object. The *extension by
zero of the structure sheaf of the localised site `C/U`*, written `j_{U!} O_U` in the Stacks
project, is the sheaf of `R`-modules obtained by sheafifying the presheaf whose sections over
`X` are the finitely supported `R(X)`-linear combinations of the arrows `X ⟶ U`. This file
constructs it and proves that morphisms out of it are canonically the sections of the target
over `U`, naturally in the target.

## Main definitions

* `Stacks.SheafOfModules.extensionByZeroUnitPresheaf`: the presheaf of `R`-modules with
  sections `ULift (X ⟶ U) →₀ R(X)` over `X`.
* `Stacks.SheafOfModules.extensionByZeroUnitGen`: its tautological section
  `Finsupp.single (𝟙 U) 1` over `U`, which generates it.
* `Stacks.SheafOfModules.extensionByZeroUnit`: the sheafification, i.e. `j_{U!} O_U`.
* `Stacks.SheafOfModules.extensionByZeroUnitPresheafMap` and
  `Stacks.SheafOfModules.extensionByZeroUnitMap`: functoriality in `U`.

## Main results

* `Stacks.SheafOfModules.extensionByZeroUnitPresheafHomEquiv`: morphisms out of the presheaf
  are the sections over `U`.
* `Stacks.SheafOfModules.extensionByZeroUnitHomEquiv`: morphisms `j_{U!} O_U ⟶ N` are the
  sections of `N` over `U`.
* `Stacks.SheafOfModules.extensionByZeroUnitHomEquiv_naturality`: naturality in the target.
* `Stacks.SheafOfModules.extensionByZeroUnitCorepresentableBy`: `j_{U!} O_U` corepresents the
  sections over `U`.
* `Stacks.SheafOfModules.extensionByZeroUnitHomEquiv_map`: compatibility with functoriality
  in `U`.

## References

* [Stacks Project, Tag 0G1V](https://stacks.math.columbia.edu/tag/0G1V)
* [Stacks Project, Tag 03DI](https://stacks.math.columbia.edu/tag/03DI)
-/

@[expose] public section

open CategoryTheory Opposite

universe u₁ v₁ w t

namespace Stacks.SheafOfModules

variable {C : Type u₁} [Category.{v₁} C]

section Presheaf

variable (R : Cᵒᵖ ⥤ RingCat.{w})

/-- The restriction map of the extension by zero of the structure sheaf: an arrow
`f : X ⟶ Y` of `Cᵒᵖ` composes the indexing arrows with `f.unop` and restricts the
coefficients along `R.map f`. -/
noncomputable def extensionByZeroUnitRestriction (U : C) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (ULift.{max u₁ v₁ w t} (X.unop ⟶ U) →₀ R.obj X) →+
      (ULift.{max u₁ v₁ w t} (Y.unop ⟶ U) →₀ R.obj Y) :=
  (Finsupp.mapDomain.addMonoidHom
      (fun h : ULift.{max u₁ v₁ w t} (X.unop ⟶ U) =>
        (ULift.up (f.unop ≫ h.down) : ULift.{max u₁ v₁ w t} (Y.unop ⟶ U)))).comp
    (Finsupp.mapRange.addMonoidHom (R.map f).hom.toAddMonoidHom)

/-- The restriction map sends the basis element indexed by `h` with coefficient `r` to the basis
element indexed by `f.unop ≫ h.down` with coefficient `R.map f r`. -/
@[simp]
lemma extensionByZeroUnitRestriction_single (U : C) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (h : ULift.{max u₁ v₁ w t} (X.unop ⟶ U)) (r : R.obj X) :
    extensionByZeroUnitRestriction.{u₁, v₁, w, t} R U f (Finsupp.single h r) =
      Finsupp.single (ULift.up (f.unop ≫ h.down)) (R.map f r) := by
  simp [extensionByZeroUnitRestriction, Finsupp.mapDomain.addMonoidHom,
    Finsupp.mapRange.addMonoidHom, Finsupp.mapRange_single, Finsupp.mapDomain_single]

/-- The restriction map is semilinear along `R.map f`. -/
lemma extensionByZeroUnitRestriction_smul (U : C) {X Y : Cᵒᵖ} (f : X ⟶ Y) (r : R.obj X)
    (x : ULift.{max u₁ v₁ w t} (X.unop ⟶ U) →₀ R.obj X) :
    extensionByZeroUnitRestriction.{u₁, v₁, w, t} R U f (r • x) =
      R.map f r • extensionByZeroUnitRestriction.{u₁, v₁, w, t} R U f x := by
  rw [extensionByZeroUnitRestriction, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply,
    show (Finsupp.mapRange.addMonoidHom (R.map f).hom.toAddMonoidHom) (r • x) =
      Finsupp.mapRange (R.map f) (map_zero (R.map f).hom) (r • x) from rfl,
    show (Finsupp.mapRange.addMonoidHom (R.map f).hom.toAddMonoidHom) x =
      Finsupp.mapRange (R.map f) (map_zero (R.map f).hom) x from rfl,
    Finsupp.mapRange_smul' r (R.map f r) x (fun a => map_mul (R.map f).hom r a),
    show (Finsupp.mapDomain.addMonoidHom
        (fun h : ULift.{max u₁ v₁ w t} (X.unop ⟶ U) =>
          (ULift.up (f.unop ≫ h.down) : ULift.{max u₁ v₁ w t} (Y.unop ⟶ U))))
        (R.map f r • Finsupp.mapRange (R.map f) (map_zero (R.map f).hom) x) =
      Finsupp.mapDomain _ (R.map f r • Finsupp.mapRange (R.map f)
        (map_zero (R.map f).hom) x) from rfl,
    Finsupp.mapDomain_smul]
  rfl

/-- The presheaf of abelian groups underlying the extension by zero of the structure sheaf. -/
noncomputable def extensionByZeroUnitAb (U : C) : Cᵒᵖ ⥤ AddCommGrpCat.{max u₁ v₁ w t} where
  obj X := AddCommGrpCat.of (ULift.{max u₁ v₁ w t} (X.unop ⟶ U) →₀ R.obj X)
  map f := AddCommGrpCat.ofHom (extensionByZeroUnitRestriction.{u₁, v₁, w, t} R U f)
  map_id X := AddCommGrpCat.hom_ext (Finsupp.addHom_ext fun h r => by simp)
  map_comp f g := AddCommGrpCat.hom_ext (Finsupp.addHom_ext fun h r => by simp)

/-- The restriction maps of `extensionByZeroUnitAb` are `extensionByZeroUnitRestriction`. -/
@[simp]
lemma extensionByZeroUnitAb_map (U : C) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (extensionByZeroUnitAb.{u₁, v₁, w, t} R U).map f =
      AddCommGrpCat.ofHom (extensionByZeroUnitRestriction.{u₁, v₁, w, t} R U f) := rfl

/-- The sections of `extensionByZeroUnitAb` over `X` form an `R(X)`-module. -/
noncomputable instance extensionByZeroUnitAbModule (U : C) (X : Cᵒᵖ) :
    Module (R.obj X) ((extensionByZeroUnitAb.{u₁, v₁, w, t} R U).obj X) :=
  inferInstanceAs (Module (R.obj X) (ULift.{max u₁ v₁ w t} (X.unop ⟶ U) →₀ R.obj X))

/-- Before sheafification, the extension by zero of the structure sheaf of `C/U` has one copy
of `R(X)` for every arrow `X ⟶ U`; the restriction maps compose the arrows and restrict the
coefficients. This is the direct-sum construction of `j_{U!} R|_U` from Stacks 03DI. -/
noncomputable def extensionByZeroUnitPresheaf (U : C) : PresheafOfModules.{max u₁ v₁ w t} R :=
  PresheafOfModules.ofPresheaf (extensionByZeroUnitAb.{u₁, v₁, w, t} R U)
    (fun {_ _} f r x => extensionByZeroUnitRestriction_smul.{u₁, v₁, w, t} R U f r x)

/-- The restriction maps of `extensionByZeroUnitPresheaf` on a basis element. -/
lemma extensionByZeroUnitPresheaf_map_single (U : C) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (h : ULift.{max u₁ v₁ w t} (X.unop ⟶ U)) (r : R.obj X) :
    (extensionByZeroUnitPresheaf.{u₁, v₁, w, t} R U).map f (Finsupp.single h r) =
      Finsupp.single (ULift.up (f.unop ≫ h.down)) (R.map f r) :=
  extensionByZeroUnitRestriction_single.{u₁, v₁, w, t} R U f h r

/-- The tautological section of the extension by zero of the structure sheaf over `U`: the
basis element indexed by `𝟙 U`, with coefficient `1`. -/
noncomputable def extensionByZeroUnitGen (U : C) :
    ToType ((extensionByZeroUnitPresheaf.{u₁, v₁, w, t} R U).obj (op U)) :=
  (Finsupp.single (ULift.up (𝟙 U)) (1 : R.obj (op U)) :
    ULift.{max u₁ v₁ w t} (U ⟶ U) →₀ R.obj (op U))

/-- Restricting the tautological section along `h : X ⟶ U` gives the basis element indexed by
`h`, with coefficient `1`. -/
lemma extensionByZeroUnitPresheaf_map_gen (U : C) {X : Cᵒᵖ} (h : X.unop ⟶ U) :
    (extensionByZeroUnitPresheaf.{u₁, v₁, w, t} R U).map h.op
        (extensionByZeroUnitGen.{u₁, v₁, w, t} R U) =
      (Finsupp.single (ULift.up h) (1 : R.obj X) :
        ULift.{max u₁ v₁ w t} (X.unop ⟶ U) →₀ R.obj X) := by
  rw [extensionByZeroUnitGen, extensionByZeroUnitPresheaf_map_single]
  simp only [Opposite.unop_op, Category.comp_id, map_one]
  rfl

end Presheaf

section PresheafHom

variable {R : Cᵒᵖ ⥤ RingCat.{w}}

/-- The morphism out of the extension by zero of the structure sheaf determined by a section
of the target over `U`: the basis element indexed by `h : X ⟶ U` is sent to the restriction
of that section along `h`. -/
noncomputable def extensionByZeroUnitPresheafDesc (U : C)
    (M : PresheafOfModules.{max u₁ v₁ w t} R) (s : ToType (M.obj (op U))) :
    extensionByZeroUnitPresheaf.{u₁, v₁, w, t} R U ⟶ M where
  app X := ModuleCat.ofHom
    (Finsupp.linearCombination (R.obj X)
      (fun h : ULift.{max u₁ v₁ w t} (X.unop ⟶ U) => M.map h.down.op s))
  naturality {X Y} f := by
    refine ModuleCat.hom_ext (Finsupp.lhom_ext fun a r => ?_)
    change Finsupp.linearCombination (R.obj Y)
        (fun h : ULift.{max u₁ v₁ w t} (Y.unop ⟶ U) => M.map h.down.op s)
        ((extensionByZeroUnitPresheaf.{u₁, v₁, w, t} R U).map f (Finsupp.single a r)) =
      M.map f (Finsupp.linearCombination (R.obj X)
        (fun h : ULift.{max u₁ v₁ w t} (X.unop ⟶ U) => M.map h.down.op s)
        (Finsupp.single a r))
    rw [extensionByZeroUnitPresheaf_map_single,
      Finsupp.linearCombination_single
        (R := (R.obj Y : Type w))
        (v := fun h : ULift.{max u₁ v₁ w t} (Y.unop ⟶ U) => M.map h.down.op s)
        (c := R.map f r) (a := ULift.up (f.unop ≫ a.down)),
      Finsupp.linearCombination_single
        (R := (R.obj X : Type w))
        (v := fun h : ULift.{max u₁ v₁ w t} (X.unop ⟶ U) => M.map h.down.op s)
        (c := r) (a := a)]
    exact ((M.map_smul f r (M.map a.down.op s)).trans
      (congrArg (R.map f r • ·) (M.map_comp_apply a.down.op f s).symm)).symm

/-- `extensionByZeroUnitPresheafDesc U M s` sends the basis element indexed by `a` with
coefficient `r` to `r • M.map a.down.op s`. -/
lemma extensionByZeroUnitPresheafDesc_app_single (U : C)
    (M : PresheafOfModules.{max u₁ v₁ w t} R) (s : ToType (M.obj (op U))) (X : Cᵒᵖ)
    (a : ULift.{max u₁ v₁ w t} (X.unop ⟶ U)) (r : R.obj X) :
    (extensionByZeroUnitPresheafDesc.{u₁, v₁, w, t} U M s).app X (Finsupp.single a r) =
      r • M.map a.down.op s := by
  change Finsupp.linearCombination (R.obj X)
      (fun h : ULift.{max u₁ v₁ w t} (X.unop ⟶ U) => M.map h.down.op s)
      (Finsupp.single a r) = _
  exact Finsupp.linearCombination_single
    (R := (R.obj X : Type w))
    (v := fun h : ULift.{max u₁ v₁ w t} (X.unop ⟶ U) => M.map h.down.op s) (c := r) (a := a)

/-- The section of the target over `U` attached to a morphism out of the extension by zero of
the structure sheaf: the image of the tautological section. -/
noncomputable def extensionByZeroUnitPresheafSection (U : C)
    (M : PresheafOfModules.{max u₁ v₁ w t} R)
    (ψ : extensionByZeroUnitPresheaf.{u₁, v₁, w, t} R U ⟶ M) : ToType (M.obj (op U)) :=
  ψ.app (op U) (extensionByZeroUnitGen.{u₁, v₁, w, t} R U)

/-- Morphisms out of the extension by zero of the structure sheaf of `C/U`, before
sheafification, are canonically the sections of the target over `U`. -/
noncomputable def extensionByZeroUnitPresheafHomEquiv (U : C)
    (M : PresheafOfModules.{max u₁ v₁ w t} R) :
    (extensionByZeroUnitPresheaf.{u₁, v₁, w, t} R U ⟶ M) ≃ ToType (M.obj (op U)) where
  toFun := extensionByZeroUnitPresheafSection.{u₁, v₁, w, t} U M
  invFun := extensionByZeroUnitPresheafDesc.{u₁, v₁, w, t} U M
  left_inv ψ := by
    refine PresheafOfModules.hom_ext fun X => ModuleCat.hom_ext (Finsupp.lhom_ext fun a r => ?_)
    change (extensionByZeroUnitPresheafDesc.{u₁, v₁, w, t} U M
        (extensionByZeroUnitPresheafSection.{u₁, v₁, w, t} U M ψ)).app X
        (Finsupp.single a r) = ψ.app X (Finsupp.single a r)
    rw [extensionByZeroUnitPresheafDesc_app_single, extensionByZeroUnitPresheafSection,
      ← PresheafOfModules.naturality_apply, extensionByZeroUnitPresheaf_map_gen]
    exact ((ψ.app X).hom.map_smul r _).symm.trans (congrArg (fun x => (ψ.app X) x)
      ((Finsupp.smul_single r (ULift.up a.down) (1 : R.obj X)).trans
        (by rw [smul_eq_mul, mul_one])))
  right_inv s := by
    rw [extensionByZeroUnitPresheafSection, extensionByZeroUnitGen,
      extensionByZeroUnitPresheafDesc_app_single]
    exact (one_smul _ _).trans (ConcreteCategory.congr_hom (M.presheaf.map_id (op U)) s)

/-- `extensionByZeroUnitPresheafHomEquiv U M ψ` is the image of the tautological section under
`ψ`. -/
@[simp]
lemma extensionByZeroUnitPresheafHomEquiv_apply (U : C)
    (M : PresheafOfModules.{max u₁ v₁ w t} R)
    (ψ : extensionByZeroUnitPresheaf.{u₁, v₁, w, t} R U ⟶ M) :
    extensionByZeroUnitPresheafHomEquiv.{u₁, v₁, w, t} U M ψ =
      ψ.app (op U) (extensionByZeroUnitGen.{u₁, v₁, w, t} R U) := rfl

/-- The presheaf-level correspondence is natural in the target. -/
lemma extensionByZeroUnitPresheafHomEquiv_naturality (U : C)
    {M N : PresheafOfModules.{max u₁ v₁ w t} R}
    (ψ : extensionByZeroUnitPresheaf.{u₁, v₁, w, t} R U ⟶ M) (φ : M ⟶ N) :
    extensionByZeroUnitPresheafHomEquiv.{u₁, v₁, w, t} U N (ψ ≫ φ) =
      φ.app (op U) (extensionByZeroUnitPresheafHomEquiv.{u₁, v₁, w, t} U M ψ) := rfl

/-- Functoriality of the extension by zero of the structure sheaf in `U`, before
sheafification: an arrow `f : V ⟶ U` sends the basis element indexed by `h : X ⟶ V` to the
one indexed by `h ≫ f`. -/
noncomputable def extensionByZeroUnitPresheafMap (R : Cᵒᵖ ⥤ RingCat.{w}) {V U : C} (f : V ⟶ U) :
    extensionByZeroUnitPresheaf.{u₁, v₁, w, t} R V ⟶
      extensionByZeroUnitPresheaf.{u₁, v₁, w, t} R U where
  app X := ModuleCat.ofHom (Finsupp.lmapDomain _ _
    (fun h : ULift.{max u₁ v₁ w t} (X.unop ⟶ V) =>
      (ULift.up (h.down ≫ f) : ULift.{max u₁ v₁ w t} (X.unop ⟶ U))))
  naturality {X Y} g := by
    refine ModuleCat.hom_ext (Finsupp.lhom_ext fun a r => ?_)
    change Finsupp.mapDomain
        (fun h : ULift.{max u₁ v₁ w t} (Y.unop ⟶ V) =>
          (ULift.up (h.down ≫ f) : ULift.{max u₁ v₁ w t} (Y.unop ⟶ U)))
        ((extensionByZeroUnitPresheaf.{u₁, v₁, w, t} R V).map g (Finsupp.single a r)) =
      (extensionByZeroUnitPresheaf.{u₁, v₁, w, t} R U).map g
        (Finsupp.mapDomain
          (fun h : ULift.{max u₁ v₁ w t} (X.unop ⟶ V) =>
            (ULift.up (h.down ≫ f) : ULift.{max u₁ v₁ w t} (X.unop ⟶ U)))
          (Finsupp.single a r))
    rw [extensionByZeroUnitPresheaf_map_single, Finsupp.mapDomain_single,
      Finsupp.mapDomain_single, extensionByZeroUnitPresheaf_map_single, Category.assoc]

/-- `extensionByZeroUnitPresheafMap R f` sends the basis element indexed by `a` to the one
indexed by `a.down ≫ f`, with the same coefficient. -/
lemma extensionByZeroUnitPresheafMap_app_single {V U : C} (f : V ⟶ U) (X : Cᵒᵖ)
    (a : ULift.{max u₁ v₁ w t} (X.unop ⟶ V)) (r : R.obj X) :
    (extensionByZeroUnitPresheafMap.{u₁, v₁, w, t} R f).app X (Finsupp.single a r) =
      Finsupp.single (ULift.up (a.down ≫ f)) r :=
  Finsupp.mapDomain_single

/-- `extensionByZeroUnitPresheafMap R f` sends the tautological section over `V` to the
restriction along `f` of the tautological section over `U`. -/
lemma extensionByZeroUnitPresheafMap_app_gen {V U : C} (f : V ⟶ U) :
    (extensionByZeroUnitPresheafMap.{u₁, v₁, w, t} R f).app (op V)
        (extensionByZeroUnitGen.{u₁, v₁, w, t} R V) =
      (extensionByZeroUnitPresheaf.{u₁, v₁, w, t} R U).map f.op
        (extensionByZeroUnitGen.{u₁, v₁, w, t} R U) := by
  rw [extensionByZeroUnitPresheaf_map_gen.{u₁, v₁, w, t} R U (X := op V) f,
    extensionByZeroUnitGen, extensionByZeroUnitPresheafMap_app_single]
  simp only [Category.id_comp]
  rfl

/-- Compatibility of the presheaf-level correspondence with functoriality in `U`. -/
lemma extensionByZeroUnitPresheafHomEquiv_map {V U : C} (f : V ⟶ U)
    (M : PresheafOfModules.{max u₁ v₁ w t} R)
    (ψ : extensionByZeroUnitPresheaf.{u₁, v₁, w, t} R U ⟶ M) :
    extensionByZeroUnitPresheafHomEquiv.{u₁, v₁, w, t} V M
        (extensionByZeroUnitPresheafMap.{u₁, v₁, w, t} R f ≫ ψ) =
      M.map f.op (extensionByZeroUnitPresheafHomEquiv.{u₁, v₁, w, t} U M ψ) := by
  have h : (extensionByZeroUnitPresheafMap.{u₁, v₁, w, t} R f ≫ ψ).app (op V)
      (extensionByZeroUnitGen.{u₁, v₁, w, t} R V) = ψ.app (op V)
      ((extensionByZeroUnitPresheafMap.{u₁, v₁, w, t} R f).app (op V)
        (extensionByZeroUnitGen.{u₁, v₁, w, t} R V)) := rfl
  rw [extensionByZeroUnitPresheafHomEquiv_apply, extensionByZeroUnitPresheafHomEquiv_apply, h,
    extensionByZeroUnitPresheafMap_app_gen, PresheafOfModules.naturality_apply]

end PresheafHom

section Sheaf

variable {J : GrothendieckTopology C}

/-- Sheafification of presheaves of abelian groups exists in any universe containing the
objects and the morphisms of the site: the site is then essentially small. -/
theorem siteHasSheafify (J : GrothendieckTopology C) [UnivLE.{u₁, t}] [UnivLE.{v₁, t}] :
    HasSheafify J AddCommGrpCat.{t} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall J

/-- In any universe containing the objects and the morphisms of the site, sheafification of
abelian presheaves inverts exactly the locally bijective morphisms. -/
theorem siteWEqualsLocallyBijective (J : GrothendieckTopology C) [UnivLE.{u₁, t}]
    [UnivLE.{v₁, t}] : J.WEqualsLocallyBijective AddCommGrpCat.{t} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{v₁, t, u₁, t + 1, t} J

attribute [local instance] siteHasSheafify siteWEqualsLocallyBijective

/-- The extension by zero of the structure sheaf of the localised site `C/U`, as a sheaf of
`R`-modules: the sheafification of `extensionByZeroUnitPresheaf`. In the notation of the
Stacks project this is `j_{U!} O_U`. -/
noncomputable def extensionByZeroUnit (R : Sheaf J RingCat.{w}) (U : C) :
    SheafOfModules.{max u₁ v₁ w t} R :=
  (PresheafOfModules.sheafification.{max u₁ v₁ w t} (𝟙 R.obj)).obj
    (extensionByZeroUnitPresheaf.{u₁, v₁, w, t} R.obj U)

/-- Functoriality of the extension by zero of the structure sheaf in `U`. -/
noncomputable def extensionByZeroUnitMap (R : Sheaf J RingCat.{w}) {V U : C} (f : V ⟶ U) :
    extensionByZeroUnit.{u₁, v₁, w, t} R V ⟶ extensionByZeroUnit.{u₁, v₁, w, t} R U :=
  (PresheafOfModules.sheafification.{max u₁ v₁ w t} (𝟙 R.obj)).map
    (extensionByZeroUnitPresheafMap.{u₁, v₁, w, t} R.obj f)

/-- Morphisms from the extension by zero of the structure sheaf of the localised site `C/U` to a
sheaf of modules `N` are canonically the sections of `N` over `U`. -/
@[stacks 0G1V "for the sheafified-free-module spelling of `j_{U!} O_U`"]
noncomputable def extensionByZeroUnitHomEquiv (R : Sheaf J RingCat.{w}) (U : C)
    (N : SheafOfModules.{max u₁ v₁ w t} R) :
    (extensionByZeroUnit.{u₁, v₁, w, t} R U ⟶ N) ≃ ToType (N.val.obj (op U)) :=
  (PresheafOfModules.sheafificationHomEquiv.{max u₁ v₁ w t} (𝟙 R.obj)).trans
    (extensionByZeroUnitPresheafHomEquiv.{u₁, v₁, w, t} U _)

/-- `extensionByZeroUnitHomEquiv R U N ψ` is the image of the tautological section under the
presheaf-level transpose of `ψ`. -/
lemma extensionByZeroUnitHomEquiv_apply (R : Sheaf J RingCat.{w}) (U : C)
    (N : SheafOfModules.{max u₁ v₁ w t} R)
    (ψ : extensionByZeroUnit.{u₁, v₁, w, t} R U ⟶ N) :
    extensionByZeroUnitHomEquiv.{u₁, v₁, w, t} R U N ψ =
      (PresheafOfModules.sheafificationHomEquiv.{max u₁ v₁ w t} (𝟙 R.obj) ψ).app (op U)
        (extensionByZeroUnitGen.{u₁, v₁, w, t} R.obj U) := rfl

/-- The bijection `extensionByZeroUnitHomEquiv` is natural in the target module. -/
@[stacks 0G1V "naturality in the target"]
lemma extensionByZeroUnitHomEquiv_naturality (R : Sheaf J RingCat.{w}) (U : C)
    {M N : SheafOfModules.{max u₁ v₁ w t} R}
    (ψ : extensionByZeroUnit.{u₁, v₁, w, t} R U ⟶ M) (φ : M ⟶ N) :
    extensionByZeroUnitHomEquiv.{u₁, v₁, w, t} R U N (ψ ≫ φ) =
      ((SheafOfModules.evaluation R (op U)).map φ)
        (extensionByZeroUnitHomEquiv.{u₁, v₁, w, t} R U M ψ) :=
  congrArg
    (fun χ : extensionByZeroUnitPresheaf.{u₁, v₁, w, t} R.obj U ⟶
        (PresheafOfModules.restrictScalars (𝟙 R.obj)).obj
          ((SheafOfModules.forget R).obj N) =>
      χ.app (op U) (extensionByZeroUnitGen.{u₁, v₁, w, t} R.obj U))
    ((PresheafOfModules.sheafificationAdjunction.{max u₁ v₁ w t}
      (𝟙 R.obj)).homEquiv_naturality_right ψ φ)

/-- The extension by zero of the structure sheaf of `C/U` corepresents the functor sending a
sheaf of modules to its sections over `U`. -/
@[stacks 0G1V "corepresentability"]
noncomputable def extensionByZeroUnitCorepresentableBy (R : Sheaf J RingCat.{w}) (U : C) :
    (SheafOfModules.evaluation R (op U) ⋙
        forget (ModuleCat.{max u₁ v₁ w t} (R.obj.obj (op U)))).CorepresentableBy
      (extensionByZeroUnit.{u₁, v₁, w, t} R U) where
  homEquiv := extensionByZeroUnitHomEquiv.{u₁, v₁, w, t} R U _
  homEquiv_comp g f := extensionByZeroUnitHomEquiv_naturality.{u₁, v₁, w, t} R U f g

/-- The bijection `extensionByZeroUnitHomEquiv` is compatible with functoriality in `U`. -/
lemma extensionByZeroUnitHomEquiv_map (R : Sheaf J RingCat.{w}) {V U : C} (f : V ⟶ U)
    (N : SheafOfModules.{max u₁ v₁ w t} R)
    (ψ : extensionByZeroUnit.{u₁, v₁, w, t} R U ⟶ N) :
    extensionByZeroUnitHomEquiv.{u₁, v₁, w, t} R V N
        (extensionByZeroUnitMap.{u₁, v₁, w, t} R f ≫ ψ) =
      N.val.map f.op (extensionByZeroUnitHomEquiv.{u₁, v₁, w, t} R U N ψ) :=
  (congrArg
    (fun χ : extensionByZeroUnitPresheaf.{u₁, v₁, w, t} R.obj V ⟶
        (PresheafOfModules.restrictScalars (𝟙 R.obj)).obj
          ((SheafOfModules.forget R).obj N) =>
      extensionByZeroUnitPresheafHomEquiv.{u₁, v₁, w, t} V
        ((PresheafOfModules.restrictScalars (𝟙 R.obj)).obj
          ((SheafOfModules.forget R).obj N)) χ)
    ((PresheafOfModules.sheafificationAdjunction.{max u₁ v₁ w t}
      (𝟙 R.obj)).homEquiv_naturality_left
        (extensionByZeroUnitPresheafMap.{u₁, v₁, w, t} R.obj f) ψ)).trans
    (extensionByZeroUnitPresheafHomEquiv_map.{u₁, v₁, w, t} f _
      (PresheafOfModules.sheafificationHomEquiv.{max u₁ v₁ w t} (𝟙 R.obj) ψ))

end Sheaf

end Stacks.SheafOfModules

end
