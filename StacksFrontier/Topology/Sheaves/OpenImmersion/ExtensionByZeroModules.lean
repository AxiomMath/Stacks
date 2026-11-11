module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafify
public import StacksFrontier.Topology.Sheaves.OpenImmersion.ExtensionByInitial

/-!
# Extension by zero of (pre)sheaves of modules along an open immersion

Let `X` be a topological space, `j : U → X` the inclusion of an open subset and `𝒪` a presheaf
of rings on `X`. For a presheaf `ℱ` of `𝒪|_U`-modules, the *extension by zero* `j_{p!}ℱ` is the
presheaf of `𝒪`-modules whose underlying abelian presheaf is the extension by zero of the
underlying abelian presheaf of `ℱ` (`TopCat.Presheaf.extendByInitial`, at the value category
`AddCommGrpCat`, whose initial object is a zero group), with the multiplication
`𝒪(V) × j_{p!}ℱ(V) → j_{p!}ℱ(V)` given on an open `V ⊆ U` by restricting a section of `𝒪` to
`V = j(j⁻¹ V)` and multiplying in `ℱ(j⁻¹ V)`, and on an open `V ⊄ U` by the zero map.

When `𝒪` is a sheaf of rings and `ℱ` a sheaf of `𝒪|_U`-modules, the extension by zero `j_!ℱ` is
the sheaf of `𝒪`-modules whose underlying abelian sheaf is the sheafification `j_!ℱ` of
`j_{p!}ℱ` (`TopCat.Presheaf.extendByInitialSheafify`), with the multiplication obtained from
that of `j_{p!}ℱ` by sheafifying (Mathlib's `PresheafOfModules.sheafify`).

## Main definitions

* `TopCat.Presheaf.extendByZeroPresheafOfModules`: `j_{p!}ℱ` for a presheaf of modules.
* `TopCat.Presheaf.extendByZeroSheafOfModules`: `j_!ℱ` for a sheaf of modules.

## Main results

* `TopCat.Presheaf.extendByZeroPresheafOfModules_presheaf`: the underlying abelian presheaf of
  `j_{p!}ℱ` is `j_{p!}` of the underlying abelian presheaf of `ℱ`.
* `TopCat.Presheaf.extendByZeroPresheafOfModules_smul_of_le`: the multiplication on sections
  over an open `V ⊆ U`.
* `TopCat.Presheaf.extendByZeroSheafOfModules_val_presheaf`: the underlying abelian sheaf of
  `j_!ℱ` is `j_!` of the underlying abelian sheaf of `ℱ`.
* `TopCat.Presheaf.toExtendByZeroSheafOfModules`: the sheafification map `j_{p!}ℱ ⟶ j_!ℱ` is
  `𝒪`-linear.
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace TopCat.Presheaf

open ExtensionByInitial

namespace ExtensionByZeroModules

variable {X : TopCat.{w}} (U : Opens X)

/-- For an open `V` of `X`, the image under `j` of `j⁻¹ V` is contained in `V`. -/
lemma imF_map_le (V : Opens X) : (imF U).obj ((Opens.map U.inclusion').obj V) ≤ V := by
  rintro _ ⟨y, hy, rfl⟩
  exact hy

variable (O : TopCat.Presheaf RingCat.{u} X)

/-- The restriction `𝒪(V) → 𝒪|_U(j⁻¹ V) = 𝒪(j(j⁻¹ V))` of sections of the presheaf of rings. -/
noncomputable def restrRing (V : (Opens X)ᵒᵖ) :
    O.obj V ⟶ ((imF U).op ⋙ O).obj (op ((Opens.map U.inclusion').obj V.unop)) :=
  O.map (homOfLE (imF_map_le U V.unop)).op

/-- The restriction maps of `𝒪` are compatible with `restrRing`. -/
lemma restrRing_naturality {V' V : (Opens X)ᵒᵖ} (f : V' ⟶ V) :
    restrRing U O V' ≫ ((imF U).op ⋙ O).map
        ((Opens.map U.inclusion').map (homOfLE f.unop.le)).op =
      O.map f ≫ restrRing U O V := by
  simp only [restrRing, Functor.comp_map, Functor.op_map, ← Functor.map_comp]
  rfl

variable {U O} (F : PresheafOfModules.{v} ((imF U).op ⋙ O))

/-- The `𝒪(V)`-module structure on `ℱ(j⁻¹ V)`, through `𝒪(V) → 𝒪|_U(j⁻¹ V)`. -/
@[instance_reducible]
noncomputable def moduleSect (V : (Opens X)ᵒᵖ) :
    Module (O.obj V) (F.presheaf.obj (op ((Opens.map U.inclusion').obj V.unop))) :=
  Module.compHom _ (restrRing U O V).hom

/-- The multiplication of `moduleSect` is that of `ℱ` after restricting to `𝒪|_U(j⁻¹ V)`. -/
lemma smul_moduleSect (V : (Opens X)ᵒᵖ) (r : O.obj V)
    (x : F.presheaf.obj (op ((Opens.map U.inclusion').obj V.unop))) :
    @HSMul.hSMul _ _ _ (@instHSMul _ _ (moduleSect F V).toSMul) r x = restrRing U O V r • x :=
  rfl

/-- Transport of a module structure along an equality of abelian groups. -/
@[instance_reducible]
noncomputable def moduleOfEq {R : Type*} [Semiring R] {A B : AddCommGrpCat.{v}} (e : A = B)
    (_ : Module R A) : Module R B := by
  subst e; assumption

lemma smul_moduleOfEq {R : Type*} [Semiring R] {A B : AddCommGrpCat.{v}} (e : A = B)
    (inst : Module R A) (r : R) (m : B) :
    @HSMul.hSMul _ _ _ (@instHSMul _ _ (moduleOfEq e inst).toSMul) r m =
      eqToHom e (r • eqToHom e.symm m) := by
  subst e; rfl

/-- The sections of `j_{p!}ℱ` over an open `V ⊄ U` form a zero group. -/
lemma subsingleton_obj {V : (Opens X)ᵒᵖ} (hV : ¬ V.unop ≤ U) :
    Subsingleton ((extendByInitial U F.presheaf).obj V) :=
  AddCommGrpCat.subsingleton_of_isZero (isInitial_obj U F.presheaf hV).isZero

/-- The zero module structure on a subsingleton abelian group. -/
@[instance_reducible]
noncomputable def moduleOfSubsingleton (R : Type*) [Semiring R] (A : AddCommGrpCat.{v})
    [Subsingleton A] : Module R A where
  smul _ _ := 0
  one_smul _ := Subsingleton.elim _ _
  mul_smul _ _ _ := Subsingleton.elim _ _
  smul_zero _ := Subsingleton.elim _ _
  smul_add _ _ _ := Subsingleton.elim _ _
  add_smul _ _ _ := Subsingleton.elim _ _
  zero_smul _ := Subsingleton.elim _ _

open Classical in
/-- The `𝒪(V)`-module structure on the sections of `j_{p!}ℱ` over an open `V`: that of
`ℱ(j⁻¹ V)` if `V ⊆ U`, and the zero module structure otherwise. -/
@[instance_reducible]
noncomputable def moduleObj (V : (Opens X)ᵒᵖ) :
    Module (O.obj V) ((extendByInitial U F.presheaf).obj V) :=
  if hV : V.unop ≤ U then moduleOfEq (obj_of_le U F.presheaf hV).symm (moduleSect F V)
  else
    haveI := subsingleton_obj F hV
    moduleOfSubsingleton _ _

/-- On an open `V ⊆ U`, the multiplication of `𝒪(V)` on `j_{p!}ℱ(V) = ℱ(j⁻¹ V)` is that of
`ℱ`, through the restriction `𝒪(V) → 𝒪|_U(j⁻¹ V)`. -/
lemma smul_moduleObj_of_le {V : (Opens X)ᵒᵖ} (hV : V.unop ≤ U) (r : O.obj V)
    (m : (extendByInitial U F.presheaf).obj V) :
    @HSMul.hSMul _ _ _ (@instHSMul _ _ (moduleObj F V).toSMul) r m =
      eqToHom (obj_of_le U F.presheaf hV).symm
        (letI := moduleSect F V; r • eqToHom (obj_of_le U F.presheaf hV) m) := by
  rw [moduleObj, dite_eq_left hV, smul_moduleOfEq]

/-- A semilinear map between transported modules is semilinear. -/
lemma map_smul_aux {R R' : Type*} [Semiring R] [Semiring R'] {A' B' A B : AddCommGrpCat.{v}}
    (e1 : A' = B') (e2 : A = B) (i1 : Module R B') (i2 : Module R' B) (σ : R → R')
    (φ : B' ⟶ B) (hφ : ∀ (r : R) (x : B'), φ (r • x) = σ r • φ x) (r : R) (m : A') :
    (eqToHom e1 ≫ φ ≫ eqToHom e2.symm)
        (@HSMul.hSMul _ _ _ (@instHSMul _ _ (moduleOfEq e1.symm i1).toSMul) r m) =
      @HSMul.hSMul _ _ _ (@instHSMul _ _ (moduleOfEq e2.symm i2).toSMul) (σ r)
        ((eqToHom e1 ≫ φ ≫ eqToHom e2.symm) m) := by
  subst e1 e2
  exact hφ r m

/-- The restriction maps of `ℱ` are semilinear for the `𝒪`-module structures `moduleSect`. -/
lemma presheaf_map_smul {V' V : (Opens X)ᵒᵖ} (f : V' ⟶ V) (r : O.obj V')
    (x : F.presheaf.obj (op ((Opens.map U.inclusion').obj V'.unop))) :
    F.presheaf.map ((Opens.map U.inclusion').map (homOfLE f.unop.le)).op
        (@HSMul.hSMul _ _ _ (@instHSMul _ _ (moduleSect F V').toSMul) r x) =
      @HSMul.hSMul _ _ _ (@instHSMul _ _ (moduleSect F V).toSMul) (O.map f r)
        (F.presheaf.map ((Opens.map U.inclusion').map (homOfLE f.unop.le)).op x) := by
  have h2 : restrRing U O V (O.map f r) = ((imF U).op ⋙ O).map
      ((Opens.map U.inclusion').map (homOfLE f.unop.le)).op (restrRing U O V' r) := by
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, restrRing_naturality]
  rw [smul_moduleSect, smul_moduleSect, h2]
  exact PresheafOfModules.map_smul F _ _ x

attribute [local instance] moduleObj in
/-- The restriction maps of `j_{p!}ℱ` are semilinear. -/
lemma map_smul {V' V : (Opens X)ᵒᵖ} (f : V' ⟶ V) (r : O.obj V')
    (m : (extendByInitial U F.presheaf).obj V') :
    (extendByInitial U F.presheaf).map f (r • m) =
      O.map f r • (extendByInitial U F.presheaf).map f m := by
  by_cases hV' : V'.unop ≤ U
  · have hV : V.unop ≤ U := f.unop.le.trans hV'
    rw [moduleObj, moduleObj, dite_eq_left hV', dite_eq_left hV, extendByInitial_map,
      ExtensionByInitial.map, dite_eq_left hV']
    exact map_smul_aux (obj_of_le U F.presheaf hV') (obj_of_le U F.presheaf hV)
      (moduleSect F V') (moduleSect F V) (O.map f) _ (presheaf_map_smul F f) r m
  · have := subsingleton_obj F hV'
    rw [Subsingleton.elim m 0, smul_zero, map_zero, smul_zero]

end ExtensionByZeroModules

open ExtensionByZeroModules

variable {X : TopCat.{w}} {U : Opens X} {O : TopCat.Presheaf RingCat.{u} X}

attribute [local instance] moduleObj in
/-- **Extension by zero of a presheaf of modules** (Stacks 00A4 (5)). Let `𝒪` be a presheaf of
rings on `X` and `ℱ` a presheaf of `𝒪|_U`-modules, where `𝒪|_U` is the presheaf `W ↦ 𝒪(j(W))`
on `U`. The extension by zero `j_{p!}ℱ` is the presheaf of `𝒪`-modules which is equal to the
extension by zero `j_{p!}ℱ` of the underlying abelian presheaf of `ℱ`
(`extendByZeroPresheafOfModules_presheaf`), endowed with the multiplication
`𝒪 × j_{p!}ℱ → j_{p!}ℱ`: over an open `V ⊆ U` a section of `𝒪` acts on `ℱ(j⁻¹ V)` through
its restriction to `𝒪|_U(j⁻¹ V)` (`extendByZeroPresheafOfModules_smul_of_le`), and over an open
`V ⊄ U` the sections form the zero module. -/
@[stacks 00A4 "(5)"]
noncomputable def extendByZeroPresheafOfModules (F : PresheafOfModules.{v} ((imF U).op ⋙ O)) :
    PresheafOfModules.{v} O :=
  letI : ∀ V, Module (O.obj V) ((extendByInitial U F.presheaf).obj V) := fun V ↦ moduleObj F V
  PresheafOfModules.ofPresheaf (extendByInitial U F.presheaf)
    (fun _ _ f r m ↦ map_smul F f r m)

/-- The underlying abelian presheaf of `j_{p!}ℱ` is the extension by zero of the underlying
abelian presheaf of `ℱ`. -/
lemma extendByZeroPresheafOfModules_presheaf (F : PresheafOfModules.{v} ((imF U).op ⋙ O)) :
    (extendByZeroPresheafOfModules F).presheaf = extendByInitial U F.presheaf :=
  rfl

/-- Over an open `V ⊆ U`, a section `r` of `𝒪` acts on `j_{p!}ℱ(V) = ℱ(j⁻¹ V)` as its
restriction to `𝒪|_U(j⁻¹ V)`. -/
lemma extendByZeroPresheafOfModules_smul_of_le (F : PresheafOfModules.{v} ((imF U).op ⋙ O))
    {V : (Opens X)ᵒᵖ} (hV : V.unop ≤ U) (r : O.obj V)
    (m : (extendByZeroPresheafOfModules F).obj V) :
    r • m =
      eqToHom (obj_of_le U F.presheaf hV).symm
        (restrRing U O V r • eqToHom (obj_of_le U F.presheaf hV) m) :=
  smul_moduleObj_of_le F hV r m

section Sheaf

variable {X : TopCat.{u}} {U : Opens X} (O : TopCat.Sheaf RingCat.{u} X)

/-- **Extension by zero of a sheaf of modules** (Stacks 00A4 (6)). Let `𝒪` be a sheaf of rings
on `X` and `ℱ` a sheaf of `𝒪|_U`-modules. The extension by zero `j_!ℱ` is the sheaf of
`𝒪`-modules which is equal to the extension by zero `j_!ℱ` of the underlying abelian sheaf of
`ℱ`, i.e. the sheafification of `j_{p!}ℱ` (`extendByZeroSheafOfModules_val_presheaf`), endowed
with the multiplication `𝒪 × j_!ℱ → j_!ℱ` induced by that of `j_{p!}ℱ`: the sheafification map
`j_{p!}ℱ ⟶ j_!ℱ` is `𝒪`-linear (`toExtendByZeroSheafOfModules`). -/
@[stacks 00A4 "(6)"]
noncomputable def extendByZeroSheafOfModules
    (F : SheafOfModules.{u} ((Opens.sheafRestrict U).obj O)) :
    SheafOfModules.{u} O :=
  PresheafOfModules.sheafify (𝟙 O.obj)
    (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
      (extendByZeroPresheafOfModules (O := O.obj) F.val).presheaf)

/-- The underlying abelian sheaf of `j_!ℱ` is the sheafification of the extension by zero of the
underlying abelian presheaf of `ℱ`. -/
lemma extendByZeroSheafOfModules_val_presheaf
    (F : SheafOfModules.{u} ((Opens.sheafRestrict U).obj O)) :
    (extendByZeroSheafOfModules O F).val.presheaf =
      ((extendByInitialSheafify U).obj F.val.presheaf).obj :=
  rfl

/-- The sheafification map `j_{p!}ℱ ⟶ j_!ℱ`, a morphism of presheaves of `𝒪`-modules. -/
noncomputable def toExtendByZeroSheafOfModules
    (F : SheafOfModules.{u} ((Opens.sheafRestrict U).obj O)) :
    extendByZeroPresheafOfModules (O := O.obj) F.val ⟶
      (PresheafOfModules.restrictScalars (𝟙 O.obj)).obj (extendByZeroSheafOfModules O F).val :=
  PresheafOfModules.toSheafify (𝟙 O.obj) _

/-- The underlying map of abelian presheaves of `j_{p!}ℱ ⟶ j_!ℱ` is the sheafification map. -/
lemma toPresheaf_map_toExtendByZeroSheafOfModules
    (F : SheafOfModules.{u} ((Opens.sheafRestrict U).obj O)) :
    (PresheafOfModules.toPresheaf O.obj).map (toExtendByZeroSheafOfModules O F) =
      CategoryTheory.toSheafify (Opens.grothendieckTopology X)
        (extendByInitial U F.val.presheaf) :=
  rfl

end Sheaf

end TopCat.Presheaf
