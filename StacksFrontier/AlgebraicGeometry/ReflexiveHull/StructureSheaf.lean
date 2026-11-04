module

public import StacksFrontier.AlgebraicGeometry.ReflexiveHull.Hull

/-!
# The structure sheaf is reflexive

The dual `𝒪_X^∨ = SheafHom(𝒪_X, 𝒪_X)` of the structure sheaf of a scheme is a copy of `𝒪_X`: a
local endomorphism of `𝒪_U` is multiplication by its value at `1`.  Consequently the canonical
map `𝒪_X ⟶ 𝒪_X^∨∨` is an isomorphism, so the structure sheaf is reflexive.

Neither integrality nor local Noetherianity of `X` is used; the result holds for an arbitrary
scheme.  This is the input "`𝒪_X` is reflexive" that [Stacks, Tag
0AY4](https://stacks.math.columbia.edu/tag/0AY4) needs in order to conclude that the dual of a
coherent module is reflexive.  The Stacks Project obtains it from the affine-local criterion of
Tag 0AY0; here it is proved directly from the defining formula of the dual, so no affine-local
comparison of `SheafHom` with an algebraic `Hom` module is involved.

## Main definitions

* `unitModule X`: the structure sheaf of `X` as a module over itself, at the type `X.Modules`.
* `oneSection X U`: the unit of `Γ(X, U)`, as a local section of `𝒪_X`.
* `unitFunctional X U`: the identity endomorphism of `𝒪_U`, as a local section of `𝒪_X^∨`.
* `dualDualUnit X`: evaluation at the identity functional, a morphism `𝒪_X^∨∨ ⟶ 𝒪_X`.

## Main results

* `eq_smul_unitFunctional`: a local functional on the structure sheaf is the multiple of the
  identity functional by its own value at `1`.  This is what makes `𝒪_X^∨` a copy of `𝒪_X`.
* `toDoubleDual_dualDualUnit` and `dualDualUnit_toDoubleDual`: `dualDualUnit X` is a two-sided
  inverse of the canonical map.
* `isReflexive_unit`: the structure sheaf of a scheme is reflexive.

## Implementation notes

The dual is `Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf`, whose sections over `U` are
the morphisms `𝒪_U ⟶ 𝒪_U` of `𝒪_U`-modules over the slice site, so `unitFunctional` is literally
an identity morphism and `dualPairing_unitFunctional` holds by definitional unfolding.

Reflexivity is proved by exhibiting a two-sided inverse of `toDoubleDual` rather than by
constructing the isomorphism `𝒪_X^∨ ≅ 𝒪_X` and transporting along it.  That avoids building the
multiplication morphism `𝒪_X ⟶ 𝒪_X^∨` as a morphism of sheaves of modules: only its value
formula is needed, and that is `eq_smul_unitFunctional`.

`unitModule` is an `abbrev`, and is load-bearing rather than cosmetic.
`Γ(SheafOfModules.unit (structureSheaf X.sheaf), U)` and `Γ(X, U)` are the same type, but
`structureSheaf X.sheaf` elaborates at `TopCat.Sheaf RingCat X.toPresheafedSpace` rather than at
`Sheaf (Opens.grothendieckTopology X) RingCat`, so without the `X.Modules` ascription neither the
`.presheaf` projection nor the module structure on sections is found by instance search.

## References

* [Stacks Project, Tag 0AVU](https://stacks.math.columbia.edu/tag/0AVU)
* [Stacks Project, Tag 0AY0](https://stacks.math.columbia.edu/tag/0AY0)
* [Stacks Project, Tag 0AY4](https://stacks.math.columbia.edu/tag/0AY4)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.ReflexiveModules

variable {X : Scheme.{u}}

/-- The structure sheaf of a scheme, as a module over itself, at the type `X.Modules`. -/
public noncomputable abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit (structureSheaf X.sheaf)

/-- The value of a local functional on a restricted section is the restriction of its value at
the terminal object of the slice site. -/
public theorem dualPairing_map_section (F : X.Modules) {U : X.Opens} (t : Γ(dualSheaf F, U))
    (W : Over U) (y : Γ(F, U)) :
    dualPairing F t W (F.presheaf.map W.hom.op y) =
      X.presheaf.map W.hom.op (evalAt F t y) := by
  have h := dualPairing_naturality F t
    (Over.homMk W.hom (Subsingleton.elim _ _) : W ⟶ Over.mk (𝟙 U)) y
  simp only [Over.homMk_left] at h
  exact h

variable (X) in
/-- The unit of `Γ(X, U)`, as a local section of the structure sheaf viewed as a module over
itself. -/
public noncomputable def oneSection (U : X.Opens) : Γ(unitModule X, U) := (1 : Γ(X, U))

variable (X) in
/-- The unit section restricts to the unit section. -/
@[simp] public theorem map_oneSection {U V : X.Opens} (i : V ⟶ U) :
    (unitModule X).presheaf.map i.op (oneSection X U) = oneSection X V :=
  map_one (X.presheaf.map i.op).hom

variable (X) in
/-- The identity endomorphism of `𝒪_U`, as a local section of the dual `𝒪_X^∨` over `U`. -/
public noncomputable def unitFunctional (U : X.Opens) : Γ(dualSheaf (unitModule X), U) :=
  𝟙 ((restrFun X.sheaf.obj U).obj (unitModule X).val)

variable (X) in
/-- The identity functional takes every local section to itself. -/
@[simp] public theorem dualPairing_unitFunctional (U : X.Opens) (W : Over U)
    (x : Γ(unitModule X, W.left)) :
    dualPairing (unitModule X) (unitFunctional X U) W x = x :=
  rfl

variable (X) in
/-- The identity functional restricts to the identity functional. -/
@[simp] public theorem map_unitFunctional {U V : X.Opens} (i : V ⟶ U) :
    (dualSheaf (unitModule X)).presheaf.map i.op (unitFunctional X U) = unitFunctional X V := by
  refine dualPairing_ext (F := unitModule X) (fun W x => ?_)
  have hle : V ≤ U := leOfHom i
  have hi : i = homOfLE hle := Subsingleton.elim _ _
  subst hi
  rw [dualPairing_map]
  rfl

/-- A local functional is linear over the sections of `𝒪_X` on the slice site. -/
private theorem dualPairing_smul_section (F : X.Modules) {U : X.Opens} (t : Γ(dualSheaf F, U))
    (W : Over U) (a : Γ(X, W.left)) (y : Γ(F, W.left)) :
    dualPairing F t W (a • y) = a * dualPairing F t W y :=
  (t.app (op W)).hom.map_smul a y

variable (X) in
/-- A local functional on the structure sheaf is multiplication by its value at `1`. -/
public theorem dualPairing_unit {U : X.Opens} (t : Γ(dualSheaf (unitModule X), U))
    (W : Over U) (x : Γ(X, W.left)) :
    dualPairing (unitModule X) t W x =
      x * dualPairing (unitModule X) t W (oneSection X W.left) :=
  have e : (x • oneSection X W.left : Γ(unitModule X, W.left)) = x := mul_one x
  (congrArg (dualPairing (unitModule X) t W) e).symm.trans
    (dualPairing_smul_section _ t W x _)

/-- The value of a local functional at a section restricting from the base is the restriction of
its value at the base section. -/
private theorem dualPairing_eq_of_map (F : X.Modules) {U : X.Opens} (t : Γ(dualSheaf F, U))
    (W : Over U) {y : Γ(F, U)} {y' : Γ(F, W.left)} (h : F.presheaf.map W.hom.op y = y') :
    dualPairing F t W y' = X.presheaf.map W.hom.op (evalAt F t y) :=
  h ▸ dualPairing_map_section F t W y

variable (X) in
/-- The value of a functional on the structure sheaf at the unit section, over an object of the
slice site, is the restriction of its value at the unit section over the base. -/
public theorem dualPairing_oneSection {U : X.Opens} (t : Γ(dualSheaf (unitModule X), U))
    (W : Over U) :
    dualPairing (unitModule X) t W (oneSection X W.left) =
      X.presheaf.map W.hom.op (evalAt (unitModule X) t (oneSection X U)) :=
  dualPairing_eq_of_map _ t W (map_oneSection X W.hom)

variable (X) in
/-- The value of a functional on `𝒪_X^∨` at the identity functional, over an object of the slice
site, is the restriction of its value at the identity functional over the base. -/
public theorem dualPairing_unitFunctional_section {U : X.Opens}
    (s : Γ(dualSheaf (dualSheaf (unitModule X)), U)) (W : Over U) :
    dualPairing (dualSheaf (unitModule X)) s W (unitFunctional X W.left) =
      X.presheaf.map W.hom.op (evalAt (dualSheaf (unitModule X)) s (unitFunctional X U)) :=
  dualPairing_eq_of_map _ s W (map_unitFunctional X W.hom)

variable (X) in
/-- **A functional on the structure sheaf is a multiple of the identity functional**, by its own
value at `1`.  This is the section-level form of the identification `𝒪_X^∨ = 𝒪_X`. -/
public theorem eq_smul_unitFunctional {U : X.Opens} (t : Γ(dualSheaf (unitModule X), U)) :
    t = evalAt (unitModule X) t (oneSection X U) • unitFunctional X U := by
  refine dualPairing_ext (F := unitModule X) (fun W x => ?_)
  rw [dualPairing_smul, dualPairing_unitFunctional, dualPairing_unit X t W x,
    dualPairing_oneSection X t W]
  exact mul_comm _ _

variable (X) in
/-- Evaluation at the identity functional, a morphism `𝒪_X^∨∨ ⟶ 𝒪_X`.  It is a two-sided inverse
of the canonical map `toDoubleDual`. -/
public noncomputable def dualDualUnit :
    dualSheaf (dualSheaf (unitModule X)) ⟶ unitModule X where
  val :=
    { app := fun U => ModuleCat.homAddEquiv.symm
        { toFun := fun s =>
            evalAt (dualSheaf (unitModule X)) (V := U.unop) s (unitFunctional X U.unop)
          map_add' := fun s s' => evalAt_add (dualSheaf (unitModule X)) s s' _
          map_smul' := fun a s => evalAt_smul (dualSheaf (unitModule X)) a s _ }
      naturality := fun {U V} i => by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro s
        have hle : V.unop ≤ U.unop := leOfHom i.unop
        have hi : i = (homOfLE hle).op := Subsingleton.elim _ _
        subst hi
        change evalAt (dualSheaf (unitModule X))
            ((dualSheaf (dualSheaf (unitModule X))).presheaf.map (homOfLE hle).op s)
            (unitFunctional X V.unop) = _
        rw [← map_unitFunctional X (homOfLE hle),
          evalAt_map (dualSheaf (unitModule X)) hle s]
        rfl }

variable (X) in
/-- Evaluation at the identity functional, read off on sections. -/
public theorem dualDualUnit_app {U : X.Opens} (s : Γ(dualSheaf (dualSheaf (unitModule X)), U)) :
    Scheme.Modules.Hom.app (dualDualUnit X) U s =
      evalAt (dualSheaf (unitModule X)) s (unitFunctional X U) :=
  rfl

variable (X) in
/-- Evaluation at the identity functional retracts the canonical map of the structure sheaf: a
function is recovered from the functional "evaluate at this function" by evaluating at the
identity. -/
public theorem toDoubleDual_dualDualUnit :
    toDoubleDual (unitModule X) ≫ dualDualUnit X = 𝟙 (unitModule X) := by
  refine Scheme.Modules.hom_ext _ _ (fun U => ?_)
  ext a
  exact toDoubleDual_val_app_apply (unitModule X) U a (unitFunctional X U)

variable (X) in
/-- Evaluation at the identity functional is a section of the canonical map of the structure
sheaf.  This is where `eq_smul_unitFunctional` is used: a functional on `𝒪_X^∨` is determined by
its value at the identity functional, because every local functional is a multiple of that
one. -/
public theorem dualDualUnit_toDoubleDual :
    dualDualUnit X ≫ toDoubleDual (unitModule X) =
      𝟙 (dualSheaf (dualSheaf (unitModule X))) := by
  refine Scheme.Modules.hom_ext _ _ (fun U => ?_)
  ext s
  rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app]
  simp only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply]
  refine dualPairing_ext (F := dualSheaf (unitModule X)) (fun W lam => ?_)
  have hL : dualPairing (dualSheaf (unitModule X))
      (Scheme.Modules.Hom.app (toDoubleDual (unitModule X)) U
        (Scheme.Modules.Hom.app (dualDualUnit X) U s)) W lam =
      X.presheaf.map W.hom.op (evalAt (dualSheaf (unitModule X)) s (unitFunctional X U)) *
        evalAt (unitModule X) lam (oneSection X W.left) := by
    rw [toDoubleDual_dualPairing]
    exact dualPairing_unit X lam (Over.mk (𝟙 W.left)) _
  have hR : dualPairing (dualSheaf (unitModule X)) s W lam =
      evalAt (unitModule X) lam (oneSection X W.left) *
        X.presheaf.map W.hom.op (evalAt (dualSheaf (unitModule X)) s (unitFunctional X U)) := by
    conv_lhs => rw [eq_smul_unitFunctional X lam]
    rw [dualPairing_smul_section, dualPairing_unitFunctional_section]
  rw [hL, hR]
  exact mul_comm _ _

/-- **The structure sheaf of a scheme is reflexive.**  Its dual is a copy of itself, by
`eq_smul_unitFunctional`, and evaluation at the identity functional inverts the canonical map.
Neither integrality nor local Noetherianity of the scheme is used. -/
public theorem isReflexive_unit (X : Scheme.{u}) : IsReflexive (unitModule X) :=
  ⟨⟨dualDualUnit X, toDoubleDual_dualDualUnit X, dualDualUnit_toDoubleDual X⟩⟩

end Stacks.AlgebraicGeometry.ReflexiveModules

end
