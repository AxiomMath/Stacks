module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.Reflexive.Basic

/-!
# The canonical map to the double dual, and reflexive modules

For an `𝒪_X`-module `F` on a scheme, the canonical evaluation map `j : F ⟶ F^∨∨` sends a local
section `f` of `F` over `U` to the morphism `F^∨|_U ⟶ 𝒪_U` which evaluates a local functional
at `f`.  The module `F` is *reflexive* when `j` is an isomorphism. A reflexive module on an
integral scheme is torsion free.

## Main definitions

* `evalHom F f`: evaluation at the local section `f`, a morphism `F^∨|_U ⟶ 𝒪_U`.
* `toDoubleDual F`: the canonical map `F ⟶ F^∨∨`, with its defining local formula
  `toDoubleDual_dualPairing`.
* `IsReflexive F`: the canonical map `toDoubleDual F` is an isomorphism.

## Main results

* `isTorsionFree_of_isReflexive`: a reflexive module on an integral scheme is torsion free.
* `isTorsionFree_of_isReflexive_of_isLocallyNoetherian`: the same statement for an integral
  locally Noetherian scheme.

## Implementation notes

The evaluation map is constructed directly, not through the tensor--internal-Hom adjunction:
over an open `U` and at an object `W` of the slice site over `U`, the component of
`toDoubleDual F f` sends a functional `lam` on `F|_{W.left}` to `lam` evaluated at the
restriction of `f`.  Reflexivity is stated using this specific map, not the existence of some
isomorphism with the double dual.

## References

* [Stacks Project, Tag 0AVU](https://stacks.math.columbia.edu/tag/0AVU)
* [Stacks Project, Tag 0AY2](https://stacks.math.columbia.edu/tag/0AY2)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.ReflexiveModules

variable {X : Scheme.{u}}

/-- The value at a local functional `lam` on `F` over `V` of evaluation at a local section `x`
of `F` over `V`. -/
public noncomputable def evalAt (F : X.Modules) {V : X.Opens} (lam : Γ(dualSheaf F, V))
    (x : Γ(F, V)) : Γ(X, V) :=
  (lam.app (op (Over.mk (𝟙 V)))).hom x

/-- Evaluation is additive in the functional. -/
public theorem evalAt_add (F : X.Modules) {V : X.Opens} (lam mu : Γ(dualSheaf F, V))
    (x : Γ(F, V)) : evalAt F (lam + mu) x = evalAt F lam x + evalAt F mu x :=
  rfl

/-- Evaluation is linear in the functional. -/
public theorem evalAt_smul (F : X.Modules) {V : X.Opens} (a : Γ(X, V))
    (lam : Γ(dualSheaf F, V)) (x : Γ(F, V)) : evalAt F (a • lam) x = a • evalAt F lam x := by
  have h : evalAt F (a • lam) x = X.presheaf.map (𝟙 (op V)) a • evalAt F lam x := rfl
  rw [h, X.presheaf.map_id]
  rfl

/-- Evaluation is additive in the section. -/
public theorem evalAt_add_right (F : X.Modules) {V : X.Opens} (lam : Γ(dualSheaf F, V))
    (x y : Γ(F, V)) : evalAt F lam (x + y) = evalAt F lam x + evalAt F lam y :=
  (lam.app (op (Over.mk (𝟙 V)))).hom.map_add x y

/-- Evaluation is linear in the section. -/
public theorem evalAt_smul_right (F : X.Modules) {V : X.Opens} (a : Γ(X, V))
    (lam : Γ(dualSheaf F, V)) (x : Γ(F, V)) : evalAt F lam (a • x) = a • evalAt F lam x :=
  (lam.app (op (Over.mk (𝟙 V)))).hom.map_smul a x

/-- Compatibility of evaluation with restriction. -/
public theorem evalAt_map (F : X.Modules) {V V' : X.Opens} (hle : V' ≤ V)
    (lam : Γ(dualSheaf F, V)) (x : Γ(F, V)) :
    evalAt F ((dualSheaf F).presheaf.map (homOfLE hle).op lam)
        (F.presheaf.map (homOfLE hle).op x) =
      X.presheaf.map (homOfLE hle).op (evalAt F lam x) :=
  dualPairing_naturality F lam
    (Over.homMk (homOfLE hle) (Subsingleton.elim _ _) :
      (Over.mk ((𝟙 V' : V' ⟶ V') ≫ homOfLE hle) : Over V) ⟶ Over.mk (𝟙 V)) x

/-- Evaluation at a local section `f` of `F` over `U`, as a morphism `F^∨|_U ⟶ 𝒪_U` of
`𝒪_U`-modules: at an object `W` of the slice site over `U` it sends a functional `lam` on
`F|_{W.left}` to the value of `lam` at the restriction of `f`. -/
public noncomputable def evalHom (F : X.Modules) {U : X.Opens} (f : Γ(F, U)) :
    (restrFun X.sheaf.obj U).obj (dualSheaf F).val ⟶
      (restrFun X.sheaf.obj U).obj (SheafOfModules.unit (structureSheaf X.sheaf)).val where
  app W := ModuleCat.homAddEquiv.symm
    { toFun := fun lam => evalAt F (V := W.unop.left) lam (F.presheaf.map W.unop.hom.op f)
      map_add' := fun lam mu => evalAt_add F lam mu _
      map_smul' := fun a lam => evalAt_smul F a lam _ }
  naturality {W W'} g := by
    refine ModuleCat.hom_ext (LinearMap.ext fun lam => ?_)
    have hle : W'.unop.left ≤ W.unop.left := leOfHom g.unop.left
    have h3 : F.presheaf.map (homOfLE hle).op (F.presheaf.map W.unop.hom.op f) =
        F.presheaf.map W'.unop.hom.op f := by
      rw [← F.presheaf.map_comp_apply]
      congr 1
    change evalAt F (V := W'.unop.left)
        ((dualSheaf F).presheaf.map (homOfLE hle).op lam) (F.presheaf.map W'.unop.hom.op f) =
      X.presheaf.map (homOfLE hle).op
        (evalAt F (V := W.unop.left) lam (F.presheaf.map W.unop.hom.op f))
    rw [← h3]
    exact evalAt_map F hle lam (F.presheaf.map W.unop.hom.op f)

/-- Evaluation at a local section, read off on components. -/
public theorem evalHom_app (F : X.Modules) {U : X.Opens} (f : Γ(F, U)) (W : Over U)
    (lam : Γ(dualSheaf F, W.left)) :
    ((evalHom F f).app (op W)).hom lam =
      evalAt F (V := W.left) lam (F.presheaf.map W.hom.op f) :=
  rfl

/-- Two local sections of a dual module with the same values agree. -/
public theorem dualPairing_ext {F : X.Modules} {U : X.Opens} {t t' : Γ(dualSheaf F, U)}
    (h : ∀ (W : Over U) (x : Γ(F, W.left)), dualPairing F t W x = dualPairing F t' W x) :
    t = t' :=
  PresheafOfModules.hom_ext fun W => ModuleCat.hom_ext (LinearMap.ext (h W.unop))

/-- Evaluation at a local section is compatible with restriction of the section. -/
public theorem evalHom_restrict (F : X.Modules) {U V : X.Opens} (hle : V ≤ U) (f : Γ(F, U)) :
    (evalHom F (F.presheaf.map (homOfLE hle).op f) : Γ(dualSheaf (dualSheaf F), V)) =
      (dualSheaf (dualSheaf F)).presheaf.map (homOfLE hle).op
        (evalHom F f : Γ(dualSheaf (dualSheaf F), U)) := by
  refine dualPairing_ext (F := dualSheaf F) (fun W lam => ?_)
  refine Eq.trans ?_ (dualPairing_map (dualSheaf F) hle
    (evalHom F f : Γ(dualSheaf (dualSheaf F), U)) W lam).symm
  change evalAt F (V := W.left) lam
      (F.presheaf.map W.hom.op (F.presheaf.map (homOfLE hle).op f)) =
    evalAt F (V := W.left) lam (F.presheaf.map (W.hom ≫ homOfLE hle).op f)
  rw [← F.presheaf.map_comp_apply]
  rfl

/-- The canonical evaluation map `j : F ⟶ F^∨∨` of a module on a scheme. -/
public noncomputable def toDoubleDual (F : X.Modules) : F ⟶ dualSheaf (dualSheaf F) where
  val :=
    { app := fun U => ModuleCat.homAddEquiv.symm
        { toFun := fun f => evalHom F (U := U.unop) f
          map_add' := fun f g => by
            refine PresheafOfModules.hom_ext fun W =>
              ModuleCat.hom_ext (LinearMap.ext fun lam => ?_)
            have h1 : F.presheaf.map W.unop.hom.op (f + g) =
                F.presheaf.map W.unop.hom.op f + F.presheaf.map W.unop.hom.op g :=
              map_add _ _ _
            have h2 := evalAt_add_right F (V := W.unop.left) lam
              (F.presheaf.map W.unop.hom.op f) (F.presheaf.map W.unop.hom.op g)
            change evalAt F (V := W.unop.left) lam
                (F.presheaf.map W.unop.hom.op (f + g)) = _
            rw [h1, h2]
            rfl
          map_smul' := fun a f => by
            refine PresheafOfModules.hom_ext fun W =>
              ModuleCat.hom_ext (LinearMap.ext fun lam => ?_)
            have h1 : F.presheaf.map W.unop.hom.op (a • f) =
                X.presheaf.map W.unop.hom.op a • F.presheaf.map W.unop.hom.op f :=
              Scheme.Modules.map_smul F _ a f
            have h2 := evalAt_smul_right F (X.presheaf.map W.unop.hom.op a) lam
              (F.presheaf.map W.unop.hom.op f)
            change evalAt F (V := W.unop.left) lam
                (F.presheaf.map W.unop.hom.op (a • f)) = _
            rw [h1, h2]
            rfl }
      naturality := fun {U V} i => by
        refine ModuleCat.hom_ext (LinearMap.ext fun f => ?_)
        have hle : V.unop ≤ U.unop := leOfHom i.unop
        have hi : i = (homOfLE hle).op := Subsingleton.elim _ _
        subst hi
        exact evalHom_restrict F hle f }

/-- The defining formula for the canonical map to the double dual: on sections over `U` it
sends `f` to evaluation at `f`. -/
public theorem toDoubleDual_dualPairing (F : X.Modules) {U : X.Opens} (f : Γ(F, U))
    (W : Over U) (lam : Γ(dualSheaf F, W.left)) :
    dualPairing (dualSheaf F) (Scheme.Modules.Hom.app (toDoubleDual F) U f) W lam =
      evalAt F (V := W.left) lam (F.presheaf.map W.hom.op f) :=
  rfl

/-- The component of `j f` at the terminal object of the slice site over `U` evaluates a local
functional at `f`. -/
public theorem toDoubleDual_val_app_apply (F : X.Modules) (U : X.Opens) (f : Γ(F, U))
    (lam : Γ(dualSheaf F, U)) :
    ((((toDoubleDual F).val.app (op U)).hom f).app (op (Over.mk (𝟙 U)))).hom lam =
      (lam.app (op (Over.mk (𝟙 U)))).hom f := by
  change evalAt F (V := U) lam (F.presheaf.map (𝟙 (op U)) f) = _
  rw [F.presheaf.map_id]
  rfl

/-- A module on a scheme is *reflexive* if the canonical map to its double dual is an
isomorphism. -/
public def IsReflexive (F : X.Modules) : Prop := IsIso (toDoubleDual F)

/-- The canonical map of a reflexive module is injective on sections. -/
public theorem injective_toDoubleDual_app {F : X.Modules} (hF : IsReflexive F) (U : X.Opens) :
    Function.Injective (Scheme.Modules.Hom.app (toDoubleDual F) U) := by
  have hiso : IsIso (toDoubleDual F) := hF
  have hcomp : Scheme.Modules.Hom.app (toDoubleDual F) U ≫
      Scheme.Modules.Hom.app (inv (toDoubleDual F)) U = 𝟙 _ := by
    rw [← Scheme.Modules.Hom.comp_app, IsIso.hom_inv_id, Scheme.Modules.Hom.id_app]
  refine Function.LeftInverse.injective
    (g := Scheme.Modules.Hom.app (inv (toDoubleDual F)) U) fun s => ?_
  simpa only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] using
    ConcreteCategory.congr_hom hcomp s

/-- A reflexive module on an integral scheme is torsion free. -/
@[stacks 0AY2 "part (1)"]
public theorem isTorsionFree_of_isReflexive [IsIntegral X] (F : X.Modules)
    (hF : IsReflexive F) : IsTorsionFree F :=
  isTorsionFree_of_injective_toDual (toDoubleDual F) (injective_toDoubleDual_app hF)

/-- A reflexive module on an integral locally Noetherian scheme is torsion free. -/
public theorem isTorsionFree_of_isReflexive_of_isLocallyNoetherian [IsIntegral X]
    [IsLocallyNoetherian X] (F : X.Modules) (hF : IsReflexive F) : IsTorsionFree F :=
  isTorsionFree_of_isReflexive F hF

end Stacks.AlgebraicGeometry.ReflexiveModules
