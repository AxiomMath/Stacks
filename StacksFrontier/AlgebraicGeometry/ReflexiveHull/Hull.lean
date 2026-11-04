module

public import StacksFrontier.AlgebraicGeometry.Reflexive.DoubleDual
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The reflexive hull of a module on a scheme

The *reflexive hull* `F⁎⁎` of an `𝒪_X`-module is its double internal-Hom dual, and the
canonical map `F ⟶ F⁎⁎` is the evaluation map `toDoubleDual`. This file packages that pair in
the form the Stacks Project specifies it, namely by the defining formula

> the component of `j f` at the terminal object of the slice site over `U` sends a local
> functional `lam` on `F|_U` to its value at `f`,

and proves that the formula *determines* the map: a morphism `F ⟶ F⁎⁎` satisfying it is
`toDoubleDual F`. Consequently reflexivity of `F` in the sense of `IsReflexive` — the
invertibility of `toDoubleDual F` — is reflexivity in the sense of the canonical map specified
by the formula, however that map happens to be constructed.

## Main definitions

* `reflexiveHull F`: the reflexive hull `F⁎⁎ = (F^∨)^∨`.
* `toReflexiveHull F`: the canonical map `F ⟶ F⁎⁎`, bundled with the defining formula.

## Main results

* `eq_toDoubleDual_of_val_app_apply`: the formula determines the canonical map.
* `isReflexive_iff_isIso`: a morphism satisfying the formula is invertible exactly when `F` is
  reflexive.

## Implementation notes

The dual used throughout is `Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf`, whose
underlying presheaf is literally the internal-Hom presheaf `internalHom` of Tag 03EM, so the
reflexive hull is the same object as the one obtained by iterating the internal-Hom dual of
Tag 0FNV; no comparison isomorphism intervenes.

The defining formula is imposed only at the terminal object `Over.mk (𝟙 U)` of the slice site
over each open `U`, which is the form in which the Stacks Project states it; by naturality it
determines the value of a section of `F⁎⁎` at every object of the slice site.

Neither coherence of `F` nor local Noetherianity of `X` is used: the hull, the canonical map
and the reflexivity predicate exist for an arbitrary module on an arbitrary scheme.

## References

* [Stacks Project, Tag 0AVU](https://stacks.math.columbia.edu/tag/0AVU)
* [Stacks Project, Tag 0FNV](https://stacks.math.columbia.edu/tag/0FNV)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.ReflexiveModules

variable {X : Scheme.{u}}

/-- The reflexive hull `F⁎⁎` of a module on a scheme: the dual of its dual. -/
@[stacks 0AVU "reflexive hull", sga "3 VIB 13.1"]
public noncomputable abbrev reflexiveHull (F : X.Modules) : X.Modules :=
  dualSheaf (dualSheaf F)

/-- The canonical map `F ⟶ F⁎⁎` to the reflexive hull, bundled with the formula that
characterizes it: over an open `U` it sends a local section `f` to the functional on `F^∨|_U`
whose component at the terminal object of the slice site over `U` is evaluation at `f`. -/
@[stacks 0AVU "canonical map to the reflexive hull"]
public noncomputable def toReflexiveHull (F : X.Modules) :
    { j : F ⟶ reflexiveHull F //
      ∀ (U : X.Opens) (f : Γ(F, U)) (lam : Γ(dualSheaf F, U)),
        (((j.val.app (op U)).hom f).app (op (Over.mk (𝟙 U)))).hom lam =
          (lam.app (op (Over.mk (𝟙 U)))).hom f } :=
  ⟨toDoubleDual F, toDoubleDual_val_app_apply F⟩

/-- The underlying morphism of the bundled canonical map is `toDoubleDual`. -/
@[simp]
public theorem toReflexiveHull_val (F : X.Modules) :
    (toReflexiveHull F).1 = toDoubleDual F :=
  rfl

/-- One section at a time: a morphism to the reflexive hull satisfying the defining formula
agrees with `toDoubleDual F` on every object of every slice site. -/
private theorem dualPairing_eq_of_val_app_apply (F : X.Modules) (j : F ⟶ reflexiveHull F)
    (hj : ∀ (U : X.Opens) (f : Γ(F, U)) (lam : Γ(dualSheaf F, U)),
      (((j.val.app (op U)).hom f).app (op (Over.mk (𝟙 U)))).hom lam =
        (lam.app (op (Over.mk (𝟙 U)))).hom f)
    (U : X.Opens) (f : Γ(F, U)) (W : Over U) (lam : Γ(dualSheaf F, W.left)) :
    dualPairing (dualSheaf F) ((j.val.app (op U)).hom f) W lam =
      dualPairing (dualSheaf F) (((toDoubleDual F).val.app (op U)).hom f) W lam := by
  have hVU : W.left ≤ U := leOfHom W.hom
  have hmap : dualPairing (dualSheaf F) ((j.val.app (op U)).hom f) W lam =
      dualPairing (dualSheaf F)
        ((reflexiveHull F).val.presheaf.map (homOfLE hVU).op ((j.val.app (op U)).hom f))
        (Over.mk (𝟙 W.left)) lam :=
    (dualPairing_map (dualSheaf F) hVU ((j.val.app (op U)).hom f) (Over.mk (𝟙 W.left)) lam).symm
  have hrhs : dualPairing (dualSheaf F) (((toDoubleDual F).val.app (op U)).hom f) W lam =
      (lam.app (op (Over.mk (𝟙 W.left)))).hom ((F.val.presheaf.map W.hom.op) f) := rfl
  have hnat : ((j.val.app (op W.left)).hom ((F.val.presheaf.map (homOfLE hVU).op) f)) =
      ((reflexiveHull F).val.presheaf.map (homOfLE hVU).op) ((j.val.app (op U)).hom f) :=
    PresheafOfModules.naturality_apply j.val (homOfLE hVU).op f
  have hWop : (W.hom).op = (homOfLE hVU).op := by congr 1
  have hj' := hj W.left ((F.val.presheaf.map (homOfLE hVU).op) f) lam
  refine hmap.trans ?_
  rw [← hnat, hrhs, hWop]
  exact hj'

/-- The defining formula determines the canonical map to the reflexive hull: a morphism
`F ⟶ F⁎⁎` which, over every open, sends a local section to evaluation at that section is
`toDoubleDual F`. -/
public theorem eq_toDoubleDual_of_val_app_apply (F : X.Modules) (j : F ⟶ reflexiveHull F)
    (hj : ∀ (U : X.Opens) (f : Γ(F, U)) (lam : Γ(dualSheaf F, U)),
      (((j.val.app (op U)).hom f).app (op (Over.mk (𝟙 U)))).hom lam =
        (lam.app (op (Over.mk (𝟙 U)))).hom f) :
    j = toDoubleDual F :=
  SheafOfModules.hom_ext <| PresheafOfModules.hom_ext fun ⟨U⟩ => ModuleCat.hom_ext <|
    LinearMap.ext fun f => dualPairing_ext (dualPairing_eq_of_val_app_apply F j hj U f)

/-- Reflexivity of `F` is invertibility of any morphism `F ⟶ F⁎⁎` satisfying the defining formula
of the canonical map. -/
@[stacks 0AVU "reflexive predicate"]
public theorem isReflexive_iff_isIso (F : X.Modules) (j : F ⟶ reflexiveHull F)
    (hj : ∀ (U : X.Opens) (f : Γ(F, U)) (lam : Γ(dualSheaf F, U)),
      (((j.val.app (op U)).hom f).app (op (Over.mk (𝟙 U)))).hom lam =
        (lam.app (op (Over.mk (𝟙 U)))).hom f) :
    IsReflexive F ↔ IsIso j := by
  rw [eq_toDoubleDual_of_val_app_apply F j hj]
  exact Iff.rfl

/-- Reflexivity is invertibility of the bundled canonical map `toReflexiveHull`. -/
public theorem isReflexive_iff_isIso_toReflexiveHull (F : X.Modules) :
    IsReflexive F ↔ IsIso (toReflexiveHull F).1 :=
  Iff.rfl

end Stacks.AlgebraicGeometry.ReflexiveModules
