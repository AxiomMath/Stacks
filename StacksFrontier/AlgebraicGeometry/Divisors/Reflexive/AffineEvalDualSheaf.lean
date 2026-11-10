module

public import StacksFrontier.AlgebraicGeometry.Modules.AffineDualSheaf
public import StacksFrontier.AlgebraicGeometry.Reflexive.DoubleDual
import all StacksFrontier.AlgebraicGeometry.Modules.AffineInternalHomNatural

/-!
# Evaluation and the affine comparison for duals and reflexive hulls

On `Spec R` the dual of the sheaf associated to a module `M` of finite presentation is the
sheaf associated to the `R`-dual of `M`
(`AlgebraicGeometry.dualSheafTildeIso`), and for `R` Noetherian and `M` finite the reflexive
hull of `M^~` is the sheaf associated to `M^{∨∨}`
(`AlgebraicGeometry.reflexiveHullTildeIso`).  This file computes the inverse of the dual
comparison, read as a pairing, over every open, and shows that the reflexive-hull comparison
carries the canonical map to the double dual to the module-theoretic evaluation map.

## Main definitions

* `AlgebraicGeometry.evalSectionHom M m`: evaluation at the global section `m^~`, as a
  morphism `(M^~)^∨ ⟶ 𝒪_{Spec R}` of `𝒪_{Spec R}`-modules.

## Main results

* `AlgebraicGeometry.dualSheafTildeIso_inv_dualPairing`: the inverse of the dual comparison
  carries `φ^~` to the functional `φ^~` itself, i.e. its pairing against a local section of
  `M^~` over any open is the value of `tilde.map φ` there.
* `AlgebraicGeometry.dualSheafTildeIso_inv_evalSectionHom`: equivalently, evaluation at `m`
  pulled back along the comparison is `tilde.map` of evaluation at `m`.
* `AlgebraicGeometry.toDoubleDual_reflexiveHullTildeIso`: the canonical map to the double dual
  composed with the affine reflexive-hull comparison is the associated sheaf of evaluation,
  `j_{M^~} ≫ (reflexiveHullTildeIso R M).hom = tilde.map (Module.Dual.eval R M)`.

## References

* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
* [Stacks Project, Tag 0AVU](https://stacks.math.columbia.edu/tag/0AVU)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace AlgebraicGeometry

variable {R : CommRingCat.{u}}

/-! ### Evaluation at a global section -/

/-- Evaluation at the global section of `M^~` attached to `m : M`, as a morphism
`(M^~)^∨ ⟶ 𝒪_{Spec R}`: over an open `V` it sends a functional `lam` on `M^~|_V` to its value
at the restriction to `V` of `m`. -/
def evalSectionHom (M : ModuleCat.{u} R) (m : M) :
    dualSheaf (tilde M) ⟶ SheafOfModules.unit (Spec R).ringCatSheaf where
  val :=
    { app := fun V => ModuleCat.homAddEquiv.symm
        { toFun := fun lam => evalAt (tilde M) lam ((tilde.toOpen M V.unop).hom m)
          map_add' := fun lam mu => evalAt_add (tilde M) lam mu _
          map_smul' := fun a lam => evalAt_smul (tilde M) a lam _ }
      naturality := by
        intro V W i
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro lam
        have hle : W.unop ≤ V.unop := leOfHom i.unop
        have hi : i = (homOfLE hle).op := Subsingleton.elim _ _
        subst hi
        have h3 : (tilde M).presheaf.map (homOfLE hle).op ((tilde.toOpen M V.unop).hom m) =
            (tilde.toOpen M W.unop).hom m :=
          congrArg (fun g => g.hom m) (tilde.toOpen_res M V.unop W.unop (homOfLE hle))
        change evalAt (tilde M) ((dualSheaf (tilde M)).presheaf.map (homOfLE hle).op lam)
            ((tilde.toOpen M W.unop).hom m) =
          (Spec R).presheaf.map (homOfLE hle).op
            (evalAt (tilde M) lam ((tilde.toOpen M V.unop).hom m))
        rw [← h3]
        exact evalAt_map (tilde M) hle lam _ }

/-- On sections over `V`, `evalSectionHom M m` sends `lam` to its value at the restriction to `V`
of the global section attached to `m`. -/
theorem evalSectionHom_app (M : ModuleCat.{u} R) (m : M) (V : (Spec R).Opens)
    (lam : Γ(dualSheaf (tilde M), V)) :
    (evalSectionHom M m).val.app (op V) lam =
      evalAt (tilde M) lam ((tilde.toOpen M V).hom m) := rfl

/-! ### The inverse of the affine dual comparison -/

/-- `tilde.map f` on global sections sends `m^~` to `(f m)^~`. -/
private theorem tilde_map_app_toOpen_top {A B : ModuleCat.{u} R} (f : A ⟶ B) (a : A) :
    (tilde.map f).val.app (op ⊤) ((tilde.toOpen A ⊤).hom a) = (tilde.toOpen B ⊤).hom (f.hom a) :=
  congrArg (fun g => g.hom a) (tilde.toOpen_map_app f ⊤)

/-- The inverse of the affine dual comparison, over every open: the section of `(M^~)^∨` that
`(dualSheafTildeIso R M).inv` attaches to the global section `φ^~` of `(M^∨)^~` is the
functional `tilde.map φ`: its pairing against a local section of `M^~` over any open of the
slice site above `⊤` is the value of `tilde.map φ` there. -/
theorem dualSheafTildeIso_inv_dualPairing (M : ModuleCat.{u} R)
    [Module.FinitePresentation R M] (φ : Module.Dual R M)
    (W : Over (⊤ : (Spec R).Opens)) (x : Γ(tilde M, W.left)) :
    dualPairing (tilde M)
        ((dualSheafTildeIso R M).inv.val.app (op ⊤)
          ((tilde.toOpen (ModuleCat.of R (Module.Dual R M)) ⊤).hom φ)) W x =
      (tilde.map (ModuleCat.ofHom φ)).val.app (op W.left) x := by
  have hA := tilde_map_app_toOpen_top
    (ModuleCat.homLinearEquiv (M := M) (N := ModuleCat.of R R) (S := R)).toModuleIso.inv φ
  have hB := (internalHomTildeIso R M (ModuleCat.of R R)
    (sheafHomPackage (Spec R) (tilde M) (tilde (ModuleCat.of R R)))).inv_app_toOpen
      (ModuleCat.ofHom φ)
  have hC : dualPairing (tilde M)
        ((internalHomTildeIso R M (ModuleCat.of R R)
          (sheafHomPackage (Spec R) (tilde M) (tilde (ModuleCat.of R R)))).iso.inv.val.app (op ⊤)
          ((tilde.toOpen (ModuleCat.of R (M ⟶ ModuleCat.of R R)) ⊤).hom (ModuleCat.ofHom φ)))
        W x =
      (tilde.map (ModuleCat.ofHom φ)).val.app (op W.left) x :=
    congrArg (fun n : (tilde M).over (⊤ : (Spec R).Opens) ⟶
        (tilde (ModuleCat.of R R)).over (⊤ : (Spec R).Opens) =>
      (n.val.app (op W)).hom x) hB
  exact Eq.trans (congrArg (fun z => dualPairing (tilde M)
    ((internalHomTildeIso R M (ModuleCat.of R R)
      (sheafHomPackage (Spec R) (tilde M) (tilde (ModuleCat.of R R)))).iso.inv.val.app (op ⊤) z)
    W x) hA) hC

/-- Evaluation at `m`, pulled back along the affine dual comparison, is `tilde.map` of
evaluation at `m`. -/
theorem dualSheafTildeIso_inv_evalSectionHom (M : ModuleCat.{u} R)
    [Module.FinitePresentation R M] (m : M) :
    (dualSheafTildeIso R M).inv ≫ evalSectionHom M m =
      tilde.map (ModuleCat.ofHom ((Module.Dual.eval R M) m)) := by
  refine tilde_hom_ext_toOpen (fun φ => ?_)
  have hE := tilde_map_app_toOpen_top (ModuleCat.ofHom ((Module.Dual.eval R M) m)) φ
  refine Eq.trans ?_ hE.symm
  exact (dualSheafTildeIso_inv_dualPairing M φ (Over.mk (𝟙 (⊤ : (Spec R).Opens)))
    ((tilde.toOpen M ⊤).hom m)).trans
    (tilde_map_app_toOpen_top (ModuleCat.ofHom φ) m)

/-! ### The canonical map to the double dual -/

/-- For `R` Noetherian and `M` finite, the composite of `j : M^~ ⟶ (M^~)^{∨∨}` with
`AlgebraicGeometry.reflexiveHullTildeIso` is the associated sheaf of the module-theoretic
evaluation map `M ⟶ M^{∨∨}`. -/
theorem toDoubleDual_reflexiveHullTildeIso (R : CommRingCat.{u}) [IsNoetherianRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] :
    toDoubleDual (tilde M) ≫ (reflexiveHullTildeIso R M).hom =
      tilde.map (ModuleCat.ofHom (Module.Dual.eval R M)) := by
  have : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
  have : _root_.IsNoetherian R (Module.Dual R M) := isNoetherian_linearMap R R M
  have : Module.Finite R (Module.Dual R M) := Module.IsNoetherian.finite R _
  have : Module.FinitePresentation R (Module.Dual R M) :=
    Module.finitePresentation_of_finite R _
  rw [show (reflexiveHullTildeIso R M).hom =
      (dualIso (dualSheafTildeIso R M)).inv ≫
        (dualSheafTildeIso R (ModuleCat.of R (Module.Dual R M))).hom from rfl,
    ← Category.assoc, ← Iso.eq_comp_inv]
  refine tilde_hom_ext_toOpen (fun m => ?_)
  change (dualIso (dualSheafTildeIso R M)).inv.val.app (op ⊤)
      ((toDoubleDual (tilde M)).val.app (op ⊤) ((tilde.toOpen M ⊤).hom m)) =
    (dualSheafTildeIso R (ModuleCat.of R (Module.Dual R M))).inv.val.app (op ⊤)
      ((tilde.map (ModuleCat.ofHom (Module.Dual.eval R M))).val.app (op ⊤)
        ((tilde.toOpen M ⊤).hom m))
  rw [tilde_map_app_toOpen_top]
  refine dualPairing_ext (fun W σ => ?_)
  refine Eq.trans ?_
    (dualSheafTildeIso_inv_dualPairing (ModuleCat.of R (Module.Dual R M))
      (Module.Dual.eval R M m) W σ).symm
  have hres : (tilde M).presheaf.map W.hom.op ((tilde.toOpen M ⊤).hom m) =
      (tilde.toOpen M W.left).hom m :=
    congrArg (fun g => g.hom m) (tilde.toOpen_res M ⊤ W.left W.hom)
  refine Eq.trans (toDoubleDual_dualPairing (tilde M) ((tilde.toOpen M ⊤).hom m) W
    ((dualSheafTildeIso R M).inv.val.app (op W.left) σ)) ?_
  rw [hres]
  change (evalSectionHom M m).val.app (op W.left)
      ((dualSheafTildeIso R M).inv.val.app (op W.left) σ) = _
  exact congrArg (fun φ : tilde (ModuleCat.of R (Module.Dual R M)) ⟶
      SheafOfModules.unit (Spec R).ringCatSheaf => (φ.val.app (op W.left)).hom σ)
    (dualSheafTildeIso_inv_evalSectionHom M m)

end AlgebraicGeometry

end
