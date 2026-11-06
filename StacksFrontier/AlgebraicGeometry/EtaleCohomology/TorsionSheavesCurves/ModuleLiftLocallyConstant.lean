module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyConstantSerreClass
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleLiftComparisons
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ModuleFiltrationTransport

/-!
# An abelian sheaf killed by `ℓ` is a sheaf of `F_ℓ`-vector spaces

An abelian sheaf `G` on a site with `ℓ • 𝟙 G = 0` carries a unique structure of sheaf of
`ZMod ℓ`-modules, `Stacks.EtaleCohomology.zmodLift`, whose underlying abelian sheaf is `G` on the
nose. If `G` is finite locally constant, the lift is locally constant of finite type, which is the
hypothesis of Tag 0A3R. This is how the dévissage of Theorem 03SC, which is about abelian
sheaves, reaches Tag 0A3R, which is about sheaves of `F_ℓ`-vector spaces.

## Main definitions

* `Stacks.EtaleCohomology.zmodLift`: the sheaf of `ZMod ℓ`-modules on an abelian sheaf killed
  by `ℓ`.

## Main results

* `Stacks.EtaleCohomology.forgetZModZmodLiftIso`: its underlying abelian sheaf is the given one.
* `Stacks.EtaleCohomology.isFiniteTypeLocallyConstant_zmodLift`: finite local constancy passes
  to the lift.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

variable {ℓ : ℕ} {X : Scheme.{u}}

/-- The action of `ZMod ℓ` on an abelian sheaf killed by `ℓ`. -/
def zmodEndRingHom {C : Type*} [Category C] [Preadditive C] {A : C} (h : ℓ • 𝟙 A = 0) :
    ZMod ℓ →+* End A :=
  haveI : CharP (End A) (ringChar (End A)) := ringChar.charP _
  ZMod.castHom (ringChar.dvd (by rw [← nsmul_one]; exact End.ext h)) (End A)

/-- **The sheaf of `F_ℓ`-vector spaces on an abelian sheaf killed by `ℓ`.** -/
def zmodLift (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (h : ℓ • 𝟙 G = 0) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod ℓ)) :=
  Stacks.ModuleCatLift.sheafOfEndAction (ZMod ℓ) X.smallEtaleTopology G (zmodEndRingHom h)

/-- The abelian sheaf underlying the lift of `G` is `G`. -/
def forgetZModZmodLiftIso (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (h : ℓ • 𝟙 G = 0) : (forgetZMod ℓ X).obj (zmodLift G h) ≅ G :=
  Iso.refl _

/-- Every morphism commutes with the action of `ZMod ℓ` through any two ring maps to the
endomorphism rings, the action being by natural numbers. -/
theorem zmod_ringHom_comp_comm [NeZero ℓ] {C : Type*} [Category C] [Preadditive C] {A B : C}
    (φ : ZMod ℓ →+* End A) (ψ : ZMod ℓ →+* End B) (e : A ⟶ B) (a : ZMod ℓ) :
    (φ a).asHom ≫ e = e ≫ (ψ a).asHom := by
  rw [← ZMod.natCast_zmod_val a, map_natCast, map_natCast, ← nsmul_one, ← nsmul_one]
  show (a.val • 𝟙 A) ≫ e = e ≫ (a.val • 𝟙 B)
  rw [Preadditive.nsmul_comp, Preadditive.comp_nsmul, Category.id_comp, Category.comp_id]

/-- Sheafification of presheaves of `ZMod ℓ`-modules on the localized small étale sites. -/
instance hasSheafify_over_moduleCat_zmod (V : X.Etale) :
    HasSheafify (X.smallEtaleTopology.over V) (ModuleCat.{u + 1} (ZMod ℓ)) :=
  Stacks.ModuleSheaf.hasSheafify_over_moduleCat.{u + 1} _ _ V

/-- Postcomposition with the forgetful functor of `ZMod ℓ`-modules carries sheaves on the
localized small étale sites to sheaves. -/
instance hasSheafCompose_over_forget₂_zmod (V : X.Etale) :
    (X.smallEtaleTopology.over V).HasSheafCompose
      (forget₂ (ModuleCat.{u + 1} (ZMod ℓ)) AddCommGrpCat.{u + 1}) :=
  Stacks.ModuleSheaf.hasSheafCompose_forget₂.{u + 1} _ _

/-- **Finite local constancy passes to the lift**: a finite locally constant abelian sheaf
killed by `ℓ` is, as a sheaf of `ZMod ℓ`-modules, locally constant of finite type. On a piece of
a trivializing covering with constant value the finite group `E`, the constant value of the
lift is `E/ℓE`, whose constant sheaf is that of `E` because the latter is killed by `ℓ`. -/
theorem isFiniteTypeLocallyConstant_zmodLift [NeZero ℓ]
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (h : ℓ • 𝟙 G = 0)
    [hG : Stacks.ConstantSheaf.IsFiniteLocallyConstant X.smallEtaleTopology G] :
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod ℓ) X.smallEtaleTopology
      (zmodLift G h) := by
  intro U
  obtain ⟨I, V, f, hcov, hE⟩ := hG.exists_finite_cover U
  refine ⟨I, V, f, hcov, fun i ↦ ?_⟩
  obtain ⟨E, hEfin, ⟨e⟩⟩ := hE i
  let J' := X.smallEtaleTopology.over (V i)
  let Q := E ⧸ AddMonoidHom.range (ℓ • 𝟙 E).hom
  let : Module (ZMod ℓ) Q := QuotientAddGroup.zmodModule (fun x ↦ ⟨x, by simp⟩)
  have : Finite Q := Finite.of_surjective _ (QuotientAddGroup.mk'_surjective _)
  refine ⟨ModuleCat.of.{u + 1} (ZMod ℓ) Q, Module.Finite.of_finite, ⟨?_⟩⟩
  have : PreservesColimitsOfSize.{0, 0} (constantSheaf J' AddCommGrpCat.{u + 1}) :=
    (constantSheafAdj J' AddCommGrpCat.{u + 1}
      (Over.mkIdTerminal (X := V i))).leftAdjoint_preservesColimits
  have hzero : (constantSheaf J' AddCommGrpCat.{u + 1}).map (ℓ • 𝟙 E) = 0 := by
    rw [Functor.map_nsmul, CategoryTheory.Functor.map_id]
    exact nsmul_id_eq_zero_of_iso e.symm
      (nsmul_id_eq_zero_map (X.smallEtaleTopology.overPullback AddCommGrpCat.{u + 1} (V i)) h)
  let eQ : (constantSheaf J' AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of Q) ≅
      (constantSheaf J' AddCommGrpCat.{u + 1}).obj E :=
    (constantSheaf J' AddCommGrpCat.{u + 1}).mapIso
        (AddCommGrpCat.cokernelIsoQuotient (ℓ • 𝟙 E)).symm ≪≫
      PreservesCokernel.iso (constantSheaf J' AddCommGrpCat.{u + 1}) (ℓ • 𝟙 E) ≪≫
      cokernelIsoOfEq hzero ≪≫ cokernelZeroIsoTarget
  exact Stacks.ModuleCatLift.sheafIsoOfForget.{u + 1} (ZMod ℓ) J'
    ((Stacks.ModuleCatLift.constantSheafForget₂Iso.{u + 1} (ZMod ℓ) J').app
      (ModuleCat.of (ZMod ℓ) Q) ≪≫ eQ ≪≫ e) (zmod_ringHom_comp_comm _ _ _)

end Stacks.EtaleCohomology

end
