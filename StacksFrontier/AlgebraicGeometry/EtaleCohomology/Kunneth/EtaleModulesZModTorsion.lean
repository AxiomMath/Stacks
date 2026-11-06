module

public import Mathlib.CategoryTheory.Equivalence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModulesConstantRing
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ModuleLiftLocallyConstant

/-!
# Sheaves of `ℤ/nℤ`-modules on `X_étale` are the abelian sheaves killed by `n`

Let `X` be a scheme and `n` a natural number. Forgetting the module structure of a sheaf of
`ℤ/nℤ`-modules on the small étale site of `X`,
`Stacks.EtaleCohomology.etaleModuleForgetAb (ZMod n) X`, is **fully faithful**, and its essential
image is the abelian sheaves annihilated by `n`. Hence it is an equivalence

`EtaleModules (ZMod n) X ≌ {F : Sheaf X_étale Ab | n • 𝟙 F = 0}`.

This is how a statement about an abelian sheaf whose sections are killed by `n`, such as the
reduction step of [Stacks, Tag 0F1H] ("we may assume `𝓕` is a sheaf of `ℤ/nℤ`-modules"), reaches
the derived categories `D(X_étale, ℤ/nℤ)` of `Stacks.EtaleCohomology.EtaleModules` on which the
Künneth formula [Stacks, Tag 0F14] is proved.

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleForgetAbZModFullyFaithful` — full faithfulness: an additive
  map of sheaves of `ℤ/nℤ`-modules is `ℤ/nℤ`-linear, every scalar acting as an integer.
* `Stacks.EtaleCohomology.etaleModulesZModEquivalence` — the equivalence above.

## Main results

* `Stacks.EtaleCohomology.etaleModuleForgetAb_zmod_essImage_iff` — the essential image is the
  abelian sheaves killed by `n`: one direction is `n = 0` in `ℤ/nℤ`, the other the lift
  `Stacks.EtaleCohomology.zmodLift`.

## References

* [Stacks Project, Tag 0F1H](https://stacks.math.columbia.edu/tag/0F1H)
* [Stacks Project, Tag 0F14](https://stacks.math.columbia.edu/tag/0F14)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

variable (n : ℕ) (X : Scheme.{u})

/-- Postcomposition with the forgetful functor carries sheaves of modules to abelian sheaves. -/
local instance : X.smallEtaleTopology.HasSheafCompose
    (forget₂ (ModuleCat.{u + 1} (ZMod n)) AddCommGrpCat.{u + 1}) :=
  ModuleSheaf.hasSheafCompose_forget₂.{u + 1} (ZMod n) X.smallEtaleTopology

/-- Multiplication by a scalar of `ℤ/nℤ` on the abelian sheaf underlying a sheaf of
`ℤ/nℤ`-modules is multiplication by an integer. -/
theorem sheafScalarEnd_zmod_eq_zsmul (F : EtaleModules.{u, 0} (ZMod n) X) (a : ZMod n) :
    Stacks.ModuleCatLift.sheafScalarEnd.{u + 1} (ZMod n) X.smallEtaleTopology F a =
      (ZMod.cast a : ℤ) • (1 : End _) := by
  conv_lhs => rw [← ZMod.intCast_zmod_cast a]
  rw [map_intCast]
  exact (zsmul_one _).symm

/-- **Forgetting the module structure of sheaves of `ℤ/nℤ`-modules is fully faithful**: an
additive map of the underlying abelian sheaves commutes with multiplication by every scalar, a
scalar of `ℤ/nℤ` acting as an integer, so it is a map of sheaves of `ℤ/nℤ`-modules. -/
def etaleModuleForgetAbZModFullyFaithful :
    (etaleModuleForgetAb.{u, 0} (ZMod n) X).FullyFaithful where
  preimage {F G} φ := Stacks.ModuleCatLift.sheafHomOfForget.{u + 1} (ZMod n) X.smallEtaleTopology φ
    (fun a => by
      rw [sheafScalarEnd_zmod_eq_zsmul, sheafScalarEnd_zmod_eq_zsmul]
      change ((ZMod.cast a : ℤ) • 𝟙 _) ≫ φ = φ ≫ ((ZMod.cast a : ℤ) • 𝟙 _)
      rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul, Category.id_comp, Category.comp_id])
  map_preimage _ := rfl
  preimage_map _ := rfl

/-- Forgetting the module structure of sheaves of `ℤ/nℤ`-modules on `X_étale` is full. -/
instance etaleModuleForgetAb_zmod_full : (etaleModuleForgetAb.{u, 0} (ZMod n) X).Full :=
  (etaleModuleForgetAbZModFullyFaithful n X).full

/-- **The abelian sheaves underlying sheaves of `ℤ/nℤ`-modules are exactly those killed by
`n`.** -/
theorem etaleModuleForgetAb_zmod_essImage_iff
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (etaleModuleForgetAb.{u, 0} (ZMod n) X).essImage F ↔ n • 𝟙 F = 0 := by
  refine ⟨fun ⟨M, ⟨e⟩⟩ => ?_, fun hF => ⟨zmodLift F hF, ⟨forgetZModZmodLiftIso F hF⟩⟩⟩
  calc n • 𝟙 F = e.inv ≫ (n • 𝟙 _) ≫ e.hom := by simp
    _ = 0 := by rw [nsmul_id_forgetZMod_eq_zero n X M, Limits.zero_comp, Limits.comp_zero]

/-- **Sheaves of `ℤ/nℤ`-modules on `X_étale` are the abelian sheaves killed by `n`**, through the
underlying abelian sheaf. -/
def etaleModulesZModEquivalence :
    EtaleModules.{u, 0} (ZMod n) X ≌
      (ObjectProperty.FullSubcategory fun F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} =>
        n • 𝟙 F = 0) :=
  haveI := (etaleModuleForgetAbZModFullyFaithful n X).faithful
  (etaleModuleForgetAb.{u, 0} (ZMod n) X).toEssImage.asEquivalence.trans
    (ObjectProperty.fullSubcategoryCongr
      (funext fun F => propext (etaleModuleForgetAb_zmod_essImage_iff n X F)))

/-- The equivalence followed by the inclusion is the underlying abelian sheaf. -/
theorem etaleModulesZModEquivalence_functor_comp_ι :
    (etaleModulesZModEquivalence n X).functor ⋙ ObjectProperty.ι _ =
      etaleModuleForgetAb.{u, 0} (ZMod n) X :=
  rfl

end Stacks.EtaleCohomology

end
