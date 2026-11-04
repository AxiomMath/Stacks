module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafHom
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.CharacterTorsorFrobenius
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.ModuleScalarAction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `μ_N` as a sheaf of `ℤ/N`-modules, and the Tate twist `𝓗om(μ_N, -)`

The sheaf `μ_N = Stacks.Kummer.rootsOfUnitySheaf X N` of `N`-th roots of unity on the small étale
site of a scheme `X` is an abelian sheaf killed by `N`
(`Stacks.Kummer.nsmul_id_rootsOfUnitySheaf`). So it is a sheaf of `ℤ/N`-modules, with
`a ∈ ℤ/N` acting by `a.val`: this is `Stacks.Kummer.rootsOfUnityModule`, whose underlying
abelian sheaf is `μ_N` itself.

For a sheaf `G` of `ℤ/N`-modules, the Tate twist `G(-1)` is the internal Hom `𝓗om(μ_N, G)`,
whose sections over an étale `U ⟶ X` are the morphisms `μ_N|_U ⟶ G|_U` of sheaves of
`ℤ/N`-modules on the slice site (`Stacks.Kummer.twistNegOneModule`, built from the internal Hom
`Stacks.ConstantSheaf.moduleSheafHom`). The dual `μ_N^∨ = 𝓗om(μ_N, ℤ/N)` is the twist of the
constant sheaf (`Stacks.Kummer.rootsOfUnityDual`).

## Main definitions

* `CategoryTheory.zmodScalarAction`: an object of a preadditive category killed by `N`, with
  `ℤ/N` acting through `ZMod.val`.
* `Stacks.Kummer.rootsOfUnityModule`: `μ_N` as a sheaf of `ℤ/N`-modules.
* `Stacks.Kummer.rootsOfUnityModuleForgetIso`: its underlying abelian sheaf is `μ_N`.
* `Stacks.Kummer.twistNegOneModule`: the Tate twist `G(-1) = 𝓗om(μ_N, G)`.
* `Stacks.Kummer.twistNegOneModuleMap`: its functoriality in `G`.
* `Stacks.Kummer.rootsOfUnityDual`: `μ_N^∨ = 𝓗om(μ_N, ℤ/N)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v w


namespace CategoryTheory

variable {C : Type w} [Category.{v} C] [Preadditive C] (N : ℕ) [NeZero N]

omit [NeZero N] in
/-- Two natural numbers congruent modulo `N` act in the same way on an object killed by `N`. -/
theorem nsmul_id_eq_of_modEq {A : C} (hA : N • 𝟙 A = 0) {a b : ℕ} (h : a ≡ b [MOD N]) :
    a • 𝟙 A = b • 𝟙 A := by
  have hk : ∀ k : ℕ, (N * k) • 𝟙 A = 0 := fun k => by rw [mul_comm, mul_smul, hA, smul_zero]
  rw [← Nat.mod_add_div a N, ← Nat.mod_add_div b N, h, add_nsmul, add_nsmul, hk, hk]

/-- The functor underlying `CategoryTheory.zmodScalarAction`. -/
def zmodScalarFunctor (A : C) (hA : N • 𝟙 A = 0) : SingleObj (ZMod N) ⥤ C where
  obj _ := A
  map {_ _} a := ZMod.val (show ZMod N from a) • 𝟙 A
  map_id x := by
    rw [SingleObj.id_as_one]
    change ZMod.val (1 : ZMod N) • 𝟙 A = 𝟙 A
    exact (nsmul_id_eq_of_modEq N hA (b := 1)
      (by rw [ZMod.val_one_eq_one_mod]; exact Nat.mod_modEq 1 N)).trans (one_nsmul _)
  map_comp {_ _ _} a b := by
    rw [SingleObj.comp_as_mul]
    change ZMod.val ((show ZMod N from b) * (show ZMod N from a)) • 𝟙 A =
      (ZMod.val (show ZMod N from a) • 𝟙 A) ≫ (ZMod.val (show ZMod N from b) • 𝟙 A)
    rw [Preadditive.nsmul_comp, Preadditive.comp_nsmul, Category.comp_id, smul_smul]
    exact nsmul_id_eq_of_modEq N hA (by rw [ZMod.val_mul, mul_comm]; exact Nat.mod_modEq _ N)

/-- The functor `CategoryTheory.zmodScalarFunctor` is additive. -/
instance (A : C) (hA : N • 𝟙 A = 0) : (zmodScalarFunctor N A hA).Additive where
  map_add {_ _ a b} := by
    change ZMod.val ((show ZMod N from a) + (show ZMod N from b)) • 𝟙 A =
      ZMod.val (show ZMod N from a) • 𝟙 A + ZMod.val (show ZMod N from b) • 𝟙 A
    rw [← add_nsmul]
    exact nsmul_id_eq_of_modEq N hA (by rw [ZMod.val_add]; exact Nat.mod_modEq _ N)

/-- An object of a preadditive category killed by `N` as a `ℤ/N`-module object: the additive
functor from the one-object category on `ℤ/N` sending `a` to `a.val • 𝟙`. -/
def zmodScalarAction (A : C) (hA : N • 𝟙 A = 0) : SingleObj (ZMod N) ⥤+ C :=
  AdditiveFunctor.of (zmodScalarFunctor N A hA)

end CategoryTheory

namespace Stacks.Kummer

/-- `μ_N` is killed by `N`, at every coefficient universe. -/
theorem nsmul_id_rootsOfUnitySheaf_univ (X : Scheme.{u}) (N : ℕ) :
    N • 𝟙 (rootsOfUnitySheaf.{u, v} X N) = 0 := by
  rw [← cancel_mono (rootsOfUnityι.{u, v} X N), zero_comp, Preadditive.nsmul_comp,
    Category.id_comp, ← Category.comp_id (rootsOfUnityι.{u, v} X N), ← Preadditive.comp_nsmul]
  exact rootsOfUnityι_comp_powMap X N

variable (X : Scheme.{u}) (N : ℕ) [NeZero N]

/-- `μ_N` as a sheaf of `ℤ/N`-modules on the small étale site of `X`: the abelian sheaf of `N`-th
roots of unity, which is killed by `N`, with `a ∈ ℤ/N` acting through `a.val`. -/
@[sga "4 IX 3.0",
  sga "4 XVIII 1.1.1" "i = 1",
  sga "4½ Arcata 2.2.4",
  sga "4½ Arcata 6.1" "special case"]
def rootsOfUnityModule : Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) v} (ZMod N)) :=
  (scalarActionToModuleSheaf X.smallEtaleTopology (ZMod N)).obj
    (zmodScalarAction N (rootsOfUnitySheaf.{u, v} X N) (nsmul_id_rootsOfUnitySheaf_univ X N))

/-- The underlying abelian sheaf of `μ_N` as a sheaf of `ℤ/N`-modules is `μ_N`. -/
def rootsOfUnityModuleForgetIso :
    (sheafCompose X.smallEtaleTopology
        (forget₂ (ModuleCat.{max (u + 1) v} (ZMod N)) AddCommGrpCat.{max (u + 1) v})).obj
      (rootsOfUnityModule.{u, v} X N) ≅ rootsOfUnitySheaf.{u, v} X N :=
  Iso.refl _

/-- The Tate twist `G(-1) = 𝓗om(μ_N, G)` of a sheaf of `ℤ/N`-modules on the small étale site
of `X`: its sections over an étale `U ⟶ X` are the morphisms `μ_N|_U ⟶ G|_U` of sheaves of
`ℤ/N`-modules on the slice site. -/
@[sga "4 XVIII 1.1.1" "i = -1", sga "4½ Arcata 6.1" "partial", sga "7 I 0.0.6" "special case"]
def twistNegOneModule (G : Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) v} (ZMod N))) :
    Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) v} (ZMod N)) :=
  Stacks.ConstantSheaf.moduleSheafHom X.smallEtaleTopology (ZMod N)
    (rootsOfUnityModule.{u, v} X N) G

/-- The functoriality of the Tate twist: postcomposition with `w : G ⟶ G'`. -/
def twistNegOneModuleMap
    {G G' : Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) v} (ZMod N))} (w : G ⟶ G') :
    twistNegOneModule.{u, v} X N G ⟶ twistNegOneModule.{u, v} X N G' :=
  Stacks.ConstantSheaf.moduleSheafHomMap X.smallEtaleTopology (ZMod N) (𝟙 _) w

/-- The dual `μ_N^∨ = 𝓗om(μ_N, ℤ/N)`, the twist of the constant sheaf `ℤ/N`. -/
@[sga "4½ Arcata 6.1" "special case"]
def rootsOfUnityDual :
    Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) v} (ZMod N)) :=
  twistNegOneModule.{u, v} X N
    ((constantSheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) v} (ZMod N))).obj
      (ModuleCat.of (ZMod N) (ULift.{max (u + 1) v} (ZMod N))))

end Stacks.Kummer

end
