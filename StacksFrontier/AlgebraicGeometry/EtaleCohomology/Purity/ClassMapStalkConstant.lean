module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.ClassMapStalkCyclic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.ZModModuleDevissage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedEtale

/-!
# The class map on stalks with constant finite coefficients

Keep the setting of `Stacks.EtaleCohomology.Purity.classMapGermMap`, at a geometric point `x` of
`U` and a neighbourhood `V` of it carrying a primitive `N`-th root of unity `ζ`. On `V` the
constant sheaf `ℤ/n` (`n ∣ N`, as a sheaf of `ℤ/N`-modules) is `μ_n`, by `1 ↦ ζ^{N/n}`
(`Stacks.EtaleCohomology.Purity.constantSliceRootIso`); so the class map on stalks with
coefficients `ℤ/n` is bijective as soon as the class map with coefficients `μ_n` is
(`Stacks.EtaleCohomology.Purity.bijective_classMapGermMap_restrictRootsOfUnityModule`). The class
map on stalks is natural and additive in the constant value, so dévissage of finite `ℤ/N`-modules
(`Stacks.EtaleCohomology.Purity.isIso_app_of_finite_zmodModule`) extends this to the constant sheaf
of every finite `ℤ/N`-module
(`Stacks.EtaleCohomology.Purity.bijective_classMapGermMap_constantSheaf`).

## Main definitions

* `Stacks.EtaleCohomology.Purity.constantSliceRootIso`.
* `Stacks.EtaleCohomology.Purity.classMapGermNatTrans`.

## Main results

* `Stacks.EtaleCohomology.Purity.bijective_classMapGermMap_constantSheaf`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
  GrothendieckTopology

universe u

namespace Stacks.EtaleCohomology.Purity

open Stacks.Kummer

attribute [local instance] AlgebraicGeometry.preservesFilteredColimitsOfSize_forget_addCommGrpCat

section SliceIso

variable {U : Scheme.{u}} (N : ℕ) [NeZero N] (V : U.Etale) {K : Type u} [Field K]
  (κ : K →+* Γ(V.left, ⊤)) {ℓ n : ℕ} (hn : ℓ * n = N) [NeZero n] {ζ' : K}
  (hζ' : IsPrimitiveRoot ζ' n)

/-- Restriction of scalars from `ℤ/n` to `ℤ/N` commutes with the constant sheaf on the slice
over `V`: it is a left adjoint, so it commutes with sheafification. -/
def restrictScalarsConstantSliceIso :
    (constantSheaf (U.smallEtaleTopology.over V) (ModuleCat.{u + 1} (ZMod N))).obj
        ((zmodRestrict.{u, 0} ℓ n N hn).obj (ModuleCat.of (ZMod n) (ULift.{u + 1} (ZMod n)))) ≅
      (sheafCompose (U.smallEtaleTopology.over V) (zmodRestrict.{u, 0} ℓ n N hn)).obj
        ((constantSheaf (U.smallEtaleTopology.over V) (ModuleCat.{u + 1} (ZMod n))).obj
          (ModuleCat.of (ZMod n) (ULift.{u + 1} (ZMod n)))) := by
  haveI := Stacks.ConstantSheaf.hasSheafify_over_moduleCat_of_univLE.{u + 1, u, 0, u + 1}
    U.smallEtaleTopology (ZMod N) V
  haveI := Stacks.ConstantSheaf.hasSheafify_over_moduleCat_of_univLE.{u + 1, u, 0, u + 1}
    U.smallEtaleTopology (ZMod n) V
  letI : Limits.PreservesLimitsOfSize.{u, u + 1} (zmodRestrict.{u, 0} ℓ n N hn) :=
    (ModuleCat.extendRestrictScalarsAdj.{u + 1} _).rightAdjoint_preservesLimits
  letI : (U.smallEtaleTopology.over V).HasSheafCompose (zmodRestrict.{u, 0} ℓ n N hn) :=
    ⟨fun P hP => Presheaf.isSheaf_comp_of_isSheaf _ P _ hP⟩
  letI : Limits.PreservesLimitsOfSize.{u, u + 1}
      (ModuleCat.coextendScalars.{0, 0, u + 1} (ZMod.castHom (dvd_of_mul_eq hn) (ZMod n))) :=
    (ModuleCat.restrictCoextendScalarsAdj.{u + 1} _).rightAdjoint_preservesLimits
  letI : (U.smallEtaleTopology.over V).HasSheafCompose
      (ModuleCat.coextendScalars.{0, 0, u + 1} (ZMod.castHom (dvd_of_mul_eq hn) (ZMod n))) :=
    ⟨fun P hP => Presheaf.isSheaf_comp_of_isSheaf _ P _ hP⟩
  haveI : (U.smallEtaleTopology.over V).PreservesSheafification (zmodRestrict.{u, 0} ℓ n N hn) :=
    Sheaf.preservesSheafification_of_adjunction _
      (ModuleCat.restrictCoextendScalarsAdj.{u + 1} (ZMod.castHom (dvd_of_mul_eq hn) (ZMod n)))
  exact ((constantCommuteCompose (U.smallEtaleTopology.over V)
    (zmodRestrict.{u, 0} ℓ n N hn)).app (ModuleCat.of (ZMod n) (ULift.{u + 1} (ZMod n)))).symm

/-- **On a neighbourhood carrying a primitive `n`-th root `ζ'`, the constant sheaf `ℤ/n` is
`μ_n`**, as sheaves of `ℤ/N`-modules on the slice: `1 ↦ ζ'`. -/
def constantSliceRootIso :
    (U.smallEtaleTopology.overPullback (ModuleCat.{u + 1} (ZMod N)) V).obj
        ((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} (ZMod N))).obj
          ((zmodRestrict.{u, 0} ℓ n N hn).obj (ModuleCat.of (ZMod n) (ULift.{u + 1} (ZMod n))))) ≅
      (U.smallEtaleTopology.overPullback (ModuleCat.{u + 1} (ZMod N)) V).obj
        (restrictRootsOfUnityModule U N ℓ n hn) := by
  haveI := Stacks.ConstantSheaf.hasSheafify_over_moduleCat_of_univLE.{u + 1, u, 0, u + 1}
    U.smallEtaleTopology (ZMod N) V
  haveI := Stacks.ConstantSheaf.hasSheafify_over_moduleCat_of_univLE.{u + 1, u, 0, u + 1}
    U.smallEtaleTopology (ZMod n) V
  exact ((Stacks.ConstantSheaf.overPullbackConstantSheafIso U.smallEtaleTopology
      (ModuleCat.{u + 1} (ZMod N)) V).app _).symm ≪≫
    restrictScalarsConstantSliceIso N V hn ≪≫
    (sheafCompose (U.smallEtaleTopology.over V) (zmodRestrict.{u, 0} ℓ n N hn)).mapIso
      (sliceRootSheafIso.{u, 0} V κ hζ')

end SliceIso

section Devissage

variable {X U : Scheme.{u}} (g : X ⟶ U) (q : ℕ) (N : ℕ) [NeZero N]
  (s : ToType ((((smallEtalePushforwardAb g).rightDerived q).obj
    ((smallEtalePullbackAb g).obj (smallEtaleModuleSheafForgetAb (ZMod N)
      (rootsOfUnityModule.{u, 0} U N)))).obj.obj (op ((opensToEtale U).obj ⊤))))
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ U)
  {V : U.Etale} (v : (Scheme.pointSmallEtale x).fiber.obj V) {K : Type u} [Field K]
  (κ : K →+* Γ(V.left, ⊤)) {ζ : K} (hζ : IsPrimitiveRoot ζ N)

/-- The constant sheaf of `ℤ/N`-modules on `U` is additive in its value. -/
instance constantSheaf_moduleCat_additive_classMapStalk :
    (constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} (ZMod N))).Additive :=
  (constantSheafAdj U.smallEtaleTopology (ModuleCat.{u + 1} (ZMod N))
    (isTerminal_opensToEtale_top U)).left_adjoint_additive

/-- **The class map on the stalks of constant sheaves**, as a natural transformation of additive
functors of the constant value. -/
def classMapGermNatTrans :
    constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} (ZMod N)) ⋙
        sheafCompose U.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} (ZMod N)) AddCommGrpCat.{u + 1}) ⋙
          smallEtaleStalkAb x ⟶
      constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} (ZMod N)) ⋙
        sheafCompose U.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} (ZMod N)) AddCommGrpCat.{u + 1}) ⋙
          smallEtalePullbackAb g ⋙ (smallEtalePushforwardAb g).rightDerived q ⋙
            smallEtaleStalkAb x where
  app M := AddCommGrpCat.ofHom (classMapGermMap g q N s (Scheme.pointSmallEtale x) v κ hζ
    ((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} (ZMod N))).obj M))
  naturality M M' f := by
    ext p
    exact classMapGermMap_naturality g q N s (Scheme.pointSmallEtale x) v κ hζ
      ((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} (ZMod N))).map f) p

include hζ in
/-- **The class map on stalks with constant finite coefficients is bijective**, as soon as for
every `n ∣ N` the power class generates the stalk of `R^q g_*(g⁻¹ μ_n)` freely over `ℤ/n`. -/
theorem bijective_classMapGermMap_constantSheaf
    (hgen : ∀ (ℓ n : ℕ) (hn : ℓ * n = N) [NeZero n]
      (y : (Scheme.pointSmallEtale x).fiber.obj ((opensToEtale U).obj ⊤)),
      Function.Bijective (fun a : ZMod n => a.val • (Scheme.pointSmallEtale x).toPresheafFiber
        ((opensToEtale U).obj ⊤) y (((smallEtalePushforwardAb g).rightDerived q).obj
          ((smallEtalePullbackAb g).obj (smallEtaleModuleSheafForgetAb (ZMod N)
            (restrictRootsOfUnityModule U N ℓ n hn)))).obj (powClass g q N s ℓ n hn)))
    (M : ModuleCat.{u + 1} (ZMod N)) [Finite M] :
    Function.Bijective (classMapGermMap g q N s (Scheme.pointSmallEtale x) v κ hζ
      ((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} (ZMod N))).obj M)) := by
  have hiso : IsIso ((classMapGermNatTrans g q N s x v κ hζ).app M) := by
    refine isIso_app_of_finite_zmodModule _ (fun n hn hn0 => ?_) M
    have : NeZero n := ⟨hn0.ne'⟩
    have hℓ : N / n * n = N := Nat.div_mul_cancel hn
    have hζ' : IsPrimitiveRoot (ζ ^ (N / n)) n := by
      have h := hζ.pow_of_dvd (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) hn)
        hn0).ne' (Nat.div_dvd_of_dvd hn)
      rwa [Nat.div_div_self hn (NeZero.ne N)] at h
    rw [ConcreteCategory.isIso_iff_bijective]
    change Function.Bijective (classMapGermMap g q N s (Scheme.pointSmallEtale x) v κ hζ
      ((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} (ZMod N))).obj
        ((zmodRestrict.{u, 0} (N / n) n N hℓ).obj
          (ModuleCat.of (ZMod n) (ULift.{u + 1} (ZMod n))))))
    rw [bijective_classMapGermMap_iff_of_slice_iso g q N s (Scheme.pointSmallEtale x) v κ hζ v
      (constantSliceRootIso N V κ hℓ hζ')]
    let y : (Scheme.pointSmallEtale x).fiber.obj ((opensToEtale U).obj ⊤) :=
      (Scheme.pointSmallEtale x).fiber.map ((isTerminal_opensToEtale_top U).from V) v
    exact bijective_classMapGermMap_restrictRootsOfUnityModule g q N s (Scheme.pointSmallEtale x) v
      κ hζ hℓ hζ' y (hgen (N / n) n hℓ y)
  rw [ConcreteCategory.isIso_iff_bijective] at hiso
  exact hiso

end Devissage

end Stacks.EtaleCohomology.Purity

end
