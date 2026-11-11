module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BaseRingLinear
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalDeRhamLinearDerived07MW
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.SmoothLiftingConnection
public import StacksFrontier.AlgebraicGeometry.DeRham.BaseDerivedGlobalSectionsForget

/-!
# The twisted de Rham complex of a smooth lifting as a complex of sheaves of `A`-modules

In the situation of [Stacks, Tag 07MW] (`...SmallSite.Situation07MW`), write `A = Γ(S, 𝒪_S)`,
`f : Y ⟶ S` for the smooth lifting and `B = (X, Y, γ)` for the object of `Cris(X/S)` it defines.
The de Rham side `RΓ(Y, F_Y ⊗ Ω^•_{Y/S})` of the remark is
`AlgebraicGeometry.Scheme.Hom.derivedBaseGlobalSections f`, the right derived functor of the
`A`-linear global sections of sheaves of `f^{-1}𝒪_S`-modules.  This file reads a sheaf of
`f^{-1}𝒪_S`-modules as a sheaf of `A`-modules on `Y_Zar = T_Zar`
(`Situation07MW.toAmbientModuleSheaf`), `A` acting through `A ⟶ Γ(Y, f^{-1}𝒪_S)`, and shows that
this does not change `RΓ(Y, -)` (`Situation07MW.derivedBaseGlobalSectionsIsoLinear`).

## Main definitions

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite.Situation07MW`.

* `toAmbientModuleSheaf` — a sheaf of `f^{-1}𝒪_S`-modules on `Y`, read as a sheaf of `A`-modules.

## Main results

* `toAmbientModuleSheafGlobalSectionsIso` — `Γ_A(Y, -)` after reading as a sheaf of `A`-modules
  is the `A`-linear `Γ(Y, -)` of sheaves of `f^{-1}𝒪_S`-modules.
* `rightAcyclic_toAmbientModuleSheaf_obj_of_injective` — an injective sheaf of
  `f^{-1}𝒪_S`-modules, read as a sheaf of `A`-modules, is acyclic for `Γ_A(Y, -)`.
* `derivedBaseGlobalSectionsIsoLinear` — `RΓ(Y, K) ≅ RΓ_A(Y, K)` in `D⁺(Mod_A)`.

## References

* [Stacks Project, Tag 07MW](https://stacks.math.columbia.edu/tag/07MW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Hom
open scoped AlgebraicGeometry

universe w₁ w₂ w₃ w₄ w₅ w₆ u

noncomputable section

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

namespace Crystalline.GlobalCrystallineSituation.SmallSite.Situation07MW

variable {S : GlobalCrystallineSituation.{u}} (T : Situation07MW S)

/-- The rings of sections of `f^{-1}𝒪_S` are commutative. -/
instance isMulCommutative_basePullbackRingSheaf (U : (Opens T.Y)ᵒᵖ) :
    IsMulCommutative ((basePullbackRingSheaf T.toBase).obj.obj U) :=
  inferInstanceAs (IsMulCommutative ((basePullbackSheaf T.toBase).obj.obj U))

/-- Evaluating an element of the centre of a category at an object, as a ring map. -/
def catCenterEvalRingHom {C : Type*} [Category* C] [Preadditive C] (M : C) :
    CatCenter C →+* End M where
  toFun η := .of (η.app M)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- `A` acting on a sheaf of `f^{-1}𝒪_S`-modules, through `A ⟶ Γ(Y, f^{-1}𝒪_S)`. -/
def twistedBaseSmulRingHom (M : TwistedModules T.toBase) : Γ(S.S.scheme, ⊤) →+* End M :=
  (catCenterEvalRingHom M).comp
    ((Stacks.SheafOfModules.terminalSectionRingHom.{u, u, u, u} (basePullbackRingSheaf T.toBase) ⊤
      isTerminalTop).comp (baseToInverseImageRingHom T.toBase))

/-- `A` acting on the abelian sheaf underlying a sheaf of `f^{-1}𝒪_S`-modules. -/
def twistedBaseAction (M : TwistedModules T.toBase) :
    Γ(S.S.scheme, ⊤) →+* End ((abelianSheafFunctor T.toBase).obj M) :=
  (Stacks.ModuleCatLift.mapEndRingHom (abelianSheafFunctor T.toBase) M).comp
    (T.twistedBaseSmulRingHom M)

/-- **A sheaf of `f^{-1}𝒪_S`-modules on `Y`, read as a sheaf of `A`-modules on `Y_Zar = T_Zar`.**
The underlying abelian sheaf is `abelianSheafFunctor f`, sections lifted to `Type (u + 1)`, and
`a ∈ A` acts by multiplication by its image in `Γ(Y, f^{-1}𝒪_S)`. -/
def toAmbientModuleSheaf :
    TwistedModules T.toBase ⥤ CrystallineThickening.AmbientModuleSheaf T.crystallineThickening where
  obj M := Stacks.ModuleCatLift.sheafOfEndAction Γ(S.S.scheme, ⊤)
    (Opens.grothendieckTopology T.crystallineThickening.obj.thickening.target.scheme)
    ((abelianSheafFunctor T.toBase).obj M) (T.twistedBaseAction M)
  map {M M'} g := ObjectProperty.homMk (Stacks.ModuleCatLift.ofEndActionMap Γ(S.S.scheme, ⊤) _ _
    ((abelianSheafFunctor T.toBase).map g).hom fun a => by
      change ((abelianSheafFunctor T.toBase).map (T.twistedBaseSmulRingHom M a).asHom ≫
        (abelianSheafFunctor T.toBase).map g).hom = ((abelianSheafFunctor T.toBase).map g ≫
          (abelianSheafFunctor T.toBase).map (T.twistedBaseSmulRingHom M' a).asHom).hom
      rw [← Functor.map_comp, ← Functor.map_comp]
      congr 2
      exact ((Stacks.SheafOfModules.terminalSectionRingHom.{u, u, u, u}
        (basePullbackRingSheaf T.toBase) ⊤ isTerminalTop
          (baseToInverseImageRingHom T.toBase a)).naturality g).symm)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The abelian sheaf underlying `toAmbientModuleSheaf M` is `abelianSheafFunctor f M`, on the
nose. -/
theorem toAmbientModuleSheaf_comp_ambientForget :
    T.toAmbientModuleSheaf ⋙ CrystallineThickening.ambientForget T.crystallineThickening =
      abelianSheafFunctor T.toBase :=
  rfl

/-- Reading as a sheaf of `A`-modules is additive. -/
instance additive_toAmbientModuleSheaf : T.toAmbientModuleSheaf.Additive where
  map_add {_ _ f g} := (CrystallineThickening.ambientForget T.crystallineThickening).map_injective
    (by
      rw [(CrystallineThickening.ambientForget T.crystallineThickening).map_add]
      exact (abelianSheafFunctor T.toBase).map_add (f := f) (g := g))

/-- Reading as a sheaf of `A`-modules preserves finite limits. -/
instance preservesFiniteLimits_toAmbientModuleSheaf :
    PreservesFiniteLimits T.toAmbientModuleSheaf :=
  have : PreservesFiniteLimits
      (T.toAmbientModuleSheaf ⋙ CrystallineThickening.ambientForget T.crystallineThickening) :=
    inferInstanceAs (PreservesFiniteLimits (abelianSheafFunctor T.toBase))
  preservesFiniteLimits_of_reflects_of_preserves _
    (CrystallineThickening.ambientForget T.crystallineThickening)

/-- Reading as a sheaf of `A`-modules preserves finite colimits. -/
instance preservesFiniteColimits_toAmbientModuleSheaf :
    PreservesFiniteColimits T.toAmbientModuleSheaf :=
  have : PreservesFiniteColimits
      (T.toAmbientModuleSheaf ⋙ CrystallineThickening.ambientForget T.crystallineThickening) :=
    inferInstanceAs (PreservesFiniteColimits (abelianSheafFunctor T.toBase))
  preservesFiniteColimits_of_reflects_of_preserves _
    (CrystallineThickening.ambientForget T.crystallineThickening)

/-- The global sections of `toAmbientModuleSheaf M` are the `A`-module `Γ(Y, M)`. -/
def toAmbientModuleSheafTopIso (M : TwistedModules T.toBase) :
    (T.toAmbientModuleSheaf.obj M).obj.obj (op ⊤) ≅ (baseGlobalSectionsFunctor T.toBase).obj M :=
  LinearEquiv.toModuleIso
    { toFun x := x
      invFun x := x
      map_add' _ _ := rfl
      map_smul' a x := by
        have h : (basePullbackRingSheaf T.toBase).obj.map (isTerminalTop.from (⊤ : Opens T.Y)).op
            (baseToInverseImageRingHom T.toBase a) = baseToInverseImageRingHom T.toBase a := by
          rw [show isTerminalTop.from (⊤ : Opens T.Y) = 𝟙 _ from isTerminalTop.hom_ext _ _, op_id,
            CategoryTheory.Functor.map_id]
          rfl
        exact ULift.ext (congrArg (fun r => r • (show M.val.obj (op ⊤) from x.down)) h)
      left_inv _ := rfl
      right_inv _ := rfl }

/-- **`Γ_A(Y, -)` after reading as a sheaf of `A`-modules is `Γ(Y, -)` of sheaves of
`f^{-1}𝒪_S`-modules, `A`-linearly.** -/
def toAmbientModuleSheafGlobalSectionsIso :
    T.toAmbientModuleSheaf ⋙
        CrystallineThickening.ambientLinearGlobalSections T.crystallineThickening ≅
      baseGlobalSectionsFunctor T.toBase :=
  Functor.isoWhiskerLeft T.toAmbientModuleSheaf
      (Sheaf.ΓNatIsoSheafSections _ _ isTerminalTop) ≪≫
    NatIso.ofComponents T.toAmbientModuleSheafTopIso (fun _ => rfl)

section Derived

variable [HasDerivedCategory.{w₁} (TwistedModules T.toBase)]
  [HasDerivedCategory.{w₂} (CrystallineThickening.AmbientModuleSheaf T.crystallineThickening)]
  [HasDerivedCategory.{w₃} (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))]
  [hY : HasDerivedCategory.{w₄} (Sheaf (Opens.grothendieckTopology
    T.crystallineThickening.obj.thickening.target.scheme) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w₅} AddCommGrpCat.{u + 1}]

omit [HasDerivedCategory (TwistedModules T.toBase)] in
/-- **An injective sheaf of `f^{-1}𝒪_S`-modules, read as a sheaf of `A`-modules, is acyclic for
`Γ_A(Y, -)`**: its underlying abelian sheaf is acyclic for `Γ(Y, -)`. -/
theorem rightAcyclic_toAmbientModuleSheaf_obj_of_injective (I : TwistedModules T.toBase)
    [Injective I] :
    (CrystallineThickening.ambientLinearGlobalSections T.crystallineThickening).rightAcyclic
      (T.toAmbientModuleSheaf.obj I) := by
  let : HasDerivedCategory.{w₄}
      (Sheaf (Opens.grothendieckTopology T.Y) AddCommGrpCat.{u + 1}) := hY
  have : EnoughInjectives (Sheaf (Opens.grothendieckTopology
      T.crystallineThickening.obj.thickening.target.scheme) AddCommGrpCat.{u + 1}) :=
    Sheaf.enoughInjectives_of_small.{u + 1, u + 1, u, u, u + 2} _ _
  exact Stacks.Cohomology.DerivedBaseChangePlus.rightAcyclic_of_rightAcyclic_baseChange
    (CrystallineThickening.ambientForget T.crystallineThickening)
    (forget₂ (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) AddCommGrpCat.{u + 1})
    (CrystallineThickening.ambientLinearGlobalSections T.crystallineThickening)
    (CrystallineThickening.ambientGlobalSections T.crystallineThickening)
    (CrystallineThickening.ambientLinearGlobalSectionsForgetIso T.crystallineThickening).symm
    (fun J _ =>
      CrystallineThickening.rightAcyclic_ambientGlobalSections_ambientForget_obj_of_injective.{w₄,
        w₅} T.crystallineThickening J) _
    (rightAcyclic_abelianSheafFunctor_obj_of_injective.{w₄, w₅, u} T.toBase I)

/-- **`RΓ(Y, K) ≅ RΓ_A(Y_Zar, K)` in `D⁺(Mod_A)`**, for a complex `K` of sheaves of
`f^{-1}𝒪_S`-modules: reading as sheaves of `A`-modules is exact and carries injectives to objects
acyclic for `Γ_A(Y, -)`, and `Γ_A(Y, -)` after it is `Γ(Y, -)`. -/
def derivedBaseGlobalSectionsIsoLinear (K : DerivedCategory.Plus (TwistedModules T.toBase)) :
    (baseGlobalSectionsFunctor T.toBase).rightDerivedFunctorPlus.obj K ≅
      (CrystallineThickening.ambientLinearGlobalSections
        T.crystallineThickening).rightDerivedFunctorPlus.obj
        (T.toAmbientModuleSheaf.mapDerivedCategoryPlus.obj K) :=
  (Functor.rightDerivedFunctorPlusNatIso T.toAmbientModuleSheafGlobalSectionsIso.symm).app K ≪≫
    (Functor.rightDerivedFunctorPlusCompIsoOfRightAcyclic T.toAmbientModuleSheaf
      (CrystallineThickening.ambientLinearGlobalSections T.crystallineThickening)
      (fun I _ => T.rightAcyclic_toAmbientModuleSheaf_obj_of_injective I)).app K ≪≫
    (CrystallineThickening.ambientLinearGlobalSections
      T.crystallineThickening).rightDerivedFunctorPlus.mapIso
      ((Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus T.toAmbientModuleSheaf).app K)

end Derived

end Crystalline.GlobalCrystallineSituation.SmallSite.Situation07MW

end

end
