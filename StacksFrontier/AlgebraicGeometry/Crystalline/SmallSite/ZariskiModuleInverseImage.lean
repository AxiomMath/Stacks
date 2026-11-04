module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InverseImageCocontinuous
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ZariskiModuleDirectImage
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The module-valued inverse image `u_{X/S}^*` and the adjointness of `u_{X/S, *}`

Fix a global crystalline situation `(p, (S, I, γ), X)`. We show that the module-valued direct image

  `u_{X/S, *} : Mod(𝒪_{X/S}) ⥤ Mod(u_{X/S, *}𝒪_{X/S})`

is a right adjoint, by the special adjoint functor theorem, and define its left adjoint

  `u_{X/S}^* : Mod(u_{X/S, *}𝒪_{X/S}) ⥤ Mod(𝒪_{X/S})`,

the module-valued inverse image along the cocontinuous forgetful functor of [Stacks, Tag 07IH].

## Main definitions

* `zariskiModuleInverseImageULift` and `zariskiModuleInverseImage`: `u_{X/S}^*` on modules,
  before and after the ring-universe isomorphism `moduleRingULiftEquivalence`.
* `zariskiModuleDirectImageAdjunction`: the adjunction `u_{X/S}^* ⊣ u_{X/S, *}` on modules.

## Main results

* `isRightAdjoint_zariskiModuleDirectImage`: the module-valued `u_{X/S, *}` is a right adjoint.
* `preservesLimitsOfSize_zariskiModuleDirectImage`: it commutes with every limit.
* `preservesColimitsOfSize_zariskiModuleInverseImage`: `u_{X/S}^*` commutes with every colimit.
* `preservesInjectiveObjects_zariskiModuleDirectImage` and
  `preservesInjectiveObjects_zariskiModuleDirectImage_iff`: `u_{X/S, *}` carries injective
  `𝒪_{X/S}`-modules to injective `u_{X/S, *}𝒪_{X/S}`-modules exactly when `u_{X/S}^*` preserves
  monomorphisms.

## References

* [Stacks Project, Tag 07IH](https://stacks.math.columbia.edu/tag/07IH)
* [Stacks Project, Tag 07IL](https://stacks.math.columbia.edu/tag/07IL)
* [Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
-/


@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

universe u

variable (S : GlobalCrystallineSituation.{u})

/-! ### The smallness inputs of the adjoint functor theorem -/

/-- Sheaves of `𝒪^{ULift}_{X/S}`-modules on the small crystalline site form an abelian category
at the module universe `u + 1`. -/
@[sga "4 IV 11.1.2" "special case", sga "4 XVII 2.2.6" "partial"]
instance instAbelianModuleSheafULift :
    Abelian (SheafOfModules.{u + 1} (structureSheafULift S)) :=
  Stacks.Cohomology.SiteModules.moduleSheavesAbelian.{u + 1, u, u + 1, u}
    (structureSheafULift S)

/-- Sheaves of `𝒪^{ULift}_{X/S}`-modules on the small crystalline site form a Grothendieck
abelian category at the module universe `u + 1`. -/
instance instIsGrothendieckAbelianModuleSheafULift :
    IsGrothendieckAbelian.{u + 1} (SheafOfModules.{u + 1} (structureSheafULift S)) :=
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck.{u + 1, u, u + 1, u}
    (structureSheafULift S)

/-- Sheaves of `u_{X/S, *}𝒪^{ULift}_{X/S}`-modules on the small Zariski site of `X` form a
Grothendieck abelian category at the module universe `u + 1`. -/
instance instIsGrothendieckAbelianZariskiModuleSheaf :
    IsGrothendieckAbelian.{u + 1} (ZariskiModuleSheaf S) :=
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck.{u, u, u + 1, u}
    (zariskiPushforwardStructureSheaf S)

/-! ### `u_{X/S}^*` on modules -/

/-- The inverse image of sheaves of modules along `u_{X/S}`, at the lifted ring coefficients:
the left adjoint of `zariskiModuleDirectImageULift`. -/
def zariskiModuleInverseImageULift :
    ZariskiModuleSheaf S ⥤ SheafOfModules.{u + 1} (structureSheafULift S) :=
  Stacks.SheafOfModules.inverseImageCocontinuous.{u + 1} (forgetToOpens S)
    (zariskiRingStructureMapULift S)

/-- The adjunction `u_{X/S}^* ⊣ u_{X/S, *}` at the lifted ring coefficients. -/
def zariskiModuleDirectImageULiftAdjunction :
    zariskiModuleInverseImageULift S ⊣ zariskiModuleDirectImageULift S :=
  Stacks.SheafOfModules.inverseImageCocontinuousAdjunction.{u + 1} (forgetToOpens S)
    (zariskiRingStructureMapULift S)

/-- The module-valued inverse image `u_{X/S}^* : Mod(u_{X/S, *}𝒪_{X/S}) ⥤ Mod(𝒪_{X/S})` along
the morphism of topoi `u_{X/S} : (X/S)_cris ⟶ Sh(X_Zar)` of [Stacks, Tag 07IL]: the inverse image
at the lifted ring coefficients, followed by the ring-universe isomorphism of categories
`moduleRingULiftEquivalence`. -/
def zariskiModuleInverseImage : ZariskiModuleSheaf S ⥤ ModuleSheaf S :=
  zariskiModuleInverseImageULift S ⋙ moduleRingULiftDown S

/-- The adjunction `u_{X/S}^* ⊣ u_{X/S, *}` on modules. -/
def zariskiModuleDirectImageAdjunction :
    zariskiModuleInverseImage S ⊣ zariskiModuleDirectImage S :=
  (zariskiModuleDirectImageULiftAdjunction S).comp
    (moduleRingULiftEquivalence S).symm.toAdjunction

/-- The module-valued direct image `u_{X/S, *}` is a right adjoint. -/
instance isRightAdjoint_zariskiModuleDirectImage :
    (zariskiModuleDirectImage S).IsRightAdjoint :=
  (zariskiModuleDirectImageAdjunction S).isRightAdjoint

/-- `u_{X/S, *}` on modules commutes with every limit. -/
instance preservesLimitsOfSize_zariskiModuleDirectImage :
    PreservesLimitsOfSize.{u + 1, u + 1} (zariskiModuleDirectImage S) :=
  (zariskiModuleDirectImageAdjunction S).rightAdjoint_preservesLimits

/-- `u_{X/S}^*` on modules commutes with every colimit. -/
instance preservesColimitsOfSize_zariskiModuleInverseImage :
    PreservesColimitsOfSize.{u + 1, u + 1} (zariskiModuleInverseImage S) :=
  (zariskiModuleDirectImageAdjunction S).leftAdjoint_preservesColimits

/-- `u_{X/S}^*` on modules is additive. -/
instance additive_zariskiModuleInverseImage : (zariskiModuleInverseImage S).Additive :=
  (zariskiModuleDirectImageAdjunction S).left_adjoint_additive

/-! ### Injective objects -/

/-- If `u_{X/S}^*` preserves monomorphisms, then `u_{X/S, *}` carries injective sheaves of
`𝒪_{X/S}`-modules to injective sheaves of `u_{X/S, *}𝒪_{X/S}`-modules, as in
[Stacks, Tag 015Z]. -/
theorem preservesInjectiveObjects_zariskiModuleDirectImage
    [(zariskiModuleInverseImage S).PreservesMonomorphisms] :
    (zariskiModuleDirectImage S).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (zariskiModuleDirectImageAdjunction S)

/-- `u_{X/S, *}` preserves injective modules exactly when `u_{X/S}^*` preserves
monomorphisms. -/
theorem preservesInjectiveObjects_zariskiModuleDirectImage_iff :
    (zariskiModuleDirectImage S).PreservesInjectiveObjects ↔
      (zariskiModuleInverseImage S).PreservesMonomorphisms :=
  ⟨fun _ ↦ Functor.preservesMonomorphisms_of_adjunction_of_preservesInjectiveObjects
      (zariskiModuleDirectImageAdjunction S),
    fun _ ↦ preservesInjectiveObjects_zariskiModuleDirectImage S⟩

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
