module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftFiniteColimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftInjectiveSeparator
public import StacksFrontier.Algebra.Homology.DerivedCategory.BaseChangeBoundedBelow
public import StacksFrontier.Algebra.Homology.DerivedCategory.FaithfulConservativePlus
public import StacksFrontier.AlgebraicGeometry.DeRham.BaseDerivedGlobalSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.InjectiveModuleGlobalSections
public import StacksFrontier.CategoryTheory.Sites.GrothendieckAbelianUnivLE

/-!
# Forgetting the `A`-module structure of `RΓ(Y, -)` over the base ring

Let `f : Y ⟶ S` be a morphism of schemes and `A = Γ(S, 𝒪_S)`.  For a complex `K` of sheaves of
`f^{-1}𝒪_S`-modules on `Y`, `AlgebraicGeometry.Scheme.Hom.derivedBaseGlobalSections f K` is
`RΓ(Y, K) ∈ D⁺(Mod_A)`.  This file proves that its image in `D⁺(Ab)` under the forgetful
functor is the abelian derived global sections `RΓ(Y, K_ab)` of the underlying complex of
abelian sheaves `K_ab`, naturally.

The abelian sheaves are taken with sections in `Type (u + 1)`, which is the coefficient
universe of the ambient-scheme global sections
`Crystalline.GlobalCrystallineSituation.CrystallineThickening.ambientGlobalSections` of the
crystalline chapter, and `A`-linear global sections land in `ModuleCat.{u + 1} A`.  The
underlying abelian sheaf `abelianSheafFunctor f` therefore lifts the sections of a sheaf of
`f^{-1}𝒪_S`-modules from `Type u` to `Type (u + 1)` and then forgets the module structure.

## Main definitions

Everything lives in the namespace `AlgebraicGeometry.Scheme.Hom`.

* `abelianSheafFunctor` — the underlying abelian sheaf, with sections lifted to `Type (u + 1)`.
* `abelianPlusObjectOfCochainComplex` — the underlying complex of abelian sheaves of a complex
  of sheaves of `f^{-1}𝒪_S`-modules, as an object of `D⁺(Ab(Y))`.

## Main results

* `rightAcyclic_abelianSheafFunctor_obj_of_injective` — the underlying abelian sheaf of an
  injective sheaf of `f^{-1}𝒪_S`-modules is right acyclic for `Γ(Y, -)`.
* `baseGlobalSectionsForgetIso` — `Γ(Y, M_ab) ≅ Γ(Y, M)` with its `A`-module structure forgotten.
* `derivedBaseGlobalSectionsFunctorForgetIso` — the isomorphism of functors
  `D⁺(Mod_{f^{-1}𝒪_S}) ⥤ D⁺(Ab)` between forgetting before and after `RΓ(Y, -)`.
* `derivedBaseGlobalSectionsForgetIso` — `forget(RΓ(Y, K)) ≅ RΓ(Y, K_ab)` in `D⁺(Ab)`.

## Implementation notes

The comparison is `Stacks.Cohomology.BoundedBelowComplexes.derivedBaseChangePlusIso`.  Its
acyclicity input: the universe lift of an injective sheaf of modules is injective
(`Stacks.SheafOfModules.preservesInjectiveObjects_moduleULift_max`), and the underlying abelian
sheaf of an injective sheaf of modules is acyclic for global sections
(`Stacks.Cohomology.GlobalSections.rightAcyclic_Γ_toSheaf_obj_of_injective`).

## References

* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped AlgebraicGeometry

universe w₁ w₂ w₃ w₄ u

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

namespace AlgebraicGeometry.Scheme.Hom

variable {Y S : Scheme.{u}} (f : Y ⟶ S)

/-- Sheafification of abelian presheaves on the opens of `Y`, with sections in `Type u`. -/
local instance hasSheafifySmall : HasSheafify (Opens.grothendieckTopology ↥Y) AddCommGrpCat.{u} :=
  _root_.SheafOfModules.hasSheafify_opens.{u} ↥Y

/-- Sheafification of abelian presheaves on the opens of `Y`, with sections in `Type (u + 1)`. -/
local instance hasSheafifyLarge :
    HasSheafify (Opens.grothendieckTopology ↥Y) AddCommGrpCat.{u + 1} :=
  _root_.SheafOfModules.hasSheafify_opens.{u + 1} ↥Y

/-- Sheafification inverts the locally bijective maps, with sections in `Type u`. -/
local instance wEqualsLocallyBijectiveSmall :
    (Opens.grothendieckTopology ↥Y).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  _root_.SheafOfModules.wEqualsLocallyBijective_opens.{u} ↥Y

/-- Sheafification inverts the locally bijective maps, with sections in `Type (u + 1)`. -/
local instance wEqualsLocallyBijectiveLarge :
    (Opens.grothendieckTopology ↥Y).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  _root_.SheafOfModules.wEqualsLocallyBijective_opens.{u + 1} ↥Y

/-- Abelian sheaves on `Y` with sections in `Type (u + 1)` have enough injectives. -/
local instance enoughInjectivesLarge :
    EnoughInjectives (Sheaf (Opens.grothendieckTopology ↥Y) AddCommGrpCat.{u + 1}) :=
  Sheaf.enoughInjectives_of_small.{u + 1, u + 1, u, u, u + 2} (Opens.grothendieckTopology ↥Y)
    AddCommGrpCat.{u + 1}

/-- `Ext`-groups of abelian sheaves on `Y` with sections in `Type (u + 1)` exist in
`Type (u + 1)`. -/
local instance hasExtLarge :
    HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology ↥Y) AddCommGrpCat.{u + 1}) :=
  hasExt_of_enoughInjectives.{u + 1} _

attribute [local instance] AlgebraicGeometry.Scheme.Hom.enoughInjectives

/-- Sheaves of `f^{-1}𝒪_S`-modules on `Y` have a separator. -/
local instance hasSeparatorTwisted : HasSeparator (TwistedModules f) :=
  _root_.SheafOfModules.hasSeparatorU.{u, u, u} (basePullbackRingSheaf f)

/-- Global sections of abelian sheaves on `Y`, with sections in `Type (u + 1)`, are additive. -/
local instance additive_Γ_large :
    (Sheaf.Γ (Opens.grothendieckTopology ↥Y) AddCommGrpCat.{u + 1}).Additive :=
  Stacks.Cohomology.GlobalSections.additive_Γ.{u + 1} (Opens.grothendieckTopology ↥Y)

/-- **The underlying abelian sheaf of a sheaf of `f^{-1}𝒪_S`-modules on `Y`, with its sections
lifted to `Type (u + 1)`**: the universe lift of sheaves of modules followed by forgetting the
module structure.  Its value on `M` has `ULift.{u + 1} (M(V))` for its sections over `V`. -/
abbrev abelianSheafFunctor :
    TwistedModules f ⥤ Sheaf (Opens.grothendieckTopology ↥Y) AddCommGrpCat.{u + 1} :=
  Stacks.SheafOfModules.moduleULift.{u + 1, u} (basePullbackRingSheaf f) ⋙
    _root_.SheafOfModules.toSheaf.{u + 1} (basePullbackRingSheaf f)

/-- The underlying abelian sheaf functor preserves finite limits. -/
instance preservesFiniteLimits_abelianSheafFunctor :
    PreservesFiniteLimits (abelianSheafFunctor f) := by
  have : PreservesFiniteLimits
      (Stacks.SheafOfModules.moduleULift.{u + 1, u} (basePullbackRingSheaf f)) :=
    ⟨fun _ _ _ => inferInstance⟩
  exact comp_preservesFiniteLimits _ _

/-- The underlying abelian sheaf functor preserves finite colimits. -/
instance preservesFiniteColimits_abelianSheafFunctor :
    PreservesFiniteColimits (abelianSheafFunctor f) := by
  have := Stacks.SheafOfModules.preservesFiniteColimits_moduleULift.{u + 1, u}
    (basePullbackRingSheaf f)
  have := Stacks.SheafOfModules.toSheaf_preservesFiniteColimits.{u + 1} (basePullbackRingSheaf f)
  exact comp_preservesFiniteColimits _ _

/-- The underlying abelian sheaf functor is faithful. -/
instance faithful_abelianSheafFunctor : (abelianSheafFunctor f).Faithful := by
  have := (Stacks.SheafOfModules.moduleULiftFullyFaithful.{u + 1, u}
    (basePullbackRingSheaf f)).faithful
  exact Functor.Faithful.comp _ _

/-- **`Γ(Y, M_ab) ≅ Γ(Y, M)` as abelian groups**, naturally in the sheaf of `f^{-1}𝒪_S`-modules
`M`: global sections of a sheaf on `Y` are its sections over the terminal open `⊤`. -/
def baseGlobalSectionsForgetIso :
    abelianSheafFunctor f ⋙ Sheaf.Γ (Opens.grothendieckTopology ↥Y) AddCommGrpCat.{u + 1} ≅
      baseGlobalSectionsFunctor f ⋙ forget₂ (ModuleCat.{u + 1} ↥Γ(S, ⊤)) AddCommGrpCat.{u + 1} :=
  Functor.isoWhiskerLeft (abelianSheafFunctor f)
      (Sheaf.ΓNatIsoSheafSections (Opens.grothendieckTopology ↥Y) AddCommGrpCat.{u + 1}
        isTerminalTop) ≪≫
    NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

section Derived

variable [HasDerivedCategory.{w₁} (TwistedModules f)]
  [HasDerivedCategory.{w₂} (ModuleCat.{u + 1} ↥Γ(S, ⊤))]
  [HasDerivedCategory.{w₃} (Sheaf (Opens.grothendieckTopology ↥Y) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w₄} AddCommGrpCat.{u + 1}]

omit [HasDerivedCategory (TwistedModules f)]
  [HasDerivedCategory (ModuleCat.{u + 1} ↥Γ(S, ⊤))] in
/-- **The underlying abelian sheaf of an injective sheaf of `f^{-1}𝒪_S`-modules is right acyclic
for `Γ(Y, -)`**: the universe lift of an injective sheaf of modules is injective, and the
underlying abelian sheaf of an injective sheaf of modules is acyclic for global sections. -/
theorem rightAcyclic_abelianSheafFunctor_obj_of_injective (I : TwistedModules f) [Injective I] :
    (Sheaf.Γ (Opens.grothendieckTopology ↥Y) AddCommGrpCat.{u + 1}).rightAcyclic
      ((abelianSheafFunctor f).obj I) := by
  have := Stacks.SheafOfModules.preservesInjectiveObjects_moduleULift_max.{u + 1}
    (basePullbackRingSheaf f)
  have : Injective ((Stacks.SheafOfModules.moduleULift.{u + 1, u}
      (basePullbackRingSheaf f)).obj I) :=
    Functor.injective_obj _ I
  exact Stacks.Cohomology.GlobalSections.rightAcyclic_Γ_toSheaf_obj_of_injective.{w₃, w₄, u + 1,
    u, u, u} (Opens.grothendieckTopology ↥Y) (basePullbackRingSheaf f) _

/-- **Forgetting the module structure commutes with `RΓ(Y, -)`**, as functors
`D⁺(Mod_{f^{-1}𝒪_S}) ⥤ D⁺(Ab)`: taking the underlying complex of abelian sheaves and then
`RΓ(Y, -)` is the same as taking the `A`-linear `RΓ(Y, -)` and then forgetting the `A`-module
structure. -/
def derivedBaseGlobalSectionsFunctorForgetIso :
    (abelianSheafFunctor f).mapDerivedCategoryPlus ⋙
        (Sheaf.Γ (Opens.grothendieckTopology ↥Y) AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus ≅
      (baseGlobalSectionsFunctor f).rightDerivedFunctorPlus ⋙
        (forget₂ (ModuleCat.{u + 1} ↥Γ(S, ⊤)) AddCommGrpCat.{u + 1}).mapDerivedCategoryPlus :=
  Stacks.Cohomology.BoundedBelowComplexes.derivedBaseChangePlusIso (abelianSheafFunctor f)
    (forget₂ (ModuleCat.{u + 1} ↥Γ(S, ⊤)) AddCommGrpCat.{u + 1}) (baseGlobalSectionsFunctor f)
    (Sheaf.Γ (Opens.grothendieckTopology ↥Y) AddCommGrpCat.{u + 1})
    (baseGlobalSectionsForgetIso f)
    (fun I _ => rightAcyclic_abelianSheafFunctor_obj_of_injective f I)

omit [HasDerivedCategory (TwistedModules f)] [HasDerivedCategory (ModuleCat.{u + 1} ↥Γ(S, ⊤))]
  [HasDerivedCategory AddCommGrpCat.{u + 1}] in
/-- **The underlying complex of abelian sheaves `K_ab` of a complex `K` of sheaves of
`f^{-1}𝒪_S`-modules concentrated in non-negative degrees, as an object of `D⁺(Ab(Y))`**: apply
`abelianSheafFunctor f` termwise, extend over `ℤ` by zero and quotient. -/
def abelianPlusObjectOfCochainComplex (K : CochainComplex (TwistedModules f) ℕ) :
    DerivedCategory.Plus (Sheaf (Opens.grothendieckTopology ↥Y) AddCommGrpCat.{u + 1}) :=
  DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient _).obj
    ⟨(((abelianSheafFunctor f).mapHomologicalComplex _).obj K).extend ComplexShape.embeddingUpNat,
      ⟨0, inferInstance⟩⟩)

omit [HasDerivedCategory (ModuleCat.{u + 1} ↥Γ(S, ⊤))]
  [HasDerivedCategory AddCommGrpCat.{u + 1}] in
/-- The underlying abelian sheaf functor, on `D⁺`, carries the complex `K` to its underlying
complex of abelian sheaves. -/
def mapDerivedCategoryPlusObjIso (K : CochainComplex (TwistedModules f) ℕ) :
    (abelianSheafFunctor f).mapDerivedCategoryPlus.obj (plusObjectOfCochainComplex f K) ≅
      abelianPlusObjectOfCochainComplex f K :=
  (abelianSheafFunctor f).mapDerivedCategoryPlusFactorsh.app _ ≪≫
    DerivedCategory.Plus.Qh.mapIso (ObjectProperty.isoMk _
      ((HomotopyCategory.quotient _ _).mapIso
        (HomologicalComplex.mapHomologicalComplexExtendIso (abelianSheafFunctor f) K
          ComplexShape.embeddingUpNat).symm))

/-- **`forget(RΓ(Y, K)) ≅ RΓ(Y, K_ab)` in `D⁺(Ab)`.**  The image under the forgetful functor
`D⁺(Mod_A) ⥤ D⁺(Ab)` of the `A`-linear derived global sections
`AlgebraicGeometry.Scheme.Hom.derivedBaseGlobalSections f K` is the derived global sections of
the underlying complex of abelian sheaves of `K`.  It is the component at `K` of
`derivedBaseGlobalSectionsFunctorForgetIso`, hence natural in `K` as an object of
`D⁺(Mod_{f^{-1}𝒪_S})`. -/
def derivedBaseGlobalSectionsForgetIso (K : CochainComplex (TwistedModules f) ℕ) :
    (forget₂ (ModuleCat.{u + 1} ↥Γ(S, ⊤)) AddCommGrpCat.{u + 1}).mapDerivedCategoryPlus.obj
        (derivedBaseGlobalSections f K) ≅
      (Sheaf.Γ (Opens.grothendieckTopology ↥Y) AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus.obj
        (abelianPlusObjectOfCochainComplex f K) :=
  ((derivedBaseGlobalSectionsFunctorForgetIso f).app (plusObjectOfCochainComplex f K)).symm ≪≫
    (Sheaf.Γ (Opens.grothendieckTopology ↥Y) AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus.mapIso
      (mapDerivedCategoryPlusObjIso f K)

end Derived

end AlgebraicGeometry.Scheme.Hom

end
