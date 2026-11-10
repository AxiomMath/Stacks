module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.AdditiveSheafAssociatedStructure
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleCoefficientLift
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.TopDegreeVanishing
public import StacksFrontier.AlgebraicGeometry.Cohomology.HypercoveringModuleComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.ConstantSequenceDatum
public import StacksFrontier.AlgebraicGeometry.EulerCharAdditivity.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleCohomologyFilteredColimits
public import StacksFrontier.Topology.Sheaves.Cohomology.CechToCohomology.AffineCovering
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.PushforwardCohomologyCollapseUnconditional
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.CohomologyAtTheTerminalObjectUnconditional

/-!
# The étale cohomology of `𝐆_a` is the cohomology of the structure sheaf, `k`-linearly

Let `X` be a scheme over a field `k`. This file identifies the étale cohomology of `𝐆_a`, at the
coefficient universe `AddCommGrpCat.{u + 1}` used by the Artin–Schreier sequence, with the
cohomology `H^n(X, 𝒪_X)` of the structure sheaf, in every degree and `k`-linearly, and deduces
the Frobenius comparison for `𝐆_a` in every degree.

The identification is the composite of the coefficient lift `H^n(X_étale, 𝐆_a^{(u)}) ≅
H^n(X_étale, 𝐆_a)`, of [Stacks, Tag 03P6] (`𝐆_a` is the associated sheaf of `𝒪_X`), of
[Stacks, Tag 03P2] for the small étale site
(`AlgebraicGeometry.smallEtaleQuasiCoherentGlobalCohomologyIso`) and of the comparison of the
derived functors of sections of sheaves of modules and of abelian sheaves. `k`-linearity is
proved by checking that each step is natural with respect to multiplication by a global
function, which is an endomorphism of the sheaves involved.

## Main definitions

* `Stacks.ArtinSchreier.gaScalar`: multiplication by a global function on `𝐆_a`.
* `Stacks.ArtinSchreier.gaCohomologyAddEquiv`: `H^n(X_étale, 𝐆_a) ≃+ H^n(X, 𝒪_X)`.
* `Stacks.ArtinSchreier.gaFrobeniusComparison`: the Frobenius comparison of [Stacks, Tag 03P2]
  for `𝐆_a`, in every degree.

## Main results

* `Stacks.ArtinSchreier.gaCohomologyAddEquiv_map_gaScalar`: the identification is `k`-linear.
* `Stacks.ArtinSchreier.subsingleton_sheafH_additiveSheaf_of_isZero_hgroup_allDegrees`: vanishing
  of `H^i(X, 𝒪_X)` implies vanishing of `H^i(X_étale, 𝐆_a)`.

## References

* [Stacks Project, Tag 03P2](https://stacks.math.columbia.edu/tag/03P2)
* [Stacks Project, Tag 03P6](https://stacks.math.columbia.edu/tag/03P6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry

universe u

namespace Stacks.ArtinSchreier

variable {X : Scheme.{u}}

/-- The global function `r` of `X`, pulled back to an étale `X`-scheme. -/
abbrev etaleRestrict (U : X.Etale) (r : Γ(X, ⊤)) : Γ(U.left, ⊤) := U.hom.appTop r

/-- Pulling `etaleRestrict U r` back along a morphism `g : V ⟶ U` of étale `X`-schemes gives
`etaleRestrict V r`. -/
theorem etaleRestrict_map {U V : X.Etale} (g : V ⟶ U) (r : Γ(X, ⊤)) :
    g.left.appTop (etaleRestrict U r) = etaleRestrict V r := by
  change (g.left ≫ U.hom).appTop r = V.hom.appTop r
  rw [MorphismProperty.Over.w g]

/-- Multiplication by a global function, on `𝐆_a` at coefficients `AddCommGrpCat.{u}`. -/
def gaBaseScalar (r : Γ(X, ⊤)) : additiveSheafBase X ⟶ additiveSheafBase X :=
  ⟨{ app := fun U => AddCommGrpCat.ofHom
        (show Γ(U.unop.left, ⊤) →+ Γ(U.unop.left, ⊤) from
          AddMonoidHom.mulLeft (etaleRestrict U.unop r))
     naturality := fun U V g => AddCommGrpCat.hom_ext (AddMonoidHom.ext
        fun (x : Γ(U.unop.left, ⊤)) => by
          change etaleRestrict V.unop r * g.unop.left.appTop x =
            g.unop.left.appTop (etaleRestrict U.unop r * x)
          rw [map_mul, etaleRestrict_map]) }⟩

/-- On sections over an étale `X`-scheme `U`, `gaBaseScalar r` is multiplication by
`etaleRestrict U r`. -/
@[simp]
theorem gaBaseScalar_app (r : Γ(X, ⊤)) (U : X.Etale) (x : Γ(U.left, ⊤)) :
    (show Γ(U.left, ⊤) from (gaBaseScalar r).hom.app (op U) x) = etaleRestrict U r * x :=
  rfl

/-- Multiplication by a global function, on `𝐆_a` at coefficients `AddCommGrpCat.{u + 1}`. -/
def gaScalar (r : Γ(X, ⊤)) : additiveSheaf.{u, u + 1} X ⟶ additiveSheaf.{u, u + 1} X :=
  ⟨{ app := fun U => AddCommGrpCat.ofHom
        (show ULift.{u + 1} Γ(U.unop.left, ⊤) →+ ULift.{u + 1} Γ(U.unop.left, ⊤) from
          AddEquiv.ulift.symm.toAddMonoidHom.comp
            ((AddMonoidHom.mulLeft (etaleRestrict U.unop r)).comp AddEquiv.ulift.toAddMonoidHom))
     naturality := fun U V g => AddCommGrpCat.hom_ext (AddMonoidHom.ext
        fun (x : ULift.{u + 1} Γ(U.unop.left, ⊤)) => by
          change ULift.up (etaleRestrict V.unop r * g.unop.left.appTop x.down) =
            ULift.up (g.unop.left.appTop (etaleRestrict U.unop r * x.down))
          rw [map_mul, etaleRestrict_map]) }⟩

/-- On sections over an étale `X`-scheme `U`, `gaScalar r` is multiplication by
`etaleRestrict U r`. -/
theorem gaScalar_app_ofSection (r : Γ(X, ⊤)) (U : X.Etale) (x : Γ(U.left, ⊤)) :
    (gaScalar r).hom.app (op U) (ofSection.{u, u + 1} x) =
      ofSection.{u, u + 1} (etaleRestrict U r * x) :=
  rfl

/-- The universe lift of `gaBaseScalar` is `gaScalar`. -/
theorem map_gaBaseScalar_comp_uliftIso (r : Γ(X, ⊤)) :
    (sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).map
        (gaBaseScalar r) ≫ (additiveSheafBaseUliftIso X).hom =
      (additiveSheafBaseUliftIso X).hom ≫ gaScalar r := by
  ext U x
  rfl

/-- When `p = 0` in `Γ(X, ⊤)`, multiplication by `r` followed by the Frobenius of `𝐆_a` is the
Frobenius followed by multiplication by `r ^ p`. -/
theorem gaScalar_comp_frobeniusMap {p : ℕ} (hp : p.Prime) (hX : (p : Γ(X, ⊤)) = 0)
    (r : Γ(X, ⊤)) :
    gaScalar r ≫ frobeniusMap.{u, u + 1} X hp hX =
      frobeniusMap.{u, u + 1} X hp hX ≫ gaScalar (r ^ p) := by
  ext U x
  obtain ⟨x, rfl⟩ := ofSection_surjective.{u, u + 1} (U := U.unop) x
  change ofSection.{u, u + 1} ((etaleRestrict U.unop r * x) ^ p) =
    ofSection.{u, u + 1} (etaleRestrict U.unop (r ^ p) * x ^ p)
  refine congrArg (ofSection.{u, u + 1} (U := U.unop)) ?_
  rw [mul_pow, etaleRestrict, etaleRestrict, map_pow]

/-! ### The Zariski side -/


/-- **Under `f^* 𝒪_X ≅ 𝒪_Y` the pullback of a section over `U` is its image under `appLE`.** -/
theorem pullbackUnitIso_hom_app_top_pullbackSectionHom_of_le {X Y : Scheme.{u}} (f : Y ⟶ X)
    (U : X.Opens) (h : (⊤ : Y.Opens) ≤ f ⁻¹ᵁ U) (x : Γ(Scheme.unitModule X, U)) :
    (Scheme.Modules.pullbackUnitIso f).hom.app ⊤
        (pullbackSectionHom f (Scheme.unitModule X) U ⊤ h x) = f.appLE U ⊤ h x := by
  have h1 : (Scheme.Modules.pullbackUnitIso f).hom.app (f ⁻¹ᵁ U)
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
          (Scheme.unitModule X)).app U x) =
      (Scheme.Modules.unitToPushforwardUnit f).app U x := by
    have h0 := Scheme.Modules.pullbackUnitIso_homEquiv f
    rw [Adjunction.homEquiv_unit] at h0
    have h0' := congrArg (fun ψ => Scheme.Modules.Hom.app ψ U) h0
    simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app] at h0'
    exact congr($h0' x)
  have h2 : (Scheme.Modules.pullbackUnitIso f).hom.app ⊤
        (pullbackSectionHom f (Scheme.unitModule X) U ⊤ h x) =
      (Scheme.unitModule Y).presheaf.map (homOfLE h).op
        ((Scheme.Modules.pullbackUnitIso f).hom.app (f ⁻¹ᵁ U)
          (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
            (Scheme.unitModule X)).app U x)) :=
    Scheme.Modules.Hom.app_presheaf_map _ (homOfLE h) _
  rw [h2, h1]
  rfl

section ModuleScalar

open Stacks.Cohomology.HypercoveringModules

/-- Multiplication by a global function, as an endomorphism of the structure sheaf viewed as a
module over itself: the action of `r` in the `Γ(X, ⊤)`-linear category of `𝒪_X`-modules. -/
def moduleScalar (r : Γ(X, ⊤)) : Scheme.unitModule X ⟶ Scheme.unitModule X :=
  letI := globalSectionsLinear X
  ((show X.ringCatSheaf.obj.obj (op (⊤ : X.Opens)) from r) •
    𝟙 (show SheafOfModules.{u} X.ringCatSheaf from Scheme.unitModule X) :)

/-- On sections over an open `V`, `moduleScalar r` is multiplication by the restriction of `r`
to `V`. -/
theorem moduleScalar_app (r : Γ(X, ⊤)) (V : X.Opens) (x : Γ(X, V)) :
    (moduleScalar r).app V x = X.presheaf.map (homOfLE le_top).op r * x :=
  let := globalSectionsLinear X
  Stacks.SheafOfModules.smul_val_app X.ringCatSheaf _ ⊤ isTerminalTop (RingHom.id _) r
    (𝟙 (show SheafOfModules.{u} X.ringCatSheaf from Scheme.unitModule X)) (op V) x

/-- The identification `𝒪_X ≅ ε_* 𝐆_a` of abelian sheaves on the opens of `X`: pull a section
back to the open subscheme, the composite of [Stacks, Tag 03P6] with the unit of
`AlgebraicGeometry.smallEtaleSectionsUnitIso`. -/
def structureSheafIsoPushforwardGa :
    (SheafOfModules.toSheaf X.ringCatSheaf).obj (Scheme.unitModule X) ≅
      (smallEtaleZariskiPushforward X).obj (additiveSheafBase X) :=
  smallEtaleSectionsUnitIso X (Scheme.unitModule X) ≪≫
    (smallEtaleZariskiPushforward X).mapIso (additiveSheafBaseIsoSmallEtaleAssociatedSheaf X).symm

/-- `structureSheafIsoPushforwardGa` sends a section of `𝒪_X` over `V` to its image under
`V.ι.appLE`, a global function on the open subscheme `V`. -/
theorem structureSheafIsoPushforwardGa_hom_app (V : X.Opens) (x : Γ(X, V)) :
    (structureSheafIsoPushforwardGa (X := X)).hom.hom.app (op V) x =
      V.ι.appLE V ⊤ (Scheme.Opens.top_le_ι_preimage le_rfl) x :=
  pullbackUnitIso_hom_app_top_pullbackSectionHom_of_le V.ι V _ x

/-- On sections over an open `V`, `structureSheafIsoPushforwardGa` carries multiplication by `r`
to multiplication by `etaleRestrict` of `r` to the étale `X`-scheme `V`. -/
theorem structureSheafIsoPushforwardGa_hom_app_moduleScalar (r : Γ(X, ⊤)) (V : X.Opens)
    (x : Γ(X, V)) :
    (structureSheafIsoPushforwardGa (X := X)).hom.hom.app (op V) ((moduleScalar r).app V x) =
      etaleRestrict ((opensToEtale X).obj V) r *
        (show Γ(((opensToEtale X).obj V).left, ⊤) from
          (structureSheafIsoPushforwardGa (X := X)).hom.hom.app (op V) x) := by
  have e1 := structureSheafIsoPushforwardGa_hom_app (X := X) V ((moduleScalar r).app V x)
  have e2 := structureSheafIsoPushforwardGa_hom_app (X := X) V x
  have e3 : V.ι.appLE V ⊤ (Scheme.Opens.top_le_ι_preimage le_rfl)
      (X.presheaf.map (homOfLE le_top).op r) = V.ι.appTop r := by
    rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE, AlgebraicGeometry.appLE_top_top_eq_appTop]
  refine e1.trans (Eq.trans ?_ (congrArg (etaleRestrict ((opensToEtale X).obj V) r * ·) e2.symm))
  refine (congrArg (V.ι.appLE V ⊤ (Scheme.Opens.top_le_ι_preimage le_rfl))
    (moduleScalar_app r V x)).trans ?_
  exact (map_mul _ _ _).trans (congrArg (· * _) e3)

/-- **`𝒪_X ≅ ε_* 𝐆_a` intertwines multiplication by a global function on both sides.** -/
theorem moduleScalar_comp_structureSheafIsoPushforwardGa (r : Γ(X, ⊤)) :
    (SheafOfModules.toSheaf X.ringCatSheaf).map (moduleScalar r) ≫
        (structureSheafIsoPushforwardGa (X := X)).hom =
      (structureSheafIsoPushforwardGa (X := X)).hom ≫
        (smallEtaleZariskiPushforward X).map (gaBaseScalar r) := by
  ext V x
  exact structureSheafIsoPushforwardGa_hom_app_moduleScalar r V.unop x

end ModuleScalar

end Stacks.ArtinSchreier

namespace AlgebraicGeometry

variable {X : Scheme.{u}} [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

/-- The natural isomorphism whose components are `hgroupIsoSheafCohomology`: positive-degree
cohomology of a module computed in `Mod(𝒪_X)` is the cohomology of its underlying abelian sheaf. -/
def hgroupNatIso (U : X.Opens) (n : ℕ) :
    Hfunctor X.ringCatSheaf U (n + 1) ≅
      SheafOfModules.toSheaf X.ringCatSheaf ⋙
        (Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) (n + 1) ⋙
          (evaluation _ _).obj (op U)) :=
  (ModuleSheafCohomology.sectionsComparisonIso (Opens.grothendieckTopology X)
      X.ringCatSheaf U (n + 1)) ≪≫
    (Functor.isoWhiskerLeft (SheafOfModules.toSheaf X.ringCatSheaf)
      (ModuleSheafCohomology.rightDerivedIso
          (ModuleSheafCohomology.evaluationRepresentation
            (Opens.grothendieckTopology X) U) (n + 1) ≪≫
        ModuleSheafCohomology.rightDerivedCoyonedaSuccIso _ n))

end AlgebraicGeometry

namespace Stacks.Cohomology.CoefficientLift

universe v₃ w₃ t₃ z₃

/-- **The coefficient-universe comparison of sheaf cohomology is natural in the sheaf.** -/
theorem sheafHUliftAddEquiv_map
    {C : Type*} [Category* C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{v₃}] [HasSheafify J AddCommGrpCat.{max v₃ t₃}]
    [J.PreservesSheafification AddCommGrpCat.uliftFunctor.{t₃, v₃}]
    [(sheafCompose J AddCommGrpCat.uliftFunctor.{t₃, v₃}).PreservesInjectiveObjects]
    [EnoughInjectives (Sheaf J AddCommGrpCat.{v₃})]
    [HasExt.{w₃} (Sheaf J AddCommGrpCat.{v₃})] [HasExt.{z₃} (Sheaf J AddCommGrpCat.{max v₃ t₃})]
    {F G : Sheaf J AddCommGrpCat.{v₃}} (g : F ⟶ G) (n : ℕ) (x : Sheaf.H.{w₃} F n) :
    sheafHUliftAddEquiv.{v₃, w₃, t₃, z₃} J G n (Sheaf.H.map g n x) =
      Sheaf.H.map ((sheafCompose J AddCommGrpCat.uliftFunctor.{t₃, v₃}).map g) n
        (sheafHUliftAddEquiv.{v₃, w₃, t₃, z₃} J F n x) := by
  let L := sheafCompose J AddCommGrpCat.uliftFunctor.{t₃, v₃}
  have : L.Additive := ⟨by intros; rfl⟩
  have : PreservesFiniteLimits L :=
    AlgebraicGeometry.Space.sheafCompose_uliftFunctor_preservesFiniteLimits.{v₃, t₃} J
  have : PreservesFiniteColimits L :=
    AlgebraicGeometry.Space.sheafCompose_uliftFunctor_preservesFiniteColimits.{v₃, t₃} J
  have h1 : (x.comp (Abelian.Ext.mk₀ g) (add_zero n)).mapExactFunctor L =
      (x.mapExactFunctor L).comp (Abelian.Ext.mk₀ (L.map g)) (add_zero n) := by
    rw [Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀]
  have h2 := ConcreteCategory.congr_hom
    (((extFunctor.{z₃} n).mapIso (constantSheafUliftIso.{v₃, t₃} J).symm.op).inv.naturality
      (L.map g)) (x.mapExactFunctor L)
  exact (congrArg (ConcreteCategory.hom
    (((extFunctor.{z₃} n).mapIso (constantSheafUliftIso.{v₃, t₃} J).symm.op).inv.app (L.obj G)))
      h1).trans h2

end Stacks.Cohomology.CoefficientLift

namespace Stacks.ArtinSchreier

open Stacks.Cohomology.HypercoveringModules

section Assembly

universe v₄ w₄

/-- Cohomology along an isomorphism of sheaves, as an additive equivalence. -/
def sheafHAddEquivOfIso {C : Type*} [Category* C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{v₄}] [HasExt.{w₄} (Sheaf J AddCommGrpCat.{v₄})]
    {F G : Sheaf J AddCommGrpCat.{v₄}} (e : F ≅ G) (n : ℕ) :
    Sheaf.H.{w₄} F n ≃+ Sheaf.H.{w₄} G n :=
  ((Sheaf.functorH J n).mapIso e).addCommGroupIsoToAddEquiv

/-- `sheafHAddEquivOfIso e n` is the map on cohomology induced by `e.hom`. -/
theorem sheafHAddEquivOfIso_apply {C : Type*} [Category* C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{v₄}] [HasExt.{w₄} (Sheaf J AddCommGrpCat.{v₄})]
    {F G : Sheaf J AddCommGrpCat.{v₄}} (e : F ≅ G) (n : ℕ) (x : Sheaf.H.{w₄} F n) :
    sheafHAddEquivOfIso e n x = Sheaf.H.map e.hom n x :=
  rfl

attribute [local instance] Stacks.Topology.hasExt_sheafOpens
  Stacks.Topology.enoughInjectives_sheafOpens
  Stacks.Cohomology.BiggerSite.preservesInjectiveObjects_sheafPushforwardContinuous

/-- `Ext` of abelian sheaves at the morphism universe of the small étale site. -/
local instance hasExt_smallEtale_u (X : Scheme.{u}) :
    HasExt.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
  haveI : IsGrothendieckAbelian.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
    Scheme.isGrothendieckAbelian_sheaf_smallEtaleTopology X AddCommGrpCat.{u}
  CategoryTheory.IsGrothendieckAbelian.hasExt _

/-- Enough injectives for abelian sheaves at the morphism universe of the small étale site. -/
local instance enoughInjectives_smallEtale_u (X : Scheme.{u}) :
    EnoughInjectives (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
  haveI : IsGrothendieckAbelian.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
    Scheme.isGrothendieckAbelian_sheaf_smallEtaleTopology X AddCommGrpCat.{u}
  IsGrothendieckAbelian.enoughInjectives

/-- `Ext` of abelian sheaves at the object universe of the small étale site. -/
local instance (priority := high) hasExt_smallEtale_succ (X : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  haveI : IsGrothendieckAbelian.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale_objectUniverse X
  CategoryTheory.IsGrothendieckAbelian.hasExt _

variable {X : Scheme.{u}}

/-- Raising the coefficients of `𝐆_a` from `AddCommGrpCat.{u}` to `AddCommGrpCat.{u + 1}`. -/
def gaUliftAddEquiv (m : ℕ) :
    Sheaf.H.{u} (additiveSheafBase X) m ≃+ Sheaf.H.{u + 1} (additiveSheaf.{u, u + 1} X) m :=
  (smallEtaleSheafHUliftAddEquiv X (additiveSheafBase X) m).trans
    (sheafHAddEquivOfIso (additiveSheafBaseUliftIso X) m)

/-- `gaUliftAddEquiv` carries the action of `gaBaseScalar r` on cohomology to the action of
`gaScalar r`. -/
theorem gaUliftAddEquiv_map_gaBaseScalar (r : Γ(X, ⊤)) (m : ℕ)
    (y : Sheaf.H.{u} (additiveSheafBase X) m) :
    gaUliftAddEquiv m (Sheaf.H.map (gaBaseScalar r) m y) =
      Sheaf.H.map (gaScalar r) m (gaUliftAddEquiv m y) := by
  have : HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
    etaleSheaves_hasSheafify_of_univLE.{u, u + 1} X
  have := (etaleUlift_properties.{u, u, u + 1} X).1
  have := (etaleUlift_properties.{u, u, u + 1} X).2
  have h := Stacks.Cohomology.CoefficientLift.sheafHUliftAddEquiv_map.{u, u, u + 1, u + 1}
    X.smallEtaleTopology (gaBaseScalar r) m y
  simp only [gaUliftAddEquiv, AddEquiv.trans_apply, sheafHAddEquivOfIso_apply]
  change Sheaf.H.map _ m
    (Stacks.Cohomology.CoefficientLift.sheafHUliftAddEquiv.{u, u, u + 1, u + 1}
      X.smallEtaleTopology _ m (Sheaf.H.map (gaBaseScalar r) m y)) = _
  rw [h, ← Sheaf.H.map_comp_apply, map_gaBaseScalar_comp_uliftIso, Sheaf.H.map_comp_apply]
  rfl

/-- [Stacks, Tag 03P6] on cohomology. -/
def gaAssocAddEquiv (m : ℕ) :
    Sheaf.H.{u} (additiveSheafBase X) m ≃+
      Sheaf.H.{u} (smallEtaleAssociatedSheaf X (Scheme.unitModule X)) m :=
  sheafHAddEquivOfIso (additiveSheafBaseIsoSmallEtaleAssociatedSheaf X) m

/-- Multiplication by a global function, on the associated sheaf of the structure module. -/
def assocScalar (r : Γ(X, ⊤)) :
    smallEtaleAssociatedSheaf X (Scheme.unitModule X) ⟶
      smallEtaleAssociatedSheaf X (Scheme.unitModule X) :=
  (additiveSheafBaseIsoSmallEtaleAssociatedSheaf X).inv ≫ gaBaseScalar r ≫
    (additiveSheafBaseIsoSmallEtaleAssociatedSheaf X).hom

/-- `gaAssocAddEquiv` carries the action of `gaBaseScalar r` on cohomology to the action of
`assocScalar r`. -/
theorem gaAssocAddEquiv_map_gaBaseScalar (r : Γ(X, ⊤)) (m : ℕ)
    (y : Sheaf.H.{u} (additiveSheafBase X) m) :
    gaAssocAddEquiv m (Sheaf.H.map (gaBaseScalar r) m y) =
      Sheaf.H.map (assocScalar r) m (gaAssocAddEquiv m y) := by
  simp only [gaAssocAddEquiv, sheafHAddEquivOfIso_apply, assocScalar, ← Sheaf.H.map_comp_apply,
    Iso.hom_inv_id_assoc]

/-- The square of `AlgebraicGeometry.smallEtaleSectionsUnitIso` with the scalars. -/
theorem moduleScalar_comp_smallEtaleSectionsUnitIso (r : Γ(X, ⊤)) :
    (SheafOfModules.toSheaf X.ringCatSheaf).map (moduleScalar r) ≫
        (smallEtaleSectionsUnitIso X (Scheme.unitModule X)).hom =
      (smallEtaleSectionsUnitIso X (Scheme.unitModule X)).hom ≫
        (smallEtaleZariskiPushforward X).map (assocScalar r) := by
  have h := congrArg (· ≫ (smallEtaleZariskiPushforward X).map
    (additiveSheafBaseIsoSmallEtaleAssociatedSheaf X).hom)
      (moduleScalar_comp_structureSheafIsoPushforwardGa (X := X) r)
  simp only [structureSheafIsoPushforwardGa, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    Category.assoc, ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
    Category.comp_id] at h
  rw [h, assocScalar]

/-- Positive-degree cohomology of the structure module is étale cohomology of its associated
sheaf: [Stacks, Tag 03P2] for `𝒞 = X_étale`, read through `hgroupNatIso`. -/
def hgroupAssocIso (n : ℕ) :
    Hgroup X.ringCatSheaf ⊤ (n + 1) (Scheme.unitModule X) ≅
      AddCommGrpCat.of
        (Sheaf.H.{u} (smallEtaleAssociatedSheaf X (Scheme.unitModule X)) (n + 1)) :=
  (hgroupNatIso (X := X) ⊤ n).app
      (show SheafOfModules.{u} X.ringCatSheaf from Scheme.unitModule X) ≪≫
    smallEtaleQuasiCoherentGlobalCohomologyIso X (Scheme.unitModule X) (n + 1) ≪≫
    Stacks.Cohomology.TerminalCohomology.h'IsoH (Scheme.smallEtaleTopology X)
      (smallEtaleAssociatedSheaf X (Scheme.unitModule X)) (n + 1) _
      (isTerminal_opensToEtale_top X)

/-- `AlgebraicGeometry.smallEtaleQuasiCoherentGlobalCohomologyIso` for the structure module
intertwines the actions of `moduleScalar r` and `assocScalar r` on cohomology in degree `n + 1`. -/
theorem smallEtaleQuasiCoherentGlobalCohomologyIso_naturality (r : Γ(X, ⊤)) (n : ℕ) :
    ((Sheaf.cohomologyPresheafFunctor _ (n + 1)).map
        ((SheafOfModules.toSheaf X.ringCatSheaf).map (moduleScalar r))).app (op ⊤) ≫
      (smallEtaleQuasiCoherentGlobalCohomologyIso X (Scheme.unitModule X) (n + 1)).hom =
    (smallEtaleQuasiCoherentGlobalCohomologyIso X (Scheme.unitModule X) (n + 1)).hom ≫
      ((Sheaf.cohomologyPresheafFunctor (Scheme.smallEtaleTopology X) (n + 1)).map
        (assocScalar r)).app (op ((opensToEtale X).obj ⊤)) := by
  have hsq := moduleScalar_comp_smallEtaleSectionsUnitIso (X := X) r
  have h1 : ((Sheaf.cohomologyPresheafFunctor _ (n + 1)).map
        ((SheafOfModules.toSheaf X.ringCatSheaf).map (moduleScalar r))).app (op ⊤) ≫
      ((Sheaf.cohomologyPresheafFunctor _ (n + 1)).mapIso
        (smallEtaleSectionsUnitIso X (Scheme.unitModule X))).hom.app (op ⊤) =
      ((Sheaf.cohomologyPresheafFunctor _ (n + 1)).mapIso
        (smallEtaleSectionsUnitIso X (Scheme.unitModule X))).hom.app (op ⊤) ≫
      ((Sheaf.cohomologyPresheafFunctor _ (n + 1)).map
        ((smallEtaleZariskiPushforward X).map (assocScalar r))).app (op ⊤) := by
    rw [Functor.mapIso_hom, ← NatTrans.comp_app, ← Functor.map_comp, hsq, Functor.map_comp,
      NatTrans.comp_app]
  have h2 := Stacks.Cohomology.BiggerSite.sheafCohomologyPushforwardIso_hom_naturality
    (Opens.grothendieckTopology X) (Scheme.smallEtaleTopology X) (opensToEtale X)
    (assocScalar r) ⊤ (n + 1)
    (fun q hq _ ↦ isZero_rightDerived_pushforward_opensToEtale X (Scheme.unitModule X) q hq)
    (fun q hq _ ↦ isZero_rightDerived_pushforward_opensToEtale X (Scheme.unitModule X) q hq)
  unfold smallEtaleQuasiCoherentGlobalCohomologyIso smallEtaleQuasiCoherentCohomologyIso
  rw [Iso.trans_hom, Iso.app_hom, ← Category.assoc, h1, Category.assoc, h2, Category.assoc]

/-- `hgroupAssocIso n` intertwines the actions of `moduleScalar r` and `assocScalar r` on
cohomology. -/
theorem hgroupAssocIso_naturality (r : Γ(X, ⊤)) (n : ℕ) :
    (Hfunctor X.ringCatSheaf ⊤ (n + 1)).map (moduleScalar r) ≫ (hgroupAssocIso n).hom =
      (hgroupAssocIso n).hom ≫ (Sheaf.functorH _ (n + 1)).map (assocScalar r) := by
  have h0 := (hgroupNatIso (X := X) ⊤ n).hom.naturality (moduleScalar r)
  have h1 := smallEtaleQuasiCoherentGlobalCohomologyIso_naturality (X := X) r n
  have h2 := Stacks.Cohomology.TerminalCohomology.h'IsoH_hom_naturality
    (Scheme.smallEtaleTopology X) (assocScalar r) (n + 1) _ (isTerminal_opensToEtale_top X)
  change _ = _ ≫ (Sheaf.functorH _ (n + 1)).map (assocScalar r) at h2
  unfold hgroupAssocIso
  rw [Iso.trans_hom, Iso.trans_hom, Iso.app_hom, ← Category.assoc, h0, Category.assoc,
    show (SheafOfModules.toSheaf X.ringCatSheaf ⋙
        Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) (n + 1) ⋙
          (evaluation _ AddCommGrpCat).obj (op ⊤)).map (moduleScalar r) =
      ((Sheaf.cohomologyPresheafFunctor _ (n + 1)).map
        ((SheafOfModules.toSheaf X.ringCatSheaf).map (moduleScalar r))).app (op ⊤) from rfl,
    reassoc_of% h1, h2]
  simp only
  rfl

variable (k : Type u) [Field k] (f : X ⟶ Spec (.of k))

/-- The ring map `k ⟶ Γ(X, ⊤)` along which `AlgebraicGeometry.cohomologyOverField` restricts
scalars. -/
def fieldToSections : k →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom

/-- **The right derived functors of global sections act on `moduleScalar r` by `r`.** -/
theorem rightDerived_map_moduleScalar_apply (r : Γ(X, ⊤)) (n : ℕ)
    (w : ((_root_.SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).rightDerived n).obj
      (Scheme.unitModule X)) :
    ((_root_.SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).rightDerived n).map
        (moduleScalar r) w =
      (show X.ringCatSheaf.obj.obj (op (⊤ : X.Opens)) from r) • w := by
  let := globalSectionsLinear X
  have h := Functor.Linear.map_smul
    (F := (_root_.SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).rightDerived n)
    (𝟙 (show SheafOfModules.{u} X.ringCatSheaf from Scheme.unitModule X))
    (show X.ringCatSheaf.obj.obj (op (⊤ : X.Opens)) from r)
  rw [CategoryTheory.Functor.map_id] at h
  exact congrArg (fun φ => φ.hom w) h

/-- **The étale cohomology of `𝐆_a` is the cohomology of `𝒪_X`, in positive degree.** -/
def gaCohomologyAddEquivSucc (n : ℕ) :
    Sheaf.H.{u + 1} (additiveSheaf.{u, u + 1} X) (n + 1) ≃+
      cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) (n + 1) :=
  (gaUliftAddEquiv (n + 1)).symm.trans <| (gaAssocAddEquiv (n + 1)).trans <|
    (hgroupAssocIso n).symm.addCommGroupIsoToAddEquiv.trans <|
      ((Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso X.ringCatSheaf ⊤
        (n + 1)).app (Scheme.unitModule X)).symm.addCommGroupIsoToAddEquiv

/-- In positive degree, `gaCohomologyAddEquivSucc` carries the action of
`gaScalar (fieldToSections k f a)` to scalar multiplication by `a : k`. -/
theorem gaCohomologyAddEquivSucc_map_gaScalar (a : k) (n : ℕ)
    (x : Sheaf.H.{u + 1} (additiveSheaf.{u, u + 1} X) (n + 1)) :
    gaCohomologyAddEquivSucc k f n (Sheaf.H.map (gaScalar (fieldToSections k f a)) (n + 1) x) =
      a • gaCohomologyAddEquivSucc k f n x := by
  set r := fieldToSections k f a
  obtain ⟨y, rfl⟩ := (gaUliftAddEquiv (X := X) (n + 1)).surjective x
  rw [← gaUliftAddEquiv_map_gaBaseScalar]
  simp only [gaCohomologyAddEquivSucc, AddEquiv.trans_apply, AddEquiv.symm_apply_apply]
  rw [gaAssocAddEquiv_map_gaBaseScalar]
  generalize gaAssocAddEquiv (n + 1) y = z
  obtain ⟨w, rfl⟩ := ((hgroupAssocIso (X := X) n).addCommGroupIsoToAddEquiv).surjective z
  have h3 := ConcreteCategory.congr_hom (hgroupAssocIso_naturality (X := X) r n) w
  have h4 := ConcreteCategory.congr_hom
    ((Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso X.ringCatSheaf ⊤
        (n + 1)).inv.naturality (moduleScalar r)) w
  change ((Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso X.ringCatSheaf ⊤
        (n + 1)).inv.app (Scheme.unitModule X))
      ((hgroupAssocIso n).inv (Sheaf.H.map (assocScalar r) (n + 1)
        ((hgroupAssocIso n).hom w))) =
    a • (show (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) (n + 1) : Type u) from
      ((Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso X.ringCatSheaf ⊤
        (n + 1)).inv.app (Scheme.unitModule X))
        ((hgroupAssocIso n).inv ((hgroupAssocIso n).hom w)))
  rw [Iso.hom_inv_id_apply]
  have h3' : Sheaf.H.map (assocScalar r) (n + 1) ((hgroupAssocIso n).hom w) =
      (hgroupAssocIso n).hom ((Hfunctor X.ringCatSheaf ⊤ (n + 1)).map (moduleScalar r) w) :=
    h3.symm
  rw [h3', Iso.hom_inv_id_apply]
  exact h4.trans (rightDerived_map_moduleScalar_apply r (n + 1) _)

/-- The étale `X`-scheme `X` itself, the final object of the small étale site. -/
def etaleSelf (X : Scheme.{u}) : X.Etale := MorphismProperty.Over.mk ⊤ (𝟙 X) (by infer_instance)

/-- `etaleSelf X` is a final object of the small étale site. -/
def isTerminal_etaleSelf (X : Scheme.{u}) : IsTerminal (etaleSelf X) :=
  letI : MorphismProperty.ContainsIdentities (@Etale : MorphismProperty Scheme.{u}) :=
    (HasRingHomProperty.isMultiplicative RingHom.Etale.stableUnderComposition
      RingHom.Etale.containsIdentities :
        MorphismProperty.IsMultiplicative
          (@Etale : MorphismProperty Scheme.{u})).toContainsIdentities
  MorphismProperty.Over.mkIdTerminal _ _

/-- **The étale cohomology of `𝐆_a` is the cohomology of `𝒪_X`, in degree zero**: both are the
global functions. -/
def gaCohomologyAddEquivZero :
    Sheaf.H.{u + 1} (additiveSheaf.{u, u + 1} X) 0 ≃+
      cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 0 :=
  (Sheaf.H.equiv₀ (additiveSheaf.{u, u + 1} X) (isTerminal_etaleSelf X)).trans <|
    AddEquiv.ulift.trans <|
      (show Γ(X, ⊤) ≃+ ((_root_.SheafOfModules.evaluation X.ringCatSheaf
          (op (⊤ : X.Opens))).rightDerived 0).obj (Scheme.unitModule X) from
        (((_root_.SheafOfModules.evaluation X.ringCatSheaf
          (op (⊤ : X.Opens))).rightDerivedZeroIsoSelf.app
            (Scheme.unitModule X)).symm.toLinearEquiv.toAddEquiv))

/-- In degree zero, `gaCohomologyAddEquivZero` carries the action of
`gaScalar (fieldToSections k f a)` to scalar multiplication by `a : k`. -/
theorem gaCohomologyAddEquivZero_map_gaScalar (a : k)
    (x : Sheaf.H.{u + 1} (additiveSheaf.{u, u + 1} X) 0) :
    gaCohomologyAddEquivZero k f (Sheaf.H.map (gaScalar (fieldToSections k f a)) 0 x) =
      a • gaCohomologyAddEquivZero k f x := by
  set r := fieldToSections k f a
  have h1 := (Sheaf.H.equiv₀_naturality (isTerminal_etaleSelf X) (gaScalar r) x).symm
  change ((_root_.SheafOfModules.evaluation X.ringCatSheaf
      (op (⊤ : X.Opens))).rightDerivedZeroIsoSelf.inv.app (Scheme.unitModule X))
      (Sheaf.H.equiv₀ (additiveSheaf.{u, u + 1} X) (isTerminal_etaleSelf X)
        (Sheaf.H.map (gaScalar r) 0 x)).down =
    a • (show (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 0 : Type u) from
      ((_root_.SheafOfModules.evaluation X.ringCatSheaf
        (op (⊤ : X.Opens))).rightDerivedZeroIsoSelf.inv.app (Scheme.unitModule X))
      (Sheaf.H.equiv₀ (additiveSheaf.{u, u + 1} X) (isTerminal_etaleSelf X) x).down)
  refine (congrArg (fun t => ((_root_.SheafOfModules.evaluation X.ringCatSheaf
      (op (⊤ : X.Opens))).rightDerivedZeroIsoSelf.inv.app (Scheme.unitModule X)) t.down)
    h1).trans ?_
  generalize Sheaf.H.equiv₀ (additiveSheaf.{u, u + 1} X) (isTerminal_etaleSelf X) x = y
  obtain ⟨y⟩ := y
  change Γ(X, ⊤) at y
  have h2 := ConcreteCategory.congr_hom
    ((_root_.SheafOfModules.evaluation X.ringCatSheaf
      (op (⊤ : X.Opens))).rightDerivedZeroIsoSelf.inv.naturality (moduleScalar r)) y
  have h3 : (moduleScalar r).app ⊤ y = r * y := by
    rw [moduleScalar_app]
    congr 1
    exact congrArg (fun φ => φ r) (show X.presheaf.map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op =
      𝟙 _ from by rw [show (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op = 𝟙 _ from
        Subsingleton.elim _ _, CategoryTheory.Functor.map_id])
  have h4 : etaleRestrict (etaleSelf X) r = r := by
    change (𝟙 X : X ⟶ X).appTop r = r
    rw [Scheme.Hom.id_appTop]
    rfl
  change ((_root_.SheafOfModules.evaluation X.ringCatSheaf
      (op (⊤ : X.Opens))).rightDerivedZeroIsoSelf.inv.app (Scheme.unitModule X))
      ((show Γ(X, ⊤) from etaleRestrict (etaleSelf X) r) * y) = _
  rw [h4, ← h3]
  exact h2.trans (rightDerived_map_moduleScalar_apply r 0 _)

/-- **The étale cohomology of `𝐆_a` is the cohomology of `𝒪_X`** (Stacks 03P2 for the structure
sheaf on the small étale site, at coefficients `AddCommGrpCat.{u + 1}`). -/
def gaCohomologyAddEquiv : (n : ℕ) →
    Sheaf.H.{u + 1} (additiveSheaf.{u, u + 1} X) n ≃+
      cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) n
  | 0 => gaCohomologyAddEquivZero k f
  | n + 1 => gaCohomologyAddEquivSucc k f n

/-- **The comparison is `k`-linear**: multiplication by a scalar of `k` on `𝐆_a` induces the
`k`-module structure of `H^n(X, 𝒪_X)`. -/
theorem gaCohomologyAddEquiv_map_gaScalar (a : k) :
    ∀ (n : ℕ) (x : Sheaf.H.{u + 1} (additiveSheaf.{u, u + 1} X) n),
      gaCohomologyAddEquiv k f n (Sheaf.H.map (gaScalar (fieldToSections k f a)) n x) =
        a • gaCohomologyAddEquiv k f n x
  | 0, x => gaCohomologyAddEquivZero_map_gaScalar k f a x
  | n + 1, x => gaCohomologyAddEquivSucc_map_gaScalar k f a n x

/-- **The Frobenius comparison of [Stacks, Tag 03P2] for `𝐆_a`, in every degree**: the
comparison `gaCohomologyAddEquiv` carries the Artin–Schreier map `x ↦ x ^ p - x` to `F - 1` for
the Frobenius-semilinear map `F` induced by `x ↦ x ^ p`. -/
def gaFrobeniusComparison {p : ℕ} (hp : p.Prime) [CharP k p] (n : ℕ) :
    TopDegreeFrobeniusComparison.{u + 1} p k f (additiveSheaf.{u, u + 1} X)
      (artinSchreierMap.{u, u + 1} X hp (natCast_eq_zero_of_charP k p f)) n where
  equiv := gaCohomologyAddEquiv k f n
  frobenius := ((gaCohomologyAddEquiv k f n).toAddMonoidHom.comp
      (Sheaf.H.map (frobeniusMap.{u, u + 1} X hp (natCast_eq_zero_of_charP k p f)) n)).comp
    (gaCohomologyAddEquiv k f n).symm.toAddMonoidHom
  frobenius_smul a v := by
    obtain ⟨y, rfl⟩ := (gaCohomologyAddEquiv k f n).surjective v
    simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom]
    rw [← gaCohomologyAddEquiv_map_gaScalar, AddEquiv.symm_apply_apply,
      AddEquiv.symm_apply_apply, ← Sheaf.H.map_comp_apply, gaScalar_comp_frobeniusMap,
      Sheaf.H.map_comp_apply, ← map_pow, gaCohomologyAddEquiv_map_gaScalar]
  equiv_map x := by
    simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, AddEquiv.symm_apply_apply]
    have h := Sheaf.H.map_add_apply
      (artinSchreierMap.{u, u + 1} X hp (natCast_eq_zero_of_charP k p f)) (𝟙 _) x
    rw [artinSchreierMap, sub_add_cancel, Sheaf.H.map_id_apply] at h
    have h' : Sheaf.H.map (artinSchreierMap.{u, u + 1} X hp (natCast_eq_zero_of_charP k p f)) n x =
        Sheaf.H.map (frobeniusMap.{u, u + 1} X hp (natCast_eq_zero_of_charP k p f)) n x - x :=
      eq_sub_of_add_eq h.symm
    rw [h', map_sub]

/-- **The vanishing transfer of [Stacks, Tag 03P2] for `𝐆_a` at coefficients
`AddCommGrpCat.{u + 1}`**: vanishing of `H^i(X, 𝒪_X)` implies vanishing of `H^i(X_étale, 𝐆_a)`. -/
theorem subsingleton_sheafH_additiveSheaf_of_isZero_hgroup_allDegrees (i : ℕ)
    (h : IsZero (Hgroup X.ringCatSheaf ⊤ i (SheafOfModules.unit X.ringCatSheaf))) :
    Subsingleton (Sheaf.H.{u + 1} (additiveSheaf.{u, u + 1} X) i) := by
  cases i with
  | zero =>
    have h' := (Stacks.Cohomology.CechAcyclic.isZero_rightDerived_evaluation_iff_isZero_Hgroup
      X.ringCatSheaf ⊤ 0 (SheafOfModules.unit X.ringCatSheaf)).mpr h
    have hz : IsZero ((_root_.SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).obj
        (SheafOfModules.unit X.ringCatSheaf)) :=
      h'.of_iso (((_root_.SheafOfModules.evaluation X.ringCatSheaf
        (op (⊤ : X.Opens))).rightDerivedZeroIsoSelf.app _).symm)
    have hs : Subsingleton Γ(X, ⊤) := (ModuleCat.isZero_iff_subsingleton).mp hz
    exact @Equiv.subsingleton _ _ ((Sheaf.H.equiv₀ (additiveSheaf.{u, u + 1} X)
      (isTerminal_etaleSelf X)).trans AddEquiv.ulift).toEquiv hs
  | succ n =>
    have : Subsingleton (Hgroup X.ringCatSheaf ⊤ (n + 1) (Scheme.unitModule X)) :=
      AddCommGrpCat.subsingleton_of_isZero h
    exact ((gaUliftAddEquiv (X := X) (n + 1)).symm.trans ((gaAssocAddEquiv (n + 1)).trans
      (hgroupAssocIso n).symm.addCommGroupIsoToAddEquiv)).toEquiv.subsingleton

end Assembly

end Stacks.ArtinSchreier

end
