module

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekCompactSupportCompactification
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekProper
public import StacksFrontier.AlgebraicGeometry.Topologies.BigEtale.SmallEtaleFunctoriality
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Existence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.SmallEtaleSitePresentation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LocallyConstantCompactSupport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleSheafSideConditions
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyZero
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.FiniteRingModuleUnderlyingAbelian
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Vanishing of `H⁰_c` of a locally constant sheaf on a non-proper integral scheme

Let `X` be an integral scheme of finite type over a field `k` which is not proper over `k`, let
`j : X ⟶ X̄` be an open immersion into a scheme proper over `k`, and let `ℱ` be a locally
constant sheaf on `X_étale`. Then `j_!ℱ` has no nonzero global section on `X̄`. Since `H⁰_c(X, ℱ)`
is `H⁰(X̄, j_!ℱ)`, this is the last assertion of Tag 03VL, `H⁰_c(X_{k̄}, ℱ_ρ) = 0` for `X` not
projective.

## Main results

* `Stacks.EtaleCohomology.extensionByZero_sections_eq_zero_of_not_isProper` — the statement on
  the small étale site of Stacks 021B, with abelian coefficients.

## Implementation notes

On the site of Stacks 021B the statement is assembled from three results of the base: every
global section of a sheaf on a proper scheme has proper support (Tag 0F73), the sections of
`j_!ℱ` with proper support are those of `ℱ` (Tag 0F75), and a locally constant sheaf on an
integral non-proper scheme has no nonzero section with proper support
(`Stacks.EtaleCohomology.compactlySupportedSections_eq_bot_of_not_isProper`).

## References

* [Stacks Project, Tag 03VL](https://stacks.math.columbia.edu/tag/03VL)
* [Stacks Project, Tag 0F73](https://stacks.math.columbia.edu/tag/0F73)
* [Stacks Project, Tag 0F75](https://stacks.math.columbia.edu/tag/0F75)
* [Stacks Project, Tag 0GK1](https://stacks.math.columbia.edu/tag/0GK1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u r w

namespace Stacks.EtaleCohomology

section BoundedSite

variable (k : Type u) [Field k] (B : BigEtaleSite.{u}) (Xbar : B.Scheme)
  (fbar : Xbar.obj ⟶ Spec (.of k)) [IsProper fbar]
  (U : SmallEtale B Xbar.obj Xbar.property) [IsOpenImmersion (B.inclusion.map U.obj.hom)]
  (F : Sheaf (SmallEtale.topology B U.obj.left.obj U.obj.left.property) AddCommGrpCat.{u + 1})

/-- **A locally constant sheaf on an integral open which is not proper has no nonzero global
section after extension by zero to a proper scheme.** Every global section of `j_!ℱ` has proper
support because the ambient scheme is proper (Tag 0F73); it is therefore the extension by zero
of a section of `ℱ` with proper support (Tag 0F75), and those vanish on an integral scheme that
is not proper. -/
@[sga "4½ Sommes_trig 1.18" "Clause b)"]
theorem extensionByZero_sections_eq_zero_of_not_isProper [IsIntegral U.obj.left.obj]
    (hf : ¬ IsProper (B.inclusion.map U.obj.hom ≫ fbar))
    [Stacks.ConstantSheaf.IsLocallyConstant
      (SmallEtale.topology B U.obj.left.obj U.obj.left.property) F]
    (s : ((abelianExtensionByZero B Xbar.obj Xbar.property U).obj F).obj.obj
      (op (SmallEtale.final B Xbar.obj Xbar.property))) :
    s = 0 := by
  set e := SmallEtale.compactlySupportedSections_extensionByZero k B Xbar fbar U F
  have hs : s ∈ SmallEtale.compactlySupportedSections k Xbar.obj fbar B Xbar.property
      ((abelianExtensionByZero B Xbar.obj Xbar.property U).obj F) := by
    rw [SmallEtale.compactlySupportedSections_eq_top_of_isProper]
    exact AddSubgroup.mem_top s
  have hbot := compactlySupportedSections_eq_bot_of_not_isProper (X := U.obj.left.obj) k
    (B.inclusion.map U.obj.hom ≫ fbar) B U.obj.left.property F hf
  have hmem : (e.symm ⟨s, hs⟩).1 ∈ (⊥ : AddSubgroup _) := hbot ▸ (e.symm ⟨s, hs⟩).2
  have h0 : e.symm ⟨s, hs⟩ = 0 := Subtype.ext (AddSubgroup.mem_bot.1 hmem)
  simpa using congrArg Subtype.val (e.symm_apply_eq.1 h0)

end BoundedSite

section ModuleExtensionByZero

variable (Λ : Type r) [Ring Λ] (B : BigEtaleSite.{u}) (Xbar : B.Scheme)
  (U : SmallEtale B Xbar.obj Xbar.property)

/-- Sheafification of presheaves of `Λ`-modules on the small étale site of Stacks 021B. -/
local instance hasSheafify_smallEtale_moduleCat (S : Scheme.{u}) (hS : B.Contains S) :
    HasSheafify (SmallEtale.topology B S hS) (ModuleCat.{u + 1} Λ) :=
  Stacks.ModuleSheaf.hasSheafify_moduleCat.{u + 1} Λ _

/-- Postcomposition with the forgetful functor of `Λ`-modules carries sheaves on the small étale
site of Stacks 021B to sheaves. -/
local instance hasSheafCompose_smallEtale_forget₂ (S : Scheme.{u}) (hS : B.Contains S) :
    (SmallEtale.topology B S hS).HasSheafCompose
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
  Stacks.ModuleSheaf.hasSheafCompose_forget₂.{u + 1} Λ _

/-- The forgetful functor of `Λ`-modules commutes with sheafification on the small étale site
of Stacks 021B. -/
local instance preservesSheafification_smallEtale_forget₂ (S : Scheme.{u}) (hS : B.Contains S) :
    (SmallEtale.topology B S hS).PreservesSheafification
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
  Stacks.ModuleSheaf.preservesSheafification_forget₂.{u + 1} Λ _

/-- Extension by zero of sheaves of `Λ`-modules on the small étale site of Stacks 021B, along
`U ⟶ X̄`: the left adjoint of restriction along `AlgebraicGeometry.smallEtalePostcompose`. -/
abbrev moduleExtensionByZero :
    Sheaf (SmallEtale.topology B U.obj.left.obj U.obj.left.property) (ModuleCat.{u + 1} Λ) ⥤
      Sheaf (SmallEtale.topology B Xbar.obj Xbar.property) (ModuleCat.{u + 1} Λ) :=
  Functor.sheafPullbackConstruction.sheafPullback
    (smallEtalePostcompose B Xbar.obj Xbar.property U) (ModuleCat.{u + 1} Λ)
    (SmallEtale.topology B U.obj.left.obj U.obj.left.property)
    (SmallEtale.topology B Xbar.obj Xbar.property)

/-- **Extension by zero of sheaves of modules is extension by zero of the underlying abelian
sheaves**, on the small étale site of Stacks 021B. -/
def moduleExtensionByZeroForget₂Iso :
    moduleExtensionByZero Λ B Xbar U ⋙
        sheafCompose (SmallEtale.topology B Xbar.obj Xbar.property)
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) ≅
      sheafCompose (SmallEtale.topology B U.obj.left.obj U.obj.left.property)
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) ⋙
        abelianExtensionByZero B Xbar.obj Xbar.property U :=
  Functor.isoWhiskerRight ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (smallEtalePostcompose B Xbar.obj Xbar.property U) (ModuleCat.{u + 1} Λ) _ _).leftAdjointUniq
      (Functor.sheafAdjunctionContinuous _ _ _ _)) _ ≪≫
    ((smallEtalePostcompose B Xbar.obj Xbar.property U).sheafPullbackSheafComposeNatIso
      (ModuleCat.{u + 1} Λ) _ _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).symm ≪≫
    Functor.isoWhiskerLeft _ ((Functor.sheafAdjunctionContinuous _ _ _ _).leftAdjointUniq
      (abelianExtensionByZeroAdjunction B Xbar.obj Xbar.property U))

/-- **A finite type locally constant sheaf of modules over a finite ring on an integral open
which is not proper has no nonzero global section after extension by zero to a proper scheme**,
on the small étale site of Stacks 021B. The abelian sheaf underlying it is finite locally
constant, so this is `Stacks.EtaleCohomology.extensionByZero_sections_eq_zero_of_not_isProper`
read through `Stacks.EtaleCohomology.moduleExtensionByZeroForget₂Iso`. -/
theorem subsingleton_moduleExtensionByZero_sections [Finite Λ]
    [ConnectedSpace U.obj.left.obj] (k : Type u) [Field k] (fbar : Xbar.obj ⟶ Spec (.of k))
    [IsProper fbar] [IsOpenImmersion (B.inclusion.map U.obj.hom)] [IsIntegral U.obj.left.obj]
    (hf : ¬ IsProper (B.inclusion.map U.obj.hom ≫ fbar))
    (G : Sheaf (SmallEtale.topology B U.obj.left.obj U.obj.left.property) (ModuleCat.{u + 1} Λ))
    (hG : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ
      (SmallEtale.topology B U.obj.left.obj U.obj.left.property) G) :
    Subsingleton (((moduleExtensionByZero Λ B Xbar U).obj G).obj.obj
      (op (SmallEtale.final B Xbar.obj Xbar.property))) := by
  have hfl : Stacks.ConstantSheaf.IsFiniteLocallyConstant
      (SmallEtale.topology B U.obj.left.obj U.obj.left.property) G :=
    congrFun (isFiniteTypeLocallyConstant_eq_isFiniteLocallyConstant B U.obj.left Λ) G ▸ hG
  have : Stacks.ConstantSheaf.IsLocallyConstant
      (SmallEtale.topology B U.obj.left.obj U.obj.left.property)
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G) := by
    have := Stacks.ConstantSheaf.isFiniteLocallyConstant_forget₂Module _ Λ G hfl
    infer_instance
  refine ⟨fun a b ↦ ?_⟩
  have e := ((sheafToPresheaf _ _).mapIso ((moduleExtensionByZeroForget₂Iso Λ B Xbar U).app G)).app
    (op (SmallEtale.final B Xbar.obj Xbar.property))
  apply (ConcreteCategory.bijective_of_isIso e.hom).1
  rw [extensionByZero_sections_eq_zero_of_not_isProper k B Xbar fbar U _ hf (e.hom a),
    extensionByZero_sections_eq_zero_of_not_isProper k B Xbar fbar U _ hf (e.hom b)]

end ModuleExtensionByZero

section EtaleSite

attribute [local instance] moduleCat_hasLimitsOfSize

variable (Λ : Type r) [Ring Λ] [Finite Λ] (B : BigEtaleSite.{u}) (Y : B.Scheme)
  [ConnectedSpace Y.1] (y : GeometricPoint Y.1) {Xbar : Scheme.{u}} (hXbar : B.Contains Xbar)
  (j : Y.1 ⟶ Xbar) [IsOpenImmersion j]

/-- An open immersion out of an object of a big étale site into a scheme the site contains, as
an object of the small étale site of Stacks 021B of the target. -/
abbrev openImmersionSmallEtale : SmallEtale B Xbar hXbar :=
  haveI : Etale (B.inclusion.map (ObjectProperty.homMk (P := fun S ↦ B.Contains S) (X := Y)
      (Y := ⟨Xbar, hXbar⟩) j)) := inferInstanceAs (Etale j)
  SmallEtale.ofEtaleHom B
    (ObjectProperty.homMk (P := fun S ↦ B.Contains S) (X := Y) (Y := ⟨Xbar, hXbar⟩) j)

/-- Sheafification of presheaves of `Λ`-modules with lifted coefficients on the small étale site
of Stacks 021B. -/
local instance hasSheafify_smallEtale_moduleCat_max (S : Scheme.{u}) (hS : B.Contains S) :
    HasSheafify (SmallEtale.topology B S hS) (ModuleCat.{max (u + 1) r} Λ) :=
  Stacks.ModuleSheaf.hasSheafify_moduleCat.{max (u + 1) r} Λ _

/-- Composition with the open immersion is continuous, in the spelling in which its source is the
object `Y` of the big étale site. -/
local instance isContinuous_smallEtalePostcompose_openImmersion :
    (smallEtalePostcompose B Xbar hXbar (openImmersionSmallEtale B Y hXbar j)).IsContinuous
      (SmallEtale.topology B Y.1 Y.2) (SmallEtale.topology B Xbar hXbar) :=
  smallEtalePostcompose_isContinuous B Xbar hXbar (openImmersionSmallEtale B Y hXbar j)

/-- Extension by zero of sheaves of `Λ`-modules with lifted coefficients on the small étale site
of Stacks 021B. -/
abbrev moduleExtensionByZeroMax :
    Sheaf (SmallEtale.topology B Y.1 Y.2) (ModuleCat.{max (u + 1) r} Λ) ⥤
      Sheaf (SmallEtale.topology B Xbar hXbar) (ModuleCat.{max (u + 1) r} Λ) :=
  Functor.sheafPullbackConstruction.sheafPullback
    (smallEtalePostcompose B Xbar hXbar (openImmersionSmallEtale B Y hXbar j))
    (ModuleCat.{max (u + 1) r} Λ) (SmallEtale.topology B Y.1 Y.2) (SmallEtale.topology B Xbar hXbar)

/-- **Extension by zero on Mathlib's site is extension by zero on the site of Stacks 021B**, for
sheaves of `Λ`-modules with lifted coefficients. -/
def etaleModuleExtensionByZeroSheafEquivIso :
    (SmallEtale.sheafEquiv B Y.1 Y.2 (ModuleCat.{max (u + 1) r} Λ)).functor ⋙
        etaleModuleExtensionByZero.{u, r} Λ j ≅
      moduleExtensionByZeroMax Λ B Y hXbar j ⋙
        (SmallEtale.sheafEquiv B Xbar hXbar (ModuleCat.{max (u + 1) r} Λ)).functor :=
  SmallEtale.sheafEquivExtensionByZeroIso B Xbar hXbar (openImmersionSmallEtale B Y hXbar j)
    (ModuleCat.{max (u + 1) r} Λ) (etaleModuleExtensionByZeroAdj.{u, r} Λ j)
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous _ _ _ _)

/-- **Extension by zero on the site of Stacks 021B commutes with raising the module universe.** -/
def moduleExtensionByZeroUliftIso :
    sheafCompose (SmallEtale.topology B Y.1 Y.2) (ModuleCat.uliftFunctor.{r, u + 1} Λ) ⋙
        moduleExtensionByZeroMax Λ B Y hXbar j ≅
      moduleExtensionByZero Λ B ⟨Xbar, hXbar⟩ (openImmersionSmallEtale B Y hXbar j) ⋙
        sheafCompose (SmallEtale.topology B Xbar hXbar) (ModuleCat.uliftFunctor.{r, u + 1} Λ) :=
  letI : ∀ Z : (SmallEtale B Xbar hXbar)ᵒᵖ, PreservesColimitsOfShape
      (CostructuredArrow (smallEtalePostcompose B Xbar hXbar
        (openImmersionSmallEtale B Y hXbar j)).op Z)
      (ModuleCat.uliftFunctor.{r, u + 1} Λ) := fun _ ↦
    ModuleCat.uliftFunctor_preservesColimitsOfShape.{r, u + 1, u + 1, u, r} Λ _
  Functor.isoWhiskerLeft _ ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (smallEtalePostcompose B Xbar hXbar (openImmersionSmallEtale B Y hXbar j))
      (ModuleCat.{max (u + 1) r} Λ) _ _).leftAdjointUniq
      (Functor.sheafAdjunctionContinuous _ _ _ _)) ≪≫
    (smallEtalePostcompose B Xbar hXbar
        (openImmersionSmallEtale B Y hXbar j)).sheafPullbackSheafComposeNatIso
      (ModuleCat.{u + 1} Λ) _ _ (ModuleCat.uliftFunctor.{r, u + 1} Λ) ≪≫
    Functor.isoWhiskerRight ((Functor.sheafAdjunctionContinuous _ _ _ _).leftAdjointUniq
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (smallEtalePostcompose B Xbar hXbar (openImmersionSmallEtale B Y hXbar j))
        (ModuleCat.{u + 1} Λ) _ _)) _

omit [Finite Λ] in
/-- A module isomorphic to a module with at most one element has at most one element. -/
theorem subsingleton_of_moduleIso {A A' : ModuleCat.{w} Λ} (e : A ≅ A')
    (h : Subsingleton A) : Subsingleton A' :=
  ⟨fun _ _ ↦ (ConcreteCategory.bijective_of_isIso e.inv).1 (h.elim _ _)⟩

include hXbar in
/-- **The global sections of the extension by zero along an open immersion of an integral scheme
which is not proper into a proper scheme vanish**, for a sheaf of `Λ`-modules on Mathlib's small
étale site which comes, with lifted coefficients, from a finite type locally constant sheaf on
the site of Stacks 021B. -/
theorem subsingleton_globalSections_extensionByZero_sheafEquiv (k : Type u) [Field k]
    (fbar : Xbar ⟶ Spec (.of k)) [IsProper fbar] [IsIntegral Y.1] (hf : ¬ IsProper (j ≫ fbar))
    (G : Sheaf (SmallEtale.topology B Y.1 Y.2) (ModuleCat.{u + 1} Λ))
    (hG : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ (SmallEtale.topology B Y.1 Y.2) G) :
    Subsingleton ((etaleModuleGlobalSections.{u, r} Λ Xbar).obj
      ((etaleModuleExtensionByZero.{u, r} Λ j).obj
        ((SmallEtale.sheafEquiv B Y.1 Y.2 (ModuleCat.{max (u + 1) r} Λ)).functor.obj
          ((sheafCompose (SmallEtale.topology B Y.1 Y.2)
            (ModuleCat.uliftFunctor.{r, u + 1} Λ)).obj G)))) := by
  set U := openImmersionSmallEtale B Y hXbar j
  have : IsProper (show (⟨Xbar, hXbar⟩ : B.Scheme).obj ⟶ Spec (.of k) from fbar) := ‹_›
  have : IsOpenImmersion (B.inclusion.map U.obj.hom) := ‹IsOpenImmersion j›
  have : IsIntegral U.obj.left.obj := ‹IsIntegral Y.1›
  have : ConnectedSpace U.obj.left.obj := ‹ConnectedSpace Y.1›
  have h0 := subsingleton_moduleExtensionByZero_sections Λ B ⟨Xbar, hXbar⟩ U k fbar hf G hG
  set H := (sheafCompose (SmallEtale.topology B Xbar hXbar)
      (ModuleCat.uliftFunctor.{r, u + 1} Λ)).obj ((moduleExtensionByZero Λ B ⟨Xbar, hXbar⟩ U).obj G)
  have e1 := (etaleModuleExtensionByZeroSheafEquivIso Λ B Y hXbar j).app
      ((sheafCompose (SmallEtale.topology B Y.1 Y.2)
        (ModuleCat.uliftFunctor.{r, u + 1} Λ)).obj G) ≪≫
    (SmallEtale.sheafEquiv B Xbar hXbar (ModuleCat.{max (u + 1) r} Λ)).functor.mapIso
      ((moduleExtensionByZeroUliftIso Λ B Y hXbar j).app G)
  have e2 := ((sheafToPresheaf _ _).mapIso
    ((SmallEtale.sheafEquiv B Xbar hXbar (ModuleCat.{max (u + 1) r} Λ)).unitIso.app H)).app
      (op (SmallEtale.final B Xbar hXbar))
  have e3 := (Sheaf.ΓNatIsoSheafSections Xbar.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)
    (SmallEtale.isTerminal_toEtaleSite_final B Xbar hXbar)).app
      ((etaleModuleExtensionByZero.{u, r} Λ j).obj
        ((SmallEtale.sheafEquiv B Y.1 Y.2 (ModuleCat.{max (u + 1) r} Λ)).functor.obj
          ((sheafCompose (SmallEtale.topology B Y.1 Y.2)
            (ModuleCat.uliftFunctor.{r, u + 1} Λ)).obj G)))
  have e4 := ((sheafToPresheaf _ _).mapIso e1).app
    (op ((SmallEtale.toEtaleSite B Xbar hXbar).obj (SmallEtale.final B Xbar hXbar)))
  have s1 : Subsingleton (H.obj.obj (op (SmallEtale.final B Xbar hXbar))) :=
    ⟨fun a b ↦ ULift.ext _ _ (h0.elim a.down b.down)⟩
  exact subsingleton_of_moduleIso Λ e3.symm
    (subsingleton_of_moduleIso Λ e4.symm (subsingleton_of_moduleIso Λ e2 s1))

include hXbar in
/-- **The global sections of the extension by zero of `ℱ_ρ` along an open immersion of an
integral scheme which is not proper into a proper scheme vanish.** For `j : Y ⟶ X̄` an open
immersion over a field `k` with `X̄` proper over `k` and `Y` integral but not proper over `k`,
`H⁰(X̄, j_!ℱ_ρ) = 0`. -/
theorem subsingleton_globalSections_extensionByZero_representationSheaf (k : Type u) [Field k]
    (fbar : Xbar ⟶ Spec (.of k)) [IsProper fbar] [IsIntegral Y.1] (hf : ¬ IsProper (j ≫ fbar))
    (M : Stacks.GroupCohomology.FiniteTypeContinuousModule.{r, u + 1, u + 1} Λ
      (EtaleFundamentalGroup Y.1 y)) :
    Subsingleton ((etaleModuleGlobalSections.{u, r} Λ Xbar).obj
      ((etaleModuleExtensionByZero.{u, r} Λ j).obj ((representationSheaf B Y y Λ).obj M))) :=
  subsingleton_globalSections_extensionByZero_sheafEquiv Λ B Y hXbar j k fbar hf _
    ((finiteTypeLocallyConstantModuleSheafEquivalence B Y y Λ).inverse.obj M).property

end EtaleSite

section Independent

attribute [local instance] moduleCat_hasLimitsOfSize

variable (Λ : Type r) [Ring Λ] [Finite Λ] {Y Xbar : Scheme.{u}} [ConnectedSpace Y] [IsIntegral Y]
  (j : Y ⟶ Xbar) [IsOpenImmersion j]

omit [Finite Λ] in
/-- Sheafification of presheaves of `Λ`-modules on a slice of Mathlib's small étale site of an
arbitrary scheme, at the module universe `u + 1`. -/
local instance hasWeakSheafify_etaleOver_moduleCat (S : Scheme.{u}) (W : S.Etale) :
    HasWeakSheafify (S.smallEtaleTopology.over W) (ModuleCat.{u + 1} Λ) :=
  letI := Stacks.ConstantSheaf.hasSheafify_over_moduleCat.{u + 1, u, r, u + 1}
    S.smallEtaleTopology Λ W
  inferInstance

/-- **`H⁰(X̄, j_!ℱ) = 0` for a finite type locally constant sheaf `ℱ` on an integral scheme which
is not proper, along an open immersion into a proper scheme.** Here `ℱ` is a sheaf of
`Λ`-modules on Mathlib's small étale site, with lifted coefficients, and no big étale site
appears in the statement: one containing `Y` and `X̄` is chosen in the proof. -/
theorem subsingleton_globalSections_extensionByZero_uliftFunctor (k : Type u) [Field k]
    (fbar : Xbar ⟶ Spec (.of k)) [IsProper fbar] (hf : ¬ IsProper (j ≫ fbar))
    (H : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hH : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ Y.smallEtaleTopology H) :
    Subsingleton ((etaleModuleGlobalSections.{u, r} Λ Xbar).obj
      ((etaleModuleExtensionByZero.{u, r} Λ j).obj
        ((sheafCompose Y.smallEtaleTopology (ModuleCat.uliftFunctor.{r, u + 1} Λ)).obj H))) := by
  have := small_pair.{u} Y Xbar
  set B' := BigEtaleSite.ofSet {Y, Xbar}
  have hY : B'.Contains Y := BigEtaleSite.contains_ofSet _ (by simp)
  have hX : B'.Contains Xbar := BigEtaleSite.contains_ofSet _ (by simp)
  let YB : B'.Scheme := ⟨Y, hY⟩
  have : ConnectedSpace YB.1 := ‹ConnectedSpace Y›
  have : IsIntegral YB.1 := ‹IsIntegral Y›
  set G := (SmallEtale.sheafEquiv B' Y hY (ModuleCat.{u + 1} Λ)).inverse.obj H
  have hG := (SmallEtale.isFiniteTypeLocallyConstant_sheafEquiv_inverse_iff B' YB Λ H).2 hH
  have h := subsingleton_globalSections_extensionByZero_sheafEquiv Λ B' YB hX j k fbar hf G hG
  have eH : (sheafCompose Y.smallEtaleTopology (ModuleCat.uliftFunctor.{r, u + 1} Λ)).obj H ≅
      (SmallEtale.sheafEquiv B' Y hY (ModuleCat.{max (u + 1) r} Λ)).functor.obj
        ((sheafCompose (SmallEtale.topology B' Y hY)
          (ModuleCat.uliftFunctor.{r, u + 1} Λ)).obj G) :=
    (sheafCompose Y.smallEtaleTopology (ModuleCat.uliftFunctor.{r, u + 1} Λ)).mapIso
        ((SmallEtale.sheafEquiv B' Y hY (ModuleCat.{u + 1} Λ)).counitIso.app H).symm ≪≫
      (SmallEtale.sheafEquivSheafComposeIso B' Y hY (ModuleCat.uliftFunctor.{r, u + 1} Λ)).app G
  exact subsingleton_of_moduleIso Λ ((etaleModuleGlobalSections.{u, r} Λ Xbar).mapIso
    ((etaleModuleExtensionByZero.{u, r} Λ j).mapIso eH)).symm h

attribute [local instance] HasDerivedCategory.standard in
/-- **`H⁰_c(Y, ℱ) = 0` for a finite type locally constant sheaf `ℱ` on an integral scheme `Y`
separated and of finite type but not proper over a field**, in the sense of Tag 0GJZ: the
zeroth compactly supported cohomology module of `ℱ` placed in degree zero, through any
compactification. By Tag 0GK1 it is `H⁰(X̄, j_!ℱ)`. -/
@[sga "5 VII 7.1.1" "b), degree i = 0"]
theorem isZero_compactlySupportedCohomologyGroup_zero_of_not_isProper (k : Type u) [Field k]
    (f : Y ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (hf : ¬ IsProper f) (jbar : CompactificationOf (Over.mk f))
    (H : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hH : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ Y.smallEtaleTopology H) :
    IsZero ((compactlySupportedCohomologyGroup.{u, r} k f jbar Λ 0).obj
      ((DerivedCategory.Plus.singleFunctor (EtaleModules.{u, r} Λ Y) 0).obj
        ((sheafCompose Y.smallEtaleTopology (ModuleCat.uliftFunctor.{r, u + 1} Λ)).obj H))) := by
  obtain ⟨e⟩ := nonempty_compactlySupportedCohomologyGroup_zero_iso k f jbar Λ
    ((sheafCompose Y.smallEtaleTopology (ModuleCat.uliftFunctor.{r, u + 1} Λ)).obj H)
  have hcomm : jbar.immersion ≫ jbar.toBase = f := Over.w jbar.obj.hom
  have hf' : ¬ IsProper (jbar.immersion ≫ jbar.toBase) := by rwa [hcomm]
  have : ConnectedSpace (Over.mk f).left := ‹ConnectedSpace Y›
  have : IsIntegral (Over.mk f).left := ‹IsIntegral Y›
  have h := subsingleton_globalSections_extensionByZero_uliftFunctor Λ jbar.immersion k
    jbar.toBase hf' H hH
  exact (@ModuleCat.isZero_of_subsingleton _ _ _ h).of_iso e

end Independent

end Stacks.EtaleCohomology
